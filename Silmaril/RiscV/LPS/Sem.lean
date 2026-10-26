module

public import Silmaril.RiscV.LPS.Instr
public import Silmaril.RiscV.LPS.Fpu
public import Mathlib.Tactic.SplitIfs

/-!
# LPS abstract RV64GC semantics, as a first-order effect tree

Hand translation of `theories/Riscv/Sem.v` (LPS commit `f1006fe8`, MIT).

The semantics is a plain function `exec : Word → Instr → Core → Eff` from a decoded
instruction and the core state (registers, FP registers, pc, `fcsr`, LR/SC reservation) to a
finite, first-order tree of residual effects. Only the operations this semantics does not
interpret appear as tree nodes:

* `Eff.load n a k` / `Eff.store n a v k`: the memory boundary. Memory belongs to the
  interpreter (`Silmaril.RiscV.LPS.Machine`); `n` is the access width in bits.
* `Eff.ecall c` / `Eff.ebreak c`: the process/hardware split. They carry the core with pc
  already advanced and no continuation.
* `Eff.illegal c`: an undecodable fetch, a CSR address this model does not implement, or a
  reserved rounding mode. The model declining, not the architecture.
* `Eff.definedIllegal c`: the architecture defines the instruction to raise an
  illegal-instruction exception (a write to a read-only CSR address). Pre-state: nothing
  retires.
* `Eff.fault c`: the instruction traps by the ISA's own rules (misaligned LR/SC/AMO).
  Pre-state.
* `Eff.done c`: the instruction retired with core state `c`.

Every tree is finite, so an interpreter is a structural recursion.

Design decisions (upstream): x0 hardwiring lives in `rget`/`rset`; `fcsr` is the only
stored FP CSR (fflags and frm are slices of it); AMOs compose from plain sized loads and
stores (a sequential single-hart memory model); F and D execute here in full.

PC-advance contract: `exec sz i` reads pc once; every non-control-flow instruction leaves
`pc + sz`; the cores carried by `ecall`/`ebreak` and by the in-`exec` `illegal` (bad CSR,
reserved rounding mode) have pc already advanced; `fault`, `definedIllegal` and the
`illegal` that `step` issues for an undecodable fetch carry pc not advanced.

Upstream's `with_regs`, `with_pc`, … field updaters become Lean structure updates
`{ c with pc := … }`.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

/-! ## Pure helpers -/

/-- `w0`. -/
def w0 : Word := 0
/-- `w1`. -/
def w1 : Word := 1
/-- `low32`. -/
def low32 (v : Word) : BitVec 32 := v.extractLsb' 0 32
/-- `is_x0`. -/
def isX0 (r : Reg) : Bool := r.toNat == 0

/-- Integer ALU at any width (`alu`). Shift amounts are masked with `shmask` (63 for 64-bit,
31 for 32-bit), per the ISA. -/
def alu {n : Nat} (shmask : Nat) (op : AluOp) (a b : BitVec n) : BitVec n :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b &&& BitVec.ofNat n shmask)
  | .slt => if ltS a b then 1 else 0
  | .sltu => if ltU a b then 1 else 0
  | .xor => a ^^^ b
  | .srl => a >>> (b &&& BitVec.ofNat n shmask)
  | .sra => a.sshiftRight (b &&& BitVec.ofNat n shmask).toNat
  | .or => a ||| b
  | .and => a &&& b

/-- `alu64`. -/
def alu64 : AluOp → Word → Word → Word := alu 63
/-- `alu32`. -/
def alu32 : AluOp → BitVec 32 → BitVec 32 → BitVec 32 := alu 31

/-- `branch_taken`. -/
def branchTaken (c : BranchCond) (a b : Word) : Bool :=
  match c with
  | .eq => eqB a b
  | .ne => !eqB a b
  | .lt => ltS a b
  | .ge => !ltS a b
  | .ltu => ltU a b
  | .geu => !ltU a b

/-- M extension at any width (`mul_div`). Division truncates (`Int.tdiv`/`Int.tmod`, Rocq's
`Z.quot`/`Z.rem`). A zero divisor gives all ones (div/divu) or the dividend (rem/remu);
signed overflow needs no special case because `ofInt` wraps. -/
def mulDiv {n : Nat} (op : MulOp) (a b : BitVec n) : BitVec n :=
  let div0 := b.toNat == 0
  match op with
  | .mul => a * b
  | .mulh => mulhSS a b
  | .mulhsu => mulhSU a b
  | .mulhu => mulhUU a b
  | .div => if div0 then BitVec.ofInt n (-1) else BitVec.ofInt n (a.toInt.tdiv b.toInt)
  | .divu => if div0 then BitVec.ofInt n (-1) else BitVec.ofNat n (a.toNat / b.toNat)
  | .rem => if div0 then a else BitVec.ofInt n (a.toInt.tmod b.toInt)
  | .remu => if div0 then a else BitVec.ofNat n (a.toNat % b.toNat)

/-- `amo_bytes`. -/
def amoBytes : AWidth → Nat
  | .w => 4
  | .d => 8

/-- Natural alignment for the A extension (`amo_aligned`). Misaligned LR/SC/AMO faults;
plain loads and stores may be misaligned in this model (qemu-user and Linux make them
work). The check precedes the SC reservation test, as in the specification and Sail. -/
def amoAligned (wd : AWidth) (a : Word) : Bool := a.toNat % amoBytes wd == 0

/-- AMO combine function, `old` being the memory value (`amo_val`). -/
def amoVal {n : Nat} (op : AmoOp) (old src : BitVec n) : BitVec n :=
  match op with
  | .swap => src
  | .add => old + src
  | .xor => old ^^^ src
  | .and => old &&& src
  | .or => old ||| src
  | .min => if ltS old src then old else src
  | .max => if ltS old src then src else old
  | .minu => if ltU old src then old else src
  | .maxu => if ltU old src then src else old

/-! ## Read-only CSR addresses -/

/-- A CSR address with `csr[11:10] = 11` is read-only (`csr_read_only`). -/
def csrReadOnly (csr : BitVec 12) : Bool := (csr.toNat >>> 10) &&& 3 == 3

/-- The write side of a CSR instruction is architecturally illegal exactly when it happens
and the address is read-only (`csr_write_illegal`). -/
def csrWriteIllegal (writes : Bool) (csr : BitVec 12) : Bool := writes && csrReadOnly csr

/-- The CSR address map (`csr_slice`): only the fcsr aliases exist, as `(lo, len)` slices of
the stored fcsr. `0x001` = fflags, `0x002` = frm, `0x003` = fcsr (low 8 bits). -/
def csrSlice (csr : BitVec 12) : Option (Nat × Nat) :=
  let c := csr.toNat
  if c = 1 then some (0, 5)
  else if c = 2 then some (5, 3)
  else if c = 3 then some (0, 8)
  else none

/-- Every address `csrSlice` resolves is read/write (`csr_read_only_unimplemented`). -/
theorem csrReadOnly_unimplemented (csr : BitVec 12) (h : csrReadOnly csr = true) :
    csrSlice csr = none := by
  unfold csrSlice
  unfold csrReadOnly at h
  simp only
  split_ifs with h1 h2 h3 <;> simp_all

/-- `slice_get`. -/
def sliceGet (f : BitVec 32) (lo len : Nat) : Word :=
  BitVec.ofNat 64 ((f.toNat >>> lo) &&& (2 ^ len - 1))

/-- `slice_set`. -/
def sliceSet (f : BitVec 32) (lo len : Nat) (v : Word) : BitVec 32 :=
  let mask := (2 ^ len - 1) <<< lo
  BitVec.ofNat 32 ((f.toNat &&& (2 ^ 32 - 1 - mask)) ||| ((v.toNat <<< lo) &&& mask))

/-- NaN boxing of a single-precision value (`nan_box`). -/
def nanBox (v : BitVec 32) : Word := BitVec.allOnes 32 ++ v

/-- An S-format input that is not properly NaN-boxed reads as the canonical NaN
(`unbox_s`). -/
def unboxS (v : Word) : BitVec 32 :=
  if (v.extractLsb' 32 32).toNat = 2 ^ 32 - 1 then low32 v else 0x7fc00000#32

/-- Sign injection at any width (`sgnj_val`). -/
def sgnjVal {n : Nat} (op : FSgnOp) (a b : BitVec n) : BitVec n :=
  let sa := bit (n - 1) a
  let sb := bit (n - 1) b
  let s := match op with
    | .sgnj => sb
    | .sgnjn => !sb
    | .sgnjx => sa ^^ sb
  BitVec.ofNat n ((if s then 2 ^ (n - 1) else 0) + a.toNat % 2 ^ (n - 1))

/-! ## Core state (`core`) -/

/-- What the ISA owns: registers, FP registers, pc, fcsr, and the LR/SC reservation
(`core`). Memory belongs to the interpreter. -/
structure Core where
  /-- `c_regs`. -/
  regs : BvMap 5 Word
  /-- `c_fregs`. -/
  fregs : BvMap 5 Word
  /-- `c_pc`. -/
  pc : Word
  /-- `c_fcsr`. -/
  fcsr : BitVec 32
  /-- `c_resv`. -/
  resv : Option Word
  deriving DecidableEq, Repr

/-- Register stores are radix trees; missing keys read as 0 (`reg_get`). -/
def regGet (rm : BvMap 5 Word) (r : Reg) : Word := (BvMap.get r rm).getD w0

namespace Core

/-- x0 reads as zero (`rget`). -/
def rget (c : Core) (r : Reg) : Word := if isX0 r then w0 else regGet c.regs r
/-- Writes to x0 are discarded (`rset`). -/
def rset (r : Reg) (v : Word) (c : Core) : Core :=
  if isX0 r then c else { c with regs := BvMap.set r v c.regs }
/-- `fget`. -/
def fget (c : Core) (r : Reg) : Word := regGet c.fregs r
/-- `fset`. -/
def fset (r : Reg) (v : Word) (c : Core) : Core := { c with fregs := BvMap.set r v c.fregs }

end Core

open Core

/-! ## The FP register file's ISA-side plumbing -/

/-- `fp_format`. -/
def FFmt.format : FFmt → FpFormat
  | .s => fmtSingle
  | .d => fmtDouble

/-- Read an FP operand at the format's width, unboxing singles (`fread`). -/
def fread (c : Core) (fmt : FFmt) (r : Reg) : Nat :=
  match fmt with
  | .s => (unboxS (c.fget r)).toNat
  | .d => (c.fget r).toNat

/-- Write an FP result, boxing singles (`fwrite`). -/
def fwrite (fmt : FFmt) (r : Reg) (v : Nat) (c : Core) : Core :=
  match fmt with
  | .s => fset r (nanBox (BitVec.ofNat 32 v)) c
  | .d => fset r (BitVec.ofNat 64 v) c

/-- `fcsr[7:5]`, the dynamic rounding mode (`frm_of`). -/
def frmOf (c : Core) : Nat := (c.fcsr.toNat >>> 5) &&& 7

/-- `resolve_rm`. -/
def resolveRm (rm : BitVec 3) (c : Core) : Option RMode := RMode.ofField rm.toNat (frmOf c)

/-- Flags accrue into `fcsr[4:0]` (`accrue`). -/
def accrue (fl : FFlags) (c : Core) : Core :=
  { c with fcsr := BitVec.ofNat 32 (c.fcsr.toNat ||| fl.bits) }

/-- A store or AMO to the reserved address invalidates the reservation (`inval_resv`). The
base addresses are compared exactly. -/
def invalResv (a : Word) (c : Core) : Core :=
  match c.resv with
  | some r => if r.toNat = a.toNat then { c with resv := none } else c
  | none => c

/-! ## The effect tree (`eff`) -/

/-- Residual effects of one instruction (`eff`). -/
inductive Eff where
  | done (c : Core)
  | illegal (c : Core)
  | definedIllegal (c : Core)
  | ecall (c : Core)
  | ebreak (c : Core)
  | fault (c : Core)
  | load (n : Nat) (a : Word) (k : BitVec n → Eff)
  | store (n : Nat) (a : Word) (v : BitVec n) (k : Eff)

/-- The kinds of terminal node of an effect tree. -/
inductive EffKind where
  | done | illegal | definedIllegal | ecall | ebreak | fault
  deriving DecidableEq, Repr

/-- The terminal node of a tree that issues no memory effect, with its kind; `none` for a
`load` or `store` node. Used to state checks, since `Eff` has no decidable equality. -/
def Eff.leaf : Eff → Option (EffKind × Core)
  | .done c => some (.done, c)
  | .illegal c => some (.illegal, c)
  | .definedIllegal c => some (.definedIllegal, c)
  | .ecall c => some (.ecall, c)
  | .ebreak c => some (.ebreak, c)
  | .fault c => some (.fault, c)
  | .load .. | .store .. => none

/-- Load a value of size `sz`, sign- or zero-extended (`load_val`). -/
def loadVal (sz : MSize) (sgn : Bool) (a : Word) (k : Word → Eff) : Eff :=
  match sz with
  | .sz1 => .load 8 a fun v => k (if sgn then sext 64 v else zext 64 v)
  | .sz2 => .load 16 a fun v => k (if sgn then sext 64 v else zext 64 v)
  | .sz4 => .load 32 a fun v => k (if sgn then sext 64 v else zext 64 v)
  | .sz8 => .load 64 a k

/-- `store_val`. -/
def storeVal (sz : MSize) (a : Word) (v : Word) (k : Eff) : Eff :=
  match sz with
  | .sz1 => .store 8 a (v.extractLsb' 0 8) k
  | .sz2 => .store 16 a (v.extractLsb' 0 16) k
  | .sz4 => .store 32 a (low32 v) k
  | .sz8 => .store 64 a v k

/-- CSR access (`exec_csr`). The read always happens; unknown addresses are `illegal` with
pc already advanced. -/
def execCsr (op : CsrOp) (rd : Reg) (operand : Word) (writes : Bool) (csr : BitVec 12)
    (c : Core) : Eff :=
  match csrSlice csr with
  | none => .illegal c
  | some (lo, len) =>
    let f := c.fcsr
    let old := sliceGet f lo len
    let newv := match op with
      | .rw => operand
      | .rs => old ||| operand
      | .rc => old &&& ~~~operand
    .done (rset rd old (if writes then { c with fcsr := sliceSet f lo len newv } else c))

/-- Integer kind of an `fcvt` operand: signedness and width. -/
def FCvtTy.int? : FCvtTy → Option (Bool × Nat)
  | .w => some (true, 32)
  | .wu => some (false, 32)
  | .l => some (true, 64)
  | .lu => some (false, 64)
  | _ => none

/-- FP format of an `fcvt` operand. -/
def FCvtTy.float? : FCvtTy → Option FFmt
  | .s => some .s
  | .d => some .d
  | _ => none

/-- Execute one decoded instruction, including the pc update (`exec`). `sz` is the encoded
size: 2 for expanded compressed instructions, else 4. -/
def exec (sz : Word) (i : Instr) (c : Core) : Eff :=
  let pc := c.pc
  let npc := pc + sz
  let cn := { c with pc := npc } -- pc advanced past the instruction
  match i with
  -- RV64I
  | .lui rd imm => .done (rset rd (sext 64 (imm ++ (0 : BitVec 12))) cn)
  | .auipc rd imm => .done (rset rd (pc + sext 64 (imm ++ (0 : BitVec 12))) cn)
  | .jal rd imm => .done (rset rd npc { c with pc := pc + sext 64 imm })
  | .jalr rd rs1 imm =>
    -- Target computed before the link write: rd may equal rs1.
    let a := c.rget rs1
    .done (rset rd npc { c with pc := (a + sext 64 imm) &&& ~~~w1 })
  | .branch bc rs1 rs2 imm =>
    .done { c with pc := if branchTaken bc (c.rget rs1) (c.rget rs2) then pc + sext 64 imm
                         else npc }
  | .load msz sgn rd rs1 imm =>
    loadVal msz sgn (c.rget rs1 + sext 64 imm) fun v => .done (rset rd v cn)
  | .store msz rs1 rs2 imm =>
    let a := c.rget rs1 + sext 64 imm
    storeVal msz a (c.rget rs2) (.done (invalResv a cn))
  | .opImm op rd rs1 imm => .done (rset rd (alu64 op (c.rget rs1) (sext 64 imm)) cn)
  | .shiftImm op rd rs1 shamt => .done (rset rd (alu64 op (c.rget rs1) (zext 64 shamt)) cn)
  | .op op rd rs1 rs2 => .done (rset rd (alu64 op (c.rget rs1) (c.rget rs2)) cn)
  | .opImm32 rd rs1 imm =>
    .done (rset rd (sext 64 (alu32 .add (low32 (c.rget rs1)) (sext 32 imm))) cn)
  | .shiftImm32 op rd rs1 shamt =>
    .done (rset rd (sext 64 (alu32 op (low32 (c.rget rs1)) (zext 32 shamt))) cn)
  | .op32 op rd rs1 rs2 =>
    .done (rset rd (sext 64 (alu32 op (low32 (c.rget rs1)) (low32 (c.rget rs2)))) cn)
  | .fence .. | .fenceI .. => .done cn -- single hart: fences are no-ops
  | .ecall => .ecall cn
  | .ebreak => .ebreak cn
  -- M
  | .mul op rd rs1 rs2 => .done (rset rd (mulDiv op (c.rget rs1) (c.rget rs2)) cn)
  -- Operands are truncated to 32 bits before the divide, per the ISA.
  | .mul32 op rd rs1 rs2 =>
    .done (rset rd (sext 64 (mulDiv op (low32 (c.rget rs1)) (low32 (c.rget rs2)))) cn)
  -- A: sequential single-hart model, composed from plain memory operations.
  | .lr wd _ _ rd rs1 =>
    let a := c.rget rs1
    if !amoAligned wd a then .fault c
    else match wd with
      | .w => .load 32 a fun v => .done { rset rd (sext 64 v) cn with resv := some a }
      | .d => .load 64 a fun v => .done { rset rd v cn with resv := some a }
  | .sc wd _ _ rd rs1 rs2 =>
    let a := c.rget rs1
    -- Alignment first, before the reservation.
    if !amoAligned wd a then .fault c
    else
      let ok := match c.resv with
        | some r => r.toNat == a.toNat
        | none => false
      let c1 := { cn with resv := none }
      if ok then
        let k := Eff.done (rset rd w0 c1)
        match wd with
        | .w => .store 32 a (low32 (c.rget rs2)) k
        | .d => .store 64 a (c.rget rs2) k
      else .done (rset rd w1 c1)
  | .amo op wd _ _ rd rs1 rs2 =>
    let a := c.rget rs1
    if !amoAligned wd a then .fault c
    else
      let src := c.rget rs2
      let c1 := invalResv a cn
      match wd with
      | .w => .load 32 a fun old =>
          .store 32 a (amoVal op old (low32 src)) (.done (rset rd (sext 64 old) c1))
      | .d => .load 64 a fun old =>
          .store 64 a (amoVal op old src) (.done (rset rd old c1))
  -- Zicsr. The architectural read-only check runs on the pre-state.
  | .csr op rd rs1 csr =>
    let writes := match op with | .rw => true | _ => !isX0 rs1
    if csrWriteIllegal writes csr then .definedIllegal c
    else execCsr op rd (c.rget rs1) writes csr cn
  | .csrI op rd uimm csr =>
    let writes := match op with | .rw => true | _ => uimm.toNat != 0
    if csrWriteIllegal writes csr then .definedIllegal c
    else execCsr op rd (zext 64 uimm) writes csr cn
  -- F/D data movement
  | .fLoad fmt rd rs1 imm =>
    let a := c.rget rs1 + sext 64 imm
    match fmt with
    | .s => .load 32 a fun v => .done (fset rd (nanBox v) cn)
    | .d => .load 64 a fun v => .done (fset rd v cn)
  | .fStore fmt rs1 rs2 imm =>
    let a := c.rget rs1 + sext 64 imm
    let v := c.fget rs2
    let k := Eff.done (invalResv a cn)
    match fmt with
    | .s => .store 32 a (low32 v) k
    | .d => .store 64 a v k
  | .fMv dir fmt rd rs1 =>
    .done <| match dir, fmt with
      | .xF, .s => rset rd (sext 64 (low32 (c.fget rs1))) cn
      | .xF, .d => rset rd (c.fget rs1) cn
      | .fX, .s => fset rd (nanBox (low32 (c.rget rs1))) cn
      | .fX, .d => fset rd (c.rget rs1) cn
  | .fSgnj op fmt rd rs1 rs2 =>
    let a := c.fget rs1
    let b := c.fget rs2
    .done <| match fmt with
      | .s => fset rd (nanBox (sgnjVal op (unboxS a) (unboxS b))) cn
      | .d => fset rd (sgnjVal op a b) cn
  -- F/D arithmetic: resolve the rounding mode (a reserved one is `illegal`, pc advanced),
  -- read the operands at the format's width, call `Fpu`, write back, accrue the flags.
  | .fAri op fmt rd rs1 rs2 rm =>
    match resolveRm rm cn with
    | none => .illegal cn
    | some md =>
      let f := fmt.format
      let a := fread c fmt rs1
      let b := fread c fmt rs2
      let (v, fl) := match op with
        | .add => fpAdd f md a b
        | .sub => fpSub f md a b
        | .mul => fpMul f md a b
        | .div => fpDiv f md a b
      .done (fwrite fmt rd v (accrue fl cn))
  | .fSqrt fmt rd rs1 rm =>
    match resolveRm rm cn with
    | none => .illegal cn
    | some md =>
      let (v, fl) := fpSqrt fmt.format md (fread c fmt rs1)
      .done (fwrite fmt rd v (accrue fl cn))
  -- The four fused forms differ by which of the product and the addend is negated, by a
  -- sign-bit flip; negating rs1 negates the product.
  | .fma op fmt rd rs1 rs2 rs3 rm =>
    match resolveRm rm cn with
    | none => .illegal cn
    | some md =>
      let f := fmt.format
      let a := fread c fmt rs1
      let b := fread c fmt rs2
      let z := fread c fmt rs3
      let (a', z') := match op with
        | .madd => (a, z)
        | .msub => (a, fpNeg f z)
        | .nmsub => (fpNeg f a, z)
        | .nmadd => (fpNeg f a, fpNeg f z)
      let (v, fl) := fpFma f md a' b z'
      .done (fwrite fmt rd v (accrue fl cn))
  | .fMinMax op fmt rd rs1 rs2 =>
    let (v, fl) := fpMinMax fmt.format (match op with | .min => false | .max => true)
      (fread c fmt rs1) (fread c fmt rs2)
    .done (fwrite fmt rd v (accrue fl cn))
  -- The compares and fclass write an integer register.
  | .fCmp op fmt rd rs1 rs2 =>
    let f := fmt.format
    let a := fread c fmt rs1
    let b := fread c fmt rs2
    let (v, fl) := match op with
      | .eq => fpEq f a b
      | .lt => fpLt f a b
      | .le => fpLe f a b
    .done (rset rd (if v then w1 else w0) (accrue fl cn))
  | .fClass fmt rd rs1 =>
    .done (rset rd (BitVec.ofNat 64 (fpClass fmt.format (fread c fmt rs1))) cn)
  -- fcvt: the decoder only produces the valid (dst, src) pairs; the rest answer `illegal`.
  -- An integer result is sign-extended into the destination even when unsigned.
  | .fCvt dst src rd rs1 rm =>
    match resolveRm rm cn with
    | none => .illegal cn
    | some md =>
      match dst.float?, src.float? with
      | some df, some sf => -- float → float
        let (v, fl) := fpConvert sf.format df.format md (fread c sf rs1)
        .done (fwrite df rd v (accrue fl cn))
      | none, some sf => -- float → integer
        match dst.int? with
        | none => .illegal cn
        | some (sgn, bits) =>
          let (v, fl) := fpToInt sf.format md sgn bits (fread c sf rs1)
          .done (rset rd (if bits = 32 then sext 64 (BitVec.ofNat 32 v) else BitVec.ofNat 64 v)
            (accrue fl cn))
      | some df, none => -- integer → float
        match src.int? with
        | none => .illegal cn
        | some (sgn, bits) =>
          let (v, fl) := fpOfInt df.format md sgn bits (c.rget rs1).toNat
          .done (fwrite df rd v (accrue fl cn))
      | none, none => .illegal cn

/-- Fetch, decode, dispatch (`step`). For a 16-bit instruction the high half of the fetched
word may be garbage; the decoder ignores it. An undecodable word is `illegal` with pc not
advanced. -/
def step (decodeAny : BitVec 32 → Option (Instr × Int)) (c : Core) : Eff :=
  .load 32 c.pc fun w32 =>
    match decodeAny w32 with
    | some (i, isz) => exec (BitVec.ofInt 64 isz) i c
    | none => .illegal c

end Silmaril.RiscV.LPS
