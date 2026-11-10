module

public import Silmaril.X86.Exact.Defs
public import Silmaril.X86.Loose.Thms
public import Silmaril.Proofs.X86.Exact.Str

/-!
# Proofs: the `Int` forms of `Σ v1` allow the results of `Ext9`

The header is `Silmaril/X86/Exact/Thms.lean`. Every `Int` form is a `Kernel`
(`Loose/Forms/Mem.lean`). For each family:

* a **success** of `Ext9.exec` is admitted by the kernel's effect: the same `rip`, registers
  and memory, and the flags Ext computes, which `FlagEff.loose` allows (PF and AF are
  undefined, so any value; the other flags are Ext's own, `none` included);
* a **fault** of `Ext9.exec` (a `dataFault`; the `Int` forms have no other) is where the
  kernel's read or write is not permitted, so the form is `unspecified` (`Kernel.bad`).

The tactic `kall` does both: it cases on the result of `Ext9`, splits on the kernel's input
and on the operand, and closes `Admits` (`kfinish`) or `Kernel.bad` (`kbadfinish`). The dispatch `allowsExec_int` gives
`Task.intAllows`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Exact.Int

open Silmaril.X86 (State Word Byte Flags Reg AluOp)
open Silmaril.X86.Ext (Sz Narrow RM Count ShiftOp UnOp leBytes leValue narrowMask retire
  readRM writeRM readNarrow writeNarrow writeRM8 loadN storeN logicFlagsN subFlagsN negFlagsN
  incFlagsN decFlagsN byteSwap Result)
open Silmaril.Process (Memory)
open Silmaril.X86.Loose
open Silmaril.X86.Loose.Forms

/-! ## Generic lemmas -/

/-- A form allows a result when it allows each of its cases. -/
theorem sem_of {F : EffSpec} {c : State} {m : Memory} {l : Nat} {res : Result}
    (h : ∀ r, res = r → F.toFormSpec.sem c m l r) : F.toFormSpec.sem c m l res := h res rfl

theorem sem_ok {F : EffSpec} {c c' : State} {m m' : Memory} {l : Nat}
    (h : (F.eff c m l).Admits c m c' m') : F.toFormSpec.sem c m l (.ok c' m') :=
  Or.inr ⟨c', m', rfl, h⟩

theorem sem_bad {F : EffSpec} {c : State} {m : Memory} {l : Nat} {r : Result}
    (h : F.unspecified c m l) : F.toFormSpec.sem c m l r := Or.inl h

/-- The loose flags of `f` allow `f`, whatever the incoming flags. -/
@[simp] theorem loose_allows (f x : Flags) : (FlagEff.loose f).Allows x f :=
  ⟨ofOpt_allows .., trivial, trivial, ofOpt_allows .., ofOpt_allows .., ofOpt_allows ..⟩

@[simp] theorem keepAll_allows' (x : Flags) : FlagEff.keepAll.Allows x x := keepAll_allows x

@[simp] theorem retire_eq_ok (next : Word) (o : Option (State × Memory)) (c' : State)
    (m' : Memory) :
    retire next o = .ok c' m' ↔ ∃ t, o = some (t, m') ∧ c' = { t with rip := next } := by
  cases o with
  | none => simp [retire]
  | some p =>
    obtain ⟨t, mm⟩ := p
    simp only [retire, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨t, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨t', ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩

@[simp] theorem retire_eq_dataFault (next : Word) (o : Option (State × Memory)) :
    retire next o = .dataFault ↔ o = none := by
  cases o <;> simp [retire]

@[simp] theorem retire_ne_divideError (next : Word) (o : Option (State × Memory)) :
    retire next o = .divideError ↔ False := by
  cases o <;> simp [retire]

@[simp] theorem retire_ne_undefinedCondition (next : Word) (o : Option (State × Memory)) cc :
    retire next o = .undefinedCondition cc ↔ False := by
  cases o <;> simp [retire]

@[simp] theorem retire_ne_trap (next : Word) (o : Option (State × Memory)) :
    retire next o = .trap ↔ False := by
  cases o <;> simp [retire]

theorem writeAll_nil (m : Memory) : writeAll m [] = some m := rfl

theorem writeAll_single (m : Memory) (a : Nat) (bs : List Byte) :
    writeAll m [(a, bs)] = m.writeBytes a bs := by
  simp only [writeAll]; cases m.writeBytes a bs <;> rfl

theorem regAfter_mk_nil (a : Word) h f rd w (c : State) (r : Reg) :
    (Effect.mk a [] h f rd w).regAfter c r = c.read r := rfl

theorem regAfter_mk_one (a : Word) (q : Reg) (v : Word) h f rd w (c : State) (r : Reg) :
    (Effect.mk a [(q, v)] h f rd w).regAfter c r = if r = q then v else c.read r := by
  by_cases hq : r = q
  · subst hq; simp [Effect.regAfter]
  · simp [Effect.regAfter, hq, Ne.symm hq]

theorem regAfter_mk_pair (a : Word) (p : Reg × Word) h f rd w (c : State) (r : Reg) :
    (Effect.mk a [p] h f rd w).regAfter c r = if r = p.1 then p.2 else c.read r :=
  regAfter_mk_one a p.1 p.2 h f rd w c r

/-- `BReg.write` is the register write `bregDst`. -/
theorem breg_write (c : State) (b : Silmaril.X86.Ext8.BReg) (v : BitVec 8) :
    b.write c v = c.write (bregDst c b v).1 (bregDst c b v).2 := by
  cases b <;> rfl

theorem sz_d_bytes : Sz.d.bytes = 4 := rfl
theorem sz_q_bytes : Sz.q.bytes = 8 := rfl

theorem nextOf_fold (c : State) (l : Nat) : c.rip + BitVec.ofNat 64 l = nextOf c l := rfl

theorem storeN_eq (m : Memory) (a : Word) (k : Nat) (v : Word) :
    storeN m a k v = m.writeBytes a.toNat (leBytes v k) := rfl

/-! ## Tactics -/

/-- Close an `Admits` goal for a kernel form, after the successor is substituted. -/
syntax "kfinish" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| kfinish) => `(tactic| kfinish [Effect.ofWrites])
  | `(tactic| kfinish [$xs,*]) =>
    `(tactic| (constructor <;>
      simp [Kernel.spec, Kernel.eff, Kernel.input, Kernel.readFails, rmRd, rmVal, rm8Rd,
        rm8Val, Effect.ofWrites, szDst, narrowDst, rm8Dst, leWord, breg_write,
        writeAll_nil, writeAll_single, regAfter_mk_nil, regAfter_mk_one, regAfter_mk_pair,
        storeN_eq, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, State.read_write,
        Silmaril.X86.Ext.writeByte, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Narrow.bytes,
        sz_d_bytes, sz_q_bytes, Silmaril.X86.Ext.narrowMask, $xs,*, *]))

/-- Close an `unspecified` goal for a kernel form from a fault hypothesis. -/
syntax "kbadfinish" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| kbadfinish [$xs,*]) =>
    `(tactic| simp [Kernel.spec, Kernel.bad, Kernel.eff, Kernel.input, Kernel.readFails, rmRd,
        rmVal, rm8Rd, rm8Val, Effect.ofWrites, szDst, narrowDst, rm8Dst, leWord, breg_write,
        writeAll_nil, writeAll_single, storeN_eq, Silmaril.X86.Ext.Sz.write,
        Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.writeByte, Silmaril.X86.Ext.Narrow.bits,
        Silmaril.X86.Ext.Narrow.bytes, sz_d_bytes, sz_q_bytes, Silmaril.X86.Ext.narrowMask,
        $xs,*, *])

/-- Simplify an `Ext9` execution hypothesis. -/
syntax "ksimp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? "at" ident : tactic
macro_rules
  | `(tactic| ksimp [$xs,*] at $h) =>
    `(tactic| simp [nextOf_fold, retire_eq_ok, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec,
        Silmaril.X86.Ext.exec, readRM, writeRM, readNarrow, writeNarrow,
        writeRM8, loadN, storeN_eq, breg_write, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read,
        Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Narrow.bytes,
        sz_d_bytes, sz_q_bytes, Silmaril.X86.Ext.narrowMask, $xs,*] at $h:ident)

/-- **The per-form tactic.** Case on the result of `Ext9`; on a success, split on the bytes
the kernel reads (`on`, the kernel's `input`) and optionally on an operand (`splitting`),
substitute the successor and close `Admits`; on a fault, show the kernel is `bad`. -/
syntax "kall" "[" Lean.Parser.Tactic.simpLemma,* "]" "on" term ("splitting" ident)? : tactic
macro_rules
  | `(tactic| kall [$xs,*] on $inp) =>
    `(tactic| (refine sem_of fun r hx => ?_; cases r <;>
      first
        | (apply sem_ok
           cases hb : $inp <;>
            simp only [Kernel.input, rmRd, rm8Rd, $xs,*, Option.bind_some, Option.bind_none,
              reduceCtorEq] at hb <;>
            ksimp [hb, $xs,*] at hx <;> casesm* _ ∧ _, ∃ _, _ <;> subst_vars <;>
            kfinish [hb, $xs,*])
        | (apply sem_bad
           cases hb : $inp <;>
            simp only [Kernel.input, rmRd, rm8Rd, $xs,*, Option.bind_some, Option.bind_none,
              reduceCtorEq] at hb <;>
            ksimp [hb, $xs,*] at hx <;> kbadfinish [hb, $xs,*])))
  | `(tactic| kall [$xs,*] on $inp splitting $d) =>
    `(tactic| (refine sem_of fun r hx => ?_; cases r <;>
      first
        | (apply sem_ok
           cases hb : $inp <;> cases $d:ident <;>
            simp only [Kernel.input, rmRd, rm8Rd, $xs,*, Option.bind_some, Option.bind_none,
              reduceCtorEq] at hb <;>
            ksimp [hb, $xs,*] at hx <;> casesm* _ ∧ _, ∃ _, _ <;> subst_vars <;>
            kfinish [hb, $xs,*])
        | (apply sem_bad
           cases hb : $inp <;> cases $d:ident <;>
            simp only [Kernel.input, rmRd, rm8Rd, $xs,*, Option.bind_some, Option.bind_none,
              reduceCtorEq] at hb <;>
            ksimp [hb, $xs,*] at hx <;> kbadfinish [hb, $xs,*])))

/-- The executor of an `Ext9` form. -/
abbrev ex (i : Silmaril.X86.Ext9.Instr) : State → Memory → Nat → Result :=
  fun c m l => Silmaril.X86.Ext9.exec i c m l

/-- A form allows every result of an executor. -/
abbrev Allows (F : EffSpec) (x : State → Memory → Nat → Result) : Prop :=
  ∀ c m l, F.toFormSpec.sem c m l (x c m l)

/-! ## Moves -/

theorem allows_mov (sz : Sz) (dst : RM) (src : Reg):
    Allows (movK sz dst src).spec
      (ex (.ext8 (.base (.mov sz dst src)))) := by
  intro c m l
  kall [movK] on (movK sz dst src).input c m l splitting dst

theorem allows_movI (sz : Sz) (dst : RM) (imm : BitVec 32):
    Allows (movIK sz dst imm).spec
      (ex (.ext8 (.base (.movI sz dst imm)))) := by
  intro c m l
  kall [movIK] on (movIK sz dst imm).input c m l splitting dst

theorem allows_movI16 (dst : RM) (imm : BitVec 16):
    Allows (movI16K dst imm).spec
      (ex (.ext8 (.base (.movI16 dst imm)))) := by
  intro c m l
  kall [movI16K] on (movI16K dst imm).input c m l splitting dst

theorem allows_mov8 (dst : Reg) (src : RM):
    Allows (mov8K dst src).spec
      (ex (.ext8 (.base (.mov8 dst src)))) := by
  intro c m l
  kall [mov8K] on (mov8K dst src).input c m l splitting src

theorem allows_movI8 (dst : RM) (imm : BitVec 8):
    Allows (movI8K dst imm).spec
      (ex (.ext8 (.base (.movI8 dst imm)))) := by
  intro c m l
  kall [movI8K] on (movI8K dst imm).input c m l splitting dst

theorem allows_movI32 (dst : Reg) (imm : BitVec 32):
    Allows (movI32K dst imm).spec
      (ex (.ext8 (.base (.movI32 dst imm)))) := by
  intro c m l
  kall [movI32K] on (movI32K dst imm).input c m l

theorem allows_movabs (dst : Reg) (imm : BitVec 64):
    Allows (movabsK dst imm).spec
      (ex (.ext8 (.base (.movabs dst imm)))) := by
  intro c m l
  kall [movabsK] on (movabsK dst imm).input c m l

theorem allows_movx (sx : Bool) (sz : Sz) (n : Narrow) (dst : Reg) (src : RM):
    Allows (movxK sx sz n dst src).spec
      (ex (.ext8 (.base (.movx sx sz n dst src)))) := by
  intro c m l
  kall [movxK] on (movxK sx sz n dst src).input c m l splitting src

theorem allows_movsxd (dst : Reg) (src : RM):
    Allows (movsxdK dst src).spec
      (ex (.ext8 (.base (.movsxd dst src)))) := by
  intro c m l
  kall [movsxdK] on (movsxdK dst src).input c m l splitting src

theorem allows_lea (sz : Sz) (dst : Reg) (src : Silmaril.X86.Ext.Mem):
    Allows (leaK sz dst src).spec
      (ex (.ext8 (.base (.lea sz dst src)))) := by
  intro c m l
  kall [leaK] on (leaK sz dst src).input c m l

theorem allows_load (sz : Sz) (dst : Reg) (src : Silmaril.X86.Ext.Mem):
    Allows (loadK sz dst src).spec
      (ex (.ext8 (.base (.load sz dst src)))) := by
  intro c m l
  kall [loadK] on (loadK sz dst src).input c m l

theorem allows_store (n : Narrow) (dst : RM) (src : Reg):
    Allows (storeK n dst src).spec
      (ex (.ext8 (.base (.store n dst src)))) := by
  intro c m l
  kall [storeK] on (storeK n dst src).input c m l splitting dst

/-! ## ALU and tests -/

theorem allows_alu (sz : Sz) (op : AluOp) (dst : RM) (src : Reg):
    Allows (aluK sz op dst (fun c => sz.read c src)).spec
      (ex (.ext8 (.base (.alu sz op dst src)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [aluK] on (aluK sz .cmp dst (fun c => sz.read c src)).input c m l splitting dst
  · kall [aluK, hop] on (aluK sz op dst (fun c => sz.read c src)).input c m l splitting dst

theorem allows_aluI (sz : Sz) (op : AluOp) (dst : RM) (imm : BitVec 32):
    Allows (aluK sz op dst (fun _ => imm.signExtend sz.bits)).spec
      (ex (.ext8 (.base (.aluI sz op dst imm)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [aluK] on (aluK sz .cmp dst (fun _ => imm.signExtend sz.bits)).input c m l splitting dst
  · kall [aluK, hop] on (aluK sz op dst (fun _ => imm.signExtend sz.bits)).input c m l splitting dst

theorem allows_aluI8 (sz : Sz) (op : AluOp) (dst : RM) (imm : BitVec 8):
    Allows (aluK sz op dst (fun _ => imm.signExtend sz.bits)).spec
      (ex (.ext8 (.base (.aluI8 sz op dst imm)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [aluK] on (aluK sz .cmp dst (fun _ => imm.signExtend sz.bits)).input c m l splitting dst
  · kall [aluK, hop] on (aluK sz op dst (fun _ => imm.signExtend sz.bits)).input c m l splitting dst

theorem allows_aluA (sz : Sz) (op : AluOp) (imm : BitVec 32):
    Allows (aluK sz op (.reg .rax) (fun _ => imm.signExtend sz.bits)).spec
      (ex (.ext8 (.base (.aluA sz op imm)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [aluK] on (aluK sz .cmp (.reg .rax) (fun _ => imm.signExtend sz.bits)).input c m l
  · kall [aluK, hop] on (aluK sz op (.reg .rax) (fun _ => imm.signExtend sz.bits)).input c m l

theorem allows_aluR (sz : Sz) (op : AluOp) (dst : Reg) (src : RM):
    Allows (aluRK sz op dst src).spec
      (ex (.ext8 (.base (.aluR sz op dst src)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [aluRK, Silmaril.X86.Ext.aluStepR] on (aluRK sz .cmp dst src).input c m l splitting src
  · kall [aluRK, Silmaril.X86.Ext.aluStepR, hop] on (aluRK sz op dst src).input c m l splitting src

theorem allows_test (sz : Sz) (dst : RM) (src : Reg):
    Allows (flagRMK sz.bits sz.bytes dst (fun c x => logicFlagsN (x &&& sz.read c src))).spec
      (ex (.ext8 (.base (.test sz dst src)))) := by
  intro c m l
  kall [flagRMK] on (flagRMK sz.bits sz.bytes dst (fun c x => logicFlagsN (x &&& sz.read c src))).input c m l splitting dst

theorem allows_test8 (dst : RM) (src : Reg):
    Allows (flagRMK 8 1 dst (fun c x => logicFlagsN (x &&& (c.read src).setWidth 8))).spec
      (ex (.ext8 (.base (.test8 dst src)))) := by
  intro c m l
  kall [flagRMK] on (flagRMK 8 1 dst (fun c x => logicFlagsN (x &&& (c.read src).setWidth 8))).input c m l splitting dst

theorem allows_testI8 (dst : RM) (imm : BitVec 8):
    Allows (flagRMK 8 1 dst (fun _ x => logicFlagsN (x &&& imm))).spec
      (ex (.ext8 (.base (.testI8 dst imm)))) := by
  intro c m l
  kall [flagRMK] on (flagRMK 8 1 dst (fun _ x => logicFlagsN (x &&& imm))).input c m l splitting dst

theorem allows_cmpI8 (dst : RM) (imm : BitVec 8):
    Allows (flagRMK 8 1 dst (fun _ x => subFlagsN x imm)).spec
      (ex (.ext8 (.base (.cmpI8 dst imm)))) := by
  intro c m l
  kall [flagRMK] on (flagRMK 8 1 dst (fun _ x => subFlagsN x imm)).input c m l splitting dst

theorem allows_testA8 (imm : BitVec 8):
    Allows (flagRegK (fun c => logicFlagsN ((c.read .rax).setWidth 8 &&& imm))).spec
      (ex (.ext8 (.base (.testA8 imm)))) := by
  intro c m l
  kall [flagRegK] on (flagRegK (fun c => logicFlagsN ((c.read .rax).setWidth 8 &&& imm))).input c m l

theorem allows_cmpA8 (imm : BitVec 8):
    Allows (flagRegK (fun c => subFlagsN ((c.read .rax).setWidth 8) imm)).spec
      (ex (.ext8 (.base (.cmpA8 imm)))) := by
  intro c m l
  kall [flagRegK] on (flagRegK (fun c => subFlagsN ((c.read .rax).setWidth 8) imm)).input c m l

theorem allows_testA (sz : Sz) (imm : BitVec 32):
    Allows (flagRegK (fun c => logicFlagsN (sz.read c .rax &&& imm.signExtend sz.bits))).spec
      (ex (.ext8 (.base (.testA sz imm)))) := by
  intro c m l
  kall [flagRegK] on (flagRegK (fun c => logicFlagsN (sz.read c .rax &&& imm.signExtend sz.bits))).input c m l

theorem allows_incdec (sz : Sz) (dec : Bool) (dst : RM):
    Allows (incdecK sz dec dst).spec
      (ex (.ext8 (.base (.incdec sz dec dst)))) := by
  intro c m l
  kall [incdecK] on (incdecK sz dec dst).input c m l splitting dst

theorem allows_neg (sz : Sz) (dst : RM):
    Allows (negK sz dst).spec
      (ex (.ext8 (.base (.unary sz .neg dst)))) := by
  intro c m l
  kall [negK] on (negK sz dst).input c m l splitting dst

theorem allows_not (sz : Sz) (dst : RM):
    Allows (notK sz dst).spec
      (ex (.ext8 (.base (.unary sz .not dst)))) := by
  intro c m l
  kall [notK] on (notK sz dst).input c m l splitting dst

theorem allows_shift (sz : Sz) (op : ShiftOp) (dst : RM) (count : Count):
    Allows (shiftK sz op dst count).spec
      (ex (.ext8 (.base (.shift sz op dst count)))) := by
  intro c m l
  kall [shiftK] on (shiftK sz op dst count).input c m l splitting dst

theorem allows_bswap (sz : Sz) (dst : Reg):
    Allows (bswapK sz dst).spec
      (ex (.ext8 (.base (.bswap sz dst)))) := by
  intro c m l
  kall [bswapK] on (bswapK sz dst).input c m l

theorem allows_cxd (sz : Sz):
    Allows (cxdK sz).spec
      (ex (.ext8 (.base (.cxd sz)))) := by
  intro c m l
  kall [cxdK] on (cxdK sz).input c m l

theorem allows_cxe (sz : Sz):
    Allows (cxeK sz).spec
      (ex (.ext8 (.base (.cxe sz)))) := by
  intro c m l
  cases sz
  · kall [cxeK] on (cxeK .d).input c m l
  · kall [cxeK] on (cxeK .q).input c m l

theorem allows_nop (len : Fin 15):
    Allows (nopK).spec
      (ex (.ext8 (.base (.nop len)))) := by
  intro c m l
  kall [nopK] on (nopK).input c m l

theorem allows_endbr64 :
    Allows (nopK).spec
      (ex (.ext8 (.base (.endbr64)))) := by
  intro c m l
  kall [nopK] on (nopK).input c m l

/-! ## `Ext8` byte forms -/

section Ext8
open Silmaril.X86.Ext8 (RM8 BReg alu8 execNew)

theorem allows_new8_alu (op : AluOp) (dst : RM8) (src : BReg):
    Allows (alu8K op dst src.read).spec
      (ex (.ext8 (.new (.alu op dst src)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [alu8K, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.execNew] on (alu8K .cmp dst src.read).input c m l splitting dst
  · kall [alu8K, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.execNew, hop] on (alu8K op dst src.read).input c m l splitting dst

theorem allows_new8_aluA (op : AluOp) (imm : BitVec 8):
    Allows (alu8K op (.reg (.low .rax)) (fun _ => imm)).spec
      (ex (.ext8 (.new (.aluA op imm)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [alu8K, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.execNew] on (alu8K .cmp (.reg (.low .rax)) (fun _ => imm)).input c m l
  · kall [alu8K, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.execNew, hop] on (alu8K op (.reg (.low .rax)) (fun _ => imm)).input c m l

theorem allows_new8_aluI (op : AluOp) (dst : RM8) (imm : BitVec 8):
    Allows (alu8K op dst (fun _ => imm)).spec
      (ex (.ext8 (.new (.aluI op dst imm)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [alu8K, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.execNew] on (alu8K .cmp dst (fun _ => imm)).input c m l splitting dst
  · kall [alu8K, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.execNew, hop] on (alu8K op dst (fun _ => imm)).input c m l splitting dst

theorem allows_new8_aluR (op : AluOp) (dst : BReg) (src : RM8):
    Allows (alu8RK op dst src).spec
      (ex (.ext8 (.new (.aluR op dst src)))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [alu8RK, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.execNew] on (alu8RK .cmp dst src).input c m l splitting src
  · kall [alu8RK, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.execNew, hop] on (alu8RK op dst src).input c m l splitting src

theorem allows_new8_test (dst : RM8) (src : BReg):
    Allows (test8K dst src.read).spec
      (ex (.ext8 (.new (.test dst src)))) := by
  intro c m l
  kall [test8K, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.execNew] on (test8K dst src.read).input c m l splitting dst

theorem allows_new8_shift (op : ShiftOp) (dst : RM8) (count : Count):
    Allows (shift8K op dst count).spec
      (ex (.ext8 (.new (.shift op dst count)))) := by
  intro c m l
  by_cases hn : (count.raw c).toNat % 32 = 0
  · kall [shift8K, Silmaril.X86.Ext8.execNew, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, hn]
      on (shift8K op dst count).input c m l splitting dst
  · kall [shift8K, Silmaril.X86.Ext8.execNew, Silmaril.X86.Ext8.RM8.read, Silmaril.X86.Ext8.RM8.write, hn]
      on (shift8K op dst count).input c m l splitting dst

theorem allows_new8_mov (dst : RM8) (src : BReg):
    Allows (mov8bK dst src).spec
      (ex (.ext8 (.new (.mov dst src)))) := by
  intro c m l
  kall [mov8bK, Silmaril.X86.Ext8.execNew, Silmaril.X86.Ext8.RM8.write] on (mov8bK dst src).input c m l splitting dst

theorem allows_new8_movR (dst : BReg) (src : RM8):
    Allows (mov8RK dst src).spec
      (ex (.ext8 (.new (.movR dst src)))) := by
  intro c m l
  kall [mov8RK, Silmaril.X86.Ext8.execNew, Silmaril.X86.Ext8.RM8.read] on (mov8RK dst src).input c m l splitting src

theorem allows_new8_movx (sx : Bool) (sz : Sz) (dst : Reg) (src : RM8):
    Allows (movx8K sx sz dst src).spec
      (ex (.ext8 (.new (.movx sx sz dst src)))) := by
  intro c m l
  kall [movx8K, Silmaril.X86.Ext8.execNew, Silmaril.X86.Ext8.RM8.read] on (movx8K sx sz dst src).input c m l splitting src

end Ext8

/-! ## `Ext9` 16-bit forms -/

section Ext9
open Silmaril.X86.Ext8 (RM8)

theorem allows_new9_alu16 (op : AluOp) (dst : RM) (src : Reg):
    Allows (alu16K op dst (fun c => (c.read src).setWidth 16)).spec
      (ex (.new (.alu16 op dst src))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [alu16K, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.alu16] on (alu16K .cmp dst (fun c => (c.read src).setWidth 16)).input c m l splitting dst
  · kall [alu16K, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.alu16, hop] on (alu16K op dst (fun c => (c.read src).setWidth 16)).input c m l splitting dst

theorem allows_new9_alu16I (op : AluOp) (dst : RM) (imm : BitVec 16):
    Allows (alu16K op dst (fun _ => imm)).spec
      (ex (.new (.alu16I op dst imm))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [alu16K, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.alu16] on (alu16K .cmp dst (fun _ => imm)).input c m l splitting dst
  · kall [alu16K, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.alu16, hop] on (alu16K op dst (fun _ => imm)).input c m l splitting dst

theorem allows_new9_alu16A (op : AluOp) (imm : BitVec 16):
    Allows (alu16K op (.reg .rax) (fun _ => imm)).spec
      (ex (.new (.alu16A op imm))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [alu16K, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.alu16] on (alu16K .cmp (.reg .rax) (fun _ => imm)).input c m l
  · kall [alu16K, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.alu16, hop] on (alu16K op (.reg .rax) (fun _ => imm)).input c m l

theorem allows_new9_alu16R (op : AluOp) (dst : Reg) (src : RM):
    Allows (alu16RK op dst src).spec
      (ex (.new (.alu16R op dst src))) := by
  intro c m l
  by_cases hop : op = .cmp
  · subst hop; kall [alu16RK, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.alu16] on (alu16RK .cmp dst src).input c m l splitting src
  · kall [alu16RK, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.alu16, hop] on (alu16RK op dst src).input c m l splitting src

theorem allows_new9_test16 (dst : RM) (src : Reg):
    Allows (flagRMK 16 2 dst (fun c x => logicFlagsN (x &&& (c.read src).setWidth 16))).spec
      (ex (.new (.test16 dst src))) := by
  intro c m l
  kall [flagRMK, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.test16] on (flagRMK 16 2 dst (fun c x => logicFlagsN (x &&& (c.read src).setWidth 16))).input c m l splitting dst

theorem allows_new9_test16I (dst : RM) (imm : BitVec 16):
    Allows (flagRMK 16 2 dst (fun _ x => logicFlagsN (x &&& imm))).spec
      (ex (.new (.test16I dst imm))) := by
  intro c m l
  kall [flagRMK, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.test16] on (flagRMK 16 2 dst (fun _ x => logicFlagsN (x &&& imm))).input c m l splitting dst

theorem allows_new9_test16A (imm : BitVec 16):
    Allows (flagRegK (fun c => logicFlagsN ((c.read .rax).setWidth 16 &&& imm))).spec
      (ex (.new (.test16A imm))) := by
  intro c m l
  kall [flagRegK, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext9.test16] on (flagRegK (fun c => logicFlagsN ((c.read .rax).setWidth 16 &&& imm))).input c m l

theorem allows_new9_testI (sz : Sz) (dst : RM) (imm : BitVec 32):
    Allows (flagRMK sz.bits sz.bytes dst (fun _ x => logicFlagsN (x &&& imm.signExtend sz.bits))).spec
      (ex (.new (.testI sz dst imm))) := by
  intro c m l
  kall [flagRMK, Silmaril.X86.Ext9.execNew] on (flagRMK sz.bits sz.bytes dst (fun _ x => logicFlagsN (x &&& imm.signExtend sz.bits))).input c m l splitting dst

theorem allows_new9_testI8 (dst : RM8) (imm : BitVec 8):
    Allows (test8K dst (fun _ => imm)).spec
      (ex (.new (.testI8 dst imm))) := by
  intro c m l
  kall [test8K, Silmaril.X86.Ext9.execNew, Silmaril.X86.Ext8.RM8.read] on (test8K dst (fun _ => imm)).input c m l splitting dst

end Ext9

/-! ## Dispatch -/

/-- **Every `Ext` form of `Int` allows every result of `Ext9`.** -/
theorem allows_specExt {i : Silmaril.X86.Ext.Instr} {F : EffSpec} (h : specExt i = some F) :
    Allows F (ex (.ext8 (.base i))) := by
  cases i <;> simp only [specExt, Option.some.injEq, reduceCtorEq] at h
  case mov => subst h; exact allows_mov _ _ _
  case movI => subst h; exact allows_movI _ _ _
  case movI16 => subst h; exact allows_movI16 _ _
  case mov8 => subst h; exact allows_mov8 _ _
  case movI8 => subst h; exact allows_movI8 _ _
  case movI32 => subst h; exact allows_movI32 _ _
  case movabs => subst h; exact allows_movabs _ _
  case load => subst h; exact allows_load _ _ _
  case store => subst h; exact allows_store _ _ _
  case movx => subst h; exact allows_movx _ _ _ _ _
  case movsxd => subst h; exact allows_movsxd _ _
  case lea => subst h; exact allows_lea _ _ _
  case alu => subst h; exact allows_alu _ _ _ _
  case aluR => subst h; exact allows_aluR _ _ _ _
  case aluI => subst h; exact allows_aluI _ _ _ _
  case aluI8 => subst h; exact allows_aluI8 _ _ _ _
  case aluA => subst h; exact allows_aluA _ _ _
  case test => subst h; exact allows_test _ _ _
  case test8 => subst h; exact allows_test8 _ _
  case testI8 => subst h; exact allows_testI8 _ _
  case testA8 => subst h; exact allows_testA8 _
  case cmpI8 => subst h; exact allows_cmpI8 _ _
  case cmpA8 => subst h; exact allows_cmpA8 _
  case testA => subst h; exact allows_testA _ _
  case incdec => subst h; exact allows_incdec _ _ _
  case shift => subst h; exact allows_shift _ _ _ _
  case bswap => subst h; exact allows_bswap _ _
  case cxd => subst h; exact allows_cxd _
  case cxe => subst h; exact allows_cxe _
  case nop => subst h; exact allows_nop _
  case endbr64 => subst h; exact allows_endbr64
  case unary op _ =>
    cases op <;> simp only [Option.some.injEq] at h <;> subst h
    · exact allows_neg _ _
    · exact allows_not _ _

/-- **Every `Ext8` byte form of `Int` allows every result of `Ext9`.** -/
theorem allows_specNew8 {i : Silmaril.X86.Ext8.New} {F : EffSpec} (h : specNew8 i = some F) :
    Allows F (ex (.ext8 (.new i))) := by
  cases i <;> simp only [specNew8, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact allows_new8_alu _ _ _
  · exact allows_new8_aluR _ _ _
  · exact allows_new8_aluA _ _
  · exact allows_new8_aluI _ _ _
  · exact allows_new8_test _ _
  · exact allows_new8_shift _ _ _
  · exact allows_new8_mov _ _
  · exact allows_new8_movR _ _
  · exact allows_new8_movx _ _ _ _

/-- **Every `Ext9` 16-bit and immediate-TEST form of `Int` allows every result of `Ext9`.** -/
theorem allows_specNew9 {i : Silmaril.X86.Ext9.New} {F : EffSpec} (h : specNew9 i = some F) :
    Allows F (ex (.new i)) := by
  cases i <;> simp only [specNew9, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact allows_new9_alu16 _ _ _
  · exact allows_new9_alu16R _ _ _
  · exact allows_new9_alu16I _ _ _
  · exact allows_new9_alu16A _ _
  · exact allows_new9_test16 _ _
  · exact allows_new9_test16I _ _
  · exact allows_new9_test16A _
  · exact allows_new9_testI _ _ _
  · exact allows_new9_testI8 _ _

/-- **Every `Int` form allows every result of `Ext9`** (`Task.intAllows`). -/
theorem allowsExec_int : Silmaril.X86.Exact.Task.intAllows := by
  intro i F h
  rcases i with (j | j) | j
  · exact allows_specExt h
  · exact allows_specNew8 h
  · exact allows_specNew9 h

end Silmaril.Proofs.X86.Exact.Int
