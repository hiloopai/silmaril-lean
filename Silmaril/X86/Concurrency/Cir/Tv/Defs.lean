module

public import Silmaril.X86.Concurrency.Cir.Defs

/-!
# Translation validation of x86 threads into CIR: the certificate and the checker

An x86 litmus thread
(`X86.Litmus.Thread`: bytes at a base address, regions, initial core) is translated into a
straight-line CIR thread by an **untrusted** proposer (`tools/litmus-x86 cir`), which also emits a
**certificate** (`Cert`): the CIR statements that stand for the initial registers (`pro`), and
for each x86 instruction, in order, its byte length and the CIR statements it becomes (`Item`).
The CIR thread is `Cert.body`, the concatenation of these statements.

`tvRun t c` checks the certificate against the bytes. It walks the code: at each offset it
decodes one instruction with the fetch (`fetchAt`, the same decoder and slice check as
`Thread.fetch`), checks the length, and checks the instruction against the item's statements
with `chk1`, a table of the supported forms. It returns the final **clobber set**: the
registers whose CIR value may differ from the x86 value (scratch registers that CIR's `rmw`
needs as a destination where x86 writes none). `tvCheck t c := (tvRun t c).isSome`.

The soundness theorem (`Cir.Tv.tvRun_sound`, in `Tv/Thms.lean`): for **every** value domain
whose values fit in 32 bits (a hypothesis only when the thread reads memory), every trace the
extractor gives for the bytes is a run of the CIR thread over the same domain: equal memory
actions up to `normActs` (an unlocked x86 read-modify-write is the CIR load then store, the same
access units), and equal final registers outside the clobber set. `Cir.Tv.TvTest` lifts this to
whole litmus tests and transfers verdicts.
The run-level form (`Cir.Tv.tvRun_xrun`) has no bound on the values: every symbolic
run of the bytes (one `stepSym` branch per step, whatever each read returns) from the initial
core to the end of the code is a run of the CIR thread over any domain holding the values read
(`actVals`).

## Sequential regions

Register-only instructions (`mov r, imm`) become CIR `assign`s: a register-transfer summary that
is deterministic, so it needs no value domain. Summarising an owned sequential region by an
opaque `local(B)` block is done **inside the IR**, not by this checker: `Task.cirLocalize` (proved)
states that replacing a straight-line CIR fragment that alone touches a block footprint by
`local B` is a refinement when `B.spec` holds of the fragment's sequential runs. CIR's `local`
blocks draw their register outputs from the value domain, so a block standing for x86 register
code would make this checker's domain-preserving refinement false.

## The abstract state of the checker

The checker keeps two register sets: `K`, the clobbered registers (CIR and x86 may differ), and
`Z`, registers whose x86 value is known to be below `2^32` (needed only for the 32-bit
`lock cmpxchg`, which on success leaves `rax` alone while CIR's `rmw` writes the zero-extended
old value). The relation it maintains is `Rel K Z rs s`.

A 4-byte read puts its destination in `Z`; an 8-byte read (load, `xchg`, `xadd`, and `rax` for
`cmpxchg`) takes it out. Previously every read put its destination in `Z`, which
holds only when the values read are below `2^32`: the old checker accepted
`mov rax, qword [x]; lock cmpxchg dword [y], ecx`, whose run reading `2^32` from `x` ends with
`rax = 2^32` on x86 and `0` in CIR (`RunEx.qCas`; `Cir.Tv.q_load_unfit`, `qCas_rejected`). With
the change, soundness holds for any value read (`chk1_sound_vals`, `tvRun_xrun`).

## Supported forms (`chk1`)

Memory operands are absolute (`[disp32]`), one base register (`[r + disp32]`, `r` not
clobbered) or RIP-relative, `addrE`. Sizes are 32 and 64 bits (and the one-byte immediate store). Modes are free
(the checker compares statements after `Stmt.demode`); flavours must be write-back.

| x86 | CIR |
| --- | --- |
| `mov m, r` | `store _ k wb a (reg r)` |
| `mov m, imm` / `movb m, imm8` | `store _ k wb a (lit v)` |
| `mov r, m` | `load r _ k wb a` (8 bytes: `r` leaves `Z`) |
| `xchg m, r` | `rmw r _ k xchg a (reg r)` (8 bytes: `r` leaves `Z`) |
| `lock xadd m, r` | `rmw r _ k fadd a (reg r)` (8 bytes: `r` leaves `Z`) |
| `lock cmpxchg m, r` | `rmw rax _ k (cas (reg rax)) a (reg r)` (32-bit: `rax ∈ Z`; 64-bit: `rax` leaves `Z`) |
| `lock add/sub/and/or/xor m, imm` | `rmw d _ k (op o) a (lit v)`, `d` becomes clobbered |
| `lock inc/dec m` | `rmw d _ k (op add/sub) a (lit 1)`, `d` becomes clobbered |
| `inc/dec m` (unlocked) | `load d _ k wb a; store _ k wb a (d ± 1)`, `d` becomes clobbered |
| `mfence`/`lfence`/`sfence` | `fence k` |
| `mov r, imm` (`C7`, `B8+r`, `movabs`) | `assign r (lit v)` (a register-transfer summary) |
| `mov r, r'` | `assign r (r')` at 64 bits, `assign r (r' & 0xffffffff)` at 32 |
| `lea r, m` | `assign r (address of m)`, masked to 32 bits at 32 |

The checker also accepts RIP-relative operands (`[rip + disp32]`, the form compiled C uses for
globals): the
walk passes each instruction the address of the next one (`nx`), so the operand becomes a
literal address.

Anything else fails the check. No branches: the code is straight-line, and the walk must end
exactly at the end of the code.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv

open Silmaril.X86 (State maxInstrLength)
open Silmaril.X86.Ext (Sz)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-- An x86 litmus thread. -/
abbrev XThread := Silmaril.X86.Litmus.Thread

/-- An x86 memory operand. -/
abbrev XMem := Silmaril.X86.Ext.Mem

/-! ## Straight-line CIR -/

/-- A list of statements as one statement: `s₁; (s₂; (...; skip))`. -/
def chain : List Stmt → Stmt
  | [] => .skip
  | s :: l => .seq s (chain l)

/-- Forget the C11 mode of an access (the checker compares statements up to modes; modes are
annotations that do not change the lowered events). -/
def _root_.Silmaril.X86.Concurrency.Cir.Stmt.demode : Stmt → Stmt
  | .load d _ sz fl a => .load d .rlx sz fl a
  | .store _ sz fl a v => .store .rlx sz fl a v
  | .rmw d _ sz op a arg => .rmw d .rlx sz op a arg
  | s => s

/-- The statement may read memory (its runs then depend on the value domain). -/
def _root_.Silmaril.X86.Concurrency.Cir.Stmt.reads : Stmt → Bool
  | .load .. | .rmw .. | .futexWait .. | .local _ => true
  | .seq s t | .ite _ s t => s.reads || t.reads
  | .loop _ _ b => b.reads
  | _ => false

/-- The registers an expression reads. -/
def _root_.Silmaril.X86.Concurrency.Cir.Expr.regs : Expr → List Reg
  | .lit _ => []
  | .reg r => [r]
  | .bin _ a b => a.regs ++ b.regs

/-! ## Actions up to unlocked read-modify-writes -/

/-- An unlocked read-modify-write (`inc m`) is its load then its store; every other action is
itself. Both sides have the same access units (`Cir.Tv.threadUnits_normActs`). -/
def Act.norm (a : XAct) : List XAct :=
  if a.ev.kind = .rmw ∧ a.ev.locked = false then
    [⟨⟨.load, a.ev.addr, a.ev.size, false⟩, a.flavor, a.rd, []⟩,
      ⟨⟨.store, a.ev.addr, a.ev.size, false⟩, a.flavor, [], a.wr⟩]
  else [a]

/-- Normalise a list of actions. -/
def normActs (as : List XAct) : List XAct := as.flatMap Act.norm

/-! ## Operands -/

/-- The 64-bit value of an immediate at size `sz` (sign-extended to the size, then
zero-extended, as `mov` writes it). -/
def immW (sz : Sz) (imm : BitVec 32) : Word := (imm.signExtend sz.bits).setWidth 64

/-- The CIR address of an x86 memory operand, where `nx` is the address of the next
instruction: `[disp32]`, `[r + disp32]` with `r` not clobbered, or `[rip + disp32]` (a
literal, since the checker knows where each instruction is). Other forms (index, FS) are
refused. -/
def addrE (K : List Reg) (nx : Word) (a : XMem) : Option Expr :=
  match a.base, a.index with
  | .none, none => some (.lit (a.disp.signExtend 64).toNat)
  | .reg r, none =>
    if r ∈ K then none else some (.bin .add (.reg r) (.lit (a.disp.signExtend 64).toNat))
  | .rip, none => some (.lit (nx + a.disp.signExtend 64).toNat)
  | _, _ => none

/-- The low 32 bits of a register value, as a CIR mask. -/
def mask32 : Nat := 0xffffffff

/-- The CIR value of a register-to-register move or `lea` at size `sz` of the 64-bit value `e`:
`e` itself at 64 bits, its low 32 bits (zero-extended) at 32 bits. -/
def szE (sz : Sz) (e : Expr) : Expr :=
  match sz with
  | .q => e
  | .d => .bin .and e (.lit mask32)

/-- The CIR operation of a locked ALU operation (`cmp` writes nothing and is refused). -/
def binOf : Silmaril.X86.AluOp → Option BinOp
  | .add => some .add
  | .sub => some .sub
  | .and => some .and
  | .or => some .or
  | .xor => some .xor
  | .cmp => none

/-- Remove a register from a set. -/
def drop (l : List Reg) (r : Reg) : List Reg := l.filter (· ≠ r)

/-! ## One instruction -/

/-- **Check one instruction against its CIR statements** (compared after `demode`), from the
clobber set `K` and the fitting set `Z`; the new sets, or `none`. -/
def chk1 (K Z : List Reg) (nx : Word) (i : Atomic9.Instr) (ops : List Stmt) :
    Option (List Reg × List Reg) :=
  match i, ops.map Stmt.demode with
  | .open9 (.ext8 (.base (.mov sz (.mem a) src))), [.store .rlx k .wb e (.reg r)] =>
    if k = sz.bytes ∧ addrE K nx a = some e ∧ r = src ∧ src ∉ K then some (K, Z) else none
  | .open9 (.ext8 (.base (.movI sz (.mem a) imm))), [.store .rlx k .wb e (.lit c)] =>
    if k = sz.bytes ∧ addrE K nx a = some e ∧ c = (immW sz imm).toNat then some (K, Z) else none
  | .open9 (.ext8 (.base (.movI8 (.mem a) imm))), [.store .rlx k .wb e (.lit c)] =>
    if k = 1 ∧ addrE K nx a = some e ∧ c = imm.toNat then some (K, Z) else none
  | .open9 (.ext8 (.base (.load sz dst a))), [.load d .rlx k .wb e] =>
    if k = sz.bytes ∧ addrE K nx a = some e ∧ d = dst then
      some (drop K dst, if sz = .d then dst :: Z else drop Z dst)
    else none
  | .open9 (.ext8 (.base (.movI sz (.reg dst) imm))), [.assign d (.lit c)] =>
    if d = dst ∧ c = (immW sz imm).toNat then
      some (drop K dst, if c < 2 ^ 32 then dst :: Z else drop Z dst)
    else none
  | .open9 (.ext8 (.base (.incdec sz dec (.mem a)))),
      [.load d .rlx k .wb e, .store .rlx k' .wb e' (.bin o (.reg d') (.lit 1))] =>
    if k = sz.bytes ∧ k' = k ∧ addrE K nx a = some e ∧ e' = e ∧ d' = d ∧ d ∉ e.regs ∧
        o = (if dec then .sub else .add) then
      some (d :: K, drop Z d)
    else none
  | .new (.xchg sz (.mem a) src), [.rmw d .rlx k .xchg e (.reg r)] =>
    if k = sz.bytes ∧ addrE K nx a = some e ∧ r = src ∧ d = src ∧ src ∉ K then
      some (K, if sz = .d then src :: Z else drop Z src)
    else none
  | .new (.xadd sz true (.mem a) src), [.rmw d .rlx k .fadd e (.reg r)] =>
    if k = sz.bytes ∧ addrE K nx a = some e ∧ r = src ∧ d = src ∧ src ∉ K then
      some (K, if sz = .d then src :: Z else drop Z src)
    else none
  | .new (.cmpxchg sz true (.mem a) src), [.rmw d .rlx k (.cas (.reg q)) e (.reg r)] =>
    if k = sz.bytes ∧ addrE K nx a = some e ∧ r = src ∧ d = .rax ∧ q = .rax ∧ src ∉ K ∧
        Silmaril.X86.Reg.rax ∉ K ∧ (sz = .q ∨ Silmaril.X86.Reg.rax ∈ Z) then
      some (K, if sz = .d then Z else drop Z .rax)
    else none
  | .new (.lockAluI sz op a imm), [.rmw d .rlx k (.op o) e (.lit c)] =>
    if k = sz.bytes ∧ addrE K nx a = some e ∧ binOf op = some o ∧ c = (immW sz imm).toNat then
      some (d :: K, drop Z d)
    else none
  | .new (.lockIncDec sz dec a), [.rmw d .rlx k (.op o) e (.lit 1)] =>
    if k = sz.bytes ∧ addrE K nx a = some e ∧ o = (if dec then .sub else .add) then
      some (d :: K, drop Z d)
    else none
  | .open9 (.ext8 (.base (.movI32 dst imm))), [.assign d (.lit c)] =>
    if d = dst ∧ c = imm.toNat then some (drop K dst, dst :: Z) else none
  | .open9 (.ext8 (.base (.movabs dst imm))), [.assign d (.lit c)] =>
    if d = dst ∧ c = imm.toNat then
      some (drop K dst, if c < 2 ^ 32 then dst :: Z else drop Z dst)
    else none
  | .new (.fence f), [.fence f'] => if f = f' then some (K, Z) else none
  | .open9 (.ext8 (.base (.mov sz (.reg dst) src))), [.assign d e] =>
    if d = dst ∧ src ∉ K ∧ e = szE sz (.reg src) then
      some (drop K dst, if sz = .d ∨ src ∈ Z then dst :: Z else drop Z dst)
    else none
  | .open9 (.ext8 (.base (.lea sz dst a))), [.assign d e] =>
    if d = dst ∧ (addrE K nx a).map (szE sz) = some e then
      some (drop K dst, if sz = .d then dst :: Z else drop Z dst)
    else none
  | _, _ => none

/-! ## Certificates -/

/-- One certificate item: an x86 instruction of `len` bytes and the CIR statements it becomes. -/
structure Item where
  len : Nat
  ops : List Stmt

/-- A certificate: the initial registers as CIR assignments (`pro`), and one item per x86
instruction, in order. -/
structure Cert where
  pro : List (Reg × Nat)
  items : List Item

/-- The prologue statements. -/
def Cert.proOps (c : Cert) : List Stmt := c.pro.map fun p => .assign p.1 (.lit p.2)

/-- Some item of the certificate reads memory. -/
def Cert.reads (c : Cert) : Bool := c.items.any fun it => it.ops.any Stmt.reads

/-- The CIR statements of a certificate. -/
def Cert.ops (c : Cert) : List Stmt := c.proOps ++ c.items.flatMap Item.ops

/-- **The CIR thread of a certificate.** -/
def Cert.body (c : Cert) : Stmt := chain c.ops

/-- The registers after the prologue. -/
def Cert.proRegs (c : Cert) : Regs := c.pro.foldl (fun rs p => rs.set p.1 (BitVec.ofNat 64 p.2)) Regs.zero

/-- Every register. -/
def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-! ## The walk -/

/-- Decode the instruction at code offset `o` (as `Thread.fetch` at `rip = base + o`). -/
def fetchAt (t : XThread) (o : Nat) : Option (Atomic9.Instr × Nat) :=
  match Atomic9.decode ((t.code.drop o).take maxInstrLength) with
  | some (i, n) =>
    if o + n ≤ t.code.length ∧ Atomic9.decode ((t.code.drop o).take n) = some (i, n) then
      some (i, n)
    else none
  | none => none

/-- Walk the items from code offset `o`; the final clobber set if every instruction checks and
the walk ends exactly at the end of the code. -/
def walk (t : XThread) : List Reg → List Reg → Nat → List Item → Option (List Reg)
  | K, _, o, [] => if o = t.code.length then some K else none
  | K, Z, o, it :: its =>
    match fetchAt t o with
    | some (i, n) =>
      if 0 < n ∧ n = it.len then
        match chk1 K Z (t.base + BitVec.ofNat 64 (o + n)) i it.ops with
        | some (K', Z') => walk t K' Z' (o + n) its
        | none => none
      else none
    | none => none

/-- The prologue gives the thread's initial registers, and the thread starts at its base. -/
def proOk (t : XThread) (c : Cert) : Bool :=
  t.init.rip == t.base && allRegs.all fun r => t.init.read r == c.proRegs r

/-- **The checker**: the final clobber set, or `none`. -/
def tvRun (t : XThread) (c : Cert) : Option (List Reg) :=
  if proOk t c ∧ t.code.length < 2 ^ 64 then
    walk t [] (allRegs.filter fun r => decide ((c.proRegs r).toNat < 2 ^ 32)) 0 c.items
  else none

/-- **The checker**, as a Boolean. -/
def tvCheck (t : XThread) (c : Cert) : Bool := (tvRun t c).isSome

/-- The values of the reads among a run's actions, as CIR reads them: the little-endian value
of the bytes read (the CIR domain of `tvRun_xrun`). -/
def actVals (acc : List (List XAct)) : List Nat :=
  (acc.flatten.filter fun a => a.ev.kind.reads).map fun a => Silmaril.X86.Ext.leValue a.rd

/-! ## The simulation relation -/

/-- CIR registers `rs` stand for the x86 core `s`: equal outside `K`, and the registers of `Z`
hold values below `2^32`. -/
structure Rel (K Z : List Reg) (rs : Regs) (s : State) : Prop where
  eq : ∀ r, r ∉ K → s.read r = rs r
  fit : ∀ r ∈ Z, (s.read r).toNat < 2 ^ 32

/-! ## Why an 8-byte read leaves the fitting set -/

/-- A one-instruction thread at thread 0's code address of a one-thread test, from a zero core:
`code` placed as the litmus tests place it. -/
def RunEx.thread (code : List Silmaril.X86.Byte) : XThread :=
  ⟨Silmaril.X86.Litmus.codeBase 0, code, Silmaril.X86.Litmus.testRegions 1,
    Silmaril.X86.Litmus.initCore (Silmaril.X86.Litmus.codeBase 0) []⟩

/-- `mov rax, qword [0x10000]` (`48 8B 04 25 00 00 01 00`). -/
def RunEx.qLoad : XThread := RunEx.thread [0x48, 0x8B, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00]

/-- `mov rax, qword [0x10000]; lock cmpxchg dword [0x10008], ecx`. -/
def RunEx.qCas : XThread :=
  RunEx.thread [0x48, 0x8B, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00,
    0xF0, 0x0F, 0xB1, 0x0C, 0x25, 0x08, 0x00, 0x01, 0x00]

/-- `mov eax, dword [0x10000]; lock cmpxchg dword [0x10008], ecx`. -/
def RunEx.dCas : XThread :=
  RunEx.thread [0x8B, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00,
    0xF0, 0x0F, 0xB1, 0x0C, 0x25, 0x08, 0x00, 0x01, 0x00]

/-- The certificate of `qCas` (`k = 8`, load of 8 bytes) or `dCas` (`k = 7`, 4 bytes): the load,
then CIR's `cas` on `rax`. -/
def RunEx.casCert (k sz : Nat) : Cert :=
  ⟨[], [⟨k, [.load .rax .rlx sz .wb (.lit 0x10000)]⟩,
    ⟨9, [.rmw .rax .rlx 4 (.cas (.reg .rax)) (.lit 0x10008) (.reg .rcx)]⟩]⟩

/-- The certificate of `qLoad`: one 8-byte CIR load. -/
def RunEx.qLoadCert : Cert := ⟨[], [⟨8, [.load .rax .rlx 8 .wb (.lit 0x10000)]⟩]⟩

/-! ## Whole litmus tests -/

open Silmaril.X86.MemoryModel.Litmus (Test Cond Atom Model outsBy)

/-- A translation-validated litmus test: a litmus test (bytes, locations, condition, recorded
verdicts) and one certificate per thread. -/
structure TvTest where
  test : Test
  certs : List Cert

/-- The CIR program of a validated test: the test's locations and the certificates' threads. -/
def TvTest.prog (c : TvTest) : Prog := ⟨c.test.locs, c.certs.map fun ct => ⟨ct.body, false⟩⟩

/-- The certificate of thread `k`. -/
def TvTest.cert (c : TvTest) (k : Nat) : Cert := c.certs.getD k ⟨[], []⟩

/-- The clobber set of every thread, if every certificate checks against its thread's bytes
(placed by `Test.xthread`). -/
def TvTest.clobs (c : TvTest) : Option (List (List Reg)) :=
  (c.test.threads.mapIdx fun k th => tvRun (c.test.xthread k th) (c.cert k)).mapM id

/-- No register the condition observes is clobbered. -/
def condAvoids (cond : Cond) (Ks : List (List Reg)) : Bool :=
  cond.atoms.all fun
    | .reg i r _ _ => !(Ks.getD i []).contains r
    | .mem .. => true

/-- **The test-level check**: one certificate per thread, every certificate checks, and the
observed registers are not clobbered. -/
def TvTest.tvOk (c : TvTest) : Bool :=
  c.test.threads.length == c.certs.length &&
    match c.clobs with
    | some Ks => condAvoids c.test.cond Ks
    | none => false

/-- The test's value domain fits in 32 bits, or no thread reads memory (the hypothesis of
`tvRun_sound`). -/
def TvTest.domOk (c : TvTest) : Bool :=
  c.certs.all (fun ct => !ct.reads) || c.test.domain.all fun v => decide (v < 2 ^ 32)

/-- The recorded verdict of a model (the x86 verdict). -/
def TvTest.verdict (c : TvTest) : Model → Silmaril.X86.MemoryModel.Litmus.Verdict
  | .sc => c.test.sc.getD c.test.xl
  | .tso => c.test.tso.getD c.test.xl
  | .xl => c.test.xl

/-- **The CIR verdict check**: the axiomatic enumerator on the CIR program's traces over the
x86 test's own domain gives the recorded SC, TSO and XL verdicts, and some SC execution
exists. -/
def TvTest.cirCheck (c : TvTest) : Bool :=
  match c.test.axJudge (c.prog.traces c.test.domain) with
  | some js =>
    c.verdict .sc == c.test.verdictOf (outsBy js Model.sc.sel) &&
      c.verdict .tso == c.test.verdictOf (outsBy js Model.tso.sel) &&
      c.verdict .xl == c.test.verdictOf (outsBy js Model.xl.sel) &&
      !(outsBy js Model.sc.sel).isEmpty
  | none => false

/-- Every check of a validated test at once (one kernel `decide` per test): the certificates
check, the domain fits, the CIR verdicts are the recorded ones, and the bytes extract. -/
def TvTest.allOk (c : TvTest) : Bool :=
  c.tvOk && c.domOk && c.cirCheck && c.test.traces.isSome

open Silmaril.X86.MemoryModel.Litmus (AxReach Verdict) in
/-- What a validated test gives (`Cir.Tv.TvTest.transfer_of_allOk`). -/
structure TvTest.Transfer (c : TvTest) : Prop where
  /-- **Refinement**: every x86 behaviour of the bytes is a CIR behaviour over the same domain,
  with the same value of the witness. -/
  refines : ∃ T, c.test.traces = some T ∧ ∀ (M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop) f,
    AxReach c.test T M f → ∃ f', BehavIn c.prog c.test.domain M f' ∧
      c.test.witness.eval f' = c.test.witness.eval f
  /-- **The CIR verdicts are the recorded (x86) verdicts.** -/
  cir : ∀ M : Model, (c.verdict M).Holds c.test (BehavIn c.prog c.test.domain M.Holds)
  /-- Some SC behaviour of the CIR program exists, so no verdict is vacuous. -/
  sc_some : ∃ f, BehavIn c.prog c.test.domain Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f
  /-- **Transfer**: every `forbidden` CIR verdict holds for the x86 bytes. -/
  x86_forbidden : ∃ T, c.test.traces = some T ∧ ∀ M : Model, c.verdict M = .forbidden →
    Verdict.forbidden.Holds c.test (AxReach c.test T M.Holds)
  /-- Every `allowed` x86 verdict is an `allowed` CIR verdict. -/
  cir_allowed : ∃ T, c.test.traces = some T ∧ ∀ (M : Model),
    Verdict.allowed.Holds c.test (AxReach c.test T M.Holds) →
      Verdict.allowed.Holds c.test (BehavIn c.prog c.test.domain M.Holds)

/-! ## Summarising owned sequential regions as `local(B)` -/

/-- Two cells are disjoint. -/
def cellsDisjoint (c d : Nat × Nat) : Bool := decide (c.1 + c.2 ≤ d.1) || decide (d.1 + d.2 ≤ c.1)

/-- Every access of the statement is at a literal address disjoint from every cell of `cs`
(an access at a computed address is refused). A literal address is taken modulo `2 ^ 64`, as
`run` evaluates it (`Expr.eval (.lit a) = BitVec.ofNat 64 a`); before the localisation theorem the
check used
the literal itself, so an access at `a + 2 ^ 64` passed as disjoint from a cell at `a`
(`Cir.not_cirLocalize_wrap`). -/
def _root_.Silmaril.X86.Concurrency.Cir.Stmt.avoids (cs : List (Nat × Nat)) : Stmt → Bool
  | .load _ _ sz _ (.lit a) | .store _ sz _ (.lit a) _ | .rmw _ _ sz _ (.lit a) _ =>
    cs.all (cellsDisjoint (a % 2 ^ 64, sz))
  | .futexWait _ (.lit a) _ => cs.all (cellsDisjoint (a % 2 ^ 64, 4))
  | .load .. | .store .. | .rmw .. | .futexWait .. => false
  | .local b => (b.ins ++ b.outs).all fun c => cs.all (cellsDisjoint c)
  | .seq s t | .ite _ s t => s.avoids cs && t.avoids cs
  | .loop _ _ b => b.avoids cs
  | _ => true

/-- The registers a statement may write. -/
def _root_.Silmaril.X86.Concurrency.Cir.Stmt.writes : Stmt → List Reg
  | .assign d _ | .load d .. | .rmw d .. | .futexWait d .. => [d]
  | .local b => b.rout
  | .seq s t | .ite _ s t => s.writes ++ t.writes
  | .loop _ _ b => b.writes
  | _ => []

/-- The footprint of a block is a set of aligned cells of 1, 2, 4 or 8 bytes, any two equal or
disjoint. -/
def _root_.Silmaril.X86.Concurrency.Cir.Block.cellsOk (b : Block) : Bool :=
  let cs := b.ins ++ b.outs
  cs.all (fun c => [1, 2, 4, 8].contains c.2 && c.1 % c.2 == 0) &&
    cs.all fun c => cs.all fun d => c == d || cellsDisjoint c d

/-- Every write of the statement (store or read-modify-write) is at a literal address and is
exactly one of the cells `cs`; a nested block writes only cells of `cs`. -/
def _root_.Silmaril.X86.Concurrency.Cir.Stmt.storesWithin (cs : List (Nat × Nat)) : Stmt → Bool
  | .store _ sz _ (.lit a) _ | .rmw _ _ sz _ (.lit a) _ => cs.contains (a, sz)
  | .store .. | .rmw .. => false
  | .local b => b.outs.all cs.contains
  | .seq s t | .ite _ s t => s.storesWithin cs && t.storesWithin cs
  | .loop _ _ b => b.storesWithin cs
  | _ => true

/-- Every store of the statement is write-back (no non-temporal or string store; read-modify-
writes and block writes are write-back by their lowering). -/
def _root_.Silmaril.X86.Concurrency.Cir.Stmt.wbStores : Stmt → Bool
  | .store _ _ fl _ _ => fl == .wb
  | .seq s t | .ite _ s t => s.wbStores && t.wbStores
  | .loop _ _ b => b.wbStores
  | _ => true

/-- **Localisation** (PROVED: `Cir.cirLocalize`, `Concurrency/Cir/Localize/Thms.lean`):
replacing a straight-line CIR fragment `ops` of thread `i` that touches only the cells of a block
footprint, which no other statement of the program touches, by `local B` is a refinement, when
`B.spec` holds of every sequential run of `ops` and `ops` writes only `B.rout`: every behaviour of
the program is a behaviour of the localised program with the same final memory and registers.
The fragment writes only cells of `B.outs`, is futex-free, and every cell of the footprint lies
inside a location and below the ghost bytes (`ctlAddr 0`). Under XL the statements after the
fragment must not use non-temporal or string stores (`Stmt.wbStores`).

A first statement allowed `ops` to write a cell of `B.ins` that is not in
`B.outs`; the block then never writes it, so the final memory differs and the statement was
**false** (`B.ins = [(a, 4)]`, `B.outs = []`, `ops = [store 4 wb a 1]`, location `a` initially
`0`, `B.spec` true). Similarly a cell of `B.outs` outside every location that `ops` never writes
gains bytes from the block's write-back. Both are excluded now (`Stmt.storesWithin B.outs` and
the location hypothesis).

A second statement was still **false** for fragments with futex
operations. `onCells` and `storesWithin` do not constrain `futexWake a n`, whose lowering
writes the ghost waiter-queue byte `qAddr a` (outside every location); the block never writes
it, so the final memory differs: `ops = [futexWake 0 1]`, `B` with an empty footprint and a
trivial contract, one thread, no locations; the program's only behaviour has `0` at `qAddr 0`,
the localised program's has nothing there (`Cir.not_cirLocalize_futex`). A `futexWait` in the
fragment fails the same way. Fixed by requiring the fragment to be futex-free
(`Stmt.futexFree`); `Carve.footOk` checks it.

A third statement was **false** in three further ways, each
refuted in Lean (`Concurrency/Cir/Localize/Thms.lean`); the hypotheses added below fix them.

* **Ghost bytes** (`Cir.not_cirLocalize_ghost`): `Stmt.avoids` does not see the ghost bytes of
  futex queues, `spawn`/`join` and thread start/end events. With a location at `qAddr 0`, a
  `futexWake 0 1` in another thread empties the queue byte between the fragment's
  `store x 1; load rax x`, so the program reads `rax = 0` while every localised run has
  `rax = 1`. Fixed by requiring every footprint cell to end at or below `ctlAddr 0` (every ghost
  byte is at or above it).
* **Address wrap** (`Cir.not_cirLocalize_wrap`): `run` takes a literal address modulo `2 ^ 64`
  but `avoids` compared the literal; a store at `x + 2 ^ 64` in another thread hits `x`. Fixed
  in `Stmt.avoids`.
* **Weak stores under XL** (`Cir.not_cirLocalize_xlWeak`): the block always writes its out
  cells; under XL that write orders an earlier read before a later non-temporal store through an
  `sfence` (`ppoXl` then `sfenceXl`), an order the fragment did not have when its run wrote
  nothing. `load rax z; [load rbx x]; sfence; store.nt y 1` against `store y 2; store z 1` has
  the XL behaviour `rax = 1, y = 2`, which the localised program forbids. Fixed by requiring,
  under XL only, that `post` stores are write-back (SC and TSO ignore flavours).

Proof (`Silmaril/Proofs/X86/Concurrency/Cir/Localize/`): in a consistent candidate of `P` the
cells are touched only by the fragment's units, so its units, restricted and renumbered, are a
one-thread XL candidate from the initial memory; `oneSem_iff` replays them, which gives a
`SeqRun` of `ops` and so `B.spec`. The localised candidate keeps every other unit (indices and
thread-`i` positions shifted), its `rf` and `co`, and gives the block's reads the initial values
and its writes the coherence-last place on their bytes. Every edge between kept units is an old
edge, and a path through the block's units enters from `pre` and leaves to `post` by
program-order edges, so it is short-cut by an old `po`, `ppo`, `implied`, `mfence` or `lockXl`
edge (the weak-store hypothesis is used exactly here). -/
def Task.cirLocalize : Prop :=
  ∀ (P : Prog) (i : Nat) (pre ops post : List Stmt) (B : Block),
    P.threads[i]? = some ⟨chain (pre ++ ops ++ post), false⟩ →
    B.cellsOk = true →
    (ops.all fun s => s.onCells (B.ins ++ B.outs) && s.storesWithin B.outs && s.threadFree &&
      s.futexFree) = true →
    (∀ c ∈ B.ins ++ B.outs, ∃ l ∈ P.locs, l.addr ≤ c.1 ∧ c.1 + c.2 ≤ l.addr + l.size) →
    (∀ c ∈ B.ins ++ B.outs, c.1 + c.2 ≤ ctlAddr 0) →
    ((pre ++ post).all (Stmt.avoids (B.ins ++ B.outs))) = true →
    (∀ j th, j ≠ i → P.threads[j]? = some th → th.body.avoids (B.ins ++ B.outs) = true) →
    (∀ s ∈ ops, ∀ r ∈ s.writes, r ∈ B.rout) →
    (∀ rs m tr rs' m', SeqRun (chain ops) rs m tr rs' m' →
      B.spec (B.rin.map (fun r => (rs r).toNat) ++ B.ins.map fun c => (m.val c.1 c.2).getD 0)
        (B.rout.map (fun r => (rs' r).toNat) ++ B.outs.map fun c => (m'.val c.1 c.2).getD 0)) →
    ∀ (M : Model) (f : Silmaril.X86.MemoryModel.Litmus.Final),
      (M = .xl → post.all Stmt.wbStores = true) → Behav P M.Holds f →
      ∃ f', Behav ⟨P.locs, P.threads.set i ⟨chain (pre ++ [.local B] ++ post), false⟩⟩ M.Holds f' ∧
        f'.mem = f.mem ∧ f'.regs = f.regs

end Silmaril.X86.Concurrency.Cir.Tv
