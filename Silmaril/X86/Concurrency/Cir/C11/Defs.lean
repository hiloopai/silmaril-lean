module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.Concurrency.Cir.Rc11.Defs

/-!
# C11 litmus tests on CIR: definitions

A C11 litmus test is a C program compiled by gcc or clang (`examples/litmus-c/`),
translation-validated into CIR with
the **C11 modes of its source** (the checker, `Cir.Tv`), and checked against RC11 on CIR.

## The test (`C11Test`)

* `tv`: the x86 test (the object's relocated bytes, its locations, the condition on the result
  slots, the x86 verdicts recorded by the x86 litmus tool) with one TV certificate per thread. The
  certificate's CIR statements carry the modes of the C11 accesses (from the sidecar
  `c11-meta.json`); `tvRun` checks the operations against the bytes up to modes.
* `expected`: the C11 verdict recorded by hand for the source (`racy` for the plain
  variants).
* `stronger`: whether x86 is strictly stronger than RC11 on this test (XL forbids the witness and
  RC11 allows it), as recorded by the proposer and **checked**.

## The mode-mapping check (`modesOk`)

TV compares statements up to modes, so on its own it says nothing about C11. `modesOk` checks
that every mode is one the x86 instruction implements under the standard C11 → x86-TSO mapping
(the one both compilers use): a plain `mov` load has mode `na`, `rlx`, `acq` or `sc`; a
plain `mov` store `na`, `rlx` or `rel` (never `sc`: an `sc` store must be `xchg` or a locked
instruction); a locked instruction any atomic mode; an unlocked read-modify-write is two `na`
accesses. A seq_cst fence is `mfence` or a locked `or 0` of a non-location (`Rc11` roles).
`fragOk`: every thread is straight-line (`Stmt.c11Frag`), so the roles are static.

## The RC11 check (`flags`)

For every choice of one CIR run per thread (over the x86 test's domain) and every candidate
execution of their units (the litmus `candidates`), the enumerator computes whether the candidate is
XL-consistent (as the litmus judge: TSO, or XL when not tame), TSO-consistent, RC11-consistent with
the program's roles (`Rc11.judge`), racy, and whether its final state satisfies the witness. The
flags of all candidates are or-ed into one number (`flags`, bit meanings at `candFlags`), which
the kernel evaluates once per test. `C11Test.check` requires: no XL-consistent candidate that is
not RC11-consistent (**the compilation is correct on this test, execution by execution**), some
RC11-consistent candidate, the RC11 verdict equal to `expected`, the CIR's XL and TSO verdicts
equal to the recorded x86 ones, and `stronger` as recorded.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.C11

open Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (Test XTrace Byte Verdict units rmwPairs cellsOk candidates
  readsOkB finalAx seqL)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte

/-! ## Modes -/

/-- A mode a plain `mov` load implements. -/
def loadMode (m : Mode) : Bool := m == .na || m == .rlx || m == .acq || m == .sc

/-- A mode a plain `mov` store implements (not `sc`: an `sc` store needs a locked instruction). -/
def storeMode (m : Mode) : Bool := m == .na || m == .rlx || m == .rel

/-- The statements make no memory access. -/
def noAccess (ops : List Stmt) : Bool :=
  ops.all fun
    | .load .. | .store .. | .rmw .. => false
    | _ => true

/-- **The modes of one instruction's statements are implemented by the instruction.** -/
def modeOk1 : Atomic9.Instr → List Stmt → Bool
  | .open9 (.ext8 (.base (.load ..))), [.load _ m ..] => loadMode m
  | .open9 (.ext8 (.base (.mov _ (.mem _) _))), [.store m ..] => storeMode m
  | .open9 (.ext8 (.base (.movI _ (.mem _) _))), [.store m ..] => storeMode m
  | .open9 (.ext8 (.base (.movI8 ..))), [.store m ..] => storeMode m
  | .open9 (.ext8 (.base (.incdec ..))), [.load _ m .., .store m' ..] => m == .na && m' == .na
  | .new (.xchg ..), [.rmw _ m ..] => m != .na
  | .new (.xadd _ true ..), [.rmw _ m ..] => m != .na
  | .new (.cmpxchg _ true ..), [.rmw _ m ..] => m != .na
  | .new (.lockAluI ..), [.rmw _ m ..] => m != .na
  | .new (.lockIncDec ..), [.rmw _ m ..] => m != .na
  | _, ops => noAccess ops

/-- Walk the items and check every instruction's modes. -/
def modesWalk (t : XThread) : Nat → List Item → Bool
  | _, [] => true
  | o, it :: its =>
    match fetchAt t o with
    | some (i, n) => modeOk1 i it.ops && modesWalk t (o + n) its
    | none => false

/-! ## Tests -/

/-- A C11 verdict: allowed, forbidden, or undefined behaviour (a data race). -/
inductive CVerdict where
  | allowed
  | forbidden
  | racy
  deriving DecidableEq, Repr

/-- A C11 litmus test compiled to x86 and validated into CIR. -/
structure C11Test where
  tv : TvTest
  expected : CVerdict
  stronger : Bool

/-- The CIR program. -/
def C11Test.prog (c : C11Test) : Prog := c.tv.prog

/-- Every certificate's modes are implemented by its instructions. -/
def C11Test.modesOk (c : C11Test) : Bool :=
  (List.range c.tv.test.threads.length).all fun k =>
    match c.tv.test.threads[k]? with
    | some th => modesWalk (c.tv.test.xthread k th) 0 (c.tv.cert k).items &&
        noAccess (c.tv.cert k).proOps
    | none => false

/-- Every thread is in the fragment with static roles. -/
def C11Test.fragOk (c : C11Test) : Bool := c.tv.certs.all fun ct => ct.body.c11Frag

/-! ## The enumerator -/

/-- The flags of one candidate, from its XL, TSO, RC11, race and witness Booleans: bit 0, XL but
not RC11; bit 1, RC11 and racy; bit 2, RC11 and the witness; bit 3, XL and the witness; bit 4,
RC11; bit 5, XL; bit 7, TSO and the witness. -/
def flagsOf (xl tso rc racy w : Bool) : Nat :=
  (if xl && !rc then 1 else 0) + (if rc && racy then 2 else 0) + (if rc && w then 4 else 0) +
    (if xl && w then 8 else 0) + (if rc then 16 else 0) + (if xl then 32 else 0) +
    (if tso && w then 128 else 0)

/-- **The flags of one candidate** (`0` if it is not well formed or its reads are wrong; bit 6
if RC11's procedure gave up). Each Boolean is evaluated once (`match`). -/
def candFlags (P : Prog) (t : Test) (trs : List XTrace) (exps : List (List Byte)) (x : Exec) : Nat :=
  if x.Wf && readsOkB t x exps then
    match Rc11.judge (P.roles x) x with
    | some (rc, racy) =>
      match decide x.Tso with
      | true =>
        match t.witness.eval (finalAx t trs x) with
        | true => flagsOf true true rc racy true
        | false => flagsOf true true rc racy false
      | false =>
        match !decide x.Tame && decide x.Xl with
        | true =>
          match t.witness.eval (finalAx t trs x) with
          | true => flagsOf true false rc racy true
          | false => flagsOf true false rc racy false
        | false =>
          match t.witness.eval (finalAx t trs x) with
          | true => flagsOf false false rc racy true
          | false => flagsOf false false rc racy false
    | none => 64
  else 0

/-- The flags of one choice of runs (bit 6 if two units overlap partially). -/
def comboFlags (P : Prog) (t : Test) (trs : List XTrace) : Nat :=
  let us := units trs
  let evs := us.map Prod.fst
  let exps := us.map Prod.snd
  if cellsOk evs then
    (candidates t evs exps (rmwPairs evs)).foldl (fun acc x => acc ||| candFlags P t trs exps x) 0
  else 64

/-- **The flags of every candidate of every choice of runs.** -/
def progFlags (P : Prog) (t : Test) (T : List (List XTrace)) : Nat :=
  (seqL T).foldl (fun acc trs => acc ||| comboFlags P t trs) 0

/-- The flags of a C11 test (over the x86 test's domain). -/
def C11Test.flags (c : C11Test) : Nat :=
  progFlags c.prog c.tv.test (c.prog.traces c.tv.test.domain)

/-- The RC11 verdict of a flag set. -/
def rcVerdict (S : Nat) : CVerdict :=
  if S.testBit 1 then .racy else if S.testBit 2 then .allowed else .forbidden

/-- The verdict of a flag bit. -/
def bitVerdict (S i : Nat) : Verdict := if S.testBit i then .allowed else .forbidden

/-- **The check of a C11 test**: the certificates validate, the modes are implemented,
the program has static roles, and on the flags: RC11's procedure never gave up, every
XL-consistent candidate is RC11-consistent, some candidate is RC11-consistent, the RC11 verdict
is the expected one, the CIR's XL and TSO verdicts are the recorded x86 ones, and `stronger` is
as recorded. -/
def C11Test.check (c : C11Test) : Bool :=
  c.tv.tvOk && c.tv.domOk && c.tv.test.traces.isSome && c.modesOk && c.fragOk &&
    Rc11.force c.flags fun S =>
      !S.testBit 6 && !S.testBit 0 && S.testBit 4 && rcVerdict S == c.expected &&
        bitVerdict S 3 == c.tv.test.xl && some (bitVerdict S 7) == c.tv.test.tso &&
        c.stronger == (S.testBit 2 && !S.testBit 3)

/-! ## What a checked test gives -/

open Silmaril.X86.MemoryModel.Litmus (AxReach ReadsOk Final)

/-- The domain of a test (the x86 test's own value domain). -/
def C11Test.dom (c : C11Test) : List Nat := c.tv.test.domain

/-- The RC11 behaviours of the CIR program. -/
def C11Test.Rc (c : C11Test) (f : Final) : Prop := BehavIn c.prog c.dom c.prog.Rc11 f

/-- The final states of racy RC11-consistent executions of the CIR program. -/
def C11Test.RcRacy (c : C11Test) (f : Final) : Prop := BehavIn c.prog c.dom c.prog.Rc11Racy f

/-- The XL behaviours of the CIR program. -/
def C11Test.Xl (c : C11Test) (f : Final) : Prop := BehavIn c.prog c.dom Exec.Xl f

/-- **An RC11 verdict holds** for a test: racy (some RC11-consistent execution has a data race:
undefined behaviour), or race-free with the witness allowed or forbidden. -/
def CVerdict.Holds (v : CVerdict) (c : C11Test) : Prop :=
  match v with
  | .racy => ∃ f, c.RcRacy f
  | .allowed => (¬ ∃ f, c.RcRacy f) ∧ Verdict.allowed.Holds c.tv.test c.Rc
  | .forbidden => (¬ ∃ f, c.RcRacy f) ∧ Verdict.forbidden.Holds c.tv.test c.Rc

/-- A candidate execution of the CIR program: one run per thread, a well-formed execution over
their units whose reads return the runs' values (`AxReach` without a model). -/
def C11Test.IsCand (c : C11Test) (x : Exec) : Prop :=
  ∃ trs, List.Forall₂ (· ∈ ·) trs (c.prog.traces c.dom) ∧ x.evs = (units trs).map Prod.fst ∧
    x.rmw = rmwPairs ((units trs).map Prod.fst) ∧ x.Wf = true ∧
    ReadsOk c.tv.test x ((units trs).map Prod.snd)

/-- **What a checked C11 test gives** (`C11Test.holds_of_check`). -/
structure C11Test.Holds (c : C11Test) : Prop where
  /-- Refinement: every x86 behaviour of the bytes, under any model, is a behaviour of
  the CIR program with the same value of the witness. -/
  refines : ∃ T, c.tv.test.traces = some T ∧ ∀ (M : Exec → Prop) f, AxReach c.tv.test T M f →
    ∃ f', BehavIn c.prog c.dom M f' ∧ c.tv.test.witness.eval f' = c.tv.test.witness.eval f
  /-- **The compilation is correct on this test, execution by execution**: every XL-consistent
  candidate execution of the CIR program is RC11-consistent (with the C11 roles of its modes). -/
  xl_rc11 : ∀ x, c.IsCand x → x.Xl → c.prog.Rc11 x
  /-- Hence every XL behaviour is an RC11 behaviour. -/
  xl_sub : ∀ f, c.Xl f → c.Rc f
  /-- **The RC11 verdict is the expected one.** -/
  rc11 : c.expected.Holds c
  /-- Some RC11-consistent execution exists (no verdict holds vacuously). -/
  rc11_some : ∃ f, c.Rc f
  /-- The CIR program's XL verdict is the recorded x86 one. -/
  cir_xl : c.tv.test.xl.Holds c.tv.test c.Xl
  /-- The CIR program's TSO verdict is the recorded x86 one. -/
  cir_tso : ∀ v, c.tv.test.tso = some v → v.Holds c.tv.test (BehavIn c.prog c.dom Exec.Tso)
  /-- **A forbidden RC11 verdict holds for the x86 bytes under XL.** -/
  x86_xl : c.expected = .forbidden → ∃ T, c.tv.test.traces = some T ∧
    Verdict.forbidden.Holds c.tv.test (AxReach c.tv.test T Exec.Xl)
  /-- `stronger` is set exactly when x86 (XL, on CIR) forbids a witness RC11 allows. -/
  stronger : c.stronger = true ↔
    (Verdict.allowed.Holds c.tv.test c.Rc ∧ Verdict.forbidden.Holds c.tv.test c.Xl)

/-! ## The mapping theorem for all CIR programs -/

/-- **Cells**: memory units that share a byte have the same footprint (`cellsOk` as a
property). The units of every choice of CIR runs have cells (`units` splits every access that
overlaps another footprint into bytes; `C11.cells_units`). Without it the execution-level
theorem `C11.tso_rc11` is false: a one-byte store forwarded into a two-byte load closes an
RC11 coherence cycle that TSO allows (`C11.partial_forward_tso`). -/
def Cells (x : Exec) : Prop :=
  ∀ a b : Fin x.n, (x.ev a).isM = true → (x.ev b).isM = true → ∀ y, (x.ev a).covers y = true →
    (x.ev b).covers y = true → (x.ev a).addr = (x.ev b).addr ∧ (x.ev a).size = (x.ev b).size

/-- **The roles respect the x86 mapping** where the proof needs it: an SC event (`E^sc`,
SC fences included) is a memory unit or an `mfence`, and an SC write is locked (an `sc` store
is `xchg` or a locked instruction, never a plain `mov`); an SC fence is an `mfence` or a
locked memory unit (the `lock or 0` idiom). Nothing is needed of release and acquire modes:
on TSO every `po ∪ rfe` path is already ordered. -/
def MapRoles (ro : Nat → Role) (x : Exec) : Prop :=
  ∀ a : Fin x.n, ((ro a.val).sc = true →
      ((x.ev a).isM = true ∨ (x.ev a).isFence .mfence = true) ∧
        ((x.ev a).isW = true → (x.ev a).locked = true)) ∧
    ((ro a.val).isF = true → (x.ev a).isFence .mfence = true ∨ (x.ev a).isA = true)

/-- The modes of a CIR statement respect the standard C11 → x86-TSO mapping read back on CIR:
a plain store is `na`, `rlx` or `rel` (an `sc` store must be a locked read-modify-write); a
plain load is not `rel` or `acqRel`; a read-modify-write is atomic. -/
def _root_.Silmaril.X86.Concurrency.Cir.Stmt.mapOk : Stmt → Bool
  | .load _ m .. => loadMode m
  | .store m .. => storeMode m
  | .rmw _ m .. => m != .na
  | .seq s t => s.mapOk && t.mapOk
  | s => s.c11Frag

/-- The program is in the static-role fragment and its modes respect the mapping. -/
def _root_.Silmaril.X86.Concurrency.Cir.Prog.c11MapOk (P : Prog) : Bool :=
  P.threads.all fun th => th.body.c11Frag && th.body.mapOk

/-- **Compilation to x86-TSO is correct on CIR** (PROVED: `C11.cirTsoRc11`): for a straight-line CIR program whose
modes respect the mapping, every TSO-consistent candidate execution of its runs is
RC11-consistent with the program's roles. This is the theorem of Lahav et al. (PLDI 2017, §5,
the x86-TSO mapping with `sc` stores as locked instructions) restated on CIR's candidates, with
the fence idiom (`lock or 0` of a non-location) as an SC fence.

Plan: `whole` and atomicity are TSO's (`noTwo_of_tso`, `atomicB`); no-thin-air because every
`po ; rfe` path goes from a read to a write, which TSO's `ppo` orders, and `rfi ⊆ po` by uniproc;
coherence because an `hb` path is `po` and `rf` edges ending at acquire reads (every read on
TSO), so `hb ; eco` closes into a `uniproc` or `ghb` cycle; SC because every `E^sc` write is
locked (so `implied` orders it before later reads) and every SC fence is `mfence` or a locked
operation, which puts `psc` inside `ghb⁺`. Per test it is PROVED by enumeration
(`C11Test.Holds.xl_rc11`, which covers XL, equal to TSO on these tame tests). In general it is
PROVED as `C11.cirTsoRc11` from the execution-level `C11.tso_rc11`; the plan above
is the proof's outline except that `rfi ⊆ po` and `rmw ⊆ po` make `hb` a `po ∪ rfe` path, and
the SC part goes through `ghb` extended by `po` edges at `mfence`s. -/
def Task.cirTsoRc11 : Prop :=
  ∀ (P : Prog) (dom : List Nat), (P.threads.all fun th => th.body.c11Frag && th.body.mapOk) →
    ∀ trs, List.Forall₂ (· ∈ ·) trs (P.traces dom) → ∀ x : Exec,
      x.evs = (units trs).map Prod.fst → x.rmw = rmwPairs ((units trs).map Prod.fst) →
      x.Wf = true → x.Tso → P.Rc11 x

end Silmaril.X86.Concurrency.Cir.C11
