module

public import Silmaril.X86.Concurrency.Cir.Tv.CSpawn.Defs
public import Silmaril.X86.Concurrency.Cir.Litmus.Defs
public import Silmaril.X86.Concurrency.Cir.Sync.Defs

/-!
# Spawn/join: mutants and non-vacuity witnesses

Three kinds of check:

* **TV mutants** of the compiled C tests (`mutants`): a dropped or shifted marker cut, a
  certificate checked against the bytes of another program, a relabelled or swapped stub, a
  child no longer marked as spawned, a control given the forbidden verdict. Each must be
  rejected by `CTest.tvOk` or `CTest.allOk`. One entry is *accepted* on purpose: swapping the
  spawn and join stubs of `MP+join` passes `tvOk`. The mark of a cut comes from the stub table,
  which is part of the x86 semantics (`mexplore`) and is trusted. Only the CIR check catches
  the swap, because the join of a thread that is not yet spawned can never complete.
* **The model stays weak under spawn** (`sbKids`, `sbKidsJoin`): SB between two spawned
  children is allowed under TSO and XL and forbidden under SC. This holds whether or not the
  parent then joins both. So spawn orders the parent's prefix before each child, and not the
  children with each other.
* **The hypotheses are satisfiable**: a concrete execution with a `swHb` edge (`swEx`), and a
  concrete event list satisfying `CtlOk` and `OpAx.ThreadsOk` (`esJoin`, the events of
  `MP+join`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv.CSpawnReview

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv Silmaril.X86.Concurrency.Cir.Tv.CSpawn

/-! ## TV mutants -/

/-- Thread `k` of a C test changed by `f`. -/
def setTh (c : CTest) (k : Nat) (f : CThread → CThread) : CTest :=
  { c with threads := c.threads.modify k f }

/-- An empty thread (default for `lateTh`). -/
def emptyTh : CThread :=
  { base := 0, code := [], regions := [], init := Silmaril.X86.Litmus.initCore 0 [], cuts := [] }

/-- Thread 0 of `MP+spawn-late@gcc` (spawn, then store). -/
def lateTh : CThread := match «MP+spawn-late@gcc».threads with
  | t :: _ => t
  | [] => emptyTh

/-- Which check a mutant targets. -/
inductive Check where
  | tv
  | all
  deriving DecidableEq

/-- A C-test mutant: the test, the check, and whether the check must accept. -/
structure CMutant where
  name : String
  test : CTest
  check : Check
  accept : Bool

/-- The mutant gets the expected answer. -/
def CMutant.ok (m : CMutant) : Bool :=
  (match m.check with
    | .tv => m.test.tvOk
    | .all => m.test.allOk) == m.accept

/-- The mutants. -/
def mutants : List CMutant :=
  [ ⟨"MP+spawn@gcc: unchanged (control)", «MP+spawn@gcc», .tv, true⟩,
    ⟨"MP+spawn@gcc: marker cut dropped (the call is walked as x86)",
      setTh «MP+spawn@gcc» 0 fun t => { t with cuts := [] }, .tv, false⟩,
    ⟨"MP+spawn@gcc: certificate against MP+spawn-late's bytes",
      setTh «MP+spawn@gcc» 0 fun _ => lateTh, .tv, false⟩,
    ⟨"MP+spawn@gcc: stub relabelled as join 1",
      { «MP+spawn@gcc» with stubs := [(0x500010, .join 1)] }, .all, false⟩,
    ⟨"MP+spawn@gcc: child not marked spawned",
      setTh «MP+spawn@gcc» 1 fun t => { t with spawned := false }, .all, false⟩,
    ⟨"MP+join@gcc: join cut dropped", setTh «MP+join@gcc» 0 fun t => { t with cuts := [0] },
      .tv, false⟩,
    ⟨"MP+join@gcc: join cut off by one", setTh «MP+join@gcc» 0 fun t => { t with cuts := [0, 6] },
      .tv, false⟩,
    ⟨"MP+join@gcc: spawn and join stubs swapped (tvOk accepts: marks are trusted)",
      { «MP+join@gcc» with stubs := [(0x500810, .spawn 1), (0x500010, .join 1)] }, .tv, true⟩,
    ⟨"MP+join@gcc: spawn and join stubs swapped (allOk rejects)",
      { «MP+join@gcc» with stubs := [(0x500810, .spawn 1), (0x500010, .join 1)] }, .all, false⟩,
    ⟨"MP+spawn-late@gcc: given MP+spawn's forbidden verdict",
      { «MP+spawn-late@gcc» with test := «MP+spawn@gcc».test }, .all, false⟩,
    ⟨"MP+nojoin@gcc: given MP+join's forbidden verdict",
      { «MP+nojoin@gcc» with test := «MP+join@gcc».test }, .all, false⟩ ]

/-! ## Spawn does not make the children sequentially consistent -/

open Lit in
/-- SB between two spawned children: allowed under TSO and XL, forbidden under SC. -/
def sbKids : Silmaril.X86.Concurrency.Cir.CTest :=
  ⟨{ shell "SB+spawn2" "two spawned children run SB"
        (.and (.atom (.reg 1 .rax 32 0)) (.atom (.reg 2 .rax 32 0))) .allowed with
      sc := some .forbidden },
    [th [.spawn 1, .spawn 2], sth [st x 1, ld .rax y], sth [st y 1, ld .rax x]]⟩

open Lit in
/-- SB between two spawned children that the parent joins before reading `x`: still allowed
under TSO and XL. -/
def sbKidsJoin : Silmaril.X86.Concurrency.Cir.CTest :=
  ⟨{ shell "SB+spawn2+join" "two spawned children run SB; the parent joins both"
        (.and (.atom (.reg 1 .rax 32 0)) (.atom (.reg 2 .rax 32 0))) .allowed with
      sc := some .forbidden },
    [th [.spawn 1, .spawn 2, .join 1, .join 2, ld .rax x], sth [st x 1, ld .rax y],
      sth [st y 1, ld .rax x]]⟩

/-! ## Satisfiable hypotheses -/

open Silmaril.X86.MemoryModel.Axiomatic in
/-- An execution with a spawn edge: thread 0 stores `x` and spawns (writes start byte `1`), and
thread 1 starts (reads the `1`) and loads `x`. -/
def swEx : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0x10000, size := 1, data := [1] },
    { tid := 0, pos := 1, act := .write, addr := ctlAddr 1, size := 1, locked := true, data := [1] },
    { tid := 1, pos := 0, act := .read, addr := ctlAddr 1, size := 1, locked := true },
    { tid := 1, pos := 2, act := .read, addr := 0x10000, size := 1 }]
  rf := fun r y =>
    if r = 2 ∧ y = ctlAddr 1 then some 1 else if r = 3 ∧ y = 0x10000 then some 0 else none

open Silmaril.X86.MemoryModel.Tso (XEvent) in
/-- The operational events of `MP+join`: thread 0 spawns, joins and loads `x`; thread 1 starts,
stores `x` and ends. -/
def esJoin : List (List (XEvent Nat)) :=
  [[.rmw 0 (ctlAddr 1) [0] [1], .rmw 0 (endAddr 1) [1] [2], .load 0 0x10000 [0, 0, 0, 0]],
    [.rmw 1 (ctlAddr 1) [1] [2], .store 1 0x10000 [1, 0, 0, 0], .rmw 1 (endAddr 1) [0] [1]]]

end Silmaril.X86.Concurrency.Cir.Tv.CSpawnReview
