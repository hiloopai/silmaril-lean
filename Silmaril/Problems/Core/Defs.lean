module

public import Silmaril.Problems.Basic
public import Silmaril.X86.RelIsa.Defs
public import Silmaril.X86.Concurrency.Lift.Defs
public import Silmaril.X86.MemoryModel.Xl.Defs

/-!
# Problem templates: model classes, correctness, refutation, companions

The quantifier shapes of x86-64 function problems. A problem is a closed `def … : Prop`
(`Silmaril.Problems`, `@[problem "ID"]`) that instantiates one of these templates with
pinned specifications and machines. The machines are relational (`Silmaril.X86.RelIsa`), so
a statement can range over a whole class of machines: every refinement of a loose top
(`Silmaril.X86.Loose`), or one deterministic machine.

**Model classes.**

* `Admissible A C := RelIsa.Le C A ∧ RelIsa.Progress C`: `C` is in the down-set of the loose
  top `A` (fewer behaviours on live states) and has some outcome from every live state
  (`Progress` excludes the empty refinement, which would satisfy every demonic spec).
  These are the models of an x86 signature (`Silmaril.X86.Institution.Model`).
* `Class σ`: a predicate on machines; `Class.below A` (the admissible down-set),
  `Class.single C`, the class order `Class.Sub` and `Class.Inhabited`.

**Correctness (function level).**

* `FnJ S C`: the judgement on one machine, `∀ entry, (S entry).MustTotal C` (satisfaction
  in the institution, `Institution.Sat C S`).
* `FnCorrect 𝓜 S`: `FnJ S` on every member of `𝓜` (demonic).
* `FnCorrectDet I S`: the singleton deterministic form `∀ entry, (S entry).Total I`.
* `FnCorrectUnder I P S`: `Spec.TotalUnder` under every memory model `SC ⊑ M ⊑ XL`.
* `TuCorrect`, `LibCorrect`, `ProcCorrect`: **stubs** that fix only the quantifier prefix over
  an abstract placement, link environment or launch type. The link- and process-level shapes
  are future work.

**Refutation.**

* `Never A Q s`: an invariant of `A` through `s`, disjoint from `Q`, closed under `A`'s
  `ok`-steps (a `stop` is allowed: a fault is also not a correct return). No termination
  measure is needed.
* `RefutesOn 𝓜 ref J` (some-model) and `RefutesAll 𝓜 J` (every-model, with inhabitation).
* `Counterexample σ`: the data a refutation shows humans.

**Companions.** `NonVacuous 𝓜 ref S`, `PostNontrivial S`, and `SpecImplies A B`.

The transfer theorems (`never_refutes`, `fnCorrect_below_of_top`, `mustTotal_mono_sub`, …)
are in `Core/Thms.lean`. Hyperproperty templates (two-run determinism) and a
separation-logic form are not included.

The three `@[problem]` declarations at the end register the generic transfer principles
themselves (IDs `problems/core/…`), so that their statements are dumped and hash-pinned like
any other problem; their solutions are in `Core/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Problems

open Silmaril.X86 (RelIsa Word)
open Silmaril.X86.FnContract (Spec AbiEntry)

/-! ## Model classes -/

/-- An admissible member of the class below a loose top model `A`: fewer behaviours, and some
outcome from every live state (rules out the empty refinement). -/
def Admissible {σ : Type} (A C : RelIsa σ) : Prop := RelIsa.Le C A ∧ RelIsa.Progress C

/-- A model class: a predicate on machines. -/
structure Class (σ : Type) where
  mem : RelIsa σ → Prop

/-- The down-set of admissible refinements of the loose top `A`. -/
def Class.below {σ : Type} (A : RelIsa σ) : Class σ := ⟨Admissible A⟩

/-- The singleton class. -/
def Class.single {σ : Type} (C : RelIsa σ) : Class σ := ⟨(· = C)⟩

/-- `𝓝` is a subclass of `𝓜`. -/
def Class.Sub {σ : Type} (𝓝 𝓜 : Class σ) : Prop := ∀ C, 𝓝.mem C → 𝓜.mem C

/-- The class is inhabited. -/
def Class.Inhabited {σ : Type} (𝓜 : Class σ) : Prop := ∃ C, 𝓜.mem C

/-! ## Function correctness -/

/-- The function judgement on one machine: from every placement `entry`, `S entry` is
demonically totally correct on `C`. -/
def FnJ {σ : Type} (S : Word → Spec σ) (C : RelIsa σ) : Prop :=
  ∀ entry, (S entry).MustTotal C

/-- **Function correctness, demonic, against a model class.** -/
def FnCorrect {σ : Type} (𝓜 : Class σ) (S : Word → Spec σ) : Prop :=
  ∀ C, 𝓜.mem C → FnJ S C

/-- The singleton deterministic form: total correctness on one `SegVC.Isa`. -/
def FnCorrectDet {σ : Type} (I : Silmaril.X86.SegVC.Isa σ) (S : Word → Spec σ) : Prop :=
  ∀ entry, (S entry).Total I

/-- The memory-model axis: total correctness under every model between SC and XL. -/
def FnCorrectUnder {σ : Type} (I : Silmaril.X86.SegVC.Isa σ)
    (P : σ → List Silmaril.X86.MemoryModel.Litmus.XAct → Prop) (S : Word → Spec σ) : Prop :=
  ∀ M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop,
    Silmaril.X86.Concurrency.Cir.MLe Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc M →
    Silmaril.X86.Concurrency.Cir.MLe M Silmaril.X86.MemoryModel.Axiomatic.Exec.Xl →
    ∀ entry, (S entry).TotalUnder I P M

/-- **Stub**: a translation unit's exports, for every valid placement `L : P`. -/
def TuCorrect {σ P : Type} (𝓜 : Class σ) (Valid : P → Prop) (exports : List (P → Word → Spec σ)) :
    Prop :=
  ∀ L, Valid L → ∀ e ∈ exports, FnCorrect 𝓜 (e L)

/-- **Stub**: a library's exports, in every link environment `Γ : E` that meets the import
specs (`Linked Γ`). -/
def LibCorrect {σ E : Type} (𝓜 : Class σ) (Linked : E → Prop)
    (exports : List (E → Word → Spec σ)) : Prop :=
  ∀ Γ, Linked Γ → ∀ e ∈ exports, FnCorrect 𝓜 (e Γ)

/-- **Stub**: a process judgement over every valid launch. -/
def ProcCorrect {L : Type} (Valid : L → Prop) (Judge : L → Prop) : Prop :=
  ∀ l, Valid l → Judge l

/-! ## Refutation -/

/-- **`A` never reaches `Q` from `s`**: some invariant through `s`, disjoint from `Q`, is
closed under `A`'s `ok`-steps. `stop`s are allowed. -/
def Never {σ : Type} (A : RelIsa σ) (Q : σ → Prop) (s : σ) : Prop :=
  ∃ I : σ → Prop, I s ∧ ∀ x, I x → ¬ Q x ∧ ∀ t, A.step x (.ok t) → I t

/-- **Some-model refutation**: the judgement fails on a named member `ref`. -/
def RefutesOn {σ : Type} (𝓜 : Class σ) (ref : RelIsa σ) (J : RelIsa σ → Prop) : Prop :=
  𝓜.mem ref ∧ ¬ J ref

/-- **Every-model refutation**: the class is inhabited and the judgement fails on every
member. -/
def RefutesAll {σ : Type} (𝓜 : Class σ) (J : RelIsa σ → Prop) : Prop :=
  (∃ C, 𝓜.mem C) ∧ ∀ C, 𝓜.mem C → ¬ J C

/-- The clause a counterexample violates. -/
inductive Clause where
  | termination | post | footprint | abi | safety
  deriving DecidableEq, Repr

/-- The counterexample a refutation carries: an entry state, its decoded arguments, and the
violated clause. Data for humans; no theorem depends on it. -/
structure Counterexample (σ : Type) where
  state : σ
  args : List Word
  clause : Clause

/-! ## Companions and spec implication -/

/-- The class has a named member `ref`, and the precondition is met by a live System V entry
on it (the statement is not true for lack of models or of inputs). -/
def NonVacuous {σ : Type} (𝓜 : Class σ) (ref : RelIsa σ) (S : Word → Spec σ) : Prop :=
  𝓜.mem ref ∧ ∃ entry s, ref.live s ∧ AbiEntry (ref.core s) (ref.mem s) ∧ (S entry).entry s

/-- The postcondition excludes something (the statement is not true for lack of content). -/
def PostNontrivial {σ : Type} (S : Word → Spec σ) : Prop :=
  ∃ entry s t, (S entry).entry s ∧ ¬ (S entry).post s t

/-- Function-spec implication, per placement: `A` is at least as strong as `B`
(`Spec.Sub`: weaker pre, smaller footprint and stronger post under `B`'s pre). -/
def SpecImplies {σ : Type} (A B : Word → Spec σ) : Prop := ∀ entry, (A entry).Sub (B entry)

/-! ## The transfer principles as problems -/

/-- **Strong refutation from one invariant**, as a problem statement. -/
@[problem "problems/core/never-refutes"]
def neverRefutesStmt : Prop :=
  ∀ (σ : Type) (A C : RelIsa σ) (R Q : σ → Prop) (s : σ),
    Never A Q s → A.live s → Admissible A C → ¬ RelIsa.Must C R Q s

/-- **A solution on the loose top solves its whole down-set**, as a problem statement. -/
@[problem "problems/core/below-of-top"]
def belowOfTopStmt : Prop :=
  ∀ (σ : Type) (A : RelIsa σ) (S : Word → Spec σ), FnJ S A → FnCorrect (Class.below A) S

/-- **Solutions transfer along spec implication**, as a problem statement. -/
@[problem "problems/core/fncorrect-of-implies"]
def fnCorrectOfImpliesStmt : Prop :=
  ∀ (σ : Type) (𝓜 : Class σ) (A B : Word → Spec σ),
    SpecImplies A B → FnCorrect 𝓜 A → FnCorrect 𝓜 B

end Silmaril.Problems
