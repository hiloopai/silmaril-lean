module

public import Silmaril.Problems.Core.Defs
public import Silmaril.X86.RelIsa.Thms
import Silmaril.Proofs.Problems.Core.Transfer

/-!
# Problem templates: transfer theorems

Everything here is proved, with the standard axioms only; the longer proofs are in
`Silmaril/Proofs/Problems/Core/Transfer.lean`.

**Classes.** `admissible_self` (the loose top is in its own down-set when it has
`Progress`), `Admissible.of_le`, `Class.below_sub`, `progress_ofIsa`, `admissible_ofIsa` (a
deterministic refinement is admissible).

**Solutions.**

* `fnCorrect_below_of_top : FnJ S A → FnCorrect (Class.below A) S`: a solution on the loose
  top solves every admissible refinement.
* `fnCorrect_of_sub`, `fnCorrect_single_iff`.
* `total_of_mustTotal_ofIsa`: on `ofIsa I`, `Spec.MustTotal` is `Spec.Total`
  (`RelIsa.must_ofIsa_iff`), and its converse `mustTotal_ofIsa_of_total`;
  `fnCorrect_single_ofIsa_of_total`: a deterministic `Total` proof, weakened along `Spec.Sub`,
  solves the singleton class `Class.single (ofIsa I)`; `fnCorrectDet_of_fnJ`, and `fnCorrectDet_of_fnCorrect`: a class
  solution gives the deterministic `Spec.Total` shape on any `ofIsa I` below the top.

**Spec implication.** `mustTotal_mono_sub` (`Spec.MustTotal` is monotone along `Spec.Sub`),
`specImplies_refl`, `SpecImplies.trans`, `fnJ_of_implies`, `fnCorrect_of_implies` (solutions
from strong to weak), `refutesAll_of_implies` and `refutesOn_of_implies` (refutations from
weak to strong).

**Refutation.**

* `never_refutes_core`, and `never_refutes : Never A Q s → A.live s → Admissible A C →
  ¬ RelIsa.Must C R Q s`.
* `refutesAll_of_never`: from `A.Progress`, a live System V entry of `S entry` and
  `Never A ((S entry).ResultV A.toViews s) s`, the every-model refutation
  `RefutesAll (Class.below A) (FnJ S)`.
* `RefutesAll.refutesOn`, `RefutesOn.not_forall`, `RefutesAll.not_fnCorrect`,
  `RefutesAll.of_sub` (the strength order every-model ⇒ some-model ⇒ weak).

**Registered solutions** (`@[solves]`): `problems/core/never-refutes`,
`problems/core/below-of-top`, `problems/core/fncorrect-of-implies`.
-/

@[expose] public section

namespace Silmaril.Problems

open Silmaril.X86 (RelIsa Word)
open Silmaril.X86.FnContract (Spec AbiEntry)
open Silmaril.X86.RelIsa (Must Le)

variable {σ : Type}

/-! ## Classes -/

/-- The loose top is a member of its own down-set iff it has `Progress`. -/
theorem admissible_self {A : RelIsa σ} (h : A.Progress) : Admissible A A := ⟨Le.refl A, h⟩

/-- A refinement of an admissible member is admissible when it has `Progress`. -/
theorem Admissible.of_le {A B C : RelIsa σ} (hB : Admissible A B) (h : Le C B)
    (hp : C.Progress) : Admissible A C := ⟨h.trans hB.1, hp⟩

/-- The down-set of a refinement is a subclass of the down-set of the top. -/
theorem Class.below_sub {A B : RelIsa σ} (h : Le B A) : (Class.below B).Sub (Class.below A) :=
  fun _ hC => ⟨hC.1.trans h, hC.2⟩

/-- `ofIsa I` has `Progress` (a deterministic machine always has an outcome). -/
theorem progress_ofIsa (I : Silmaril.X86.SegVC.Isa σ) : (RelIsa.ofIsa I).Progress :=
  RelIsa.progress_ofIsa

/-- A deterministic refinement of `A` is admissible. -/
theorem admissible_ofIsa {A : RelIsa σ} {I : Silmaril.X86.SegVC.Isa σ}
    (h : Le (RelIsa.ofIsa I) A) : Admissible A (RelIsa.ofIsa I) := ⟨h, progress_ofIsa I⟩

/-! ## Solutions -/

/-- A solution for a class solves every subclass. -/
theorem fnCorrect_of_sub {𝓝 𝓜 : Class σ} {S : Word → Spec σ} (h : 𝓝.Sub 𝓜)
    (hS : FnCorrect 𝓜 S) : FnCorrect 𝓝 S := fun C hC => hS C (h C hC)

/-- **A solution on the loose top solves every admissible refinement** (only `Le` is used). -/
theorem fnCorrect_below_of_top {A : RelIsa σ} {S : Word → Spec σ} (h : FnJ S A) :
    FnCorrect (Class.below A) S :=
  fun _ hC entry => Silmaril.X86.FnContract.Spec.MustTotalIn.of_le hC.1 (h entry)

/-- The singleton class is the one-machine judgement. -/
theorem fnCorrect_single_iff {C : RelIsa σ} {S : Word → Spec σ} :
    FnCorrect (Class.single C) S ↔ FnJ S C :=
  ⟨fun h => h C rfl, fun h _ hC => hC ▸ h⟩

/-- **On a deterministic machine, demonic total correctness is total correctness.** -/
theorem total_of_mustTotal_ofIsa {I : Silmaril.X86.SegVC.Isa σ} {S : Spec σ}
    (h : S.MustTotal (RelIsa.ofIsa I)) : S.Total I :=
  Silmaril.Proofs.Problems.Core.total_of_mustTotal_ofIsa h

/-- **On a deterministic machine, total correctness is demonic total correctness**: the
converse of `total_of_mustTotal_ofIsa`. -/
theorem mustTotal_ofIsa_of_total {I : Silmaril.X86.SegVC.Isa σ} {S : Spec σ} (h : S.Total I) :
    S.MustTotal (RelIsa.ofIsa I) :=
  Silmaril.Proofs.Problems.Core.mustTotal_ofIsa_of_total h

/-- **From a deterministic `Total` proof to a class solution**: deterministic total
correctness of `S` on `I`, weakened along `Spec.Sub` to `T`, solves `T` on the singleton
class of `ofIsa I`. -/
theorem fnCorrect_single_ofIsa_of_total {I : Silmaril.X86.SegVC.Isa σ} {S T : Word → Spec σ}
    (h : ∀ e, (S e).Total I) (hs : ∀ e, (S e).Sub (T e)) :
    FnCorrect (Class.single (RelIsa.ofIsa I)) T :=
  fnCorrect_single_iff.2 fun e =>
    Silmaril.Proofs.Problems.Core.mustTotal_mono_sub (hs e) (mustTotal_ofIsa_of_total (h e))

/-- The one-machine judgement on `ofIsa I` is the deterministic form. -/
theorem fnCorrectDet_of_fnJ {I : Silmaril.X86.SegVC.Isa σ} {S : Word → Spec σ}
    (h : FnJ S (RelIsa.ofIsa I)) : FnCorrectDet I S :=
  fun entry => total_of_mustTotal_ofIsa (h entry)

/-- **From a class solution to the deterministic shape**: a deterministic machine below the
top inherits `Spec.Total`. -/
theorem fnCorrectDet_of_fnCorrect {A : RelIsa σ} {I : Silmaril.X86.SegVC.Isa σ}
    {S : Word → Spec σ} (h : FnCorrect (Class.below A) S) (hle : Le (RelIsa.ofIsa I) A) :
    FnCorrectDet I S :=
  fnCorrectDet_of_fnJ (h _ (admissible_ofIsa hle))

/-! ## Spec implication -/

/-- `Spec.MustTotal` is monotone along `Spec.Sub`. -/
theorem mustTotal_mono_sub {A : RelIsa σ} {S T : Spec σ} (hst : S.Sub T) (h : S.MustTotal A) :
    T.MustTotal A :=
  Silmaril.Proofs.Problems.Core.mustTotal_mono_sub hst h

theorem specImplies_refl (A : Word → Spec σ) : SpecImplies A A :=
  fun _ => ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem SpecImplies.trans {A B D : Word → Spec σ} (hab : SpecImplies A B)
    (hbd : SpecImplies B D) : SpecImplies A D :=
  Silmaril.Proofs.Problems.Core.specImplies_trans hab hbd

/-- The one-machine judgement transfers along spec implication. -/
theorem fnJ_of_implies {A B : Word → Spec σ} {C : RelIsa σ} (h : SpecImplies A B)
    (hA : FnJ A C) : FnJ B C := fun e => mustTotal_mono_sub (h e) (hA e)

/-- **Solutions go from the stronger spec to the weaker.** -/
theorem fnCorrect_of_implies {𝓜 : Class σ} {A B : Word → Spec σ} (h : SpecImplies A B)
    (hA : FnCorrect 𝓜 A) : FnCorrect 𝓜 B := fun C hC => fnJ_of_implies h (hA C hC)

/-- **Refutations go from the weaker spec to the stronger.** -/
theorem refutesAll_of_implies {𝓜 : Class σ} {A B : Word → Spec σ} (h : SpecImplies A B)
    (hB : RefutesAll 𝓜 (FnJ B)) : RefutesAll 𝓜 (FnJ A) :=
  ⟨hB.1, fun C hC hA => hB.2 C hC (fnJ_of_implies h hA)⟩

/-- Some-model refutations go the same way. -/
theorem refutesOn_of_implies {𝓜 : Class σ} {ref : RelIsa σ} {A B : Word → Spec σ}
    (h : SpecImplies A B) (hB : RefutesOn 𝓜 ref (FnJ B)) : RefutesOn 𝓜 ref (FnJ A) :=
  ⟨hB.1, fun hA => hB.2 (fnJ_of_implies h hA)⟩

/-! ## Refutation strengths -/

/-- Every-model implies some-model, at any member. -/
theorem RefutesAll.refutesOn {𝓜 : Class σ} {J : RelIsa σ → Prop} (h : RefutesAll 𝓜 J)
    {ref : RelIsa σ} (hr : 𝓜.mem ref) : RefutesOn 𝓜 ref J := ⟨hr, h.2 ref hr⟩

/-- Some-model implies the weak refutation of the class statement. -/
theorem RefutesOn.not_forall {𝓜 : Class σ} {ref : RelIsa σ} {J : RelIsa σ → Prop}
    (h : RefutesOn 𝓜 ref J) : ¬ ∀ C, 𝓜.mem C → J C := fun hJ => h.2 (hJ ref h.1)

/-- An every-model refutation of `FnJ S` refutes `FnCorrect` (weakly). -/
theorem RefutesAll.not_fnCorrect {𝓜 : Class σ} {S : Word → Spec σ}
    (h : RefutesAll 𝓜 (FnJ S)) : ¬ FnCorrect 𝓜 S :=
  fun hS => h.1.elim fun C hC => h.2 C hC (hS C hC)

/-- An every-model refutation covers every inhabited subclass. -/
theorem RefutesAll.of_sub {𝓝 𝓜 : Class σ} {J : RelIsa σ → Prop} (h : RefutesAll 𝓜 J)
    (hs : 𝓝.Sub 𝓜) (hi : 𝓝.Inhabited) : RefutesAll 𝓝 J := ⟨hi, fun C hC => h.2 C (hs C hC)⟩

/-! ## Refutation from one invariant -/

/-- An invariant of the top `A` that excludes `Q`, is closed under `A`'s ok-steps and lies
inside `C.live` refutes `Must C R Q` for every `C` below `A` with `Progress`. -/
theorem never_refutes_core {A C : RelIsa σ} {R Q Inv : σ → Prop}
    (hQ : ∀ s, Inv s → ¬ Q s) (hstep : ∀ s t, Inv s → A.step s (.ok t) → Inv t)
    (hlive : ∀ s, Inv s → C.live s) (hle : Le C A) (hprog : C.Progress) :
    ∀ s, Inv s → ¬ Must C R Q s :=
  Silmaril.Proofs.Problems.Core.never_refutes_core hQ hstep hlive hle hprog

/-- **Strong refutation from one invariant.** If the loose top `A` never reaches `Q` from a
live state `s`, then no admissible refinement `C` can demonically reach `Q` from `s`. -/
theorem never_refutes {A C : RelIsa σ} {R Q : σ → Prop} {s : σ} (hA : Never A Q s)
    (hl : A.live s) (hC : Admissible A C) : ¬ Must C R Q s :=
  Silmaril.Proofs.Problems.Core.never_refutes hA hl hC

/-- **Every-model refutation of a function problem from one invariant.** If the loose top
has `Progress` (so its down-set is inhabited), and from some live System V entry `s` of
`S entry` the top never reaches a result of `S entry`, then `FnJ S` fails on every admissible
refinement. -/
theorem refutesAll_of_never {A : RelIsa σ} {S : Word → Spec σ} (hp : A.Progress) (entry : Word)
    (s : σ) (hl : A.live s) (habi : AbiEntry (A.core s) (A.mem s)) (he : (S entry).entry s)
    (hN : Never A ((S entry).ResultV A.toViews s) s) :
    RefutesAll (Class.below A) (FnJ S) :=
  Silmaril.Proofs.Problems.Core.refutesAll_of_never hp entry s hl habi he hN

/-! ## The registered transfer principles -/

@[solves "problems/core/never-refutes"]
theorem neverRefutesStmt_sol : neverRefutesStmt :=
  fun _ _ _ _ _ _ hA hl hC => never_refutes hA hl hC

@[solves "problems/core/below-of-top"]
theorem belowOfTopStmt_sol : belowOfTopStmt := fun _ _ _ h => fnCorrect_below_of_top h

@[solves "problems/core/fncorrect-of-implies"]
theorem fnCorrectOfImpliesStmt_sol : fnCorrectOfImpliesStmt :=
  fun _ _ _ _ h hA => fnCorrect_of_implies h hA

end Silmaril.Problems
