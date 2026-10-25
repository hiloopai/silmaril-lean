module

public import Silmaril.Compile.Category.PassAPI
public import Silmaril.Wasm.Binaryen.PassAPI.Shared
public import Silmaril.Wasm.Binaryen.Exe.PipelineSound
public import Silmaril.Wasm.Binaryen.DetLift

@[expose] public section

/-! # The executable optimizer as a compiler-category pass

`pipelinePass` and `bestPass` expose the existing optimizer through
`Compile.Category.Pass`. They run exactly `pipelineWith` and the module selected by
`bestNamed`, respectively. Their input and output programs retain the executable
profile and validity invariant `ExeInv` as a subtype.

The behavioural language observes actual Core instantiation admissibility and
export-session traces, in every valid initial store and import environment. Its
single interface is the fixed name-based session protocol; it does not assert
equality of static import/export manifests or expose memory/table contents beyond
the observations already made by `ExportEquiv`. Instantiation admissibility is
observed separately so an empty set of session traces cannot hide its loss.

Export equivalence gives equality of these behaviours. The compiler-category view
uses its refinement consequence; `pipelineEndo_exportEquiv` and
`bestEndo_exportEquiv` retain the original, stronger exact-equivalence guarantee.
No existing stage, executable import, profile guard or scoring policy is changed.
-/

namespace Silmaril.Wasm.Binaryen.Exe.CompilerPass

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Numerics Validation
open Silmaril.Compile
open CategoryTheory

/-- Observable instantiation admissibility, or the trace of a named export session.
The initial environment and request script remain part of the observation. -/
inductive Observation (H : Type) where
  | instantiates (store : Store H) (imports : List ExternAddr)
  | session (store : Store H) (imports : List ExternAddr)
      (script : List Call) (outcomes : List (Behaviour Val))

/-- Core export observations of lowered Binaryen modules. The interface is the
fixed name-based session protocol, and the behaviour records each environment. -/
def exportLanguage {H : Type} (P : Profile) (host : HostSemantics H) : Category.Language where
  Iface := Unit
  Prog := BModule
  iface _ := ()
  Obs := Observation H
  beh m := fun
    | .instantiates store imports =>
      StoreOk store ∧ ∃ c, Instantiate P host store m.lower imports c
    | .session store imports script outcomes =>
      StoreOk store ∧ outcomes ∈ moduleObs P host store imports m.lower script

private theorem exportEquiv_beh_subset {H : Type} {P : Profile} {host : HostSemantics H}
    {a b : BModule} (h : ExportEquiv (· = ·) P host a.lower b.lower) :
    (exportLanguage P host).beh a ⊆ (exportLanguage P host).beh b := by
  intro observation observed
  cases observation with
  | instantiates store imports =>
    rcases observed with ⟨hs, c, hc⟩
    exact ⟨hs, h.2.instantiates store imports c hs hc⟩
  | session store imports script outcomes =>
    rcases observed with ⟨hs, houtcomes⟩
    obtain ⟨outcomes', houtcomes', hrel⟩ := h.1.obs store imports script hs outcomes houtcomes
    have heq := DetLift.sessionRel_eq hrel
    exact ⟨hs, heq.symm ▸ houtcomes'⟩

/-- Exact export equivalence preserves all instantiation and session observations,
including traps, exceptions and divergence, in both directions. -/
theorem exportEquiv_beh_eq {H : Type} {P : Profile} {host : HostSemantics H}
    {a b : BModule} (h : ExportEquiv (· = ·) P host a.lower b.lower) :
    (exportLanguage P host).beh a = (exportLanguage P host).beh b :=
  Set.Subset.antisymm (exportEquiv_beh_subset h)
    (exportEquiv_beh_subset
      (Binaryen.Contract.equiv_symm_of_symm (fun _ _ h => h.symm) h))

/-- The closed-host deterministic language used by the executable pipeline. -/
abbrev language (o : GrowKind → Nat → Nat → Nat → Bool) (H : Type) : Category.Language :=
  exportLanguage (Profile.deterministic o) (closedHost (H := H))

/-- The compiler-category programs retain the original executable invariant. -/
abbrev verifiedLanguage (o : GrowKind → Nat → Nat → Nat → Bool) (H : Type) :
    Category.Language :=
  (language o H).onInvariant ExeInv

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- The existing exact-equivalence contract implies behavioural refinement for
the actual export-observation language. -/
theorem exeContract_refines {a b : BModule} (_ : ExeInv a) (h : (ExeC o H).Rel a b) :
    (language o H).Refines a b :=
  ⟨rfl, (exportEquiv_beh_eq h).subset⟩

/-- Any existing executable pass, retaining its invariant and exact run function,
as a behavioural optimization on invariant-satisfying programs. -/
def ofExePass (p : Binaryen.PassAPI.Pass (ExeC o H)) :
    Category.EndoPass (verifiedLanguage o H) :=
  Category.EndoPass.ofInvariantPass (L := language o H) p.toShared exeContract_refines

@[simp] theorem ofExePass_run_val (p : Binaryen.PassAPI.Pass (ExeC o H))
    (m : (verifiedLanguage o H).Prog) :
    ((ofExePass p).run m).val = p.run m.val := rfl

/-- The stronger, original contract remains available after conversion. -/
theorem ofExePass_exportEquiv (p : Binaryen.PassAPI.Pass (ExeC o H))
    (m : (verifiedLanguage o H).Prog) :
    EE H o ((ofExePass p).run m).val m.val :=
  p.sound m.property

/-- Conversion preserves the original left-to-right pass composition. -/
@[simp] theorem ofExePass_mul (p q : Binaryen.PassAPI.Pass (ExeC o H)) :
    ofExePass (p * q) = ofExePass p * ofExePass q := by
  apply Category.EndoPass.ext
  funext m
  apply Subtype.ext
  rfl

/-- The actual executable pipeline as a compiler-category optimization. The empty
host-state premise is the existing inlining theorem's premise. -/
def pipelineEndo (hH : H → False) (budget rounds : Nat) :
    Category.EndoPass (verifiedLanguage o H) :=
  ofExePass (pipelineP hH budget rounds)

/-- The actual best-of-candidates choice, including its original scoring and
input-wins-ties policy, as a compiler-category optimization. -/
def bestEndo (hH : H → False) (score : BModule → Nat) (rounds : Nat) :
    Category.EndoPass (verifiedLanguage o H) :=
  ofExePass (bestP hH score rounds)

/-- The pipeline as a partial compiler-category pass at the identity convention.
It always succeeds on programs carrying `ExeInv`. -/
def pipelinePass (hH : H → False) (budget rounds : Nat) :
    Category.Pass (𝟙 (verifiedLanguage o H)) :=
  (pipelineEndo hH budget rounds).toPass

/-- The driver's optimizer choice as a compiler-category pass. -/
def bestPass (hH : H → False) (score : BModule → Nat) (rounds : Nat) :
    Category.Pass (𝟙 (verifiedLanguage o H)) :=
  (bestEndo hH score rounds).toPass

/-- Removing the invariant proof recovers the unchanged executable pipeline. -/
@[simp] theorem pipelineEndo_run_val (hH : H → False) (budget rounds : Nat)
    (m : (verifiedLanguage o H).Prog) :
    ((pipelineEndo hH budget rounds).run m).val = pipelineWith budget rounds m.val := by
  change (pipelineP (o := o) hH budget rounds).run m.val = _
  rw [pipelineP_run]

/-- Removing the invariant proof recovers exactly the driver's selected module. -/
@[simp] theorem bestEndo_run_val (hH : H → False) (score : BModule → Nat) (rounds : Nat)
    (m : (verifiedLanguage o H).Prog) :
    ((bestEndo hH score rounds).run m).val = (bestNamed score rounds m.val).2 := by
  change (bestP (o := o) hH score rounds).run m.val = _
  exact (bestNamed_run (o := o) hH score rounds m.val).symm

/-- The compiler pass runs the existing pipeline and succeeds on its typed input. -/
theorem pipelinePass_run (hH : H → False) (budget rounds : Nat)
    (m : (verifiedLanguage o H).Prog) :
    ((pipelinePass hH budget rounds).run m).map Subtype.val =
      some (pipelineWith budget rounds m.val) := by
  change some (((pipelineEndo (o := o) hH budget rounds).run m).val) = _
  exact congrArg some (pipelineEndo_run_val hH budget rounds m)

/-- The compiler pass returns exactly the module selected by `bestNamed`. -/
theorem bestPass_run (hH : H → False) (score : BModule → Nat) (rounds : Nat)
    (m : (verifiedLanguage o H).Prog) :
    ((bestPass hH score rounds).run m).map Subtype.val =
      some (bestNamed score rounds m.val).2 := by
  change some (((bestEndo (o := o) hH score rounds).run m).val) = _
  exact congrArg some (bestEndo_run_val hH score rounds m)

/-- The pipeline adapter retains exact export equivalence, beyond the refinement
exposed by the compiler-category interface. -/
theorem pipelineEndo_exportEquiv (hH : H → False) (budget rounds : Nat)
    (m : (verifiedLanguage o H).Prog) :
    EE H o ((pipelineEndo hH budget rounds).run m).val m.val :=
  ofExePass_exportEquiv (pipelineP hH budget rounds) m

/-- The selected optimizer result retains the driver's exact export equivalence. -/
theorem bestEndo_exportEquiv (hH : H → False) (score : BModule → Nat) (rounds : Nat)
    (m : (verifiedLanguage o H).Prog) :
    EE H o ((bestEndo hH score rounds).run m).val m.val :=
  ofExePass_exportEquiv (bestP hH score rounds) m

/-- Exact export equivalence is also available directly at the partial-pass
interface for every successful compilation. -/
theorem pipelinePass_exportEquiv (hH : H → False) (budget rounds : Nat)
    {m result : (verifiedLanguage o H).Prog}
    (h : (pipelinePass hH budget rounds).run m = some result) :
    EE H o result.val m.val := by
  have heq : (pipelineEndo hH budget rounds).run m = result := Option.some.inj h
  rw [← heq]
  exact pipelineEndo_exportEquiv hH budget rounds m

/-- The partial-pass view of the driver's choice retains exact equivalence too. -/
theorem bestPass_exportEquiv (hH : H → False) (score : BModule → Nat) (rounds : Nat)
    {m result : (verifiedLanguage o H).Prog}
    (h : (bestPass hH score rounds).run m = some result) :
    EE H o result.val m.val := by
  have heq : (bestEndo hH score rounds).run m = result := Option.some.inj h
  rw [← heq]
  exact bestEndo_exportEquiv hH score rounds m

/-- The converted pipeline preserves every export-observation specification in
both directions, retaining the actual semantics of its input language. -/
theorem pipelineEndo_beh_eq (hH : H → False) (budget rounds : Nat)
    (m : (verifiedLanguage o H).Prog) :
    (verifiedLanguage o H).beh ((pipelineEndo hH budget rounds).run m) =
      (verifiedLanguage o H).beh m :=
  exportEquiv_beh_eq (pipelineEndo_exportEquiv hH budget rounds m)

/-- The converted best-of-candidates optimizer also preserves the full
export-observation behaviour set. -/
theorem bestEndo_beh_eq (hH : H → False) (score : BModule → Nat) (rounds : Nat)
    (m : (verifiedLanguage o H).Prog) :
    (verifiedLanguage o H).beh ((bestEndo hH score rounds).run m) =
      (verifiedLanguage o H).beh m :=
  exportEquiv_beh_eq (bestEndo_exportEquiv hH score rounds m)

end Silmaril.Wasm.Binaryen.Exe.CompilerPass
