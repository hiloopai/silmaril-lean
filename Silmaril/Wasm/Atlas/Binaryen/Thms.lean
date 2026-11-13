module

public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.Atlas.Binaryen.Defs
public import Silmaril.Wasm.Binaryen.PassAPI.Shared
public import Silmaril.Wasm.Binaryen.Pipeline.Thms

/-!
# The session charts: lowering, model equivalence and passes

* `Binaryen.toCore P host`: lowering `BModule → Module`, equal on every sentence (definitional:
  an IR module means its lowering).
* `Binaryen.equiv_of_exportEquiv`: `ExportEquiv Eq P host m m'` makes `m` and `m'` equivalent
  points of the Core session chart (they satisfy the same sentences).
* `Binaryen.pass_equiv`: for every pass `p` of `PassAPI.equivContract P host` and every
  `BModule.Ok` module `m`, `p.run m` and `m` are equivalent points of the Binaryen IR chart.
  This covers the shared Silmaril passes (`ExtraStage.equivP`, `extraSelectedP`) and silmaril's
  `ArbitraryProfile.EquivPass P host`, which is this pass type by definition.
* `Binaryen.selected_equiv`: the instance for the Silmaril pipeline: a selection of every-profile
  stages (`extraSelectedRound`) maps a `BModule.Ok` module to an equivalent point, at every
  profile, for closed modules (`closedHost`).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Binaryen

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {H : Type} {host : HostSemantics H}

/-- **Lowering as a transition**, equal on every sentence. -/
def toCore (P : Profile) (host : HostSemantics H) : Transition (birChart P host) (coreChart P host) :=
  BTrans.ofEq BModule.lower id (fun _ _ => trivial) (fun _ _ _ => rfl)

/-- Under `Eq` the session relation is equality. -/
theorem sessionRel_eq {bs bs' : List (Behaviour Val)} (h : SessionRel (· = ·) bs bs') :
    bs = bs' := by
  induction h with
  | nil => rfl
  | cons hb _ ih => exact congrArg₂ List.cons hb ih
  | ub h => exact absurd ((h .traps).trans (h .diverges).symm) (by intro e; cases e)

theorem coreObs_subset {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b b', R b b' → b = b')
    {m m' : Module} (h : ExportRefines R P host m m') (c : SCall H) :
    coreObs P host m c ⊆ coreObs P host m' c := by
  rintro bs ⟨hs, hbs⟩
  obtain ⟨bs', hbs', hr⟩ := h.obs c.1 c.2.1 c.2.2 hs bs hbs
  exact ⟨hs, (sessionRel_eq (hr.mono hR)) ▸ hbs'⟩

/-- **`ExportEquiv Eq` is model equivalence** in the Core session chart. -/
theorem equiv_of_exportEquiv {m m' : Module} (h : ExportEquiv (· = ·) P host m m') :
    (coreChart P host).Equiv m m' := fun s =>
  BSen.sat_congr (fun c => Set.Subset.antisymm (coreObs_subset (fun _ _ e => e) h.1 c)
    (coreObs_subset (fun _ _ e => e.symm) h.2 c)) s

/-- **Every equivalence pass yields an equivalent point** of the Binaryen IR chart. -/
theorem pass_equiv (p : Silmaril.Compile.PassAPI.Pass (PassAPI.equivContract P host).toShared)
    {m : BModule} (hm : m.Ok) : (birChart P host).Equiv m (p.run m) := fun s =>
  (equiv_of_exportEquiv (P := P) (host := host) (p.sound hm) s).symm

/-- **The Silmaril pipeline is a model equivalence** (every profile, closed modules). -/
theorem selected_equiv (P : Profile) (stages : List Silmaril.Wasm.Binaryen.Pipeline.ExtraStage)
    (h : ∀ s ∈ stages, s.anyProfile = true) {m : BModule} (hm : m.Ok) :
    (birChart P (closedHost (H := H))).Equiv m
      (Silmaril.Wasm.Binaryen.Pipeline.extraSelectedRound stages m) := by
  have e := pass_equiv (Silmaril.Wasm.Binaryen.Pipeline.extraSelectedP (H := H) P stages h) hm
  rwa [Silmaril.Wasm.Binaryen.Pipeline.extraSelectedP_run] at e

end Silmaril.Wasm.Atlas.Binaryen
