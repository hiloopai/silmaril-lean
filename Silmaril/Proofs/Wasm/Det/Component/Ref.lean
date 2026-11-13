module

public import Silmaril.Wasm.Det.Component.Defs
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.Component.Reference.Sound.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms

/-!
# One export call on the reference machine: proofs

* `isInst_unique`: a module has at most one instance (`Silmaril.Wasm.Game.IsInstance.unique`);
* `exportSpec_returns_eq`: under `CoreDet`, two `returns` outcomes of the canonical-ABI
  specification of an export call are equal;
* `exportDet_of_coreDet`: with `refToSpec_of_arity`, the same for the reference machine.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Component

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Component
open Silmaril.Wasm.Component.Reference (Simple SimpleExport NumModule exportSpec coreOut liftOutcome
  Outcome refHost exportBehaviours toRefVal refToSpec_of_arity)

/-- A module has at most one instance. -/
theorem isInst_unique {m : NumModule} {I J : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    (hJ : m.IsInst J) : I = J := by
  obtain ⟨⟨mt, hmt⟩, -, -⟩ := hI
  obtain ⟨⟨mt', hmt'⟩, -, -⟩ := hJ
  have he : mt = mt' := Option.some.inj (hmt.valid.symm.trans hmt'.valid)
  rw [he] at hmt
  exact Silmaril.Wasm.Game.IsInstance.unique hmt hmt'

/-- A `returns` outcome of the specification comes from a core run returning values. -/
theorem returns_mem_spec {P : Profile} {c : Simple} {x : SimpleExport}
    {vs : List Silmaril.Wasm.Component.Val} {r : Option (List Silmaril.Wasm.Component.Reference.Val)}
    (h : Outcome.returns r ∈ exportSpec P c x vs) :
    ∃ xs I d ws, Silmaril.Wasm.Component.checkLower x.ty.params vs = some xs ∧ c.mod.IsInst I ∧
      Steps P Det.noHost (invoke I.store (I.addrs.getD x.core 0) (xs.map ofFlat)) d ∧
      d.code = (Result.values ws).toAdmin ∧
      Outcome.returns r = liftOutcome x.ty (ws.mapM toFlat?) := by
  unfold exportSpec at h
  rcases hl : Silmaril.Wasm.Component.checkLower x.ty.params vs with _ | xs
  · rw [hl] at h
    cases h
  · rw [hl] at h
    rcases h with ⟨r', ⟨I, hI, d, res, hs, hd, hr'⟩, he⟩ | ⟨hdv, -⟩
    · show ∃ xs' I d ws, some xs = some xs' ∧ _
      rcases res with ws | a | -
      · exact ⟨xs, I, d, ws, rfl, hI, hs, hd, by rw [he, hr']⟩
      · have ht : Outcome.returns r = Outcome.traps := by rw [he, hr']; rfl
        cases ht
      · have ht : Outcome.returns r = Outcome.traps := by rw [he, hr']; rfl
        cases ht
    · cases hdv

/-- **Specification level**: under `CoreDet`, two `returns` outcomes of one export call are
equal. -/
theorem exportSpec_returns_eq {P : Profile} {c : Simple} {x : SimpleExport}
    (hD : CoreDet P c x) {vs : List Silmaril.Wasm.Component.Val}
    {r₁ r₂ : Option (List Silmaril.Wasm.Component.Reference.Val)}
    (h₁ : Outcome.returns r₁ ∈ exportSpec P c x vs)
    (h₂ : Outcome.returns r₂ ∈ exportSpec P c x vs) : r₁ = r₂ := by
  obtain ⟨xs₁, I₁, d₁, ws₁, hl₁, hI₁, hs₁, hd₁, he₁⟩ := returns_mem_spec h₁
  obtain ⟨xs₂, I₂, d₂, ws₂, hl₂, hI₂, hs₂, hd₂, he₂⟩ := returns_mem_spec h₂
  have hx : xs₁ = xs₂ := Option.some.inj (hl₁.symm.trans hl₂)
  have hI : I₁ = I₂ := isInst_unique hI₁ hI₂
  rw [← hx, ← hI] at hs₂
  have hdet : DetCall P I₁.store (I₁.addrs.getD x.core 0) (xs₁.map ofFlat) := hD I₁ hI₁ xs₁
  have ho : Out.ret (.values ws₁) = Out.ret (.values ws₂) :=
    (hdet [] d₁ d₂ _ _ (.stop hs₁) (.stop hs₂) (.ret (by simp) hd₁) (.ret (by simp) hd₂)).1
  have hw : ws₁ = ws₂ := by
    injection ho with h
    injection h
  have hr : Outcome.returns r₁ = Outcome.returns r₂ := by rw [he₁, he₂, hw]
  injection hr

open Silmaril.Wasm.Component in
/-- **The reference machine**: for a float-free simple component within the flat arities whose
module is instantiated as the IR assumes, `CoreDet` of export `x` makes each export call (from
the freshly instantiated component, any component choice profile) deterministic modulo traps. -/
theorem exportDet_of_coreDet (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) {x : SimpleExport} (hx : x ∈ c.exports)
    (hD : CoreDet P c x) {vs : List Silmaril.Wasm.Component.Val}
    (hvs : Silmaril.Wasm.Component.ValTy.checkList x.ty.params vs = true) :
    ExportDet prof (refHost P) () c.toRef [] x.name (vs.map toRefVal) := by
  intro r₁ r₂ h₁ h₂
  exact exportSpec_returns_eq hD (refToSpec_of_arity P prof c hc hf hi ha x hx vs hvs h₁)
    (refToSpec_of_arity P prof c hc hf hi ha x hx vs hvs h₂)

end Silmaril.Proofs.Wasm.Det.Component
