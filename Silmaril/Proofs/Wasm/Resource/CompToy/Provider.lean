module

public import Silmaril.Proofs.Wasm.Resource.CompToy.DropMain
public import Silmaril.Wasm.Resource.CompProvider.Thms

/-!
# The toy resource component satisfies the provider sentence

* **`toy_ctrVCOn`**: the counter verification condition `CtrVCOn` holds for the toy over
  `core3P P` with host `refHost P`, at every profile `P` and choice profile, with
  `ctr := toyCtrP P` and `R := toyR P`: `init` is `toyR_init`, `step`/`mono` are `toyR_make`,
  `toyR_get`, `toyR_drop`, `fresh` is `toyR_make`;
* **`toy_compProvider`**: hence (`compProvider_of_ctrOn`) every multi-call trace of the toy
  (`refMultiSem`) is accepted by the provider sentence `compProviderSpec makeE dropE`.

The answers of the canon built-ins are not assumed anywhere: the callouts to `resource.new` and
`resource.drop` are runs of the machine's dispatch program. New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

variable (P : Silmaril.Wasm.Numerics.Profile)

/-- `step` and `mono` of `CtrVCOn` at every export of the toy. -/
theorem toyR_step (prof : ProfileKind) {es : List (String × FuncId)}
    {m m' : Machine.Config (core3P P) Unit} {k : ℕ} {j : Xt.Exp} {f : FuncId} {a : List Silmaril.Wasm.Component.Reference.Val}
    {r : Option (List Silmaril.Wasm.Component.Reference.Val)} (hR : toyR P es m) (hf : es.lookup ((toyProgP P).names j) = some f)
    (h : Calls prof (refHost P).hr (refHost P).dispatch m ⟨k⟩ f a m' (.resolved r)) :
    toyR P es m' ∧ toyCtrP P m ≤ toyCtrP P m' := by
  obtain ⟨j, hj⟩ := j
  match j, hj with
  | 0, _ =>
    obtain ⟨h₁, h₂, -⟩ := toyR_make hR hf h
    exact ⟨h₁, by omega⟩
  | 1, _ =>
    obtain ⟨h₁, h₂⟩ := toyR_get hR hf h
    exact ⟨h₁, h₂.ge⟩
  | 2, _ =>
    obtain ⟨h₁, h₂⟩ := toyR_drop hR hf h
    exact ⟨h₁, h₂.ge⟩
  | n + 3, hn => exact absurd hn (by simp [Xt])

/-- **The counter verification condition for the toy**, at every profile and choice profile,
with no hypothesis on the answers of the canon built-ins. -/
theorem toy_ctrVCOn (prof : ProfileKind) :
    CtrVCOn prof (refHost P) () (toyProgP P) makeE (toyCtrP P) (toyR P) where
  init m₀ inst es hi := (toyR_init (P := P) prof (refHost P) m₀ inst es hi).1
  step _ _ _ _ _ _ _ _ hR hf h := (toyR_step P prof hR hf h).1
  mono _ _ _ _ _ _ _ _ hR hf h := (toyR_step P prof hR hf h).2
  fresh _ _ _ _ _ _ _ hR hf h := by
    obtain ⟨-, h₂, h₃⟩ := toyR_make hR hf h
    obtain rfl : _ = toyCtrP P _ := by simpa using h₃
    omega

/-- **The toy component defining a resource satisfies the provider sentence over several
calls**: at every profile `P` and choice profile, every multi-call trace of `toyProgP P` with the
reference host `refHost P` is accepted by `compProviderSpec makeE dropE`. -/
theorem toy_compProvider (prof : ProfileKind) :
    Models (protoLogic CFn (List RVal) Component.Outcome (Option (List ℕ)))
      (refMultiSem prof (refHost P) ()) (toyProgP P) (compProviderSpec makeE dropE) :=
  compProvider_of_ctrOn (toy_ctrVCOn P prof)

end Silmaril.Wasm.Resource.CompToy
