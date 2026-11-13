module

public import Silmaril.Wasm.Det.CompRef.Thms
public import Silmaril.Wasm.Component.Reference.Litmus.Thms
import Silmaril.Proofs.Wasm.Det.CompRef.Litmus

/-!
# Litmus: the adder component is deterministic and stateless on the reference machine

For the simple component `adderS` (`add(a: u32, b: u32) -> u32` over `i32.add`,
`Silmaril.Wasm.Component.Reference.Litmus`), at every profile `P` and component choice profile
`prof`, over the reference machine with `core3P P`:

* `adder_modDet`, `adder_modStateless`: its module's only instance store passes the no-memory
  and stateless checks (kernel evaluation);
* `adder_returns_eq`: two returned outcomes of `add(x, y)` coincide (`simple_returns_eq`);
* `adder_seq_returns_eq`: the returned outcome of `add(x, y)` after any two sequences of typed
  earlier calls coincide (`simple_seq_returns_eq`).

Proofs: `Silmaril.Proofs.Wasm.Det.CompRef.Litmus`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.CompRef.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Numerics (Profile)

theorem adder_modDet (P : Profile) : ModDet P adderS.mod :=
  Silmaril.Proofs.Wasm.Det.CompRef.Litmus.adder_modDet P

theorem adder_modStateless (P : Profile) : ModStateless P adderS.mod :=
  Silmaril.Proofs.Wasm.Det.CompRef.Litmus.adder_modStateless P

/-- **Litmus: `add(x, y)` has one returned outcome on the reference machine.** -/
theorem adder_returns_eq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x y : BitVec 32) {rs₁ rs₂ : List Silmaril.Wasm.Component.Value.Val}
    (h₁ : Outcome.returns (some rs₁) ∈ exportBehaviours prof (refHost P) () adderS.toRef [] "add"
      ([.u32 x, .u32 y].map toRefVal))
    (h₂ : Outcome.returns (some rs₂) ∈ exportBehaviours prof (refHost P) () adderS.toRef [] "add"
      ([.u32 x, .u32 y].map toRefVal)) : rs₁ = rs₂ :=
  simple_returns_eq P prof adderS adderS_good Silmaril.Proofs.Wasm.Det.CompRef.Litmus.adderS_floatFree
    adderS_inst adderS_arity (adder_modDet P) ⟨0, by decide⟩ [.u32 x, .u32 y] rfl h₁ h₂

/-- **Litmus: the returned outcome of `add(x, y)` does not depend on earlier calls.** -/
theorem adder_seq_returns_eq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (calls₁ calls₂ : List (Fin adderS.exports.length × List Silmaril.Wasm.Component.Val))
    (ht₁ : TypedCalls adderS calls₁) (ht₂ : TypedCalls adderS calls₂) (x y : BitVec 32)
    {p₁ p₂ : List (List Silmaril.Wasm.Component.Value.Val) × Outcome}
    {rs₁ rs₂ : List Silmaril.Wasm.Component.Value.Val}
    (h₁ : p₁ ∈ seqBehaviours prof (refHost P) () adderS.toRef
      (calls₁.map fun q => (adderS.exports[q.1].name, q.2.map toRefVal)) "add"
      ([.u32 x, .u32 y].map toRefVal))
    (h₂ : p₂ ∈ seqBehaviours prof (refHost P) () adderS.toRef
      (calls₂.map fun q => (adderS.exports[q.1].name, q.2.map toRefVal)) "add"
      ([.u32 x, .u32 y].map toRefVal))
    (hr₁ : p₁.2 = .returns (some rs₁)) (hr₂ : p₂.2 = .returns (some rs₂)) : rs₁ = rs₂ :=
  simple_seq_returns_eq P prof adderS adderS_good
    Silmaril.Proofs.Wasm.Det.CompRef.Litmus.adderS_floatFree adderS_inst adderS_arity
    (adder_modStateless P) calls₁ calls₂ ht₁ ht₂ ⟨0, by decide⟩ [.u32 x, .u32 y] rfl h₁ h₂ hr₁ hr₂

end Silmaril.Wasm.Det.CompRef.Litmus
