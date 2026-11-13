module

public import Silmaril.Wasm.Det.CompRef.Defs
public import Silmaril.Wasm.Det.CompIR.Thms
public import Silmaril.Wasm.Component.Reference.Sound.Thms
import Silmaril.Proofs.Wasm.Det.CompRef.Simple

/-!
# Determinism and statelessness of components over the reference machine

Transfer of the IR closure (`Silmaril.Wasm.Det.CompIR`) to the reference Component Model machine
over Core 3.0 at an arbitrary profile `P` and component choice profile `prof`, through IR
soundness (`Simple.sound`, `Simple.sound_seq`), for simple components
(`Silmaril.Wasm.Component.Reference.Simple`: one core module lifted at component types):

* `modSem_detMod`, `modSem_statelessMod`: the IR's Core 3.0 semantics of a module whose
  instances are `DetModule` (`ModDet`), resp. `StatelessModule` (`ModStateless`), is
  deterministic (stateless) modulo traps and trap-strict (the instance strategy between the IR's
  import and export handlers);
* `simple_detMod`, `simple_statelessMod`: so is the IR strategy of the simple component;
* `simple_returns_eq` (**reference determinism**): for a float-free simple component within
  the flat arities, two returned outcomes of the reference machine for the same export call on
  the same typed values coincide;
* `simple_seq_returns_eq` (**reference statelessness**): for a stateless module, the returned
  outcome of an export call after any two sequences of resolved earlier calls on the same
  instance coincide.

Only returned outcomes (`Outcome.returns (some _)`) are compared: traps are exempt, and the
other outcomes are not observed by IR soundness. Components with several instances or imports
are covered in the IR (`den_detMod`) but not transferred (soundness is proved for `Simple` only).

Proofs: `Silmaril.Proofs.Wasm.Det.CompRef.{Basic,Simple}`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.CompRef

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Det.Game
  Silmaril.Wasm.Det.CompIR
open Silmaril.Wasm.Numerics (Profile)

theorem modSem_detMod {P : Profile} {m : NumModule} (hD : ModDet P m) :
    DetMod (noneTraps _) ((modSem P).sem m) ∧
      Strict (noneTraps _) (noneTraps _) ((modSem P).sem m) :=
  Silmaril.Proofs.Wasm.Det.CompRef.modSem_det hD

theorem modSem_statelessMod {P : Profile} {m : NumModule} (hD : ModStateless P m) :
    StatelessMod (noneTraps _) ((modSem P).sem m) ∧
      Strict (noneTraps _) (noneTraps _) ((modSem P).sem m) :=
  Silmaril.Proofs.Wasm.Det.CompRef.modSem_stateless hD

theorem simple_detMod {P : Profile} (c : Simple) (hD : ModDet P c.mod) :
    DetMod (noneTraps _) (c.toComp.den (modSem P)) ∧
      Strict (noneTraps _) (noneTraps _) (c.toComp.den (modSem P)) :=
  Silmaril.Proofs.Wasm.Det.CompRef.simple_detMod c hD

theorem simple_statelessMod {P : Profile} (c : Simple) (hD : ModStateless P c.mod) :
    StatelessMod (noneTraps _) (c.toComp.den (modSem P)) ∧
      Strict (noneTraps _) (noneTraps _) (c.toComp.den (modSem P)) :=
  Silmaril.Proofs.Wasm.Det.CompRef.simple_statelessMod c hD

/-- **Reference determinism of simple components**: two returned outcomes of the reference
machine for the same export call coincide (every profile and component choice profile). -/
theorem simple_returns_eq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple)
    (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (hD : ModDet P c.mod)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {rs₁ rs₂ : List Silmaril.Wasm.Component.Value.Val}
    (h₁ : Outcome.returns (some rs₁) ∈ exportBehaviours prof (refHost P) () c.toRef []
      c.exports[j].name (vs.map toRefVal))
    (h₂ : Outcome.returns (some rs₂) ∈ exportBehaviours prof (refHost P) () c.toRef []
      c.exports[j].name (vs.map toRefVal)) : rs₁ = rs₂ :=
  Silmaril.Proofs.Wasm.Det.CompRef.simple_returns_eq P prof c hc hf hi ha hD j vs hvs h₁ h₂

/-- **Reference statelessness of simple components**: the returned outcome of an export call
does not depend on the earlier resolved calls on the same instance (every profile and component
choice profile). -/
theorem simple_seq_returns_eq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (hD : ModStateless P c.mod)
    (calls₁ calls₂ : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (ht₁ : TypedCalls c calls₁) (ht₂ : TypedCalls c calls₂)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {p₁ p₂ : List (List Silmaril.Wasm.Component.Value.Val) × Outcome}
    {rs₁ rs₂ : List Silmaril.Wasm.Component.Value.Val}
    (h₁ : p₁ ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls₁.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal))
    (h₂ : p₂ ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls₂.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal))
    (hr₁ : p₁.2 = .returns (some rs₁)) (hr₂ : p₂.2 = .returns (some rs₂)) : rs₁ = rs₂ :=
  Silmaril.Proofs.Wasm.Det.CompRef.simple_seq_returns_eq P prof c hc hf hi ha hD calls₁ calls₂ ht₁
    ht₂ j vs hvs h₁ h₂ hr₁ hr₂

end Silmaril.Wasm.Det.CompRef
