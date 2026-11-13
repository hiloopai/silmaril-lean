module

public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Defs

/-!
# Typing judgements of the wasm-3.0 script against Core 3.0 validation: definitions

`Wasm30.toModel` relates Core's steps to the `Step` facts of the backend canonical model
`stepModel B`. This header sets up the same kind of statement for **typing relations**: the
script's `Reftype_ok`, `Reftype_sub` and `Ref_ok`, read in `stepModel B`, against Silmaril's
Core 3.0 validation (`TyOk`, `Sub`, `RefOk`). These are the type judgements round 6's interpreter
reaches (`Round6.RefOkV.AgreeTy`, `Round6.RefOkV.Agree`), so they are the only ones related here.

* `TySen H`: a Core typing judgement in the empty context `{}`. `ok rt` is `⊢ rt ok`, `sub p rt`
  is `⊢ p <: rt`, and `refOk s r rt` is `s ⊢ r : rt`.
* `TySen.Holds`: what Core's validation says (`TyOk {}`, `Sub {}`, `RefOk`).
* `TySen.toSen hn`: the sentence translation, a fact sentence of the institution at the images
  `tyV`, `storeV hn` and `refToValue`, in the context `{}` (`ctxEmptyV`).
* `TySen.Dom env hn`: the domain of the satisfaction condition. Types are bounded
  (`Round4.tyBnd`), the types of `sub` and the type of `refOk` are Core-valid, and the store of
  `refOk` is Core-valid with a typed image in `env`. `ok rt` only asks for `rt` to be bounded.
* `TySen.Exact`: the sentences on which the condition is an equivalence (`sub`, `refOk`).

The results are in `Typing30.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Typing30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm.SpecTec.Sim

/-- **A Core typing judgement in the empty context**, over stores of host type `H`. -/
inductive TySen (H : Type) where
  /-- `{} ⊢ rt ok`. -/
  | ok (rt : CRefType)
  /-- `{} ⊢ p <: rt`. -/
  | sub (p rt : CRefType)
  /-- `s ⊢ r : rt`. -/
  | refOk (s : Store H) (r : Ref) (rt : CRefType)

variable {H : Type}

namespace TySen

/-- **Core's reading** of a typing judgement. -/
def Holds : TySen H → Prop
  | ok rt => TyOk {} rt
  | sub p rt => Sub {} p rt
  | refOk s r rt => RefOk s r rt

/-- **The sentence translation**: a judgement as a fact of the script's typing relation. -/
def toSen (hn : H → String) : TySen H → SSen
  | ok rt => .fact "Reftype_ok" "%|-%:OK" [] (.tuple [Round6.RefOkV.ctxEmptyV, tyV rt])
  | sub p rt => .fact "Reftype_sub" "%|-%<:%" [] (.tuple [Round6.RefOkV.ctxEmptyV, tyV p, tyV rt])
  | refOk s r rt => .fact "Ref_ok" "%|-%:%" [] (.tuple [storeV hn s, refToValue r, tyV rt])

/-- **The domain** of the satisfaction condition, at evaluator `env`. -/
def Dom (env : Env) (hn : H → String) : TySen H → Prop
  | ok rt => Round4.tyBnd rt = true
  | sub p rt => Round4.tyBnd p = true ∧ Round4.tyBnd rt = true ∧ TyOk {} p ∧ TyOk {} rt
  | refOk s _ rt => TypedV env storeT (storeV hn s) ∧ StoreOk s ∧ Round4.tyBnd rt = true ∧ TyOk {} rt

/-- The judgements on which the satisfaction condition is an equivalence. -/
def Exact : TySen H → Prop
  | ok _ => False
  | sub _ _ => True
  | refOk _ _ _ => True

end TySen

end Silmaril.Wasm.SpecTec.Institution.Typing30
