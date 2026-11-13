module

public import Silmaril.Proofs.Wasm.Spec.Check.GameLink
public import Silmaril.Wasm.Logic.GameLink.Examples.Thms

@[expose] public section

/-!
# Litmus: the increment provider, verified in the Wasm specification institutions

The provider of `Silmaril.Wasm.Logic.GameLink.Examples` exports the Core 3.0 function
`local.get 0; i32.const 1; i32.add` (`OpenExamples.incBody`) at every export. From its Hoare-logic
proof (`incProvider_sat`, every profile) and the soundness of the verification conditions:

* `incProvider_neverCall`: it never calls any import;
* `incProvider_retPost`: every return is a single `i32` value.

Both hold at every profile, for every program whose exports are this function and take one
`i32`.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.GameLink.Examples (incISpec i32T incProvider_sat)
open Silmaril.Wasm.Logic.OpenExamples (incBody)

variable {P : Profile} {X : WIface} (p : WasmProg X) {a₁ : Nat} {fi₁ : FuncInst Nat} {code : Func}
  {ps rs : Ty (.list .val)}

/-- With one `i32` parameter, every export question is an increment question. -/
theorem incISpec_pre (hparams : ∀ j, (X.exports.get j).params = [i32T])
    (f : (ifaceSig X.exports).Op) : (incISpec X.exports).pre f := by
  obtain ⟨j, args, hargs⟩ := f
  have hargs' : List.Forall₂ ScalarType.HasVal [i32T] args := hparams j ▸ hargs
  obtain ⟨v, hv, rfl⟩ : ∃ v, ScalarType.HasVal i32T v ∧ args = [v] := by
    cases hargs' with
    | cons h hrest => cases hrest; exact ⟨_, h, rfl⟩
  obtain ⟨bits, rfl⟩ := hv
  exact ⟨bits, rfl⟩

/-- **The increment provider never calls an import** (every profile). -/
theorem incProvider_neverCall (haddr : ∀ j, p.inst.addr j = a₁) (hcode : fi₁.code = .wasm code)
    (hbody : code.body = incBody) (he : Expand fi₁.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) (hfi : p.store.funcs[a₁]? = some fi₁)
    (hparams : ∀ j, (X.exports.get j).params = [i32T]) (i : X.Imp) :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) p i := by
  have hm := incProvider_sat (P := P) (I := p.inst) ⟨fun e => e.1 ≠ i, fun _ _ => True⟩ haddr
    hcode hbody he hps hrs
  rw [models_iff]
  intro t ht a hc
  obtain ⟨e, hei, -, hpre⟩ := gameSat_icall hm hfi (incISpec_pre hparams) (fun _ _ => trivial) ht hc
  exact hpre hei

/-- **Every return of the increment provider is a single `i32`** (every profile). -/
theorem incProvider_retPost (haddr : ∀ j, p.inst.addr j = a₁) (hcode : fi₁.code = .wasm code)
    (hbody : code.body = incBody) (he : Expand fi₁.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) (hfi : p.store.funcs[a₁]? = some fi₁)
    (hparams : ∀ j, (X.exports.get j).params = [i32T]) (j : X.Exp) :
    Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p
      ⟨j, fun b => ∃ m : BitVec 32, b = .returns [Val.i32 m]⟩ := by
  have hm := incProvider_sat (P := P) (I := p.inst) ⟨fun _ => True, fun _ _ => True⟩ haddr
    hcode hbody he hps hrs
  rw [models_iff]
  intro t ht b hc
  obtain ⟨f, w, -, rfl, hpost⟩ :=
    gameSat_ret hm hfi (incISpec_pre hparams) (fun _ _ => trivial) ht hc
  obtain ⟨m, hm'⟩ := incISpec_pre hparams f
  have hres : Answer.toResult (ft := X.exports.get f.1) w = .values [Val.i32 (m + 1)] := hpost m hm'
  refine ⟨m + 1, ?_⟩
  show (Answer.toResult (ft := X.exports.get f.1) w).toBehaviour = _
  rw [hres]
  rfl

end Silmaril.Wasm.Spec
