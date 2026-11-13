module

public import Silmaril.Wasm.FX.Examples.Defs

/-!
# The example kit: global hypotheses and behaviour transfer

* `kitOk`: the kit setting satisfies `FXAsyncFX.Ok` as soon as every kernel function `f` is
  below `nf`, has no parameters, and its body is encoded by `Y f`;
* `kitTag`, `kitD`, `kitH`, `kitAdd`: the tag, the two block types and `i32.add`, for
  `EncI` derivations;
* **`kit_beh`**: under the deterministic profile and no host calls, a kernel run that stops with
  `done vs`, checked along the run for the fragment (`checkRun`) and for tight suspensions
  (`checkTight`), gives the exact `StepFX'` behaviour set `{obsB (.done vs)}` of the encoded
  program;
* `kit_mem`: for every profile and host, `obsB (.done vs)` is a `StepFX'` behaviour.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (SV SCfg Ins Prog sstep runN beh Obs Outcome sInit)
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (checkRun supported_of_checkRun)
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (checkTight tight_of_checkTight)
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable (P : Profile) (host : HostSemantics Nat) (nf : Nat) (Y : Nat → List InstrFX)

theorem kitTag : TagOk (kitS P host nf Y) 0 := ⟨⟨kitTypes.head!⟩, rfl, rfl⟩

theorem kitD : (kitS P host nf Y).M.blockType? btD = some ([ti32], [ti32]) := by
  rfl

theorem kitH : (kitS P host nf Y).M.blockType? btH = some ([ti32], [ti32, ti32]) := by
  rfl

theorem kitAdd : PrimOk (kitS P host nf Y) 2 opAdd (.intBinOp .i32 .add) := by
  intro bs f hbs _
  match bs, hbs with
  | [a, b], _ =>
    exact .numeric (.intBinOp (t := .i32) (op := .add) (x := b) (y := a) (z := b + a) rfl)

/-- **The kit satisfies the global hypotheses.** -/
theorem kitOk {W : Prog (Ins Val)} (hnf : nf < 2 ^ 32)
    (henc : ∀ f np body, W f = some (np, body) →
      f < nf ∧ np = 0 ∧ EncI (kitS P host nf Y) W body (Y f)) :
    Ok (kitS P host nf Y) W where
  funcs f np body h := by
    obtain ⟨hf, rfl, he⟩ := henc f np body h
    have hix : (ix f : FuncIdx).toNat = f := by
      simp only [ix, Idx.toNat, Nat.mod_eq_of_lt (by omega : f < 2 ^ 32)]
    refine ⟨by decide, ⟨kitTypes.head!, kitM nf, .host f⟩, f, Y f, ?_, ?_, rfl, ?_, he⟩
    · show (List.range nf)[(ix f : FuncIdx).toNat]? = some f
      rw [hix, List.getElem?_range hf]
    · show ((List.range nf).map fun f => (⟨kitTypes.head!, kitM nf, .host f⟩ : FuncInst Nat))[f]? = _
      rw [List.getElem?_map, List.getElem?_range hf]
      rfl
    · show (if f < nf then _ else none) = _
      simp only [hf, ite_true]; rfl
  root := rfl
  tags := Function.injective_id

/-- **Exact behaviours from a checked kernel run.** -/
theorem kit_beh (o : GrowKind → Nat → Nat → Nat → Bool) {W : Prog (Ins Val)}
    (hok : Ok (kitS (Profile.deterministic o) noHost nf Y) W) (f : Nat) {n fuel : Nat}
    {vs : List (SV Val)} (hrun : runN (sstep W i32Test) n (sInit f []) = .stop (.done vs))
    (hc : checkRun W fuel (sInit f []) = true) (ht : checkTight W fuel (sInit f []) = true) :
    behavioursFX' (Profile.deterministic o) noHost (kitFx nf Y)
        (fxInit (kitS (Profile.deterministic o) noHost nf Y) f []) = {obsB (.done vs)} := by
  have hsup : Silmaril.Proofs.Wasm.Models.FXAsyncSus.TightSupported W
      (sInit f (([] : List Val).map .val)) :=
    ⟨supported_of_checkRun fuel _ hc, tight_of_checkTight fuel _ ht⟩
  have h := Silmaril.Wasm.Models.FXAsyncSus.beh_eq_tight (kitS (Profile.deterministic o) noHost nf Y)
    (o := o) rfl rfl hok (rel_init (kitS (Profile.deterministic o) noHost nf Y) f []) hsup
  rw [show behavioursFX' (Profile.deterministic o) noHost (kitFx nf Y)
      (fxInit (kitS (Profile.deterministic o) noHost nf Y) f []) = _ from h,
    show sInit f (([] : List Val).map SV.val) = sInit f [] from rfl,
    Silmaril.Proofs.Wasm.Models.FXAsync.beh_of_stop hrun]
  simp only [Set.image_singleton, Outcome.toObs]

/-- **A checked kernel run is a `StepFX'` behaviour**, for every profile and host. -/
theorem kit_mem {W : Prog (Ins Val)} (hok : Ok (kitS P host nf Y) W) (f : Nat) {n fuel : Nat}
    {vs : List (SV Val)} (hrun : runN (sstep W i32Test) n (sInit f []) = .stop (.done vs))
    (hc : checkRun W fuel (sInit f []) = true) :
    obsB (.done vs) ∈ behavioursFX' P host (kitFx nf Y) (fxInit (kitS P host nf Y) f []) :=
  kernel_in_fx (kitS P host nf Y) hok (rel_init (kitS P host nf Y) f [])
    (supported_of_checkRun fuel _ hc) _ (Or.inl ⟨n, _, hrun, rfl⟩)

end Silmaril.Proofs.Wasm.FX.Examples
