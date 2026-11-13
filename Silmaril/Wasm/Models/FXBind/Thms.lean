module

public import Silmaril.Proofs.Wasm.Models.FXBind.Refute

/-!
# Lowering WasmFX partial application (`cont.bind`) to Wasm: results

The source `vs₂ vs₁ ref.func a cont.new cont.bind resume` (`srcBind`) binds `vs₁` to a fresh
continuation of `a` and resumes it with `vs₂`; the intended target is the call
`vs₁ vs₂ ref.func a call_ref` (`tgtCall a d (vs₁ ++ vs₂)`). This extends the first lowering
(`Silmaril.Wasm.Models.FXLower.lower_correct`, the case `vs₁ = []` without `cont.bind`) by partial
application. Under track H's untyped `StepFX`:

* **`bind_sound`** (any host, any FX table): every Core behaviour of the intended target is a
  behaviour of the source; more generally **`bind_rot_sound`** for every rotation `U₂ ++ X₂` of
  the stack `vs₂ ++ vs₁ = X₂ ++ U₂`;
* **`bind_complete`** (no host calls, no FX functions): every behaviour of the source is a Core
  behaviour of a call on `X₁ ++ U₂ ++ X₂` for a split `vs₂ ++ vs₁ = X₁ ++ X₂ ++ U₂`;
* **`bind_eq_rot`** (arity matched: `a` takes `|vs₂ ++ vs₁|` parameters): the source's
  behaviours are exactly the union of the behaviours of the calls on the rotations; the runs
  that leave values outside the handler frame are stuck (`underHW_short_empty`);
* **`bind_ne_target`** (refutation): for the function `first` (return the first of two
  arguments) and `x ≠ y`, the source with `vs₂ = [x]`, `vs₁ = [y]` returns `[x]` and the
  intended target only returns `[y]`. So `lower_correct` does **not** extend to `cont.bind`
  under the untyped reduction, even with matched arity. The restatement that holds is
  `bind_eq_rot`; the intended equality needs a typed `cont.bind` that binds exactly the
  parameters `$ct` has beyond `$ct'`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXBind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXLower (tgtCall)
open Silmaril.Proofs.Wasm.Models.FXBind (BindTargets RotTargets firstS firstD)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **Every rotation is a behaviour of the source.** -/
theorem bind_rot_sound {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ X₂ U₂ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs')
    (hS : vs₂ ++ vs₁ = X₂ ++ U₂) :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩ ⊆
      behavioursFX P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBind.bind_rot_sound hf hr hS

/-- **Soundness of the partial-application lowering.** -/
theorem bind_sound {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ ⊆
      behavioursFX P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBind.bind_sound hf hr

/-- **Completeness up to the untyped splits.** -/
theorem bind_complete {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) :
    behavioursFX P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ ⊆
      BindTargets (P := P) s f a fi.type (vs₂ ++ vs₁) :=
  Silmaril.Proofs.Wasm.Models.FXBind.bind_complete hf

/-- **The source has exactly the behaviours of the rotations** (arity matched). -/
theorem bind_eq_rot {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : (vs₂ ++ vs₁).length = ps.length)
    (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFX P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ =
      RotTargets (P := P) s f a fi.type (vs₂ ++ vs₁) :=
  Silmaril.Proofs.Wasm.Models.FXBind.bind_eq_rot hf he hn hr

/-- **Refutation: the intended lowering is not behaviour-preserving for the untyped
`cont.bind`.** -/
theorem bind_ne_target (o : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {x y : Val} (hxy : x ≠ y) (K : List (Option ContFX)) (f : Frame) (ct ct' : TypeIdx) :
    behavioursFX (Profile.deterministic o) noHost noFX
        ⟨firstS (H := H), K, f, srcBind 0 ct ct' [] [x] [y]⟩ ≠
      behavioursOf (Profile.deterministic o) noHost
        ⟨firstS (H := H), f, tgtCall 0 firstD ([y] ++ [x])⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBind.bind_ne_target o hxy K f ct ct'

/-- info: 'Silmaril.Wasm.Models.FXBind.bind_eq_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_eq_rot

/-- info: 'Silmaril.Wasm.Models.FXBind.bind_ne_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_ne_target

/-- info: 'Silmaril.Wasm.Models.FXBind.bind_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_sound

end Silmaril.Wasm.Models.FXBind
