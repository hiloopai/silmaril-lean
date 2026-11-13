module

public import Silmaril.Proofs.Wasm.Models.FXBindT.Example

/-!
# Partial application under `StepFX'` and a typed `cont.bind`: results

The source `vs₂ vs₁ ref.func a cont.new $ct cont.bind $ct $ct' resume $ct'` (`srcBind`) and the
intended target `vs₁ vs₂ ref.func a call_ref` (`tgtCall a d (vs₁ ++ vs₂)`) are those of
`Silmaril.Wasm.Models.FXBind`, where an earlier step proved soundness, completeness up to stack splits and
the rotation equality under track H's `StepFX`, and refuted the intended equality.

**The relations.** `StepFX'` (`Silmaril.Wasm.Models.FXV`) lets continuation references move as
values; its `cont.bind` is untyped. `StepFXT` (`Defs`) is `StepFX'` with the `cont.bind` rules
typed: they bind exactly `n` values, where `BindArity f.module ct ct' n` says
`n + |params ct'| = |params ct|`. `stepFXT_incl`: `StepFXT ⊆ StepFX'`; `behavioursFXT_noK`: on
code without continuations the three relations have the same behaviours.

**Under `StepFX'`** (the pass-1 results re-proved): `bind_sound'`, `bind_rot_sound'`,
`bind_complete'`, **`bind_eq_rot'`** and the refutation **`bind_ne_target'`**.

**Under `StepFXT`**: **`bindT_eq`**: with `cont.bind` binding `|vs₁|` values and `a` taking
`|vs₂ ++ vs₁|` parameters, the source's behaviours **are** the intended target's (no host calls,
no FX functions). This is the equality an earlier step refuted for the untyped rule. `bindT_first`,
`bindT_first_not_x`: on an earlier counterexample the typed source returns only `[y]`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXBindT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBind
open Silmaril.Wasm.Models.FXLower (tgtCall)
open Silmaril.Proofs.Wasm.Models.FXBind (BindTargets RotTargets firstS firstD)
open Silmaril.Proofs.Wasm.Models.FXVRuns (NoKs)
open Silmaril.Proofs.Wasm.Models.FXBindT (firstF)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **`StepFXT ⊆ StepFX'`.** -/
theorem stepFXT_incl {host : HostSemantics H} {fx : H → Option FuncFX} {x y : ConfigFX H}
    (h : StepFXT P host fx x y) : StepFX' P host fx x y :=
  Silmaril.Proofs.Wasm.Models.FXBindT.stepFXT_incl h

/-- Every `StepFXT` behaviour is a `StepFX'` behaviour. -/
theorem behavioursFXT_incl {host : HostSemantics H} {fx : H → Option FuncFX} (x : ConfigFX H) :
    behavioursFXT P host fx x ⊆ behavioursFX' P host fx x :=
  Silmaril.Proofs.Wasm.Models.FXBindT.behavioursFXT_incl x

/-- **On code without continuations `StepFXT` has the `StepFX` behaviours.** -/
theorem behavioursFXT_noK {host : HostSemantics H} {x : ConfigFX H} (hx : NoKs x.code) :
    behavioursFXT P host noFX x = behavioursFX P host noFX x :=
  Silmaril.Proofs.Wasm.Models.FXBindT.behavioursFXT_noK hx

/-- **Soundness under `StepFX'`** (any host, any FX table). -/
theorem bind_sound' {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ ⊆
      behavioursFX' P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBindT.bind_sound' hf hr

/-- Every rotation is a `StepFX'` behaviour of the source. -/
theorem bind_rot_sound' {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ X₂ U₂ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs')
    (hS : vs₂ ++ vs₁ = X₂ ++ U₂) :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩ ⊆
      behavioursFX' P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBindT.bind_rot_sound' hf hr hS

/-- **Completeness up to the untyped splits under `StepFX'`.** -/
theorem bind_complete' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) :
    behavioursFX' P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ ⊆
      BindTargets (P := P) s f a fi.type (vs₂ ++ vs₁) :=
  Silmaril.Proofs.Wasm.Models.FXBindT.bind_complete' hf

/-- **Under `StepFX'` the source has exactly the behaviours of the rotations.** -/
theorem bind_eq_rot' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : (vs₂ ++ vs₁).length = ps.length)
    (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFX' P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ =
      RotTargets (P := P) s f a fi.type (vs₂ ++ vs₁) :=
  Silmaril.Proofs.Wasm.Models.FXBindT.bind_eq_rot' hf he hn hr

/-- **Refutation under `StepFX'`.** -/
theorem bind_ne_target' (o : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {x y : Val} (hxy : x ≠ y) (K : List (Option ContFX)) (f : Frame) (ct ct' : TypeIdx) :
    behavioursFX' (Profile.deterministic o) noHost noFX
        ⟨firstS (H := H), K, f, srcBind 0 ct ct' [] [x] [y]⟩ ≠
      behavioursOf (Profile.deterministic o) noHost
        ⟨firstS (H := H), f, tgtCall 0 firstD ([y] ++ [x])⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBindT.bind_ne_target' o hxy K f ct ct'

/-- **Soundness of the typed lowering** (any host, no FX functions). -/
theorem bindT_sound {host : HostSemantics H} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi)
    (hr : hs.mapM (resolve s f) = some hs') (hA : BindArity f.module ct ct' vs₁.length) :
    behavioursOf P host ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ ⊆
      behavioursFXT P host noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBindT.bindT_sound hf hr hA

/-- **The typed partial-application lowering is correct.** -/
theorem bindT_eq {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : (vs₂ ++ vs₁).length = ps.length)
    (hA : BindArity f.module ct ct' vs₁.length) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFXT P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ =
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBindT.bindT_eq hf he hn hA hr

/-- **On an earlier counterexample the typed source is the intended call.** -/
theorem bindT_first (o : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool) (x y : Val)
    (K : List (Option ContFX)) :
    behavioursFXT (Profile.deterministic o) noHost noFX
        ⟨firstS (H := H), K, firstF, srcBind 0 ⟨0⟩ ⟨1⟩ [] [x] [y]⟩ =
      behavioursOf (Profile.deterministic o) noHost
        ⟨firstS (H := H), firstF, tgtCall 0 firstD ([y] ++ [x])⟩ :=
  Silmaril.Proofs.Wasm.Models.FXBindT.bindT_first o x y K

/-- info: 'Silmaril.Wasm.Models.FXBindT.bindT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bindT_eq

/-- info: 'Silmaril.Wasm.Models.FXBindT.bind_eq_rot'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_eq_rot'

/-- info: 'Silmaril.Wasm.Models.FXBindT.bind_ne_target'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_ne_target'

/-- info: 'Silmaril.Wasm.Models.FXBindT.bindT_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bindT_first

end Silmaril.Wasm.Models.FXBindT
