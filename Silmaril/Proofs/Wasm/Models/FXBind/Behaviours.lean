module

public import Silmaril.Proofs.Wasm.Models.FXBind.Runs

/-!
# Partial application: behaviours of the source

* **`bind_rot_sound`** (any host, any FX table): for every split `vs₂ ++ vs₁ = X₂ ++ U₂`, the
  Core behaviours of the call on the rotation `U₂ ++ X₂` are behaviours of the source;
* **`bind_sound`**: in particular the intended target `vs₁ vs₂ ref.func a call_ref` (`U₂ = vs₁`,
  `X₂ = vs₂`);
* **`bind_complete`** (no host calls, no FX functions): every behaviour of the source is a Core
  behaviour of a call on `X₁ ++ U₂ ++ X₂` for some split `vs₂ ++ vs₁ = X₁ ++ X₂ ++ U₂` (`X₁` is
  left outside the handler frame by the untyped `resume`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXBind
open Silmaril.Wasm.Models.FXLower (tgtCall)
open Silmaril.Proofs.Wasm.Models.FXLower (behavioursFX_of_steps behaviours_handler_sub
  behavioursFX_sub_of_succ cons_not_result behaviours_underHW withVals_tgtCall)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **Every rotation is a behaviour of the source** (any host, any FX table). -/
theorem bind_rot_sound {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ X₂ U₂ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs')
    (hS : vs₂ ++ vs₁ = X₂ ++ U₂) :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩ ⊆
      behavioursFX P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  (behaviours_handler_sub _ hs' _).trans (behavioursFX_of_steps (bsrc_runs hf hr hS))

/-- **Soundness of the partial-application lowering**: every Core behaviour of the call with
the bound arguments first is a behaviour of the source. -/
theorem bind_sound {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ ⊆
      behavioursFX P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  bind_rot_sound hf hr rfl

/-- The calls a run of the source can reach. -/
def BindTargets (s : Store H) (f : Frame) (a : Nat) (d : Validation.DefType)
    (S : List Val) : Set (Behaviour Val) :=
  {b | ∃ X₁ X₂ U₂, S = X₁ ++ X₂ ++ U₂ ∧ b ∈ behavioursOf P noHost ⟨s, f, tgtCall a d (X₁ ++ U₂ ++ X₂)⟩}

/-- **Completeness up to the untyped splits** (no host calls, no FX functions). -/
theorem bind_complete {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) :
    behavioursFX P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ ⊆
      BindTargets (P := P) s f a fi.type (vs₂ ++ vs₁) := by
  refine behavioursFX_sub_of_succ (fun r => by
    rw [show (⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ : ConfigFX H).code = _ from
      srcBind_eq a ct ct' hs vs₂ vs₁]
    exact cons_not_result rfl r) fun y hy => ?_
  rw [bsrc_succ₁ hf hy]
  refine behavioursFX_sub_of_succ (cons_not_result rfl) fun z hz => ?_
  obtain ⟨U₁, U₂, hS, rfl⟩ := bsrc_succ₂ hz
  refine behavioursFX_sub_of_succ (cons_not_result rfl) fun w hw => ?_
  obtain ⟨hs', X₁, X₂, rfl, rfl⟩ := bsrc_succ₃ hw
  intro b hb
  refine ⟨X₁, X₂, U₂, by rw [hS], ?_⟩
  have h := behaviours_underHW (P := P) _ hs' X₁ ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩ hb
  rwa [withVals_tgtCall, ← List.append_assoc] at h

end Silmaril.Proofs.Wasm.Models.FXBind
