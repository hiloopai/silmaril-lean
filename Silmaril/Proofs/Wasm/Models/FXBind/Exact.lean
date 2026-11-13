module

public import Silmaril.Proofs.Wasm.Models.FXBind.Stuck

/-!
# Partial application: the source's behaviours exactly (arity matched)

When `a` takes exactly `|vs₂ ++ vs₁|` parameters, every run that leaves values outside the
handler frame is stuck (`underHW_short_empty`), so (no host calls, no FX functions):

* **`bind_eq_rot`**: the source's behaviours are exactly the union, over the splits
  `vs₂ ++ vs₁ = X₂ ++ U₂`, of the Core behaviours of the call on the rotation `U₂ ++ X₂`.

The intended target is the rotation `U₂ = vs₁`, `X₂ = vs₂`. The others come from the untyped
`cont.bind`, which may bind any suffix of the stack.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXBind
open Silmaril.Wasm.Models.FXLower (tgtCall)
open Silmaril.Proofs.Wasm.Models.FXLower (underHW behaviours_underHW behavioursFX_sub_of_succ
  cons_not_result withVals_tgtCall)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- The behaviours of the calls on the rotations of `S`. -/
def RotTargets (s : Store H) (f : Frame) (a : Nat) (d : DefType) (S : List Val) :
    Set (Behaviour Val) :=
  {b | ∃ X₂ U₂, S = X₂ ++ U₂ ∧ b ∈ behavioursOf P noHost ⟨s, f, tgtCall a d (U₂ ++ X₂)⟩}

/-- The successors of the source after `resume`, with arity matched: only the runs that pass
every value left by `cont.bind` reach a call. -/
theorem bind_resume_sub {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {hs' : List HClause} {S X₁ X₂ U₂ : List Val}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : S.length = ps.length) (hS : S = X₁ ++ X₂ ++ U₂) :
    behavioursFX P noHost noFX
        (underHW (kRes K a fi.type U₂) hs' X₁ ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩) ⊆
      RotTargets (P := P) s f a fi.type S := by
  rcases List.eq_nil_or_concat X₁ with rfl | ⟨L, v, rfl⟩
  · intro b hb
    have h := behaviours_underHW (P := P) _ hs' [] ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩ hb
    exact ⟨X₂, U₂, by simpa using hS, h⟩
  · have hV : (U₂ ++ X₂).length < ps.length := by
      rw [← hn, hS]
      simp
      omega
    rw [underHW_short_empty hf he hV]
    exact Set.empty_subset _

/-- **The partial-application source has exactly the behaviours of the rotations** (no host
calls, no FX functions, arity matched). -/
theorem bind_eq_rot {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : (vs₂ ++ vs₁).length = ps.length)
    (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFX P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ =
      RotTargets (P := P) s f a fi.type (vs₂ ++ vs₁) := by
  apply Set.Subset.antisymm
  · refine behavioursFX_sub_of_succ (fun r => by
      rw [show (⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ : ConfigFX H).code = _ from
        srcBind_eq a ct ct' hs vs₂ vs₁]
      exact cons_not_result rfl r) fun y hy => ?_
    rw [bsrc_succ₁ hf hy]
    refine behavioursFX_sub_of_succ (cons_not_result rfl) fun z hz => ?_
    obtain ⟨U₁, U₂, hS, rfl⟩ := bsrc_succ₂ hz
    refine behavioursFX_sub_of_succ (cons_not_result rfl) fun w hw => ?_
    obtain ⟨hs'', X₁, X₂, rfl, rfl⟩ := bsrc_succ₃ hw
    exact bind_resume_sub hf he hn hS
  · rintro b ⟨X₂, U₂, hS, hb⟩
    have h := bind_rot_sound (P := P) (host := noHost) (fx := noFX) (K := K) (ct := ct)
      (ct' := ct') hf hr hS
    rw [Silmaril.Wasm.Models.FX.blockFX_noFX] at h
    exact h hb

end Silmaril.Proofs.Wasm.Models.FXBind
