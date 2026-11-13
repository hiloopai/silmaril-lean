module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdCE
public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdMain

/-!
# The backward simulation of the tail-call rewrite: every callee segment

* `bce_wrap`: a target step of a wrapper is a step of the callee it wraps (a frame or a call
  redex), matched by the callee's own backward step;
* **`ce_bwd`**: every callee segment, by recursion on the nesting of wrappers.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **A target step of a wrapper**, matched by the wrapped callee's step (`rec`). -/
theorem bce_wrap {k : Nat} {xs ys₀ : List Admin} {fi : Frame} {B : List Admin}
    (hce : CE false k xs ys₀) (hpw : PW ys₀ B)
    {s t t' : Store H} {f g : Frame} {W W' : List Val} {rest rest' ys' : List Admin}
    (rec : ∀ {t' : Store H} {g : Frame} {W' : List Val} {rest' ys'' : List Admin},
      BIH P host (codeSize ys₀) → ContextTyped ⟨t, g, vals W' ++ ys₀ ++ rest'⟩ →
      TSegRed P host g t ys₀ t' ys'' → BCEM P host k ys₀ ys'' s f xs t')
    (ih : BIH P host (codeSize [.frame k fi B])) (hst : StoreRel FRel s t)
    (hTs : ContextTyped ⟨s, f, vals W ++ xs ++ rest⟩)
    (hTt : ContextTyped ⟨t, g, vals W' ++ [.frame k fi B] ++ rest'⟩)
    (hfr : Closure.FrameRedex P host t g k fi B t' g ys') :
    BCEM P host k [.frame k fi B] ys' s f xs t' := by
  obtain ⟨N, pre, Y, rfl⟩ := hpw
  have hTi : ContextTyped ⟨t, fi, vals pre ++ ys₀ ++ .plain .return_ :: Y⟩ :=
    CT_fill N (ContextTyped.frame hTt)
  have hle : codeSize ys₀ ≤
      codeSize [Admin.frame k fi (N.fill (vals pre ++ ys₀ ++ .plain .return_ :: Y))] := by
    have h1 := Closure.codeSize_le_ctx pre ys₀ (.plain .return_ :: Y)
    have h2 := codeSize_le_fill (vals pre ++ ys₀ ++ .plain .return_ :: Y) N
    have h3 := Closure.codeSize_frame_lt [] k fi
      (N.fill (vals pre ++ ys₀ ++ .plain .return_ :: Y)) []
    simp only [Sim.vals_nil', List.nil_append, List.append_nil] at h3
    omega
  rcases CE.tgt_shape_aux hce with ⟨fi₀, B₀, rfl⟩ | ⟨vs, a, d, rfl, rfl, har⟩
  · -- a wrapped frame
    have hB : N.fill (vals pre ++ [Admin.frame k fi₀ B₀] ++ .plain .return_ :: Y) =
        N.fill (vals pre ++ Admin.frame k fi₀ B₀ :: .plain .return_ :: Y) := by simp
    obtain ⟨V₁, b₁, r₁, hB₁, hb₁⟩ :=
      fill_head' N (V := pre) (b := .frame k fi₀ B₀) (Y := .plain .return_ :: Y)
    have hctx : CtxHead b₁ := by
      rcases hb₁ with rfl | h
      · exact .inr (.inr ⟨_, _, _, rfl⟩)
      · exact .inr (.inl h)
    rw [hB] at hfr
    obtain ⟨fi', B₂, hs, rfl⟩ := frameRedex_ctxt hfr hB₁ hctx
    obtain ⟨X', hX, rfl⟩ := fill_inv' (.inr ⟨_, _, _, rfl⟩) N hs
    rcases Step.split_head rfl hX with ⟨ws, us, is', rfl, hs', rfl⟩ | ⟨hc₁, -⟩ | ⟨hc₁, -⟩
    rotate_left
    · cases hc₁
    · cases hc₁
    obtain ⟨is₀, hcode, hfr₀⟩ := Closure.Step.frame_redex_aux hs' us k fi₀ B₀ rfl
    dsimp only at hcode hfr₀
    have hff := FrameRedex.frame_eq hfr₀
    subst fi'
    subst hcode
    have hm := rec (ih.mono hle) hTi (TSegRed.frame hfr₀)
    have e : vals ws ++ (vals us ++ is₀) ++ .plain .return_ :: Y =
        vals (ws ++ us) ++ is₀ ++ .plain .return_ :: Y := by simp
    rw [e]
    exact bcem_wrap N (ws ++ us) Y hm
  · -- a wrapped call redex
    have hc' : (Admin.callRefType d).IsCallRef := crt_isCallRef d
    have hB : N.fill (vals pre ++ (vals vs ++ [Admin.ref (.func a), .callRefType d]) ++
        .plain .return_ :: Y) = N.fill (vals (pre ++ (vs ++ [.ref (.func a)])) ++
          Admin.callRefType d :: .plain .return_ :: Y) := by simp [vals, Val.toAdmin]
    obtain ⟨V₁, b₁, r₁, hB₁, hb₁⟩ :=
      fill_head N (V := pre ++ (vs ++ [.ref (.func a)])) (Y := .plain .return_ :: Y) hc'
    have hctx : CtxHead b₁ := by
      rcases hb₁ with rfl | h
      · exact .inl hc'
      · exact .inr (.inl h)
    rw [hB] at hfr
    obtain ⟨fi', B₂, hs, rfl⟩ := frameRedex_ctxt hfr hB₁ hctx
    obtain ⟨X', hX, rfl⟩ := fill_inv hc' N hs
    rcases Step.split_head (Admin.val?_of_isCallRef hc') hX with ⟨ws₀, us, is', hV, hs', rfl⟩ |
        ⟨hc₁, -⟩ | ⟨hc₁, -⟩
    rotate_left
    · cases hc₁
    · cases hc₁
    obtain ⟨rfl, ws₂, us₁, is₂, rfl, rfl, hch⟩ := call_inv hc' hs'
    obtain ⟨rfl, rfl⟩ := call_split_t (pre := pre) (ws₁ := ws₀ ++ ws₂) har hst hTs
      (by rw [hV]; simp) hch
    have hm := rec (ih.mono hle) hTi (TSegRed.call hch)
    have e : vals ws₀ ++ (vals ws₂ ++ is₂) ++ .plain .return_ :: Y =
        vals (ws₀ ++ ws₂) ++ is₂ ++ .plain .return_ :: Y := by simp
    rw [e]
    exact bcem_wrap N (ws₀ ++ ws₂) Y hm

/-- **Every callee segment, backwards.** -/
theorem ce_bwd (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host) :
    ∀ {fw : Bool} {k : Nat} {xs ys : List Admin}, CE fw k xs ys → fw = false →
    ∀ {s t t' : Store H} {f g : Frame} {W W' : List Val} {rest rest' ys' : List Admin},
      BIH P host (codeSize ys) → StoreRel FRel s t →
      ContextTyped ⟨s, f, vals W ++ xs ++ rest⟩ → ContextTyped ⟨t, g, vals W' ++ ys ++ rest'⟩ →
      TSegRed P host g t ys t' ys' → BCEM P host k ys ys' s f xs t'
  | _, _, _, _, .frame hb, hfw, s, t, t', f, g, W, W', rest, rest', ys', ih, hst, hTs, hTt,
      hred => by
    subst hfw
    generalize hx : [Admin.frame _ _ _] = ys at hred
    cases hred with
    | frame hfr =>
      simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact bce_frame hhostB hok hb ih hst hTs hTt hfr
    | call hch =>
      have := congrArg List.getLast? hx
      simp at this
  | _, _, _, _, .call har, _, s, t, t', f, g, W, W', rest, rest', ys', ih, hst, hTs, hTt,
      hred => by
    generalize hx : vals _ ++ [Admin.ref (.func _), .callRefType _] = ys at hred
    cases hred with
    | frame hfr =>
      have := congrArg List.getLast? hx
      simp at this
    | call hch =>
      obtain ⟨rfl, rfl, rfl⟩ := call_redex_inj hx
      exact bce_call hhostB hok har hst hTs hch
  | _, _, _, _, .pend har hpt hsuf hrt, _, s, t, t', f, g, W, W', rest, rest', ys', ih, hst, hTs,
      hTt, hred => by
    generalize hx : [Admin.frame _ _ _] = ys at hred
    cases hred with
    | frame hfr =>
      simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact bce_pend hhostB hok har hpt hsuf hrt hst hTs hfr
    | call hch =>
      have := congrArg List.getLast? hx
      simp at this
  | _, _, _, _, .wrap hce hpw, hfw, s, t, t', f, g, W, W', rest, rest', ys', ih, hst, hTs, hTt,
      hred => by
    generalize hx : [Admin.frame _ _ _] = ys at hred
    cases hred with
    | frame hfr =>
      simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact bce_wrap (hfw ▸ hce) hpw
        (fun hih hT hseg => ce_bwd hhostB hok hce hfw hih hst hTs hT hseg)
        ih hst hTs hTt hfr
    | call hch =>
      have := congrArg List.getLast? hx
      simp at this
  | _, _, _, _, .vals hn hpw, _, s, t, t', f, g, W, W', rest, rest', ys', ih, hst, hTs, hTt,
      hred => by
    generalize hx : [Admin.frame _ _ _] = ys at hred
    cases hred with
    | frame hfr =>
      simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact bce_vals hn hpw hst hfr
    | call hch =>
      have := congrArg List.getLast? hx
      simp at this

end Silmaril.Raw.Wasm.LimeCompile.TailSim
