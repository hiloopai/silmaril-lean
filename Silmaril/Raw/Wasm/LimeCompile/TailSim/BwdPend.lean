module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdLabel
public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdCE

/-!
# The backward simulation of the tail-call rewrite: the catch-up of a pending tail call

When the target's frame body is pending (`PendR`), the target's only step is its `CALL_REF` in
the innermost label. The source catches up in one run: its `RETURN_CALL_REF` bubbles out of its
labels (`return_call_ref-label`), leaves the frame (`return_call_ref-frame-addr`, or
`-frame-null`) and makes the same call:

* `PendR.shape`: a pending pair is a nest of labels on each side around the same innermost
  values, the source's `RETURN_CALL_REF` and the target's `CALL_REF; RETURN`;
* `fill_inv`: a step of a nest of labels around code whose first non-value is a `CALL_REF` is a
  step of that code;
* **`ce_frame_pend`**: the catch-up, with the callee's arity from the source's typing
  (`frameAddr_arity`); the results are a wrapped callee (`CE.wrap`), returned values inside the
  wrapper (`CE.vals`), a trap or a throw, or (for a divergent host call) the source's call redex
  against the target's pending wrapper (`CE.pend`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **The shape of a pending pair.** -/
theorem PendR.shape {b b' : List Admin} (hp : PendR b b') :
    ∃ (Nt Ns : NCtx) (V : List Val) (c c' : Admin) (X Y : List Admin), RCRPair c c' ∧
      b' = Nt.fill (vals V ++ c' :: .plain .return_ :: Y) ∧ b = Ns.fill (vals V ++ c :: X) := by
  induction hp with
  | @rcr V c c' x y hcc => exact ⟨.hole, .hole, V, c, c', x, y, hcc, rfl, rfl⟩
  | @label V n cont cont' b b' x y _ ih =>
    obtain ⟨Nt, Ns, V₀, c, c', X, Y, hcc, rfl, rfl⟩ := ih
    exact ⟨.label V n cont' Nt y, .label V n cont Ns x, V₀, c, c', X, Y, hcc, rfl, rfl⟩

/-- The first non-value of a nest around a `CALL_REF` is the `CALL_REF` or a label. -/
theorem fill_head (N : NCtx) {V : List Val} {c' : Admin} {Y : List Admin} (_hc : c'.IsCallRef) :
    ∃ V' b r, N.fill (vals V ++ c' :: Y) = vals V' ++ b :: r ∧
      (b = c' ∨ ∃ n cont bb, b = .label n cont bb) := by
  cases N with
  | hole => exact ⟨V, c', Y, rfl, .inl rfl⟩
  | label V₀ n cont N L => exact ⟨V₀, _, L, rfl, .inr ⟨_, _, _, rfl⟩⟩

/-- **A step of a nest around a `CALL_REF`** is a step of its innermost code. -/
theorem fill_inv {V : List Val} {c' : Admin} {Y : List Admin} (hc : c'.IsCallRef) :
    ∀ (N : NCtx) {t t' : Store H} {g g' : Frame} {Z : List Admin},
      Step P host ⟨t, g, N.fill (vals V ++ c' :: Y)⟩ ⟨t', g', Z⟩ →
      ∃ X', Step P host ⟨t, g, vals V ++ c' :: Y⟩ ⟨t', g', X'⟩ ∧ Z = N.fill X'
  | .hole, t, t', g, g', Z, h => ⟨Z, h, rfl⟩
  | .label V₀ n cont N L, t, t', g, g', Z, h => by
    rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨hc', -⟩ | ⟨hc', -⟩
    rotate_left
    · cases hc'
    · cases hc'
    obtain ⟨is₂, hred, rfl⟩ := Closure.Step.label_inv hs
    have hnotexit : ∀ (vs : List Val) (k : Admin) (r : List Admin), k.val? = none →
        N.fill (vals V ++ c' :: Y) = vals vs ++ k :: r → k = c' ∨ ∃ n cont bb, k = .label n cont bb := by
      intro vs k r hk hx
      obtain ⟨V', b, r', he, hb⟩ := fill_head N (V := V) (Y := Y) hc
      rw [he] at hx
      have hbv : b.val? = none := by
        rcases hb with rfl | ⟨_, _, _, rfl⟩
        · exact Admin.val?_of_isCallRef hc
        · rfl
      obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hbv hk hx
      exact hb
    have hcv : c'.val? = none := Admin.val?_of_isCallRef hc
    generalize hB : N.fill (vals V ++ c' :: Y) = B at hred
    cases hred with
    | ctxt hs₁ =>
      subst hB
      obtain ⟨X', hX, rfl⟩ := fill_inv hc N hs₁
      refine ⟨X', hX, ?_⟩
      simp [NCtx.fill, hV]
    | values vs =>
      exfalso
      obtain ⟨V', b, r', he, hb⟩ := fill_head N (V := V) (Y := Y) hc
      have hm : b ∈ vals vs := by rw [← hB, he]; simp
      obtain ⟨w, rfl⟩ := PC.mem_vals hm
      rcases hb with hb | ⟨_, _, _, hb⟩
      · rw [← hb] at hcv; simp at hcv
      · rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hb
    | @brZero vs' vs l rest hl hn =>
      exfalso
      rcases hnotexit (vs' ++ vs) (.plain (.br l)) rest rfl (by rw [hB]; simp) with h1 |
        ⟨_, _, _, h1⟩
      · rw [← h1] at hc; exact hc
      · cases h1
    | @brSucc vs l rest hl =>
      exfalso
      rcases hnotexit vs (.plain (.br l)) rest rfl (by rw [hB]; simp) with h1 | ⟨_, _, _, h1⟩
      · rw [← h1] at hc; exact hc
      · cases h1
    | @returnCallRef vs c₀ rest hc₀ =>
      exfalso
      rcases hnotexit vs c₀ rest (Admin.val?_of_isReturnCallRef hc₀) (by rw [hB]; simp) with h1 |
        ⟨_, _, _, h1⟩
      · subst h1; exact Admin.IsCallRef.not_isReturnCallRef hc hc₀
      · subst h1; exact hc₀
    | @return_ vs rest =>
      exfalso
      rcases hnotexit vs (.plain .return_) rest rfl (by rw [hB]; simp) with h1 | ⟨_, _, _, h1⟩
      · rw [← h1] at hc; exact hc
      · cases h1
    | throwRef a =>
      exfalso
      rcases hnotexit [.ref (.exn a)] (.plain .throwRef) [] rfl (by
        rw [hB]; simp [throwing, vals, Val.toAdmin]) with h1 | ⟨_, _, _, h1⟩
      · rw [← h1] at hc; exact hc
      · cases h1
    | trap =>
      exfalso
      rcases hnotexit [] .trap [] rfl (by rw [hB]; simp) with h1 |
        ⟨_, _, _, h1⟩
      · rw [← h1] at hc; exact hc
      · cases h1

end Silmaril.Raw.Wasm.LimeCompile.TailSim
