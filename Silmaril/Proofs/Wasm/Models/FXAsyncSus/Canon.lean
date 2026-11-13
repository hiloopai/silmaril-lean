module

public import Silmaril.Wasm.Models.FXAsyncBack.Thms

/-!
# Contexts of suspension in canonical form, and their uniqueness at a deep focus

A context `CtxV` may nest value sequences in many ways that plug alike. `canon E` is its
canonical form (`CCtx`): the layers of labels, frames and handlers from the outside in, each
with the values before it and the code after it, and an innermost value prefix and suffix.

* `canon_plug`, `canon_frameAt`, `canon_handles`: plugging, the frame at the hole and the
  handled tags are read off the canonical form;
* `canon_comp_handler`: the canonical form of `comp E₁ (.handler hs E₂)`;
* **`canon_unique`**: if `E.plug (fvals vs ++ [e]) = E'.plug (fvals vs' ++ [e])` for a
  non-value `e` that is not a label, frame or handler, then `E` and `E'` have the same layers
  and suffix, and `pre E ++ vs = pre E' ++ vs'`. So the context that a `suspend` captures is
  fixed by the plugged code up to how the values before the `suspend` are split.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append_cons_inj)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (IsWrap)

/-- A label, frame or handler, without its body. -/
inductive Wrp where
  | label (n : Nat) (k : List InstrFX)
  | frame (n : Nat) (f : Frame)
  | handler (hs : List HClause)

/-- Wrap a body. -/
def Wrp.wrap : Wrp → List AdminFX → AdminFX
  | .label n k, b => .label n k b
  | .frame n f, b => .frame n f b
  | .handler hs, b => .handler hs b

/-- A layer: a wrapper with the values before it and the code after it. -/
structure Layer where
  pre : List FVal
  w : Wrp
  post : List AdminFX

/-- Plug code into layers (outermost first). -/
def plugLs : List Layer → List AdminFX → List AdminFX
  | [], c => c
  | L :: Ls, c => fvals L.pre ++ L.w.wrap (plugLs Ls c) :: L.post

/-- A canonical context: an innermost value prefix and suffix, and the layers. -/
structure CCtx where
  pre : List FVal
  post : List AdminFX
  layers : List Layer

/-- Plug a canonical context. -/
def CCtx.plug (C : CCtx) (c : List AdminFX) : List AdminFX :=
  plugLs C.layers (fvals C.pre ++ c ++ C.post)

/-- Values before and code after a canonical context. -/
def seqC (vs : List FVal) (C : CCtx) (rest : List AdminFX) : CCtx :=
  match C.layers with
  | [] => ⟨vs ++ C.pre, C.post ++ rest, []⟩
  | L :: Ls => ⟨C.pre, C.post, { L with pre := vs ++ L.pre, post := L.post ++ rest } :: Ls⟩

/-- The canonical form of a context. -/
def canon : CtxV → CCtx
  | .hole => ⟨[], [], []⟩
  | .seq vs E rest => seqC vs (canon E) rest
  | .label n k E => let C := canon E; ⟨C.pre, C.post, ⟨[], .label n k, []⟩ :: C.layers⟩
  | .frame n f E => let C := canon E; ⟨C.pre, C.post, ⟨[], .frame n f, []⟩ :: C.layers⟩
  | .handler hs E => let C := canon E; ⟨C.pre, C.post, ⟨[], .handler hs, []⟩ :: C.layers⟩

/-- The frame at the hole of layers, from frame `f`. -/
def frameLs : List Layer → Frame → Frame
  | [], f => f
  | ⟨_, .frame _ fi, _⟩ :: Ls, _ => frameLs Ls fi
  | _ :: Ls, f => frameLs Ls f

/-- A layer is a handler with a clause for `ta`. -/
def Layer.Handles (ta : Nat) (L : Layer) : Prop :=
  ∃ hs, L.w = .handler hs ∧ ∃ c ∈ hs, c.tag = ta

/-! ## Reading plugging, frames and handlers off the canonical form -/

theorem seqC_plug (vs : List FVal) (C : CCtx) (rest c : List AdminFX) :
    (seqC vs C rest).plug c = fvals vs ++ C.plug c ++ rest := by
  rcases C with ⟨p, q, _ | ⟨L, Ls⟩⟩ <;> simp [seqC, CCtx.plug, plugLs, fvals]

theorem seqC_frame (vs : List FVal) (C : CCtx) (rest : List AdminFX) (f : Frame) :
    frameLs (seqC vs C rest).layers f = frameLs C.layers f := by
  rcases C with ⟨p, q, _ | ⟨⟨a, w, b⟩, Ls⟩⟩
  · rfl
  · cases w <;> rfl

theorem seqC_handles (vs : List FVal) (C : CCtx) (rest : List AdminFX) (ta : Nat) :
    (∃ L ∈ (seqC vs C rest).layers, L.Handles ta) ↔ ∃ L ∈ C.layers, L.Handles ta := by
  rcases C with ⟨p, q, _ | ⟨L, Ls⟩⟩ <;> simp [seqC, Layer.Handles]

theorem canon_plug (E : CtxV) (c : List AdminFX) : (canon E).plug c = E.plug c := by
  induction E with
  | hole => simp [canon, CCtx.plug, plugLs, CtxV.plug, fvals]
  | seq vs E rest ih =>
    rw [CtxV.plug, ← ih, canon]
    exact seqC_plug vs (canon E) rest c
  | label n k E ih => simp [canon, CCtx.plug, plugLs, CtxV.plug, ← ih, Wrp.wrap, fvals]
  | frame n f E ih => simp [canon, CCtx.plug, plugLs, CtxV.plug, ← ih, Wrp.wrap, fvals]
  | handler hs E ih => simp [canon, CCtx.plug, plugLs, CtxV.plug, ← ih, Wrp.wrap, fvals]

theorem canon_frameAt (E : CtxV) (f : Frame) : frameLs (canon E).layers f = E.frameAt f := by
  induction E generalizing f with
  | hole => rfl
  | seq vs E rest ih =>
    rw [CtxV.frameAt, ← ih, canon]
    exact seqC_frame vs (canon E) rest f
  | label n k E ih => exact ih f
  | frame n fi E ih => exact ih fi
  | handler hs E ih => exact ih f

theorem canon_handles (E : CtxV) (ta : Nat) :
    (∃ L ∈ (canon E).layers, L.Handles ta) ↔ E.Handles ta := by
  induction E with
  | hole => simp [canon, CtxV.Handles]
  | seq vs E rest ih =>
    rw [CtxV.Handles, ← ih, canon]
    exact seqC_handles vs (canon E) rest ta
  | label n k E ih => simp [canon, CtxV.Handles, ← ih, Layer.Handles]
  | frame n f E ih => simp [canon, CtxV.Handles, ← ih, Layer.Handles]
  | handler hs E ih => simp [canon, CtxV.Handles, ← ih, Layer.Handles]

/-- The canonical form of a context ending in a handler. -/
theorem canon_comp_handler (E₁ : CtxV) (hs : List HClause) (E₂ : CtxV) :
    canon (Silmaril.Wasm.Models.FXAsyncFX.comp E₁ (.handler hs E₂)) =
      ⟨(canon E₂).pre, (canon E₂).post,
        (canon E₁).layers ++ ⟨(canon E₁).pre, .handler hs, (canon E₁).post⟩ ::
          (canon E₂).layers⟩ := by
  induction E₁ with
  | hole => simp [canon, Silmaril.Wasm.Models.FXAsyncFX.comp]
  | seq vs E rest ih =>
    simp only [Silmaril.Wasm.Models.FXAsyncFX.comp, canon, ih]
    rcases hE : (canon E).layers with _ | ⟨L, Ls⟩ <;> simp [seqC, hE]
  | label n k E ih => simp [canon, Silmaril.Wasm.Models.FXAsyncFX.comp, ih]
  | frame n f E ih => simp [canon, Silmaril.Wasm.Models.FXAsyncFX.comp, ih]
  | handler hs' E ih => simp [canon, Silmaril.Wasm.Models.FXAsyncFX.comp, ih]

/-! ## Uniqueness -/

theorem wrap_fval (w : Wrp) (b : List AdminFX) : fval? (w.wrap b) = none := by
  cases w <;> rfl

theorem wrap_isWrap (w : Wrp) (b : List AdminFX) : IsWrap (w.wrap b) := by
  cases w <;> trivial

theorem wrap_inj {w w' : Wrp} {b b' : List AdminFX} (h : w.wrap b = w'.wrap b') :
    w = w' ∧ b = b' := by
  cases w <;> cases w' <;> simp_all [Wrp.wrap]

/-- **Layers are fixed by the plugged code at a deep focus.** -/
theorem plugLs_unique {e : AdminFX} (he : fval? e = none) (hw : ¬ IsWrap e) :
    ∀ (Ls Ls' : List Layer) {V V' : List FVal} {T T' : List AdminFX},
      plugLs Ls (fvals V ++ e :: T) = plugLs Ls' (fvals V' ++ e :: T') →
      Ls = Ls' ∧ V = V' ∧ T = T'
  | [], [], _, _, _, _, h => by
    obtain ⟨hV, -, hT⟩ := fvals_append_cons_inj h he he
    exact ⟨rfl, hV, hT⟩
  | [], L' :: Ls', _, _, _, _, h => by
    obtain ⟨-, he', -⟩ := fvals_append_cons_inj h he (wrap_fval _ _)
    exact absurd (he' ▸ wrap_isWrap _ _) hw
  | L :: Ls, [], _, _, _, _, h => by
    obtain ⟨-, he', -⟩ := fvals_append_cons_inj h (wrap_fval _ _) he
    exact absurd (he' ▸ wrap_isWrap _ _) hw
  | L :: Ls, L' :: Ls', _, _, _, _, h => by
    obtain ⟨hpre, hwr, hpost⟩ := fvals_append_cons_inj h (wrap_fval _ _) (wrap_fval _ _)
    obtain ⟨hw', hb⟩ := wrap_inj hwr
    obtain ⟨rfl, hV, hT⟩ := plugLs_unique he hw Ls Ls' hb
    exact ⟨by cases L; cases L'; simp_all, hV, hT⟩

/-- **A context is fixed by the plugged code at a deep focus**, up to the split of the values
in front of it. -/
theorem canon_unique {e : AdminFX} (he : fval? e = none) (hw : ¬ IsWrap e) {E E' : CtxV}
    {vs vs' : List FVal} (h : E.plug (fvals vs ++ [e]) = E'.plug (fvals vs' ++ [e])) :
    (canon E).layers = (canon E').layers ∧ (canon E).pre ++ vs = (canon E').pre ++ vs' ∧
      (canon E).post = (canon E').post := by
  rw [← canon_plug, ← canon_plug] at h
  have hc : ∀ (C : CCtx) (ws : List FVal),
      C.plug (fvals ws ++ [e]) = plugLs C.layers (fvals (C.pre ++ ws) ++ e :: C.post) := by
    intro C ws
    simp [CCtx.plug, fvals]
  rw [hc, hc] at h
  obtain ⟨hL, hV, hT⟩ := plugLs_unique he hw _ _ h
  exact ⟨hL, hV, hT⟩

/-- Contexts with the same canonical form plug alike. -/
theorem plug_eq_of_canon {E E' : CtxV} (h : canon E = canon E') : E.plug = E'.plug := by
  funext c
  rw [← canon_plug, ← canon_plug, h]

end Silmaril.Proofs.Wasm.Models.FXAsyncSus
