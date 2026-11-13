module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Root
public import Silmaril.Wasm.Models.FXAsyncSus.Thms

/-!
# Contexts of an effect: decomposition and plug-equality

A stopped effect `E.plug (fvals vs ++ [e])` (`e` the `suspend` or `switch`) is seen by the
context rules through pieces of code. These lemmas find the context of each piece:

* `plug_cases`: the plugged code is values, then the focus `e` or a label, frame or handler;
* `plug_app_inv`: if `c₁ ++ c₂` is plugged and `c₁` is not all values, `c₁` is plugged too;
* `plug_wrp_inv`: if `[w b]` (a label, frame or handler) is plugged, `b` is plugged;
* `plug_vals_wrp_inv`: if `vs ++ [w b]` is plugged, `[w b]` is plugged;
* `canon_eq_of_plug`: contexts that plug the same code with the same payload have the same
  canonical form (`Silmaril.Proofs.Wasm.Models.FXAsyncSus.canon_unique`), hence the same plugging
  function, frame at the hole and handled tags (`Unhandled.of_canon`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic.EveryRun (Unhandled suspCode switchCode)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append_cons_inj fvals_eq_append)
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (canon canon_unique canon_frameAt canon_handles
  plug_eq_of_canon CCtx Wrp)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (IsWrap)

variable {H : Type}

/-! ## Wrappers as contexts -/

theorem wrap_fval (w : Wrp) (b : List AdminFX) : fval? (w.wrap b) = none := by
  cases w <;> rfl

theorem wrap_isWrap (w : Wrp) (b : List AdminFX) : IsWrap (w.wrap b) := by
  cases w <;> trivial

theorem wrap_inj {w w' : Wrp} {b b' : List AdminFX} (h : w.wrap b = w'.wrap b') :
    w = w' ∧ b = b' := by
  cases w <;> cases w' <;> simp_all [Wrp.wrap]

/-! ## The shape of plugged code -/

section Plug

variable {vs : List FVal} {e : AdminFX}

theorem plug_cases (he : fval? e = none) (E : CtxV) :
    ∃ V a R, E.plug (fvals vs ++ [e]) = fvals V ++ a :: R ∧ fval? a = none ∧ (a = e ∨ IsWrap a) := by
  induction E with
  | hole => exact ⟨vs, e, [], rfl, he, Or.inl rfl⟩
  | seq us E rest ih =>
    obtain ⟨V, a, R, h, ha, hae⟩ := ih
    exact ⟨us ++ V, a, R ++ rest, by simp [CtxV.plug, h], ha, hae⟩
  | label n k E _ => exact ⟨[], _, [], rfl, rfl, Or.inr trivial⟩
  | frame n f E _ => exact ⟨[], _, [], rfl, rfl, Or.inr trivial⟩
  | handler hs E _ => exact ⟨[], _, [], rfl, rfl, Or.inr trivial⟩

theorem plug_ne_fvals (he : fval? e = none) (E : CtxV) (V : List FVal) :
    E.plug (fvals vs ++ [e]) ≠ fvals V := by
  intro h
  obtain ⟨V', a, R, h', ha, -⟩ := plug_cases (vs := vs) he E
  have h'' : fvals V ++ [] = fvals V' ++ a :: R := by rw [List.append_nil, ← h, h']
  have := congrArg (fun l => (Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF l).2) h''
  simp [Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF_fvals_append,
    Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF_cons_none ha] at this

/-- The focus of plugged code is `e` or a wrapper. -/
theorem plug_focus (he : fval? e = none) {E : CtxV} {V : List FVal}
    {a : AdminFX} {R : List AdminFX} (ha : fval? a = none)
    (h : E.plug (fvals vs ++ [e]) = fvals V ++ a :: R) : a = e ∨ IsWrap a := by
  obtain ⟨V', a', R', h', ha', hae⟩ := plug_cases (vs := vs) he E
  obtain ⟨-, rfl, -⟩ := fvals_append_cons_inj (h.symm.trans h') ha ha'
  exact hae

/-- A one-element list split with a nonempty left part. -/
theorem singleton_split {a : AdminFX} {c₁ c₂ : List AdminFX} (h : [a] = c₁ ++ c₂)
    (hc : c₁ ≠ []) : c₁ = [a] ∧ c₂ = [] := by
  rcases c₁ with _ | ⟨b, _ | ⟨b', l⟩⟩
  · exact absurd rfl hc
  · simp only [List.singleton_append, List.cons.injEq] at h
    exact ⟨by rw [h.1], h.2.symm⟩
  · simp at h

theorem not_fvals_nil : ¬ ∃ U, ([] : List AdminFX) ≠ [] ∧ [] = fvals U := by simp

/-- The hole case of `plug_app_inv`. -/
theorem plug_app_hole {c₁ c₂ : List AdminFX} (h : fvals vs ++ [e] = c₁ ++ c₂)
    (hU : ∀ U, c₁ ≠ fvals U) : c₁ = fvals vs ++ [e] := by
  rcases List.append_eq_append_iff.mp h with ⟨a', rfl, h'⟩ | ⟨c', h₁, rfl⟩
  · rcases a' with _ | ⟨b, a''⟩
    · exact absurd (by simp) (hU vs)
    · have h'' : b = e ∧ a'' = [] ∧ c₂ = [] := by
        simp only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff] at h'
        exact ⟨h'.1.symm, h'.2.1, h'.2.2⟩
      rw [h''.1, h''.2.1]
  · obtain ⟨V₁, V₂, -, hA, -⟩ := fvals_eq_append h₁
    exact absurd hA (hU V₁)

/-- The wrapper cases of `plug_app_inv`. -/
theorem plug_app_wrap {a : AdminFX} {c₁ c₂ : List AdminFX} (h : [a] = c₁ ++ c₂)
    (hU : ∀ U, c₁ ≠ fvals U) : c₁ = [a] :=
  (singleton_split h (fun hc => hU [] (by simp [hc]))).1

/-- The prefix split of the sequence case of `plug_app_inv`. -/
theorem plug_app_seq {us : List FVal} {p c₁ c₂ : List AdminFX} (h : fvals us ++ p = c₁ ++ c₂)
    (hU : ∀ U, c₁ ≠ fvals U) : ∃ m, c₁ = fvals us ++ m ∧ p = m ++ c₂ ∧ ∀ U, m ≠ fvals U := by
  rcases List.append_eq_append_iff.mp h with ⟨m, rfl, h₂⟩ | ⟨m', h₃, -⟩
  · exact ⟨m, rfl, h₂, fun U hm => hU (us ++ U) (by simp [hm])⟩
  · obtain ⟨V₁, V₂, -, hA, -⟩ := fvals_eq_append h₃
    exact absurd hA (hU V₁)

/-- **A piece of plugged code that is not all values is plugged.** -/
theorem plug_app_inv (he : fval? e = none) :
    ∀ (E : CtxV) {c₁ c₂ : List AdminFX}, E.plug (fvals vs ++ [e]) = c₁ ++ c₂ →
      (∀ U, c₁ ≠ fvals U) → ∃ E₁ : CtxV, c₁ = E₁.plug (fvals vs ++ [e])
  | .hole, _, _, h, hU => ⟨.hole, plug_app_hole h hU⟩
  | .seq us E rest, c₁, c₂, h, hU => by
    have h' : (fvals us ++ E.plug (fvals vs ++ [e])) ++ rest = c₁ ++ c₂ := by
      simpa [CtxV.plug] using h
    rcases List.append_eq_append_iff.mp h' with ⟨r₁, rfl, -⟩ | ⟨c', h₁, rfl⟩
    · exact ⟨.seq us E r₁, by simp [CtxV.plug]⟩
    · obtain ⟨m, rfl, h₂, hm⟩ := plug_app_seq h₁ hU
      obtain ⟨E₁, hE₁⟩ := plug_app_inv he E h₂ hm
      exact ⟨.seq us E₁ [], by simp [CtxV.plug, hE₁]⟩
  | .label n k E, _, _, h, hU => ⟨.label n k E, plug_app_wrap h hU⟩
  | .frame n fi E, _, _, h, hU => ⟨.frame n fi E, plug_app_wrap h hU⟩
  | .handler hs E, _, _, h, hU => ⟨.handler hs E, plug_app_wrap h hU⟩

/-- **The body of a plugged wrapper is plugged.** -/
theorem plug_wrp_inv (he : fval? e = none) (hw : ¬ IsWrap e) :
    ∀ (E : CtxV) {w : Wrp} {b : List AdminFX}, E.plug (fvals vs ++ [e]) = [w.wrap b] →
      ∃ E' : CtxV, b = E'.plug (fvals vs ++ [e])
  | .hole, w, b, h => by
    obtain ⟨-, rfl, -⟩ := fvals_append_cons_inj (V₂ := []) h he (wrap_fval w b)
    exact absurd (wrap_isWrap w b) hw
  | .seq us E rest, w, b, h => by
    obtain ⟨V, a, R, hp, ha, -⟩ := plug_cases (vs := vs) he E
    have h' : fvals (us ++ V) ++ a :: (R ++ rest) = fvals [] ++ w.wrap b :: [] := by
      rw [← h]; simp [CtxV.plug, hp]
    obtain ⟨hV, rfl, hR⟩ := fvals_append_cons_inj h' ha (wrap_fval w b)
    obtain ⟨-, rfl⟩ := List.append_eq_nil_iff.mp hV
    obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hR
    exact plug_wrp_inv he hw E (w := w) (b := b) (by simpa using hp)
  | .label n k E, w, b, h => by
    obtain ⟨-, rfl⟩ := wrap_inj (w := .label n k) (List.singleton_inj.mp h)
    exact ⟨E, rfl⟩
  | .frame n fi E, w, b, h => by
    obtain ⟨-, rfl⟩ := wrap_inj (w := .frame n fi) (List.singleton_inj.mp h)
    exact ⟨E, rfl⟩
  | .handler hs E, w, b, h => by
    obtain ⟨-, rfl⟩ := wrap_inj (w := .handler hs) (List.singleton_inj.mp h)
    exact ⟨E, rfl⟩

/-- **A plugged wrapper under values is plugged.** -/
theorem plug_vals_wrp_inv (he : fval? e = none) (hw : ¬ IsWrap e) :
    ∀ (E : CtxV) {us : List FVal} {a : AdminFX}, IsWrap a →
      E.plug (fvals vs ++ [e]) = fvals us ++ [a] → ∃ E' : CtxV, [a] = E'.plug (fvals vs ++ [e])
  | .hole, us, a, hwa, h => by
    obtain ⟨-, rfl, -⟩ := fvals_append_cons_inj h he (by cases a <;> trivial)
    exact absurd hwa hw
  | .seq us' E rest, us, a, hwa, h => by
    obtain ⟨V, a', R, hp, ha', -⟩ := plug_cases (vs := vs) he E
    have h' : fvals (us' ++ V) ++ a' :: (R ++ rest) = fvals us ++ a :: [] := by
      rw [← h]; simp [CtxV.plug, hp]
    obtain ⟨-, rfl, hR⟩ := fvals_append_cons_inj h' ha' (by cases a <;> trivial)
    obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hR
    exact plug_vals_wrp_inv he hw E hwa hp
  | .label n k E, us, a, _, h => ⟨.label n k E, by
      have hl := congrArg List.length h
      have hus : us = [] := List.length_eq_zero_iff.mp (by simpa [CtxV.plug] using hl)
      rw [h, hus]; rfl⟩
  | .frame n fi E, us, a, _, h => ⟨.frame n fi E, by
      have hl := congrArg List.length h
      have hus : us = [] := List.length_eq_zero_iff.mp (by simpa [CtxV.plug] using hl)
      rw [h, hus]; rfl⟩
  | .handler hs E, us, a, _, h => ⟨.handler hs E, by
      have hl := congrArg List.length h
      have hus : us = [] := List.length_eq_zero_iff.mp (by simpa [CtxV.plug] using hl)
      rw [h, hus]; rfl⟩

end Plug

/-! ## Plug-equal contexts -/

theorem cctx_ext {C C' : CCtx} (h₁ : C.pre = C'.pre) (h₂ : C.post = C'.post)
    (h₃ : C.layers = C'.layers) : C = C' := by
  cases C; cases C'; simp_all

/-- **Contexts that plug alike at a deep focus with the same payload are canonically equal.** -/
theorem canon_eq_of_plug {e : AdminFX} (he : fval? e = none) (hw : ¬ IsWrap e) {E E' : CtxV}
    {vs : List FVal} (h : E.plug (fvals vs ++ [e]) = E'.plug (fvals vs ++ [e])) :
    canon E = canon E' := by
  obtain ⟨hL, hp, hq⟩ := canon_unique he hw h
  exact cctx_ext (List.append_cancel_right hp) hq hL

theorem canon_of_susp {E E' : CtxV} {vs : List FVal} {x : TagIdx}
    (h : E.plug (suspCode vs x) = E'.plug (suspCode vs x)) : canon E = canon E' :=
  canon_eq_of_plug (e := .fx (.suspend x)) rfl id h

theorem switchCode_eq (vs : List FVal) (k : Nat) (ct : TypeIdx) (x : TagIdx) :
    switchCode vs k ct x = fvals (vs ++ [.cont k]) ++ [.fx (.switch ct x)] := by
  simp [switchCode, FVal.toAdmin]

theorem canon_of_switch {E E' : CtxV} {vs : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx}
    (h : E.plug (switchCode vs k ct x) = E'.plug (switchCode vs k ct x)) : canon E = canon E' := by
  rw [switchCode_eq] at h
  exact canon_eq_of_plug (e := .fx (.switch ct x)) rfl id h

theorem frameAt_of_canon {E E' : CtxV} (h : canon E = canon E') (f : Frame) :
    E.frameAt f = E'.frameAt f := by
  rw [← canon_frameAt, h, canon_frameAt]

theorem handles_of_canon {E E' : CtxV} (h : canon E = canon E') (ta : Nat) :
    E.Handles ta ↔ E'.Handles ta := by
  rw [← canon_handles, h, canon_handles]

theorem Unhandled.of_canon {s : Store H} {f : Frame} {E E' : CtxV} {x : TagIdx}
    (h : canon E = canon E') (hu : Unhandled s f E x) : Unhandled s f E' x := by
  intro ta ti ht hE
  rw [← frameAt_of_canon h] at ht
  exact hu ta ti ht ((handles_of_canon h ta).mpr hE)

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
