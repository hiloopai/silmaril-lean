module

public import Silmaril.Raw.Wasm.Auto.ESeg.Comp2

/-! # Soundness of the extended chains and of covers

* `applyX_sound`, `runX_sound`, `checkEqX_sound`, `evalL_eq_of_checkEqXL`: an extended chain
  (pass-1 steps used as equations, and the computed rewrites `comp2?`) keeps the value in every
  frame typed by `Γ`;
* `get?_isSome`: a subterm of a term that does not trap does not trap (evaluation is strict);
* `coversOk_sound`: if every term of the other side has a value, so has every covered term.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.EGraph

variable {Γ : List IntType} {rules : List Rule} {f : Frame}

theorem baseEq_sound (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) {e e' : Term} {s : Step}
    (h : baseEq Γ rules e s = some e') : e.eval f = e'.eval f := by
  unfold baseEq at h
  split at h
  · rename_i e₀ h₀
    cases h
    exact (applyStep_sound hR hf h₀).2 rfl
  · cases h

/-- **An extended step keeps the value.** -/
theorem applyX_sound (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) {e e' : Term} :
    ∀ {s : XStep}, applyX Γ rules e s = some e' → e.eval f = e'.eval f
  | .rw _ _ _ _, h | .fold _, h | .unfold _ _, h | .comp _, h | .uncomp _ _, h =>
    baseEq_sound hR hf h
  | .comp2 p, h => by
    obtain ⟨a, hg, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hc, hs⟩ := Option.bind_eq_some_iff.mp h
    exact set_eq (comp2?_eval hc) hg hs
  | .uncomp2 p b, h => by
    obtain ⟨a, hg, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hc
      exact set_eq (comp2?_eval hc).symm hg h
    · cases h

/-- **An extended chain keeps the value.** -/
theorem runX_sound (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) :
    ∀ {ss : List XStep} {e e' : Term}, runX Γ rules e ss = some e' → e.eval f = e'.eval f
  | [], e, e', h => by cases h; rfl
  | s :: ss, e, e', h => by
    simp only [runX] at h
    split at h
    · rename_i e₁ h₁
      exact (applyX_sound hR hf h₁).trans (runX_sound hR hf h)
    · cases h

/-- **Soundness of the extended equivalence checker.** -/
theorem checkEqX_sound (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) {e₁ e₂ : Term}
    {ss : List XStep} (h : checkEqX Γ rules e₁ e₂ ss = true) : e₁.eval f = e₂.eval f := by
  unfold checkEqX at h
  split at h
  · rename_i e he
    have he₂ : e = e₂ := by simpa using h
    rw [← he₂]
    exact runX_sound hR hf he
  · cases h

theorem evalL_eq_of_checkEqXL (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) :
    ∀ {es₁ es₂ : List Term} {cs : List (List XStep)}, checkEqXL Γ rules es₁ es₂ cs = true →
      evalL f es₁ = evalL f es₂
  | [], [], [], _ => rfl
  | e₁ :: es₁, e₂ :: es₂, c :: cs, h => by
    simp only [checkEqXL, Bool.and_eq_true] at h
    simp only [evalL, checkEqX_sound hR hf h.1, evalL_eq_of_checkEqXL hR hf h.2]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [checkEqXL] at h

/-! ## Strictness and covers -/

theorem unV_isSome {t : IntType} {op : IntUnOp} {a : Option Val} (h : (unV t op a).isSome) :
    a.isSome := by
  cases a <;> simp_all [unV]

theorem testV_isSome {t : IntType} {a : Option Val} (h : (testV t a).isSome) : a.isSome := by
  cases a <;> simp_all [testV]

theorem binV_isSome {t : IntType} {op : IntBinOp} {a b : Option Val}
    (h : (binV t op a b).isSome) : a.isSome ∧ b.isSome := by
  cases a <;> cases b <;> simp_all [binV]

theorem relV_isSome {t : IntType} {op : IntRelOp} {a b : Option Val}
    (h : (relV t op a b).isSome) : a.isSome ∧ b.isSome := by
  cases a <;> cases b <;> simp_all [relV]

/-- **Evaluation is strict**: a subterm of a term with a value has a value. -/
theorem get?_isSome : ∀ {r r' : Term} {p : List Nat}, r.get? p = some r' →
    (r.eval f).isSome → (r'.eval f).isSome
  | r, r', [], hg, h => by
    have : r = r' := by simpa [Term.get?] using hg
    exact this ▸ h
  | .un _ _ a, r', 0 :: p, hg, h => get?_isSome (r := a) hg (unV_isSome h)
  | .test _ a, r', 0 :: p, hg, h => get?_isSome (r := a) hg (testV_isSome h)
  | .bin _ _ a _, r', 0 :: p, hg, h => get?_isSome (r := a) hg (binV_isSome h).1
  | .rel _ _ a _, r', 0 :: p, hg, h => get?_isSome (r := a) hg (relV_isSome h).1
  | .bin _ _ _ b, r', 1 :: p, hg, h => get?_isSome (r := b) hg (binV_isSome h).2
  | .rel _ _ _ b, r', 1 :: p, hg, h => get?_isSome (r := b) hg (relV_isSome h).2
  | .const _ _, _, _ :: _, hg, _ | .lget _, _, _ :: _, hg, _ => by simp [Term.get?] at hg
  | .un _ _ _, _, (_ + 1) :: _, hg, _ | .test _ _, _, (_ + 1) :: _, hg, _ => by
    simp [Term.get?] at hg
  | .bin _ _ _ _, _, (_ + 2) :: _, hg, _ | .rel _ _ _ _, _, (_ + 2) :: _, hg, _ => by
    simp [Term.get?] at hg

/-- A typed term with a value is an integer of its type. -/
theorem typed_some {Γ : List IntType} (hf : FrameOk Γ f) {e : Term} {t : IntType}
    (ht : e.typeOf Γ = some t) (hs : (e.eval f).isSome) : ∃ x, e.eval f = some (intVal t x) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨x, rfl⟩ := typeOf_sound hf ht v hv
  exact ⟨x, hv⟩

/-- One cover is sound. -/
theorem coverOk_sound (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) {other : List Term}
    (ho : ∀ r ∈ other, (r.eval f).isSome) :
    ∀ {c : Cover} {e : Term}, coverOk Γ rules other e c = true → (e.eval f).isSome
  | .total, e, h => by
    simp only [coverOk, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨hn, t, ht⟩ := h
    obtain ⟨x, hx⟩ := noTrap_total hf ht hn
    simp [hx]
  | .sub j p ss, e, h => by
    simp only [coverOk] at h
    split at h
    · rename_i r hr
      split at h
      · rename_i r' hr'
        rw [checkEqX_sound hR hf h]
        exact get?_isSome hr' (ho r (List.mem_of_getElem? hr))
      · cases h
    · cases h
  | .split1 c, .un t op a, h => by
    simp only [coverOk, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨t', ht⟩, hc⟩ := h
    have hta : a.typeOf Γ = some t := by
      simp only [Term.typeOf] at ht; split at ht <;> simp_all
    obtain ⟨x, hx⟩ := typed_some hf hta (coverOk_sound hR hf ho hc)
    simp [Term.eval, unV, hx]
  | .split1 c, .test t a, h => by
    simp only [coverOk, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨t', ht⟩, hc⟩ := h
    have hta : a.typeOf Γ = some t := by
      simp only [Term.typeOf] at ht; split at ht <;> simp_all
    obtain ⟨x, hx⟩ := typed_some hf hta (coverOk_sound hR hf ho hc)
    simp [Term.eval, testV, hx]
  | .split2 c₁ c₂, .bin t op a b, h => by
    simp only [coverOk, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨hs, t', ht⟩, hc₁⟩, hc₂⟩ := h
    have htab : a.typeOf Γ = some t ∧ b.typeOf Γ = some t := by
      simp only [Term.typeOf] at ht; split at ht <;> simp_all
    obtain ⟨x, hx⟩ := typed_some hf htab.1 (coverOk_sound hR hf ho hc₁)
    obtain ⟨y, hy⟩ := typed_some hf htab.2 (coverOk_sound hR hf ho hc₂)
    obtain ⟨z, hz⟩ := intBinOp_ok_of_safe (x := x) hs hy
    simp [Term.eval, binV, hx, hy, hz]
  | .split2 c₁ c₂, .rel t op a b, h => by
    simp only [coverOk, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨t', ht⟩, hc₁⟩, hc₂⟩ := h
    have htab : a.typeOf Γ = some t ∧ b.typeOf Γ = some t := by
      simp only [Term.typeOf] at ht; split at ht <;> simp_all
    obtain ⟨x, hx⟩ := typed_some hf htab.1 (coverOk_sound hR hf ho hc₁)
    obtain ⟨y, hy⟩ := typed_some hf htab.2 (coverOk_sound hR hf ho hc₂)
    simp [Term.eval, relV, hx, hy]
  | .chain ss c, e, h => by
    simp only [coverOk] at h
    split at h
    · rename_i e' he'
      rw [runX_sound hR hf he']
      exact coverOk_sound hR hf ho h
    · cases h
  | .split1 _, .const _ _, h | .split1 _, .lget _, h | .split1 _, .bin _ _ _ _, h
  | .split1 _, .rel _ _ _ _, h | .split2 _ _, .const _ _, h | .split2 _ _, .lget _, h
  | .split2 _ _, .un _ _ _, h | .split2 _ _, .test _ _, h => by simp [coverOk] at h

/-- **Covers are sound**: if every term of the other side has a value, so has every term of
this side. -/
theorem coversOk_sound (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) {other : List Term}
    (ho : ∀ r ∈ other, (r.eval f).isSome) :
    ∀ {es : List Term} {cs : List Cover}, coversOk Γ rules other es cs = true →
      ∀ e ∈ es, (e.eval f).isSome
  | [], [], _, e, he => by simp at he
  | e₀ :: es, c :: cs, h, e, he => by
    simp only [coversOk, Bool.and_eq_true] at h
    rcases List.mem_cons.mp he with rfl | he'
    · exact coverOk_sound hR hf ho h.1
    · exact coversOk_sound hR hf ho h.2 e he'
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => by simp [coversOk] at h

end Silmaril.Proofs.Wasm.Auto.ESeg