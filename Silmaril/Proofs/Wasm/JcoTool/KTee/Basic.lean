module

public import Silmaril.Wasm.JcoTool.KTee.Defs

/-!
# The generated tee: facts about the fragment and the guards

Generic facts of `KDrop.dexec` and the runtime (`dexec_ite_ret`, `dexec_seq_ret`, `dinvoke_inv`,
`dwait_index`), and the meaning of the tee's guards (`wrG_iff`, `rdG_iff`, `stopG_iff`,
`closeG_iff`, `exitG_iff`) and of the dispatch (`cbT_ret`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KTee

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Event EventCode blocked)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KTee

/-! ## The fragment -/

theorem dlab_ret {x : Option (Out × DSt)} {v : Nat} {s : DSt}
    (h : dexec.dlab x = some (.ret v, s)) : x = some (.ret v, s) := by
  rcases x with _ | ⟨o, t⟩
  · cases h
  · rcases o with _ | (_ | k) | w <;> simp_all [dexec.dlab]

/-- A branch of an `if` that returned. -/
theorem dexec_ite_ret {c : E} {t e : S} {f : Nat} {s s' : DSt} {v : Nat}
    (h : dexec (.ite c t e) f s = some (.ret v, s')) :
    (c.eval s.down ≠ 0 ∧ dexec t f s = some (.ret v, s')) ∨
      (c.eval s.down = 0 ∧ dexec e f s = some (.ret v, s')) := by
  have h' : dexec.dlab (if c.eval s.down ≠ 0 then dexec t f s else dexec e f s) =
      some (.ret v, s') := h
  by_cases hc : c.eval s.down = 0
  · simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte] at h'
    exact .inr ⟨hc, dlab_ret h'⟩
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte] at h'
    exact .inl ⟨hc, dlab_ret h'⟩

/-- A sequence that returned. -/
theorem dexec_seq_ret {a b : S} {f : Nat} {s s' : DSt} {v : Nat}
    (h : dexec (.seq a b) f s = some (.ret v, s')) :
    dexec a f s = some (.ret v, s') ∨
      ∃ s₁, dexec a f s = some (.norm, s₁) ∧ dexec b f s₁ = some (.ret v, s') := by
  simp only [dexec] at h
  rcases ha : dexec a f s with _ | ⟨o, s₁⟩
  · rw [ha] at h; cases h
  · rw [ha] at h
    rcases o with _ | k | w
    · exact .inr ⟨s₁, rfl, h⟩
    · cases h
    · exact .inl h

theorem dexec_seq_norm {a b : S} {f : Nat} {s s₁ : DSt} (h : dexec a f s = some (.norm, s₁)) :
    dexec (.seq a b) f s = dexec b f s₁ := by
  simp only [dexec, h]

/-- What an invocation that returned tells about the run of its body. -/
theorem dinvoke_inv {body : S} {ps : List Nat} {st st' : DStore} {ms ms' : MS}
    (h : dinvoke body ps st ms = some (st', ms')) :
    ∃ code s', dexec body FUEL ⟨ms.g, ms.m, locals ps, st, ms.rp⟩ = some (.ret code, s') ∧
      modeOf code = some ms'.mode ∧ st' = s'.st ∧ ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩ := by
  unfold dinvoke at h
  split at h
  · rename_i code s' hx
    cases hm : modeOf code with
    | none => rw [hm] at h; cases h
    | some md =>
      rw [hm] at h
      cases h
      exact ⟨code, s', hx, hm, rfl, rfl⟩
  · cases h

/-- The event's index is the handle it was taken from, and its code is that of the handle's
end. -/
theorem dwait_index {st st' : DStore} {s h : Nat} {e : Event} (hw : DWait st s h st' e) :
    e.index = h := by
  obtain ⟨-, -, ht⟩ := hw
  unfold takeEv at ht
  split at ht
  · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp ht
    rw [← (Prod.mk.inj hp).2]
  · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp ht
    rw [← (Prod.mk.inj hp).2]
  · cases ht

theorem code_two {c : EventCode} (h : c.toNat = 2) : c = .streamRead := by
  cases c <;> simp_all [EventCode.toNat]

theorem code_three {c : EventCode} (h : c.toNat = 3) : c = .streamWrite := by
  cases c <;> simp_all [EventCode.toNat]

theorem wfD_inv {e : Event} (h : wfD e = true) :
    e.payload < M32 ∧ e.index < M32 ∧ e.items.length ≤ 256 ∧
      (e.code = .streamRead → e.payload / 16 = e.items.length) := by
  simp only [wfD, wellFormed, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, -⟩, h₅⟩ := h
  refine ⟨h₁, h₂, h₃, fun hc => ?_⟩
  rcases h₅ with h₅ | h₅
  · exact absurd hc h₅
  · exact h₅

/-! ## Expressions -/

@[simp] theorem eval_ldA_RS (t : St) : (ldA aRS).eval t = t.m aRS := by
  simp [ldA, E.eval, aRS, M32]

@[simp] theorem eval_ldA_O (t : St) (j : Nat) (hj : j ≤ 1) : (ldA (aO j)).eval t = t.m (aO j) := by
  have : aO j % M32 = aO j := Nat.mod_eq_of_lt (by simp [aO, M32]; omega)
  simp [ldA, E.eval, this]

/-- A comparison's value is `0` or `1`. -/
theorem ite01 (p : Prop) [Decidable p] : (if p then 1 else 0 : Nat) ≤ 1 := by
  split <;> omega

theorem ite01_ne (p : Prop) [Decidable p] : (if p then 1 else 0 : Nat) ≠ 0 ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ite10_ne (p : Prop) [Decidable p] : (if p then 0 else 1 : Nat) ≠ 0 ↔ ¬ p := by
  by_cases hp : p <;> simp [hp]

theorem isE_ne (a : E) (v : Nat) (hv : v < M32) (t : St) :
    (isE a v).eval t ≠ 0 ↔ a.eval t = v := by
  simp only [isE, E.eval, Bin.eval, Nat.mod_eq_of_lt hv]
  exact ite01_ne _

theorem andE_ne (a b : E) (t : St) : (andE a b).eval t ≠ 0 ↔ a.eval t ≠ 0 ∧ b.eval t ≠ 0 := by
  simp only [andE, E.eval]
  by_cases ha : a.eval t = 0 <;> by_cases hb : b.eval t = 0 <;> simp [ha, hb, Bin.eval, M32]

/-- `orE` on `0/1` values. -/
theorem orE_ne (a b : E) (t : St) (ha : a.eval t ≤ 1) (hb : b.eval t ≤ 1) :
    (orE a b).eval t ≠ 0 ↔ a.eval t ≠ 0 ∨ b.eval t ≠ 0 := by
  have hm : (a.eval t + b.eval t) % M32 = a.eval t + b.eval t :=
    Nat.mod_eq_of_lt (by simp [M32]; omega)
  have h0 : (0 : Nat) % M32 = 0 := rfl
  show (if (a.eval t + b.eval t) % M32 = 0 % M32 then 0 else 1 : Nat) ≠ 0 ↔ _
  rw [hm, h0, ite10_ne]
  omega

theorem isE_le (a : E) (v : Nat) (t : St) : (isE a v).eval t ≤ 1 := ite01 _

theorem andE_le (a b : E) (t : St) : (andE a b).eval t ≤ 1 := ite01 _

theorem blocked_lt : blocked < M32 := by decide

theorem OFFg_le (j : Nat) : OFFg j < 9 := by unfold OFFg; split_ifs <;> decide

theorem ltu_ne (a b : E) (t : St) : (E.bin .ltu a b).eval t ≠ 0 ↔ a.eval t < b.eval t :=
  ite01_ne _

theorem geu_ne (a b : E) (t : St) : (E.bin .geu a b).eval t ≠ 0 ↔ b.eval t ≤ a.eval t :=
  ite01_ne _

theorem ne_ne (a b : E) (t : St) : (E.bin .ne a b).eval t ≠ 0 ↔ a.eval t ≠ b.eval t :=
  ite10_ne _

/-- Output `j` is idle with bytes left to write. -/
theorem wrG_iff (j : Nat) (hj : j ≤ 1) (t : St) :
    (wrG j).eval t ≠ 0 ↔ t.m (aO j) = 0 ∧ t.g (OFFg j) < t.g LENg := by
  rw [wrG, andE_ne, isE_ne _ _ (by decide), ltu_ne, eval_ldA_O t j hj]
  rfl

/-- When the tee reads. -/
theorem rdG_iff (t : St) :
    rdG.eval t ≠ 0 ↔ t.m aRS = 0 ∧ t.m (aO 0) ≠ 1 ∧ t.m (aO 1) ≠ 1 ∧
      ¬ (t.m (aO 0) = 2 ∧ t.m (aO 1) = 2) := by
  have h1 : (E.c 1).eval t = 1 := rfl
  have hz : (E.eqz (andE (isE (ldA (aO 0)) 2) (isE (ldA (aO 1)) 2))).eval t ≠ 0 ↔
      ¬ (t.m (aO 0) = 2 ∧ t.m (aO 1) = 2) := by
    show (if (andE (isE (ldA (aO 0)) 2) (isE (ldA (aO 1)) 2)).eval t = 0 then 1 else 0 : Nat) ≠ 0 ↔ _
    rw [ite01_ne, ← not_ne_iff, andE_ne, isE_ne _ _ (by decide), isE_ne _ _ (by decide),
      eval_ldA_O t 0 (by omega), eval_ldA_O t 1 (by omega)]
  rw [rdG, andE_ne, andE_ne, andE_ne, isE_ne _ _ (by decide), ne_ne, ne_ne, hz, h1,
    eval_ldA_RS, eval_ldA_O t 0 (by omega), eval_ldA_O t 1 (by omega)]

/-- When the tee drops its input. -/
theorem stopG_iff (t : St) :
    stopG.eval t ≠ 0 ↔ t.m aRS = 2 ∨ (t.m aRS = 0 ∧ t.m (aO 0) = 2 ∧ t.m (aO 1) = 2) := by
  rw [stopG, orE_ne _ _ _ (isE_le _ _ _) (andE_le _ _ _), andE_ne, andE_ne]
  simp only [isE_ne _ _ (show 0 < M32 by decide), isE_ne _ _ (show 2 < M32 by decide),
    eval_ldA_RS, eval_ldA_O t 0 (by omega), eval_ldA_O t 1 (by omega)]

/-- When the tee drops output `j`. -/
theorem closeG_iff (j : Nat) (hj : j ≤ 1) (t : St) :
    (closeG j).eval t ≠ 0 ↔ t.m aRS = 3 ∧
      ((t.m (aO j) = 0 ∧ t.g LENg ≤ t.g (OFFg j)) ∨ t.m (aO j) = 2) := by
  rw [closeG, andE_ne, orE_ne _ _ _ (andE_le _ _ _) (isE_le _ _ _), andE_ne, geu_ne]
  simp only [isE_ne _ _ (show 0 < M32 by decide), isE_ne _ _ (show 2 < M32 by decide),
    isE_ne _ _ (show 3 < M32 by decide), eval_ldA_RS, eval_ldA_O t j hj]
  rfl

/-- When the tee exits. -/
theorem exitG_iff (t : St) :
    exitG.eval t ≠ 0 ↔ t.m aRS = 3 ∧ t.m (aO 0) = 3 ∧ t.m (aO 1) = 3 := by
  rw [exitG, andE_ne, andE_ne]
  simp only [isE_ne _ _ (show 3 < M32 by decide), eval_ldA_RS, eval_ldA_O t 0 (by omega),
    eval_ldA_O t 1 (by omega)]

/-! ## Memory (as in `KCore`'s proofs, restated for this topic) -/

theorem upd_apply (f : Nat → Nat) (k v j : Nat) : upd f k v j = if j = k then v else f j := rfl

theorem slice_length (m : Nat → Nat) (a n : Nat) : (slice m a n).length = n := by
  simp [slice]

theorem slice_congr {m m' : Nat → Nat} {a n : Nat} (h : ∀ i, i < n → m (a + i) = m' (a + i)) :
    slice m a n = slice m' a n := by
  unfold slice
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem slice_drop (m : Nat → Nat) (a n j : Nat) : (slice m a n).drop j = slice m (a + j) (n - j) := by
  unfold slice
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [Nat.add_assoc]

theorem slice_writeBytes (m : Nat → Nat) (a : Nat) (bs : List Nat) :
    slice (writeBytes m a bs) a bs.length = bs := by
  apply List.ext_getElem
  · simp [slice_length]
  · intro i h₁ h₂
    have hi : i < bs.length := by simpa [slice_length] using h₁
    simp [slice, writeBytes, hi, List.getD_eq_getElem?_getD]

/-- Writing below `a` leaves `slice m a n` alone. -/
theorem slice_upd_lo {m : Nat → Nat} {a n x v : Nat} (h : x < a) :
    slice (upd m x v) a n = slice m a n := by
  apply slice_congr
  intro i hi
  have hx : a + i ≠ x := by omega
  simp [upd_apply, hx]

theorem aRS_lt : aRS < IN := by decide

theorem aO_lt (j : Nat) (hj : j ≤ 1) : aO j < IN := by simp [aO, IN]; omega

theorem aO_ne_RS (j : Nat) : aO j ≠ aRS := by simp [aO, aRS]; omega

theorem aO01 : aO 0 ≠ aO 1 := by decide

theorem OFFg_ne_LEN (j : Nat) : OFFg j ≠ LENg := by unfold OFFg; split_ifs <;> decide

theorem OFF01 : OFFg 0 ≠ OFFg 1 := by decide

theorem WHg0 : WHg 0 = OUTSW := rfl

theorem WHg1 : WHg 1 = W1g := rfl

theorem OFFg0 : OFFg 0 = OFF0 := rfl

theorem OFFg1 : OFFg 1 = OFF1 := rfl

end Silmaril.Proofs.Wasm.JcoTool.KTee
