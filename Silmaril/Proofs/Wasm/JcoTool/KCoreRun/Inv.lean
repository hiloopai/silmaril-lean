module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Ctl

/-!
# Inversion of the checked semantics

One lemma per statement: what `bexec nl S f s = some (o, s')` says about the values the
statement computes and the state it leaves.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd mcopy)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec)

variable {nl f : Nat} {s s' : DSt} {o : Out}

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem bexec_lset {i : Nat} {e : E} (h : bexec nl (.lset i e) f s = some (o, s')) :
    i < nl ∧ ∃ v, cev nl s e = some v ∧ o = .norm ∧ s' = { s with l := upd s.l i v } := by
  by_cases hi : i < nl
  · have h' : (cev nl s e).map (fun v => (Out.norm, { s with l := upd s.l i v })) = some (o, s') := by
      simpa only [bexec, hi, ↓reduceIte] using h
    obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp h'
    exact ⟨hi, v, hv, (Prod.mk.inj he).1.symm, (Prod.mk.inj he).2.symm⟩
  · simp [bexec, hi] at h

theorem bexec_gset {i : Nat} {e : E} (h : bexec nl (.gset i e) f s = some (o, s')) :
    i < NG ∧ ∃ v, cev nl s e = some v ∧ o = .norm ∧ s' = { s with g := upd s.g i v } := by
  by_cases hi : i < NG
  · have h' : (cev nl s e).map (fun v => (Out.norm, { s with g := upd s.g i v })) = some (o, s') := by
      simpa only [bexec, hi, ↓reduceIte] using h
    obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp h'
    exact ⟨hi, v, hv, (Prod.mk.inj he).1.symm, (Prod.mk.inj he).2.symm⟩
  · simp [bexec, hi] at h

theorem bexec_st8 {a v : E} (h : bexec nl (.st8 a v) f s = some (o, s')) :
    ∃ x y, cev nl s a = some x ∧ cev nl s v = some y ∧ x < MSZ ∧ o = .norm ∧
      s' = { s with m := upd s.m x (y % 256) } := by
  cases hx : cev nl s a with
  | none => simp [bexec, hx] at h
  | some x =>
    cases hy : cev nl s v with
    | none => simp [bexec, hx, hy] at h
    | some y =>
      by_cases hm : x < MSZ
      · have h' : some (Out.norm, { s with m := upd s.m x (y % 256) }) = some (o, s') := by
          simpa only [bexec, hx, hy, hm, ↓reduceIte, Option.bind_eq_bind, Option.bind] using h
        exact ⟨x, y, rfl, rfl, hm, (Prod.mk.inj (Option.some.inj h')).1.symm,
          (Prod.mk.inj (Option.some.inj h')).2.symm⟩
      · simp [bexec, hx, hy, hm] at h

theorem bexec_mcopy {d src n : E} (h : bexec nl (.mcopy d src n) f s = some (o, s')) :
    ∃ x y z, cev nl s d = some x ∧ cev nl s src = some y ∧ cev nl s n = some z ∧ x ≤ y ∧
      y + z ≤ MSZ ∧ o = .norm ∧ s' = { s with m := mcopy s.m x y z } := by
  cases hx : cev nl s d with
  | none => simp [bexec, hx] at h
  | some x =>
    cases hy : cev nl s src with
    | none => simp [bexec, hx, hy] at h
    | some y =>
      cases hz : cev nl s n with
      | none => simp [bexec, hx, hy, hz] at h
      | some z =>
        by_cases hm : x ≤ y ∧ y + z ≤ MSZ
        · have h' : some (Out.norm, { s with m := mcopy s.m x y z }) = some (o, s') := by
            simpa only [bexec, hx, hy, hz, hm, and_self, ↓reduceIte, Option.bind_eq_bind,
              Option.bind] using h
          exact ⟨x, y, z, rfl, rfl, rfl, hm.1, hm.2, (Prod.mk.inj (Option.some.inj h')).1.symm,
            (Prod.mk.inj (Option.some.inj h')).2.symm⟩
        · simp [bexec, hx, hy, hz, hm] at h

theorem bexec_ite {c : E} {t e : S} (h : bexec nl (.ite c t e) f s = some (o, s')) :
    ∃ v o₁, cev nl s c = some v ∧ (if v ≠ 0 then bexec nl t f s else bexec nl e f s) = some (o₁, s') ∧
      o = labOut o₁ := by
  cases hv : cev nl s c with
  | none => simp [bexec, hv] at h
  | some v =>
    have h' : dexec.dlab (if v ≠ 0 then bexec nl t f s else bexec nl e f s) = some (o, s') := by
      simpa only [bexec, hv] using h
    cases hr : (if v ≠ 0 then bexec nl t f s else bexec nl e f s) with
    | none => rw [hr] at h'; cases h'
    | some r =>
      obtain ⟨o₁, s₁⟩ := r
      have h'' : some (labOut o₁, s₁) = some (o, s') := by rw [← dlab_some, ← hr]; exact h'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h'')
      exact ⟨v, o₁, rfl, hr, rfl⟩

theorem bexec_block {b : S} (h : bexec nl (.block b) f s = some (o, s')) :
    ∃ o₁, bexec nl b f s = some (o₁, s') ∧ o = labOut o₁ := by
  have h' : dexec.dlab (bexec nl b f s) = some (o, s') := by simpa only [bexec] using h
  cases hr : bexec nl b f s with
  | none => rw [hr] at h'; cases h'
  | some r =>
    obtain ⟨o₁, s₁⟩ := r
    have h'' : some (labOut o₁, s₁) = some (o, s') := by rw [← dlab_some, ← hr]; exact h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h'')
    exact ⟨o₁, rfl, rfl⟩

theorem bexec_brIf {k : Nat} {c : E} (h : bexec nl (.brIf k c) f s = some (o, s')) :
    k < M32 ∧ ∃ v, cev nl s c = some v ∧ s = s' ∧ o = (if v ≠ 0 then .br k else .norm) := by
  by_cases hk : k < M32
  · have h' : (cev nl s c).map (fun v => if v ≠ 0 then (Out.br k, s) else (Out.norm, s)) =
        some (o, s') := by simpa only [bexec, hk, ↓reduceIte] using h
    obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp h'
    refine ⟨hk, v, hv, ?_⟩
    by_cases h0 : v ≠ 0
    · have he' : (Out.br k, s) = (o, s') := by rw [ite_t h0] at he; exact he
      rw [ite_t h0]
      exact ⟨(Prod.mk.inj he').2, (Prod.mk.inj he').1.symm⟩
    · have he' : (Out.norm, s) = (o, s') := by rw [ite_f h0] at he; exact he
      rw [ite_f h0]
      exact ⟨(Prod.mk.inj he').2, (Prod.mk.inj he').1.symm⟩
  · simp [bexec, hk] at h

theorem bexec_ret {e : E} (h : bexec nl (.ret e) f s = some (o, s')) :
    ∃ v, cev nl s e = some v ∧ s = s' ∧ o = .ret v := by
  have h' : (cev nl s e).map (fun v => (Out.ret v, s)) = some (o, s') := by
    simpa only [bexec] using h
  obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp h'
  exact ⟨v, hv, (Prod.mk.inj he).2, (Prod.mk.inj he).1.symm⟩

theorem bexec_br {k : Nat} (h : bexec nl (.br k) f s = some (o, s')) :
    k < M32 ∧ s = s' ∧ o = .br k := by
  by_cases hk : k < M32
  · have h' : some (Out.br k, s) = some (o, s') := by simpa only [bexec, hk, ↓reduceIte] using h
    exact ⟨hk, (Prod.mk.inj (Option.some.inj h')).2, (Prod.mk.inj (Option.some.inj h')).1.symm⟩
  · simp [bexec, hk] at h

theorem bexec_seq {a b : S}
    (h : bexec nl (.seq a b) f s = some (o, s')) :
    ∃ o₁ s₁, bexec nl a f s = some (o₁, s₁) ∧
      ((o₁ = .norm ∧ bexec nl b f s₁ = some (o, s')) ∨ (o₁ ≠ .norm ∧ o = o₁ ∧ s' = s₁)) := by
  cases ha : bexec nl a f s with
  | none => simp [bexec, ha] at h
  | some r =>
    obtain ⟨o₁, s₁⟩ := r
    refine ⟨o₁, s₁, rfl, ?_⟩
    by_cases hn : o₁ = .norm
    · subst hn
      exact .inl ⟨rfl, by simpa [bexec, ha] using h⟩
    · have h' : some (o₁, s₁) = some (o, s') := by
        rcases o₁ with _ | k | v
        · exact absurd rfl hn
        all_goals simpa [bexec, ha] using h
      exact .inr ⟨hn, (Prod.mk.inj (Option.some.inj h')).1.symm,
        (Prod.mk.inj (Option.some.inj h')).2.symm⟩

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
