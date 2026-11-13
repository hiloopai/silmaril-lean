module

public import Silmaril.Proofs.Wasm.JcoTool.KCore.Feed

/-!
# How the cases of the callback end

(Restyled to the Isar conventions of `docs/projects/wasm-components.md` when moved out of `Silmaril/Raw`; the statements are
restated in `Silmaril.Wasm.JcoTool.KCore.Thms`.)

`OutIn P a`: every run of `a` that finishes ends with an outcome satisfying `P`. The cases of
the callback only return (`retOnly`), so the callback runs the case of its `pc`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCore

open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

/-- Every finished run of `a` ends with an outcome in `P`. -/
def OutIn (P : Out → Prop) (a : S) : Prop := ∀ f s o s', exec a f s = some (o, s') → P o

/-- Normal end, or `return`. -/
def NR (o : Out) : Prop := o = .norm ∨ ∃ v, o = .ret v

/-- `return`. -/
def IsRet (o : Out) : Prop := ∃ v, o = .ret v

theorem outIn_mono {P Q : Out → Prop} {a : S} (h : ∀ o, P o → Q o) (ha : OutIn P a) : OutIn Q a :=
  fun f s o s' hx => h o (ha f s o s' hx)

theorem outIn_norm_nr {a : S} (ha : OutIn (· = .norm) a) : OutIn NR a :=
  outIn_mono (fun _ h => .inl h) ha

theorem outIn_lset (i : Nat) (e : E) : OutIn (· = .norm) (.lset i e) := by
  intro f s o s' h; cases h; rfl

theorem outIn_gset (i : Nat) (e : E) : OutIn (· = .norm) (.gset i e) := by
  intro f s o s' h; cases h; rfl

theorem outIn_st8 (a v : E) : OutIn (· = .norm) (.st8 a v) := by
  intro f s o s' h; cases h; rfl

theorem outIn_mcopy (d src n : E) : OutIn (· = .norm) (.mcopy d src n) := by
  intro f s o s' h; cases h; rfl

theorem outIn_nop : OutIn (· = .norm) .nop := by
  intro f s o s' h; cases h; rfl

theorem outIn_unreachable (P : Out → Prop) : OutIn P .unreachable := by
  intro f s o s' h; cases h

theorem outIn_ret (e : E) : OutIn IsRet (.ret e) := by
  intro f s o s' h; cases h; exact ⟨_, rfl⟩

theorem callBI_norm {b : BI} {as dst : List Nat} {s s' : St} {o : Out}
    (h : callBI b as dst s = some (o, s')) : o = .norm := by
  unfold callBI at h
  split at h <;> (try split at h) <;> (try split at h) <;>
    first
    | (cases h; rfl)
    | (simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h; rfl)
    | cases h

theorem outIn_call (b : BI) (as : List E) (dst : List Nat) : OutIn (· = .norm) (.call b as dst) := by
  intro f s o s' h
  exact callBI_norm h

theorem outIn_seq {P : Out → Prop} {a b : S} (ha : OutIn (fun o => o = .norm ∨ P o) a)
    (hb : OutIn P b) : OutIn P (.seq a b) := by
  intro f s o s' h
  cases h₁ : exec a f s with
  | none => rw [exec_seq, h₁] at h; cases h
  | some r =>
    obtain ⟨o₁, s₁⟩ := r
    rcases ha f s o₁ s₁ h₁ with rfl | hp
    · rw [exec_seq_norm h₁] at h
      exact hb f s₁ o s' h
    · cases o₁ with
      | norm => rw [exec_seq_norm h₁] at h; exact hb f s₁ o s' h
      | br k => rw [exec_seq, h₁] at h; cases h; exact hp
      | ret v => rw [exec_seq, h₁] at h; cases h; exact hp

theorem lab_keep {x : Option (Out × St)} {o : Out} {s' : St} (h : lab x = some (o, s'))
    (hx : ∀ o₁ s₁, x = some (o₁, s₁) → NR o₁) : x = some (o, s') := by
  cases x with
  | none => cases h
  | some r =>
    obtain ⟨o₁, s₁⟩ := r
    rcases hx o₁ s₁ rfl with rfl | ⟨v, rfl⟩
    · exact h
    · exact h

theorem outIn_ite {P : Out → Prop} {c : E} {t e : S} (hP : ∀ o, P o → NR o) (ht : OutIn P t)
    (he : OutIn P e) : OutIn P (.ite c t e) := by
  intro f s o s' h
  rw [exec_ite] at h
  by_cases hc : c.eval s ≠ 0
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte] at h
    exact ht f s o s' (lab_keep h fun o₁ s₁ hx => hP o₁ (ht f s o₁ s₁ hx))
  · simp only [hc, ↓reduceIte] at h
    exact he f s o s' (lab_keep h fun o₁ s₁ hx => hP o₁ (he f s o₁ s₁ hx))

theorem outIn_seqs_nr {as : List S} (h : ∀ a ∈ as, OutIn NR a) : OutIn NR (seqs as) := by
  induction as with
  | nil => exact outIn_norm_nr outIn_nop
  | cons a as ih =>
    cases as with
    | nil => exact h a (by simp)
    | cons b bs =>
      exact outIn_seq (outIn_mono (fun o ho => .inr ho) (h a (by simp)))
        (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem outIn_cS (c : KStmt) : OutIn (· = .norm) (cS c) := by
  have hnr : ∀ {a : S}, OutIn (· = .norm) a → OutIn (fun o => o = .norm ∨ o = .norm) a :=
    fun ha => outIn_mono (fun _ h => .inl h) ha
  have hP : ∀ o : Out, o = .norm → NR o := fun _ h => .inl h
  have hchk : ∀ (c : E), OutIn (· = .norm) (.ite c .unreachable .nop) :=
    fun c => outIn_ite hP (outIn_unreachable _) outIn_nop
  induction c with
  | skip => exact outIn_nop
  | seq p q ihp ihq => exact outIn_seq (hnr ihp) ihq
  | emit e => exact outIn_seq (hnr (hchk _)) (outIn_seq (hnr (outIn_st8 _ _)) (outIn_gset _ _))
  | set e => exact outIn_gset _ _
  | push e => exact outIn_seq (hnr (hchk _)) (outIn_seq (hnr (outIn_st8 _ _)) (outIn_gset _ _))
  | emitBuf => exact outIn_seq (hnr (hchk _)) (outIn_seq (hnr (outIn_mcopy _ _ _)) (outIn_gset _ _))
  | clear => exact outIn_gset _ _
  | ite c p q ihp ihq => exact outIn_ite hP ihp ihq

theorem outIn_seqs_ret {as : List S} {l : S} (h : ∀ a ∈ as, OutIn NR a) (hl : OutIn IsRet l) :
    OutIn IsRet (seqs (as ++ [l])) := by
  induction as with
  | nil => exact hl
  | cons a as ih =>
    have hrest : OutIn IsRet (seqs (as ++ [l])) := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha : OutIn (fun o => o = .norm ∨ IsRet o) a := h a (by simp)
    cases as with
    | nil => exact outIn_seq ha hl
    | cons b bs => exact outIn_seq ha hrest

theorem outIn_brIf (k : Nat) (c : E) : OutIn (fun o => o = .norm ∨ o = .br k) (.brIf k c) := by
  intro f s o s' h
  simp only [exec] at h
  split at h
  · cases h; exact .inr rfl
  · cases h; exact .inl rfl

theorem loopN_br0 {body : St → Option (Out × St)}
    (hb : ∀ s o s', body s = some (o, s') → o = .br 0 ∨ o = .br 1) :
    ∀ n s o s', loopN body n s = some (o, s') → o = .br 0 := by
  intro n
  induction n with
  | zero => intro s o s' h; cases h
  | succ n ih =>
    intro s o s' h
    simp only [loopN] at h
    cases h₁ : body s with
    | none => rw [h₁] at h; cases h
    | some r =>
      obtain ⟨o₁, s₁⟩ := r
      rcases hb s o₁ s₁ h₁ with rfl | rfl
      · rw [h₁] at h; exact ih s₁ o s' h
      · rw [h₁] at h; cases h; rfl

theorem outIn_feedLoop (k : KM) : OutIn NR (feedLoop k) := by
  have hP : ∀ {a : S}, OutIn (· = .norm) a → OutIn (fun o => o = .norm ∨ (o = .br 0 ∨ o = .br 1)) a :=
    fun ha => outIn_mono (fun _ h => .inl h) ha
  have hb : OutIn (fun o => o = .br 0 ∨ o = .br 1) (body k) := by
    have hbr : OutIn (fun o => o = .norm ∨ (o = .br 0 ∨ o = .br 1)) (.brIf 1 (.bin .geu (.l LI) (.l LN))) :=
      outIn_mono (fun o h => h.imp_right .inr) (outIn_brIf 1 _)
    have hbr' : OutIn (fun o => o = .norm ∨ (o = .br 0 ∨ o = .br 1)) (.brIf 1 (cE k.done)) :=
      outIn_mono (fun o h => h.imp_right .inr) (outIn_brIf 1 _)
    have hend : OutIn (fun o => o = .br 0 ∨ o = .br 1) (.br 0) := by
      intro f s o s' h; cases h; exact .inl rfl
    exact outIn_seq hbr (outIn_seq (hP (outIn_lset _ _)) (outIn_seq hbr'
      (outIn_seq (hP (outIn_lset _ _)) (outIn_seq (hP (outIn_cS _))
        (outIn_seq (hP (outIn_lset _ _)) hend)))))
  intro f s o s' h
  rw [feedLoop_eq] at h
  simp only [exec] at h
  cases hl : loopN (exec (body k) f) f s with
  | none => rw [hl] at h; cases h
  | some r =>
    obtain ⟨o₁, s₁⟩ := r
    have h0 : o₁ = .br 0 := loopN_br0 (fun s o s' hx => hb f s o s' hx) f s o₁ s₁ hl
    rw [hl, h0] at h
    cases h
    exact .inl rfl

theorem nr_of_norm {a : S} (h : OutIn (· = .norm) a) : OutIn NR a := outIn_norm_nr h

theorem nr_P : ∀ o, NR o → NR o := fun _ h => h

theorem outIn_ite_nr {c : E} {t e : S} (ht : OutIn NR t) (he : OutIn NR e) : OutIn NR (.ite c t e) :=
  outIn_ite nr_P ht he

theorem isRet_nr {a : S} (h : OutIn IsRet a) : OutIn NR a := outIn_mono (fun _ h => .inr h) h

theorem outIn_check (c₁ c₂ : E) : OutIn NR (.ite c₁ (.ite c₂ .nop .unreachable) .unreachable) :=
  outIn_ite_nr (outIn_ite_nr (nr_of_norm outIn_nop) (outIn_unreachable _)) (outIn_unreachable _)

theorem outIn_onRead (k : KM) (p : E) : OutIn NR (onRead k p) :=
  outIn_ite_nr (nr_of_norm (outIn_gset _ _)) (outIn_seqs_nr (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact nr_of_norm (outIn_lset _ _)
    · exact nr_of_norm (outIn_lset _ _)
    · exact outIn_feedLoop k
    · exact nr_of_norm (outIn_gset _ _)
    · exact nr_of_norm (outIn_gset _ _)))

theorem outIn_onWrite (p : E) : OutIn NR (onWrite p) :=
  outIn_ite_nr (nr_of_norm (outIn_gset _ _)) (outIn_seqs_nr (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact nr_of_norm (outIn_lset _ _)
    · exact outIn_ite_nr (nr_of_norm (outIn_gset _ _)) (nr_of_norm (outIn_gset _ _))
    · exact nr_of_norm (outIn_gset _ _)))

theorem outIn_flushOut (k : KM) : OutIn NR (flushOut k) := outIn_seqs_nr (by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact nr_of_norm (outIn_gset _ _)
  · exact nr_of_norm (outIn_gset _ _)
  · exact nr_of_norm (outIn_lset _ _)
  · exact nr_of_norm (outIn_cS _)
  · exact nr_of_norm (outIn_gset _ _)
  · exact nr_of_norm (outIn_gset _ _))

theorem outIn_yield : OutIn IsRet yield_ := outIn_ret _

theorem nr_done (k : KM) :
    OutIn NR (.ite (cE k.done) (seqs [.call .dropR [.g INSR] [], flushOut k, yield_]) .nop) :=
  outIn_ite_nr (isRet_nr (outIn_seqs_ret (as := [.call .dropR [.g INSR] [], flushOut k])
    (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact nr_of_norm (outIn_call _ _ _)
      · exact outIn_flushOut k) outIn_yield)) (nr_of_norm outIn_nop)

theorem nr_wait (i : Nat) (c : E) : OutIn NR (.ite c (seqs [.gset PC (.c i), .ret waitCode]) .nop) :=
  outIn_ite_nr (isRet_nr (outIn_seqs_ret (as := [.gset PC (.c i)])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha
        exact nr_of_norm (outIn_gset _ _)) (outIn_ret _))) (nr_of_norm outIn_nop)

theorem nr_reset : OutIn NR (.ite (.bin .geu (.g OOFF) (.g OLEN)) (seqs [.gset OOFF (.c 0),
    .gset OLEN (.c 0), .ite (.g NXT) (.gset PC (.c pRD)) (.gset PC (.c pCL)), yield_]) .nop) :=
  outIn_ite_nr (isRet_nr (outIn_seqs_ret (as := [_, _, _]) (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact nr_of_norm (outIn_gset _ _)
    · exact nr_of_norm (outIn_gset _ _)
    · exact outIn_ite_nr (nr_of_norm (outIn_gset _ _)) (nr_of_norm (outIn_gset _ _))) outIn_yield))
    (nr_of_norm outIn_nop)

theorem ret_wtr (k : KM) : OutIn IsRet (cbWTR k) :=
  outIn_seqs_ret (as := [_, _]) (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact outIn_check _ _
    · exact outIn_onRead k _) outIn_yield

theorem ret_wtw : OutIn IsRet cbWTW :=
  outIn_seqs_ret (as := [_, _]) (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact outIn_check _ _
    · exact outIn_onWrite _) outIn_yield

theorem ret_rd (k : KM) (N : Nat) : OutIn IsRet (cbRD k N) :=
  outIn_seqs_ret (as := [_, _, _, _, _]) (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact nr_of_norm (outIn_lset _ _)
    · exact nr_done k
    · exact nr_of_norm (outIn_call _ _ _)
    · exact nr_wait _ _
    · exact outIn_onRead k _) outIn_yield

theorem ret_eoi (k : KM) : OutIn IsRet (cbEOI k) :=
  outIn_seqs_ret (as := [_, _]) (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact nr_of_norm (outIn_call _ _ _)
    · exact outIn_flushOut k) outIn_yield

theorem ret_wr : OutIn IsRet cbWR :=
  outIn_seqs_ret (as := [_, _, _, _]) (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact nr_reset
    · exact nr_of_norm (outIn_call _ _ _)
    · exact nr_wait _ _
    · exact outIn_onWrite _) outIn_yield

theorem ret_cl : OutIn IsRet cbCL :=
  outIn_seqs_ret (as := [_, _]) (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact nr_of_norm (outIn_call _ _ _)
    · exact nr_of_norm (outIn_gset _ _)) (outIn_ret _)

/-- **Every case of the callback returns** (or traps). -/
theorem retOnly (k : KM) (N : Nat) :
    OutIn IsRet (cbWTR k) ∧ OutIn IsRet cbWTW ∧ OutIn IsRet (cbRD k N) ∧ OutIn IsRet (cbEOI k) ∧
      OutIn IsRet cbWR ∧ OutIn IsRet cbCL :=
  ⟨ret_wtr k, ret_wtw, ret_rd k N, ret_eoi k, ret_wr, ret_cl⟩

end Silmaril.Proofs.Wasm.JcoTool.KCore
