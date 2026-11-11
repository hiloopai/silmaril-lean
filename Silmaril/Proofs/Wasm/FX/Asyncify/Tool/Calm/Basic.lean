module

public import Silmaril.Wasm.FX.Asyncify.Tool.Calm.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Call

/-!
# Calm functions never suspend: proofs

`mayS P` is `suspSet P (L + 1)` for `L` defined functions. The sets `suspSet P n` grow with `n`
(`suspSet_mono`); once two consecutive ones agree they agree forever (`suspSet_stable_from`);
and each strict growth adds a defined function (`cnt_lt`), of which there are `L`. So
`suspSet P (L + 1) = suspSet P (L + 2)` (`suspSet_stable`): `mayS P` is a fixed point of
`suspStep P` (`mayS_fix`), hence closed under callers (`calm_calls`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-! ## The analysis is a fixed point -/

theorem suspStep_mono {P : Prog} {S S' : Nat → Bool} (h : ∀ f, S f = true → S' f = true) :
    ∀ f, suspStep P S f = true → suspStep P S' f = true := by
  intro f hf
  unfold suspStep at hf ⊢
  by_cases hi : f < P.imps.length
  · simp [hi]
  · simp only [hi, ↓reduceIte] at hf ⊢
    cases hfn : P.fns[f - P.imps.length]? with
    | none => rw [hfn] at hf; cases hf
    | some fn =>
      rw [hfn] at hf
      simp only [List.any_eq_true] at hf ⊢
      obtain ⟨st, hst, hS⟩ := hf
      refine ⟨st, hst, ?_⟩
      cases st with
      | pure _ => cases hS
      | call g _ _ => exact h _ hS

theorem suspSet_mono (P : Prog) : ∀ (n f : Nat), suspSet P n f = true → suspSet P (n + 1) f = true
  | 0, f, h => by
    have hi : f < P.imps.length := by simpa [suspSet] using h
    simp [suspSet, suspStep, hi]
  | n + 1, f, h => suspStep_mono (suspSet_mono P n) f h

theorem suspSet_imp (P : Prog) {f : Nat} (hf : f < P.imps.length) : ∀ n, suspSet P n f = true
  | 0 => by simp [suspSet, hf]
  | n + 1 => by simp [suspSet, suspStep, hf]

theorem suspSet_out (P : Prog) {f : Nat} (hf : P.imps.length + P.fns.length ≤ f) :
    ∀ n, suspSet P n f = false
  | 0 => by simp [suspSet]; omega
  | n + 1 => by
    have hi : ¬ f < P.imps.length := by omega
    have hn : P.fns[f - P.imps.length]? = none := List.getElem?_eq_none (by omega)
    simp [suspSet, suspStep, hi, hn]

theorem suspSet_stable_from (P : Prog) {n : Nat} (h : suspSet P n = suspSet P (n + 1)) :
    ∀ m, suspSet P (n + m) = suspSet P (n + m + 1)
  | 0 => h
  | m + 1 => by
    have ih := suspSet_stable_from P h m
    show suspStep P (suspSet P (n + m)) = suspStep P (suspSet P (n + m + 1))
    rw [ih]

/-- The number of defined functions in `suspSet P n`. -/
def cnt (P : Prog) (n : Nat) : Nat :=
  ((List.range P.fns.length).filter fun j => suspSet P n (P.imps.length + j)).length

theorem filter_len_le {p q : Nat → Bool} : ∀ {l : List Nat}, (∀ x ∈ l, p x = true → q x = true) →
    (l.filter p).length ≤ (l.filter q).length
  | [], _ => le_refl _
  | a :: l, h => by
    have ih := filter_len_le (l := l) fun x hx => h x (by simp [hx])
    by_cases hp : p a = true
    · have hq : q a = true := h a (by simp) hp
      simp only [List.filter_cons, hp, hq, ↓reduceIte, List.length_cons]
      omega
    · by_cases hq : q a = true
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        omega
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte]
        exact ih

theorem filter_len_lt {p q : Nat → Bool} : ∀ {l : List Nat}, (∀ x ∈ l, p x = true → q x = true) →
    (∃ x ∈ l, p x = false ∧ q x = true) → (l.filter p).length < (l.filter q).length
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | a :: l, h, ⟨x, hx, hpx, hqx⟩ => by
    have hle := filter_len_le (l := l) fun y hy => h y (by simp [hy])
    by_cases hxa : x = a
    · subst hxa
      simp only [List.filter_cons, hpx, hqx, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have hxl : x ∈ l := by simpa [hxa] using hx
      have ih := filter_len_lt (l := l) (fun y hy => h y (by simp [hy])) ⟨x, hxl, hpx, hqx⟩
      by_cases hp : p a = true
      · have hq : q a = true := h a (by simp) hp
        simp only [List.filter_cons, hp, hq, ↓reduceIte, List.length_cons]
        omega
      · by_cases hq : q a = true
        · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
          omega
        · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte]
          exact ih

theorem cnt_le (P : Prog) (n : Nat) : cnt P n ≤ P.fns.length := by
  have := List.length_filter_le (fun j => suspSet P n (P.imps.length + j)) (List.range P.fns.length)
  simpa [cnt] using this

/-- Two consecutive sets that differ differ at a defined function, which the later one adds. -/
theorem cnt_lt (P : Prog) {n : Nat} (h : suspSet P n ≠ suspSet P (n + 1)) :
    cnt P n < cnt P (n + 1) := by
  obtain ⟨f, hf⟩ : ∃ f, suspSet P n f ≠ suspSet P (n + 1) f := by
    by_contra hall
    exact h (funext fun f => by_contra fun hne => hall ⟨f, hne⟩)
  have hfalse : suspSet P n f = false := by
    cases hn : suspSet P n f with
    | false => rfl
    | true => exact absurd (hn.trans (suspSet_mono P n f hn).symm) hf
  have htrue : suspSet P (n + 1) f = true := by
    cases hn1 : suspSet P (n + 1) f with
    | true => rfl
    | false => exact absurd (hfalse.trans hn1.symm) hf
  have hge : P.imps.length ≤ f := by
    by_contra hlt
    have := suspSet_imp P (f := f) (by omega) n
    rw [hfalse] at this; cases this
  have hlt : f < P.imps.length + P.fns.length := by
    by_contra hge'
    have := suspSet_out P (f := f) (by omega) (n + 1)
    rw [htrue] at this; cases this
  unfold cnt
  refine filter_len_lt (fun j _ hj => suspSet_mono P n _ hj) ⟨f - P.imps.length, ?_, ?_, ?_⟩
  · simp only [List.mem_range]; omega
  · rw [show P.imps.length + (f - P.imps.length) = f by omega]; exact hfalse
  · rw [show P.imps.length + (f - P.imps.length) = f by omega]; exact htrue

theorem cnt_grow (P : Prog) : ∀ k, (∀ n ≤ k, suspSet P n ≠ suspSet P (n + 1)) → k + 1 ≤ cnt P (k + 1)
  | 0, h => by have := cnt_lt P (h 0 (le_refl 0)); omega
  | k + 1, h => by
    have ih := cnt_grow P k fun n hn => h n (by omega)
    have := cnt_lt P (h (k + 1) (le_refl _))
    omega

/-- **The analysis is stable after `L + 1` rounds.** -/
theorem suspSet_stable (P : Prog) :
    suspSet P (P.fns.length + 1) = suspSet P (P.fns.length + 2) := by
  by_contra hne
  have hall : ∀ n ≤ P.fns.length + 1, suspSet P n ≠ suspSet P (n + 1) := by
    intro n hn heq
    have := suspSet_stable_from P heq (P.fns.length + 1 - n)
    rw [show n + (P.fns.length + 1 - n) = P.fns.length + 1 by omega] at this
    exact hne this
  have hg := cnt_grow P (P.fns.length + 1) hall
  have hl := cnt_le P (P.fns.length + 1 + 1)
  omega

/-- **`mayS P` is a fixed point of one round of the analysis.** -/
theorem mayS_fix (P : Prog) : suspStep P (mayS P) = mayS P := by
  show suspSet P (P.fns.length + 2) = suspSet P (P.fns.length + 1)
  exact (suspSet_stable P).symm

/-- A calm function is a defined function. -/
theorem calm_defined {P : Prog} {f : Nat} (h : mayS P f = false) : P.imps.length ≤ f := by
  by_contra hlt
  have := suspSet_imp P (f := f) (by omega) (P.fns.length + 1)
  have h' : mayS P f = true := this
  rw [h] at h'; cases h'

/-- **A calm function calls calm functions only** (`mayS P` is closed under callers). -/
theorem calm_calls {P : Prog} {f : Nat} {fn : FnSrc} (h : mayS P f = false)
    (hfn : P.fns[f - P.imps.length]? = some fn) {g : FuncIdx} {as rs : List LocalIdx}
    (hg : Stmt.call g as rs ∈ fn.stmts) : mayS P g.value.val = false := by
  have hfix : suspStep P (mayS P) f = false := by rw [mayS_fix]; exact h
  have hi : ¬ f < P.imps.length := Nat.not_lt.2 (calm_defined h)
  simp only [suspStep, hi, ↓reduceIte, hfn, List.any_eq_false] at hfix
  have := hfix _ hg
  simpa using this

/-! ## Calm runs -/

/-- The instructions of a statement of a well-formed function: pure, or its call. -/
theorem stmt_shape {P : Prog} {fn : FnSrc} (hok : FnOk P fn) {s : Stmt} (hs : s ∈ fn.stmts)
    {i : Instr} (hi : i ∈ s.code) :
    pureIns fn.nloc i = true ∨ ∃ g as rs, i = .call g ∧ Stmt.call g as rs ∈ fn.stmts := by
  cases s with
  | pure is =>
    obtain ⟨-, hp, -⟩ := Stmt.wf_pure (hok.stmts _ hs)
    exact Or.inl (hp i hi)
  | call g as rs =>
    obtain ⟨-, has, hrs⟩ := Stmt.wf_call (hok.stmts _ hs)
    have hi' : (i ∈ getsCode as ∨ i = .call g) ∨ i ∈ setsCode rs := by
      simpa only [Stmt.code, List.mem_append, List.mem_singleton] using hi
    rcases hi' with (h | h) | h
    · obtain ⟨a, ha, hia⟩ : ∃ a ∈ as, .localGet a = i := by simpa [getsCode] using h
      exact Or.inl (by rw [← hia]; simp [pureIns, has a ha])
    · exact Or.inr ⟨g, as, rs, h, hs⟩
    · exact Or.inl (setsCode_pure hrs i h)

theorem mem_flatS {i : Instr} : ∀ {ss : List Stmt}, i ∈ flatS ss → ∃ s ∈ ss, i ∈ s.code
  | [], h => by simp [flatS] at h
  | s :: ss, h => by
    have h' : i ∈ s.code ∨ i ∈ flatS ss := by simpa only [flatS, List.mem_append] using h
    rcases h' with h1 | h1
    · exact ⟨s, by simp, h1⟩
    · obtain ⟨s', hs', hi⟩ := mem_flatS h1
      exact ⟨s', by simp [hs'], hi⟩

/-- The instructions of a well-formed body: pure, or the call of a call statement. -/
theorem body_shape {P : Prog} {fn : FnSrc} (hok : FnOk P fn) {i : Instr} (hi : i ∈ fn.body) :
    pureIns fn.nloc i = true ∨ ∃ g as rs, i = .call g ∧ Stmt.call g as rs ∈ fn.stmts := by
  have hi' : i ∈ flatS fn.stmts ∨ i ∈ fn.tail := by
    simpa only [FnSrc.body, List.mem_append] using hi
  rcases hi' with h | h
  · obtain ⟨s, hs, his⟩ := mem_flatS h
    exact stmt_shape hok hs his
  · exact Or.inl (hok.tailPure i h)

theorem calm_fnAt {P : Prog} {fr : Frame} {fn : FnSrc} (hge : P.imps.length ≤ fr.fid)
    (hfn : P.fns[fr.fid - P.imps.length]? = some fn) : P.fnAt fr.fid = some fn := by
  simp [Prog.fnAt, hge, hfn]

/-- A calm frame below a frame that returns stays calm. -/
theorem calmCfg_ret {P : Prog} {c : Cfg} {fr : Frame} {rest : List Frame} {vs : List W}
    (hc : CalmCfg P c) (hf : c.frames = fr :: rest) :
    ∀ c', ret c vs rest = .next c' → CalmCfg P c' := by
  intro c' h
  cases rest with
  | nil => cases h
  | cons caller rest' =>
    have hc' : c' = { c with frames := { caller with ops := vs ++ caller.ops } :: rest' } :=
      (Res.next.inj h).symm
    intro g hg
    rw [hc'] at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · obtain ⟨fn, h1, h2, h3, h4⟩ := hc caller (by simp [hf])
      exact ⟨fn, h1, h2, h3, h4⟩
    · exact hc g (by simp [hf, hg])

end Silmaril.Wasm.FX.Asyncify.Tool
