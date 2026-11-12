module

public import Silmaril.Wasm.Verify.Flow.Defs
public import Silmaril.Proofs.Wasm.Verify.Guard.Basic

/-!
# The flow analysis: basic facts

* `callPl_plainOK`: `CallPl` meets the requirements of the reachability invariant.
* `FLe`: the order on abstract states (more facts, a more precise top); `okL_mono`, `okA_mono`:
  the checks are monotone; `nextI_mono`, `nextX_mono`.
* `finA`, `okA_append`: checking a concatenation; `okA_expression`: on source code `okA` is
  `okL`; `okA_vals_append`: values only set the top state.
* `scopeSeqs`, `frameScopes`: append and flat code.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Validation

variable {K : List Nat} {bad : Nat → Bool} {fs : List Nat}

/-! ## The reachability predicate -/

theorem CallPl.of_body {G : Nat → Prop} {i₀ : Instr} {b : List Instr}
    (hrf : instrRF i₀ = exprRF b) (hc : instrCalls i₀ = exprCalls b)
    (h : CallPl G bad fs i₀) : ∀ i ∈ b, PlOK (CallPl G bad fs) i := by
  intro i hi
  exact .inr ⟨fun x hx => h.1 x (hrf ▸ mem_exprRF hi hx),
    fun x hx => h.2 x (hc ▸ mem_exprCalls hi hx)⟩

/-- **`CallPl` meets the requirements of the reachability invariant**, with calls of bad
functions as the bad steps. -/
theorem callPl_plainOK {G : Nat → Prop} :
    PlainOK G (fun a => bad a = true) fs (CallPl G bad fs) where
  block _ _ h := CallPl.of_body (by simp [instrRF]) (by simp [instrCalls]) h
  loop _ _ h := CallPl.of_body (by simp [instrRF]) (by simp [instrCalls]) h
  tryTable _ _ _ h := CallPl.of_body (by simp [instrRF]) (by simp [instrCalls]) h
  ifLeft _ _ _ h := .inr ⟨
    fun x hx => h.1 x (by simp only [instrRF, List.mem_append] at hx ⊢; exact .inl hx),
    fun x hx => h.2 x (by simp only [instrCalls, List.mem_append] at hx ⊢; exact .inl hx)⟩
  ifRight _ _ _ h := .inr ⟨
    fun x hx => h.1 x (by simp only [instrRF, List.mem_append] at hx ⊢; exact .inr hx),
    fun x hx => h.2 x (by simp only [instrCalls, List.mem_append] at hx ⊢; exact .inr hx)⟩
  call _ a h ha := h.2 _ (by simp [instrCalls]) a ha
  returnCall _ a h ha := h.1 _ (by simp [instrRF]) a ha
  refFunc _ a h ha := h.1 _ (by simp [instrRF]) a ha

/-! ## The order on states -/

/-- The order on top states, given the facts `S'` of the larger state: `t'` is at least as
precise as `t`. -/
def TLe (S' : List Nat) (t t' : Top) : Prop :=
  t = t' ∨ t = .other ∨ (∃ k, t = .loc k ∧ (t' = .zero ∨ t' = .nonI32 ∨ (t' = .gd ∧ k ∈ S'))) ∨
    (t = .zero ∧ t' = .nonI32)

/-- The order on states: `st'` is dead, or knows more and has a more precise top. -/
def FLe (st st' : FSt) : Prop :=
  st'.top = .ex ∨ ((∀ k ∈ st.S, k ∈ st'.S) ∧ TLe st'.S st.top st'.top)

theorem FLe.refl (st : FSt) : FLe st st := .inr ⟨fun _ h => h, .inl rfl⟩

theorem FLe.of_other {S S' : List Nat} (hS : ∀ k ∈ S, k ∈ S') (t : Top) :
    FLe ⟨S, .other⟩ ⟨S', t⟩ :=
  .inr ⟨hS, .inr (.inl rfl)⟩

theorem addK_mono {S S' : List Nat} (hS : ∀ k ∈ S, k ∈ S') (x : Nat) :
    ∀ k ∈ addK K x S, k ∈ addK K x S' := by
  intro k hk
  unfold addK at hk ⊢
  split
  · rename_i hx
    simp only [hx, ↓reduceIte, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hS k hk)
  · rename_i hx
    simp only [hx, Bool.false_eq_true, ↓reduceIte] at hk
    exact hS k hk

theorem mem_thenS {st : FSt} {k : Nat} :
    k ∈ thenS st ↔ k ∈ st.S ∨ st.top = .loc k := by
  obtain ⟨S, t⟩ := st
  cases t <;> simp [thenS, or_comm, eq_comm]

theorem thenS_mono {st st' : FSt} (hS : ∀ k ∈ st.S, k ∈ st'.S) (ht : TLe st'.S st.top st'.top)
    (hz : st'.top ≠ .zero) (hn : st'.top ≠ .nonI32) : ∀ k ∈ thenS st, k ∈ thenS st' := by
  intro k hk
  rcases mem_thenS.1 hk with hk | hk
  · exact mem_thenS.2 (.inl (hS k hk))
  · have hloc : st'.top = .loc k ∨ k ∈ st'.S := by
      rcases ht with h | h | ⟨j, hj, hj'⟩ | ⟨h, -⟩
      · exact .inl (h ▸ hk)
      · rw [hk] at h; cases h
      · have hjk : j = k := by rw [hk] at hj; cases hj; rfl
        subst hjk
        rcases hj' with h | h | ⟨-, h⟩
        · exact absurd h hz
        · exact absurd h hn
        · exact .inr h
      · rw [hk] at h; cases h
    exact mem_thenS.2 (hloc.elim .inr .inl)

theorem reqI_mono {st st' : FSt} (ht : TLe st'.S st.top st'.top) (i : Instr)
    (h : reqI K bad fs st i = true) : reqI K bad fs st' i = true := by
  have hgd : st.top = .gd → st'.top = .gd := by
    intro hg
    rcases ht with h' | h' | ⟨k, h', -⟩ | ⟨h', -⟩
    · exact h' ▸ hg
    all_goals rw [hg] at h'; cases h'
  have hnon : st.top = .nonI32 → st'.top = .nonI32 := by
    intro hg
    rcases ht with h' | h' | ⟨k, h', -⟩ | ⟨h', -⟩
    · exact h' ▸ hg
    all_goals rw [hg] at h'; cases h'
  simp only [reqI, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨(h₁ | h₁) | h₁, h₂⟩ := h
  · exact ⟨.inl (.inl h₁), h₂.elim .inl fun h => .inr (hgd h)⟩
  · exact ⟨.inl (.inr (hgd h₁)), h₂.elim .inl fun h => .inr (hgd h)⟩
  · exact ⟨.inr (hnon h₁), h₂.elim .inl fun h => .inr (hgd h)⟩

/-- The `if` requirement is monotone. -/
theorem okI_if_mono {st st' : FSt} (hS : ∀ k ∈ st.S, k ∈ st'.S) (ht : TLe st'.S st.top st'.top)
    {b₁ b₂ : List Instr}
    (ih₁ : ∀ S₁ S₁' : List Nat, (∀ k ∈ S₁, k ∈ S₁') → okL K bad fs ⟨S₁, .other⟩ b₁ = true →
      okL K bad fs ⟨S₁', .other⟩ b₁ = true)
    (ih₂ : ∀ S₁ S₁' : List Nat, (∀ k ∈ S₁, k ∈ S₁') → okL K bad fs ⟨S₁, .other⟩ b₂ = true →
      okL K bad fs ⟨S₁', .other⟩ b₂ = true)
    (h₁ : st.top = .zero ∨ st.top = .nonI32 ∨ okL K bad fs ⟨thenS st, .other⟩ b₁ = true)
    (h₂ : st.top = .gd ∨ st.top = .nonI32 ∨ okL K bad fs ⟨st.S, .other⟩ b₂ = true) :
    (st'.top = .zero ∨ st'.top = .nonI32 ∨ okL K bad fs ⟨thenS st', .other⟩ b₁ = true) ∧
      (st'.top = .gd ∨ st'.top = .nonI32 ∨ okL K bad fs ⟨st'.S, .other⟩ b₂ = true) := by
  have hthen : st'.top = .zero ∨ st'.top = .nonI32 ∨
      okL K bad fs ⟨thenS st', .other⟩ b₁ = true := by
    by_cases hz : st'.top = .zero
    · exact .inl hz
    by_cases hn : st'.top = .nonI32
    · exact .inr (.inl hn)
    have hs : st.top ≠ .zero ∧ st.top ≠ .nonI32 := by
      rcases ht with h' | h' | ⟨k, h', -⟩ | ⟨-, h'⟩
      · rw [h']; exact ⟨hz, hn⟩
      · rw [h']; exact ⟨nofun, nofun⟩
      · rw [h']; exact ⟨nofun, nofun⟩
      · exact absurd h' hn
    have hb : okL K bad fs ⟨thenS st, .other⟩ b₁ = true := by
      rcases h₁ with h | h | h
      · exact absurd h hs.1
      · exact absurd h hs.2
      · exact h
    exact .inr (.inr (ih₁ _ _ (thenS_mono hS ht hz hn) hb))
  have helse : st'.top = .gd ∨ st'.top = .nonI32 ∨ okL K bad fs ⟨st'.S, .other⟩ b₂ = true := by
    by_cases hg : st'.top = .gd
    · exact .inl hg
    by_cases hn : st'.top = .nonI32
    · exact .inr (.inl hn)
    have hs : st.top ≠ .gd ∧ st.top ≠ .nonI32 := by
      rcases ht with h' | h' | ⟨k, h', -⟩ | ⟨-, h'⟩
      · rw [h']; exact ⟨hg, hn⟩
      · rw [h']; exact ⟨nofun, nofun⟩
      · rw [h']; exact ⟨nofun, nofun⟩
      · exact absurd h' hn
    have hb : okL K bad fs ⟨st.S, .other⟩ b₂ = true := by
      rcases h₂ with h | h | h
      · exact absurd h hs.1
      · exact absurd h hs.2
      · exact h
    exact .inr (.inr (ih₂ _ _ hS hb))
  exact ⟨hthen, helse⟩

theorem nextI_localGet_mono {st st' : FSt} (hS : ∀ k ∈ st.S, k ∈ st'.S) (x : LocalIdx) :
    FLe (nextI K st (.localGet x)) (nextI K st' (.localGet x)) := by
  refine .inr ⟨hS, ?_⟩
  simp only [nextI]
  by_cases hx : x.toNat ∈ st.S
  · have hx' : x.toNat ∈ st'.S := hS _ hx
    simp only [List.contains_iff_mem, hx, hx', ↓reduceIte]
    exact .inl rfl
  by_cases hx' : x.toNat ∈ st'.S
  · simp only [List.contains_iff_mem, hx, hx', ↓reduceIte]
    split
    · exact .inr (.inr (.inl ⟨_, rfl, .inr (.inr ⟨rfl, hx'⟩)⟩))
    · exact .inr (.inl rfl)
  · simp only [List.contains_iff_mem, hx, hx', ↓reduceIte]
    exact .inl rfl

theorem nextI_mono {st st' : FSt} (hS : ∀ k ∈ st.S, k ∈ st'.S) (i : Instr) :
    FLe (nextI K st i) (nextI K st' i) := by
  cases i
  case localGet x => exact nextI_localGet_mono hS x
  case localSet x => exact .inr ⟨addK_mono hS _, .inl rfl⟩
  case localTee x => exact .inr ⟨addK_mono hS _, .inl rfl⟩
  all_goals exact .inr ⟨hS, .inl rfl⟩

mutual

/-- **The check of an instruction is monotone.** -/
theorem okI_mono : ∀ (i : Instr) {st st' : FSt}, (∀ k ∈ st.S, k ∈ st'.S) →
    TLe st'.S st.top st'.top → okI K bad fs st i = true → okI K bad fs st' i = true
  | i, st, st', hS, ht, h => by
    cases i with
    | block _ b => exact okL_mono b (FLe.of_other hS _) h
    | loop _ b => exact okL_mono b (FLe.of_other hS _) h
    | tryTable _ _ b => exact okL_mono b (FLe.of_other hS _) h
    | if_ _ b₁ b₂ =>
      simp only [okI, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h ⊢
      have h' := okI_if_mono hS ht (fun S₁ S₁' hS₁ hb => okL_mono b₁ (FLe.of_other hS₁ _) hb)
        (fun S₁ S₁' hS₁ hb => okL_mono b₂ (FLe.of_other hS₁ _) hb)
        (by rcases h.1 with (h | h) | h <;> simp only [h, true_or, or_true])
        (by rcases h.2 with (h | h) | h <;> simp only [h, true_or, or_true])
      exact ⟨by rcases h'.1 with h | h | h <;> simp only [h, true_or, or_true],
        by rcases h'.2 with h | h | h <;> simp only [h, true_or, or_true]⟩
    | _ => simp only [okI] at h ⊢; exact reqI_mono ht _ h

/-- **The check of a sequence is monotone.** -/
theorem okL_mono : ∀ (is : List Instr) {st st' : FSt}, FLe st st' →
    okL K bad fs st is = true → okL K bad fs st' is = true
  | [], _, _, _, _ => by simp [okL]
  | i :: is, st, st', hle, h => by
    rcases hle with hex | ⟨hS, ht⟩
    · simp [okL, hex]
    · by_cases hst : st.top = .ex
      · have hst' : st'.top = .ex := by
          rcases ht with h' | h' | ⟨k, h', -⟩ | ⟨h', -⟩
          · exact h' ▸ hst
          all_goals rw [hst] at h'; cases h'
        simp [okL, hst']
      · have h' : okI K bad fs st i = true ∧ okL K bad fs (nextI K st i) is = true := by
          simpa [okL, hst] using h
        have h₁ : okI K bad fs st' i = true := okI_mono i hS ht h'.1
        have h₂ : okL K bad fs (nextI K st' i) is = true := okL_mono is (nextI_mono hS i) h'.2
        simp [okL, h₁, h₂]

end

/-! ## Administrative code -/

theorem nextX_mono {st st' : FSt} (hS : ∀ k ∈ st.S, k ∈ st'.S) (x : Admin) :
    FLe (nextX K st x) (nextX K st' x) := by
  cases x with
  | plain i => exact nextI_mono hS i
  | ref r => exact .inr ⟨hS, .inl rfl⟩
  | trap => exact .inr ⟨hS, .inl rfl⟩
  | _ => exact .inr ⟨hS, .inl rfl⟩

theorem okX_mono {st st' : FSt} (hS : ∀ k ∈ st.S, k ∈ st'.S) (ht : TLe st'.S st.top st'.top)
    (x : Admin) (h : okX K bad fs st x = true) : okX K bad fs st' x = true := by
  cases x with
  | plain i => exact okI_mono i hS ht h
  | label n cont b => exact okL_mono cont (FLe.of_other hS _) h
  | _ => rfl

theorem top_ex_of_TLe {S' : List Nat} {t t' : Top} (ht : TLe S' t t') (h : t = .ex) : t' = .ex := by
  rcases ht with h' | h' | ⟨k, h', -⟩ | ⟨h', -⟩
  · exact h' ▸ h
  all_goals rw [h] at h'; cases h'

/-- **The check of administrative code is monotone.** -/
theorem okA_mono : ∀ (l : List Admin) {st st' : FSt}, FLe st st' →
    okA K bad fs st l = true → okA K bad fs st' l = true
  | [], _, _, _, _ => by simp [okA]
  | x :: l, st, st', hle, h => by
    rcases hle with hex | ⟨hS, ht⟩
    · simp [okA, hex]
    · by_cases hst : st.top = .ex
      · simp [okA, top_ex_of_TLe ht hst]
      · have h' : okX K bad fs st x = true ∧ okA K bad fs (nextX K st x) l = true := by
          simpa [okA, hst] using h
        have h₁ : okX K bad fs st' x = true := okX_mono hS ht x h'.1
        have h₂ : okA K bad fs (nextX K st' x) l = true := okA_mono l (nextX_mono hS x) h'.2
        simp [okA, h₁, h₂]

/-- The state after administrative code (dead states stay dead). -/
def finA (K : List Nat) (st : FSt) : List Admin → FSt
  | [] => st
  | x :: l => if st.top = .ex then st else finA K (nextX K st x) l

theorem okA_ex {S : List Nat} (l : List Admin) : okA K bad fs ⟨S, .ex⟩ l = true := by
  cases l <;> simp [okA]

/-- **Checking a concatenation.** -/
theorem okA_append : ∀ (st : FSt) (l₁ l₂ : List Admin),
    okA K bad fs st (l₁ ++ l₂) = true ↔
      okA K bad fs st l₁ = true ∧ okA K bad fs (finA K st l₁) l₂ = true
  | st, [], l₂ => by simp [okA, finA]
  | st, x :: l₁, l₂ => by
    by_cases hst : st.top = .ex
    · have hst' : st = ⟨st.S, .ex⟩ := by rw [← hst]
      rw [hst']
      simp [okA, finA, okA_ex]
    · simp only [List.cons_append, okA, hst, finA, ↓reduceIte, beq_iff_eq, Bool.or_eq_true,
        false_or, Bool.and_eq_true]
      rw [okA_append (nextX K st x) l₁ l₂]
      exact and_assoc.symm

theorem subset_addK {S : List Nat} (x : Nat) : ∀ j ∈ S, j ∈ addK K x S := by
  intro j hj
  unfold addK
  split
  · exact List.mem_cons_of_mem _ hj
  · exact hj

theorem nextX_S_sub (st : FSt) (x : Admin) : ∀ j ∈ st.S, j ∈ (nextX K st x).S := by
  cases x with
  | plain i =>
    cases i <;> simp only [nextX, nextI] <;> first | exact fun j hj => hj | exact subset_addK _
  | _ => exact fun j hj => hj

theorem finA_S_mono : ∀ (st : FSt) (l : List Admin), ∀ k ∈ st.S, k ∈ (finA K st l).S
  | _, [], _, hk => hk
  | st, x :: l, k, hk => by
    unfold finA
    split
    · exact hk
    · exact finA_S_mono _ l k (nextX_S_sub st x k hk)

/-- A state after code knows at least what it knew before, and its top is at least `other`. -/
theorem fle_finA (st : FSt) (l : List Admin) : FLe ⟨st.S, .other⟩ (finA K st l) :=
  .inr ⟨finA_S_mono st l, .inr (.inl rfl)⟩

/-! ## Source code and values -/

theorem okA_expression : ∀ (st : FSt) (is : List Instr),
    okA K bad fs st (expression is) = okL K bad fs st is
  | _, [] => by simp [okA, okL, expression]
  | st, i :: is => by
    simp only [expression, List.map_cons, okA, okX, nextX, okL]
    rw [← okA_expression (nextI K st i) is]
    rfl

/-- The top state after a value. -/
def topOfVal : Val → Top
  | .num ⟨.int .i32, c⟩ => if c == 0 then .zero else .gd
  | _ => .nonI32

theorem nextX_toAdmin (st : FSt) (v : Val) : nextX K st v.toAdmin = ⟨st.S, topOfVal v⟩ := by
  cases v with
  | num n =>
    obtain ⟨ty, c⟩ := n
    cases ty with
    | int t => cases t <;> rfl
    | float t => rfl
  | vec b => rfl
  | ref r => rfl

@[simp] theorem okX_toAdmin (st : FSt) (v : Val) : okX K bad fs st v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _
  all_goals simp [Val.toAdmin, okX, okI, reqI, isBadCall, isSetK]

theorem topOfVal_ne_ex (v : Val) : topOfVal v ≠ .ex := by
  cases v with
  | num n =>
    obtain ⟨ty, c⟩ := n
    cases ty with
    | int t =>
      cases t
      · simp only [topOfVal]
        split <;> exact nofun
      · exact nofun
    | float t => exact nofun
  | vec b => exact nofun
  | ref r => exact nofun

/-- Values only set the top state. -/
theorem okA_vals_append {S : List Nat} {t : Top} (ht : t ≠ .ex) (vs : List Val) (l : List Admin) :
    okA K bad fs ⟨S, t⟩ (vals vs ++ l) = true ↔
      okA K bad fs ⟨S, (vs.getLast?.map topOfVal).getD t⟩ l = true := by
  induction vs generalizing t with
  | nil => simp [vals]
  | cons v vs ih =>
    have hv : topOfVal v ≠ .ex := topOfVal_ne_ex v
    simp only [vals, List.map_cons, List.cons_append, okA, ht, okX_toAdmin, nextX_toAdmin,
      beq_iff_eq, Bool.or_eq_true, false_or, Bool.true_and]
    have h₁ := ih hv
    simp only [vals] at h₁
    rw [h₁]
    cases vs with
    | nil => simp
    | cons w ws =>
      cases h : (w :: ws).getLast? with
      | none => simp at h
      | some x => simp [List.getLast?_cons_cons, h]

/-- The top state after values is never `ex`. -/
theorem topVals_ne_ex {t : Top} (ht : t ≠ .ex) (vs : List Val) :
    (vs.getLast?.map topOfVal).getD t ≠ .ex := by
  cases h : vs.getLast? with
  | none => simpa using ht
  | some v => simpa using topOfVal_ne_ex v

/-! ## Nested bodies -/

@[simp] theorem scopeSeqs_nil : scopeSeqs [] = [] := by simp [scopeSeqs]
@[simp] theorem frameScopes_nil : frameScopes [] = [] := by simp [frameScopes]

@[simp] theorem scopeSeqs_label (n : Nat) (cont : List Instr) (b l : List Admin) :
    scopeSeqs (.label n cont b :: l) = b :: (scopeSeqs b ++ scopeSeqs l) := by simp [scopeSeqs]
@[simp] theorem scopeSeqs_handler (n : Nat) (cs : List Catch) (b l : List Admin) :
    scopeSeqs (.handler n cs b :: l) = b :: (scopeSeqs b ++ scopeSeqs l) := by simp [scopeSeqs]
@[simp] theorem scopeSeqs_frame (n : Nat) (f : Frame) (b l : List Admin) :
    scopeSeqs (.frame n f b :: l) = scopeSeqs l := by simp [scopeSeqs]
@[simp] theorem frameScopes_label (n : Nat) (cont : List Instr) (b l : List Admin) :
    frameScopes (.label n cont b :: l) = frameScopes b ++ frameScopes l := by simp [frameScopes]
@[simp] theorem frameScopes_handler (n : Nat) (cs : List Catch) (b l : List Admin) :
    frameScopes (.handler n cs b :: l) = frameScopes b ++ frameScopes l := by simp [frameScopes]
@[simp] theorem frameScopes_frame (n : Nat) (f : Frame) (b l : List Admin) :
    frameScopes (.frame n f b :: l) = (f, b) :: (frameScopes b ++ frameScopes l) := by
  simp [frameScopes]

@[simp] theorem scopeSeqs_plain (i : Instr) (l : List Admin) :
    scopeSeqs (.plain i :: l) = scopeSeqs l := by simp [scopeSeqs]
@[simp] theorem frameScopes_plain (i : Instr) (l : List Admin) :
    frameScopes (.plain i :: l) = frameScopes l := by simp [frameScopes]
@[simp] theorem scopeSeqs_ref (r : Ref) (l : List Admin) :
    scopeSeqs (.ref r :: l) = scopeSeqs l := by simp [scopeSeqs]
@[simp] theorem frameScopes_ref (r : Ref) (l : List Admin) :
    frameScopes (.ref r :: l) = frameScopes l := by simp [frameScopes]

theorem scopeSeqs_append (l₁ l₂ : List Admin) :
    scopeSeqs (l₁ ++ l₂) = scopeSeqs l₁ ++ scopeSeqs l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [scopeSeqs, ih]

theorem frameScopes_append (l₁ l₂ : List Admin) :
    frameScopes (l₁ ++ l₂) = frameScopes l₁ ++ frameScopes l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [frameScopes, ih]

/-- Code without nested bodies has no nested scopes. -/
theorem scopes_of_codeBodies {l : List Admin} (h : codeBodies l = []) :
    scopeSeqs l = [] ∧ frameScopes l = [] := by
  induction l with
  | nil => simp
  | cons a as ih =>
    cases a with
    | label n cont b => simp at h
    | handler n cs b => simp at h
    | frame n f b => simp at h
    | plain i => simpa [scopeSeqs, frameScopes] using ih (by simpa using h)
    | ref r => simpa [scopeSeqs, frameScopes] using ih (by simpa using h)
    | trap => simpa [scopeSeqs, frameScopes] using ih (by simpa using h)
    | callRefType d => simpa [scopeSeqs, frameScopes] using ih (by simpa using h)
    | returnCallRefType d => simpa [scopeSeqs, frameScopes] using ih (by simpa using h)

end Silmaril.Wasm.Verify
