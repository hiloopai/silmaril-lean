module

public import Silmaril.Wasm.Verify.Guard.Defs
public import Silmaril.Proofs.Wasm.Verify.Reach.Step

/-!
# Guarded calls: basic lemmas

* `guardPl_plainOK`: the instruction predicate `GuardPl G B fs` meets the requirements of the
  reachability invariant, with guarded calls into `B`.
* The guard discipline `Chain`: append (`chain_append`), monotonicity in the state
  (`Chain.mono`), sequences without bad calls (`chain_of_noBad`), and source sequences
  (`chain_expression`: a `Guarded` sequence follows the discipline from any state).
* `pair_base`: the shape of most step rules (no exit on the left, the last element neither a
  guard nor an exit, no bad call on the right).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Validation

variable {G B : Nat → Prop} {fs : List Nat}

/-! ## Source level -/

theorem mem_exprRF {b : List Instr} {i : Instr} (hi : i ∈ b) {x : Nat} (hx : x ∈ instrRF i) :
    x ∈ exprRF b := by
  induction b with
  | nil => cases hi
  | cons j b ih =>
    rw [exprRF, List.mem_append]
    rcases List.mem_cons.1 hi with rfl | hi
    · exact .inl hx
    · exact .inr (ih hi)

theorem mem_exprCalls {b : List Instr} {i : Instr} (hi : i ∈ b) {x : Nat} (hx : x ∈ instrCalls i) :
    x ∈ exprCalls b := by
  induction b with
  | nil => cases hi
  | cons j b ih =>
    rw [exprCalls, List.mem_append]
    rcases List.mem_cons.1 hi with rfl | hi
    · exact .inl hx
    · exact .inr (ih hi)

theorem mem_exprBodies {b : List Instr} {i : Instr} (hi : i ∈ b) {k : List Instr}
    (hk : k ∈ instrBodies i) : k ∈ exprBodies b := by
  induction b with
  | nil => cases hi
  | cons j b ih =>
    rw [exprBodies, List.mem_append]
    rcases List.mem_cons.1 hi with rfl | hi
    · exact .inl hk
    · exact .inr (ih hi)

/-- The body of a structured instruction inherits `GuardPl`. -/
theorem GuardPl.of_body {i₀ : Instr} {b : List Instr} (hrf : instrRF i₀ = exprRF b)
    (hc : instrCalls i₀ = exprCalls b) (hb : ∀ k ∈ exprBodies b, k ∈ instrBodies i₀)
    (h : GuardPl G B fs i₀) : ∀ i ∈ b, PlOK (GuardPl G B fs) i := by
  intro i hi
  refine .inr ⟨fun x hx => h.1 x (hrf ▸ mem_exprRF hi hx),
    fun x hx => h.2.1 x (hc ▸ mem_exprCalls hi hx),
    fun k hk => h.2.2 k (hb k (mem_exprBodies hi hk))⟩

/-- **`GuardPl` meets the requirements of the invariant**, with guarded calls into `B`. -/
theorem guardPl_plainOK : PlainOK G B fs (GuardPl G B fs) where
  block _ _ h := GuardPl.of_body (by simp [instrRF]) (by simp [instrCalls])
    (fun k hk => by simp [instrBodies, hk]) h
  loop _ _ h := GuardPl.of_body (by simp [instrRF]) (by simp [instrCalls])
    (fun k hk => by simp [instrBodies, hk]) h
  tryTable _ _ _ h := GuardPl.of_body (by simp [instrRF]) (by simp [instrCalls])
    (fun k hk => by simp [instrBodies, hk]) h
  ifLeft _ _ _ h := .inr ⟨
    fun x hx => h.1 x (by simp only [instrRF, List.mem_append] at hx ⊢; exact .inl hx),
    fun x hx => h.2.1 x (by simp only [instrCalls, List.mem_append] at hx ⊢; exact .inl hx),
    fun k hk => h.2.2 k (by simp only [instrBodies, List.mem_cons, List.mem_append] at hk ⊢; tauto)⟩
  ifRight _ _ _ h := .inr ⟨
    fun x hx => h.1 x (by simp only [instrRF, List.mem_append] at hx ⊢; exact .inr hx),
    fun x hx => h.2.1 x (by simp only [instrCalls, List.mem_append] at hx ⊢; exact .inr hx),
    fun k hk => h.2.2 k (by simp only [instrBodies, List.mem_cons, List.mem_append] at hk ⊢; tauto)⟩
  call _ a h ha := h.2.1 _ (by simp [instrCalls]) a ha
  returnCall _ a h ha := h.1 _ (by simp [instrRF]) a ha
  refFunc _ a h ha := h.1 _ (by simp [instrRF]) a ha

/-! ## Runtime classification of elements -/

@[simp] theorem isExA_toAdmin (v : Val) : isExA v.toAdmin = false := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem isBadA_toAdmin (v : Val) : ¬ isBadA B fs v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, isBadA, BadI]

@[simp] theorem codeBodies_nil : codeBodies [] = [] := by simp [codeBodies]
@[simp] theorem codeConts_nil : codeConts [] = [] := by simp [codeConts]

theorem codeBodies_cons_flat {x : Admin} {l : List Admin}
    (hx : ∀ n cont body, x ≠ .label n cont body) (hy : ∀ n cs body, x ≠ .handler n cs body)
    (hz : ∀ n f body, x ≠ .frame n f body) : codeBodies (x :: l) = codeBodies l := by
  cases x <;> simp_all [codeBodies]

theorem codeConts_cons_flat {x : Admin} {l : List Admin}
    (hx : ∀ n cont body, x ≠ .label n cont body) (hy : ∀ n cs body, x ≠ .handler n cs body)
    (hz : ∀ n f body, x ≠ .frame n f body) : codeConts (x :: l) = codeConts l := by
  cases x <;> simp_all [codeConts]

@[simp] theorem codeBodies_label (n : Nat) (cont : List Instr) (body l : List Admin) :
    codeBodies (.label n cont body :: l) = body :: (codeBodies body ++ codeBodies l) := by
  simp [codeBodies]
@[simp] theorem codeBodies_handler (n : Nat) (cs : List Catch) (body l : List Admin) :
    codeBodies (.handler n cs body :: l) = body :: (codeBodies body ++ codeBodies l) := by
  simp [codeBodies]
@[simp] theorem codeBodies_frame (n : Nat) (f : Frame) (body l : List Admin) :
    codeBodies (.frame n f body :: l) = body :: (codeBodies body ++ codeBodies l) := by
  simp [codeBodies]
@[simp] theorem codeConts_label (n : Nat) (cont : List Instr) (body l : List Admin) :
    codeConts (.label n cont body :: l) = cont :: (codeConts body ++ codeConts l) := by
  simp [codeConts]
@[simp] theorem codeConts_handler (n : Nat) (cs : List Catch) (body l : List Admin) :
    codeConts (.handler n cs body :: l) = codeConts body ++ codeConts l := by
  simp [codeConts]
@[simp] theorem codeConts_frame (n : Nat) (f : Frame) (body l : List Admin) :
    codeConts (.frame n f body :: l) = codeConts body ++ codeConts l := by
  simp [codeConts]
@[simp] theorem codeBodies_plain (i : Instr) (l : List Admin) :
    codeBodies (.plain i :: l) = codeBodies l := by simp [codeBodies]
@[simp] theorem codeBodies_ref (r : Ref) (l : List Admin) :
    codeBodies (.ref r :: l) = codeBodies l := by simp [codeBodies]
@[simp] theorem codeBodies_trap (l : List Admin) : codeBodies (.trap :: l) = codeBodies l := by
  simp [codeBodies]
@[simp] theorem codeBodies_callRefType (d : DefType) (l : List Admin) :
    codeBodies (.callRefType d :: l) = codeBodies l := by simp [codeBodies]
@[simp] theorem codeBodies_returnCallRefType (d : DefType) (l : List Admin) :
    codeBodies (.returnCallRefType d :: l) = codeBodies l := by simp [codeBodies]
@[simp] theorem codeConts_plain (i : Instr) (l : List Admin) :
    codeConts (.plain i :: l) = codeConts l := by simp [codeConts]
@[simp] theorem codeConts_ref (r : Ref) (l : List Admin) :
    codeConts (.ref r :: l) = codeConts l := by simp [codeConts]
@[simp] theorem codeConts_trap (l : List Admin) : codeConts (.trap :: l) = codeConts l := by
  simp [codeConts]
@[simp] theorem codeConts_callRefType (d : DefType) (l : List Admin) :
    codeConts (.callRefType d :: l) = codeConts l := by simp [codeConts]
@[simp] theorem codeConts_returnCallRefType (d : DefType) (l : List Admin) :
    codeConts (.returnCallRefType d :: l) = codeConts l := by simp [codeConts]

@[simp] theorem codeBodies_toAdmin (v : Val) (l : List Admin) :
    codeBodies (v.toAdmin :: l) = codeBodies l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]
@[simp] theorem codeConts_toAdmin (v : Val) (l : List Admin) :
    codeConts (v.toAdmin :: l) = codeConts l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

@[simp] theorem codeBodies_append (l₁ l₂ : List Admin) :
    codeBodies (l₁ ++ l₂) = codeBodies l₁ ++ codeBodies l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [ih]

@[simp] theorem codeConts_append (l₁ l₂ : List Admin) :
    codeConts (l₁ ++ l₂) = codeConts l₁ ++ codeConts l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [ih]

@[simp] theorem codeBodies_vals (vs : List Val) : codeBodies (vals vs) = [] := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simpa [vals] using ih

@[simp] theorem codeConts_vals (vs : List Val) : codeConts (vals vs) = [] := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simpa [vals] using ih

@[simp] theorem codeBodies_expression (es : List Instr) : codeBodies (expression es) = [] := by
  induction es with
  | nil => simp [expression]
  | cons i es ih => simpa [expression] using ih

@[simp] theorem codeConts_expression (es : List Instr) : codeConts (expression es) = [] := by
  induction es with
  | nil => simp [expression]
  | cons i es ih => simpa [expression] using ih

@[simp] theorem codeBodies_map_ref (l : List Ref) : codeBodies (l.map Admin.ref) = [] := by
  induction l with
  | nil => simp
  | cons r l ih => simp [ih]

@[simp] theorem codeConts_map_ref (l : List Ref) : codeConts (l.map Admin.ref) = [] := by
  induction l with
  | nil => simp
  | cons r l ih => simp [ih]

@[simp] theorem codeBodies_take_drop_map_ref (n i : Nat) (l : List Ref) :
    codeBodies (List.take n (List.drop i (List.map Admin.ref l))) = [] := by
  rw [← List.map_drop, ← List.map_take]
  exact codeBodies_map_ref _

@[simp] theorem codeConts_take_drop_map_ref (n i : Nat) (l : List Ref) :
    codeConts (List.take n (List.drop i (List.map Admin.ref l))) = [] := by
  rw [← List.map_drop, ← List.map_take]
  exact codeConts_map_ref _

/-! ## The guard discipline -/

/-- The state after a sequence. -/
def finSt (st : PSt) (l : List Admin) : PSt := l.foldl (fun s x => nextSt x s) st

@[simp] theorem finSt_nil (st : PSt) : finSt st [] = st := rfl
@[simp] theorem finSt_cons (st : PSt) (x : Admin) (l : List Admin) :
    finSt st (x :: l) = finSt (nextSt x st) l := rfl
theorem finSt_append (st : PSt) (l₁ l₂ : List Admin) :
    finSt st (l₁ ++ l₂) = finSt (finSt st l₁) l₂ := by
  simp [finSt, List.foldl_append]

theorem nextSt_ex (x : Admin) : nextSt x .ex = .ex := by simp [nextSt]

@[simp] theorem finSt_ex (l : List Admin) : finSt .ex l = .ex := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [nextSt_ex] using ih

@[simp] theorem chain_nil (st : PSt) : Chain B fs st [] := trivial
@[simp] theorem chain_cons (st : PSt) (x : Admin) (l : List Admin) :
    Chain B fs st (x :: l) ↔ (isBadA B fs x → st ≠ .other) ∧ Chain B fs (nextSt x st) l := Iff.rfl

theorem chain_ex (l : List Admin) : Chain B fs .ex l := by
  induction l with
  | nil => trivial
  | cons x l ih => exact ⟨fun _ h => (by cases h), (by rw [nextSt_ex]; exact ih)⟩

theorem chain_append {st : PSt} {l₁ l₂ : List Admin} :
    Chain B fs st (l₁ ++ l₂) ↔ Chain B fs st l₁ ∧ Chain B fs (finSt st l₁) l₂ := by
  induction l₁ generalizing st with
  | nil => simp
  | cons x l ih =>
    simp only [List.cons_append, chain_cons, finSt_cons]
    rw [ih]
    tauto

/-- `st'` allows everything `st` allows. -/
def PSt.Le (st st' : PSt) : Prop := st = .other ∨ st' = .ex ∨ st = st'

theorem nextSt_mono {st st' : PSt} (h : st.Le st') (x : Admin) :
    (nextSt x st).Le (nextSt x st') := by
  rcases h with rfl | rfl | rfl
  · cases st' <;> cases hx : isExA x <;> cases hg : isGdA x <;> simp [nextSt, PSt.Le, hx, hg]
  · exact .inr (.inl (nextSt_ex x))
  · exact .inr (.inr rfl)

theorem Chain.mono {st st' : PSt} {l : List Admin} (h : Chain B fs st l) (hle : st.Le st') :
    Chain B fs st' l := by
  induction l generalizing st st' with
  | nil => trivial
  | cons x l ih =>
    refine ⟨fun hb hst => ?_, ih h.2 (nextSt_mono hle x)⟩
    rcases hle with rfl | rfl | rfl
    · exact absurd rfl (h.1 hb)
    · cases hst
    · exact h.1 hb hst

theorem PSt.le_other (st : PSt) : PSt.Le .other st := .inl rfl
theorem PSt.le_ex (st : PSt) : PSt.Le st .ex := .inr (.inl rfl)
theorem PSt.le_refl (st : PSt) : PSt.Le st st := .inr (.inr rfl)

/-- A sequence without bad calls follows the discipline from any state. -/
theorem chain_of_noBad {l : List Admin} (h : ∀ x ∈ l, ¬ isBadA B fs x) (st : PSt) :
    Chain B fs st l := by
  induction l generalizing st with
  | nil => trivial
  | cons x l ih =>
    exact ⟨fun hb => absurd hb (h x (by simp)), ih (fun y hy => h y (by simp [hy])) _⟩

/-! ## Source sequences -/

theorem isBadA_plain {i : Instr} : isBadA B fs (.plain i) ↔ BadI B fs i := Iff.rfl

theorem nextSt_gd {c : BitVec IntType.i32.width} (hc : c ≠ 0) (st : PSt) :
    nextSt (.plain (.intConst .i32 c)) st ≠ .other := by
  unfold nextSt
  split
  · simp
  · simp only [isGdA]
    have hc' : (c != 0) = true := bne_iff_ne.2 hc
    simp only [hc', ↓reduceIte]
    exact fun h => by cases h

theorem chain_expression_aux : ∀ (b : List Instr) (st : PSt) (pre : List Instr),
    Guarded B fs (pre ++ b) → (∀ j, pre.getLast? = some j → GdI j → st ≠ .other) →
    Chain B fs st (expression b)
  | [], _, _, _, _ => trivial
  | i :: b, st, pre, h, hpre => by
    refine ⟨fun hb => ?_, ?_⟩
    · obtain ⟨j, hj, hg⟩ := h pre i b rfl hb
      exact hpre j hj hg
    · refine chain_expression_aux b _ (pre ++ [i]) (by simpa using h) fun j hj hg => ?_
      have hji : j = i := by simpa using hj.symm
      obtain ⟨c, rfl, hc⟩ := hji ▸ hg
      exact nextSt_gd hc st

/-- **A guarded source sequence follows the discipline from any state.** -/
theorem chain_expression {b : List Instr} (h : Guarded B fs b) (st : PSt) :
    Chain B fs st (expression b) :=
  chain_expression_aux b st [] (by simpa using h) (fun j hj => by cases hj)

/-! ## Bodies of acceptable instructions -/

theorem not_badI_of_callees {i : Instr} (h : instrCallees i = []) : ¬ BadI B fs i := by
  rintro ⟨y, a, rfl, -⟩
  simp [instrCallees] at h

theorem guarded_of_noBad {b : List Instr} (h : ∀ j ∈ b, ¬ BadI B fs j) : Guarded B fs b :=
  fun _ i _ hb hbad => absurd hbad (h i (by simp [hb]))

/-- The body of an acceptable structured instruction is guarded. -/
theorem PlOK.guarded {i : Instr} {b : List Instr} (hcal : instrCallees i = exprCallees b)
    (hb : b ∈ instrBodies i) (h : PlOK (GuardPl G B fs) i) : Guarded B fs b := by
  rcases h with h | h
  · exact guarded_of_noBad fun j hj =>
      not_badI_of_callees (instrCallees_nil_of_mem (hcal ▸ h) hj)
  · exact h.2.2 b hb

theorem PlOK.guarded_block {bt : BlockType} {b : List Instr}
    (h : PlOK (GuardPl G B fs) (.block bt b)) : Guarded B fs b :=
  PlOK.guarded (by simp [instrCallees]) (by simp [instrBodies]) h

theorem PlOK.guarded_loop {bt : BlockType} {b : List Instr}
    (h : PlOK (GuardPl G B fs) (.loop bt b)) : Guarded B fs b :=
  PlOK.guarded (by simp [instrCallees]) (by simp [instrBodies]) h

theorem PlOK.guarded_tryTable {bt : BlockType} {cs : List Catch} {b : List Instr}
    (h : PlOK (GuardPl G B fs) (.tryTable bt cs b)) : Guarded B fs b :=
  PlOK.guarded (by simp [instrCallees]) (by simp [instrBodies]) h

end Silmaril.Wasm.Verify
