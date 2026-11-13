module

public import Silmaril.Wasm.Det.GrowTrap.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
public import Silmaril.Wasm.SingleThreaded.Locality

/-!
# Subset 2 (allocation failure traps): basic facts about the invariant

Algebra of the runtime invariant of `Silmaril.Wasm.Det.GrowTrap`: `GAs` is pointwise
(`gAs_append`), `GrowSeq` splits at an append with the right part as continuation
(`growSeq_append`), `PairSeq` with the last element of the left part as predecessor
(`pairSeq_append`); values satisfy everything (`gAs_vals`, `growSeq_vals`, `pairSeq_vals`);
source sequences of the subset satisfy the runtime conditions (`gAs_expression`,
`growSeq_expression`, `pairSeq_expression`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.GrowTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Det.GrowTrap
open Silmaril.Wasm.Verify (instrCalls exprCalls)

variable {G : Nat → Prop} {fs : List Nat}

/-! ## Values -/

@[simp] theorem isGrowA_toAdmin (v : Val) : isGrowA v.toAdmin = false := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem isCRT_toAdmin (v : Val) : isCRT v.toAdmin = false := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem isGrowA_plain (i : Instr) : isGrowA (.plain i) = isGrow i := by
  cases i <;> rfl
@[simp] theorem isGrowA_trap : isGrowA .trap = false := rfl
@[simp] theorem isGrowA_ref (r : Ref) : isGrowA (.ref r) = false := rfl
@[simp] theorem isGrowA_callRefType (d) : isGrowA (.callRefType d) = false := rfl
@[simp] theorem isGrowA_returnCallRefType (d) : isGrowA (.returnCallRefType d) = false := rfl
@[simp] theorem isGrowA_label (n : Nat) (k : List Instr) (b : List Admin) :
    isGrowA (.label n k b) = false := rfl
@[simp] theorem isGrowA_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    isGrowA (.handler n cs b) = false := rfl
@[simp] theorem isGrowA_frame (n : Nat) (f : Frame) (b : List Admin) :
    isGrowA (.frame n f b) = false := rfl
@[simp] theorem isCRT_plain (i : Instr) : isCRT (.plain i) = false := rfl
@[simp] theorem isCRT_trap : isCRT .trap = false := rfl
@[simp] theorem isCRT_ref (r : Ref) : isCRT (.ref r) = false := rfl
@[simp] theorem isCRT_callRefType (d) : isCRT (.callRefType d) = true := rfl
@[simp] theorem isCRT_returnCallRefType (d) : isCRT (.returnCallRefType d) = false := rfl
@[simp] theorem isCRT_label (n : Nat) (k : List Instr) (b : List Admin) :
    isCRT (.label n k b) = false := rfl
@[simp] theorem isCRT_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    isCRT (.handler n cs b) = false := rfl
@[simp] theorem isCRT_frame (n : Nat) (f : Frame) (b : List Admin) :
    isCRT (.frame n f b) = false := rfl

@[simp] theorem instrCalls_flat {i : Instr} (h : ∀ bt b, i ≠ .block bt b)
    (h' : ∀ bt b, i ≠ .loop bt b) (h'' : ∀ bt b₁ b₂, i ≠ .if_ bt b₁ b₂)
    (h''' : ∀ bt cs b, i ≠ .tryTable bt cs b) (hc : ∀ x, i ≠ .call x) : instrCalls i = [] := by
  cases i <;> simp_all [instrCalls]

theorem gA_toAdmin (v : Val) : GA G fs v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;>
    simp [Val.toAdmin, GA, instrOk, flatOk, CallsIn, instrCalls]

@[simp] theorem gAs_nil : GAs G fs [] := trivial

@[simp] theorem gAs_cons {a : Admin} {l : List Admin} : GAs G fs (a :: l) ↔ GA G fs a ∧ GAs G fs l :=
  Iff.rfl

@[simp] theorem gAs_append {l₁ l₂ : List Admin} :
    GAs G fs (l₁ ++ l₂) ↔ GAs G fs l₁ ∧ GAs G fs l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, and_assoc]

@[simp] theorem gAs_vals (vs : List Val) : GAs G fs (vals vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨gA_toAdmin v, ih⟩

/-! ## `GrowSeq` -/

@[simp] theorem growSeq_nil (K : List Admin) : GrowSeq [] K := trivial

@[simp] theorem growSeq_cons {x : Admin} {l K : List Admin} :
    GrowSeq (x :: l) K ↔ (isGrowA x = true → guardA (l ++ K) = true) ∧ GrowSeq l K := Iff.rfl

theorem growSeq_append {l₁ l₂ K : List Admin} :
    GrowSeq (l₁ ++ l₂) K ↔ GrowSeq l₁ (l₂ ++ K) ∧ GrowSeq l₂ K := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, and_assoc]

/-- A sequence without `memory.grow` satisfies `GrowSeq` in every continuation. -/
theorem growSeq_of_noGrow {l : List Admin} (h : ∀ x ∈ l, isGrowA x = false) (K : List Admin) :
    GrowSeq l K := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    exact ⟨fun ha => absurd ha (by simp [h a (by simp)]),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

@[simp] theorem growSeq_vals (vs : List Val) (K : List Admin) : GrowSeq (vals vs) K :=
  growSeq_of_noGrow (by simp [vals]) K

/-- The guard of a source sequence is a guard of its lowering, in every continuation. -/
theorem guardRestA_expression {l : List Instr} (K : List Admin) (h : guardRestB l = true) :
    guardRestA (expression l ++ K) = true := by
  unfold guardRestB at h
  split at h
  · simpa [expression, guardRestA] using h
  · cases h

theorem teeGuardA_expression {l : List Instr} (K : List Admin) (h : teeGuardB l = true) :
    teeGuardA (expression l ++ K) = true := by
  cases l with
  | nil => cases h
  | cons i l =>
    cases i with
    | localTee x =>
      have hr : guardRestB l = true := by simpa [teeGuardB] using h
      simpa [expression, teeGuardA] using guardRestA_expression K hr
    | _ => simp [teeGuardB] at h

theorem guardA_expression {l : List Instr} (K : List Admin) (h : guardB l = true) :
    guardA (expression l ++ K) = true := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Bool.or_eq_true_iff.mpr (.inl (guardRestA_expression K h))
  · exact Bool.or_eq_true_iff.mpr (.inr (teeGuardA_expression K h))

theorem seqOk_cons {i : Instr} {is : List Instr} :
    seqOk (i :: is) = true ↔ instrOk i = true ∧ (isGrow i = true → guardB is = true) ∧
      seqOk is = true := by
  simp only [seqOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  cases isGrow i <;> simp [and_assoc]

theorem seqOk_mem {is : List Instr} (h : seqOk is = true) {i : Instr} (hi : i ∈ is) :
    instrOk i = true := by
  induction is with
  | nil => cases hi
  | cons j is ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (seqOk_cons.mp h).1
    · exact ih (seqOk_cons.mp h).2.2 hi


/-- **A source sequence of the subset satisfies `GrowSeq`**, in every continuation. -/
theorem growSeq_expression {is : List Instr} (h : seqOk is = true) (K : List Admin) :
    GrowSeq (expression is) K := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    have h' := seqOk_cons.mp h
    refine ⟨fun hg => ?_, ih h'.2.2⟩
    have hg' : isGrow i = true := by simpa using hg
    exact guardA_expression K (h'.2.1 hg')

/-! ## `PairSeq` -/

/-- The predecessor of the element after `l`, `p` before `l`. -/
def lastP (p : Option Admin) (l : List Admin) : Option Admin :=
  match l.getLast? with
  | some x => some x
  | none => p

/-- An `EndOk` predecessor. -/
def EndOpt (G : Nat → Prop) (p : Option Admin) : Prop := ∃ y, p = some y ∧ EndOk G y

@[simp] theorem pairSeq_nil (p : Option Admin) : PairSeq G p [] := trivial

@[simp] theorem pairSeq_cons {p : Option Admin} {x : Admin} {l : List Admin} :
    PairSeq G p (x :: l) ↔ (isCRT x = true → EndOpt G p) ∧ PairSeq G (some x) l := Iff.rfl

theorem lastP_cons (p : Option Admin) (x : Admin) (l : List Admin) :
    lastP p (x :: l) = lastP (some x) l := by
  unfold lastP
  rcases hl : l.getLast? with _ | y
  · simp [List.getLast?_eq_none_iff.mp hl]
  · simp [List.getLast?_cons, hl]

theorem pairSeq_append {p : Option Admin} {l₁ l₂ : List Admin} :
    PairSeq G p (l₁ ++ l₂) ↔ PairSeq G p l₁ ∧ PairSeq G (lastP p l₁) l₂ := by
  induction l₁ generalizing p with
  | nil => simp [lastP]
  | cons a l ih => simp [ih, lastP_cons, and_assoc]

/-- Only the head condition depends on the predecessor. -/
theorem PairSeq.congr {p q : Option Admin} {l : List Admin} (h : PairSeq G p l)
    (hpq : EndOpt G p → EndOpt G q) : PairSeq G q l := by
  cases l with
  | nil => trivial
  | cons x l => exact ⟨fun hx => hpq (h.1 hx), h.2⟩

theorem pairSeq_of_noCRT {l : List Admin} (h : ∀ x ∈ l, isCRT x = false) (p : Option Admin) :
    PairSeq G p l := by
  induction l generalizing p with
  | nil => trivial
  | cons a l ih =>
    exact ⟨fun ha => absurd ha (by simp [h a (by simp)]),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _⟩

@[simp] theorem pairSeq_vals (vs : List Val) (p : Option Admin) : PairSeq G p (vals vs) :=
  pairSeq_of_noCRT (by simp [vals]) p

theorem pairSeq_expression (is : List Instr) (p : Option Admin) :
    PairSeq G p (expression is) :=
  pairSeq_of_noCRT (by simp [expression]) p

/-! ## Source sequences as administrative code -/

theorem mem_exprCalls {b : List Instr} {i : Instr} (hi : i ∈ b) {x : Nat}
    (hx : x ∈ instrCalls i) : x ∈ exprCalls b := by
  induction b with
  | nil => cases hi
  | cons j b ih =>
    rw [exprCalls, List.mem_append]
    rcases List.mem_cons.mp hi with rfl | hi
    · exact .inl hx
    · exact .inr (ih hi)

/-- The instructions of a structured body name only functions the structured instruction
names. -/
theorem callsIn_body {i₀ : Instr} {b : List Instr} (h : CallsIn G fs i₀)
    (hb : ∀ x, x ∈ exprCalls b → x ∈ instrCalls i₀) : ∀ i ∈ b, CallsIn G fs i :=
  fun _ hi x hx => h x (hb x (mem_exprCalls hi hx))

/-- **A source sequence of the subset is administrative code of the subset.** -/
theorem gAs_expression {is : List Instr} (h : seqOk is = true) (hc : ∀ i ∈ is, CallsIn G fs i) :
    GAs G fs (expression is) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    exact ⟨⟨seqOk_mem h (by simp), hc i (by simp)⟩,
      ih (seqOk_cons.mp h).2.2 fun j hj => hc j (List.mem_cons_of_mem _ hj)⟩

end Silmaril.Proofs.Wasm.Det.GrowTrap
