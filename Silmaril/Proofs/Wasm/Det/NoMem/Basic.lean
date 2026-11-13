module

public import Silmaril.Wasm.Det.NoMem.Defs

/-!
# The memory-free, float-free subset: list lemmas

Reading `Seq` and `lastS` over appends, values, expressions and results; monotonicity in the
"previous element" flag. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Det.NoMem

variable {q : Nat → Bool} {ind : Bool} {fs : List Nat}

/-! ## Unfolding -/

@[simp] theorem seq_nil {p : Prop} : Seq q ind fs p [] := trivial

@[simp] theorem seq_cons {p : Prop} {a : Admin} {as : List Admin} :
    Seq q ind fs p (a :: as) ↔ (IsCRT a → p) ∧ AOk q ind fs a ∧ Seq q ind fs (InS q a) as :=
  Iff.rfl

@[simp] theorem lastS_nil {p : Prop} : lastS q p [] = p := rfl

@[simp] theorem lastS_cons {p : Prop} {a : Admin} {as : List Admin} :
    lastS q p (a :: as) = lastS q (InS q a) as := rfl

@[simp] theorem aOk_plain {i : Instr} : AOk q ind fs (.plain i) ↔ PlainOk q ind fs i := Iff.rfl

@[simp] theorem aOk_label {n : Nat} {cont : List Instr} {body : List Admin} :
    AOk q ind fs (.label n cont body) ↔
      (∀ i ∈ cont, instrB q ind fs i = true) ∧ Seq q ind fs False body := Iff.rfl

@[simp] theorem aOk_handler {n : Nat} {cs : List Catch} {body : List Admin} :
    AOk q ind fs (.handler n cs body) ↔ Seq q ind fs False body := Iff.rfl

@[simp] theorem aOk_frame {n : Nat} {f : Frame} {body : List Admin} :
    AOk q ind fs (.frame n f body) ↔ Seq q ind f.module.funcs False body := Iff.rfl

@[simp] theorem aOk_ref {r : Ref} : AOk q ind fs (.ref r) := trivial
@[simp] theorem aOk_trap : AOk q ind fs .trap := trivial
@[simp] theorem aOk_crt {d} : AOk q ind fs (.callRefType d) := trivial
@[simp] theorem aOk_rcrt {d} : AOk q ind fs (.returnCallRefType d) := trivial

@[simp] theorem isCRT_plain {i : Instr} : ¬ IsCRT (.plain i) := id
@[simp] theorem isCRT_ref {r : Ref} : ¬ IsCRT (.ref r) := id
@[simp] theorem isCRT_trap : ¬ IsCRT .trap := id
@[simp] theorem isCRT_label {n cont body} : ¬ IsCRT (.label n cont body) := id
@[simp] theorem isCRT_handler {n cs body} : ¬ IsCRT (.handler n cs body) := id
@[simp] theorem isCRT_frame {n f body} : ¬ IsCRT (.frame n f body) := id
@[simp] theorem isCRT_crt {d} : IsCRT (.callRefType d) := trivial
@[simp] theorem isCRT_rcrt {d} : IsCRT (.returnCallRefType d) := trivial

@[simp] theorem inS_trap : InS q .trap := trivial
@[simp] theorem inS_throwRef : InS q (.plain .throwRef) := trivial
@[simp] theorem inS_ref {r : Ref} : InS q (.ref r) ↔ ∀ b, r = .func b → q b = true := Iff.rfl
@[simp] theorem inS_label {n cont body} : ¬ InS q (.label n cont body) := id
@[simp] theorem inS_handler {n cs body} : ¬ InS q (.handler n cs body) := id
@[simp] theorem inS_frame {n f body} : ¬ InS q (.frame n f body) := id
@[simp] theorem inS_crt {d} : ¬ InS q (.callRefType d) := id
@[simp] theorem inS_rcrt {d} : ¬ InS q (.returnCallRefType d) := id

/-! ## Monotonicity in the flag -/

theorem seq_mono {p p' : Prop} (hp : p → p') {l : List Admin} (h : Seq q ind fs p l) :
    Seq q ind fs p' l := by
  cases l with
  | nil => trivial
  | cons a as =>
    rw [seq_cons] at h ⊢
    exact ⟨fun hc => hp (h.1 hc), h.2⟩

/-- When the code does not start with an administrative call, the flag does not matter. -/
theorem seq_irrel {p p' : Prop} {a : Admin} {as : List Admin} (ha : ¬ IsCRT a)
    (h : Seq q ind fs p (a :: as)) : Seq q ind fs p' (a :: as) := by
  rw [seq_cons] at h ⊢
  exact ⟨fun hc => absurd hc ha, h.2⟩

theorem lastS_mono {p p' : Prop} (hp : p → p') {l : List Admin} (h : lastS q p l) :
    lastS q p' l := by
  cases l with
  | nil => exact hp h
  | cons a as => exact h

/-- For nonempty code, the flag before it does not matter for `lastS`. -/
theorem lastS_irrel {p p' : Prop} {l : List Admin} (hl : l ≠ []) : lastS q p l = lastS q p' l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => rfl

/-! ## Appends -/

theorem lastS_append {p : Prop} (l₁ l₂ : List Admin) :
    lastS q p (l₁ ++ l₂) = lastS q (lastS q p l₁) l₂ := by
  induction l₁ generalizing p with
  | nil => rfl
  | cons a as ih => exact ih

theorem seq_append {p : Prop} (l₁ l₂ : List Admin) :
    Seq q ind fs p (l₁ ++ l₂) ↔ Seq q ind fs p l₁ ∧ Seq q ind fs (lastS q p l₁) l₂ := by
  induction l₁ generalizing p with
  | nil => simp
  | cons a as ih =>
    simp only [List.cons_append, seq_cons, ih, lastS_cons, and_assoc]

theorem seq_append3 {p : Prop} (l₁ l₂ l₃ : List Admin) :
    Seq q ind fs p (l₁ ++ l₂ ++ l₃) ↔ Seq q ind fs p l₁ ∧ Seq q ind fs (lastS q p l₁) l₂ ∧
      Seq q ind fs (lastS q (lastS q p l₁) l₂) l₃ := by
  rw [seq_append, seq_append, and_assoc, lastS_append]

/-! ## Values, expressions and results -/

@[simp] theorem isCRT_toAdmin (v : Val) : ¬ IsCRT v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> exact id

@[simp] theorem aOk_toAdmin (v : Val) : AOk q ind fs v.toAdmin := by
  match v with
  | .num ⟨.int _, _⟩ => exact Or.inl rfl
  | .num ⟨.float t, b⟩ => exact Or.inr (Or.inl ⟨t, b, rfl⟩)
  | .vec b => exact Or.inr (Or.inr ⟨b, rfl⟩)
  | .ref _ => trivial

@[simp] theorem seq_vals {p : Prop} (vs : List Val) : Seq q ind fs p (vals vs) := by
  induction vs generalizing p with
  | nil => trivial
  | cons v vs ih => exact ⟨fun h => absurd h (isCRT_toAdmin v), aOk_toAdmin v, ih⟩

theorem seq_vals_append {p : Prop} (vs : List Val) (l : List Admin) :
    Seq q ind fs p (vals vs ++ l) ↔ Seq q ind fs (lastS q p (vals vs)) l := by
  rw [seq_append]
  exact ⟨fun h => h.2, fun h => ⟨seq_vals vs, h⟩⟩

theorem instrsB_iff {b : List Instr} : instrsB q ind fs b = true ↔ ∀ i ∈ b, instrB q ind fs i = true := by
  induction b with
  | nil => simp [instrsB]
  | cons i is ih => simp [instrsB, ih]

theorem seq_expression {p : Prop} {b : List Instr} (h : ∀ i ∈ b, instrB q ind fs i = true) :
    Seq q ind fs p (expression b) := by
  induction b generalizing p with
  | nil => trivial
  | cons i is ih =>
    exact ⟨fun hc => absurd hc isCRT_plain, Or.inl (h i (List.mem_cons_self ..)),
      ih fun j hj => h j (List.mem_cons_of_mem _ hj)⟩

theorem seq_toAdmin {p : Prop} (r : Result) : Seq q ind fs p r.toAdmin := by
  cases r with
  | values vs => exact seq_vals vs
  | throw a => exact ⟨fun h => absurd h isCRT_ref, trivial, fun h => absurd h isCRT_plain,
      Or.inl rfl, trivial⟩
  | trap => exact ⟨fun h => absurd h isCRT_trap, trivial, trivial⟩

theorem seq_single {p : Prop} {a : Admin} (ha : ¬ IsCRT a) (h : AOk q ind fs a) :
    Seq q ind fs p [a] :=
  ⟨fun hc => absurd hc ha, h, trivial⟩

/-! ## Instructions -/

theorem instrB_block {bt : BlockType} {b : List Instr} :
    instrB q ind fs (.block bt b) = instrsB q ind fs b := by simp [instrB]

theorem instrB_loop {bt : BlockType} {b : List Instr} :
    instrB q ind fs (.loop bt b) = instrsB q ind fs b := by simp [instrB]

theorem instrB_if {bt : BlockType} {b₁ b₂ : List Instr} :
    instrB q ind fs (.if_ bt b₁ b₂) = (instrsB q ind fs b₁ && instrsB q ind fs b₂) := by
  simp [instrB]

theorem instrB_tryTable {bt : BlockType} {cs : List Catch} {b : List Instr} :
    instrB q ind fs (.tryTable bt cs b) = instrsB q ind fs b := by simp [instrB]

end Silmaril.Proofs.Wasm.Det.NoMem
