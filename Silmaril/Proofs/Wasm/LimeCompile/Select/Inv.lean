module

public import Silmaril.Wasm.LimeCompile.Select.Defs

/-!
# Erasing `select` annotations: inversion lemmas

What code can erase to a given erased code: values, references, traps and every plain
instruction other than `select` and the structured ones are **rigid** (their only preimage is
themselves); `block`, `loop`, `if`, `try_table`, `label`, `handler` and `frame` invert to the
same shape with erasure-equal contents; erased lists split like their images.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Select

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Select

theorem selL_eq_map (l : List Instr) : selL l = l.map selI := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [selL, ih, List.map_cons]

theorem selAs_eq_map (l : List Admin) : selAs l = l.map selA := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [selAs, ih, List.map_cons]

@[simp] theorem selAs_nil : selAs [] = [] := rfl

@[simp] theorem selAs_cons (a : Admin) (l : List Admin) : selAs (a :: l) = selA a :: selAs l :=
  rfl

@[simp] theorem selAs_append (l l' : List Admin) : selAs (l ++ l') = selAs l ++ selAs l' := by
  simp only [selAs_eq_map, List.map_append]

@[simp] theorem selL_nil : selL [] = [] := rfl

@[simp] theorem selL_cons (i : Instr) (l : List Instr) : selL (i :: l) = selI i :: selL l := rfl

@[simp] theorem selA_plain (i : Instr) : selA (.plain i) = .plain (selI i) := rfl

@[simp] theorem selA_label (n : Nat) (cont : List Instr) (b : List Admin) :
    selA (.label n cont b) = .label n (selL cont) (selAs b) := rfl

@[simp] theorem selA_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    selA (.handler n cs b) = .handler n cs (selAs b) := rfl

@[simp] theorem selA_frame (n : Nat) (f : Frame) (b : List Admin) :
    selA (.frame n f b) = .frame n f (selAs b) := rfl

@[simp] theorem selA_ref (r : Ref) : selA (.ref r) = .ref r := rfl

@[simp] theorem selA_trap : selA .trap = .trap := rfl

@[simp] theorem selA_callRefType (d : DefType) : selA (.callRefType d) = .callRefType d := rfl

@[simp] theorem selA_returnCallRefType (d : DefType) :
    selA (.returnCallRefType d) = .returnCallRefType d := rfl

@[simp] theorem selI_block (bt : BlockType) (b : List Instr) :
    selI (.block bt b) = .block bt (selL b) := rfl

@[simp] theorem selI_loop (bt : BlockType) (b : List Instr) :
    selI (.loop bt b) = .loop bt (selL b) := rfl

@[simp] theorem selI_if (bt : BlockType) (b₁ b₂ : List Instr) :
    selI (.if_ bt b₁ b₂) = .if_ bt (selL b₁) (selL b₂) := rfl

@[simp] theorem selI_tryTable (bt : BlockType) (cs : List Catch) (b : List Instr) :
    selI (.tryTable bt cs b) = .tryTable bt cs (selL b) := rfl

@[simp] theorem selI_select (ts : Option (List ValType)) : selI (.select ts) = .select none := rfl

/-- A plain instruction that is neither `select` nor structured is fixed by erasure. -/
def Flat (i : Instr) : Prop := i.bodies = [] ∧ ∀ ts, i ≠ .select ts

theorem selI_of_flat {i : Instr} (h : Flat i) : selI i = i := by
  cases i <;> first | rfl | exact absurd rfl (h.2 _) | exact absurd h.1 (by simp [Instr.bodies])

/-- The only preimage of a flat instruction is itself. -/
theorem eq_of_selI_flat {i j : Instr} (hj : Flat j) (h : selI i = selI j) : i = j := by
  rw [selI_of_flat hj] at h
  cases i <;> first
    | exact h
    | exact absurd h.symm (hj.2 _)
    | exact absurd hj.1 (by rw [← h]; simp [Instr.bodies])


theorem flat_mk {i : Instr} (h₁ : i.bodies = []) (h₂ : ∀ ts, i ≠ .select ts) : Flat i := ⟨h₁, h₂⟩

/-- A **rigid** administrative instruction: its only erasure-preimage is itself. -/
def Rig (a : Admin) : Prop := ∀ b, selA b = selA a → b = a

theorem rig_plain {i : Instr} (h : Flat i) : Rig (.plain i) := by
  intro b hb
  cases b with
  | plain j => exact congrArg Admin.plain (eq_of_selI_flat h (Admin.plain.inj hb))
  | _ => cases hb

theorem rig_ref (r : Ref) : Rig (.ref r) := by
  intro b hb
  cases b <;> cases hb
  rfl

theorem rig_trap : Rig .trap := by
  intro b hb
  cases b <;> cases hb
  rfl

theorem rig_callRefType (d : DefType) : Rig (.callRefType d) := by
  intro b hb
  cases b <;> cases hb
  rfl

theorem rig_returnCallRefType (d : DefType) : Rig (.returnCallRefType d) := by
  intro b hb
  cases b <;> cases hb
  rfl

theorem rig_val (v : Val) : Rig v.toAdmin := by
  match v with
  | .num ⟨.int _, _⟩ => exact rig_plain (flat_mk rfl fun _ h => nomatch h)
  | .num ⟨.float _, _⟩ => exact rig_plain (flat_mk rfl fun _ h => nomatch h)
  | .vec _ => exact rig_plain (flat_mk rfl fun _ h => nomatch h)
  | .ref r => exact rig_ref r

@[simp] theorem selA_val (v : Val) : selA v.toAdmin = v.toAdmin := by
  match v with
  | .num ⟨.int _, _⟩ | .num ⟨.float _, _⟩ | .vec _ | .ref _ => rfl

@[simp] theorem selAs_vals (vs : List Val) : selAs (vals vs) = vals vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [vals, List.map_cons, selAs_cons, selA_val] at ih ⊢; rw [ih]

theorem selAs_expression (b : List Instr) : selAs (expression b) = expression (selL b) := by
  induction b with
  | nil => rfl
  | cons i b ih => simp only [expression, List.map_cons, selAs_cons, selA_plain, selL_cons] at ih ⊢; rw [ih]

theorem selAs_eq_nil {X : List Admin} : selAs X = [] ↔ X = [] := by
  cases X <;> simp

theorem eq_of_selAs_rig {L X : List Admin} (hL : ∀ a ∈ L, Rig a) (h : selAs X = selAs L) :
    X = L := by
  induction L generalizing X with
  | nil => exact selAs_eq_nil.mp h
  | cons a L ih =>
    cases X with
    | nil => cases h
    | cons b X =>
      have h' : selA b = selA a ∧ selAs X = selAs L := by simpa using h
      rw [hL a (by simp) b h'.1, ih (fun x hx => hL x (by simp [hx])) h'.2]

theorem rig_vals (vs : List Val) : ∀ a ∈ vals vs, Rig a := by
  intro a ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
  exact rig_val v

theorem eq_vals_of_selAs {X : List Admin} {vs : List Val} (h : selAs X = selAs (vals vs)) :
    X = vals vs :=
  eq_of_selAs_rig (rig_vals vs) h

theorem selAs_eq_append {X A B : List Admin} (h : selAs X = selAs (A ++ B)) :
    ∃ A' B', X = A' ++ B' ∧ selAs A' = selAs A ∧ selAs B' = selAs B := by
  rw [selAs_eq_map, selAs_eq_map, List.map_append] at h
  obtain ⟨A', B', rfl, hA, hB⟩ := List.map_eq_append_iff.mp h
  exact ⟨A', B', rfl, by rw [selAs_eq_map, hA, selAs_eq_map], by rw [selAs_eq_map, hB, selAs_eq_map]⟩

theorem selAs_eq_vals_append {X B : List Admin} {vs : List Val}
    (h : selAs X = selAs (vals vs ++ B)) : ∃ B', X = vals vs ++ B' ∧ selAs B' = selAs B := by
  obtain ⟨A', B', rfl, hA, hB⟩ := selAs_eq_append h
  exact ⟨B', by rw [eq_vals_of_selAs hA], hB⟩

theorem selAs_eq_singleton {X : List Admin} {a : Admin} (h : selAs X = selAs [a]) :
    ∃ a', X = [a'] ∧ selA a' = selA a := by
  rcases X with _ | ⟨a', _ | ⟨b, X⟩⟩
  · cases h
  · exact ⟨a', rfl, by simpa using h⟩
  · exact absurd (List.cons.inj h).2 (by simp)

theorem selA_eq_plain {a : Admin} {j : Instr} (h : selA a = .plain j) :
    ∃ i, a = .plain i ∧ selI i = j := by
  cases a <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem selA_eq_label {a : Admin} {n : Nat} {cont : List Instr} {body : List Admin}
    (h : selA a = .label n cont body) :
    ∃ cont' body', a = .label n cont' body' ∧ selL cont' = cont ∧ selAs body' = body := by
  cases a <;> cases h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem selA_eq_handler {a : Admin} {n : Nat} {cs : List Catch} {body : List Admin}
    (h : selA a = .handler n cs body) :
    ∃ body', a = .handler n cs body' ∧ selAs body' = body := by
  cases a <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem selA_eq_frame {a : Admin} {n : Nat} {f : Frame} {body : List Admin}
    (h : selA a = .frame n f body) :
    ∃ body', a = .frame n f body' ∧ selAs body' = body := by
  cases a <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem selI_eq_block {i : Instr} {bt : BlockType} {B : List Instr} (h : selI i = .block bt B) :
    ∃ b, i = .block bt b ∧ selL b = B := by
  cases i <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem selI_eq_loop {i : Instr} {bt : BlockType} {B : List Instr} (h : selI i = .loop bt B) :
    ∃ b, i = .loop bt b ∧ selL b = B := by
  cases i <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem selI_eq_if {i : Instr} {bt : BlockType} {B₁ B₂ : List Instr}
    (h : selI i = .if_ bt B₁ B₂) : ∃ b₁ b₂, i = .if_ bt b₁ b₂ ∧ selL b₁ = B₁ ∧ selL b₂ = B₂ := by
  cases i <;> cases h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem selI_eq_tryTable {i : Instr} {bt : BlockType} {cs : List Catch} {B : List Instr}
    (h : selI i = .tryTable bt cs B) : ∃ b, i = .tryTable bt cs b ∧ selL b = B := by
  cases i <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem selI_eq_select {i : Instr} {ts : Option (List ValType)} (h : selI i = .select ts) :
    ∃ ts', i = .select ts' := by
  cases i <;> cases h
  exact ⟨_, rfl⟩

end Silmaril.Proofs.Wasm.LimeCompile.Select
