module

public import Silmaril.Wasm.Models.Runtime.Defs

/-!
# The runtime invariant: basic lemmas

Unfolding lemmas for `Rt.CodeIn` on appends, values and expressions, and the inclusion of
source instructions of `S` into the runtime instructions (`instrB_of_inFeatB`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Rt

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models
  Silmaril.Wasm.Models.Rt

variable {S : FeatureSet}

@[simp] theorem codeIn_nil : CodeIn S [] := trivial

@[simp] theorem codeIn_cons {a : Admin} {l : List Admin} :
    CodeIn S (a :: l) ↔ AdmIn S a ∧ CodeIn S l := Iff.rfl

@[simp] theorem codeIn_append {l₁ l₂ : List Admin} :
    CodeIn S (l₁ ++ l₂) ↔ CodeIn S l₁ ∧ CodeIn S l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, and_assoc]

@[simp] theorem admIn_plain {i : Instr} : AdmIn S (.plain i) ↔ instrB S i = true := Iff.rfl
@[simp] theorem admIn_ref {r : Ref} : AdmIn S (.ref r) := trivial
@[simp] theorem admIn_trap : AdmIn S .trap := trivial
@[simp] theorem admIn_callRefType {d : DefType} : AdmIn S (.callRefType d) := trivial
@[simp] theorem admIn_returnCallRefType {d : DefType} : AdmIn S (.returnCallRefType d) := trivial
@[simp] theorem admIn_label {n : Nat} {cont : List Instr} {body : List Admin} :
    AdmIn S (.label n cont body) ↔ Instr.insInFeatB S cont = true ∧ CodeIn S body := Iff.rfl
@[simp] theorem admIn_handler {n : Nat} {cs : List Catch} {body : List Admin} :
    AdmIn S (.handler n cs body) ↔ S.has .control = true ∧ CodeIn S body := Iff.rfl
@[simp] theorem admIn_frame {n : Nat} {f : Frame} {body : List Admin} :
    AdmIn S (.frame n f body) ↔ CodeIn S body := Iff.rfl

@[simp] theorem instrB_intConst (t : IntType) (b : BitVec t.width) :
    instrB S (.intConst t b) = true := rfl
@[simp] theorem instrB_floatConst (t : FloatType) (b : BitVec t.width) :
    instrB S (.floatConst t b) = true := rfl
@[simp] theorem instrB_vecConst (b : BitVec 128) : instrB S (.vecConst b) = true := rfl

/-- Code made of references only. -/
theorem codeIn_of_refs {l : List Admin} (h : ∀ a ∈ l, ∃ r, a = .ref r) : CodeIn S l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    obtain ⟨r, rfl⟩ := h a List.mem_cons_self
    exact ⟨trivial, ih fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

@[simp] theorem codeIn_take_drop_ref (rs : List Ref) (i n : Nat) :
    CodeIn S (List.take n (List.drop i (rs.map Admin.ref))) := by
  refine codeIn_of_refs fun a ha => ?_
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  exact ⟨r, rfl⟩

@[simp] theorem admIn_val (v : Val) : AdmIn S v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, instrB]

@[simp] theorem codeIn_vals (vs : List Val) : CodeIn S (vals vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨admIn_val v, ih⟩

@[simp] theorem admIn_constI32 (c : BitVec 32) : AdmIn S (constI32 c) := admIn_val _

@[simp] theorem admIn_aconst (a : AddrType) (i : BitVec a.intType.width) :
    AdmIn S (aconst a i) := by
  simp [aconst, instrB]

/-- Source instructions of `S` are runtime instructions of `S`. -/
theorem instrB_of_inFeatB {i : Instr} (h : Instr.inFeatB S i = true) : instrB S i = true := by
  cases i <;> simp_all [instrB]

theorem insInFeatB_cons {i : Instr} {is : List Instr} :
    Instr.insInFeatB S (i :: is) = true ↔
      Instr.inFeatB S i = true ∧ Instr.insInFeatB S is = true := by
  simp [Instr.insInFeatB]

theorem insInFeatB_iff {is : List Instr} :
    Instr.insInFeatB S is = true ↔ ∀ i ∈ is, Instr.inFeatB S i = true := by
  induction is with
  | nil => simp [Instr.insInFeatB]
  | cons i is ih => simp [insInFeatB_cons, ih]

theorem codeIn_expression {is : List Instr} (h : Instr.insInFeatB S is = true) :
    CodeIn S (expression is) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    have h' := insInFeatB_cons.mp h
    exact ⟨instrB_of_inFeatB h'.1, ih h'.2⟩

end Silmaril.Proofs.Wasm.Models.Rt
