module

public import Silmaril.Wasm.Verify.Reach.Defs

/-!
# Function reachability: basic lemmas

Computation lemmas for `codePlains` and `instrCallees`, the store invariant `StoreIn` under the
store updates of the step rules, and `CodeIn.sub`, which rebuilds the code invariant from
inclusions of references, frames and source instructions (the shape of silmaril-lean's
`CfgGood.mk'`, `Silmaril.Wasm.SingleThreaded.Locality`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Validation

variable {H : Type} {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop}

/-! ## `codePlains` -/

@[simp] theorem codePlains_nil : codePlains [] = [] := by simp [codePlains]
@[simp] theorem codePlains_plain (i : Instr) (l : List Admin) :
    codePlains (.plain i :: l) = i :: codePlains l := by simp [codePlains]
@[simp] theorem codePlains_ref (r : Ref) (l : List Admin) :
    codePlains (.ref r :: l) = codePlains l := by simp [codePlains]
@[simp] theorem codePlains_callRefType (d : DefType) (l : List Admin) :
    codePlains (.callRefType d :: l) = codePlains l := by simp [codePlains]
@[simp] theorem codePlains_returnCallRefType (d : DefType) (l : List Admin) :
    codePlains (.returnCallRefType d :: l) = codePlains l := by simp [codePlains]
@[simp] theorem codePlains_trap (l : List Admin) : codePlains (.trap :: l) = codePlains l := by
  simp [codePlains]
@[simp] theorem codePlains_label (n : Nat) (cont : List Instr) (body l : List Admin) :
    codePlains (.label n cont body :: l) = cont ++ codePlains body ++ codePlains l := by
  simp [codePlains]
@[simp] theorem codePlains_handler (n : Nat) (cs : List Catch) (body l : List Admin) :
    codePlains (.handler n cs body :: l) = codePlains body ++ codePlains l := by
  simp [codePlains]
@[simp] theorem codePlains_frame (n : Nat) (f : Frame) (body l : List Admin) :
    codePlains (.frame n f body :: l) = codePlains body ++ codePlains l := by
  simp [codePlains]

@[simp] theorem codePlains_append (l₁ l₂ : List Admin) :
    codePlains (l₁ ++ l₂) = codePlains l₁ ++ codePlains l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [ih]

@[simp] theorem codePlains_expression (es : List Instr) : codePlains (expression es) = es := by
  induction es with
  | nil => simp [expression]
  | cons i es ih => simpa [expression] using ih

@[simp] theorem codePlains_map_ref (l : List Ref) : codePlains (l.map Admin.ref) = [] := by
  induction l with
  | nil => simp
  | cons r l ih => simp [ih]

/-- The source instructions of values are constants. -/
def IsConst (i : Instr) : Prop :=
  (∃ t b, i = .intConst t b) ∨ (∃ t b, i = .floatConst t b) ∨ ∃ b, i = .vecConst b

theorem codePlains_toAdmin (v : Val) (l : List Admin) :
    ∀ i ∈ codePlains (v.toAdmin :: l), IsConst i ∨ i ∈ codePlains l := by
  intro i hi
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;>
    simp only [Val.toAdmin, codePlains_plain, codePlains_ref, List.mem_cons] at hi <;>
    first
      | (rcases hi with rfl | hi
         · exact .inl (by first
             | exact .inl ⟨_, _, rfl⟩
             | exact .inr (.inl ⟨_, _, rfl⟩)
             | exact .inr (.inr ⟨_, rfl⟩))
         · exact .inr hi)
      | exact .inr hi

theorem codePlains_vals (vs : List Val) : ∀ i ∈ codePlains (vals vs), IsConst i := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih =>
    intro i hi
    rcases codePlains_toAdmin v (vals vs) i hi with h | h
    · exact h
    · exact ih i h

theorem codePlains_constI32 (b : BitVec 32) (l : List Admin) :
    codePlains (constI32 b :: l) = .intConst .i32 b :: codePlains l := by
  simp [constI32, Val.i32, Val.toAdmin]

/-! ## Instructions -/

theorem IsConst.callees {i : Instr} (h : IsConst i) : instrCallees i = [] := by
  rcases h with ⟨t, b, rfl⟩ | ⟨t, b, rfl⟩ | ⟨b, rfl⟩ <;> rfl

theorem InstrIn.of_callees {i : Instr} (h : instrCallees i = []) : InstrIn G fs i := by
  intro x hx
  simp [h] at hx

theorem InstrIn.of_const {i : Instr} (h : IsConst i) : InstrIn G fs i :=
  InstrIn.of_callees h.callees

theorem mem_exprCallees {b : List Instr} {i : Instr} (hi : i ∈ b) {x : Nat}
    (hx : x ∈ instrCallees i) : x ∈ exprCallees b := by
  induction b with
  | nil => cases hi
  | cons j b ih =>
    rw [exprCallees, List.mem_append]
    rcases List.mem_cons.1 hi with rfl | hi
    · exact .inl hx
    · exact .inr (ih hi)

theorem InstrIn.of_expr {b : List Instr} (h : ∀ x ∈ exprCallees b, ∀ a, fs[x]? = some a → G a) :
    ∀ i ∈ b, InstrIn G fs i :=
  fun _ hi x hx => h x (mem_exprCallees hi hx)

theorem InstrIn.block {bt : BlockType} {b : List Instr} (h : InstrIn G fs (.block bt b)) :
    ∀ i ∈ b, InstrIn G fs i :=
  InstrIn.of_expr (by simpa [InstrIn, instrCallees] using h)

theorem InstrIn.loop {bt : BlockType} {b : List Instr} (h : InstrIn G fs (.loop bt b)) :
    ∀ i ∈ b, InstrIn G fs i :=
  InstrIn.of_expr (by simpa [InstrIn, instrCallees] using h)

theorem InstrIn.tryTable {bt : BlockType} {cs : List Catch} {b : List Instr}
    (h : InstrIn G fs (.tryTable bt cs b)) : ∀ i ∈ b, InstrIn G fs i :=
  InstrIn.of_expr (by simpa [InstrIn, instrCallees] using h)

theorem InstrIn.if_left {bt : BlockType} {b₁ b₂ : List Instr} (h : InstrIn G fs (.if_ bt b₁ b₂)) :
    InstrIn G fs (.block bt b₁) := by
  intro x hx a ha
  exact h x (by simp only [instrCallees, List.mem_append] at hx ⊢; exact .inl hx) a ha

theorem InstrIn.if_right {bt : BlockType} {b₁ b₂ : List Instr}
    (h : InstrIn G fs (.if_ bt b₁ b₂)) : InstrIn G fs (.block bt b₂) := by
  intro x hx a ha
  exact h x (by simp only [instrCallees, List.mem_append] at hx ⊢; exact .inr hx) a ha

/-! ## References -/

theorem RefIn.of_funcs_nil {r : Ref} (h : refFuncs r = []) : RefIn G r := by
  intro a ha
  simp [h] at ha

@[simp] theorem refIn_null : RefIn G .null := RefIn.of_funcs_nil rfl
@[simp] theorem refIn_i31 (b : BitVec 31) : RefIn G (.i31 b) := RefIn.of_funcs_nil rfl
@[simp] theorem refIn_struct (a : Nat) : RefIn G (.struct a) := RefIn.of_funcs_nil rfl
@[simp] theorem refIn_array (a : Nat) : RefIn G (.array a) := RefIn.of_funcs_nil rfl
@[simp] theorem refIn_exn (a : Nat) : RefIn G (.exn a) := RefIn.of_funcs_nil rfl
@[simp] theorem refIn_host (a : Nat) : RefIn G (.host a) := RefIn.of_funcs_nil rfl
@[simp] theorem refIn_extern (r : Ref) : RefIn G (.extern r) ↔ RefIn G r := Iff.rfl
@[simp] theorem refIn_func (a : Nat) : RefIn G (.func a) ↔ G a := by simp [RefIn, refFuncs]

/-! ## The code invariant from inclusions -/

/-- Rebuild `CodeIn` from inclusions of references, frames and source instructions. -/
theorem CodeIn.sub {code code' : List Admin} (h : CodeIn G fs Pl code)
    (hr : ∀ r ∈ codeRefs code', r ∈ codeRefs code ∨ RefIn G r)
    (hf : ∀ fr ∈ codeFrames code', fr ∈ codeFrames code ∨ FrameIn G fs fr)
    (hp : ∀ i ∈ codePlains code', i ∈ codePlains code ∨ PlOK Pl i) : CodeIn G fs Pl code' :=
  ⟨fun r hr' => (hr r hr').elim (h.1 r) id, fun fr hf' => (hf fr hf').elim (h.2.1 fr) id,
    fun i hp' => (hp i hp').elim (h.2.2 i) id⟩

theorem CodeIn.append {l₁ l₂ : List Admin} :
    CodeIn G fs Pl (l₁ ++ l₂) ↔ CodeIn G fs Pl l₁ ∧ CodeIn G fs Pl l₂ := by
  simp only [CodeIn, codeRefs_append, codeFrames_append, codePlains_append, List.mem_append]
  constructor
  · intro h
    exact ⟨⟨fun r hr => h.1 r (.inl hr), fun f hf => h.2.1 f (.inl hf),
        fun i hi => h.2.2 i (.inl hi)⟩,
      ⟨fun r hr => h.1 r (.inr hr), fun f hf => h.2.1 f (.inr hf), fun i hi => h.2.2 i (.inr hi)⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun r hr => hr.elim (h₁.1 r) (h₂.1 r), fun f hf => hf.elim (h₁.2.1 f) (h₂.2.1 f),
      fun i hi => hi.elim (h₁.2.2 i) (h₂.2.2 i)⟩

/-- The code of values whose references are in `G`. -/
theorem CodeIn.ofVals {vs : List Val} (h : ∀ r, Val.ref r ∈ vs → RefIn G r) :
    CodeIn G fs Pl (vals vs) := by
  refine ⟨fun r hr => h r (by simpa using hr), fun fr hf => by simp at hf,
    fun i hi => .inl (codePlains_vals vs i hi).callees⟩

/-! ## Reachability: the instruction predicate `InstrIn` -/

/-- `InstrIn G fs` meets the requirements of the invariant, with no guarded calls. -/
theorem instrIn_plainOK : PlainOK G (fun _ => False) fs (InstrIn G fs) where
  block _ _ h i hi := .inr (InstrIn.block h i hi)
  loop _ _ h i hi := .inr (InstrIn.loop h i hi)
  tryTable _ _ _ h i hi := .inr (InstrIn.tryTable h i hi)
  ifLeft _ _ _ h := .inr (InstrIn.if_left h)
  ifRight _ _ _ h := .inr (InstrIn.if_right h)
  call _ a h ha := .inl (h _ (by simp [instrCallees]) a ha)
  returnCall _ a h ha := h _ (by simp [instrCallees]) a ha
  refFunc _ a h ha := h _ (by simp [instrCallees]) a ha

theorem PlOK.instrIn {i : Instr} (h : PlOK (InstrIn G fs) i) : InstrIn G fs i :=
  h.elim InstrIn.of_callees id

end Silmaril.Wasm.Verify
