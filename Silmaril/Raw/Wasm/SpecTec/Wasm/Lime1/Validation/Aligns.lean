module

public import Silmaril.Wasm.Lime1.Validation.Instructions
public import Silmaril.Wasm.Lime1.Validation.Modules
-- Hand copy (track ws4-p1-lime-wasmi): source namespaces kept, only import lines rewritten.

/-! # Memory arguments of valid Lime1 code

`Instr.memargs` / `Expr.memargs` collect every `MemArg` immediate of an instruction
(sequence), recursing into structured-control bodies. Validation bounds every
alignment exponent by `3` (the access width is at most 64 bits), so all of them lie
below `2^6`. Valid modules also use only table and memory index `0` in their
element and data segments.

`Lime1.Validation.ModuleValid.binaryCompat` (in `Binary/Agreement.lean`) follows from
`ModuleValid.funcs_memargs`, `globals_memargs`, `elems_memargs`, `data_memargs`,
`elem_table_zero` and `data_memory_zero`, together with
`Expr.alignsBelow64 e = true ↔ ∀ a ∈ e.memargs, a.align.val < 2^6`.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1

mutual
/-- The memory-argument immediates of an instruction, including nested bodies. -/
def Instr.memargs : Instr → List MemArg
  | .block _ body | .loop _ body => Expr.memargs body
  | .if_ _ left right => Expr.memargs left ++ Expr.memargs right
  | .intLoad _ _ a | .floatLoad _ a | .intStore _ _ a | .floatStore _ a => [a]
  | _ => []

/-- The memory-argument immediates of an instruction sequence. -/
def Expr.memargs : Expr → List MemArg
  | [] => []
  | i :: is => Instr.memargs i ++ Expr.memargs is
end

@[simp] theorem Expr.memargs_nil : Expr.memargs [] = [] := by
  simp [Expr.memargs]

@[simp] theorem Expr.memargs_cons (i : Instr) (is : Expr) :
    Expr.memargs (i :: is) = Instr.memargs i ++ Expr.memargs is := by
  simp [Expr.memargs]

theorem Expr.memargs_append (is js : Expr) :
    Expr.memargs (is ++ js) = Expr.memargs is ++ Expr.memargs js := by
  induction is with
  | nil => simp
  | cons i is ih => simp [ih]

theorem Expr.mem_memargs {e : Expr} {a : MemArg} :
    a ∈ Expr.memargs e ↔ ∃ i ∈ e, a ∈ Instr.memargs i := by
  induction e with
  | nil => simp
  | cons i is ih => simp [ih]

namespace Validation

/-- An aligned access of width at most 64 bits has alignment exponent at most 3. -/
theorem Aligned.align_lt {arg : MemArg} {w : Nat} (h : Aligned arg w) (hw : w ≤ 64) :
    arg.align.val < 2 ^ 6 := by
  unfold Aligned at h
  by_contra hc
  have h6 : 2 ^ 6 ≤ 2 ^ arg.align.val := Nat.pow_le_pow_right (by decide) (by omega)
  have : w / 8 ≤ 8 := by omega
  omega

theorem IntAccess.align_lt {t : IntType} {p : Option PackSize} {arg : MemArg}
    (h : IntAccess t p arg) : arg.align.val < 2 ^ 6 := by
  have ht : t.width ≤ 64 := by cases t <;> decide
  cases p with
  | none => exact Aligned.align_lt h ht
  | some p => exact Aligned.align_lt h.2 (by have := h.1; omega)

theorem FloatType.width_le (t : FloatType) : t.width ≤ 64 := by cases t <;> decide

mutual
/-- Every memory argument of a valid instruction has alignment exponent below `2^6`. -/
theorem InstrType.memargs_align {C : Context} {i : Instr} {a b : ResultType}
    (h : InstrType C i a b) : ∀ x ∈ Instr.memargs i, x.align.val < 2 ^ 6 := by
  match h with
  | .frame _ h => exact InstrType.memargs_align h
  | .block _ _ hb => simpa [Instr.memargs] using ExprType.memargs_align hb
  | .loop _ _ hb => simpa [Instr.memargs] using ExprType.memargs_align hb
  | .if_ _ _ hl hr =>
    intro x hx
    simp only [Instr.memargs, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ExprType.memargs_align hl x hx
    · exact ExprType.memargs_align hr x hx
  | .intLoad _ _ _ _ access => simpa [Instr.memargs] using IntAccess.align_lt access
  | .floatLoad t _ _ aligned =>
    simpa [Instr.memargs] using Aligned.align_lt aligned (FloatType.width_le t)
  | .intStore _ _ _ _ access => simpa [Instr.memargs] using IntAccess.align_lt access
  | .floatStore t _ _ aligned =>
    simpa [Instr.memargs] using Aligned.align_lt aligned (FloatType.width_le t)
  | .nop | .unreachable .. | .drop .. | .select .. | .br .. | .brIf .. | .brTable ..
  | .return_ .. | .call .. | .callIndirect .. | .localGet .. | .localSet .. | .localTee ..
  | .globalGet .. | .globalSet .. | .memorySize .. | .memoryGrow .. | .memoryFill ..
  | .memoryCopy .. | .intConst .. | .floatConst .. | .intUnOp .. | .intBinOp ..
  | .intTestOp .. | .intRelOp .. | .floatUnOp .. | .floatBinOp .. | .floatRelOp ..
  | .convert .. => simp [Instr.memargs]

/-- Every memory argument of a valid expression has alignment exponent below `2^6`. -/
theorem ExprType.memargs_align {C : Context} {e : Expr} {a b : ResultType}
    (h : ExprType C e a b) : ∀ x ∈ Expr.memargs e, x.align.val < 2 ^ 6 := by
  match h with
  | .nil _ => simp
  | .cons hi his =>
    intro x hx
    simp only [Expr.memargs_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact InstrType.memargs_align hi x hx
    · exact ExprType.memargs_align his x hx
end

theorem ConstantInstr.memargs_eq_nil {C : Context} {i : Instr} (h : ConstantInstr C i) :
    Instr.memargs i = [] := by
  cases h <;> simp [Instr.memargs]

theorem ConstantExpr.memargs_eq_nil {C : Context} {e : Expr} (h : ConstantExpr C e) :
    Expr.memargs e = [] := by
  induction e with
  | nil => simp
  | cons i is ih =>
    simp only [Expr.memargs_cons, List.append_eq_nil_iff]
    exact ⟨(h i (by simp)).memargs_eq_nil, ih fun j hj => h j (by simp [hj])⟩

theorem ConstExprType.memargs_eq_nil {C : Context} {e : Expr} {t : ValType}
    (h : ConstExprType C e t) : Expr.memargs e = [] :=
  h.constant.memargs_eq_nil

theorem ConstExprType.memargs_align {C : Context} {e : Expr} {t : ValType}
    (h : ConstExprType C e t) : ∀ x ∈ Expr.memargs e, x.align.val < 2 ^ 6 := by
  simp [h.memargs_eq_nil]

namespace ModuleValid

variable {m : Module}

theorem funcs_memargs (h : ModuleValid m) :
    ∀ f ∈ m.funcs, ∀ x ∈ Expr.memargs f.body, x.align.val < 2 ^ 6 := by
  intro f hf
  obtain ⟨_, _, _, hb⟩ := h.functions f hf
  exact ExprType.memargs_align hb

theorem globals_memargs (h : ModuleValid m) :
    ∀ g ∈ m.globals, ∀ x ∈ Expr.memargs g.init, x.align.val < 2 ^ 6 :=
  fun g hg => ConstExprType.memargs_align (h.globals g hg)

theorem elems_memargs (h : ModuleValid m) :
    ∀ e ∈ m.elems, ∀ x ∈ Expr.memargs e.offset, x.align.val < 2 ^ 6 :=
  fun e he => (h.elements e he).offset.memargs_align

theorem data_memargs (h : ModuleValid m) :
    ∀ d ∈ m.data, ∀ x ∈ Expr.memargs d.offset, x.align.val < 2 ^ 6 :=
  fun d hd => (h.data d hd).offset.memargs_align

/-- An index that resolves in a list of length at most one is index `0`. -/
private theorem idx_eq_zero_of_lookup {kind : IndexKind} {α : Type} {l : List α}
    {i : Idx kind} (hl : l.length ≤ 1) (h : ∃ x, l[i.toNat]? = some x) : i = ⟨0⟩ := by
  obtain ⟨x, hx⟩ := h
  have hlt := (List.getElem?_eq_some_iff.mp hx).1
  apply Idx.toNat_injective
  simp only [Idx.toNat] at hlt ⊢
  simp only [Fin.val_zero]
  omega

theorem elem_table_zero (h : ModuleValid m) : ∀ e ∈ m.elems, e.table = ⟨0⟩ :=
  fun e he => idx_eq_zero_of_lookup h.singleTable (h.elements e he).table

theorem data_memory_zero (h : ModuleValid m) : ∀ d ∈ m.data, d.memory = ⟨0⟩ :=
  fun d hd => idx_eq_zero_of_lookup h.singleMemory (h.data d hd).memory

end ModuleValid

end Validation

end Silmaril.Wasm.Lime1
