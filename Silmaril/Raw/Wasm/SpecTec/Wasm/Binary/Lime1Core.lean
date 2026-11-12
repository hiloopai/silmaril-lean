module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Lime1Core.Leaf
-- Hand copy: source namespaces kept, only import lines rewritten.
-- Split from the copied `Lime1Core.lean` for build time (Silmaril change): source declarations
-- unchanged; the non-nesting cases of `core_instr_aux` are proved in `Lime1Core/Leaf.lean`.

/-! # Lime1 and Core 3.0 agree on instruction encodings

The instruction-level agreement between the Lime1 grammar (`Lime1.Binary.Instr ov`)
and the Core 3.0 grammar restricted to the matching forms
(`Core.Instr (Core.Forms.ofOverlong ov)`), along `Lime1.Instr.toCore`:

* every Lime1 opcode is one Core opcode-table entry (`PlainOp`, `PrefixFCOp`, `MemOp`
  have the same constructor names on both sides);
* a Lime1 `memarg` with alignment exponent `< 2^6` is Core's `Memarg` rule `mem0`
  with a `u32` offset (`instrAligns` is the compatibility premise; the converse needs
  none, since Core rejects larger exponents and the restricted forms disable the
  memory-index and 64-bit-offset rules);
* `call_indirect`'s table operand `TableIdxZero ov` is Core's
  `ReservedIdx (Forms.ofOverlong ov .tableIdxImm)` at table `0`: the literal byte is
  rule `zero`, an overlong zero (only with `ov = true`) is rule `idx`;
* the reserved bytes of `memory.size/grow/copy/fill` are `ReservedIdx false`'s `zero`.

`instrAligns`/`exprAligns` are definitionally `Lime1.Instr.alignsBelow64`/
`Lime1.Expr.alignsBelow64` of `Binary/Agreement.lean`, which imports this file.
-/

@[expose] public section

open Silmaril.Wasm.Binary

namespace Silmaril.Wasm.Binary.Lime1Core

open Lime1.Binary (TableIdxZero TableZero ZeroPayload)

/-! ## Instructions: Lime1 to Core -/

mutual
theorem instr_core_aux {ov : Bool} : ∀ {b : Bytes} {i : Lime1.Instr},
    Lime1.Binary.Instr ov b i → instrAligns i = true →
    Core.Instr (Core.Forms.ofOverlong ov) b i.toCore := by
  intro b i h ha
  cases h with
  | plain h => exact .plain (plainOp_core h)
  | prefixFC h hn => exact .prefixFC (prefixFCOp_core h) hn
  | block ht hb =>
    exact .block (blockType_core ht) (instrs_core_aux hb (by simpa [instrAligns] using ha))
  | loop ht hb =>
    exact .loop (blockType_core ht) (instrs_core_aux hb (by simpa [instrAligns] using ha))
  | if_ ht hb =>
    exact .if_ (blockType_core ht) (instrs_core_aux hb (by simpa [instrAligns, exprAligns] using ha))
  | ifElse ht h₁ h₂ =>
    simp only [instrAligns, Bool.and_eq_true] at ha
    exact .ifElse (blockType_core ht) (instrs_core_aux h₁ ha.1) (instrs_core_aux h₂ ha.2)
  | br h => exact .br h
  | brIf h => exact .brIf h
  | brTable h h' => exact .brTable h h'
  | call h => exact .call h
  | callIndirect h hz => exact .callIndirect h (tableIdxZero_core hz)
  | localGet h => exact .localGet h
  | localSet h => exact .localSet h
  | localTee h => exact .localTee h
  | globalGet h => exact .globalGet h
  | globalSet h => exact .globalSet h
  | mem h hm => exact mem_core h hm ha
  | memorySize => exact .memorySize .zero
  | memoryGrow => exact .memoryGrow .zero
  | memoryCopy hn =>
    have := Core.Instr.memoryCopy (F := Core.Forms.ofOverlong ov) hn .zero .zero
    simpa [Lime1.Instr.toCore] using this
  | memoryFill hn => exact .memoryFill hn .zero
  | i32Const h => exact .i32Const h
  | i64Const h => exact .i64Const h
  | f32Const h => exact .f32Const h
  | f64Const h => exact .f64Const h

theorem instrs_core_aux {ov : Bool} : ∀ {b : Bytes} {is : List Lime1.Instr},
    Lime1.Binary.Instrs ov b is → exprAligns is = true →
    Core.Instrs (Core.Forms.ofOverlong ov) b (Lime1.Expr.toCore is) := by
  intro b is h ha
  cases h with
  | nil => exact .nil
  | cons h hs =>
    simp only [exprAligns, Bool.and_eq_true] at ha
    exact .cons (instr_core_aux h ha.1) (instrs_core_aux hs ha.2)
end

/-! ## Instructions: Core to Lime1 -/

mutual
theorem core_instr_aux {ov : Bool} : ∀ {b : Bytes} {ci : Wasm.Instr},
    Core.Instr (Core.Forms.ofOverlong ov) b ci → ∀ {i : Lime1.Instr}, ci = i.toCore →
    Lime1.Binary.Instr ov b i := by
  intro b ci h i hc
  cases hnest : coreNested ci
  · exact core_instr_leaf h hnest hc
  cases h with
  | block ht hb =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    obtain ⟨rfl, hb'⟩ := hc
    exact .block (blockType_lime1 ht) (core_instrs_aux hb hb')
  | loop ht hb =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    obtain ⟨rfl, hb'⟩ := hc
    exact .loop (blockType_lime1 ht) (core_instrs_aux hb hb')
  | if_ ht hb =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    obtain ⟨rfl, hb', he⟩ := hc
    rename_i right
    have : right = [] := by
      cases right with
      | nil => rfl
      | cons _ _ => simp [Lime1.Expr.toCore] at he
    subst this
    exact .if_ (blockType_lime1 ht) (core_instrs_aux hb hb')
  | ifElse ht h₁ h₂ =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    obtain ⟨rfl, hb₁, hb₂⟩ := hc
    exact .ifElse (blockType_lime1 ht) (core_instrs_aux h₁ hb₁) (core_instrs_aux h₂ hb₂)
  | plain h => simp [plainOp_coreNested h] at hnest
  | prefixFB h _ => simp [prefixFBOp_coreNested h] at hnest
  | prefixFC h _ => simp [prefixFCOp_coreNested h] at hnest
  | prefixFD h _ => simp [prefixFDOp_coreNested h] at hnest
  | mem h _ => simp [memOp_coreNested h] at hnest
  | vecMem h _ _ => simp [vecMemOp_coreNested h] at hnest
  | vecMemLane h _ _ => simp [vecMemLaneOp_coreNested h] at hnest
  | vecLane h _ => simp [vecLaneOp_coreNested h] at hnest
  | _ => simp [coreNested] at hnest

theorem core_instrs_aux {ov : Bool} : ∀ {b : Bytes} {cs : List Wasm.Instr},
    Core.Instrs (Core.Forms.ofOverlong ov) b cs → ∀ {is : List Lime1.Instr},
    cs = Lime1.Expr.toCore is → Lime1.Binary.Instrs ov b is := by
  intro b cs h is hc
  cases h with
  | nil =>
    cases is with
    | nil => exact .nil
    | cons _ _ => simp [Lime1.Expr.toCore] at hc
  | cons h hs =>
    cases is with
    | nil => simp [Lime1.Expr.toCore] at hc
    | cons i is =>
      simp only [Lime1.Expr.toCore, List.cons.injEq] at hc
      exact .cons (core_instr_aux h hc.1) (core_instrs_aux hs hc.2)
end

/-! ## Agreement -/

theorem instr_core {ov : Bool} {b : Bytes} {i : Lime1.Instr} (h : Lime1.Binary.Instr ov b i)
    (ha : instrAligns i = true) : Core.Instr (Core.Forms.ofOverlong ov) b i.toCore :=
  instr_core_aux h ha

/-- No compatibility premise: the restricted Core grammar rejects alignments `≥ 2^6`. -/
theorem core_instr {ov : Bool} {b : Bytes} {i : Lime1.Instr}
    (h : Core.Instr (Core.Forms.ofOverlong ov) b i.toCore) : Lime1.Binary.Instr ov b i :=
  core_instr_aux h rfl

theorem expr_core {ov : Bool} {b : Bytes} {e : Lime1.Expr} (h : Lime1.Binary.Expr ov b e)
    (ha : exprAligns e = true) : Core.Expr (Core.Forms.ofOverlong ov) b (Lime1.Expr.toCore e) := by
  cases h with
  | mk h => exact .mk (instrs_core_aux h ha)

theorem core_expr {ov : Bool} {b : Bytes} {e : Lime1.Expr}
    (h : Core.Expr (Core.Forms.ofOverlong ov) b (Lime1.Expr.toCore e)) :
    Lime1.Binary.Expr ov b e := by
  cases h with
  | mk h => exact .mk (core_instrs_aux h rfl)

end Silmaril.Wasm.Binary.Lime1Core
