module

public import Silmaril.Wasm.Text.Core.FunctionalTypes

/-!
# Core 3.0 text format: functionality of instructions

* **Keywords.**  The keyword of every instruction (`nullaryName` and the
  keywords of the instructions with immediates) is a lower-case word that is
  not one of the reserved words of the grammar (`end`, `then`, `param`,
  `funcref`, …), not a numeral and not a memory-argument token
  (`nullaryName_goodB`, by evaluation).
* **Item classes.**  The items following an instruction keyword are
  *operands* (`Operand`: anything that can neither start an instruction nor be
  `end`/`else`), and every instruction sequence starts with an instruction
  keyword (`IsStart`).  Hence the items spanned by one instruction are
  determined by the item stream (`instrs_prefix`, `blockInstr_prefix`), with
  no reference to the identifier context.
* **Functionality.**  For a fixed context with distinct names, the reading of
  an instruction, an instruction sequence, a folded instruction and a block
  instruction is unique (`plain_functional'`, `instrs_functional'`).  The
  implicitly used function types only depend on the type names
  (`instrs_uses`), which is what the module-level fixpoint needs.
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Core

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Formats.SExpEncoding.Wat Silmaril.Wasm

/-! ## Keywords -/

/-- Keywords of the plain instructions with immediates. -/
def explicitKws0 : List String :=
  ["select", "br", "br_if", "br_table", "br_on_null", "br_on_non_null", "br_on_cast",
    "br_on_cast_fail", "call", "call_ref", "call_indirect", "return_call", "return_call_ref",
    "return_call_indirect", "throw", "local.get", "local.set", "local.tee", "global.get",
    "global.set", "table.get", "table.set", "table.size", "table.grow", "table.fill",
    "table.copy", "table.init", "elem.drop", "memory.size", "memory.grow", "memory.fill",
    "memory.copy", "memory.init", "data.drop", "ref.null", "ref.func", "ref.test", "ref.cast",
    "struct.new", "struct.new_default", "struct.get", "struct.get_s", "struct.get_u",
    "struct.set", "array.new", "array.new_default", "array.new_fixed", "array.new_data",
    "array.new_elem", "array.get", "array.get_s", "array.get_u", "array.set", "array.fill",
    "array.copy", "array.init_data", "array.init_elem", "i32.const", "i64.const", "f32.const",
    "f64.const", "v128.const", "i8x16.shuffle"]

def explicitKws : List String :=
  explicitKws0 ++ memOps.map (·.1) ++ laneMemOps.map (·.1) ++ laneOps.map (·.1)

/-- Keywords of block instructions. -/
def blockKws : List String := ["block", "loop", "if", "try_table"]

/-- Words of the grammar that are not instruction keywords. -/
def reservedKws : List String :=
  ["end", "else", "then", "type", "param", "result", "local", "item", "offset", "catch",
    "catch_ref", "catch_all", "catch_all_ref", "ref", "null", "mut", "export", "import", "elem",
    "data", "memory", "table", "func", "declare", "field", "sub", "final", "rec", "struct",
    "array", "inf", "nan", "module", "start", "tag", "global", "i8", "i16", "v128", "i8x16",
    "i16x8", "i32x4", "i64x2", "f32x4", "f64x2"] ++ numKws ++ heapKws ++ refAbbrevKws

/-- Starts with a lower-case letter. -/
def lowerB (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => decide ('a' ≤ c ∧ c ≤ 'z')

/-- A word starting with a lower-case letter. -/
def LowerKw (s : String) : Prop := lowerB s = true

instance (s : String) : Decidable (LowerKw s) := by unfold LowerKw; infer_instance

/-- `p` is a prefix of `s`. -/
def HasPre (p s : String) : Prop := p.toList.isPrefixOf s.toList = true

instance (p s : String) : Decidable (HasPre p s) := by unfold HasPre; infer_instance

theorem hasPre_of_eq {p s : String} {r : List Char} (e : s.toList = p.toList ++ r) : HasPre p s := by
  unfold HasPre; rw [e, List.isPrefixOf_iff_prefix]; exact ⟨r, rfl⟩

/-- The conditions satisfied by every instruction keyword. -/
def KwOk (s : String) : Prop :=
  s ∉ reservedKws ∧ LowerKw s ∧ ¬ HasPre "nan:" s ∧ ¬ HasPre "offset=" s ∧ ¬ HasPre "align=" s

instance (s : String) : Decidable (KwOk s) := by unfold KwOk; infer_instance

/-- The keyword of a nullary instruction: an instruction keyword distinct from
the keywords of the other instructions. -/
def goodKwB (s : String) : Bool :=
  decide (s ∉ explicitKws ∧ s ∉ blockKws ∧ KwOk s)

section nullary
/-! Evaluation of `nullaryName`, family by family. -/

theorem repr8 : Nat.repr 8 = "8" := by
  apply String.toList_injective
  rw [Nat.toList_repr, Nat.toDigits_of_lt_base (by decide)]
  have e : "8".toList = ['8'] := by decide
  rw [e]; simp

theorem repr16 : Nat.repr 16 = "16" := by
  apply String.toList_injective
  rw [Nat.toList_repr, Nat.toDigits_of_base_le (by decide) (by decide),
    Nat.toDigits_of_lt_base (by decide)]
  have e : "16".toList = ['1', '6'] := by decide
  rw [e]; simp

theorem repr32 : Nat.repr 32 = "32" := by
  apply String.toList_injective
  rw [Nat.toList_repr, Nat.toDigits_of_base_le (by decide) (by decide),
    Nat.toDigits_of_lt_base (by decide)]
  have e : "32".toList = ['3', '2'] := by decide
  rw [e]; simp

theorem good_intUnOp (t : IntType) (op : IntUnOp) :
    (nullaryName (.intUnOp t op)).all goodKwB = true := by
  cases t <;> cases op <;> (try (rename_i p; cases p)) <;>
    simp only [nullaryName, intUnName, PackSize.width, IntType.width, Nat.toString_eq_repr, repr8,
      repr16, repr32] <;> decide

theorem good_intBinOp (t : IntType) (op : IntBinOp) :
    (nullaryName (.intBinOp t op)).all goodKwB = true := by
  cases t <;> cases op <;> (try (rename_i p; cases p)) <;> decide

theorem good_intTestOp (t : IntType) (op : IntTestOp) :
    (nullaryName (.intTestOp t op)).all goodKwB = true := by
  cases t <;> cases op <;> decide

theorem good_intRelOp (t : IntType) (op : IntRelOp) :
    (nullaryName (.intRelOp t op)).all goodKwB = true := by
  cases t <;> cases op <;> (try (rename_i p; cases p)) <;> decide

theorem good_floatUnOp (t : FloatType) (op : FloatUnOp) :
    (nullaryName (.floatUnOp t op)).all goodKwB = true := by
  cases t <;> cases op <;> decide

theorem good_floatBinOp (t : FloatType) (op : FloatBinOp) :
    (nullaryName (.floatBinOp t op)).all goodKwB = true := by
  cases t <;> cases op <;> decide

theorem good_floatRelOp (t : FloatType) (op : FloatRelOp) :
    (nullaryName (.floatRelOp t op)).all goodKwB = true := by
  cases t <;> cases op <;> decide

theorem good_convert (op : ConvertOp) : (nullaryName (.convert op)).all goodKwB = true := by
  cases op <;> (try (rename_i a b c; cases a <;> cases b <;> cases c)) <;>
    (try (rename_i a; cases a)) <;> decide

theorem good_vecIntUnOp (sh : IntShape) (op : VecIntUnOp) :
    (nullaryName (.vecIntUnOp sh op)).all goodKwB = true := by
  cases sh <;> cases op <;> decide

theorem good_vecFloatUnOp (sh : FloatShape) (op : FloatUnOp) :
    (nullaryName (.vecFloatUnOp sh op)).all goodKwB = true := by
  cases sh <;> cases op <;> decide

theorem good_vecIntBinOp (sh : IntShape) (op : VecIntBinOp) :
    (nullaryName (.vecIntBinOp sh op)).all goodKwB = true := by
  cases sh <;> cases op <;> (try (rename_i p; cases p)) <;> decide

theorem good_vecFloatBinOp (sh : FloatShape) (op : VecFloatBinOp) :
    (nullaryName (.vecFloatBinOp sh op)).all goodKwB = true := by
  cases sh <;> cases op <;> decide

theorem good_vecIntRelOp (sh : IntShape) (op : IntRelOp) :
    (nullaryName (.vecIntRelOp sh op)).all goodKwB = true := by
  cases sh <;> cases op <;> (try (rename_i p; cases p)) <;> decide

theorem good_vecFloatRelOp (sh : FloatShape) (op : FloatRelOp) :
    (nullaryName (.vecFloatRelOp sh op)).all goodKwB = true := by
  cases sh <;> cases op <;> decide

theorem good_vecShiftOp (sh : IntShape) (op : VecShiftOp) :
    (nullaryName (.vecShiftOp sh op)).all goodKwB = true := by
  cases sh <;> cases op <;> (try (rename_i p; cases p)) <;> decide

theorem good_vecExtUnOp (src dst : IntShape) (op : VecExtUnOp) :
    (nullaryName (.vecExtUnOp src dst op)).all goodKwB = true := by
  cases src <;> cases dst <;> cases op <;> (rename_i p; cases p) <;> decide

theorem good_vecExtBinOp (src dst : IntShape) (op : VecExtBinOp) :
    (nullaryName (.vecExtBinOp src dst op)).all goodKwB = true := by
  cases src <;> cases dst <;> cases op <;> (try (rename_i a b; cases a <;> cases b)) <;> decide

theorem good_vecExtTernOp (src dst : IntShape) (op : VecExtTernOp) :
    (nullaryName (.vecExtTernOp src dst op)).all goodKwB = true := by
  cases src <;> cases dst <;> cases op <;> decide

theorem good_vecNarrow (src dst : IntShape) (s : Signedness) :
    (nullaryName (.vecNarrow src dst s)).all goodKwB = true := by
  cases src <;> cases dst <;> cases s <;> decide

theorem good_vecConvert_extend (src dst : Shape) (h : Half) (s : Signedness) :
    (nullaryName (.vecConvert src dst (.extend h s))).all goodKwB = true := by
  rcases src with s' | s' <;> cases s' <;> rcases dst with d | d <;> cases d <;> cases h <;>
    cases s <;> decide

theorem good_vecConvert_convert (src dst : Shape) (h : Option Half) (s : Signedness) :
    (nullaryName (.vecConvert src dst (.convert h s))).all goodKwB = true := by
  rcases src with s' | s' <;> cases s' <;> rcases dst with d | d <;> cases d <;>
    rcases h with _ | h <;> (try cases h) <;> cases s <;> decide

theorem good_vecConvert_truncSat (src dst : Shape) (s : Signedness) (z : Bool) :
    (nullaryName (.vecConvert src dst (.truncSat s z))).all goodKwB = true := by
  rcases src with s' | s' <;> cases s' <;> rcases dst with d | d <;> cases d <;> cases s <;>
    cases z <;> decide

theorem good_vecConvert_relaxedTrunc (src dst : Shape) (s : Signedness) (z : Bool) :
    (nullaryName (.vecConvert src dst (.relaxedTrunc s z))).all goodKwB = true := by
  rcases src with s' | s' <;> cases s' <;> rcases dst with d | d <;> cases d <;> cases s <;>
    cases z <;> decide

theorem good_vecConvert_other (src dst : Shape) :
    (nullaryName (.vecConvert src dst .demoteZero)).all goodKwB = true ∧
      (nullaryName (.vecConvert src dst .promoteLow)).all goodKwB = true := by
  rcases src with s' | s' <;> cases s' <;> rcases dst with d | d <;> cases d <;>
    exact ⟨by decide, by decide⟩

theorem good_vecConvert (src dst : Shape) (op : VecConvertOp) :
    (nullaryName (.vecConvert src dst op)).all goodKwB = true := by
  cases op with
  | extend h s => exact good_vecConvert_extend src dst h s
  | convert h s => exact good_vecConvert_convert src dst h s
  | truncSat s z => exact good_vecConvert_truncSat src dst s z
  | relaxedTrunc s z => exact good_vecConvert_relaxedTrunc src dst s z
  | demoteZero => exact (good_vecConvert_other src dst).1
  | promoteLow => exact (good_vecConvert_other src dst).2

/-- Every keyword computed by `nullaryName` is good (by evaluation). -/
theorem nullaryName_goodB (i : Instr) : (nullaryName i).all goodKwB = true := by
  cases i with
  | intUnOp t op => exact good_intUnOp t op
  | intBinOp t op => exact good_intBinOp t op
  | intTestOp t op => exact good_intTestOp t op
  | intRelOp t op => exact good_intRelOp t op
  | floatUnOp t op => exact good_floatUnOp t op
  | floatBinOp t op => exact good_floatBinOp t op
  | floatRelOp t op => exact good_floatRelOp t op
  | convert op => exact good_convert op
  | i31Get s => cases s <;> decide
  | vecUnOp op => cases op; decide
  | vecBinOp op => cases op <;> decide
  | vecTernOp op => cases op; decide
  | vecTestOp op => cases op; decide
  | vecIntUnOp sh op => exact good_vecIntUnOp sh op
  | vecFloatUnOp sh op => exact good_vecFloatUnOp sh op
  | vecIntBinOp sh op => exact good_vecIntBinOp sh op
  | vecFloatBinOp sh op => exact good_vecFloatBinOp sh op
  | vecIntTernOp sh op => cases sh <;> cases op <;> decide
  | vecFloatTernOp sh op => cases sh <;> cases op <;> decide
  | vecAllTrue sh => cases sh <;> decide
  | vecIntRelOp sh op => exact good_vecIntRelOp sh op
  | vecFloatRelOp sh op => exact good_vecFloatRelOp sh op
  | vecShiftOp sh op => exact good_vecShiftOp sh op
  | vecBitmask sh => cases sh <;> decide
  | vecSwizzle op => cases op <;> decide
  | vecExtUnOp src dst op => exact good_vecExtUnOp src dst op
  | vecExtBinOp src dst op => exact good_vecExtBinOp src dst op
  | vecExtTernOp src dst op => exact good_vecExtTernOp src dst op
  | vecNarrow src dst s => exact good_vecNarrow src dst s
  | vecConvert src dst op => exact good_vecConvert src dst op
  | vecSplat sh => rcases sh with s | s <;> cases s <;> decide
  | _ => rfl

end nullary

theorem nullaryName_good {i : Instr} {s : String} (h : nullaryName i = some s) :
    s ∉ explicitKws ∧ s ∉ blockKws ∧ KwOk s := by
  have := nullaryName_goodB i
  rw [h] at this
  simpa [goodKwB] using this

/-- Keywords of plain instructions. -/
def PlainKw (s : String) : Prop := (∃ i, nullaryName i = some s) ∨ s ∈ explicitKws

/-- Keywords of instructions. -/
def InstrKw (s : String) : Prop := PlainKw s ∨ s ∈ blockKws

theorem explicitKws_ok : ∀ s ∈ explicitKws, KwOk s ∧ s ∉ blockKws := by decide +kernel

theorem blockKws_ok : ∀ s ∈ blockKws, KwOk s := by decide +kernel

theorem PlainKw.ok {s : String} (h : PlainKw s) : KwOk s ∧ s ∉ blockKws := by
  rcases h with ⟨i, hi⟩ | h
  · exact ⟨(nullaryName_good hi).2.2, (nullaryName_good hi).2.1⟩
  · exact explicitKws_ok s h

theorem InstrKw.ok {s : String} (h : InstrKw s) : KwOk s := by
  rcases h with h | h
  · exact h.ok.1
  · exact blockKws_ok s h

theorem InstrKw.not_reserved {s : String} (h : InstrKw s) : s ∉ reservedKws := h.ok.1

theorem memOps_mem {s : String} {N : Nat} {k : MemIdx → MemArg → Instr} (h : (s, N, k) ∈ memOps) :
    s ∈ explicitKws := by
  unfold explicitKws
  simp only [List.mem_append, List.mem_map]
  exact .inl (.inl (.inr ⟨_, h, rfl⟩))

theorem laneMemOps_mem {s : String} {N : Nat} {k : MemIdx → MemArg → LaneIdx → Instr}
    (h : (s, N, k) ∈ laneMemOps) : s ∈ explicitKws := by
  unfold explicitKws
  simp only [List.mem_append, List.mem_map]
  exact .inl (.inr ⟨_, h, rfl⟩)

theorem laneOps_mem {s : String} {k : LaneIdx → Instr} (h : (s, k) ∈ laneOps) :
    s ∈ explicitKws := by
  unfold explicitKws
  simp only [List.mem_append, List.mem_map]
  exact .inr ⟨_, h, rfl⟩

/-! ## Item classes -/

/-- Items that start an instruction. -/
def IsStart (x : SExp) : Prop :=
  (∃ s, x = K s ∧ InstrKw s) ∨ ∃ s ys, x = L (K s :: ys) ∧ InstrKw s

/-- Items that may follow an instruction keyword as immediates. -/
def Operand (x : SExp) : Prop := ¬ IsStart x ∧ x ≠ K "end" ∧ x ≠ K "else"

/-- The rest of the items after an instruction (or an instruction sequence) does
not continue its immediates. -/
def Stop (r : List SExp) : Prop := ∀ x ∈ r.head?, ¬ Operand x

/-- The items after a block body: nothing, `end` or `else`. -/
def Term (r : List SExp) : Prop := r = [] ∨ (∃ t, r = K "end" :: t) ∨ ∃ t, r = K "else" :: t

theorem Term.stop {r : List SExp} (h : Term r) : Stop r := by
  rcases h with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp [Stop]
  · intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    subst hx; exact fun h => h.2.1 rfl
  · intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    subst hx; exact fun h => h.2.2 rfl

theorem isStart_not_operand {x : SExp} (h : IsStart x) : ¬ Operand x := fun h' => h'.1 h

/-- Bare tokens that are operands. -/
def KwOperand (t : String) : Prop :=
  (¬ LowerKw t ∨ t ∈ reservedKws ∨ HasPre "nan:" t ∨ HasPre "offset=" t ∨ HasPre "align=" t) ∧
    t ≠ "end" ∧ t ≠ "else"

instance (t : String) : Decidable (KwOperand t) := by unfold KwOperand; infer_instance

theorem operand_K {t : String} (h : KwOperand t) : Operand (K t) := by
  obtain ⟨h, hne, hne'⟩ := h
  have notStart : ¬ IsStart (K t) := by
    rintro (⟨s, e, hs⟩ | ⟨s, ys, e, -⟩)
    · simp only [K_inj] at e; subst e
      obtain ⟨h1, h2, h3, h4, h5⟩ := hs.ok
      rcases h with h | h | h | h | h <;> contradiction
    · simp at e
  refine ⟨notStart, ?_, ?_⟩
  · rintro e; simp only [K_inj] at e; exact hne e
  · rintro e; simp only [K_inj] at e; exact hne' e

theorem operand_L {s : String} {ys : List SExp} (h : s ∈ reservedKws) : Operand (L (K s :: ys)) := by
  refine ⟨?_, by simp, by simp⟩
  rintro (⟨s', e, -⟩ | ⟨s', ys', e, hs⟩)
  · simp at e
  · simp only [L_inj, List.cons.injEq, K_inj] at e; obtain ⟨rfl, -⟩ := e
    exact hs.not_reserved h

theorem operand_headKw {s : String} {x : SExp} (h : s ∈ reservedKws) (hx : HeadKw s x) :
    Operand x := by
  obtain ⟨ys, rfl⟩ := hx; exact operand_L h

theorem operand_id {n : String} : Operand (Formats.SExp2.atom (Atom.id n)) := by
  refine ⟨?_, by simp [K, kw], by simp [K, kw]⟩
  rintro (⟨s, e, -⟩ | ⟨s, ys, e, -⟩) <;> simp [K, kw, L, listOf] at e

theorem not_lowerKw_of_digit {t : String} {c : Char} {r : List Char} (e : t.toList = c :: r)
    (hc : IsDigit c) : ¬ LowerKw t := by
  unfold LowerKw lowerB; rw [e]
  simp only [decide_eq_true_eq, not_and]
  intro h1 _
  have h2 := hc.2
  simp only [Char.le_def] at h1 h2
  have := UInt32.le_trans h1 h2
  revert this; decide

theorem not_lowerKw_sign {t : String} {c : Char} {r : List Char} (e : t.toList = c :: r)
    (hc : c = '+' ∨ c = '-') : ¬ LowerKw t := by
  unfold LowerKw lowerB; rw [e]
  rcases hc with rfl | rfl <;> simp

theorem kwOperand_of_not_lower {t : String} (h : ¬ LowerKw t) : KwOperand t := by
  refine ⟨.inl h, ?_, ?_⟩ <;> (rintro rfl; exact h (by decide))

theorem operand_numTok {x : SExp} (h : NumTok x) : Operand x := by
  obtain ⟨t, rfl, c, hc, hd⟩ := h
  apply operand_K; apply kwOperand_of_not_lower
  cases e : t.toList with
  | nil => rw [e] at hc; simp at hc
  | cons c' r =>
      rw [e] at hc; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
      subst hc; exact not_lowerKw_of_digit e hd

theorem operand_idx {names : List (Option String)} {k : IndexKind} {x : SExp} {i : Wasm.Idx k}
    (h : Idx names x i) : Operand x := by
  rcases idx_shape h with h | ⟨n, rfl⟩
  · exact operand_numTok h
  · exact operand_id

theorem operand_atomU {N : Nat} {x : SExp} {n : Nat} (h : AtomU N x n) : Operand x :=
  operand_numTok (atomU_numTok h)

theorem operand_reserved {s : String} (h : s ∈ reservedKws) (h1 : s ≠ "end") (h2 : s ≠ "else") :
    Operand (K s) :=
  operand_K ⟨.inr (.inl h), h1, h2⟩

theorem operand_atomI {N : Nat} {x : SExp} {b : BitVec N} (h : AtomI N x b) : Operand x := by
  obtain ⟨t, rfl, h⟩ := h
  apply operand_K; apply kwOperand_of_not_lower
  rcases h with ⟨n, hu, -⟩ | ⟨i, ⟨sc, rest, s, n, e, hs, hu, -⟩, -⟩
  · obtain ⟨c, r, e, hc⟩ := un_head hu; exact not_lowerKw_of_digit e hc
  · rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · obtain ⟨c, r, e', hc⟩ := un_head hu
      simp only [List.nil_append] at e; rw [e'] at e
      exact not_lowerKw_of_digit e hc
    · exact not_lowerKw_sign (r := rest) e (.inl rfl)
    · exact not_lowerKw_sign (r := rest) e (.inr rfl)

theorem operand_atomF {t : FloatType} {x : SExp} {b : BitVec t.width} (h : AtomF t x b) :
    Operand x := by
  obtain ⟨s, rfl, sc, mc, sg, v, n, e, hs, hv, -, -⟩ := h
  apply operand_K
  rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp only [List.nil_append] at e
    rcases hv with ⟨mc', ec, m, k, ex, rfl, hm, -, -⟩ | ⟨mc', ec, m, k, ex, rfl, -, -, -⟩ |
        ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨ds, n', rfl, -, -⟩
    · apply kwOperand_of_not_lower
      obtain ⟨c, r, e', hc⟩ := mant_head hm
      rw [e', List.cons_append] at e
      exact not_lowerKw_of_digit e (by simpa using hc)
    · exact kwOperand_of_not_lower (not_lowerKw_of_digit e (by decide))
    · rw [String.toList_injective e]; decide
    · rw [String.toList_injective e]; decide
    · refine ⟨.inr (.inr (.inl (hasPre_of_eq (r := "0x".toList ++ ds) ?_))), ?_, ?_⟩
      · rw [e]; simp only [← List.append_assoc]; rfl
      · rintro rfl; exact absurd (hasPre_of_eq e) (by decide)
      · rintro rfl; exact absurd (hasPre_of_eq e) (by decide)
  · exact kwOperand_of_not_lower (not_lowerKw_sign (r := mc) e (.inl rfl))
  · exact kwOperand_of_not_lower (not_lowerKw_sign (r := mc) e (.inr rfl))

theorem refAbbrevKws_ok : ∀ s ∈ refAbbrevKws, s ∈ reservedKws ∧ s ≠ "end" ∧ s ≠ "else" := by
  decide +kernel

theorem heapKws_ok : ∀ s ∈ heapKws, s ∈ reservedKws ∧ s ≠ "end" ∧ s ≠ "else" := by
  decide +kernel

theorem operand_refTypeT {I : IdCtx} {x : SExp} {r : RefType} (h : RefTypeT I x r) : Operand x := by
  rcases refTypeT_shape h with h | ⟨s, rfl, hs⟩
  · exact operand_headKw (by decide) h
  · obtain ⟨h1, h2, h3⟩ := refAbbrevKws_ok s hs; exact operand_reserved h1 h2 h3

theorem operand_heapTypeT {I : IdCtx} {x : SExp} {h : HeapType} (hh : HeapTypeT I x h) :
    Operand x := by
  rcases hh with ⟨s, a, rfl, ha, -⟩ | ⟨i, hi, -⟩
  · obtain ⟨h1, h2, h3⟩ := heapKws_ok s (absHeapKw_mem ha); exact operand_reserved h1 h2 h3
  · exact operand_idx hi

theorem operand_tuList {x : SExp} (h : TUList x) : Operand x := by
  rcases h with h | h | h <;> exact operand_headKw (by decide) h

theorem operand_forall₂ {α : Type} {R : SExp → α → Prop} (hR : ∀ x a, R x a → Operand x)
    {xs : List SExp} {as : List α} (h : List.Forall₂ R xs as) : ∀ x ∈ xs, Operand x :=
  forall₂_mem_left hR h

theorem operand_optIdx {names : List (Option String)} {k : IndexKind} {xs : List SExp}
    {i : Wasm.Idx k} (h : OptIdx names xs i) : ∀ x ∈ xs, Operand x := by
  rcases h with ⟨rfl, -⟩ | ⟨x, rfl, hx⟩
  · simp
  · intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact operand_idx hx

theorem operand_memArgT {N : Nat} {xs : List SExp} {a : MemArg} (h : MemArgT N xs a) :
    ∀ x ∈ xs, Operand x := by
  obtain ⟨ox, ax, rfl, ho, ha⟩ := h
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · rcases ho with ⟨rfl, -⟩ | ⟨t, r, rfl, e, -⟩
    · simp at hx
    · simp only [List.mem_singleton] at hx; subst hx
      refine operand_K ⟨.inr (.inr (.inr (.inl (hasPre_of_eq e)))), ?_, ?_⟩ <;>
        (rintro rfl; exact absurd (hasPre_of_eq e) (by decide))
  · rcases ha with ⟨rfl, -⟩ | ⟨t, r, m, rfl, e, -⟩
    · simp at hx
    · simp only [List.mem_singleton] at hx; subst hx
      refine operand_K ⟨.inr (.inr (.inr (.inr (hasPre_of_eq e)))), ?_, ?_⟩ <;>
        (rintro rfl; exact absurd (hasPre_of_eq e) (by decide))

theorem operand_v128ConstT {xs : List SExp} {b : BitVec 128} (h : V128ConstT xs b) :
    ∀ x ∈ xs, Operand x := by
  have shape : ∀ s : String, s ∈ ["i8x16", "i16x8", "i32x4", "i64x2", "f32x4", "f64x2"] →
      Operand (K s) := fun s hs => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact operand_reserved (by decide) (by decide) (by decide)
  rcases h with ⟨cs, vs, rfl, hc, -⟩ | ⟨cs, vs, rfl, hc, -⟩ | ⟨cs, vs, rfl, hc, -⟩ |
      ⟨cs, vs, rfl, hc, -⟩ | ⟨cs, vs, rfl, hc, -⟩ | ⟨cs, vs, rfl, hc, -⟩ <;>
    intro x hx <;> simp only [List.mem_cons] at hx <;> rcases hx with rfl | hx
  all_goals first
    | exact shape _ (by simp)
    | exact operand_forall₂ (fun _ _ h => operand_atomI h) hc x hx
    | exact operand_forall₂ (fun _ _ h => operand_atomF h) hc x hx


/-! ## Shapes of instructions -/

theorem mem_explicit0 {s : String} (h : s ∈ explicitKws0) : s ∈ explicitKws := by
  unfold explicitKws; simp [h]

theorem ops_nil : ∀ y ∈ ([] : List SExp), Operand y := by simp

theorem ops_one {x : SExp} (h : Operand x) : ∀ y ∈ [x], Operand y := by
  intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact h

theorem ops_cons {x : SExp} {xs : List SExp} (h : Operand x) (h' : ∀ y ∈ xs, Operand y) :
    ∀ y ∈ x :: xs, Operand y := by
  intro y hy; rcases List.mem_cons.mp hy with rfl | hy
  · exact h
  · exact h' y hy

theorem ops_append {xs ys : List SExp} (h : ∀ y ∈ xs, Operand y) (h' : ∀ y ∈ ys, Operand y) :
    ∀ y ∈ xs ++ ys, Operand y := by
  intro y hy; rcases List.mem_append.mp hy with hy | hy
  · exact h y hy
  · exact h' y hy

theorem operand_fieldIdxT {I : IdCtx} {t : TypeIdx} {x : SExp} {f : FieldIdx}
    (h : FieldIdxT I t x f) : Operand x := operand_idx (show Idx _ x f from h)

theorem ops_typeUseT {I : IdCtx} {xs : List SExp} {x : TypeIdx} {ls : List (Option String)}
    {u : List FuncType} (h : TypeUseT I xs x ls u) : ∀ y ∈ xs, Operand y :=
  fun y hy => operand_tuList (typeUseT_mem h y hy)

/-- The items of a plain instruction: an instruction keyword and operands. -/
theorem plain_shape {I : IdCtx} {xs : List SExp} {i : Instr} {u : List FuncType}
    (h : Plain I xs i u) : ∃ s ys, xs = K s :: ys ∧ PlainKw s ∧ ∀ y ∈ ys, Operand y := by
  have kw : ∀ {s : String}, s ∈ explicitKws0 → PlainKw s := fun h => .inr (mem_explicit0 h)
  cases h with
  | nullary hs => exact ⟨_, [], rfl, .inl ⟨_, hs⟩, ops_nil⟩
  | select => exact ⟨_, [], rfl, kw (by decide), ops_nil⟩
  | selectTyped _ hc =>
      exact ⟨_, _, rfl, kw (by decide), fun y hy => operand_tuList
        (.inr (.inr (concat_mem (R := ResultT I) (fun _ _ h => resultT_head h) hc y hy)))⟩
  | br hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | brIf hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | brTable hxs _ =>
      exact ⟨_, _, rfl, kw (by decide), operand_forall₂ (fun _ _ h => operand_idx h) hxs⟩
  | brOnNull hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | brOnNonNull hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | brOnCast hx h1 h2 =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx)
        (ops_cons (operand_refTypeT h1) (ops_one (operand_refTypeT h2)))⟩
  | brOnCastFail hx h1 h2 =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx)
        (ops_cons (operand_refTypeT h1) (ops_one (operand_refTypeT h2)))⟩
  | call hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | callRef hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | callIndirect ht hu _ =>
      exact ⟨_, _, rfl, kw (by decide), ops_append (operand_optIdx ht) (ops_typeUseT hu)⟩
  | returnCall hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | returnCallRef hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | returnCallIndirect ht hu _ =>
      exact ⟨_, _, rfl, kw (by decide), ops_append (operand_optIdx ht) (ops_typeUseT hu)⟩
  | throw hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | localGet hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | localSet hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | localTee hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | globalGet hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | globalSet hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | tableGet hx => exact ⟨_, _, rfl, kw (by decide), operand_optIdx hx⟩
  | tableSet hx => exact ⟨_, _, rfl, kw (by decide), operand_optIdx hx⟩
  | tableSize hx => exact ⟨_, _, rfl, kw (by decide), operand_optIdx hx⟩
  | tableGrow hx => exact ⟨_, _, rfl, kw (by decide), operand_optIdx hx⟩
  | tableFill hx => exact ⟨_, _, rfl, kw (by decide), operand_optIdx hx⟩
  | tableCopy h1 h2 =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx h1) (ops_one (operand_idx h2))⟩
  | tableCopy0 => exact ⟨_, _, rfl, kw (by decide), ops_nil⟩
  | tableInit ht hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_append (operand_optIdx ht) (ops_one (operand_idx hy))⟩
  | elemDrop hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | memOp hm hmx ha =>
      exact ⟨_, _, rfl, .inr (memOps_mem hm), ops_append (operand_optIdx hmx) (operand_memArgT ha)⟩
  | laneMemOp hm hmx ha hl =>
      exact ⟨_, _, rfl, .inr (laneMemOps_mem hm),
        ops_append (ops_append (operand_optIdx hmx) (operand_memArgT ha)) (ops_one (operand_atomU hl))⟩
  | memorySize hx => exact ⟨_, _, rfl, kw (by decide), operand_optIdx hx⟩
  | memoryGrow hx => exact ⟨_, _, rfl, kw (by decide), operand_optIdx hx⟩
  | memoryFill hx => exact ⟨_, _, rfl, kw (by decide), operand_optIdx hx⟩
  | memoryCopy h1 h2 =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx h1) (ops_one (operand_idx h2))⟩
  | memoryCopy0 => exact ⟨_, _, rfl, kw (by decide), ops_nil⟩
  | memoryInit hm hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_append (operand_optIdx hm) (ops_one (operand_idx hy))⟩
  | dataDrop hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | refNull hh => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_heapTypeT hh)⟩
  | refFunc hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | refTest hr => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_refTypeT hr)⟩
  | refCast hr => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_refTypeT hr)⟩
  | structNew hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | structNewDefault hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | structGet hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_fieldIdxT hy))⟩
  | structGetS hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_fieldIdxT hy))⟩
  | structGetU hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_fieldIdxT hy))⟩
  | structSet hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_fieldIdxT hy))⟩
  | arrayNew hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | arrayNewDefault hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | arrayNewFixed hx hn =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_atomU hn))⟩
  | arrayNewData hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_idx hy))⟩
  | arrayNewElem hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_idx hy))⟩
  | arrayGet hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | arrayGetS hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | arrayGetU hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | arraySet hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | arrayFill hx => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_idx hx)⟩
  | arrayCopy hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_idx hy))⟩
  | arrayInitData hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_idx hy))⟩
  | arrayInitElem hx hy =>
      exact ⟨_, _, rfl, kw (by decide), ops_cons (operand_idx hx) (ops_one (operand_idx hy))⟩
  | i32Const hc => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_atomI hc)⟩
  | i64Const hc => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_atomI hc)⟩
  | f32Const hc => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_atomF hc)⟩
  | f64Const hc => exact ⟨_, _, rfl, kw (by decide), ops_one (operand_atomF hc)⟩
  | v128Const hv => exact ⟨_, _, rfl, kw (by decide), operand_v128ConstT hv⟩
  | shuffle hxs _ =>
      exact ⟨_, _, rfl, kw (by decide), operand_forall₂ (fun _ _ h => operand_atomU h) hxs⟩
  | lane hl hx => exact ⟨_, _, rfl, .inr (laneOps_mem hl), ops_one (operand_atomU hx)⟩

theorem blockInstr_shape {I : IdCtx} {xs : List SExp} {i : Instr} {u : List FuncType}
    (h : BlockInstr I xs i u) : ∃ s ys, xs = K s :: ys ∧ s ∈ blockKws := by
  cases h <;> exact ⟨_, _, rfl, by decide⟩

theorem folded_shape {I : IdCtx} {x : SExp} {e : Expr} {u : List FuncType} (h : Folded I x e u) :
    ∃ s ys, x = L (K s :: ys) ∧ InstrKw s := by
  cases h with
  | plain hp _ =>
      obtain ⟨s, ys, e, hs, -⟩ := plain_shape hp
      simp only [List.cons.injEq, K_inj] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨_, _, rfl, .inl hs⟩
  | block => exact ⟨_, _, rfl, .inr (by decide)⟩
  | loop => exact ⟨_, _, rfl, .inr (by decide)⟩
  | ifThen => exact ⟨_, _, rfl, .inr (by decide)⟩
  | ifThenElse => exact ⟨_, _, rfl, .inr (by decide)⟩
  | tryTable => exact ⟨_, _, rfl, .inr (by decide)⟩

theorem isStart_K {s : String} (h : InstrKw s) : IsStart (K s) := .inl ⟨s, rfl, h⟩

theorem instrs_cases_head {I : IdCtx} {r : List SExp} {e : Expr} {u : List FuncType}
    (h : Instrs I r e u) : r = [] ∨ ∃ x t, r = x :: t ∧ IsStart x := by
  cases h with
  | nil => exact .inl rfl
  | plain hp _ =>
      obtain ⟨s, ys, rfl, hs, -⟩ := plain_shape hp
      exact .inr ⟨_, _, rfl, isStart_K (.inl hs)⟩
  | block hb _ =>
      obtain ⟨s, ys, rfl, hs⟩ := blockInstr_shape hb
      exact .inr ⟨_, _, rfl, isStart_K (.inr hs)⟩
  | folded hf _ =>
      obtain ⟨s, ys, rfl, hs⟩ := folded_shape hf
      exact .inr ⟨_, _, rfl, .inr ⟨s, ys, rfl, hs⟩⟩

/-- `r` does not start with a `P`-item. -/
def NotP (P : SExp → Prop) (r : List SExp) : Prop := ∀ x ∈ r.head?, ¬ P x

theorem notP_nil {P : SExp → Prop} : NotP P [] := by simp [NotP]

theorem notP_cons {P : SExp → Prop} {x : SExp} {t : List SExp} (h : ¬ P x) : NotP P (x :: t) := by
  intro y hy; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy; subst hy; exact h

theorem notP_append {P : SExp → Prop} {xs r : List SExp} (h : ∀ x ∈ xs, ¬ P x) (hr : NotP P r) :
    NotP P (xs ++ r) := by
  cases xs with
  | nil => simpa using hr
  | cons x xs => exact notP_cons (h x (by simp))

theorem notP_instrs {P : SExp → Prop} (hP : ∀ x, IsStart x → ¬ P x) {I : IdCtx} {body r : List SExp}
    {e : Expr} {u : List FuncType} (h : Instrs I body e u) (hr : NotP P r) : NotP P (body ++ r) := by
  rcases instrs_cases_head h with rfl | ⟨x, t, rfl, hx⟩
  · simpa using hr
  · exact notP_cons (hP x hx)

theorem stop_iff {r : List SExp} : Stop r ↔ NotP Operand r := Iff.rfl

theorem stop_instrs {I : IdCtx} {body r : List SExp} {e : Expr} {u : List FuncType}
    (h : Instrs I body e u) (hr : Stop r) : Stop (body ++ r) :=
  notP_instrs (fun _ hx => isStart_not_operand hx) h hr

/-! ## Labels, block types, catches -/

theorem labelT_mem {I I' : IdCtx} {lx : List SExp} {id : Option String} (h : LabelT I lx id I') :
    ∀ x ∈ lx, IdAtom x := by
  rcases h with ⟨rfl, -⟩ | ⟨n, rfl, -⟩ | ⟨n, x, rfl, -⟩
  · simp
  · intro y hy; simp only [List.mem_singleton] at hy; exact ⟨n, hy⟩
  · intro y hy; simp only [List.mem_singleton] at hy; exact ⟨n, hy⟩

theorem endIdT_mem {ex : List SExp} {id : Option String} (h : EndIdT ex id) :
    ∀ x ∈ ex, IdAtom x := by
  rcases h with rfl | ⟨n, rfl, -⟩
  · simp
  · intro y hy; simp only [List.mem_singleton] at hy; exact ⟨n, hy⟩

theorem valueFormT_mem {I : IdCtx} {xs : List SExp} {ts : List ValType}
    (h : ValueFormT I xs ts) : ∀ x ∈ xs, TUList x := by
  obtain ⟨pxs, rxs, rfl, hp, hr⟩ := h
  exact fun x hx => .inr (params_results_mem hp hr x hx)

theorem valueFormT_functional {I : IdCtx} (hT : Distinct I.types) {xs : List SExp}
    {ts ts' : List ValType} (h : ValueFormT I xs ts) (h' : ValueFormT I xs ts') : ts = ts' := by
  obtain ⟨pxs, rxs, rfl, hp, hr⟩ := h
  obtain ⟨pxs', rxs', e, hp', hr'⟩ := h'
  obtain ⟨rfl, rfl⟩ := params_results_split hp hr hp' hr' e
  exact concat_functional (R := ResultT I) (fun _ _ _ h h' => resultT_functional hT h h') hr hr'

theorem valueFormT_eq {I I' : IdCtx} (hE : TypesEq I I') : ValueFormT I = ValueFormT I' := by
  funext xs ts; unfold ValueFormT; rw [paramT_eq hE, resultT_eq hE]

theorem blockTypeT_mem {I : IdCtx} {xs : List SExp} {bt : BlockType} {u : List FuncType}
    (h : BlockTypeT I xs bt u) : ∀ x ∈ xs, TUList x := by
  rcases h with ⟨ts, hc, -⟩ | ⟨ts, t, hc, -⟩ | ⟨x, ls, hu, -⟩
  · exact valueFormT_mem hc
  · exact valueFormT_mem hc
  · exact typeUseT_mem hu

def catchKws : List String := ["catch", "catch_ref", "catch_all", "catch_all_ref"]

/-- A catch clause item. -/
def CatchList (x : SExp) : Prop := ∃ s ∈ catchKws, HeadKw s x

theorem catchT_head {I : IdCtx} {x : SExp} {c : Catch} (h : CatchT I x c) : CatchList x := by
  rcases h with ⟨tx, lx, t, l, rfl, -⟩ | ⟨tx, lx, t, l, rfl, -⟩ | ⟨lx, l, rfl, -⟩ | ⟨lx, l, rfl, -⟩
  · exact ⟨"catch", by decide, _, rfl⟩
  · exact ⟨"catch_ref", by decide, _, rfl⟩
  · exact ⟨"catch_all", by decide, _, rfl⟩
  · exact ⟨"catch_all_ref", by decide, _, rfl⟩

theorem isStart_not_idAtom {x : SExp} (h : IsStart x) : ¬ IdAtom x := by
  rcases h with ⟨s, rfl, -⟩ | ⟨s, ys, rfl, -⟩
  · exact not_idAtom_K
  · exact not_idAtom_L

theorem isStart_not_headKw {x : SExp} {s : String} (hs : s ∈ reservedKws) (h : IsStart x) :
    ¬ HeadKw s x := by
  rintro ⟨ys, rfl⟩
  rcases h with ⟨s', e, -⟩ | ⟨s', ys', e, hs'⟩
  · simp at e
  · simp only [L_inj, List.cons.injEq, K_inj] at e; obtain ⟨rfl, -⟩ := e
    exact hs'.not_reserved hs

theorem isStart_not_tuList {x : SExp} (h : IsStart x) : ¬ TUList x := by
  rintro (h' | h' | h') <;> exact isStart_not_headKw (by decide) h h'

theorem isStart_not_catch {x : SExp} (h : IsStart x) : ¬ CatchList x := by
  rintro ⟨s, hs, h'⟩
  refine isStart_not_headKw ?_ h h'
  simp only [catchKws, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> decide

theorem tuList_not_catch {x : SExp} (h : TUList x) : ¬ CatchList x := by
  rintro ⟨s, hs, h'⟩
  simp only [catchKws, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases h with h | h | h <;> rcases hs with rfl | rfl | rfl | rfl <;>
    exact headKw_ne (by decide) h h'

theorem catch_not_idAtom {x : SExp} (h : CatchList x) : ¬ IdAtom x := by
  obtain ⟨s, -, h⟩ := h; exact not_idAtom_of_headKw h

theorem operand_not_idAtom {x : SExp} (h : ¬ Operand x) : ¬ IdAtom x := by
  rintro ⟨n, rfl⟩; exact h operand_id

theorem term_cons_not_start {x : SExp} {t : List SExp} (h : Term (x :: t)) : ¬ IsStart x := by
  have hE : ¬ IsStart (K "end") := by
    rintro (⟨s, e, hs⟩ | ⟨s, ys, e, -⟩)
    · simp only [K_inj] at e; subst e; exact hs.not_reserved (by decide)
    · simp at e
  have hL : ¬ IsStart (K "else") := by
    rintro (⟨s, e, hs⟩ | ⟨s, ys, e, -⟩)
    · simp only [K_inj] at e; subst e; exact hs.not_reserved (by decide)
    · simp at e
  rcases h with h | ⟨t', h⟩ | ⟨t', h⟩
  · simp at h
  · simp only [List.cons.injEq] at h; rw [h.1]; exact hE
  · simp only [List.cons.injEq] at h; rw [h.1]; exact hL

theorem term_end {t : List SExp} : Term (K "end" :: t) := .inr (.inl ⟨t, rfl⟩)

theorem term_else {t : List SExp} : Term (K "else" :: t) := .inr (.inr ⟨t, rfl⟩)

theorem notP_end {P : SExp → Prop} {t : List SExp} (h : ¬ P (K "end")) : NotP P (K "end" :: t) :=
  notP_cons h

/-! ## The items spanned by one instruction -/

/-- The items after a label and a block type. -/
theorem next_label {I I' : IdCtx} {bx body r : List SExp} {bt : BlockType} {uu : List FuncType}
    {e : Expr} {u : List FuncType} (hb : BlockTypeT I bx bt uu) (hbody : Instrs I' body e u)
    (hr : NotP IdAtom r) : NotP IdAtom (bx ++ (body ++ r)) :=
  notP_append (fun x hx => tuList_notId (blockTypeT_mem hb x hx))
    (notP_instrs (fun _ h => isStart_not_idAtom h) hbody hr)

theorem next_blockType {I : IdCtx} {body r : List SExp} {e : Expr} {u : List FuncType}
    (hbody : Instrs I body e u) (hr : NotP TUList r) : NotP TUList (body ++ r) :=
  notP_instrs (fun _ h => isStart_not_tuList h) hbody hr

theorem notTU_end {t : List SExp} : NotP TUList (K "end" :: t) :=
  notP_cons (by rintro (⟨ys, e⟩ | ⟨ys, e⟩ | ⟨ys, e⟩) <;> simp at e)

theorem notTU_else {t : List SExp} : NotP TUList (K "else" :: t) :=
  notP_cons (by rintro (⟨ys, e⟩ | ⟨ys, e⟩ | ⟨ys, e⟩) <;> simp at e)

theorem notCatch_end {t : List SExp} : NotP CatchList (K "end" :: t) :=
  notP_cons (by rintro ⟨s, -, ys, e⟩; simp at e)

theorem notId_end {t : List SExp} : NotP IdAtom (K "end" :: t) := notP_cons not_idAtom_K

theorem notId_else {t : List SExp} : NotP IdAtom (K "else" :: t) := notP_cons not_idAtom_K

theorem stop_notId {r : List SExp} (h : Stop r) : NotP IdAtom r :=
  fun x hx => operand_not_idAtom (h x hx)


/-- Motive: the items spanned by an instruction sequence followed by nothing,
`end` or `else` are determined by the item stream. -/
def InstrsPrefix (a : List SExp) : Prop :=
  ∀ {J : IdCtx} {a' r r' : List SExp} {e' : Expr} {u' : List FuncType}, Instrs J a' e' u' →
    a ++ r = a' ++ r' → Term r → Term r' → a = a'

/-- Motive: the items spanned by a block instruction are determined by the item
stream. -/
def BlockPrefix (xs : List SExp) : Prop :=
  ∀ {J : IdCtx} {xs' r r' : List SExp} {i' : Instr} {u' : List FuncType}, BlockInstr J xs' i' u' →
    xs ++ r = xs' ++ r' → Stop r → Stop r' → xs = xs'

theorem prefix_nil : InstrsPrefix [] := by
  intro J a' r r' e' u' h' eq hr hr'
  rcases instrs_cases_head h' with rfl | ⟨x, t, rfl, hx⟩
  · rfl
  · simp only [List.nil_append, List.cons_append] at eq; subst eq
    exact absurd hx (term_cons_not_start hr)

theorem prefix_plain {I : IdCtx} {xs rest : List SExp} {i : Instr} {is : Expr}
    {u u₁ : List FuncType} (hp : Plain I xs i u) (hrest : Instrs I rest is u₁)
    (ih : InstrsPrefix rest) : InstrsPrefix (xs ++ rest) := by
  intro J a' r r' e' u' h' eq hr hr'
  obtain ⟨s, ys, rfl, hs, hys⟩ := plain_shape hp
  cases h' with
  | nil =>
      simp only [List.cons_append, List.append_assoc, List.nil_append] at eq; subst eq
      exact absurd (isStart_K (.inl hs)) (term_cons_not_start hr')
  | plain hp' hrest' =>
      obtain ⟨s', ys', rfl, hs', hys'⟩ := plain_shape hp'
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, K_inj] at eq
      obtain ⟨rfl, eq⟩ := eq
      obtain ⟨rfl, eq2⟩ := munch hys hys' (stop_instrs hrest hr.stop)
        (stop_instrs hrest' hr'.stop) eq
      rw [ih hrest' eq2 hr hr']
  | block hb' _ =>
      obtain ⟨s', ys', rfl, hs'⟩ := blockInstr_shape hb'
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, K_inj] at eq
      obtain ⟨rfl, -⟩ := eq
      exact absurd hs' hs.ok.2
  | folded hf' _ =>
      obtain ⟨s', ys', rfl, -⟩ := folded_shape hf'
      simp at eq

theorem prefix_block {I : IdCtx} {xs rest : List SExp} {i : Instr} {is : Expr}
    {u u₁ : List FuncType} (hb : BlockInstr I xs i u) (hrest : Instrs I rest is u₁)
    (ihb : BlockPrefix xs) (ih : InstrsPrefix rest) : InstrsPrefix (xs ++ rest) := by
  intro J a' r r' e' u' h' eq hr hr'
  cases h' with
  | nil =>
      obtain ⟨s, ys, rfl, hs⟩ := blockInstr_shape hb
      simp only [List.cons_append, List.append_assoc, List.nil_append] at eq; subst eq
      exact absurd (isStart_K (.inr hs)) (term_cons_not_start hr')
  | plain hp' _ =>
      obtain ⟨s, ys, rfl, hs⟩ := blockInstr_shape hb
      obtain ⟨s', ys', rfl, hs', -⟩ := plain_shape hp'
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, K_inj] at eq
      obtain ⟨rfl, -⟩ := eq
      exact absurd hs hs'.ok.2
  | block hb' hrest' =>
      have eq1 := eq
      simp only [List.append_assoc] at eq1
      obtain rfl := ihb hb' eq1 (stop_instrs hrest hr.stop) (stop_instrs hrest' hr'.stop)
      simp only [List.append_assoc, List.append_cancel_left_eq] at eq
      rw [ih hrest' eq hr hr']
  | folded hf' _ =>
      obtain ⟨s, ys, rfl, hs⟩ := blockInstr_shape hb
      obtain ⟨s', ys', rfl, -⟩ := folded_shape hf'
      simp at eq

theorem prefix_folded {I : IdCtx} {x : SExp} {rest : List SExp} {is : Expr} {u : List FuncType}
    (hf : Folded I x is u) (ih : InstrsPrefix rest) : InstrsPrefix (x :: rest) := by
  intro J a' r r' e' u' h' eq hr hr'
  obtain ⟨s, ys, rfl, hs⟩ := folded_shape hf
  cases h' with
  | nil =>
      simp only [List.cons_append, List.nil_append] at eq; subst eq
      exact absurd (.inr ⟨s, ys, rfl, hs⟩) (term_cons_not_start hr')
  | plain hp' _ =>
      obtain ⟨s', ys', rfl, -, -⟩ := plain_shape hp'
      simp at eq
  | block hb' _ =>
      obtain ⟨s', ys', rfl, -⟩ := blockInstr_shape hb'
      simp at eq
  | folded hf' hrest' =>
      simp only [List.cons_append, List.cons.injEq] at eq
      obtain ⟨rfl, eq⟩ := eq
      rw [ih hrest' eq hr hr']

theorem prefix_bblock {I I' : IdCtx} {lx bx body ex : List SExp} {id : Option String}
    {bt : BlockType} {is : Expr} {u u₁ : List FuncType} (hl : LabelT I lx id I')
    (hb : BlockTypeT I bx bt u) (hbody : Instrs I' body is u₁) (hend : EndIdT ex id)
    (ih : InstrsPrefix body) {kw : String} (hkw : kw = "block" ∨ kw = "loop") :
    BlockPrefix (K kw :: (lx ++ bx ++ body ++ K "end" :: ex)) := by
  intro J xs' r r' i' u' h' eq hr hr'
  have main : ∀ {I'' : IdCtx} {lx' bx' body' ex' : List SExp} {id' : Option String}
      {bt' : BlockType} {is' : Expr} {uu uu₁ : List FuncType}, LabelT J lx' id' I'' →
      BlockTypeT J bx' bt' uu → Instrs I'' body' is' uu₁ → EndIdT ex' id' →
      (lx ++ bx ++ body ++ K "end" :: ex) ++ r = (lx' ++ bx' ++ body' ++ K "end" :: ex') ++ r' →
      lx ++ bx ++ body ++ K "end" :: ex = lx' ++ bx' ++ body' ++ K "end" :: ex' := by
    intro I'' lx' bx' body' ex' id' bt' is' uu uu₁ hl' hb' hbody' hend' eq
    simp only [List.append_assoc, List.cons_append] at eq
    obtain ⟨rfl, eq1⟩ := munch (labelT_mem hl) (labelT_mem hl')
      (next_label hb hbody notId_end) (next_label hb' hbody' notId_end) eq
    obtain ⟨rfl, eq2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
      (next_blockType hbody notTU_end) (next_blockType hbody' notTU_end) eq1
    obtain rfl := ih hbody' eq2 term_end term_end
    simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at eq2
    obtain ⟨rfl, -⟩ := munch (endIdT_mem hend) (endIdT_mem hend') (stop_notId hr)
      (stop_notId hr') eq2
    rfl
  cases h' with
  | block hl' hb' hbody' hend' =>
      simp only [List.cons_append, List.cons.injEq, K_inj] at eq
      obtain ⟨rfl, eq⟩ := eq
      rw [main hl' hb' hbody' hend' eq]
  | loop hl' hb' hbody' hend' =>
      simp only [List.cons_append, List.cons.injEq, K_inj] at eq
      obtain ⟨rfl, eq⟩ := eq
      rw [main hl' hb' hbody' hend' eq]
  | _ => rcases hkw with rfl | rfl <;> simp at eq

theorem prefix_if {I I' : IdCtx} {lx bx thn e₁ els e₂ : List SExp} {id : Option String}
    {bt : BlockType} {is₁ is₂ : Expr} {u u₁ u₂ : List FuncType} (hl : LabelT I lx id I')
    (hb : BlockTypeT I bx bt u) (hthn : Instrs I' thn is₁ u₁) (he₁ : EndIdT e₁ id)
    (hels : Instrs I' els is₂ u₂) (he₂ : EndIdT e₂ id) (ih₁ : InstrsPrefix thn)
    (ih₂ : InstrsPrefix els) :
    BlockPrefix (K "if" :: (lx ++ bx ++ thn ++ K "else" :: (e₁ ++ els ++ K "end" :: e₂))) := by
  intro J xs' r r' i' u' h' eq hr hr'
  cases h' with
  | if_ hl' hb' hthn' he₁' hels' he₂' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at eq
      obtain ⟨rfl, eq1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (next_label hb hthn notId_else) (next_label hb' hthn' notId_else) eq
      obtain ⟨rfl, eq2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (next_blockType hthn notTU_else) (next_blockType hthn' notTU_else) eq1
      obtain rfl := ih₁ hthn' eq2 term_else term_else
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at eq2
      obtain ⟨rfl, eq3⟩ := munch (endIdT_mem he₁) (endIdT_mem he₁')
        (notP_instrs (fun _ h => isStart_not_idAtom h) hels notId_end)
        (notP_instrs (fun _ h => isStart_not_idAtom h) hels' notId_end) eq2
      obtain rfl := ih₂ hels' eq3 term_end term_end
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at eq3
      obtain ⟨rfl, -⟩ := munch (endIdT_mem he₂) (endIdT_mem he₂') (stop_notId hr)
        (stop_notId hr') eq3
      rfl
  | ifNoElse hl' hb' hthn' hend' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at eq
      obtain ⟨rfl, eq1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (next_label hb hthn notId_else) (next_label hb' hthn' notId_end) eq
      obtain ⟨rfl, eq2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (next_blockType hthn notTU_else) (next_blockType hthn' notTU_end) eq1
      obtain rfl := ih₁ hthn' eq2 term_else term_end
      simp at eq2
  | _ => simp at eq

theorem prefix_ifNoElse {I I' : IdCtx} {lx bx thn ex : List SExp} {id : Option String}
    {bt : BlockType} {is₁ : Expr} {u u₁ : List FuncType} (hl : LabelT I lx id I')
    (hb : BlockTypeT I bx bt u) (hthn : Instrs I' thn is₁ u₁) (hend : EndIdT ex id)
    (ih₁ : InstrsPrefix thn) :
    BlockPrefix (K "if" :: (lx ++ bx ++ thn ++ K "end" :: ex)) := by
  intro J xs' r r' i' u' h' eq hr hr'
  cases h' with
  | if_ hl' hb' hthn' he₁' hels' he₂' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at eq
      obtain ⟨rfl, eq1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (next_label hb hthn notId_end) (next_label hb' hthn' notId_else) eq
      obtain ⟨rfl, eq2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (next_blockType hthn notTU_end) (next_blockType hthn' notTU_else) eq1
      obtain rfl := ih₁ hthn' eq2 term_end term_else
      simp at eq2
  | ifNoElse hl' hb' hthn' hend' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at eq
      obtain ⟨rfl, eq1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (next_label hb hthn notId_end) (next_label hb' hthn' notId_end) eq
      obtain ⟨rfl, eq2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (next_blockType hthn notTU_end) (next_blockType hthn' notTU_end) eq1
      obtain rfl := ih₁ hthn' eq2 term_end term_end
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at eq2
      obtain ⟨rfl, -⟩ := munch (endIdT_mem hend) (endIdT_mem hend') (stop_notId hr)
        (stop_notId hr') eq2
      rfl
  | _ => simp at eq

theorem catchT_mem {K' : IdCtx} {cxs : List SExp} {cs : List Catch}
    (hc : List.Forall₂ (CatchT K') cxs cs) : ∀ x ∈ cxs, CatchList x :=
  forall₂_mem_left (fun _ _ h => catchT_head h) hc

theorem prefix_tryTable {I I' : IdCtx} {lx bx cxs body ex : List SExp} {id : Option String}
    {bt : BlockType} {cs : List Catch} {is : Expr} {u u₁ : List FuncType}
    (hl : LabelT I lx id I') (hb : BlockTypeT I bx bt u) (hc : List.Forall₂ (CatchT I) cxs cs)
    (hbody : Instrs I' body is u₁) (hend : EndIdT ex id) (ih : InstrsPrefix body) :
    BlockPrefix (K "try_table" :: (lx ++ bx ++ cxs ++ body ++ K "end" :: ex)) := by
  intro J xs' r r' i' u' h' eq hr hr'
  cases h' with
  | tryTable hl' hb' hc' hbody' hend' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at eq
      obtain ⟨rfl, eq1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (notP_append (fun x hx => tuList_notId (blockTypeT_mem hb x hx))
          (notP_append (fun x hx => catch_not_idAtom (catchT_mem hc x hx))
            (notP_instrs (fun _ h => isStart_not_idAtom h) hbody notId_end)))
        (notP_append (fun x hx => tuList_notId (blockTypeT_mem hb' x hx))
          (notP_append (fun x hx => catch_not_idAtom (catchT_mem hc' x hx))
            (notP_instrs (fun _ h => isStart_not_idAtom h) hbody' notId_end))) eq
      obtain ⟨rfl, eq2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (notP_append (fun x hx h => tuList_not_catch h (catchT_mem hc x hx))
          (next_blockType hbody notTU_end))
        (notP_append (fun x hx h => tuList_not_catch h (catchT_mem hc' x hx))
          (next_blockType hbody' notTU_end)) eq1
      obtain ⟨rfl, eq3⟩ := munch (catchT_mem hc) (catchT_mem hc')
        (notP_instrs (fun _ h => isStart_not_catch h) hbody notCatch_end)
        (notP_instrs (fun _ h => isStart_not_catch h) hbody' notCatch_end) eq2
      obtain rfl := ih hbody' eq3 term_end term_end
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at eq3
      obtain ⟨rfl, -⟩ := munch (endIdT_mem hend) (endIdT_mem hend') (stop_notId hr)
        (stop_notId hr') eq3
      rfl
  | _ => simp at eq

/-- Both prefix properties, by mutual induction. -/
theorem prefix_mutual :
    (∀ {I : IdCtx} {a : List SExp} {e : Expr} {u : List FuncType}, Instrs I a e u →
      InstrsPrefix a) ∧
    (∀ {I : IdCtx} {xs : List SExp} {i : Instr} {u : List FuncType}, BlockInstr I xs i u →
      BlockPrefix xs) := by
  have key := @Instrs.rec (fun _ a _ _ _ => InstrsPrefix a) (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ => True) (fun _ xs _ _ _ => BlockPrefix xs)
    (fun {_} => prefix_nil)
    (fun hp hrest ih => prefix_plain hp hrest ih)
    (fun hb hrest ihb ih => prefix_block hb hrest ihb ih)
    (fun hf _ _ ih => prefix_folded hf ih)
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun {_} => trivial) (fun _ _ _ _ => trivial)
    (fun hl hb hbody hend ih => prefix_bblock hl hb hbody hend ih (.inl rfl))
    (fun hl hb hbody hend ih => prefix_bblock hl hb hbody hend ih (.inr rfl))
    (fun hl hb hthn he₁ hels he₂ ih₁ ih₂ => prefix_if hl hb hthn he₁ hels he₂ ih₁ ih₂)
    (fun hl hb hthn hend ih₁ => prefix_ifNoElse hl hb hthn hend ih₁)
    (fun hl hb hc hbody hend ih => prefix_tryTable hl hb hc hbody hend ih)
  have keyB := @BlockInstr.rec (fun _ a _ _ _ => InstrsPrefix a) (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ => True) (fun _ xs _ _ _ => BlockPrefix xs)
    (fun {_} => prefix_nil)
    (fun hp hrest ih => prefix_plain hp hrest ih)
    (fun hb hrest ihb ih => prefix_block hb hrest ihb ih)
    (fun hf _ _ ih => prefix_folded hf ih)
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun {_} => trivial) (fun _ _ _ _ => trivial)
    (fun hl hb hbody hend ih => prefix_bblock hl hb hbody hend ih (.inl rfl))
    (fun hl hb hbody hend ih => prefix_bblock hl hb hbody hend ih (.inr rfl))
    (fun hl hb hthn he₁ hels he₂ ih₁ ih₂ => prefix_if hl hb hthn he₁ hels he₂ ih₁ ih₂)
    (fun hl hb hthn hend ih₁ => prefix_ifNoElse hl hb hthn hend ih₁)
    (fun hl hb hc hbody hend ih => prefix_tryTable hl hb hc hbody hend ih)
  exact ⟨fun h => key h, fun h => keyB h⟩

theorem instrs_prefix {I J : IdCtx} {a a' r r' : List SExp} {e e' : Expr} {u u' : List FuncType}
    (h : Instrs I a e u) (h' : Instrs J a' e' u') (eq : a ++ r = a' ++ r') (hr : Term r)
    (hr' : Term r') : a = a' := prefix_mutual.1 h h' eq hr hr'

theorem blockInstr_prefix {I J : IdCtx} {xs xs' r r' : List SExp} {i i' : Instr}
    {u u' : List FuncType} (h : BlockInstr I xs i u) (h' : BlockInstr J xs' i' u')
    (eq : xs ++ r = xs' ++ r') (hr : Stop r) (hr' : Stop r') : xs = xs' :=
  prefix_mutual.2 h h' eq hr hr'


/-! ## Functionality of plain instructions -/

theorem memArgTok_not_idx {t : String} {r : List Char} {p : String}
    (hp : p = "offset=" ∨ p = "align=") (e : t.toList = p.toList ++ r) :
    ¬ (NumTok (K t) ∨ IdAtom (K t)) := by
  rintro (h | h)
  · obtain ⟨t', e', c, hc, hd⟩ := h
    simp only [K_inj] at e'; subst e'
    rw [e] at hc
    rcases hp with rfl | rfl <;> simp at hc <;> subst hc <;> revert hd <;> decide
  · exact not_idAtom_K h

theorem memArgT_functional {N : Nat} {xs : List SExp} {a a' : MemArg} (h : MemArgT N xs a)
    (h' : MemArgT N xs a') : a = a' := by
  obtain ⟨ox, ax, rfl, ho, ha⟩ := h
  obtain ⟨ox', ax', e, ho', ha'⟩ := h'
  have offTok : ∀ {ox : List SExp} {a : MemArg}, ((ox = [] ∧ a.offset = 0) ∨ ∃ t r, ox = [K t] ∧
      t.toList = "offset=".toList ++ r ∧ UN 64 r a.offset.val) →
      ∀ x ∈ ox, ∃ t r, x = K t ∧ t.toList = "offset=".toList ++ r := by
    intro ox a ho x hx
    rcases ho with ⟨rfl, -⟩ | ⟨t, r, rfl, e, -⟩
    · simp at hx
    · simp only [List.mem_singleton] at hx; exact ⟨t, r, hx, e⟩
  have alignNot : ∀ {ax : List SExp} {a : MemArg}, ((ax = [] ∧ a.align.val = Nat.log2 N) ∨
      ∃ t r m, ax = [K t] ∧ t.toList = "align=".toList ++ r ∧ UN 64 r m ∧ m = 2 ^ a.align.val) →
      ∀ x ∈ ax.head?, ¬ ∃ t r, x = K t ∧ t.toList = "offset=".toList ++ r := by
    intro ax a ha x hx
    rcases ha with ⟨rfl, -⟩ | ⟨t, r, m, rfl, e, -⟩
    · simp at hx
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; subst hx
      rintro ⟨t', r', e', e''⟩
      simp only [K_inj] at e'; subst e'
      rw [e] at e''
      have := congrArg List.head? e''
      revert this; simp
  obtain ⟨rfl, rfl⟩ := munch (offTok ho) (offTok ho') (alignNot ha) (alignNot ha') e
  obtain ⟨al, off⟩ := a
  obtain ⟨al', off'⟩ := a'
  simp only [MemArg.mk.injEq]
  constructor
  · rcases ha with ⟨rfl, h1⟩ | ⟨t, r, m, rfl, e1, hu, hm⟩ <;>
      rcases ha' with ⟨e2, h2⟩ | ⟨t', r', m', e2, e3, hu', hm'⟩
    · exact Fin.ext (h1.trans h2.symm)
    · simp at e2
    · simp at e2
    · simp only [List.cons.injEq, K_inj, and_true] at e2; subst e2
      rw [e1] at e3; simp only [List.append_cancel_left_eq] at e3; subst e3
      have := un_functional hu hu'
      subst hm hm'
      exact Fin.ext (Nat.pow_right_injective (le_refl 2) this)
  · rcases ho with ⟨rfl, h1⟩ | ⟨t, r, rfl, e1, hu⟩ <;>
      rcases ho' with ⟨e2, h2⟩ | ⟨t', r', e2, e3, hu'⟩
    · exact h1.trans h2.symm
    · simp at e2
    · simp at e2
    · simp only [List.cons.injEq, K_inj, and_true] at e2; subst e2
      rw [e1] at e3; simp only [List.append_cancel_left_eq] at e3; subst e3
      exact Fin.ext (un_functional hu hu')

theorem v128ConstT_functional {xs : List SExp} {b b' : BitVec 128} (h : V128ConstT xs b)
    (h' : V128ConstT xs b') : b = b' := by
  rcases h with ⟨cs, vs, rfl, hc, -, rfl⟩ | ⟨cs, vs, rfl, hc, -, rfl⟩ | ⟨cs, vs, rfl, hc, -, rfl⟩ |
      ⟨cs, vs, rfl, hc, -, rfl⟩ | ⟨cs, vs, rfl, hc, -, rfl⟩ | ⟨cs, vs, rfl, hc, -, rfl⟩ <;>
    rcases h' with ⟨cs', vs', e, hc', -, rfl⟩ | ⟨cs', vs', e, hc', -, rfl⟩ |
      ⟨cs', vs', e, hc', -, rfl⟩ | ⟨cs', vs', e, hc', -, rfl⟩ | ⟨cs', vs', e, hc', -, rfl⟩ |
      ⟨cs', vs', e, hc', -, rfl⟩
  all_goals simp only [List.cons.injEq, K_inj] at e
  all_goals first
    | (exact absurd e.1 (by decide))
    | (obtain ⟨-, rfl⟩ := e
       first
         | rw [forall₂_functional (R := AtomI _) (fun _ _ _ h h' => atomI_functional h h') hc hc']
         | rw [forall₂_functional (R := AtomF _) (fun _ _ _ h h' => atomF_functional h h') hc hc'])

theorem fieldIdxT_functional {I : IdCtx} (hFl : ∀ f ∈ I.fields, Distinct f) {t : TypeIdx}
    {x : SExp} {f f' : FieldIdx} (h : FieldIdxT I t x f) (h' : FieldIdxT I t x f') : f = f' := by
  have hd : Distinct ((I.fields[t.toNat]?).getD []) := by
    cases e : I.fields[t.toNat]? with
    | none => simp [Distinct]
    | some l => exact hFl l (List.mem_of_getElem? e)
  exact idx_functional hd h h'

theorem memOps_nodup : (memOps.map (·.1)).Nodup := by decide +kernel

theorem laneMemOps_nodup : (laneMemOps.map (·.1)).Nodup := by decide +kernel

theorem laneOps_nodup : (laneOps.map (·.1)).Nodup := by decide +kernel

theorem memOps_key {s : String} {N : Nat} {k : MemIdx → MemArg → Instr} (h : (s, N, k) ∈ memOps) :
    s ∈ memOps.map (·.1) := List.mem_map.mpr ⟨_, h, rfl⟩

theorem laneMemOps_key {s : String} {N : Nat} {k : MemIdx → MemArg → LaneIdx → Instr}
    (h : (s, N, k) ∈ laneMemOps) : s ∈ laneMemOps.map (·.1) := List.mem_map.mpr ⟨_, h, rfl⟩

theorem laneOps_key {s : String} {k : LaneIdx → Instr} (h : (s, k) ∈ laneOps) :
    s ∈ laneOps.map (·.1) := List.mem_map.mpr ⟨_, h, rfl⟩

/-- The keyword families of the plain instructions are disjoint. -/
theorem kwFamilies_disjoint :
    (∀ s ∈ memOps.map (·.1), s ∉ explicitKws0 ∧ s ∉ laneMemOps.map (·.1) ∧
      s ∉ laneOps.map (·.1)) ∧
    (∀ s ∈ laneMemOps.map (·.1), s ∉ explicitKws0 ∧ s ∉ laneOps.map (·.1)) ∧
    (∀ s ∈ laneOps.map (·.1), s ∉ explicitKws0) := by
  decide +kernel

theorem nullary_not_explicit {i : Instr} {s : String} (hn : nullaryName i = some s) :
    s ∉ explicitKws := (nullaryName_good hn).1

theorem not_nullary_of_explicit0 {i : Instr} {s : String} (hn : nullaryName i = some s)
    (h : s ∈ explicitKws0) : False := nullary_not_explicit hn (mem_explicit0 h)

/-- Contradictions between plain-instruction keywords. -/
theorem plainKw_contra_mem0 {s : String} {N : Nat} {k : MemIdx → MemArg → Instr}
    (h : (s, N, k) ∈ memOps) (h0 : s ∈ explicitKws0) : False :=
  (kwFamilies_disjoint.1 s (memOps_key h)).1 h0

theorem plainKw_contra_laneMem0 {s : String} {N : Nat} {k : MemIdx → MemArg → LaneIdx → Instr}
    (h : (s, N, k) ∈ laneMemOps) (h0 : s ∈ explicitKws0) : False :=
  (kwFamilies_disjoint.2.1 s (laneMemOps_key h)).1 h0

theorem plainKw_contra_lane0 {s : String} {k : LaneIdx → Instr} (h : (s, k) ∈ laneOps)
    (h0 : s ∈ explicitKws0) : False :=
  kwFamilies_disjoint.2.2 s (laneOps_key h) h0

theorem plainKw_contra_mem_laneMem {s : String} {N N' : Nat} {k : MemIdx → MemArg → Instr}
    {k' : MemIdx → MemArg → LaneIdx → Instr} (h : (s, N, k) ∈ memOps)
    (h' : (s, N', k') ∈ laneMemOps) : False :=
  (kwFamilies_disjoint.1 s (memOps_key h)).2.1 (laneMemOps_key h')

theorem plainKw_contra_mem_lane {s : String} {N : Nat} {k : MemIdx → MemArg → Instr}
    {k' : LaneIdx → Instr} (h : (s, N, k) ∈ memOps) (h' : (s, k') ∈ laneOps) : False :=
  (kwFamilies_disjoint.1 s (memOps_key h)).2.2 (laneOps_key h')

theorem plainKw_contra_laneMem_lane {s : String} {N : Nat} {k : MemIdx → MemArg → LaneIdx → Instr}
    {k' : LaneIdx → Instr} (h : (s, N, k) ∈ laneMemOps) (h' : (s, k') ∈ laneOps) : False :=
  (kwFamilies_disjoint.2.1 s (laneMemOps_key h)).2 (laneOps_key h')

set_option hygiene false in
/-- Close a goal whose two plain-instruction derivations have different keywords. -/
macro "plain_kw_contra" : tactic => `(tactic| first
  | (simp at hxs; done)
  | (have hk := congrArg List.head? hxs
     simp only [List.head?_cons, List.cons_append, List.singleton_append, Option.some.injEq,
       K_inj] at hk
     subst hk
     first
       | exact (not_nullary_of_explicit0 ‹nullaryName _ = some _› (by decide)).elim
       | exact (plainKw_contra_mem0 ‹(_, _, _) ∈ memOps› (by decide)).elim
       | exact (plainKw_contra_laneMem0 ‹(_, _, _) ∈ laneMemOps› (by decide)).elim
       | exact (plainKw_contra_lane0 ‹(_, _) ∈ laneOps› (by decide)).elim
       | exact (nullary_not_explicit ‹nullaryName _ = some _› (memOps_mem ‹(_, _, _) ∈ memOps›)).elim
       | exact (nullary_not_explicit ‹nullaryName _ = some _›
           (laneMemOps_mem ‹(_, _, _) ∈ laneMemOps›)).elim
       | exact (nullary_not_explicit ‹nullaryName _ = some _› (laneOps_mem ‹(_, _) ∈ laneOps›)).elim
       | exact (plainKw_contra_mem_laneMem ‹(_, _, _) ∈ memOps› ‹(_, _, _) ∈ laneMemOps›).elim
       | exact (plainKw_contra_mem_lane ‹(_, _, _) ∈ memOps› ‹(_, _) ∈ laneOps›).elim
       | exact (plainKw_contra_laneMem_lane ‹(_, _, _) ∈ laneMemOps› ‹(_, _) ∈ laneOps›).elim))

theorem idxItem {x : SExp} {names : List (Option String)} {k : IndexKind} {i : Wasm.Idx k}
    (h : Idx names x i) : NumTok x ∨ IdAtom x := idx_shape h

theorem optIdx_items {names : List (Option String)} {k : IndexKind} {xs : List SExp}
    {i : Wasm.Idx k} (h : OptIdx names xs i) : ∀ x ∈ xs, NumTok x ∨ IdAtom x := by
  rcases h with ⟨rfl, -⟩ | ⟨x, rfl, hx⟩
  · simp
  · intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact idx_shape hx

theorem memArgT_notIdx {N : Nat} {xs : List SExp} {a : MemArg} (h : MemArgT N xs a) :
    ∀ x ∈ xs, ¬ (NumTok x ∨ IdAtom x) := by
  obtain ⟨ox, ax, rfl, ho, ha⟩ := h
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · rcases ho with ⟨rfl, -⟩ | ⟨t, r, rfl, e, -⟩
    · simp at hx
    · simp only [List.mem_singleton] at hx; subst hx; exact memArgTok_not_idx (.inl rfl) e
  · rcases ha with ⟨rfl, -⟩ | ⟨t, r, m, rfl, e, -⟩
    · simp at hx
    · simp only [List.mem_singleton] at hx; subst hx; exact memArgTok_not_idx (.inr rfl) e

theorem tu_notIdx {x : SExp} (h : TUList x) : ¬ (NumTok x ∨ IdAtom x) := by
  rintro (h' | h')
  · exact tuList_notNum h h'
  · exact tuList_notId h h'

/-- Splitting an optional index off a type use. -/
theorem optIdx_typeUse_split {I I' : IdCtx} {k : IndexKind} {tx tu tx' tu' : List SExp}
    {t t' : Wasm.Idx k} {x x' : TypeIdx} {ls ls' : List (Option String)} {u u' : List FuncType}
    (ht : OptIdx I.tables tx t) (hu : TypeUseT I tu x ls u)
    (ht' : OptIdx I'.tables tx' t') (hu' : TypeUseT I' tu' x' ls' u')
    (e : tx ++ tu = tx' ++ tu') : tx = tx' ∧ tu = tu' := by
  refine munch (P := fun x => NumTok x ∨ IdAtom x) (optIdx_items ht) (optIdx_items ht') ?_ ?_ e
  · intro y hy; exact tu_notIdx (typeUseT_mem hu y (List.mem_of_mem_head? hy))
  · intro y hy; exact tu_notIdx (typeUseT_mem hu' y (List.mem_of_mem_head? hy))

/-- Splitting an optional index off a memory argument. -/
theorem optIdx_memArg_split {names : List (Option String)} {k : IndexKind} {N : Nat}
    {mx ax mx' ax' : List SExp} {m m' : Wasm.Idx k} {a a' : MemArg}
    (hm : OptIdx names mx m) (ha : MemArgT N ax a) (hm' : OptIdx names mx' m')
    (ha' : MemArgT N ax' a') (e : mx ++ ax = mx' ++ ax') : mx = mx' ∧ ax = ax' := by
  refine munch (P := fun x => NumTok x ∨ IdAtom x) (optIdx_items hm) (optIdx_items hm') ?_ ?_ e
  · intro y hy; exact memArgT_notIdx ha y (List.mem_of_mem_head? hy)
  · intro y hy; exact memArgT_notIdx ha' y (List.mem_of_mem_head? hy)


set_option hygiene false in
/-- Diagonal case: one index immediate. -/
macro "plain_diag1" hd:term : tactic => `(tactic| (
  rename_i hx'
  simp only [List.cons.injEq, and_true, true_and] at hxs
  subst hxs
  obtain rfl := idx_functional $hd hx hx'
  exact ⟨rfl, rfl⟩))

set_option hygiene false in
/-- Diagonal case: an optional index immediate. -/
macro "plain_diagOpt" hd:term : tactic => `(tactic| (
  rename_i hx'
  simp only [List.cons.injEq, true_and] at hxs
  subst hxs
  obtain rfl := optIdx_functional $hd hx hx'
  exact ⟨rfl, rfl⟩))

set_option hygiene false in
/-- Diagonal case: two index immediates. -/
macro "plain_diag2" hd₁:term "," hd₂:term : tactic => `(tactic| (
  rename_i hx' hy'
  simp only [List.cons.injEq, and_true, true_and] at hxs
  obtain ⟨rfl, rfl⟩ := hxs
  obtain rfl := idx_functional $hd₁ hx hx'
  obtain rfl := idx_functional $hd₂ hy hy'
  exact ⟨rfl, rfl⟩))

set_option maxHeartbeats 4000000 in
/-- For a fixed context with distinct names, a plain instruction is determined
by its items. -/
theorem plain_functional' {I : IdCtx} (hI : I.Ok) {xs : List SExp} {i : Instr}
    {u : List FuncType} (h : Plain I xs i u) :
    ∀ {ys : List SExp} {i' : Instr} {u' : List FuncType}, Plain I ys i' u' → xs = ys →
      i = i' ∧ u = u' := by
  obtain ⟨hT, hTg, hG, hM, hTb, hF, hD, hE, hL, hLb, hFl⟩ := hI
  cases h with
  | nullary hn =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hn'
      simp only [List.cons.injEq, K_inj, and_true] at hxs; subst hxs
      exact ⟨nullaryName_injective hn hn', rfl⟩
  | select =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      · exact ⟨rfl, rfl⟩
      · rename_i rxs ts hne hc
        simp only [List.cons.injEq, true_and] at hxs
        exact absurd hxs.symm hne
  | selectTyped hne hc =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      · simp only [List.cons.injEq, true_and] at hxs
        exact absurd hxs hne
      · rename_i rxs' ts' hne' hc'
        simp only [List.cons.injEq, true_and] at hxs; subst hxs
        rw [concat_functional (R := ResultT I) (fun _ _ _ h h' => resultT_functional hT h h') hc hc']
        exact ⟨rfl, rfl⟩
  | br hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hLb
  | brIf hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hLb
  | brTable hxs₀ _ =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i ls' l' hxs₁ _
      simp only [List.cons.injEq, true_and] at hxs; subst hxs
      have := forall₂_functional (R := Idx I.labels) (fun _ _ _ h h' => idx_functional hLb h h')
        hxs₀ hxs₁
      obtain ⟨rfl, h2⟩ := List.append_inj' this rfl
      simp only [List.cons.injEq, and_true] at h2; subst h2
      exact ⟨rfl, rfl⟩
  | brOnNull hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hLb
  | brOnNonNull hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hLb
  | brOnCast hx h1 h2 =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hx' h1' h2'
      simp only [List.cons.injEq, and_true, true_and] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      rw [idx_functional hLb hx hx', refTypeT_functional hT h1 h1', refTypeT_functional hT h2 h2']
      exact ⟨rfl, rfl⟩
  | brOnCastFail hx h1 h2 =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hx' h1' h2'
      simp only [List.cons.injEq, and_true, true_and] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      rw [idx_functional hLb hx hx', refTypeT_functional hT h1 h1', refTypeT_functional hT h2 h2']
      exact ⟨rfl, rfl⟩
  | call hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hF
  | callRef hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | callIndirect ht hu _ =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i ht' _ _
      have hu' := ‹TypeUseT I _ _ _ u'›
      simp only [List.cons.injEq, true_and] at hxs
      obtain ⟨rfl, rfl⟩ := optIdx_typeUse_split ht hu ht' hu' hxs
      obtain rfl := optIdx_functional hTb ht ht'
      obtain ⟨rfl, -, rfl⟩ := typeUseT_functional hT hu hu'
      exact ⟨rfl, rfl⟩
  | returnCall hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hF
  | returnCallRef hx =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | returnCallIndirect ht hu _ =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i ht' _ _
      have hu' := ‹TypeUseT I _ _ _ u'›
      simp only [List.cons.injEq, true_and] at hxs
      obtain ⟨rfl, rfl⟩ := optIdx_typeUse_split ht hu ht' hu' hxs
      obtain rfl := optIdx_functional hTb ht ht'
      obtain ⟨rfl, -, rfl⟩ := typeUseT_functional hT hu hu'
      exact ⟨rfl, rfl⟩
  | throw hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hTg
  | localGet hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hL
  | localSet hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hL
  | localTee hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hL
  | globalGet hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hG
  | globalSet hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hG
  | tableGet hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diagOpt hTb
  | tableSet hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diagOpt hTb
  | tableSize hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diagOpt hTb
  | tableGrow hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diagOpt hTb
  | tableFill hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diagOpt hTb
  | tableCopy hx hy =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag2 hTb, hTb
  | tableCopy0 =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); exact ⟨rfl, rfl⟩
  | tableInit ht hy =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i ht' hy'
      simp only [List.cons.injEq, true_and] at hxs
      obtain ⟨rfl, h2⟩ := List.append_inj' hxs (by
        rcases ht with ⟨rfl, -⟩ | ⟨x, rfl, -⟩ <;> rcases ht' with ⟨rfl, -⟩ | ⟨x', rfl, -⟩ <;>
          simp_all)
      simp only [List.cons.injEq, and_true] at h2; subst h2
      rw [optIdx_functional hTb ht ht', idx_functional hE hy hy']
      exact ⟨rfl, rfl⟩
  | elemDrop hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hE
  | memOp hm hmx ha =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hm' hmx' ha'
      simp only [List.cons.injEq, K_inj] at hxs
      obtain ⟨rfl, hxs⟩ := hxs
      have := lookup_unique memOps_nodup hm hm'
      simp only [Prod.mk.injEq] at this; obtain ⟨rfl, rfl⟩ := this
      obtain ⟨rfl, rfl⟩ := optIdx_memArg_split hmx ha hmx' ha' hxs
      rw [optIdx_functional hM hmx hmx', memArgT_functional ha ha']
      exact ⟨rfl, rfl⟩
  | laneMemOp hm hmx ha hl =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hm' hmx' ha' hl'
      simp only [List.cons.injEq, K_inj] at hxs
      obtain ⟨rfl, hxs⟩ := hxs
      have := lookup_unique laneMemOps_nodup hm hm'
      simp only [Prod.mk.injEq] at this; obtain ⟨rfl, rfl⟩ := this
      obtain ⟨hxs2, h2⟩ := List.append_inj' hxs rfl
      simp only [List.cons.injEq, and_true] at h2; subst h2
      obtain ⟨rfl, rfl⟩ := optIdx_memArg_split hmx ha hmx' ha' hxs2
      rw [optIdx_functional hM hmx hmx', memArgT_functional ha ha',
        Fin.ext (atomU_functional hl hl')]
      exact ⟨rfl, rfl⟩
  | memorySize hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diagOpt hM
  | memoryGrow hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diagOpt hM
  | memoryFill hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diagOpt hM
  | memoryCopy hx hy =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag2 hM, hM
  | memoryCopy0 =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); exact ⟨rfl, rfl⟩
  | memoryInit hm hy =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hm' hy'
      simp only [List.cons.injEq, true_and] at hxs
      obtain ⟨rfl, h2⟩ := List.append_inj' hxs (by
        rcases hm with ⟨rfl, -⟩ | ⟨x, rfl, -⟩ <;> rcases hm' with ⟨rfl, -⟩ | ⟨x', rfl, -⟩ <;>
          simp_all)
      simp only [List.cons.injEq, and_true] at h2; subst h2
      rw [optIdx_functional hM hm hm', idx_functional hD hy hy']
      exact ⟨rfl, rfl⟩
  | dataDrop hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hD
  | refNull hh =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hh'
      simp only [List.cons.injEq, and_true, true_and] at hxs; subst hxs
      rw [heapTypeT_functional hT hh hh']; exact ⟨rfl, rfl⟩
  | refFunc hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hF
  | refTest hr =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hr'
      simp only [List.cons.injEq, and_true, true_and] at hxs; subst hxs
      rw [refTypeT_functional hT hr hr']; exact ⟨rfl, rfl⟩
  | refCast hr =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hr'
      simp only [List.cons.injEq, and_true, true_and] at hxs; subst hxs
      rw [refTypeT_functional hT hr hr']; exact ⟨rfl, rfl⟩
  | structNew hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | structNewDefault hx =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | structGet hx hy =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hx' hy'
      simp only [List.cons.injEq, and_true, true_and] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain rfl := idx_functional hT hx hx'
      rw [fieldIdxT_functional hFl hy hy']; exact ⟨rfl, rfl⟩
  | structGetS hx hy =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hx' hy'
      simp only [List.cons.injEq, and_true, true_and] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain rfl := idx_functional hT hx hx'
      rw [fieldIdxT_functional hFl hy hy']; exact ⟨rfl, rfl⟩
  | structGetU hx hy =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hx' hy'
      simp only [List.cons.injEq, and_true, true_and] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain rfl := idx_functional hT hx hx'
      rw [fieldIdxT_functional hFl hy hy']; exact ⟨rfl, rfl⟩
  | structSet hx hy =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hx' hy'
      simp only [List.cons.injEq, and_true, true_and] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain rfl := idx_functional hT hx hx'
      rw [fieldIdxT_functional hFl hy hy']; exact ⟨rfl, rfl⟩
  | arrayNew hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | arrayNewDefault hx =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | arrayNewFixed hx hy =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hx' hy'
      simp only [List.cons.injEq, and_true, true_and] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      rw [idx_functional hT hx hx', atomU32_functional hy hy']; exact ⟨rfl, rfl⟩
  | arrayNewData hx hy =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag2 hT, hD
  | arrayNewElem hx hy =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag2 hT, hE
  | arrayGet hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | arrayGetS hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | arrayGetU hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | arraySet hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | arrayFill hx => intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag1 hT
  | arrayCopy hx hy =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag2 hT, hT
  | arrayInitData hx hy =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag2 hT, hD
  | arrayInitElem hx hy =>
      intro ys i' u' h' hxs; cases h' <;> (try plain_kw_contra); plain_diag2 hT, hE
  | i32Const hc =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hc'
      simp only [List.cons.injEq, and_true, true_and] at hxs; subst hxs
      rw [atomI_functional hc hc']; exact ⟨rfl, rfl⟩
  | i64Const hc =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hc'
      simp only [List.cons.injEq, and_true, true_and] at hxs; subst hxs
      rw [atomI_functional hc hc']; exact ⟨rfl, rfl⟩
  | f32Const hc =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hc'
      simp only [List.cons.injEq, and_true, true_and] at hxs; subst hxs
      rw [atomF_functional hc hc']; exact ⟨rfl, rfl⟩
  | f64Const hc =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hc'
      simp only [List.cons.injEq, and_true, true_and] at hxs; subst hxs
      rw [atomF_functional hc hc']; exact ⟨rfl, rfl⟩
  | v128Const hv =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hv'
      simp only [List.cons.injEq, true_and] at hxs; subst hxs
      rw [v128ConstT_functional hv hv']; exact ⟨rfl, rfl⟩
  | shuffle hl _ =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hl' _
      simp only [List.cons.injEq, true_and] at hxs; subst hxs
      rw [forall₂_functional (R := fun x (l : LaneIdx) => AtomU 8 x l.val)
        (fun _ _ _ h h' => Fin.ext (atomU_functional h h')) hl hl']
      exact ⟨rfl, rfl⟩
  | lane hl hx =>
      intro ys i' u' h' hxs
      cases h' <;> (try plain_kw_contra)
      rename_i hl' hx'
      simp only [List.cons.injEq, K_inj, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain rfl := lookup_unique laneOps_nodup hl hl'
      rw [Fin.ext (atomU_functional hx hx')]; exact ⟨rfl, rfl⟩


set_option maxHeartbeats 4000000 in
/-- Across contexts resolving type identifiers alike, a plain instruction uses the
same function types implicitly. -/
theorem plain_uses {I : IdCtx} (hT : Distinct I.types) {xs : List SExp} {i : Instr}
    {u : List FuncType} (h : Plain I xs i u) :
    ∀ {I' : IdCtx} {ys : List SExp} {i' : Instr} {u' : List FuncType}, TypesEq I I' →
      Plain I' ys i' u' → xs = ys → u = u' := by
  cases h <;> intro I' ys i' u' hE h' hxs <;> cases h' <;> first | rfl | plain_kw_contra | skip
  · rename_i tx tu tb t ls ht _ hu tx' tu' tb' t' ls' ht' _ hu'
    simp only [List.cons.injEq, true_and] at hxs
    obtain ⟨rfl, rfl⟩ := optIdx_typeUse_split ht hu ht' hu' hxs
    exact typeUseT_uses hT hE hu hu'
  · rename_i tx tu tb t ls ht _ hu tx' tu' tb' t' ls' ht' _ hu'
    simp only [List.cons.injEq, true_and] at hxs
    obtain ⟨rfl, rfl⟩ := optIdx_typeUse_split ht hu ht' hu' hxs
    exact typeUseT_uses hT hE hu hu'

/-! ## Block types, labels and catches -/

theorem blockTypeT_functional {I : IdCtx} (hT : Distinct I.types) {xs : List SExp}
    {bt bt' : BlockType} {u u' : List FuncType} (h : BlockTypeT I xs bt u)
    (h' : BlockTypeT I xs bt' u') : bt = bt' ∧ u = u' := by
  have cf := fun {ts ts' : List ValType} (h : ValueFormT I xs ts) (h' : ValueFormT I xs ts') =>
    valueFormT_functional hT h h'
  rcases h with ⟨ts, hc, rfl, rfl, rfl⟩ | ⟨ts, t, hc, rfl, rfl, rfl⟩ |
      ⟨x, ls, hu, -, rfl, hn⟩ <;>
    rcases h' with ⟨ts', hc', rfl, rfl, rfl⟩ | ⟨ts', t', hc', rfl, rfl, rfl⟩ |
      ⟨x', ls', hu', -, rfl, hn'⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd (cf hc hc') (by simp)
  · exact absurd ⟨_, hc, by simp⟩ hn'
  · exact absurd (cf hc hc') (by simp)
  · have := cf hc hc'; simp only [List.cons.injEq, and_true] at this; subst this
    exact ⟨rfl, rfl⟩
  · exact absurd ⟨_, hc, by simp⟩ hn'
  · exact absurd ⟨_, hc', by simp⟩ hn
  · exact absurd ⟨_, hc', by simp⟩ hn
  · obtain ⟨rfl, -, rfl⟩ := typeUseT_functional hT hu hu'; exact ⟨rfl, rfl⟩

theorem blockTypeT_uses {I I' : IdCtx} (hT : Distinct I.types) (hE : TypesEq I I')
    {xs : List SExp} {bt bt' : BlockType} {u u' : List FuncType} (h : BlockTypeT I xs bt u)
    (h' : BlockTypeT I' xs bt' u') : u = u' := by
  rcases h with ⟨ts, hc, rfl, rfl, rfl⟩ | ⟨ts, t, hc, rfl, rfl, rfl⟩ |
      ⟨x, ls, hu, -, rfl, hn⟩ <;>
    rcases h' with ⟨ts', hc', rfl, rfl, rfl⟩ | ⟨ts', t', hc', rfl, rfl, rfl⟩ |
      ⟨x', ls', hu', -, rfl, hn'⟩
  all_goals first | rfl | skip
  · rw [valueFormT_eq hE] at hc; exact absurd ⟨_, hc, by simp⟩ hn'
  · rw [valueFormT_eq hE] at hc; exact absurd ⟨_, hc, by simp⟩ hn'
  · rw [← valueFormT_eq hE] at hc'; exact absurd ⟨_, hc', by simp⟩ hn
  · rw [← valueFormT_eq hE] at hc'; exact absurd ⟨_, hc', by simp⟩ hn
  · exact typeUseT_uses hT hE hu hu'

theorem distinct_of_lookup :
    ∀ {names : List (Option String)},
      (∀ (i j : Nat) (n : String), names[i]? = some (some n) → names[j]? = some (some n) → i = j) → Distinct names
  | [], _ => by simp [Distinct]
  | a :: names, h => by
      have h' : ∀ (i j : Nat) (n : String), names[i]? = some (some n) → names[j]? = some (some n) → i = j :=
        fun i j n hi hj => by
          have := h (i + 1) (j + 1) n (by simpa using hi) (by simpa using hj); omega
      have ih := distinct_of_lookup h'
      unfold Distinct at ih ⊢
      cases a with
      | none => simpa using ih
      | some m =>
          simp only [List.filterMap_cons, id_eq, List.nodup_cons]
          refine ⟨fun hm => ?_, ih⟩
          simp only [List.mem_filterMap] at hm
          obtain ⟨o, ho, rfl⟩ := hm
          obtain ⟨j, hj, hjo⟩ := List.getElem_of_mem ho
          have := h 0 (j + 1) m (by simp) (by simp [hj, hjo])
          omega

theorem distinct_iff {names : List (Option String)} :
    Distinct names ↔ ∀ (i j : Nat) (n : String), names[i]? = some (some n) → names[j]? = some (some n) → i = j :=
  ⟨fun h _ _ _ hi hj => distinct_lookup_unique h hi hj, distinct_of_lookup⟩

theorem labelT_functional {I : IdCtx} (hLb : Distinct I.labels) {lx : List SExp}
    {id id' : Option String} {I₁ I₂ : IdCtx} (h : LabelT I lx id I₁) (h' : LabelT I lx id' I₂) :
    id = id' ∧ I₁ = I₂ := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨n, rfl, rfl, hn, rfl⟩ | ⟨n, x, rfl, rfl, hx, rfl⟩ <;>
    rcases h' with ⟨e, rfl, rfl⟩ | ⟨n', e, rfl, hn', rfl⟩ | ⟨n', x', e, rfl, hx', rfl⟩
  all_goals simp only [List.cons.injEq, Formats.SExp2.atom.injEq, Atom.id.injEq, and_true,
    List.ne_cons_self, List.cons_ne_nil] at e
  · exact ⟨rfl, rfl⟩
  · subst e; exact ⟨rfl, rfl⟩
  · subst e; exact absurd (List.mem_of_getElem? hx') hn
  · subst e; exact absurd (List.mem_of_getElem? hx) hn'
  · subst e; obtain rfl := distinct_lookup_unique hLb hx hx'; exact ⟨rfl, rfl⟩

theorem labelT_types {I I' : IdCtx} {lx : List SExp} {id : Option String} (h : LabelT I lx id I') :
    I'.types = I.types := by
  rcases h with ⟨-, -, rfl⟩ | ⟨n, -, -, -, rfl⟩ | ⟨n, x, -, -, -, rfl⟩ <;> rfl

theorem labelT_typesEq {I J I' J' : IdCtx} {lx lx' : List SExp} {id id' : Option String}
    (hE : TypesEq I J) (h : LabelT I lx id I') (h' : LabelT J lx' id' J') : TypesEq I' J' := by
  intro x i; rw [labelT_types h, labelT_types h']; exact hE x i

theorem labelT_ok {I I' : IdCtx} {lx : List SExp} {id : Option String} (hI : I.Ok)
    (h : LabelT I lx id I') : I'.Ok := by
  obtain ⟨hT, hTg, hG, hM, hTb, hF, hD, hE, hL, hLb, hFl⟩ := hI
  have hlab : Distinct I'.labels := by
    rcases h with ⟨-, -, rfl⟩ | ⟨n, -, -, hn, rfl⟩ | ⟨n, x, -, -, hx, rfl⟩
    · unfold Distinct at hLb ⊢; simpa using hLb
    · unfold Distinct at hLb ⊢
      simp only [List.filterMap_cons, id_eq, List.nodup_cons, List.mem_filterMap]
      refine ⟨?_, hLb⟩
      rintro ⟨o, ho, e⟩; cases o with
      | none => simp at e
      | some m => simp only [Option.some.injEq] at e; subst e; exact hn ho
    · rw [distinct_iff] at hLb ⊢
      have hx' : x < I.labels.length := by
        rcases Nat.lt_or_ge x I.labels.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hx
      intro i j m hi hj
      cases i <;> cases j
      · rfl
      · rename_i j
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
        subst hi
        rw [List.getElem?_set] at hj
        split at hj
        · simp at hj
        · have := hLb _ _ _ hx hj; omega
      · rename_i i
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
        subst hj
        rw [List.getElem?_set] at hi
        split at hi
        · simp at hi
        · have := hLb _ _ _ hx hi; omega
      · rename_i i j
        simp only [List.getElem?_cons_succ] at hi hj
        rw [List.getElem?_set] at hi hj
        split at hi
        · simp at hi
        · split at hj
          · simp at hj
          · have := hLb _ _ _ hi hj; omega
  rcases h with ⟨-, -, rfl⟩ | ⟨n, -, -, -, rfl⟩ | ⟨n, x, -, -, -, rfl⟩ <;>
    exact ⟨hT, hTg, hG, hM, hTb, hF, hD, hE, hL, hlab, hFl⟩

theorem catchT_functional {I : IdCtx} (hI : I.Ok) {x : SExp} {c c' : Catch} (h : CatchT I x c)
    (h' : CatchT I x c') : c = c' := by
  obtain ⟨hT, hTg, hG, hM, hTb, hF, hD, hE, hL, hLb, hFl⟩ := hI
  rcases h with ⟨tx, lx, t, l, rfl, ht, hl, rfl⟩ | ⟨tx, lx, t, l, rfl, ht, hl, rfl⟩ |
      ⟨lx, l, rfl, hl, rfl⟩ | ⟨lx, l, rfl, hl, rfl⟩ <;>
    rcases h' with ⟨tx', lx', t', l', e, ht', hl', rfl⟩ | ⟨tx', lx', t', l', e, ht', hl', rfl⟩ |
      ⟨lx', l', e, hl', rfl⟩ | ⟨lx', l', e, hl', rfl⟩
  all_goals simp at e
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := e
       rw [idx_functional hTg ht ht', idx_functional hLb hl hl'])
    | (subst e; rw [idx_functional hLb hl hl'])

theorem catchT_forall₂_functional {I : IdCtx} (hI : I.Ok) {xs : List SExp} {cs cs' : List Catch}
    (h : List.Forall₂ (CatchT I) xs cs) (h' : List.Forall₂ (CatchT I) xs cs') : cs = cs' :=
  forall₂_functional (R := CatchT I) (fun _ _ _ h h' => catchT_functional hI h h') h h'


/-! ## Functionality of instruction sequences -/

theorem instrs_stop {I : IdCtx} {r : List SExp} {e : Expr} {u : List FuncType}
    (h : Instrs I r e u) : Stop r := by
  simpa using stop_instrs h (r := []) (by simp [Stop])

theorem foldedSeq_mem {I : IdCtx} {xs : List SExp} {e : Expr} {u : List FuncType}
    (h : FoldedSeq I xs e u) : ∀ x ∈ xs, IsStart x := by
  induction xs generalizing e u with
  | nil => simp
  | cons y ys ih =>
      cases h with
      | cons hf hrest =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · obtain ⟨s, ys, rfl, hs⟩ := folded_shape hf; exact .inr ⟨s, ys, rfl, hs⟩
        · exact ih hrest x hx

theorem notP_instrs_nil {P : SExp → Prop} (hP : ∀ x, IsStart x → ¬ P x) {I : IdCtx}
    {body : List SExp} {e : Expr} {u : List FuncType} (h : Instrs I body e u) : NotP P body := by
  simpa using notP_instrs hP h (r := []) notP_nil

/-- The common part of block-like instructions: label and block type. -/
theorem block_common {I I' I₁ I₁' : IdCtx} {lx bx : List SExp} {id id' : Option String}
    {bt bt' : BlockType} {u u' : List FuncType} (hl : LabelT I lx id I₁) (hb : BlockTypeT I bx bt u)
    (hl' : LabelT I' lx id' I₁') (hb' : BlockTypeT I' bx bt' u') (hE : TypesEq I I')
    (hT : Distinct I.types) :
    u = u' ∧ TypesEq I₁ I₁' ∧ Distinct I₁.types ∧
      (I = I' → I.Ok → bt = bt' ∧ I₁ = I₁' ∧ I₁.Ok) := by
  refine ⟨blockTypeT_uses hT hE hb hb', labelT_typesEq hE hl hl', by rw [labelT_types hl]; exact hT,
    fun hI hok => ?_⟩
  subst hI
  obtain ⟨-, rfl⟩ := labelT_functional hok.2.2.2.2.2.2.2.2.2.1 hl hl'
  exact ⟨(blockTypeT_functional hT hb hb').1, rfl, labelT_ok hok hl⟩

/-- Motive for instruction sequences. -/
def FunI (I : IdCtx) (a : List SExp) (e : Expr) (u : List FuncType) : Prop :=
  ∀ {I' : IdCtx} {a' : List SExp} {e' : Expr} {u' : List FuncType}, Instrs I' a' e' u' → a = a' →
    TypesEq I I' → Distinct I.types → u = u' ∧ (I = I' → I.Ok → e = e')

/-- Motive for folded instructions. -/
def FunF (I : IdCtx) (x : SExp) (e : Expr) (u : List FuncType) : Prop :=
  ∀ {I' : IdCtx} {x' : SExp} {e' : Expr} {u' : List FuncType}, Folded I' x' e' u' → x = x' →
    TypesEq I I' → Distinct I.types → u = u' ∧ (I = I' → I.Ok → e = e')

/-- Motive for sequences of folded instructions. -/
def FunS (I : IdCtx) (xs : List SExp) (e : Expr) (u : List FuncType) : Prop :=
  ∀ {I' : IdCtx} {xs' : List SExp} {e' : Expr} {u' : List FuncType}, FoldedSeq I' xs' e' u' →
    xs = xs' → TypesEq I I' → Distinct I.types → u = u' ∧ (I = I' → I.Ok → e = e')

/-- Motive for block instructions. -/
def FunB (I : IdCtx) (xs : List SExp) (i : Instr) (u : List FuncType) : Prop :=
  ∀ {I' : IdCtx} {xs' : List SExp} {i' : Instr} {u' : List FuncType}, BlockInstr I' xs' i' u' →
    xs = xs' → TypesEq I I' → Distinct I.types → u = u' ∧ (I = I' → I.Ok → i = i')

theorem fun_nil {I : IdCtx} : FunI I [] [] [] := by
  intro I' a' e' u' h' ha hE hT
  cases h' with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | plain hp' _ => obtain ⟨s, ys, rfl, -, -⟩ := plain_shape hp'; simp at ha
  | block hb' _ => obtain ⟨s, ys, rfl, -⟩ := blockInstr_shape hb'; simp at ha
  | folded => simp at ha

theorem fun_plain {I : IdCtx} {xs rest : List SExp} {i : Instr} {is : Expr} {u u₁ : List FuncType}
    (hp : Plain I xs i u) (hrest : Instrs I rest is u₁) (ih : FunI I rest is u₁) :
    FunI I (xs ++ rest) (i :: is) (u ++ u₁) := by
  intro I' a' e' u' h' ha hE hT
  obtain ⟨s, ys, rfl, hs, hys⟩ := plain_shape hp
  cases h' with
  | nil => simp at ha
  | plain hp' hrest' =>
      obtain ⟨s', ys', rfl, hs', hys'⟩ := plain_shape hp'
      simp only [List.cons_append, List.cons.injEq, K_inj] at ha
      obtain ⟨rfl, ha⟩ := ha
      obtain ⟨rfl, rfl⟩ := munch hys hys' (instrs_stop hrest) (instrs_stop hrest') ha
      have hu := plain_uses hT hp hE hp' rfl
      obtain ⟨hu1, he1⟩ := ih hrest' rfl hE hT
      refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
      subst hI
      obtain ⟨rfl, -⟩ := plain_functional' hok hp hp' rfl
      rw [he1 rfl hok]
  | block hb' _ =>
      obtain ⟨s', ys', rfl, hs'⟩ := blockInstr_shape hb'
      simp only [List.cons_append, List.cons.injEq, K_inj] at ha
      obtain ⟨rfl, -⟩ := ha
      exact absurd hs' hs.ok.2
  | folded hf' _ =>
      obtain ⟨s', ys', rfl, -⟩ := folded_shape hf'
      simp at ha

theorem fun_block {I : IdCtx} {xs rest : List SExp} {i : Instr} {is : Expr} {u u₁ : List FuncType}
    (hb : BlockInstr I xs i u) (hrest : Instrs I rest is u₁) (ihb : FunB I xs i u)
    (ih : FunI I rest is u₁) : FunI I (xs ++ rest) (i :: is) (u ++ u₁) := by
  intro I' a' e' u' h' ha hE hT
  cases h' with
  | nil => obtain ⟨s, ys, rfl, -⟩ := blockInstr_shape hb; simp at ha
  | plain hp' _ =>
      obtain ⟨s, ys, rfl, hs⟩ := blockInstr_shape hb
      obtain ⟨s', ys', rfl, hs', -⟩ := plain_shape hp'
      simp only [List.cons_append, List.cons.injEq, K_inj] at ha
      obtain ⟨rfl, -⟩ := ha
      exact absurd hs hs'.ok.2
  | block hb' hrest' =>
      obtain rfl := blockInstr_prefix hb hb' ha (instrs_stop hrest) (instrs_stop hrest')
      simp only [List.append_cancel_left_eq] at ha; subst ha
      obtain ⟨hu, he⟩ := ihb hb' rfl hE hT
      obtain ⟨hu1, he1⟩ := ih hrest' rfl hE hT
      refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
      rw [he hI hok, he1 hI hok]
  | folded hf' _ =>
      obtain ⟨s, ys, rfl, -⟩ := blockInstr_shape hb
      obtain ⟨s', ys', rfl, -⟩ := folded_shape hf'
      simp at ha

theorem fun_folded {I : IdCtx} {x : SExp} {rest : List SExp} {is is' : Expr}
    {u u₁ : List FuncType} (hf : Folded I x is u) (_hrest : Instrs I rest is' u₁)
    (ihf : FunF I x is u) (ih : FunI I rest is' u₁) : FunI I (x :: rest) (is ++ is') (u ++ u₁) := by
  intro I' a' e' u' h' ha hE hT
  obtain ⟨s, ys, rfl, -⟩ := folded_shape hf
  cases h' with
  | nil => simp at ha
  | plain hp' _ => obtain ⟨s', ys', rfl, -, -⟩ := plain_shape hp'; simp at ha
  | block hb' _ => obtain ⟨s', ys', rfl, -⟩ := blockInstr_shape hb'; simp at ha
  | folded hf' hrest' =>
      simp only [List.cons.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      obtain ⟨hu, he⟩ := ihf hf' rfl hE hT
      obtain ⟨hu1, he1⟩ := ih hrest' rfl hE hT
      refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
      rw [he hI hok, he1 hI hok]

theorem fun_fplain {I : IdCtx} {s : String} {imms subs : List SExp} {i : Instr} {is : Expr}
    {u u₁ : List FuncType} (hp : Plain I (K s :: imms) i u) (hsubs : Instrs I subs is u₁)
    (ih : FunI I subs is u₁) : FunF I (L (K s :: (imms ++ subs))) (is ++ [i]) (u₁ ++ u) := by
  intro I' x' e' u' h' hx hE hT
  obtain ⟨s0, ys, e0, hs, hys⟩ := plain_shape hp
  simp only [List.cons.injEq, K_inj] at e0; obtain ⟨rfl, rfl⟩ := e0
  cases h'
  case plain hp' hsubs' =>
      simp only [L_inj, List.cons.injEq, K_inj] at hx
      obtain ⟨rfl, hx⟩ := hx
      obtain ⟨s1, ys', e1, -, hys'⟩ := plain_shape hp'
      simp only [List.cons.injEq, K_inj] at e1; obtain ⟨-, rfl⟩ := e1
      obtain ⟨rfl, rfl⟩ := munch hys hys' (instrs_stop hsubs) (instrs_stop hsubs') hx
      have hu := plain_uses hT hp hE hp' rfl
      obtain ⟨hu1, he1⟩ := ih hsubs' rfl hE hT
      refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
      subst hI
      obtain ⟨rfl, -⟩ := plain_functional' hok hp hp' rfl
      rw [he1 rfl hok]
  all_goals
    simp only [L_inj, List.cons.injEq, K_inj] at hx
    obtain ⟨rfl, -⟩ := hx
    exact absurd (by decide) hs.ok.2

theorem fun_fblock {I I₁ : IdCtx} {lx bx body : List SExp} {id : Option String}
    {bt : BlockType} {is : Expr} {u u₁ : List FuncType} {kw : String}
    {mk : BlockType → Expr → Instr}
    (hk : (kw = "block" ∧ mk = Instr.block) ∨ (kw = "loop" ∧ mk = Instr.loop))
    (hl : LabelT I lx id I₁) (hb : BlockTypeT I bx bt u) (hbody : Instrs I₁ body is u₁)
    (ih : FunI I₁ body is u₁) : FunF I (L (K kw :: (lx ++ bx ++ body))) [mk bt is] (u ++ u₁) := by
  intro I' x' e' u' h' hx hE hT
  have main : ∀ {I₁' : IdCtx} {bx' body' : List SExp} {id' : Option String} {bt' : BlockType}
      {is' : Expr} {uu uu₁ : List FuncType}, LabelT I' lx id' I₁' → BlockTypeT I' bx' bt' uu →
      Instrs I₁' body' is' uu₁ → bx ++ body = bx' ++ body' →
      u ++ u₁ = uu ++ uu₁ ∧ (I = I' → I.Ok → bt = bt' ∧ is = is') := by
    intro I₁' bx' body' id' bt' is' uu uu₁ hl' hb' hbody' e
    obtain ⟨rfl, rfl⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
      (notP_instrs_nil (fun _ h => isStart_not_tuList h) hbody)
      (notP_instrs_nil (fun _ h => isStart_not_tuList h) hbody') e
    obtain ⟨hu, hE₁, hT₁, hfun⟩ := block_common hl hb hl' hb' hE hT
    obtain ⟨hu1, he1⟩ := ih hbody' rfl hE₁ hT₁
    refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
    obtain ⟨rfl, hI₁, hok₁⟩ := hfun hI hok
    exact ⟨rfl, he1 hI₁ hok₁⟩
  have splitL : ∀ {lx' bx' body' : List SExp} {id' : Option String} {I₁' : IdCtx}
      {bt' : BlockType} {is' : Expr} {uu uu₁ : List FuncType}, LabelT I' lx' id' I₁' →
      BlockTypeT I' bx' bt' uu → Instrs I₁' body' is' uu₁ →
      lx ++ (bx ++ body) = lx' ++ (bx' ++ body') → lx = lx' ∧ bx ++ body = bx' ++ body' := by
    intro lx' bx' body' id' I₁' bt' is' uu uu₁ hl' hb' hbody' e
    have n1 := next_label hb hbody (r := []) notP_nil
    have n2 := next_label hb' hbody' (r := []) notP_nil
    simp only [List.append_nil] at n1 n2
    exact munch (labelT_mem hl) (labelT_mem hl') n1 n2 e
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases h'
  all_goals simp only [L_inj, List.cons.injEq, K_inj, List.append_assoc] at hx
  all_goals first
    | (exact absurd hx.1 (by decide))
    | (obtain ⟨-, hx⟩ := hx
       rename_i hbody' hl' hb'
       obtain ⟨rfl, hx2⟩ := splitL hl' hb' hbody' hx
       obtain ⟨hu, he⟩ := main hl' hb' hbody' hx2
       refine ⟨hu, fun hI hok => ?_⟩
       obtain ⟨rfl, rfl⟩ := he hI hok
       rfl)
    | (obtain ⟨rfl, -⟩ := hx
       obtain ⟨s', ys', e1, hs', -⟩ := plain_shape ‹Plain _ _ _ _›
       simp only [List.cons.injEq, K_inj] at e1
       exact absurd (by rw [← e1.1]; decide) hs'.ok.2)


theorem notTU_headKw {s : String} {x : SExp} (hs : s ≠ "type" ∧ s ≠ "param" ∧ s ≠ "result")
    (h : HeadKw s x) : ¬ TUList x := by
  rintro (h' | h' | h')
  · exact headKw_ne hs.1 h h'
  · exact headKw_ne hs.2.1 h h'
  · exact headKw_ne hs.2.2 h h'

theorem notP_of_forall {P : SExp → Prop} {xs : List SExp} (h : ∀ x ∈ xs, ¬ P x) : NotP P xs :=
  fun x hx => h x (List.mem_of_mem_head? hx)

/-- The items after the label of an `if` with folded conditions. -/
theorem if_splits {I I' I₁ I₁' : IdCtx} {lx bx conds tl lx' bx' conds' tl' : List SExp}
    {id id' : Option String} {bt bt' : BlockType} {u u' uc uc' : List FuncType} {cs cs' : Expr}
    (hl : LabelT I lx id I₁) (hb : BlockTypeT I bx bt u) (hc : FoldedSeq I conds cs uc)
    (hl' : LabelT I' lx' id' I₁') (hb' : BlockTypeT I' bx' bt' u')
    (hc' : FoldedSeq I' conds' cs' uc') (htl : ∀ x ∈ tl, ∃ s, s ≠ "type" ∧ s ≠ "param" ∧
      s ≠ "result" ∧ HeadKw s x ∧ ¬ IsStart x) (_hne : tl ≠ [])
    (htl' : ∀ x ∈ tl', ∃ s, s ≠ "type" ∧ s ≠ "param" ∧ s ≠ "result" ∧ HeadKw s x ∧ ¬ IsStart x)
    (_hne' : tl' ≠ [])
    (e : lx ++ (bx ++ (conds ++ tl)) = lx' ++ (bx' ++ (conds' ++ tl'))) :
    lx = lx' ∧ bx = bx' ∧ conds = conds' ∧ tl = tl' := by
  have tlNotId : ∀ {tl : List SExp}, (∀ x ∈ tl, ∃ s, s ≠ "type" ∧ s ≠ "param" ∧ s ≠ "result" ∧
      HeadKw s x ∧ ¬ IsStart x) → ∀ x ∈ tl, ¬ IdAtom x := by
    intro tl htl x hx; obtain ⟨s, -, -, -, h, -⟩ := htl x hx; exact not_idAtom_of_headKw h
  have tlNotTU : ∀ {tl : List SExp}, (∀ x ∈ tl, ∃ s, s ≠ "type" ∧ s ≠ "param" ∧ s ≠ "result" ∧
      HeadKw s x ∧ ¬ IsStart x) → ∀ x ∈ tl, ¬ TUList x := by
    intro tl htl x hx; obtain ⟨s, h1, h2, h3, h, -⟩ := htl x hx; exact notTU_headKw ⟨h1, h2, h3⟩ h
  obtain ⟨rfl, e1⟩ := munch (labelT_mem hl) (labelT_mem hl')
    (notP_append (fun x hx => tuList_notId (blockTypeT_mem hb x hx))
      (notP_append (fun x hx => isStart_not_idAtom (foldedSeq_mem hc x hx))
        (notP_of_forall (tlNotId htl))))
    (notP_append (fun x hx => tuList_notId (blockTypeT_mem hb' x hx))
      (notP_append (fun x hx => isStart_not_idAtom (foldedSeq_mem hc' x hx))
        (notP_of_forall (tlNotId htl')))) e
  obtain ⟨rfl, e2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
    (notP_append (fun x hx => isStart_not_tuList (foldedSeq_mem hc x hx))
      (notP_of_forall (tlNotTU htl)))
    (notP_append (fun x hx => isStart_not_tuList (foldedSeq_mem hc' x hx))
      (notP_of_forall (tlNotTU htl'))) e1
  have notStartHead : ∀ {tl : List SExp}, (∀ x ∈ tl, ∃ s, s ≠ "type" ∧ s ≠ "param" ∧
      s ≠ "result" ∧ HeadKw s x ∧ ¬ IsStart x) → NotP IsStart tl := by
    intro tl htl x hx; obtain ⟨s, -, -, -, -, h⟩ := htl x (List.mem_of_mem_head? hx); exact h
  obtain ⟨rfl, rfl⟩ := munch (foldedSeq_mem hc) (foldedSeq_mem hc') (notStartHead htl)
    (notStartHead htl') e2
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem then_tl {thn : List SExp} : ∀ x ∈ [L (K "then" :: thn)], ∃ s, s ≠ "type" ∧ s ≠ "param" ∧
    s ≠ "result" ∧ HeadKw s x ∧ ¬ IsStart x := by
  intro x hx; simp only [List.mem_singleton] at hx; subst hx
  refine ⟨"then", by decide, by decide, by decide, ⟨_, rfl⟩, ?_⟩
  rintro (⟨s, e, -⟩ | ⟨s, ys, e, hs⟩)
  · simp at e
  · simp only [L_inj, List.cons.injEq, K_inj] at e; obtain ⟨rfl, -⟩ := e
    exact hs.not_reserved (by decide)

theorem thenElse_tl {thn els : List SExp} :
    ∀ x ∈ [L (K "then" :: thn), L (K "else" :: els)], ∃ s, s ≠ "type" ∧ s ≠ "param" ∧
      s ≠ "result" ∧ HeadKw s x ∧ ¬ IsStart x := by
  intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact then_tl (thn := thn) _ (by simp)
  · refine ⟨"else", by decide, by decide, by decide, ⟨_, rfl⟩, ?_⟩
    rintro (⟨s, e, -⟩ | ⟨s, ys, e, hs⟩)
    · simp at e
    · simp only [L_inj, List.cons.injEq, K_inj] at e; obtain ⟨rfl, -⟩ := e
      exact hs.not_reserved (by decide)

theorem fun_fifThen {I I₁ : IdCtx} {lx bx conds thn : List SExp} {id : Option String}
    {bt : BlockType} {cs is₁ : Expr} {u uc u₁ : List FuncType} (hl : LabelT I lx id I₁)
    (hb : BlockTypeT I bx bt u) (hc : FoldedSeq I conds cs uc) (_hthn : Instrs I₁ thn is₁ u₁)
    (ihc : FunS I conds cs uc) (iht : FunI I₁ thn is₁ u₁) :
    FunF I (L (K "if" :: (lx ++ bx ++ conds ++ [L (K "then" :: thn)])))
      (cs ++ [.if_ bt is₁ []]) (u ++ uc ++ u₁) := by
  intro I' x' e' u' h' hx hE hT
  cases h' with
  | ifThen hl' hb' hc' hthn' =>
      simp only [L_inj, List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨rfl, rfl, rfl, h4⟩ := if_splits hl hb hc hl' hb' hc' then_tl (by simp) then_tl
        (by simp) hx
      simp only [List.cons.injEq, L_inj, true_and, and_true] at h4; subst h4
      obtain ⟨hu, hE₁, hT₁, hfun⟩ := block_common hl hb hl' hb' hE hT
      obtain ⟨huc, hec⟩ := ihc hc' rfl hE hT
      obtain ⟨hu1, he1⟩ := iht hthn' rfl hE₁ hT₁
      refine ⟨by rw [hu, huc, hu1], fun hI hok => ?_⟩
      obtain ⟨rfl, hI₁, hok₁⟩ := hfun hI hok
      rw [hec hI hok, he1 hI₁ hok₁]
  | ifThenElse hl' hb' hc' hthn' hels' =>
      simp only [L_inj, List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨-, -, -, h4⟩ := if_splits hl hb hc hl' hb' hc' then_tl (by simp) thenElse_tl
        (by simp) hx
      simp at h4
  | _ =>
    simp only [L_inj, List.cons.injEq, K_inj] at hx
    first
      | exact absurd hx.1 (by decide)
      | (obtain ⟨rfl, -⟩ := hx
         obtain ⟨s', ys', e1, hs', -⟩ := plain_shape ‹Plain _ _ _ _›
         simp only [List.cons.injEq, K_inj] at e1
         exact absurd (by rw [← e1.1]; decide) hs'.ok.2)

theorem fun_fifThenElse {I I₁ : IdCtx} {lx bx conds thn els : List SExp} {id : Option String}
    {bt : BlockType} {cs is₁ is₂ : Expr} {u uc u₁ u₂ : List FuncType} (hl : LabelT I lx id I₁)
    (hb : BlockTypeT I bx bt u) (hc : FoldedSeq I conds cs uc) (_hthn : Instrs I₁ thn is₁ u₁)
    (_hels : Instrs I₁ els is₂ u₂) (ihc : FunS I conds cs uc) (iht : FunI I₁ thn is₁ u₁)
    (ihe : FunI I₁ els is₂ u₂) :
    FunF I (L (K "if" :: (lx ++ bx ++ conds ++ [L (K "then" :: thn), L (K "else" :: els)])))
      (cs ++ [.if_ bt is₁ is₂]) (u ++ uc ++ u₁ ++ u₂) := by
  intro I' x' e' u' h' hx hE hT
  cases h' with
  | ifThen hl' hb' hc' hthn' =>
      simp only [L_inj, List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨-, -, -, h4⟩ := if_splits hl hb hc hl' hb' hc' thenElse_tl (by simp) then_tl
        (by simp) hx
      simp at h4
  | ifThenElse hl' hb' hc' hthn' hels' =>
      simp only [L_inj, List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨rfl, rfl, rfl, h4⟩ := if_splits hl hb hc hl' hb' hc' thenElse_tl (by simp)
        thenElse_tl (by simp) hx
      simp only [List.cons.injEq, L_inj, true_and, and_true] at h4
      obtain ⟨rfl, rfl⟩ := h4
      obtain ⟨hu, hE₁, hT₁, hfun⟩ := block_common hl hb hl' hb' hE hT
      obtain ⟨huc, hec⟩ := ihc hc' rfl hE hT
      obtain ⟨hu1, he1⟩ := iht hthn' rfl hE₁ hT₁
      obtain ⟨hu2, he2⟩ := ihe hels' rfl hE₁ hT₁
      refine ⟨by rw [hu, huc, hu1, hu2], fun hI hok => ?_⟩
      obtain ⟨rfl, hI₁, hok₁⟩ := hfun hI hok
      rw [hec hI hok, he1 hI₁ hok₁, he2 hI₁ hok₁]
  | _ =>
    simp only [L_inj, List.cons.injEq, K_inj] at hx
    first
      | exact absurd hx.1 (by decide)
      | (obtain ⟨rfl, -⟩ := hx
         obtain ⟨s', ys', e1, hs', -⟩ := plain_shape ‹Plain _ _ _ _›
         simp only [List.cons.injEq, K_inj] at e1
         exact absurd (by rw [← e1.1]; decide) hs'.ok.2)

theorem fun_ftry {I I₁ : IdCtx} {lx bx cxs body : List SExp} {id : Option String}
    {bt : BlockType} {cs : List Catch} {is : Expr} {u u₁ : List FuncType}
    (hl : LabelT I lx id I₁) (hb : BlockTypeT I bx bt u) (hcs : List.Forall₂ (CatchT I) cxs cs)
    (hbody : Instrs I₁ body is u₁) (ih : FunI I₁ body is u₁) :
    FunF I (L (K "try_table" :: (lx ++ bx ++ cxs ++ body))) [.tryTable bt cs is] (u ++ u₁) := by
  intro I' x' e' u' h' hx hE hT
  cases h' with
  | tryTable hl' hb' hcs' hbody' =>
      simp only [L_inj, List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨rfl, e1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (notP_append (fun x hx => tuList_notId (blockTypeT_mem hb x hx))
          (notP_append (fun x hx => catch_not_idAtom (catchT_mem hcs x hx))
            (notP_instrs_nil (fun _ h => isStart_not_idAtom h) hbody)))
        (notP_append (fun x hx => tuList_notId (blockTypeT_mem hb' x hx))
          (notP_append (fun x hx => catch_not_idAtom (catchT_mem hcs' x hx))
            (notP_instrs_nil (fun _ h => isStart_not_idAtom h) hbody'))) hx
      obtain ⟨rfl, e2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (notP_append (fun x hx h => tuList_not_catch h (catchT_mem hcs x hx))
          (notP_instrs_nil (fun _ h => isStart_not_tuList h) hbody))
        (notP_append (fun x hx h => tuList_not_catch h (catchT_mem hcs' x hx))
          (notP_instrs_nil (fun _ h => isStart_not_tuList h) hbody')) e1
      obtain ⟨rfl, rfl⟩ := munch (catchT_mem hcs) (catchT_mem hcs')
        (notP_instrs_nil (fun _ h => isStart_not_catch h) hbody)
        (notP_instrs_nil (fun _ h => isStart_not_catch h) hbody') e2
      obtain ⟨hu, hE₁, hT₁, hfun⟩ := block_common hl hb hl' hb' hE hT
      obtain ⟨hu1, he1⟩ := ih hbody' rfl hE₁ hT₁
      refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
      obtain ⟨rfl, hI₁, hok₁⟩ := hfun hI hok
      subst hI
      rw [catchT_forall₂_functional hok hcs hcs', he1 hI₁ hok₁]
  | _ =>
    simp only [L_inj, List.cons.injEq, K_inj] at hx
    first
      | exact absurd hx.1 (by decide)
      | (obtain ⟨rfl, -⟩ := hx
         obtain ⟨s', ys', e1, hs', -⟩ := plain_shape ‹Plain _ _ _ _›
         simp only [List.cons.injEq, K_inj] at e1
         exact absurd (by rw [← e1.1]; decide) hs'.ok.2)

theorem fun_snil {I : IdCtx} : FunS I [] [] [] := by
  intro I' xs' e' u' h' hx hE hT
  cases h' with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons => simp at hx

theorem fun_scons {I : IdCtx} {x : SExp} {rest : List SExp} {is is' : Expr}
    {u u₁ : List FuncType} (_hf : Folded I x is u) (_hrest : FoldedSeq I rest is' u₁)
    (ihf : FunF I x is u) (ih : FunS I rest is' u₁) : FunS I (x :: rest) (is ++ is') (u ++ u₁) := by
  intro I' xs' e' u' h' hx hE hT
  cases h' with
  | nil => simp at hx
  | cons hf' hrest' =>
      simp only [List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨hu, he⟩ := ihf hf' rfl hE hT
      obtain ⟨hu1, he1⟩ := ih hrest' rfl hE hT
      refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
      rw [he hI hok, he1 hI hok]


theorem fun_bblock {I I₁ : IdCtx} {lx bx body ex : List SExp} {id : Option String}
    {bt : BlockType} {is : Expr} {u u₁ : List FuncType} {kw : String}
    {mk : BlockType → Expr → Instr}
    (hk : (kw = "block" ∧ mk = Instr.block) ∨ (kw = "loop" ∧ mk = Instr.loop))
    (hl : LabelT I lx id I₁) (hb : BlockTypeT I bx bt u) (hbody : Instrs I₁ body is u₁)
    (_hend : EndIdT ex id) (ih : FunI I₁ body is u₁) :
    FunB I (K kw :: (lx ++ bx ++ body ++ K "end" :: ex)) (mk bt is) (u ++ u₁) := by
  intro I' xs' i' u' h' hx hE hT
  have main : ∀ {I₁' : IdCtx} {lx' bx' body' ex' : List SExp} {id' : Option String}
      {bt' : BlockType} {is' : Expr} {uu uu₁ : List FuncType}, LabelT I' lx' id' I₁' →
      BlockTypeT I' bx' bt' uu → Instrs I₁' body' is' uu₁ →
      lx ++ (bx ++ (body ++ K "end" :: ex)) = lx' ++ (bx' ++ (body' ++ K "end" :: ex')) →
      u ++ u₁ = uu ++ uu₁ ∧ (I = I' → I.Ok → mk bt is = mk bt' is') := by
    intro I₁' lx' bx' body' ex' id' bt' is' uu uu₁ hl' hb' hbody' e
    obtain ⟨rfl, e1⟩ := munch (labelT_mem hl) (labelT_mem hl')
      (next_label hb hbody notId_end) (next_label hb' hbody' notId_end) e
    obtain ⟨rfl, e2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
      (next_blockType hbody notTU_end) (next_blockType hbody' notTU_end) e1
    obtain rfl := instrs_prefix hbody hbody' e2 term_end term_end
    obtain ⟨hu, hE₁, hT₁, hfun⟩ := block_common hl hb hl' hb' hE hT
    obtain ⟨hu1, he1⟩ := ih hbody' rfl hE₁ hT₁
    refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
    obtain ⟨rfl, hI₁, hok₁⟩ := hfun hI hok
    rw [he1 hI₁ hok₁]
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases h' with
    | block hl' hb' hbody' _ =>
        simp only [List.cons.injEq, true_and, List.append_assoc] at hx
        exact main hl' hb' hbody' hx
    | _ => simp at hx
  · cases h' with
    | loop hl' hb' hbody' _ =>
        simp only [List.cons.injEq, true_and, List.append_assoc] at hx
        exact main hl' hb' hbody' hx
    | _ => simp at hx

theorem fun_bif {I I₁ : IdCtx} {lx bx thn e₁ els e₂ : List SExp} {id : Option String}
    {bt : BlockType} {is₁ is₂ : Expr} {u u₁ u₂ : List FuncType} (hl : LabelT I lx id I₁)
    (hb : BlockTypeT I bx bt u) (hthn : Instrs I₁ thn is₁ u₁) (he₁ : EndIdT e₁ id)
    (hels : Instrs I₁ els is₂ u₂) (_he₂ : EndIdT e₂ id) (iht : FunI I₁ thn is₁ u₁)
    (ihe : FunI I₁ els is₂ u₂) :
    FunB I (K "if" :: (lx ++ bx ++ thn ++ K "else" :: (e₁ ++ els ++ K "end" :: e₂)))
      (.if_ bt is₁ is₂) (u ++ u₁ ++ u₂) := by
  intro I' xs' i' u' h' hx hE hT
  cases h' with
  | if_ hl' hb' hthn' he₁' hels' _ =>
      simp only [List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨rfl, e1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (next_label hb hthn notId_else) (next_label hb' hthn' notId_else) hx
      obtain ⟨rfl, e2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (next_blockType hthn notTU_else) (next_blockType hthn' notTU_else) e1
      obtain rfl := instrs_prefix hthn hthn' e2 term_else term_else
      simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at e2
      obtain ⟨rfl, e3⟩ := munch (endIdT_mem he₁) (endIdT_mem he₁')
        (notP_instrs (fun _ h => isStart_not_idAtom h) hels notId_end)
        (notP_instrs (fun _ h => isStart_not_idAtom h) hels' notId_end) e2
      obtain rfl := instrs_prefix hels hels' e3 term_end term_end
      obtain ⟨hu, hE₁, hT₁, hfun⟩ := block_common hl hb hl' hb' hE hT
      obtain ⟨hu1, he1⟩ := iht hthn' rfl hE₁ hT₁
      obtain ⟨hu2, he2⟩ := ihe hels' rfl hE₁ hT₁
      refine ⟨by rw [hu, hu1, hu2], fun hI hok => ?_⟩
      obtain ⟨rfl, hI₁, hok₁⟩ := hfun hI hok
      rw [he1 hI₁ hok₁, he2 hI₁ hok₁]
  | ifNoElse hl' hb' hthn' _ =>
      simp only [List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨rfl, e1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (next_label hb hthn notId_else) (next_label hb' hthn' notId_end) hx
      obtain ⟨rfl, e2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (next_blockType hthn notTU_else) (next_blockType hthn' notTU_end) e1
      obtain rfl := instrs_prefix hthn hthn' e2 term_else term_end
      simp at e2
  | _ => simp at hx

theorem fun_bifNoElse {I I₁ : IdCtx} {lx bx thn ex : List SExp} {id : Option String}
    {bt : BlockType} {is₁ : Expr} {u u₁ : List FuncType} (hl : LabelT I lx id I₁)
    (hb : BlockTypeT I bx bt u) (hthn : Instrs I₁ thn is₁ u₁) (_hend : EndIdT ex id)
    (iht : FunI I₁ thn is₁ u₁) :
    FunB I (K "if" :: (lx ++ bx ++ thn ++ K "end" :: ex)) (.if_ bt is₁ []) (u ++ u₁) := by
  intro I' xs' i' u' h' hx hE hT
  cases h' with
  | if_ hl' hb' hthn' _ _ _ =>
      simp only [List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨rfl, e1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (next_label hb hthn notId_end) (next_label hb' hthn' notId_else) hx
      obtain ⟨rfl, e2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (next_blockType hthn notTU_end) (next_blockType hthn' notTU_else) e1
      obtain rfl := instrs_prefix hthn hthn' e2 term_end term_else
      simp at e2
  | ifNoElse hl' hb' hthn' _ =>
      simp only [List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨rfl, e1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (next_label hb hthn notId_end) (next_label hb' hthn' notId_end) hx
      obtain ⟨rfl, e2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (next_blockType hthn notTU_end) (next_blockType hthn' notTU_end) e1
      obtain rfl := instrs_prefix hthn hthn' e2 term_end term_end
      obtain ⟨hu, hE₁, hT₁, hfun⟩ := block_common hl hb hl' hb' hE hT
      obtain ⟨hu1, he1⟩ := iht hthn' rfl hE₁ hT₁
      refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
      obtain ⟨rfl, hI₁, hok₁⟩ := hfun hI hok
      rw [he1 hI₁ hok₁]
  | _ => simp at hx

theorem fun_btry {I I₁ : IdCtx} {lx bx cxs body ex : List SExp} {id : Option String}
    {bt : BlockType} {cs : List Catch} {is : Expr} {u u₁ : List FuncType}
    (hl : LabelT I lx id I₁) (hb : BlockTypeT I bx bt u) (hcs : List.Forall₂ (CatchT I) cxs cs)
    (hbody : Instrs I₁ body is u₁) (_hend : EndIdT ex id) (ih : FunI I₁ body is u₁) :
    FunB I (K "try_table" :: (lx ++ bx ++ cxs ++ body ++ K "end" :: ex)) (.tryTable bt cs is)
      (u ++ u₁) := by
  intro I' xs' i' u' h' hx hE hT
  cases h' with
  | tryTable hl' hb' hcs' hbody' _ =>
      simp only [List.cons.injEq, true_and, List.append_assoc] at hx
      obtain ⟨rfl, e1⟩ := munch (labelT_mem hl) (labelT_mem hl')
        (notP_append (fun x hx => tuList_notId (blockTypeT_mem hb x hx))
          (notP_append (fun x hx => catch_not_idAtom (catchT_mem hcs x hx))
            (notP_instrs (fun _ h => isStart_not_idAtom h) hbody notId_end)))
        (notP_append (fun x hx => tuList_notId (blockTypeT_mem hb' x hx))
          (notP_append (fun x hx => catch_not_idAtom (catchT_mem hcs' x hx))
            (notP_instrs (fun _ h => isStart_not_idAtom h) hbody' notId_end))) hx
      obtain ⟨rfl, e2⟩ := munch (blockTypeT_mem hb) (blockTypeT_mem hb')
        (notP_append (fun x hx h => tuList_not_catch h (catchT_mem hcs x hx))
          (next_blockType hbody notTU_end))
        (notP_append (fun x hx h => tuList_not_catch h (catchT_mem hcs' x hx))
          (next_blockType hbody' notTU_end)) e1
      obtain ⟨rfl, e3⟩ := munch (catchT_mem hcs) (catchT_mem hcs')
        (notP_instrs (fun _ h => isStart_not_catch h) hbody notCatch_end)
        (notP_instrs (fun _ h => isStart_not_catch h) hbody' notCatch_end) e2
      obtain rfl := instrs_prefix hbody hbody' e3 term_end term_end
      obtain ⟨hu, hE₁, hT₁, hfun⟩ := block_common hl hb hl' hb' hE hT
      obtain ⟨hu1, he1⟩ := ih hbody' rfl hE₁ hT₁
      refine ⟨by rw [hu, hu1], fun hI hok => ?_⟩
      obtain ⟨rfl, hI₁, hok₁⟩ := hfun hI hok
      subst hI
      rw [catchT_forall₂_functional hok hcs hcs', he1 hI₁ hok₁]
  | _ => simp at hx

/-- Functionality of instruction sequences and folded instructions, by mutual
induction. -/
theorem fun_mutual :
    (∀ {I : IdCtx} {a : List SExp} {e : Expr} {u : List FuncType}, Instrs I a e u →
      FunI I a e u) ∧
    (∀ {I : IdCtx} {x : SExp} {e : Expr} {u : List FuncType}, Folded I x e u → FunF I x e u) := by
  have key := @Instrs.rec (fun I a e u _ => FunI I a e u) (fun I x e u _ => FunF I x e u)
    (fun I xs e u _ => FunS I xs e u) (fun I xs i u _ => FunB I xs i u)
    (fun {_} => fun_nil)
    (fun hp hrest ih => fun_plain hp hrest ih)
    (fun hb hrest ihb ih => fun_block hb hrest ihb ih)
    (fun hf hrest ihf ih => fun_folded hf hrest ihf ih)
    (fun hp hsubs ih => fun_fplain hp hsubs ih)
    (fun hl hb hbody ih => fun_fblock (.inl ⟨rfl, rfl⟩) hl hb hbody ih)
    (fun hl hb hbody ih => fun_fblock (.inr ⟨rfl, rfl⟩) hl hb hbody ih)
    (fun hl hb hc hthn ihc iht => fun_fifThen hl hb hc hthn ihc iht)
    (fun hl hb hc hthn hels ihc iht ihe => fun_fifThenElse hl hb hc hthn hels ihc iht ihe)
    (fun hl hb hcs hbody ih => fun_ftry hl hb hcs hbody ih)
    (fun {_} => fun_snil)
    (fun hf hrest ihf ih => fun_scons hf hrest ihf ih)
    (fun hl hb hbody hend ih => fun_bblock (.inl ⟨rfl, rfl⟩) hl hb hbody hend ih)
    (fun hl hb hbody hend ih => fun_bblock (.inr ⟨rfl, rfl⟩) hl hb hbody hend ih)
    (fun hl hb hthn he₁ hels he₂ iht ihe => fun_bif hl hb hthn he₁ hels he₂ iht ihe)
    (fun hl hb hthn hend iht => fun_bifNoElse hl hb hthn hend iht)
    (fun hl hb hcs hbody hend ih => fun_btry hl hb hcs hbody hend ih)
  have keyF := @Folded.rec (fun I a e u _ => FunI I a e u) (fun I x e u _ => FunF I x e u)
    (fun I xs e u _ => FunS I xs e u) (fun I xs i u _ => FunB I xs i u)
    (fun {_} => fun_nil)
    (fun hp hrest ih => fun_plain hp hrest ih)
    (fun hb hrest ihb ih => fun_block hb hrest ihb ih)
    (fun hf hrest ihf ih => fun_folded hf hrest ihf ih)
    (fun hp hsubs ih => fun_fplain hp hsubs ih)
    (fun hl hb hbody ih => fun_fblock (.inl ⟨rfl, rfl⟩) hl hb hbody ih)
    (fun hl hb hbody ih => fun_fblock (.inr ⟨rfl, rfl⟩) hl hb hbody ih)
    (fun hl hb hc hthn ihc iht => fun_fifThen hl hb hc hthn ihc iht)
    (fun hl hb hc hthn hels ihc iht ihe => fun_fifThenElse hl hb hc hthn hels ihc iht ihe)
    (fun hl hb hcs hbody ih => fun_ftry hl hb hcs hbody ih)
    (fun {_} => fun_snil)
    (fun hf hrest ihf ih => fun_scons hf hrest ihf ih)
    (fun hl hb hbody hend ih => fun_bblock (.inl ⟨rfl, rfl⟩) hl hb hbody hend ih)
    (fun hl hb hbody hend ih => fun_bblock (.inr ⟨rfl, rfl⟩) hl hb hbody hend ih)
    (fun hl hb hthn he₁ hels he₂ iht ihe => fun_bif hl hb hthn he₁ hels he₂ iht ihe)
    (fun hl hb hthn hend iht => fun_bifNoElse hl hb hthn hend iht)
    (fun hl hb hcs hbody hend ih => fun_btry hl hb hcs hbody hend ih)
  exact ⟨fun h => key h, fun h => keyF h⟩

/-- **For a fixed context with distinct names, an instruction sequence is
determined by its items.** -/
theorem instrs_functional' {I : IdCtx} (hI : I.Ok) {xs : List SExp} {e e' : Expr}
    {u u' : List FuncType} (h : Instrs I xs e u) (h' : Instrs I xs e' u') : e = e' ∧ u = u' := by
  obtain ⟨hu, he⟩ := fun_mutual.1 h h' rfl (TypesEq.refl I) hI.1
  exact ⟨he rfl hI, hu⟩

/-- Across contexts resolving type identifiers alike, an instruction sequence
uses the same function types implicitly. -/
theorem instrs_uses {I I' : IdCtx} (hT : Distinct I.types) (hE : TypesEq I I') {xs : List SExp}
    {e e' : Expr} {u u' : List FuncType} (h : Instrs I xs e u) (h' : Instrs I' xs e' u') :
    u = u' :=
  (fun_mutual.1 h h' rfl hE hT).1

theorem folded_functional' {I : IdCtx} (hI : I.Ok) {x : SExp} {e e' : Expr}
    {u u' : List FuncType} (h : Folded I x e u) (h' : Folded I x e' u') : e = e' ∧ u = u' := by
  obtain ⟨hu, he⟩ := fun_mutual.2 h h' rfl (TypesEq.refl I) hI.1
  exact ⟨he rfl hI, hu⟩

theorem folded_uses {I I' : IdCtx} (hT : Distinct I.types) (hE : TypesEq I I') {x : SExp}
    {e e' : Expr} {u u' : List FuncType} (h : Folded I x e u) (h' : Folded I' x e' u') :
    u = u' :=
  (fun_mutual.2 h h' rfl hE hT).1

end Silmaril.Wasm.Text.Core
