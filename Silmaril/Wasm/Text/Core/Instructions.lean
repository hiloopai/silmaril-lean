module

public import Silmaril.Wasm.Text.Core.Types
public import Silmaril.Wasm.Text.Core.Names

/-!
# Core 3.0 text format: instructions (SpecTec `6.3-text.instructions`)

* `Plain I xs i uses` — `Tplaininstr_(I)` with its abbreviations (omitted
  table/memory indices default to `0`, `call_indirect typeuse`, omitted memory
  arguments, …).  Instructions without immediates are given uniformly by
  `nullaryName`.
* `Instrs`, `Folded`, `BlockInstr` — `Tinstrs_(I)` (unfolded and folded),
  `Tfoldedinstr_(I)` and `Tblockinstr_(I)`, mutually inductive.
* `LabelT` — `Tlabel_(I)`, including shadowing of an existing label name.

Disambiguations (the SpecTec grammar is ambiguous here; both choices agree with
the reference interpreter, see `Silmaril.Wasm.Text.Core.Modules`):

* `select` without `(result …)` is `SELECT none` only (SpecTec also derives
  `SELECT (some [])` from the empty abbreviation of `(result)*`);
* a block type of the shape `(param)* (result t)?` (inline, no parameters, at
  most one result) is the value form `_RESULT t?`, never the type-use
  abbreviation (which SpecTec also allows).

Both are SpecTec ambiguities, resolved as the reference interpreter does.

Erratum T3: `Talign_(N)` defaults to `N` in the SpecTec snapshot, where `N` is
the natural alignment in *bytes*; the abstract syntax stores the alignment
*exponent*, so the default here is `log2 N` (as `align=m` gives `n` with
`m = 2^n`).
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Core

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Wasm

/-! ## Labels and block types -/

/-- `Tlabel_(I)`: the optional label name and the extended context. -/
def LabelT (I : IdCtx) (xs : List SExp) (id : Option String) (I' : IdCtx) : Prop :=
  (xs = [] ∧ id = none ∧ I' = { I with labels := none :: I.labels }) ∨
    (∃ n, xs = [.atom (.id n)] ∧ id = some n ∧ some n ∉ I.labels ∧
      I' = { I with labels := some n :: I.labels }) ∨
    ∃ n x, xs = [.atom (.id n)] ∧ id = some n ∧ I.labels[x]? = some (some n) ∧
      I' = { I with labels := some n :: I.labels.set x none }

/-- The optional identifier after `end`/`else`, which must repeat the label. -/
def EndIdT (xs : List SExp) (id : Option String) : Prop :=
  xs = [] ∨ ∃ n, xs = [.atom (.id n)] ∧ id = some n

/-- Inline parameter and result clauses whose parameters are all empty
(`(param)`), with results `ts`: the shape the value form of a block type
accepts. -/
def ValueFormT (I : IdCtx) (xs : List SExp) (ts : List ValType) : Prop :=
  ∃ pxs rxs, xs = pxs ++ rxs ∧ Concat (ParamT I) pxs [] ∧ Concat (ResultT I) rxs ts

/-- A plain result list is in value form. -/
theorem valueFormT_of_results {I : IdCtx} {xs : List SExp} {ts : List ValType}
    (h : Concat (ResultT I) xs ts) : ValueFormT I xs ts :=
  ⟨[], xs, rfl, Concat.nil', h⟩

/-- The first item of a value form is an empty `(param)` or a result clause. -/
theorem valueFormT_head {I : IdCtx} {x : SExp} {rest : List SExp} {ts : List ValType}
    (h : ValueFormT I (x :: rest) ts) : x = L [K "param"] ∨ ∃ tl, x = L (K "result" :: tl) := by
  obtain ⟨pxs, rxs, e, ⟨pss, hp, hps, -⟩, ⟨rss, hr, -, -⟩⟩ := h
  cases pxs with
  | nil =>
    simp only [List.nil_append] at e
    subst e
    cases hr with
    | cons h _ => obtain ⟨txs, rfl, -⟩ := h; exact .inr ⟨_, rfl⟩
  | cons p ps =>
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, -⟩ := e
    cases hp with
    | @cons _ a _ as h _ =>
      simp only [List.flatten_cons] at hps
      obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hps.symm
      rcases h with ⟨n, tx, t, rfl, -, h⟩ | ⟨txs, ts', rfl, h, h'⟩
      · simp at h
      · obtain rfl : ts' = [] := List.map_eq_nil_iff.mp h'.symm
        cases h
        exact .inl rfl

/-- A list headed by a keyword other than `param`/`result` is no value form. -/
theorem not_valueFormT_kw {I : IdCtx} {k : String} (h₁ : k ≠ "param") (h₂ : k ≠ "result")
    {tl rest : List SExp} {ts : List ValType} : ¬ ValueFormT I (L (K k :: tl) :: rest) ts := by
  intro h
  rcases valueFormT_head h with e | ⟨tl', e⟩ <;> simp at e <;> simp_all

/-- A list headed by a non-empty `param` clause is no value form. -/
theorem not_valueFormT_param {I : IdCtx} {y : SExp} {tl rest : List SExp} {ts : List ValType} :
    ¬ ValueFormT I (L (K "param" :: y :: tl) :: rest) ts := by
  intro h
  rcases valueFormT_head h with e | ⟨tl', e⟩ <;> simp at e

/-- `Tblocktype_(I)` (with the value-form disambiguation).

SpecTec ambiguity, resolved as the reference interpreter does: a block type without `(type x)` whose inline
parameters are empty and whose results number at most one is the value form
`_RESULT t?`, never a type use, so it adds no implicit type definition
(`parser.mly`, the `([], [])`/`([], [t])` cases of `block_type`).  This
includes empty `(param)`/`(result)` clauses, which the abbreviations expand
to nothing (`(param) (result i32)` is `(result i32)`). -/
def BlockTypeT (I : IdCtx) (xs : List SExp) (bt : BlockType) (uses : List FuncType) : Prop :=
  (∃ ts, ValueFormT I xs ts ∧ ts = [] ∧ bt = .empty ∧ uses = []) ∨
    (∃ ts t, ValueFormT I xs ts ∧ ts = [t] ∧ bt = .value t ∧ uses = []) ∨
    ∃ x locals, TypeUseT I xs x locals uses ∧ (∀ l ∈ locals, l = none) ∧ bt = .typeIdx x ∧
      ¬ ∃ ts, ValueFormT I xs ts ∧ ts.length ≤ 1

/-! ## Memory arguments -/

/-- `Tmemarg_(N)` for natural alignment `N` bytes. -/
def MemArgT (N : Nat) (xs : List SExp) (a : MemArg) : Prop :=
  ∃ ox ax, xs = ox ++ ax ∧
    ((ox = [] ∧ a.offset = 0) ∨ ∃ t r, ox = [K t] ∧ t.toList = "offset=".toList ++ r ∧
      UN 64 r a.offset.val) ∧
    ((ax = [] ∧ a.align.val = Nat.log2 N) ∨ ∃ t r m, ax = [K t] ∧
      t.toList = "align=".toList ++ r ∧ UN 64 r m ∧ m = 2 ^ a.align.val)

/-- An optional memory/table index defaulting to `0`. -/
def OptIdx (names : List (Option String)) {k : IndexKind} (xs : List SExp) (i : Wasm.Idx k) :
    Prop :=
  (xs = [] ∧ i.toNat = 0) ∨ ∃ x, xs = [x] ∧ Idx names x i

/-- Memory instructions with a memory argument: keyword, natural alignment, and
the instruction built from the memory index and memory argument. -/
def memOps : List (String × Nat × (MemIdx → MemArg → Instr)) :=
  [("i32.load", 4, .intLoad .i32 none), ("i64.load", 8, .intLoad .i64 none),
   ("f32.load", 4, .floatLoad .f32), ("f64.load", 8, .floatLoad .f64),
   ("i32.load8_s", 1, .intLoad .i32 (some (.i8, .signed))),
   ("i32.load8_u", 1, .intLoad .i32 (some (.i8, .unsigned))),
   ("i32.load16_s", 2, .intLoad .i32 (some (.i16, .signed))),
   ("i32.load16_u", 2, .intLoad .i32 (some (.i16, .unsigned))),
   ("i64.load8_s", 1, .intLoad .i64 (some (.i8, .signed))),
   ("i64.load8_u", 1, .intLoad .i64 (some (.i8, .unsigned))),
   ("i64.load16_s", 2, .intLoad .i64 (some (.i16, .signed))),
   ("i64.load16_u", 2, .intLoad .i64 (some (.i16, .unsigned))),
   ("i64.load32_s", 4, .intLoad .i64 (some (.i32, .signed))),
   ("i64.load32_u", 4, .intLoad .i64 (some (.i32, .unsigned))),
   ("v128.load", 16, .vecLoad .full),
   ("v128.load8x8_s", 8, .vecLoad (.extend8x8 .signed)),
   ("v128.load8x8_u", 8, .vecLoad (.extend8x8 .unsigned)),
   ("v128.load16x4_s", 8, .vecLoad (.extend16x4 .signed)),
   ("v128.load16x4_u", 8, .vecLoad (.extend16x4 .unsigned)),
   ("v128.load32x2_s", 8, .vecLoad (.extend32x2 .signed)),
   ("v128.load32x2_u", 8, .vecLoad (.extend32x2 .unsigned)),
   ("v128.load8_splat", 1, .vecLoad (.splat .i8)),
   ("v128.load16_splat", 2, .vecLoad (.splat .i16)),
   ("v128.load32_splat", 4, .vecLoad (.splat .i32)),
   ("v128.load64_splat", 8, .vecLoad (.splat .i64)),
   ("v128.load32_zero", 4, .vecLoad .zero32), ("v128.load64_zero", 8, .vecLoad .zero64),
   ("i32.store", 4, .intStore .i32 none), ("i64.store", 8, .intStore .i64 none),
   ("f32.store", 4, .floatStore .f32), ("f64.store", 8, .floatStore .f64),
   ("i32.store8", 1, .intStore .i32 (some .i8)), ("i32.store16", 2, .intStore .i32 (some .i16)),
   ("i64.store8", 1, .intStore .i64 (some .i8)), ("i64.store16", 2, .intStore .i64 (some .i16)),
   ("i64.store32", 4, .intStore .i64 (some .i32)),
   ("v128.store", 16, .vecStore)]

/-- Vector lane memory instructions. -/
def laneMemOps : List (String × Nat × (MemIdx → MemArg → LaneIdx → Instr)) :=
  [("v128.load8_lane", 1, .vecLoadLane .i8), ("v128.load16_lane", 2, .vecLoadLane .i16),
   ("v128.load32_lane", 4, .vecLoadLane .i32), ("v128.load64_lane", 8, .vecLoadLane .i64),
   ("v128.store8_lane", 1, .vecStoreLane .i8), ("v128.store16_lane", 2, .vecStoreLane .i16),
   ("v128.store32_lane", 4, .vecStoreLane .i32), ("v128.store64_lane", 8, .vecStoreLane .i64)]

/-- Lane access instructions (`Tplaininstr_/vec-lane`). -/
def laneOps : List (String × (LaneIdx → Instr)) :=
  [("i8x16.extract_lane_s", .vecExtractLane (.int .i8x16) (some .signed)),
   ("i8x16.extract_lane_u", .vecExtractLane (.int .i8x16) (some .unsigned)),
   ("i16x8.extract_lane_s", .vecExtractLane (.int .i16x8) (some .signed)),
   ("i16x8.extract_lane_u", .vecExtractLane (.int .i16x8) (some .unsigned)),
   ("i32x4.extract_lane", .vecExtractLane (.int .i32x4) none),
   ("i64x2.extract_lane", .vecExtractLane (.int .i64x2) none),
   ("f32x4.extract_lane", .vecExtractLane (.float .f32x4) none),
   ("f64x2.extract_lane", .vecExtractLane (.float .f64x2) none),
   ("i8x16.replace_lane", .vecReplaceLane (.int .i8x16)),
   ("i16x8.replace_lane", .vecReplaceLane (.int .i16x8)),
   ("i32x4.replace_lane", .vecReplaceLane (.int .i32x4)),
   ("i64x2.replace_lane", .vecReplaceLane (.int .i64x2)),
   ("f32x4.replace_lane", .vecReplaceLane (.float .f32x4)),
   ("f64x2.replace_lane", .vecReplaceLane (.float .f64x2))]

/-- Little-endian concatenation of `w`-bit lanes (`$inv_ibytes_` of the
concatenated lane bytes). -/
def lanesToBits (w : Nat) (ls : List Nat) : BitVec 128 :=
  BitVec.ofNat 128 (ls.foldr (fun v acc => v + 2 ^ w * acc) 0)

/-- `v128.const` shapes and lane literals (`Tplaininstr_/vec-const`). -/
def V128ConstT (xs : List SExp) (b : BitVec 128) : Prop :=
  (∃ (cs : List SExp) (vs : List (BitVec 8)), xs = K "i8x16" :: cs ∧ List.Forall₂ (AtomI 8) cs vs ∧
      vs.length = 16 ∧ b = lanesToBits 8 (vs.map BitVec.toNat)) ∨
  (∃ (cs : List SExp) (vs : List (BitVec 16)), xs = K "i16x8" :: cs ∧ List.Forall₂ (AtomI 16) cs vs ∧
      vs.length = 8 ∧ b = lanesToBits 16 (vs.map BitVec.toNat)) ∨
  (∃ (cs : List SExp) (vs : List (BitVec 32)), xs = K "i32x4" :: cs ∧ List.Forall₂ (AtomI 32) cs vs ∧
      vs.length = 4 ∧ b = lanesToBits 32 (vs.map BitVec.toNat)) ∨
  (∃ (cs : List SExp) (vs : List (BitVec 64)), xs = K "i64x2" :: cs ∧ List.Forall₂ (AtomI 64) cs vs ∧
      vs.length = 2 ∧ b = lanesToBits 64 (vs.map BitVec.toNat)) ∨
  (∃ (cs : List SExp) (vs : List (BitVec 32)), xs = K "f32x4" :: cs ∧
      List.Forall₂ (AtomF .f32) cs vs ∧ vs.length = 4 ∧
      b = lanesToBits 32 (vs.map BitVec.toNat)) ∨
  ∃ (cs : List SExp) (vs : List (BitVec 64)), xs = K "f64x2" :: cs ∧ List.Forall₂ (AtomF .f64) cs vs ∧
    vs.length = 2 ∧ b = lanesToBits 64 (vs.map BitVec.toNat)

/-- `Tfieldidx__(I, x)`. -/
def FieldIdxT (I : IdCtx) (t : TypeIdx) (x : SExp) (i : FieldIdx) : Prop :=
  Idx ((I.fields[t.toNat]?).getD []) x i

/-! ## Plain instructions -/

/-- `Tplaininstr_(I)` with its abbreviations; the last index lists the function
types used through type-use abbreviations. -/
inductive Plain (I : IdCtx) : List SExp → Instr → List FuncType → Prop where
  | nullary {s : String} {i : Instr} : nullaryName i = some s → Plain I [K s] i []
  | select : Plain I [K "select"] (.select none) []
  | selectTyped {rxs : List SExp} {ts : List ValType} : rxs ≠ [] → Concat (ResultT I) rxs ts →
      Plain I (K "select" :: rxs) (.select (some ts)) []
  | br {x : SExp} {l : LabelIdx} : Idx I.labels x l → Plain I [K "br", x] (.br l) []
  | brIf {x : SExp} {l : LabelIdx} : Idx I.labels x l → Plain I [K "br_if", x] (.brIf l) []
  | brTable {xs : List SExp} {ls : List LabelIdx} {l : LabelIdx} :
      List.Forall₂ (Idx I.labels) xs (ls ++ [l]) → (ls ++ [l]).length < 2 ^ 32 →
      Plain I (K "br_table" :: xs) (.brTable ls l) []
  | brOnNull {x : SExp} {l : LabelIdx} : Idx I.labels x l →
      Plain I [K "br_on_null", x] (.brOnNull l) []
  | brOnNonNull {x : SExp} {l : LabelIdx} : Idx I.labels x l →
      Plain I [K "br_on_non_null", x] (.brOnNonNull l) []
  | brOnCast {x r₁ r₂ : SExp} {l : LabelIdx} {t₁ t₂ : RefType} : Idx I.labels x l →
      RefTypeT I r₁ t₁ → RefTypeT I r₂ t₂ → Plain I [K "br_on_cast", x, r₁, r₂] (.brOnCast l t₁ t₂) []
  | brOnCastFail {x r₁ r₂ : SExp} {l : LabelIdx} {t₁ t₂ : RefType} : Idx I.labels x l →
      RefTypeT I r₁ t₁ → RefTypeT I r₂ t₂ →
      Plain I [K "br_on_cast_fail", x, r₁, r₂] (.brOnCastFail l t₁ t₂) []
  | call {x : SExp} {f : FuncIdx} : Idx I.funcs x f → Plain I [K "call", x] (.call f) []
  | callRef {x : SExp} {t : TypeIdx} : Idx I.types x t → Plain I [K "call_ref", x] (.callRef t) []
  | callIndirect {tx tu : List SExp} {tb : TableIdx} {t : TypeIdx} {locals : List (Option String)}
      {uses : List FuncType} : OptIdx I.tables tx tb → TypeUseT I tu t locals uses →
      (∀ l ∈ locals, l = none) → Plain I (K "call_indirect" :: (tx ++ tu)) (.callIndirect tb t) uses
  | returnCall {x : SExp} {f : FuncIdx} : Idx I.funcs x f →
      Plain I [K "return_call", x] (.returnCall f) []
  | returnCallRef {x : SExp} {t : TypeIdx} : Idx I.types x t →
      Plain I [K "return_call_ref", x] (.returnCallRef t) []
  | returnCallIndirect {tx tu : List SExp} {tb : TableIdx} {t : TypeIdx}
      {locals : List (Option String)} {uses : List FuncType} : OptIdx I.tables tx tb →
      TypeUseT I tu t locals uses → (∀ l ∈ locals, l = none) →
      Plain I (K "return_call_indirect" :: (tx ++ tu)) (.returnCallIndirect tb t) uses
  | throw {x : SExp} {t : TagIdx} : Idx I.tags x t → Plain I [K "throw", x] (.throw t) []
  | localGet {x : SExp} {i : LocalIdx} : Idx I.locals x i →
      Plain I [K "local.get", x] (.localGet i) []
  | localSet {x : SExp} {i : LocalIdx} : Idx I.locals x i →
      Plain I [K "local.set", x] (.localSet i) []
  | localTee {x : SExp} {i : LocalIdx} : Idx I.locals x i →
      Plain I [K "local.tee", x] (.localTee i) []
  | globalGet {x : SExp} {g : GlobalIdx} : Idx I.globals x g →
      Plain I [K "global.get", x] (.globalGet g) []
  | globalSet {x : SExp} {g : GlobalIdx} : Idx I.globals x g →
      Plain I [K "global.set", x] (.globalSet g) []
  | tableGet {xs : List SExp} {t : TableIdx} : OptIdx I.tables xs t →
      Plain I (K "table.get" :: xs) (.tableGet t) []
  | tableSet {xs : List SExp} {t : TableIdx} : OptIdx I.tables xs t →
      Plain I (K "table.set" :: xs) (.tableSet t) []
  | tableSize {xs : List SExp} {t : TableIdx} : OptIdx I.tables xs t →
      Plain I (K "table.size" :: xs) (.tableSize t) []
  | tableGrow {xs : List SExp} {t : TableIdx} : OptIdx I.tables xs t →
      Plain I (K "table.grow" :: xs) (.tableGrow t) []
  | tableFill {xs : List SExp} {t : TableIdx} : OptIdx I.tables xs t →
      Plain I (K "table.fill" :: xs) (.tableFill t) []
  | tableCopy {x₁ x₂ : SExp} {t₁ t₂ : TableIdx} : Idx I.tables x₁ t₁ → Idx I.tables x₂ t₂ →
      Plain I [K "table.copy", x₁, x₂] (.tableCopy t₁ t₂) []
  | tableCopy0 : Plain I [K "table.copy"] (.tableCopy ⟨0⟩ ⟨0⟩) []
  | tableInit {tx : List SExp} {y : SExp} {t : TableIdx} {e : ElemIdx} : OptIdx I.tables tx t →
      Idx I.elems y e → Plain I (K "table.init" :: (tx ++ [y])) (.tableInit t e) []
  | elemDrop {x : SExp} {e : ElemIdx} : Idx I.elems x e → Plain I [K "elem.drop", x] (.elemDrop e) []
  | memOp {s : String} {N : Nat} {k : MemIdx → MemArg → Instr} {mx ax : List SExp} {m : MemIdx}
      {a : MemArg} : (s, N, k) ∈ memOps → OptIdx I.mems mx m → MemArgT N ax a →
      Plain I (K s :: (mx ++ ax)) (k m a) []
  | laneMemOp {s : String} {N : Nat} {k : MemIdx → MemArg → LaneIdx → Instr}
      {mx ax : List SExp} {lx : SExp} {m : MemIdx} {a : MemArg} {l : LaneIdx} :
      (s, N, k) ∈ laneMemOps → OptIdx I.mems mx m → MemArgT N ax a → AtomU 8 lx l.val →
      Plain I (K s :: (mx ++ ax ++ [lx])) (k m a l) []
  | memorySize {xs : List SExp} {m : MemIdx} : OptIdx I.mems xs m →
      Plain I (K "memory.size" :: xs) (.memorySize m) []
  | memoryGrow {xs : List SExp} {m : MemIdx} : OptIdx I.mems xs m →
      Plain I (K "memory.grow" :: xs) (.memoryGrow m) []
  | memoryFill {xs : List SExp} {m : MemIdx} : OptIdx I.mems xs m →
      Plain I (K "memory.fill" :: xs) (.memoryFill m) []
  | memoryCopy {x₁ x₂ : SExp} {m₁ m₂ : MemIdx} : Idx I.mems x₁ m₁ → Idx I.mems x₂ m₂ →
      Plain I [K "memory.copy", x₁, x₂] (.memoryCopy m₁ m₂) []
  | memoryCopy0 : Plain I [K "memory.copy"] (.memoryCopy ⟨0⟩ ⟨0⟩) []
  | memoryInit {mx : List SExp} {y : SExp} {m : MemIdx} {d : DataIdx} : OptIdx I.mems mx m →
      Idx I.datas y d → Plain I (K "memory.init" :: (mx ++ [y])) (.memoryInit m d) []
  | dataDrop {x : SExp} {d : DataIdx} : Idx I.datas x d → Plain I [K "data.drop", x] (.dataDrop d) []
  | refNull {x : SExp} {h : HeapType} : HeapTypeT I x h → Plain I [K "ref.null", x] (.refNull h) []
  | refFunc {x : SExp} {f : FuncIdx} : Idx I.funcs x f → Plain I [K "ref.func", x] (.refFunc f) []
  | refTest {x : SExp} {r : RefType} : RefTypeT I x r → Plain I [K "ref.test", x] (.refTest r) []
  | refCast {x : SExp} {r : RefType} : RefTypeT I x r → Plain I [K "ref.cast", x] (.refCast r) []
  | structNew {x : SExp} {t : TypeIdx} : Idx I.types x t →
      Plain I [K "struct.new", x] (.structNew t) []
  | structNewDefault {x : SExp} {t : TypeIdx} : Idx I.types x t →
      Plain I [K "struct.new_default", x] (.structNewDefault t) []
  | structGet {x y : SExp} {t : TypeIdx} {f : FieldIdx} : Idx I.types x t → FieldIdxT I t y f →
      Plain I [K "struct.get", x, y] (.structGet none t f) []
  | structGetS {x y : SExp} {t : TypeIdx} {f : FieldIdx} : Idx I.types x t → FieldIdxT I t y f →
      Plain I [K "struct.get_s", x, y] (.structGet (some .signed) t f) []
  | structGetU {x y : SExp} {t : TypeIdx} {f : FieldIdx} : Idx I.types x t → FieldIdxT I t y f →
      Plain I [K "struct.get_u", x, y] (.structGet (some .unsigned) t f) []
  | structSet {x y : SExp} {t : TypeIdx} {f : FieldIdx} : Idx I.types x t → FieldIdxT I t y f →
      Plain I [K "struct.set", x, y] (.structSet t f) []
  | arrayNew {x : SExp} {t : TypeIdx} : Idx I.types x t → Plain I [K "array.new", x] (.arrayNew t) []
  | arrayNewDefault {x : SExp} {t : TypeIdx} : Idx I.types x t →
      Plain I [K "array.new_default", x] (.arrayNewDefault t) []
  | arrayNewFixed {x n : SExp} {t : TypeIdx} {k : Fin (2 ^ 32)} : Idx I.types x t → AtomU32 n k →
      Plain I [K "array.new_fixed", x, n] (.arrayNewFixed t k) []
  | arrayNewData {x y : SExp} {t : TypeIdx} {d : DataIdx} : Idx I.types x t → Idx I.datas y d →
      Plain I [K "array.new_data", x, y] (.arrayNewData t d) []
  | arrayNewElem {x y : SExp} {t : TypeIdx} {e : ElemIdx} : Idx I.types x t → Idx I.elems y e →
      Plain I [K "array.new_elem", x, y] (.arrayNewElem t e) []
  | arrayGet {x : SExp} {t : TypeIdx} : Idx I.types x t →
      Plain I [K "array.get", x] (.arrayGet none t) []
  | arrayGetS {x : SExp} {t : TypeIdx} : Idx I.types x t →
      Plain I [K "array.get_s", x] (.arrayGet (some .signed) t) []
  | arrayGetU {x : SExp} {t : TypeIdx} : Idx I.types x t →
      Plain I [K "array.get_u", x] (.arrayGet (some .unsigned) t) []
  | arraySet {x : SExp} {t : TypeIdx} : Idx I.types x t → Plain I [K "array.set", x] (.arraySet t) []
  | arrayFill {x : SExp} {t : TypeIdx} : Idx I.types x t →
      Plain I [K "array.fill", x] (.arrayFill t) []
  | arrayCopy {x y : SExp} {t₁ t₂ : TypeIdx} : Idx I.types x t₁ → Idx I.types y t₂ →
      Plain I [K "array.copy", x, y] (.arrayCopy t₁ t₂) []
  | arrayInitData {x y : SExp} {t : TypeIdx} {d : DataIdx} : Idx I.types x t → Idx I.datas y d →
      Plain I [K "array.init_data", x, y] (.arrayInitData t d) []
  | arrayInitElem {x y : SExp} {t : TypeIdx} {e : ElemIdx} : Idx I.types x t → Idx I.elems y e →
      Plain I [K "array.init_elem", x, y] (.arrayInitElem t e) []
  | i32Const {c : SExp} {b : BitVec 32} : AtomI 32 c b →
      Plain I [K "i32.const", c] (.intConst .i32 b) []
  | i64Const {c : SExp} {b : BitVec 64} : AtomI 64 c b →
      Plain I [K "i64.const", c] (.intConst .i64 b) []
  | f32Const {c : SExp} {b : BitVec 32} : AtomF .f32 c b →
      Plain I [K "f32.const", c] (.floatConst .f32 b) []
  | f64Const {c : SExp} {b : BitVec 64} : AtomF .f64 c b →
      Plain I [K "f64.const", c] (.floatConst .f64 b) []
  | v128Const {xs : List SExp} {b : BitVec 128} : V128ConstT xs b →
      Plain I (K "v128.const" :: xs) (.vecConst b) []
  | shuffle {xs : List SExp} {ls : List LaneIdx} : List.Forall₂ (fun x (l : LaneIdx) => AtomU 8 x l.val)
      xs ls → ls.length = 16 → Plain I (K "i8x16.shuffle" :: xs) (.vecShuffle ls) []
  | lane {s : String} {k : LaneIdx → Instr} {lx : SExp} {l : LaneIdx} : (s, k) ∈ laneOps →
      AtomU 8 lx l.val → Plain I [K s, lx] (k l) []

/-! ## Instruction sequences, folded and block instructions -/

/-- `Tcatch_(I)`. -/
def CatchT (I : IdCtx) (x : SExp) (c : Catch) : Prop :=
  (∃ tx lx t l, x = L [K "catch", tx, lx] ∧ Idx I.tags tx t ∧ Idx I.labels lx l ∧
      c = .catch_ t l) ∨
  (∃ tx lx t l, x = L [K "catch_ref", tx, lx] ∧ Idx I.tags tx t ∧ Idx I.labels lx l ∧
      c = .catchRef t l) ∨
  (∃ lx l, x = L [K "catch_all", lx] ∧ Idx I.labels lx l ∧ c = .catchAll l) ∨
  ∃ lx l, x = L [K "catch_all_ref", lx] ∧ Idx I.labels lx l ∧ c = .catchAllRef l

mutual
  /-- `Tinstrs_(I)`: unfolded and folded instructions, freely mixed. -/
  inductive Instrs : IdCtx → List SExp → Expr → List FuncType → Prop where
    | nil {I : IdCtx} : Instrs I [] [] []
    | plain {I : IdCtx} {xs rest : List SExp} {i : Instr} {is : Expr} {u u' : List FuncType} :
        Plain I xs i u → Instrs I rest is u' → Instrs I (xs ++ rest) (i :: is) (u ++ u')
    | block {I : IdCtx} {xs rest : List SExp} {i : Instr} {is : Expr} {u u' : List FuncType} :
        BlockInstr I xs i u → Instrs I rest is u' → Instrs I (xs ++ rest) (i :: is) (u ++ u')
    | folded {I : IdCtx} {x : SExp} {rest : List SExp} {is is' : Expr} {u u' : List FuncType} :
        Folded I x is u → Instrs I rest is' u' → Instrs I (x :: rest) (is ++ is') (u ++ u')

  /-- `Tfoldedinstr_(I)`: one parenthesized instruction tree. -/
  inductive Folded : IdCtx → SExp → Expr → List FuncType → Prop where
    | plain {I : IdCtx} {s : String} {imms subs : List SExp} {i : Instr} {is : Expr}
        {u u' : List FuncType} :
        Plain I (K s :: imms) i u → Instrs I subs is u' →
        Folded I (L (K s :: (imms ++ subs))) (is ++ [i]) (u' ++ u)
    | block {I I' : IdCtx} {lx bx body : List SExp} {id : Option String} {bt : BlockType}
        {is : Expr} {u u' : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → Instrs I' body is u' →
        Folded I (L (K "block" :: (lx ++ bx ++ body))) [.block bt is] (u ++ u')
    | loop {I I' : IdCtx} {lx bx body : List SExp} {id : Option String} {bt : BlockType}
        {is : Expr} {u u' : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → Instrs I' body is u' →
        Folded I (L (K "loop" :: (lx ++ bx ++ body))) [.loop bt is] (u ++ u')
    | ifThen {I I' : IdCtx} {lx bx conds thn : List SExp} {id : Option String} {bt : BlockType}
        {cs is₁ : Expr} {u uc u₁ : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → FoldedSeq I conds cs uc →
        Instrs I' thn is₁ u₁ →
        Folded I (L (K "if" :: (lx ++ bx ++ conds ++ [L (K "then" :: thn)])))
          (cs ++ [.if_ bt is₁ []]) (u ++ uc ++ u₁)
    | ifThenElse {I I' : IdCtx} {lx bx conds thn els : List SExp} {id : Option String}
        {bt : BlockType} {cs is₁ is₂ : Expr} {u uc u₁ u₂ : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → FoldedSeq I conds cs uc →
        Instrs I' thn is₁ u₁ → Instrs I' els is₂ u₂ →
        Folded I (L (K "if" :: (lx ++ bx ++ conds ++ [L (K "then" :: thn), L (K "else" :: els)])))
          (cs ++ [.if_ bt is₁ is₂]) (u ++ uc ++ u₁ ++ u₂)
    | tryTable {I I' : IdCtx} {lx bx cxs body : List SExp} {id : Option String} {bt : BlockType}
        {cs : List Catch} {is : Expr} {u u' : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → List.Forall₂ (CatchT I) cxs cs →
        Instrs I' body is u' →
        Folded I (L (K "try_table" :: (lx ++ bx ++ cxs ++ body))) [.tryTable bt cs is] (u ++ u')

  /-- `Tfoldedinstr_(I)*`. -/
  inductive FoldedSeq : IdCtx → List SExp → Expr → List FuncType → Prop where
    | nil {I : IdCtx} : FoldedSeq I [] [] []
    | cons {I : IdCtx} {x : SExp} {rest : List SExp} {is is' : Expr} {u u' : List FuncType} :
        Folded I x is u → FoldedSeq I rest is' u' → FoldedSeq I (x :: rest) (is ++ is') (u ++ u')

  /-- `Tblockinstr_(I)`: unfolded structured instructions ending in `end`. -/
  inductive BlockInstr : IdCtx → List SExp → Instr → List FuncType → Prop where
    | block {I I' : IdCtx} {lx bx body ex : List SExp} {id : Option String} {bt : BlockType}
        {is : Expr} {u u' : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → Instrs I' body is u' → EndIdT ex id →
        BlockInstr I (K "block" :: (lx ++ bx ++ body ++ K "end" :: ex)) (.block bt is) (u ++ u')
    | loop {I I' : IdCtx} {lx bx body ex : List SExp} {id : Option String} {bt : BlockType}
        {is : Expr} {u u' : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → Instrs I' body is u' → EndIdT ex id →
        BlockInstr I (K "loop" :: (lx ++ bx ++ body ++ K "end" :: ex)) (.loop bt is) (u ++ u')
    | if_ {I I' : IdCtx} {lx bx thn e₁ els e₂ : List SExp} {id : Option String} {bt : BlockType}
        {is₁ is₂ : Expr} {u u₁ u₂ : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → Instrs I' thn is₁ u₁ → EndIdT e₁ id →
        Instrs I' els is₂ u₂ → EndIdT e₂ id →
        BlockInstr I (K "if" :: (lx ++ bx ++ thn ++ K "else" :: (e₁ ++ els ++ K "end" :: e₂)))
          (.if_ bt is₁ is₂) (u ++ u₁ ++ u₂)
    | ifNoElse {I I' : IdCtx} {lx bx thn ex : List SExp} {id : Option String} {bt : BlockType}
        {is₁ : Expr} {u u₁ : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → Instrs I' thn is₁ u₁ → EndIdT ex id →
        BlockInstr I (K "if" :: (lx ++ bx ++ thn ++ K "end" :: ex)) (.if_ bt is₁ []) (u ++ u₁)
    | tryTable {I I' : IdCtx} {lx bx cxs body ex : List SExp} {id : Option String}
        {bt : BlockType} {cs : List Catch} {is : Expr} {u u' : List FuncType} :
        LabelT I lx id I' → BlockTypeT I bx bt u → List.Forall₂ (CatchT I) cxs cs →
        Instrs I' body is u' → EndIdT ex id →
        BlockInstr I (K "try_table" :: (lx ++ bx ++ cxs ++ body ++ K "end" :: ex))
          (.tryTable bt cs is) (u ++ u')
end

/-- `Texpr_(I)`. -/
abbrev ExprT (I : IdCtx) (xs : List SExp) (e : Expr) (uses : List FuncType) : Prop :=
  Instrs I xs e uses

end Silmaril.Wasm.Text.Core
