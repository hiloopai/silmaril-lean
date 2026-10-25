module

public import Silmaril.Wasm.Lime1.Modules

/-! # Lime1 instruction validation

Stacks are bottom-to-top and labels innermost-first. The judgment is independent
of Wasm1 validation: indexed block signatures support parameters and multiple
results, loops branch to their parameter stack, and the profile's numeric and
bulk-memory additions have explicit rules. Stack-polymorphic control transfers
and the frame rule retain their ordinary Wasm meaning.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Validation

structure Context where
  types : List FuncType := []
  funcs : List FuncType := []
  tables : List TableType := []
  memories : List MemoryType := []
  globals : List GlobalType := []
  locals : List ValType := []
  labels : List ResultType := []
  returnType : Option ResultType := none
  deriving Repr

def Context.withLabel (C : Context) (ts : ResultType) : Context :=
  { C with labels := ts :: C.labels }

/-- Resolve the complete parameter/result signature of a block annotation. -/
def blockType? (C : Context) : BlockType → Option FuncType
  | .empty => some ⟨[], []⟩
  | .value t => some ⟨[], [t]⟩
  | .typeIdx i => C.types[i.toNat]?

/-- Scalar conversion endpoints include nontrapping saturating conversion. -/
def conversionType (op : ConvertOp) : ValType × ValType := (op.source, op.target)

/-- Sign extension must use a strictly smaller packed width. -/
def IntUnOpValid (t : IntType) : IntUnOp → Prop
  | .extend size => size.width < t.width
  | _ => True

/-- Alignment may be smaller than the accessed width. Offsets are intrinsically u32. -/
def Aligned (arg : MemArg) (width : Nat) : Prop :=
  2 ^ arg.align.val ≤ width / 8

def IntAccess (t : IntType) (packed : Option PackSize) (arg : MemArg) : Prop :=
  match packed with
  | none => Aligned arg t.width
  | some p => p.width < t.width ∧ Aligned arg p.width

mutual
  inductive InstrType : Context → Instr → ResultType → ResultType → Prop where
    | frame {C : Context} {i : Instr} {a b : ResultType} (pre : ResultType)
        (h : InstrType C i a b) : InstrType C i (pre ++ a) (pre ++ b)
    | nop {C : Context} : InstrType C .nop [] []
    | unreachable {C : Context} (a b : ResultType) : InstrType C .unreachable a b
    | drop {C : Context} (t : ValType) : InstrType C .drop [t] []
    | select {C : Context} (t : ValType) : InstrType C .select [t, t, .i32] [t]
    | block {C : Context} (bt : BlockType) {ft : FuncType} {body : Expr}
        (type : blockType? C bt = some ft)
        (h : ExprType (C.withLabel ft.results) body ft.params ft.results) :
        InstrType C (.block bt body) ft.params ft.results
    | loop {C : Context} (bt : BlockType) {ft : FuncType} {body : Expr}
        (type : blockType? C bt = some ft)
        (h : ExprType (C.withLabel ft.params) body ft.params ft.results) :
        InstrType C (.loop bt body) ft.params ft.results
    | if_ {C : Context} (bt : BlockType) {ft : FuncType} {left right : Expr}
        (type : blockType? C bt = some ft)
        (hl : ExprType (C.withLabel ft.results) left ft.params ft.results)
        (hr : ExprType (C.withLabel ft.results) right ft.params ft.results) :
        InstrType C (.if_ bt left right) (ft.params ++ [.i32]) ft.results
    | br {C : Context} (i : LabelIdx) {ts : ResultType} (h : C.labels[i.toNat]? = some ts)
        (pre out : ResultType) : InstrType C (.br i) (pre ++ ts) out
    | brIf {C : Context} (i : LabelIdx) {ts : ResultType} (h : C.labels[i.toNat]? = some ts) :
        InstrType C (.brIf i) (ts ++ [.i32]) ts
    | brTable {C : Context} (is : List LabelIdx) (default : LabelIdx) {ts : ResultType}
        (hd : C.labels[default.toNat]? = some ts)
        (hs : ∀ i ∈ is, C.labels[i.toNat]? = some ts) (pre out : ResultType) :
        InstrType C (.brTable is default) (pre ++ ts ++ [.i32]) out
    | return_ {C : Context} {ts : ResultType} (h : C.returnType = some ts) (pre out : ResultType) :
        InstrType C .return_ (pre ++ ts) out
    | call {C : Context} (i : FuncIdx) {ft : FuncType} (h : C.funcs[i.toNat]? = some ft) :
        InstrType C (.call i) ft.params ft.results
    | callIndirect {C : Context} (i : TypeIdx) {ft : FuncType} (h : C.types[i.toNat]? = some ft)
        (table : C.tables ≠ []) :
        InstrType C (.callIndirect i) (ft.params ++ [.i32]) ft.results
    | localGet {C : Context} (i : LocalIdx) {t : ValType} (h : C.locals[i.toNat]? = some t) :
        InstrType C (.localGet i) [] [t]
    | localSet {C : Context} (i : LocalIdx) {t : ValType} (h : C.locals[i.toNat]? = some t) :
        InstrType C (.localSet i) [t] []
    | localTee {C : Context} (i : LocalIdx) {t : ValType} (h : C.locals[i.toNat]? = some t) :
        InstrType C (.localTee i) [t] [t]
    | globalGet {C : Context} (i : GlobalIdx) {gt : GlobalType} (h : C.globals[i.toNat]? = some gt) :
        InstrType C (.globalGet i) [] [gt.value]
    | globalSet {C : Context} (i : GlobalIdx) {t : ValType}
        (h : C.globals[i.toNat]? = some ⟨.var, t⟩) :
        InstrType C (.globalSet i) [t] []
    | intLoad {C : Context} (t : IntType) (p : Option (PackSize × Signedness)) (arg : MemArg)
        (memory : C.memories ≠ []) (access : IntAccess t (p.map Prod.fst) arg) :
        InstrType C (.intLoad t p arg) [.i32] [.int t]
    | floatLoad {C : Context} (t : FloatType) (arg : MemArg)
        (memory : C.memories ≠ []) (aligned : Aligned arg t.width) :
        InstrType C (.floatLoad t arg) [.i32] [.float t]
    | intStore {C : Context} (t : IntType) (p : Option PackSize) (arg : MemArg)
        (memory : C.memories ≠ []) (access : IntAccess t p arg) :
        InstrType C (.intStore t p arg) [.i32, .int t] []
    | floatStore {C : Context} (t : FloatType) (arg : MemArg)
        (memory : C.memories ≠ []) (aligned : Aligned arg t.width) :
        InstrType C (.floatStore t arg) [.i32, .float t] []
    | memorySize {C : Context} (memory : C.memories ≠ []) : InstrType C .memorySize [] [.i32]
    | memoryGrow {C : Context} (memory : C.memories ≠ []) : InstrType C .memoryGrow [.i32] [.i32]
    | memoryFill {C : Context} (memory : C.memories ≠ []) :
        InstrType C .memoryFill [.i32, .i32, .i32] []
    | memoryCopy {C : Context} (memory : C.memories ≠ []) :
        InstrType C .memoryCopy [.i32, .i32, .i32] []
    | intConst {C : Context} (t : IntType) (bits : BitVec t.width) :
        InstrType C (.intConst t bits) [] [.int t]
    | floatConst {C : Context} (t : FloatType) (bits : BitVec t.width) :
        InstrType C (.floatConst t bits) [] [.float t]
    | intUnOp {C : Context} (t : IntType) (op : IntUnOp) (valid : IntUnOpValid t op) :
        InstrType C (.intUnOp t op) [.int t] [.int t]
    | intBinOp {C : Context} (t : IntType) (op : IntBinOp) :
        InstrType C (.intBinOp t op) [.int t, .int t] [.int t]
    | intTestOp {C : Context} (t : IntType) (op : IntTestOp) :
        InstrType C (.intTestOp t op) [.int t] [.i32]
    | intRelOp {C : Context} (t : IntType) (op : IntRelOp) :
        InstrType C (.intRelOp t op) [.int t, .int t] [.i32]
    | floatUnOp {C : Context} (t : FloatType) (op : FloatUnOp) :
        InstrType C (.floatUnOp t op) [.float t] [.float t]
    | floatBinOp {C : Context} (t : FloatType) (op : FloatBinOp) :
        InstrType C (.floatBinOp t op) [.float t, .float t] [.float t]
    | floatRelOp {C : Context} (t : FloatType) (op : FloatRelOp) :
        InstrType C (.floatRelOp t op) [.float t, .float t] [.i32]
    | convert {C : Context} (op : ConvertOp) :
        InstrType C (.convert op) [(conversionType op).1] [(conversionType op).2]

  inductive ExprType : Context → Expr → ResultType → ResultType → Prop where
    | nil {C : Context} (ts : ResultType) : ExprType C [] ts ts
    | cons {C : Context} {i : Instr} {is : Expr} {a b c : ResultType}
        (hi : InstrType C i a b) (his : ExprType C is b c) : ExprType C (i :: is) a c
end

namespace ExprType

variable {i : Instr} {C : Context} {is js : Expr} {a b c : ResultType}

theorem singleton (h : InstrType C i a b) : ExprType C [i] a b :=
  .cons h (.nil b)

theorem append (h : ExprType C is a b) (h' : ExprType C js b c) :
    ExprType C (is ++ js) a c := by
  induction is generalizing a with
  | nil => cases h; exact h'
  | cons i is ih =>
    cases h with
    | cons hi his => exact .cons hi (ih his)

theorem append_iff : ExprType C (is ++ js) a c ↔
    ∃ b, ExprType C is a b ∧ ExprType C js b c := by
  constructor
  · intro h
    induction is generalizing a with
    | nil => exact ⟨a, .nil a, h⟩
    | cons i is ih =>
      cases h with
      | cons hi his =>
        obtain ⟨b, hl, hr⟩ := ih his
        exact ⟨b, .cons hi hl, hr⟩
  · rintro ⟨b, hl, hr⟩
    exact hl.append hr

theorem frame (pre : ResultType) (h : ExprType C is a b) :
    ExprType C is (pre ++ a) (pre ++ b) := by
  induction is generalizing a with
  | nil => cases h; exact .nil _
  | cons i is ih =>
    cases h with
    | cons hi his => exact .cons (.frame pre hi) (ih his)

theorem nil_iff : ExprType C [] a b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

end ExprType

end Silmaril.Wasm.Lime1.Validation
