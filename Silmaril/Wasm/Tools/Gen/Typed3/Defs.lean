module

public import Silmaril.Wasm.Tools.Gen.API.Defs
public import Silmaril.Wasm.Models.Syntax.Defs
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Validation.Check.TyOk

/-!
# A Core 3.0 generator that is valid by construction

`Silmaril.Wasm.Tools.Gen.Typed` builds typed Lime1 terms; this module builds typed **Core 3.0**
terms, whose erasure carries a Core 3.0 typing derivation (`Thms.module_validIn`), for the
features beyond Lime1:

* **GC**: `struct.new`/`get`/`set` on a struct type `$S` (`(mut i32) (mut i64)`),
  `array.new`/`get`/`set`/`len` on an array type `$A` (`(mut i32)`), `ref.i31`, `i31.get`,
  `ref.null`, `ref.is_null`;
* **exceptions**: two tags (`[]` and `[i32]`), `throw`, `throw_ref`, `try_table` with `catch`
  and `catch_all_ref`;
* **multi-memory** and **memory64**: up to three memories, each `i32` or `i64` addressed;
  loads, stores, `memory.size`/`grow`/`fill`/`copy` at any of them, with addresses of the
  memory's address type;
* **typed function references**: `ref.func`, `call_ref` and `ref.as_non_null` on the function
  type `$F` (`[i32] -> [i32]`), typed `select` on references;
* the Lime1 fragment (numeric operators, conversions, locals, globals, blocks, `if`, `br_if`,
  direct calls), multi-value function types.

The type section is fixed (`pre`: `$S`, `$A`, then the function types `sigs`); its closed
types `dts` are computed by silmaril's type-section checker, and the facts about them (the
section is valid, the closed value types are valid, expansions, subtyping) are proved once by
kernel evaluation of silmaril's sound checkers on these constants. Everything that depends on
the generated module (locals, globals, memories, functions, labels, the declared function
references) is a fact a constructor of `TE`/`TS`/`TA` carries, decided at generation time, so
there is no module-level check and no fallback.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Typed3

open Silmaril.Wasm Silmaril.Wasm.Validation

/-! ## Value types and the fixed type section -/

/-- The value types of generated code: numbers and nullable references to `$S`, `$A`, `$F`,
`i31` and `exn` (all defaultable). -/
inductive VT where
  | num (t : NumType)
  | sref | aref | fref | i31 | exn
  deriving DecidableEq, Repr, Inhabited

abbrev I32 : VT := .num (.int .i32)
abbrev I64 : VT := .num (.int .i64)
abbrev F32 : VT := .num (.float .f32)
abbrev F64 : VT := .num (.float .f64)

/-- Is a value type a number? -/
def VT.isNum : VT → Bool
  | .num _ => true
  | _ => false

/-- An index. -/
def idx {k : IndexKind} (n : Nat) : Idx k := ⟨Fin.ofNat _ n⟩

/-- The type index of `$F` (`[i32] -> [i32]`, the third function type). -/
def fIdx : Nat := 4

/-- The heap type of a reference type, in source syntax. -/
def srcHeap : VT → HeapType
  | .sref => .typeIdx (idx 0)
  | .aref => .typeIdx (idx 1)
  | .fref => .typeIdx (idx fIdx)
  | .i31 => .abstract .i31
  | .exn => .abstract .exn
  | .num _ => .abstract .none

/-- Source syntax of a value type. -/
def srcVT : VT → ValType
  | .num t => .num t
  | t => .ref ⟨true, srcHeap t⟩

/-- The function types: parameters and results. -/
def sigs : List (List VT × List VT) :=
  [([], []), ([I32], []), ([I32], [I32]), ([], [I32]), ([I64, I32], [I64]), ([F32, F64], [F64]),
   ([.sref], [I32]), ([I32, .aref], []), ([], [I32, I64]), ([F64], [F32]),
   ([.i31, .fref], [I32]), ([], [.sref]), ([.exn], []), ([I64], [])]

/-- A one-type group, final, with no supertype. -/
def single (ct : CompositeType) : RecType := ⟨[⟨true, [], ct⟩]⟩

/-- **The type section**: `$S`, `$A`, then one type per signature (type `2 + j`). -/
def pre : List RecType :=
  [single (.struct [⟨.var, .val (.num (.int .i32))⟩, ⟨.var, .val (.num (.int .i64))⟩]),
   single (.array ⟨.var, .val (.num (.int .i32))⟩)] ++
  sigs.map fun (ps, rs) => single (.func ⟨ps.map srcVT, rs.map srcVT⟩)

/-- The closed defined types of the section (silmaril's `typesCheck?`; `Thms`: `types_ok`). -/
def dts : List DefType := (typesCheck? RecTypeOkAt.check {} pre).getD []

def dS : DefType := dts.getD 0 default
def dA : DefType := dts.getD 1 default
/-- The defined type of signature `j`. -/
def sigD (j : Fin sigs.length) : DefType := dts.getD (2 + j.val) default

def j0 : Fin sigs.length := ⟨0, by decide⟩
def j1 : Fin sigs.length := ⟨1, by decide⟩
def j2 : Fin sigs.length := ⟨2, by decide⟩

def dF : DefType := sigD j2

/-- The closed heap type of a reference type. -/
def heapC : VT → CHeapType
  | .sref => .defHeap dS
  | .aref => .defHeap dA
  | .fref => .defHeap dF
  | .i31 => .abs .i31
  | .exn => .abs .exn
  | .num _ => .abs .none

/-- The closed value type. -/
def toC : VT → CValType
  | .num t => .num t
  | t => .refT true (heapC t)

/-- The type context of every generated context. -/
def Δ0 : TypeCtx := ⟨dts, []⟩

/-- The tags: `[] -> []` and `[i32] -> []`. -/
def tagDts : List DefType := [sigD j0, sigD j1]

/-- The facts every generated context satisfies: the fixed types and tags. -/
structure Wf (C : Context) : Prop where
  tctx : C.toTypeCtx = Δ0
  tags : C.tags = tagDts

/-- The value type of an address type. -/
def aVT (a : AddrType) : VT := .num (.int a.intType)

/-- Load facts: alignment within the access, packing narrower than the type. -/
def LoadOk (t : IntType) (p : Option (PackSize × Signedness)) (arg : MemArg) (a : AddrType) :
    Prop :=
  match p with
  | none => MemArgOk arg a t.width
  | some (sz, _) => sz.width < t.width ∧ MemArgOk arg a sz.width

instance (t : IntType) (p : Option (PackSize × Signedness)) (arg : MemArg) (a : AddrType) :
    Decidable (LoadOk t p arg a) := by
  unfold LoadOk; split <;> infer_instance

/-- Store facts. -/
def StoreOk (t : IntType) (p : Option PackSize) (arg : MemArg) (a : AddrType) : Prop :=
  match p with
  | none => MemArgOk arg a t.width
  | some sz => sz.width < t.width ∧ MemArgOk arg a sz.width

instance (t : IntType) (p : Option PackSize) (arg : MemArg) (a : AddrType) :
    Decidable (StoreOk t p arg a) := by
  unfold StoreOk; split <;> infer_instance

/-- The parameters of signature `j`. -/
def sigP (j : Fin sigs.length) : List VT := (sigs.get j).1
/-- The results of signature `j`. -/
def sigR (j : Fin sigs.length) : List VT := (sigs.get j).2

/-! ## Typed terms -/

mutual

/-- **Typed expressions**: push one value of type `t`. -/
inductive TE : Context → VT → Type where
  | iconst {C : Context} (t : IntType) (b : BitVec t.width) : TE C (.num (.int t))
  | fconst {C : Context} (t : FloatType) (b : BitVec t.width) : TE C (.num (.float t))
  | null {C : Context} (t : VT) (h : t.isNum = false) : TE C t
  | get {C : Context} {t : VT} (x : LocalIdx) (h : C.locals[x.toNat]? = some ⟨.set, toC t⟩) :
      TE C t
  | gget {C : Context} {t : VT} (x : GlobalIdx) (m : Mutability)
      (h : C.globals[x.toNat]? = some ⟨m, toC t⟩) : TE C t
  | ibin {C : Context} (t : IntType) (op : IntBinOp) (a b : TE C (.num (.int t))) :
      TE C (.num (.int t))
  | iun {C : Context} (t : IntType) (op : IntUnOp) (v : op.valid t = true)
      (a : TE C (.num (.int t))) : TE C (.num (.int t))
  | itest {C : Context} (t : IntType) (op : IntTestOp) (a : TE C (.num (.int t))) : TE C I32
  | irel {C : Context} (t : IntType) (op : IntRelOp) (a b : TE C (.num (.int t))) : TE C I32
  | fbin {C : Context} (t : FloatType) (op : FloatBinOp) (a b : TE C (.num (.float t))) :
      TE C (.num (.float t))
  | fun_ {C : Context} (t : FloatType) (op : FloatUnOp) (a : TE C (.num (.float t))) :
      TE C (.num (.float t))
  | frel {C : Context} (t : FloatType) (op : FloatRelOp) (a b : TE C (.num (.float t))) :
      TE C I32
  | cvt {C : Context} (op : ConvertOp) (a : TE C (.num op.source)) : TE C (.num op.target)
  | load {C : Context} (t : IntType) (p : Option (PackSize × Signedness)) (x : MemIdx)
      (arg : MemArg) (a : AddrType) (l : Limits) (hm : C.mems[x.toNat]? = some ⟨a, l⟩)
      (hok : LoadOk t p arg a) (addr : TE C (aVT a)) : TE C (.num (.int t))
  | fload {C : Context} (t : FloatType) (x : MemIdx) (arg : MemArg) (a : AddrType) (l : Limits)
      (hm : C.mems[x.toNat]? = some ⟨a, l⟩) (hok : MemArgOk arg a t.width)
      (addr : TE C (aVT a)) : TE C (.num (.float t))
  | msize {C : Context} (x : MemIdx) (a : AddrType) (l : Limits)
      (hm : C.mems[x.toNat]? = some ⟨a, l⟩) : TE C (aVT a)
  | mgrow {C : Context} (x : MemIdx) (a : AddrType) (l : Limits)
      (hm : C.mems[x.toNat]? = some ⟨a, l⟩) (v : TE C (aVT a)) : TE C (aVT a)
  | call {C : Context} {t : VT} (x : FuncIdx) (j : Fin sigs.length)
      (hf : C.funcs[x.toNat]? = some (sigD j)) (hr : sigR j = [t]) (args : TA C (sigP j)) :
      TE C t
  | select {C : Context} {t : VT} (a b : TE C t) (c : TE C I32) : TE C t
  | block {C : Context} {t : VT} (s : TS (C.withLabel [toC t])) (v : TE (C.withLabel [toC t]) t) :
      TE C t
  | ite {C : Context} {t : VT} (c : TE C I32) (a b : TE (C.withLabel [toC t]) t) : TE C t
  | tee {C : Context} {t : VT} (x : LocalIdx) (h : C.locals[x.toNat]? = some ⟨.set, toC t⟩)
      (a : TE C t) : TE C t
  | snew {C : Context} (a : TE C I32) (b : TE C I64) : TE C .sref
  | sget0 {C : Context} (a : TE C .sref) : TE C I32
  | sget1 {C : Context} (a : TE C .sref) : TE C I64
  | anew {C : Context} (v n : TE C I32) : TE C .aref
  | aget {C : Context} (a : TE C .aref) (i : TE C I32) : TE C I32
  | alen {C : Context} (a : TE C .aref) : TE C I32
  | i31new {C : Context} (a : TE C I32) : TE C .i31
  | i31get {C : Context} (sx : Signedness) (a : TE C .i31) : TE C I32
  | isnull {C : Context} {t : VT} (h : t.isNum = false) (a : TE C t) : TE C I32
  | asnn {C : Context} {t : VT} (h : t.isNum = false) (a : TE C t) : TE C t
  | rfunc {C : Context} (x : FuncIdx) (hf : C.funcs[x.toNat]? = some dF) (hr : x.toNat ∈ C.refs) :
      TE C .fref
  | callref {C : Context} (arg : TE C I32) (f : TE C .fref) : TE C I32
  | tryc {C : Context} (b : TE ((C.withLabel [toC I32]).withLabel [toC I32]) I32) : TE C I32
  | exnc {C : Context} (s : TS ((C.withLabel [toC .exn]).withLabel [])) : TE C .exn

/-- **Typed statements**: no stack effect. -/
inductive TS : Context → Type where
  | nop {C : Context} : TS C
  | drop {C : Context} {t : VT} (a : TE C t) : TS C
  | set {C : Context} {t : VT} (x : LocalIdx) (h : C.locals[x.toNat]? = some ⟨.set, toC t⟩)
      (a : TE C t) : TS C
  | gset {C : Context} {t : VT} (x : GlobalIdx) (h : C.globals[x.toNat]? = some ⟨.var, toC t⟩)
      (a : TE C t) : TS C
  | store {C : Context} (t : IntType) (p : Option PackSize) (x : MemIdx) (arg : MemArg)
      (a : AddrType) (l : Limits) (hm : C.mems[x.toNat]? = some ⟨a, l⟩)
      (hok : StoreOk t p arg a) (addr : TE C (aVT a)) (v : TE C (.num (.int t))) : TS C
  | fstore {C : Context} (t : FloatType) (x : MemIdx) (arg : MemArg) (a : AddrType) (l : Limits)
      (hm : C.mems[x.toNat]? = some ⟨a, l⟩) (hok : MemArgOk arg a t.width)
      (addr : TE C (aVT a)) (v : TE C (.num (.float t))) : TS C
  | fill {C : Context} (x : MemIdx) (a : AddrType) (l : Limits)
      (hm : C.mems[x.toNat]? = some ⟨a, l⟩) (d : TE C (aVT a)) (v : TE C I32)
      (n : TE C (aVT a)) : TS C
  | copy {C : Context} (x₁ x₂ : MemIdx) (a₁ a₂ : AddrType) (l₁ l₂ : Limits)
      (h₁ : C.mems[x₁.toNat]? = some ⟨a₁, l₁⟩) (h₂ : C.mems[x₂.toNat]? = some ⟨a₂, l₂⟩)
      (d : TE C (aVT a₁)) (s : TE C (aVT a₂)) (n : TE C (aVT (a₁.min a₂))) : TS C
  | block {C : Context} (s : TS (C.withLabel [])) : TS C
  | loop {C : Context} (s : TS (C.withLabel [])) : TS C
  | ite {C : Context} (c : TE C I32) (a b : TS (C.withLabel [])) : TS C
  | brIf {C : Context} (l : LabelIdx) (h : C.labels[l.toNat]? = some []) (c : TE C I32) : TS C
  | call {C : Context} (x : FuncIdx) (j : Fin sigs.length)
      (hf : C.funcs[x.toNat]? = some (sigD j)) (hr : sigR j = []) (args : TA C (sigP j)) : TS C
  | seq {C : Context} (a b : TS C) : TS C
  | sset {C : Context} (r : TE C .sref) (v : TE C I32) : TS C
  | aset {C : Context} (r : TE C .aref) (i v : TE C I32) : TS C
  | throw {C : Context} (a : TE C I32) : TS C
  | throwRef {C : Context} (a : TE C .exn) : TS C

/-- **Typed argument lists**: push `ts`. -/
inductive TA : Context → List VT → Type where
  | nil {C : Context} : TA C []
  | cons {C : Context} {t : VT} {ts : List VT} (a : TE C t) (r : TA C ts) : TA C (t :: ts)

end

/-! ## Erasure -/

mutual

/-- The instructions of an expression. -/
def TE.erase {C : Context} {t : VT} : TE C t → Expr
  | .iconst t b => [.intConst t b]
  | .fconst t b => [.floatConst t b]
  | .null t _ => [.refNull (srcHeap t)]
  | .get x _ => [.localGet x]
  | .gget x _ _ => [.globalGet x]
  | .ibin t op a b => a.erase ++ b.erase ++ [.intBinOp t op]
  | .iun t op _ a => a.erase ++ [.intUnOp t op]
  | .itest t op a => a.erase ++ [.intTestOp t op]
  | .irel t op a b => a.erase ++ b.erase ++ [.intRelOp t op]
  | .fbin t op a b => a.erase ++ b.erase ++ [.floatBinOp t op]
  | .fun_ t op a => a.erase ++ [.floatUnOp t op]
  | .frel t op a b => a.erase ++ b.erase ++ [.floatRelOp t op]
  | .cvt op a => a.erase ++ [.convert op]
  | .load t p x arg _ _ _ _ addr => addr.erase ++ [.intLoad t p x arg]
  | .fload t x arg _ _ _ _ addr => addr.erase ++ [.floatLoad t x arg]
  | .msize x _ _ _ => [.memorySize x]
  | .mgrow x _ _ _ v => v.erase ++ [.memoryGrow x]
  | .call x _ _ _ args => args.erase ++ [.call x]
  | @TE.select _ t a b c => a.erase ++ b.erase ++ c.erase ++ [.select (some [srcVT t])]
  | @TE.block _ t s v => [.block (.value (srcVT t)) (s.erase ++ v.erase)]
  | @TE.ite _ t c a b => c.erase ++ [.if_ (.value (srcVT t)) a.erase b.erase]
  | .tee x _ a => a.erase ++ [.localTee x]
  | .snew a b => a.erase ++ b.erase ++ [.structNew (idx 0)]
  | .sget0 a => a.erase ++ [.structGet none (idx 0) (idx 0)]
  | .sget1 a => a.erase ++ [.structGet none (idx 0) (idx 1)]
  | .anew v n => v.erase ++ n.erase ++ [.arrayNew (idx 1)]
  | .aget a i => a.erase ++ i.erase ++ [.arrayGet none (idx 1)]
  | .alen a => a.erase ++ [.arrayLen]
  | .i31new a => a.erase ++ [.refI31]
  | .i31get sx a => a.erase ++ [.i31Get sx]
  | .isnull _ a => a.erase ++ [.refIsNull]
  | .asnn _ a => a.erase ++ [.refAsNonNull]
  | .rfunc x _ _ => [.refFunc x]
  | .callref arg f => arg.erase ++ f.erase ++ [.callRef (idx fIdx)]
  | .tryc b =>
      [.block (.value (srcVT I32)) [.tryTable (.value (srcVT I32)) [.catch_ (idx 1) (idx 0)] b.erase]]
  | .exnc s =>
      [.block (.value (srcVT .exn)) [.tryTable .empty [.catchAllRef (idx 0)] s.erase, .throw (idx 0)]]

/-- The instructions of a statement. -/
def TS.erase {C : Context} : TS C → Expr
  | .nop => [.nop]
  | .drop a => a.erase ++ [.drop]
  | .set x _ a => a.erase ++ [.localSet x]
  | .gset x _ a => a.erase ++ [.globalSet x]
  | .store t p x arg _ _ _ _ addr v => addr.erase ++ v.erase ++ [.intStore t p x arg]
  | .fstore t x arg _ _ _ _ addr v => addr.erase ++ v.erase ++ [.floatStore t x arg]
  | .fill x _ _ _ d v n => d.erase ++ v.erase ++ n.erase ++ [.memoryFill x]
  | .copy x₁ x₂ _ _ _ _ _ _ d s n => d.erase ++ s.erase ++ n.erase ++ [.memoryCopy x₁ x₂]
  | .block s => [.block .empty s.erase]
  | .loop s => [.loop .empty s.erase]
  | .ite c a b => c.erase ++ [.if_ .empty a.erase b.erase]
  | .brIf l _ c => c.erase ++ [.brIf l]
  | .call x _ _ _ args => args.erase ++ [.call x]
  | .seq a b => a.erase ++ b.erase
  | .sset r v => r.erase ++ v.erase ++ [.structSet (idx 0) (idx 0)]
  | .aset r i v => r.erase ++ i.erase ++ v.erase ++ [.arraySet (idx 1)]
  | .throw a => a.erase ++ [.throw (idx 1)]
  | .throwRef a => a.erase ++ [.throwRef]

/-- The instructions of an argument list. -/
def TA.erase {C : Context} {ts : List VT} : TA C ts → Expr
  | .nil => []
  | .cons a r => a.erase ++ r.erase

end

/-! ## Generation -/

/-- A uniform choice, `none` for the empty list. -/
def pickOpt {α : Type} (l : List α) : Rand (Option α) := do
  if l.isEmpty then return none
  return l[(← Rand.nat l.length)]?

/-- The locals of type `t` (the first 64). -/
def localsOf (C : Context) (t : VT) :
    List {x : LocalIdx // C.locals[x.toNat]? = some ⟨.set, toC t⟩} :=
  (List.range (min C.locals.length 64)).filterMap fun i =>
    if h : C.locals[(idx i : LocalIdx).toNat]? = some ⟨.set, toC t⟩ then some ⟨idx i, h⟩ else none

/-- The globals of type `t` (the first 64). -/
def globalsOf (C : Context) (t : VT) :
    List ((x : GlobalIdx) × (m : Mutability) ×' C.globals[x.toNat]? = some ⟨m, toC t⟩) :=
  (List.range (min C.globals.length 64)).filterMap fun i =>
    match h : C.globals[(idx i : GlobalIdx).toNat]? with
    | some gt => if hv : gt.type = toC t then some ⟨idx i, gt.mutability, by rw [h, ← hv]⟩ else none
    | none => none

/-- The mutable globals of type `t`. -/
def mutGlobalsOf (C : Context) (t : VT) :
    List {x : GlobalIdx // C.globals[x.toNat]? = some ⟨.var, toC t⟩} :=
  (List.range (min C.globals.length 64)).filterMap fun i =>
    if h : C.globals[(idx i : GlobalIdx).toNat]? = some ⟨.var, toC t⟩ then some ⟨idx i, h⟩ else none

/-- The functions whose signature has the results `rs` (the first 64). -/
def funcsWith (C : Context) (rs : List VT) :
    List ((x : FuncIdx) × (j : Fin sigs.length) ×'
      (sigR j = rs ∧ C.funcs[x.toNat]? = some (sigD j))) :=
  (List.range (min C.funcs.length 64)).flatMap fun i =>
    (List.finRange sigs.length).filterMap fun j =>
      if h : sigR j = rs ∧ C.funcs[(idx i : FuncIdx).toNat]? = some (sigD j) then
        some ⟨idx i, j, h⟩
      else none

/-- The labels with no values. -/
def emptyLabels (C : Context) : List {l : LabelIdx // C.labels[l.toNat]? = some []} :=
  (List.range (min C.labels.length 64)).filterMap fun i =>
    if h : C.labels[(idx i : LabelIdx).toNat]? = some [] then some ⟨idx i, h⟩ else none

/-- The memories. -/
def memsOf (C : Context) :
    List ((x : MemIdx) × (a : AddrType) × (l : Limits) ×' C.mems[x.toNat]? = some ⟨a, l⟩) :=
  (List.range (min C.mems.length 8)).filterMap fun i =>
    match h : C.mems[(idx i : MemIdx).toNat]? with
    | some mt => some ⟨idx i, mt.address, mt.limits, by rw [h]⟩
    | none => none

/-- The functions of type `$F` that may be referenced. -/
def refFuncs (C : Context) : List {x : FuncIdx // C.funcs[x.toNat]? = some dF ∧ x.toNat ∈ C.refs} :=
  (List.range (min C.funcs.length 64)).filterMap fun i =>
    if h : C.funcs[(idx i : FuncIdx).toNat]? = some dF ∧ (idx i : FuncIdx).toNat ∈ C.refs then
      some ⟨idx i, h⟩
    else none

/-- A small memory offset. -/
def offset : Rand Nat := Rand.pick [0, 0, 1, 8, 1024] 0

/-- A random 64-bit number. -/
def bits : Rand Nat := fun r => let (x, r') := r.next; (x.toNat, r')

/-- An interesting integer of a width. -/
def intBits (w : Nat) : Rand Nat := do
  match ← Rand.nat 6 with
  | 0 => pure 0
  | 1 => pure 1
  | 2 => pure (2 ^ w - 1)
  | 3 => pure (2 ^ (w - 1))
  | 4 => Rand.nat 256
  | _ => return (← bits) % 2 ^ w

/-- A constant of a type (`ref.null` for references). -/
def const (C : Context) : (t : VT) → Rand (TE C t)
  | .num (.int it) => do return .iconst it (BitVec.ofNat _ (← intBits it.width))
  | .num (.float ft) => do return .fconst ft (BitVec.ofNat _ (← intBits ft.width))
  | .sref => pure (.null .sref rfl)
  | .aref => pure (.null .aref rfl)
  | .fref => pure (.null .fref rfl)
  | .i31 => pure (.null .i31 rfl)
  | .exn => pure (.null .exn rfl)

def intBinOps : List IntBinOp :=
  [.add, .sub, .mul, .div .signed, .div .unsigned, .rem .signed, .rem .unsigned, .and, .or, .xor,
    .shl, .shr .signed, .shr .unsigned, .rotl, .rotr]
def intRelOps : List IntRelOp :=
  [.eq, .ne, .lt .signed, .lt .unsigned, .gt .signed, .gt .unsigned, .le .signed, .le .unsigned,
    .ge .signed, .ge .unsigned]
def floatBinOps : List FloatBinOp := [.add, .sub, .mul, .div, .min, .max, .copysign]
def floatUnOps : List FloatUnOp := [.abs, .neg, .sqrt, .ceil, .floor, .trunc, .nearest]
def floatRelOps : List FloatRelOp := [.eq, .ne, .lt, .gt, .le, .ge]
def intUnOps : List IntUnOp := [.clz, .ctz, .popcnt, .extend .i8, .extend .i16, .extend .i32]

/-- The unary integer operators valid at `t`. -/
def unOpsAt (t : IntType) : List {op : IntUnOp // op.valid t = true} :=
  intUnOps.filterMap fun op => if h : op.valid t = true then some ⟨op, h⟩ else none

/-- Every scalar conversion. -/
def convs : List ConvertOp :=
  [.wrap, .extend .signed, .extend .unsigned] ++
  ([IntType.i32, .i64].flatMap fun i => [FloatType.f32, .f64].flatMap fun f =>
    [.trunc f i .signed, .trunc f i .unsigned, .truncSat f i .signed, .truncSat f i .unsigned,
     .convert i f .signed, .convert i f .unsigned]) ++
  [.demote, .promote, .reinterpretInt .f32, .reinterpretInt .f64, .reinterpretFloat .i32,
   .reinterpretFloat .i64]

/-- The conversions to `t`. -/
def convsTo (t : NumType) : List {op : ConvertOp // op.target = t} :=
  convs.filterMap fun op => if h : op.target = t then some ⟨op, h⟩ else none

/-- Integer loads: type, packing, alignment. -/
def intLoads : List (IntType × Option (PackSize × Signedness) × Nat) :=
  [(.i32, none, 2), (.i32, some (.i8, .signed), 0), (.i32, some (.i16, .unsigned), 1),
   (.i64, none, 3), (.i64, some (.i32, .signed), 2), (.i64, some (.i8, .unsigned), 0)]

/-- Integer stores. -/
def intStores : List (IntType × Option PackSize × Nat) :=
  [(.i32, none, 2), (.i32, some .i8, 0), (.i64, none, 3), (.i64, some .i16, 1)]

/-- A memory argument. -/
def marg (align off : Nat) : MemArg := ⟨Fin.ofNat _ align, Fin.ofNat _ off⟩

/-- The natural alignment of a float. -/
def falign : FloatType → Nat
  | .f32 => 2
  | .f64 => 3

/-- The value types of locals, globals and dropped values. -/
def allVTs : List VT := [I32, I64, F32, F64, .sref, .aref, .fref, .i31, .exn]

/-- The reference types. -/
def refVTs : List {t : VT // t.isNum = false} :=
  [⟨.sref, rfl⟩, ⟨.aref, rfl⟩, ⟨.fref, rfl⟩, ⟨.i31, rfl⟩, ⟨.exn, rfl⟩]

/-- Pick among generators (the first when the draw is out of range). -/
def oneOf {α : Type} (d : Rand α) (gs : List (Rand α)) : Rand α := do
  (gs.getD (← Rand.nat gs.length) d)

mutual

/-- **A typed expression of type `t`**, depth at most `n`. -/
def genTE : Nat → (C : Context) → (t : VT) → Rand (TE C t)
  | 0, C, t => do
    match ← pickOpt (localsOf C t) with
    | some ⟨x, h⟩ => if ← Rand.bool then return .get x h else const C t
    | none => const C t
  | n + 1, C, t => do
    let sub := genTE n C
    let opsT : List (Rand (TE C t)) :=
      [ genTE 0 C t,
        do return .select (← sub t) (← sub t) (← sub I32),
        do
          let C' := C.withLabel [toC t]
          return .block (← genTS n C') (← genTE n C' t),
        do
          let C' := C.withLabel [toC t]
          return .ite (← sub I32) (← genTE n C' t) (← genTE n C' t),
        do
          match ← pickOpt (localsOf C t) with
          | some ⟨x, h⟩ => return .tee x h (← sub t)
          | none => const C t,
        do
          match ← pickOpt (globalsOf C t) with
          | some ⟨x, m, h⟩ => return .gget x m h
          | none => const C t,
        do
          match ← pickOpt (funcsWith C [t]) with
          | some ⟨x, j, hr, hf⟩ => return .call x j hf hr (← genTA n C (sigP j))
          | none => const C t ]
    let opsK : List (Rand (TE C t)) := match t with
      | .num (.int it) =>
        [ do return .ibin it (← Rand.pick intBinOps .add) (← sub (.num (.int it)))
                (← sub (.num (.int it))),
          do
            match ← pickOpt (unOpsAt it) with
            | some ⟨op, v⟩ => return .iun it op v (← sub (.num (.int it)))
            | none => const C (.num (.int it)),
          do
            match ← pickOpt (convsTo (.int it)) with
            | some ⟨op, ht⟩ => return ht ▸ TE.cvt op (← sub (.num op.source))
            | none => const C (.num (.int it)),
          do
            match ← pickOpt (memsOf C) with
            | some ⟨x, a, l, hm⟩ =>
              match ← pickOpt (intLoads.filter fun e => e.1 == it) with
              | some (t', p, al) =>
                let arg := marg al (← offset)
                if ht : t' = it then
                  if hok : LoadOk t' p arg a then
                    return ht ▸ TE.load t' p x arg a l hm hok (← sub (aVT a))
                  else const C (.num (.int it))
                else const C (.num (.int it))
              | none => const C (.num (.int it))
            | none => const C (.num (.int it)),
          do
            match ← pickOpt (memsOf C) with
            | some ⟨x, a, l, hm⟩ =>
              if ht : aVT a = .num (.int it) then
                if ← Rand.bool then return ht ▸ TE.msize x a l hm
                else return ht ▸ TE.mgrow x a l hm (← sub (aVT a))
              else const C (.num (.int it))
            | none => const C (.num (.int it)) ] ++
        (match it with
          | .i32 =>
            [ do
                let u ← Rand.pick [IntType.i32, .i64] .i32
                if ← Rand.bool then return .itest u .eqz (← sub (.num (.int u)))
                else
                  return .irel u (← Rand.pick intRelOps .eq) (← sub (.num (.int u)))
                    (← sub (.num (.int u))),
              do
                let f ← Rand.pick [FloatType.f32, .f64] .f32
                return .frel f (← Rand.pick floatRelOps .eq) (← sub (.num (.float f)))
                  (← sub (.num (.float f))),
              do return .sget0 (← sub .sref),
              do return .aget (← sub .aref) (← sub I32),
              do return .alen (← sub .aref),
              do return .i31get (← Rand.pick [.signed, .unsigned] .signed) (← sub .i31),
              do
                let ⟨u, h⟩ ← Rand.pick refVTs ⟨.sref, rfl⟩
                return .isnull h (← sub u),
              do return .callref (← sub I32) (← sub .fref),
              do return .tryc (← genTE n ((C.withLabel [toC I32]).withLabel [toC I32]) I32) ]
          | .i64 => [ do return .sget1 (← sub .sref) ])
      | .num (.float ft) =>
        [ do return .fbin ft (← Rand.pick floatBinOps .add) (← sub (.num (.float ft)))
                (← sub (.num (.float ft))),
          do return .fun_ ft (← Rand.pick floatUnOps .neg) (← sub (.num (.float ft))),
          do
            match ← pickOpt (convsTo (.float ft)) with
            | some ⟨op, ht⟩ => return ht ▸ TE.cvt op (← sub (.num op.source))
            | none => const C (.num (.float ft)),
          do
            match ← pickOpt (memsOf C) with
            | some ⟨x, a, l, hm⟩ =>
              let arg := marg (falign ft) (← offset)
              if hok : MemArgOk arg a ft.width then
                return .fload ft x arg a l hm hok (← sub (aVT a))
              else const C (.num (.float ft))
            | none => const C (.num (.float ft)) ]
      | .sref => [ do return .snew (← sub I32) (← sub I64), do return .asnn rfl (← sub .sref) ]
      | .aref => [ do return .anew (← sub I32) (← sub I32), do return .asnn rfl (← sub .aref) ]
      | .fref =>
        [ do
            match ← pickOpt (refFuncs C) with
            | some ⟨x, hf, hr⟩ => return .rfunc x hf hr
            | none => const C .fref,
          do return .asnn rfl (← sub .fref) ]
      | .i31 => [ do return .i31new (← sub I32), do return .asnn rfl (← sub .i31) ]
      | .exn => [ do return .exnc (← genTS n ((C.withLabel [toC .exn]).withLabel [])) ]
    oneOf (const C t) (opsT ++ opsK)

/-- **A typed statement**, depth at most `n`. -/
def genTS : Nat → (C : Context) → Rand (TS C)
  | 0, _ => pure TS.nop
  | n + 1, C => do
    let e := genTE n C
    let ops : List (Rand (TS C)) :=
      [ pure TS.nop,
        do return TS.drop (← e (← Rand.pick allVTs I32)),
        do return TS.seq (← genTS n C) (← genTS n C),
        do return TS.block (← genTS n (C.withLabel [])),
        do return TS.loop (← genTS n (C.withLabel [])),
        do return TS.ite (← e I32) (← genTS n (C.withLabel [])) (← genTS n (C.withLabel [])),
        do
          let t ← Rand.pick allVTs I32
          match ← pickOpt (localsOf C t) with
          | some ⟨x, h⟩ => return TS.set x h (← e t)
          | none => pure TS.nop,
        do
          let t ← Rand.pick allVTs I32
          match ← pickOpt (mutGlobalsOf C t) with
          | some ⟨x, h⟩ => return TS.gset x h (← e t)
          | none => pure TS.nop,
        do
          match ← pickOpt (emptyLabels C) with
          | some ⟨l, h⟩ => return TS.brIf l h (← e I32)
          | none => pure TS.nop,
        do
          match ← pickOpt (funcsWith C []) with
          | some ⟨x, j, hr, hf⟩ => return TS.call x j hf hr (← genTA n C (sigP j))
          | none => pure TS.nop,
        do
          match ← pickOpt (memsOf C) with
          | some ⟨x, a, l, hm⟩ =>
            match ← pickOpt intStores with
            | some (t, p, al) =>
              let arg := marg al (← offset)
              if hok : StoreOk t p arg a then
                return TS.store t p x arg a l hm hok (← e (aVT a)) (← e (.num (.int t)))
              else pure TS.nop
            | none => pure TS.nop
          | none => pure TS.nop,
        do
          match ← pickOpt (memsOf C) with
          | some ⟨x, a, l, hm⟩ =>
            let ft ← Rand.pick [FloatType.f32, .f64] .f32
            let arg := marg (falign ft) (← offset)
            if hok : MemArgOk arg a ft.width then
              return TS.fstore ft x arg a l hm hok (← e (aVT a)) (← e (.num (.float ft)))
            else pure TS.nop
          | none => pure TS.nop,
        do
          match ← pickOpt (memsOf C) with
          | some ⟨x, a, l, hm⟩ => return TS.fill x a l hm (← e (aVT a)) (← e I32) (← e (aVT a))
          | none => pure TS.nop,
        do
          match ← pickOpt (memsOf C), ← pickOpt (memsOf C) with
          | some ⟨x₁, a₁, l₁, h₁⟩, some ⟨x₂, a₂, l₂, h₂⟩ =>
            return TS.copy x₁ x₂ a₁ a₂ l₁ l₂ h₁ h₂ (← e (aVT a₁)) (← e (aVT a₂))
              (← e (aVT (a₁.min a₂)))
          | _, _ => pure TS.nop,
        do return TS.sset (← e .sref) (← e I32),
        do return TS.aset (← e .aref) (← e I32) (← e I32),
        do if (← Rand.nat 4) == 0 then return TS.throw (← e I32) else pure TS.nop,
        do if (← Rand.nat 4) == 0 then return TS.throwRef (← e .exn) else pure TS.nop ]
    oneOf (pure TS.nop) ops

/-- **A typed argument list** for `ts`. -/
def genTA : Nat → (C : Context) → (ts : List VT) → Rand (TA C ts)
  | _, _, [] => pure .nil
  | n, C, t :: ts => do return .cons (← genTE n C t) (← genTA n C ts)

end

/-! ## Modules -/

/-- The limits of every memory: one page to four. -/
def memLimits : Limits := ⟨Fin.ofNat _ 1, some (Fin.ofNat _ 4)⟩

/-- The skeleton of a module: everything but the code. -/
structure Skel where
  /-- Each function's signature. -/
  fsigs : List (Fin sigs.length)
  /-- Globals: type, mutability, initial bits. -/
  gspecs : List (VT × Bool × Nat)
  /-- The memories' address types. -/
  mems : List AddrType

/-- The initialiser of a global. -/
def ginit : VT → Nat → Expr
  | .num (.int it), b => [.intConst it (BitVec.ofNat _ b)]
  | .num (.float ft), b => [.floatConst ft (BitVec.ofNat _ b)]
  | t, _ => [.refNull (srcHeap t)]

/-- A global's mutability. -/
def gmut (m : Bool) : Mutability := if m then .var else .const

namespace Skel

def memTypes (k : Skel) : List MemoryType := k.mems.map (⟨·, memLimits⟩)

def globals (k : Skel) : List Global :=
  k.gspecs.map fun (t, m, b) => ⟨⟨gmut m, srcVT t⟩, ginit t b⟩

/-- Export names (at most ten functions). -/
def exportNames : List String := ["f0", "f1", "f2", "f3", "f4", "f5", "f6", "f7", "f8", "f9"]

def exports (k : Skel) : List Export :=
  (exportNames.take k.fsigs.length).zipIdx.map fun (n, i) => ⟨n, .func (idx i)⟩

/-- The tags: the types of signatures 0 and 1. -/
def tagTypes : List TagType := [idx 2, idx 3]

/-- The module of a skeleton, with no functions. -/
def module0 (k : Skel) : Module where
  types := pre
  tags := tagTypes
  globals := k.globals
  memories := k.memTypes
  exports := k.exports

/-- The closed global types. -/
def gts (k : Skel) : List CGlobalType := k.gspecs.map fun (t, m, _) => ⟨gmut m, toC t⟩

/-- **The validation context of a skeleton's module.** -/
def ctx (k : Skel) : Context :=
  { types := dts, tags := tagDts, globals := k.gts, mems := k.memTypes,
    funcs := k.fsigs.map sigD, refs := funcIdxNonFuncs k.module0 }

end Skel

/-- The local types of declared locals. -/
def lts (ls : List VT) : List LocalType := ls.map fun t => ⟨.set, toC t⟩

/-- The context of a function body. -/
def fctx (C0 : Context) (j : Fin sigs.length) (ls : List VT) : Context :=
  C0.funcBody ((sigP j).map toC) ((sigR j).map toC) (lts ls)

/-- A function's code. -/
structure FBody (C0 : Context) (j : Fin sigs.length) where
  locals : List VT
  stmts : TS (fctx C0 j locals)
  rets : TA (fctx C0 j locals) (sigR j)

/-- The code of every function, in order. -/
inductive Bodies (C0 : Context) : List (Fin sigs.length) → Type where
  | nil : Bodies C0 []
  | cons {j : Fin sigs.length} {l : List (Fin sigs.length)} (b : FBody C0 j) (r : Bodies C0 l) :
      Bodies C0 (j :: l)

/-- The functions. -/
def Bodies.funcs {C0 : Context} : {l : List (Fin sigs.length)} → Bodies C0 l → List Func
  | [], .nil => []
  | j :: _, .cons b r => ⟨idx (2 + j.val), b.locals.map srcVT, b.stmts.erase ++ b.rets.erase⟩ :: r.funcs

/-- Generate the code of every function. -/
def genBodies (C0 : Context) (depth : Nat) : (l : List (Fin sigs.length)) → Rand (Bodies C0 l)
  | [] => pure .nil
  | j :: l => do
    let locals ← Rand.list (← Rand.nat 4) (Rand.pick allVTs I32)
    let C := fctx C0 j locals
    let k ← Rand.range 1 (2 + depth)
    let stmts ← Rand.list k (genTS depth C)
    let s : TS C := stmts.foldr .seq .nop
    let rets ← genTA depth C (sigR j)
    return .cons ⟨locals, s, rets⟩ (← genBodies C0 depth l)

/-- The skeleton of a seed. -/
def skel (size : Nat) : Rand Skel := do
  let nf ← Rand.range 1 (1 + min 10 (size / 2))
  let fsigs ← Rand.list nf (do
    let j ← Rand.nat sigs.length
    return if h : j < sigs.length then ⟨j, h⟩ else ⟨0, by decide⟩)
  let ng ← Rand.nat 5
  let gspecs ← Rand.list ng (do return (← Rand.pick allVTs I32, ← Rand.bool, ← intBits 32))
  let nm ← Rand.nat 4
  let mems ← Rand.list nm (Rand.pick [AddrType.i32, .i64] .i32)
  return ⟨fsigs, gspecs, mems⟩

/-- The module of a skeleton and its code. -/
def Skel.module (k : Skel) (bs : Bodies k.ctx k.fsigs) : Module :=
  { k.module0 with funcs := bs.funcs }

/-- **The typed Core 3.0 generator**: valid by construction (`Thms`). The state is threaded by
hand so that the result is visibly `k.module bs`. -/
def module (size : Nat) : Rand Module := fun r =>
  let p₁ := skel size r
  let p₂ := genBodies p₁.1.ctx (min 4 (1 + size / 8)) p₁.1.fsigs p₁.2
  (p₁.1.module p₂.1, p₂.2)

end Silmaril.Wasm.Tools.Gen.Typed3
