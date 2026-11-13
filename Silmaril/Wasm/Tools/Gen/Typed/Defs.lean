module

public import Silmaril.Wasm.Tools.Gen.API.Defs
public import Silmaril.Wasm.Models.Syntax.Defs
public import Silmaril.Wasm.Lime1.Validation.Modules
public import Silmaril.Wasm.Lime1.ToCore

/-!
# A generator that is valid by construction

The raw generator of `Silmaril.Wasm.Tools.Gen.Core` aims at validity and is checked. This one
**needs no checker**: it builds *typed* terms, whose erasure is well typed by construction
(`Thms`: `module_validIn`), for every feature set `S ≥ v10`.

* `TE S C t`, `TS S C`, `TA S C ts` (one mutual family): expressions pushing one value of type
  `t`, statements with no stack effect, and argument lists pushing `ts`, in a Lime1 validation
  context `C` (`Silmaril.Wasm.Lime1.Validation.Context`). A constructor carries the facts its
  instruction needs: the local, global or function it names and its type, the memory, the label
  and its type, the alignment of an access, and, for the capabilities beyond the MVP (sign
  extension, saturating conversions, `memory.fill`/`memory.copy`), that `S` has them. `erase`
  gives the Lime1 instructions.
* Covered: integer and float constants, unary, binary, test and relational operators,
  conversions (saturating ones with `satConv`), sign extension (`signExt`), `local.get`/`set`/
  `tee`, `global.get`/`set`, loads, stores, `memory.size`/`grow`/`fill`/`copy`, `select`,
  `block`/`loop`/`if` with a result or none, `br_if`, `drop`, `nop` and direct calls.
* `genTE`, `genTS`, `genTA`: seeded generators of typed terms (each choice is among
  constructors whose facts hold, decided at generation time; there is always a constant to fall
  back on, so there is no module-level fallback).
* `module S size`: function types (several results only with multi-value), functions, constant
  globals, an optional memory with a data segment, exports; the Lime1 module `lmodule` and its
  Core 3.0 image (`Silmaril.Wasm.Lime1.Module.toCore`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Typed

open Silmaril.Wasm Silmaril.Wasm.Lime1.Validation Silmaril.Wasm.Models

/-- Value types (Lime1's: numeric). -/
abbrev VT := V1.ValType

/-- `i32`. -/
abbrev I32 : VT := .int .i32

/-- An index. -/
def idx {k : IndexKind} (n : Nat) : Idx k := ⟨Fin.ofNat _ n⟩

instance (t : IntType) (op : Lime1.IntUnOp) : Decidable (IntUnOpValid t op) := by
  unfold IntUnOpValid; split <;> infer_instance

instance (arg : V1.MemArg) (w : Nat) : Decidable (Aligned arg w) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (t : IntType) (p : Option V1.PackSize) (arg : V1.MemArg) :
    Decidable (IntAccess t p arg) := by
  unfold IntAccess; split <;> infer_instance

mutual

/-- **Typed expressions**: push one value of type `t`. -/
inductive TE (S : FeatureSet) : Context → VT → Type where
  | iconst {C : Context} (t : IntType) (b : BitVec t.width) : TE S C (.int t)
  | fconst {C : Context} (t : FloatType) (b : BitVec t.width) : TE S C (.float t)
  | get {C : Context} {t : VT} (x : LocalIdx) (h : C.locals[x.toNat]? = some t) : TE S C t
  | gget {C : Context} {t : VT} (x : GlobalIdx) (m : Mutability)
      (h : C.globals[x.toNat]? = some ⟨m, t⟩) : TE S C t
  | ibin {C : Context} (t : IntType) (op : IntBinOp) (a b : TE S C (.int t)) : TE S C (.int t)
  | iun {C : Context} (t : IntType) (op : Lime1.IntUnOp) (v : IntUnOpValid t op)
      (hf : IntUnOp.inFeatB S op.toCore = true) (a : TE S C (.int t)) : TE S C (.int t)
  | itest {C : Context} (t : IntType) (op : IntTestOp) (a : TE S C (.int t)) : TE S C I32
  | irel {C : Context} (t : IntType) (op : IntRelOp) (a b : TE S C (.int t)) : TE S C I32
  | fbin {C : Context} (t : FloatType) (op : FloatBinOp) (a b : TE S C (.float t)) :
      TE S C (.float t)
  | fun_ {C : Context} (t : FloatType) (op : FloatUnOp) (a : TE S C (.float t)) :
      TE S C (.float t)
  | frel {C : Context} (t : FloatType) (op : FloatRelOp) (a b : TE S C (.float t)) : TE S C I32
  | cvt {C : Context} (op : ConvertOp) (hf : ConvertOp.inFeatB S op = true)
      (a : TE S C op.source) : TE S C op.target
  | load {C : Context} (t : IntType) (p : Option (V1.PackSize × Signedness)) (arg : V1.MemArg)
      (hm : C.memories ≠ []) (acc : IntAccess t (p.map Prod.fst) arg) (a : TE S C I32) :
      TE S C (.int t)
  | fload {C : Context} (t : FloatType) (arg : V1.MemArg) (hm : C.memories ≠ [])
      (al : Aligned arg t.width) (a : TE S C I32) : TE S C (.float t)
  | msize {C : Context} (hm : C.memories ≠ []) : TE S C I32
  | mgrow {C : Context} (hm : C.memories ≠ []) (a : TE S C I32) : TE S C I32
  | call {C : Context} {t : VT} (x : FuncIdx) (ft : V1.FuncType)
      (h : C.funcs[x.toNat]? = some ft) (hr : ft.results = [t]) (args : TA S C ft.params) :
      TE S C t
  | select {C : Context} {t : VT} (a b : TE S C t) (c : TE S C I32) : TE S C t
  | block {C : Context} {t : VT} (s : TS S (C.withLabel [t])) (v : TE S (C.withLabel [t]) t) :
      TE S C t
  | ite {C : Context} {t : VT} (c : TE S C I32) (a b : TE S (C.withLabel [t]) t) : TE S C t
  | tee {C : Context} {t : VT} (x : LocalIdx) (h : C.locals[x.toNat]? = some t) (a : TE S C t) :
      TE S C t

/-- **Typed statements**: no stack effect. -/
inductive TS (S : FeatureSet) : Context → Type where
  | nop {C : Context} : TS S C
  | drop {C : Context} {t : VT} (a : TE S C t) : TS S C
  | set {C : Context} {t : VT} (x : LocalIdx) (h : C.locals[x.toNat]? = some t) (a : TE S C t) :
      TS S C
  | gset {C : Context} {t : VT} (x : GlobalIdx) (h : C.globals[x.toNat]? = some ⟨.var, t⟩)
      (a : TE S C t) : TS S C
  | store {C : Context} (t : IntType) (p : Option V1.PackSize) (arg : V1.MemArg)
      (hm : C.memories ≠ []) (acc : IntAccess t p arg) (a : TE S C I32) (v : TE S C (.int t)) :
      TS S C
  | fstore {C : Context} (t : FloatType) (arg : V1.MemArg) (hm : C.memories ≠ [])
      (al : Aligned arg t.width) (a : TE S C I32) (v : TE S C (.float t)) : TS S C
  | fill {C : Context} (hm : C.memories ≠ []) (hf : S.has .bulkMemoryOpt = true)
      (a b c : TE S C I32) : TS S C
  | copy {C : Context} (hm : C.memories ≠ []) (hf : S.has .bulkMemoryOpt = true)
      (a b c : TE S C I32) : TS S C
  | block {C : Context} (s : TS S (C.withLabel [])) : TS S C
  | loop {C : Context} (s : TS S (C.withLabel [])) : TS S C
  | ite {C : Context} (c : TE S C I32) (a b : TS S (C.withLabel [])) : TS S C
  | brIf {C : Context} (l : LabelIdx) (h : C.labels[l.toNat]? = some []) (c : TE S C I32) :
      TS S C
  | call {C : Context} (x : FuncIdx) (ft : V1.FuncType) (h : C.funcs[x.toNat]? = some ft)
      (hr : ft.results = []) (args : TA S C ft.params) : TS S C
  | seq {C : Context} (a b : TS S C) : TS S C

/-- **Typed argument lists**: push `ts`. -/
inductive TA (S : FeatureSet) : Context → List VT → Type where
  | nil {C : Context} : TA S C []
  | cons {C : Context} {t : VT} {ts : List VT} (a : TE S C t) (r : TA S C ts) : TA S C (t :: ts)

end

variable {S : FeatureSet}

mutual

/-- The instructions of an expression. -/
def TE.erase {C : Context} {t : VT} : TE S C t → Lime1.Expr
  | .iconst t b => [.intConst t b]
  | .fconst t b => [.floatConst t b]
  | .get x _ => [.localGet x]
  | .gget x _ _ => [.globalGet x]
  | .ibin t op a b => a.erase ++ b.erase ++ [.intBinOp t op]
  | .iun t op _ _ a => a.erase ++ [.intUnOp t op]
  | .itest t op a => a.erase ++ [.intTestOp t op]
  | .irel t op a b => a.erase ++ b.erase ++ [.intRelOp t op]
  | .fbin t op a b => a.erase ++ b.erase ++ [.floatBinOp t op]
  | .fun_ t op a => a.erase ++ [.floatUnOp t op]
  | .frel t op a b => a.erase ++ b.erase ++ [.floatRelOp t op]
  | .cvt op _ a => a.erase ++ [.convert op]
  | .load t p arg _ _ a => a.erase ++ [.intLoad t p arg]
  | .fload t arg _ _ a => a.erase ++ [.floatLoad t arg]
  | .msize _ => [.memorySize]
  | .mgrow _ a => a.erase ++ [.memoryGrow]
  | .call x _ _ _ args => args.erase ++ [.call x]
  | .select a b c => a.erase ++ b.erase ++ c.erase ++ [.select]
  | @TE.block _ _ t s v => [.block (.value t) (s.erase ++ v.erase)]
  | @TE.ite _ _ t c a b => c.erase ++ [.if_ (.value t) a.erase b.erase]
  | .tee x _ a => a.erase ++ [.localTee x]

/-- The instructions of a statement. -/
def TS.erase {C : Context} : TS S C → Lime1.Expr
  | .nop => [.nop]
  | .drop a => a.erase ++ [.drop]
  | .set x _ a => a.erase ++ [.localSet x]
  | .gset x _ a => a.erase ++ [.globalSet x]
  | .store t p arg _ _ a v => a.erase ++ v.erase ++ [.intStore t p arg]
  | .fstore t arg _ _ a v => a.erase ++ v.erase ++ [.floatStore t arg]
  | .fill _ _ a b c => a.erase ++ b.erase ++ c.erase ++ [.memoryFill]
  | .copy _ _ a b c => a.erase ++ b.erase ++ c.erase ++ [.memoryCopy]
  | .block s => [.block .empty s.erase]
  | .loop s => [.loop .empty s.erase]
  | .ite c a b => c.erase ++ [.if_ .empty a.erase b.erase]
  | .brIf l _ c => c.erase ++ [.brIf l]
  | .call x _ _ _ args => args.erase ++ [.call x]
  | .seq a b => a.erase ++ b.erase

/-- The instructions of an argument list. -/
def TA.erase {C : Context} {ts : List VT} : TA S C ts → Lime1.Expr
  | .nil => []
  | .cons a r => a.erase ++ r.erase

end

/-! ## Generation -/

/-- A uniform choice, `none` for the empty list. -/
def pickOpt {α : Type} (l : List α) : Rand (Option α) := do
  if l.isEmpty then return none
  return l[(← Rand.nat l.length)]?

/-- The locals of type `t` (the first 64). -/
def localsOf (C : Context) (t : VT) : List {x : LocalIdx // C.locals[x.toNat]? = some t} :=
  (List.range (min C.locals.length 64)).filterMap fun i =>
    if h : C.locals[(idx i : LocalIdx).toNat]? = some t then some ⟨idx i, h⟩ else none

/-- The globals of type `t` (the first 64). -/
def globalsOf (C : Context) (t : VT) :
    List ((x : GlobalIdx) × (m : Mutability) ×' C.globals[x.toNat]? = some ⟨m, t⟩) :=
  (List.range (min C.globals.length 64)).filterMap fun i =>
    match h : C.globals[(idx i : GlobalIdx).toNat]? with
    | some gt => if hv : gt.value = t then some ⟨idx i, gt.mutability, by rw [h, ← hv]⟩ else none
    | none => none

/-- The mutable globals of type `t`. -/
def mutGlobalsOf (C : Context) (t : VT) :
    List {x : GlobalIdx // C.globals[x.toNat]? = some ⟨.var, t⟩} :=
  (List.range (min C.globals.length 64)).filterMap fun i =>
    if h : C.globals[(idx i : GlobalIdx).toNat]? = some ⟨.var, t⟩ then some ⟨idx i, h⟩ else none

/-- The functions with the given results (the first 64). -/
def funcsWith (C : Context) (rs : List VT) :
    List ((x : FuncIdx) × (ft : V1.FuncType) ×' (C.funcs[x.toNat]? = some ft ∧ ft.results = rs)) :=
  (List.range (min C.funcs.length 64)).filterMap fun i =>
    match h : C.funcs[(idx i : FuncIdx).toNat]? with
    | some ft => if hr : ft.results = rs then some ⟨idx i, ft, h, hr⟩ else none
    | none => none

/-- The labels with no values. -/
def emptyLabels (C : Context) : List {l : LabelIdx // C.labels[l.toNat]? = some []} :=
  (List.range (min C.labels.length 64)).filterMap fun i =>
    if h : C.labels[(idx i : LabelIdx).toNat]? = some [] then some ⟨idx i, h⟩ else none

/-- A small memory offset. -/
def offset : Rand (Fin (2 ^ 32)) := do
  return Fin.ofNat _ (← Rand.pick [0, 0, 1, 8, 1024] 0)

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

/-- A constant of a type. -/
def const (C : Context) : (t : VT) → Rand (TE S C t)
  | .int it => do return .iconst it (BitVec.ofNat _ (← intBits it.width))
  | .float ft => do return .fconst ft (BitVec.ofNat _ (← intBits ft.width))

def intBinOps : List IntBinOp :=
  [.add, .sub, .mul, .div .signed, .div .unsigned, .rem .signed, .rem .unsigned, .and, .or, .xor,
    .shl, .shr .signed, .shr .unsigned, .rotl, .rotr]
def intRelOps : List IntRelOp :=
  [.eq, .ne, .lt .signed, .lt .unsigned, .gt .signed, .gt .unsigned, .le .signed, .le .unsigned,
    .ge .signed, .ge .unsigned]
def floatBinOps : List FloatBinOp := [.add, .sub, .mul, .div, .min, .max, .copysign]
def floatUnOps : List FloatUnOp := [.abs, .neg, .sqrt, .ceil, .floor, .trunc, .nearest]
def floatRelOps : List FloatRelOp := [.eq, .ne, .lt, .gt, .le, .ge]
def intUnOps : List Lime1.IntUnOp := [.clz, .ctz, .popcnt, .extend .i8, .extend .i16, .extend .i32]

/-- The unary integer operators valid at `t` and in `S`. -/
def unOpsAt (S : FeatureSet) (t : IntType) :
    List {op : Lime1.IntUnOp // IntUnOpValid t op ∧ IntUnOp.inFeatB S op.toCore = true} :=
  intUnOps.filterMap fun op =>
    if h : IntUnOpValid t op ∧ IntUnOp.inFeatB S op.toCore = true then some ⟨op, h⟩ else none

/-- Every scalar conversion. -/
def convs : List ConvertOp :=
  [.wrap, .extend .signed, .extend .unsigned] ++
  ([IntType.i32, .i64].flatMap fun i => [FloatType.f32, .f64].flatMap fun f =>
    [.trunc f i .signed, .trunc f i .unsigned, .truncSat f i .signed, .truncSat f i .unsigned,
     .convert i f .signed, .convert i f .unsigned]) ++
  [.demote, .promote, .reinterpretInt .f32, .reinterpretInt .f64, .reinterpretFloat .i32,
   .reinterpretFloat .i64]

/-- The conversions to `t` in `S`. -/
def convsTo (S : FeatureSet) (t : VT) :
    List {op : ConvertOp // op.target = t ∧ ConvertOp.inFeatB S op = true} :=
  convs.filterMap fun op =>
    if h : op.target = t ∧ ConvertOp.inFeatB S op = true then some ⟨op, h⟩ else none

theorem aligned_of {a w : Nat} (h : 2 ^ (Fin.ofNat (2 ^ 32) a).val ≤ w / 8) (o : Fin (2 ^ 32)) :
    Aligned ⟨Fin.ofNat _ a, o⟩ w := h

/-- Integer loads: type, packing and alignment, with their access facts. -/
def intLoads : List ((t : IntType) × (p : Option (V1.PackSize × Signedness)) × (a : Nat) ×'
    ∀ o : Fin (2 ^ 32), IntAccess t (p.map Prod.fst) ⟨Fin.ofNat _ a, o⟩) :=
  [⟨.i32, none, 2, aligned_of (by decide)⟩,
   ⟨.i32, some (.i8, .signed), 0, fun o => ⟨by decide, aligned_of (by decide) o⟩⟩,
   ⟨.i32, some (.i16, .unsigned), 1, fun o => ⟨by decide, aligned_of (by decide) o⟩⟩,
   ⟨.i64, none, 3, aligned_of (by decide)⟩,
   ⟨.i64, some (.i32, .signed), 2, fun o => ⟨by decide, aligned_of (by decide) o⟩⟩,
   ⟨.i64, some (.i8, .unsigned), 0, fun o => ⟨by decide, aligned_of (by decide) o⟩⟩]

/-- Integer stores. -/
def intStores : List ((t : IntType) × (p : Option V1.PackSize) × (a : Nat) ×'
    ∀ o : Fin (2 ^ 32), IntAccess t p ⟨Fin.ofNat _ a, o⟩) :=
  [⟨.i32, none, 2, aligned_of (by decide)⟩,
   ⟨.i32, some .i8, 0, fun o => ⟨by decide, aligned_of (by decide) o⟩⟩,
   ⟨.i64, none, 3, aligned_of (by decide)⟩,
   ⟨.i64, some .i16, 1, fun o => ⟨by decide, aligned_of (by decide) o⟩⟩]

/-- The natural alignment of a float. -/
def falign (t : FloatType) : (a : Nat) ×' ∀ o : Fin (2 ^ 32), Aligned ⟨Fin.ofNat _ a, o⟩ t.width :=
  match t with
  | .f32 => ⟨2, aligned_of (by decide)⟩
  | .f64 => ⟨3, aligned_of (by decide)⟩

/-- Pick among generators (the first when the draw is out of range). -/
def oneOf {α : Type} (d : Rand α) (gs : List (Rand α)) : Rand α := do
  (gs.getD (← Rand.nat gs.length) d)

mutual

/-- **A typed expression of type `t`**, depth at most `n`. -/
def genTE (S : FeatureSet) : Nat → (C : Context) → (t : VT) → Rand (TE S C t)
  | 0, C, t => do
    match ← pickOpt (localsOf C t) with
    | some ⟨x, h⟩ => if ← Rand.bool then return .get x h else const C t
    | none => const C t
  | n + 1, C, t => do
    let sub := genTE S n C
    let hasMem := !C.memories.isEmpty
    let opsT : List (Rand (TE S C t)) :=
      [ genTE S 0 C t,
        do return .select (← sub t) (← sub t) (← sub I32),
        do
          let C' := C.withLabel [t]
          return .block (← genTS S n C') (← genTE S n C' t),
        do
          let C' := C.withLabel [t]
          return .ite (← sub I32) (← genTE S n C' t) (← genTE S n C' t),
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
          | some ⟨x, ft, h, hr⟩ => return .call x ft h hr (← genTA S n C ft.params)
          | none => const C t,
        do
          match ← pickOpt (convsTo S t) with
          | some ⟨op, ht, hf⟩ => return ht ▸ TE.cvt op hf (← sub op.source)
          | none => const C t ]
    let opsN : List (Rand (TE S C t)) := match t with
      | .int it =>
        [ do return .ibin it (← Rand.pick intBinOps .add) (← sub (.int it)) (← sub (.int it)),
          do
            match ← pickOpt (unOpsAt S it) with
            | some ⟨op, v, hf⟩ => return .iun it op v hf (← sub (.int it))
            | none => const C (.int it) ] ++
        (if hm : C.memories ≠ [] then
          [ do
              let ls := intLoads.filter fun l => l.1 == it
              match ← pickOpt ls with
              | some ⟨t', p, a, acc⟩ =>
                if ht : t' = it then
                  let o ← offset
                  return ht ▸ TE.load t' p ⟨Fin.ofNat _ a, o⟩ hm (acc o) (← sub I32)
                else const C (.int it)
              | none => const C (.int it) ]
         else []) ++
        (match it with
          | .i32 =>
            [ do
                let u ← Rand.pick [IntType.i32, .i64] .i32
                if ← Rand.bool then return .itest u .eqz (← sub (.int u))
                else return .irel u (← Rand.pick intRelOps .eq) (← sub (.int u)) (← sub (.int u)),
              do
                let f ← Rand.pick [FloatType.f32, .f64] .f32
                return .frel f (← Rand.pick floatRelOps .eq) (← sub (.float f)) (← sub (.float f)) ] ++
            (if hm : C.memories ≠ [] then
              [ pure (.msize hm), do return .mgrow hm (← sub I32) ] else [])
          | .i64 => [])
      | .float ft =>
        [ do return .fbin ft (← Rand.pick floatBinOps .add) (← sub (.float ft)) (← sub (.float ft)),
          do return .fun_ ft (← Rand.pick floatUnOps .neg) (← sub (.float ft)) ] ++
        (if hm : C.memories ≠ [] then
          [ do
              let ⟨a, al⟩ := falign ft
              let o ← offset
              return .fload ft ⟨Fin.ofNat _ a, o⟩ hm (al o) (← sub I32) ]
         else [])
    let _ := hasMem
    oneOf (const C t) (opsT ++ opsN)

/-- **A typed statement**, depth at most `n`. -/
def genTS (S : FeatureSet) : Nat → (C : Context) → Rand (TS S C)
  | 0, _ => pure TS.nop
  | n + 1, C => do
    let e := genTE S n C
    let ops : List (Rand (TS S C)) :=
      [ pure TS.nop,
        do return TS.drop (← e (← Rand.pick [I32, .int .i64, .float .f32, .float .f64] I32)),
        do return TS.seq (← genTS S n C) (← genTS S n C),
        do return TS.block (← genTS S n (C.withLabel [])),
        do return TS.loop (← genTS S n (C.withLabel [])),
        do return TS.ite (← e I32) (← genTS S n (C.withLabel [])) (← genTS S n (C.withLabel [])),
        do
          let t ← Rand.pick [I32, .int .i64, .float .f32, .float .f64] I32
          match ← pickOpt (localsOf C t) with
          | some ⟨x, h⟩ => return TS.set x h (← e t)
          | none => pure TS.nop,
        do
          let t ← Rand.pick [I32, .int .i64, .float .f32, .float .f64] I32
          match ← pickOpt (mutGlobalsOf C t) with
          | some ⟨x, h⟩ => return TS.gset x h (← e t)
          | none => pure TS.nop,
        do
          match ← pickOpt (emptyLabels C) with
          | some ⟨l, h⟩ => return TS.brIf l h (← e I32)
          | none => pure TS.nop,
        do
          match ← pickOpt (funcsWith C []) with
          | some ⟨x, ft, h, hr⟩ => return TS.call x ft h hr (← genTA S n C ft.params)
          | none => pure TS.nop ] ++
      (if hm : C.memories ≠ [] then
        [ do
            match ← pickOpt intStores with
            | some ⟨t, p, a, acc⟩ =>
              let o ← offset
              return TS.store t p ⟨Fin.ofNat _ a, o⟩ hm (acc o) (← e I32) (← e (.int t))
            | none => pure TS.nop,
          do
            let ft ← Rand.pick [FloatType.f32, .f64] .f32
            let ⟨a, al⟩ := falign ft
            let o ← offset
            return TS.fstore ft ⟨Fin.ofNat _ a, o⟩ hm (al o) (← e I32) (← e (.float ft)) ] ++
        (if hf : S.has .bulkMemoryOpt = true then
          ([ do return TS.fill hm hf (← e I32) (← e I32) (← e I32),
             do return TS.copy hm hf (← e I32) (← e I32) (← e I32) ] : List (Rand (TS S C)))
         else [])
       else [])
    oneOf (pure TS.nop) ops

/-- **A typed argument list** for `ts`. -/
def genTA (S : FeatureSet) : Nat → (C : Context) → (ts : List VT) → Rand (TA S C ts)
  | _, _, [] => pure .nil
  | n, C, t :: ts => do return .cons (← genTE S n C t) (← genTA S n C ts)

end

/-! ## Modules -/

/-- A function type of `S` (several results only with multi-value). -/
def funcType (S : FeatureSet) : Rand V1.FuncType := do
  let vts : List VT := [I32, .int .i64, .float .f32, .float .f64]
  let np ← Rand.nat 4
  let nr ← Rand.nat (if S.has .multiValue then 3 else 2)
  return ⟨← Rand.list np (Rand.pick vts I32), ← Rand.list nr (Rand.pick vts I32)⟩

/-- A function type is admissible in `S`: at most one result without multi-value. -/
def FuncTypeOk (S : FeatureSet) (ft : V1.FuncType) : Bool :=
  decide (ft.results.length ≤ 1) || S.has .multiValue

/-- A constant global of a type. -/
def global (t : VT) (mut_ : Bool) (b : Nat) : Lime1.Global :=
  ⟨⟨if mut_ then .var else .const, t⟩, match t with
    | .int it => [.intConst it (BitVec.ofNat _ b)]
    | .float ft => [.floatConst ft (BitVec.ofNat _ b)]⟩

/-- The skeleton of a module: everything but the code, with the facts the code relies on. -/
structure Skel (S : FeatureSet) where
  types : List V1.FuncType
  /-- Several results only with multi-value. -/
  typesOk : ∀ ft ∈ types, FuncTypeOk S ft = true
  /-- Each function's type index and type. -/
  funcs : List (TypeIdx × V1.FuncType)
  /-- Every function's type index resolves to its type. -/
  resolved : ∀ p ∈ funcs, types[p.1.toNat]? = some p.2
  /-- Globals: type, mutability, initial bits. -/
  gspecs : List (VT × Bool × Nat)
  mem : Bool

/-- The globals of a skeleton. -/
def Skel.globals (k : Skel S) : List Lime1.Global := k.gspecs.map fun (t, m, b) => global t m b

/-- The memories of a skeleton: one page to four, or none. -/
def Skel.memories (k : Skel S) : List V1.MemoryType :=
  if k.mem then [⟨⟨Fin.ofNat _ 1, some (Fin.ofNat _ 4)⟩⟩] else []

/-- The Lime1 module of a skeleton, with empty bodies. -/
def Skel.module0 (k : Skel S) : Lime1.Module where
  types := k.types
  funcs := k.funcs.map fun (x, _) => ⟨x, [], []⟩
  globals := k.globals
  memories := k.memories

/-- The validation context of a skeleton's module. -/
def Skel.ctx (k : Skel S) : Context := moduleContext k.module0

/-- A function's code at the skeleton's context. -/
structure FBody (S : FeatureSet) (C0 : Context) (ft : V1.FuncType) where
  locals : List VT
  stmts : TS S (functionContext C0 ft locals)
  rets : TA S (functionContext C0 ft locals) ft.results

/-- The code of every function, in order. -/
inductive Bodies (S : FeatureSet) (C0 : Context) : List (TypeIdx × V1.FuncType) → Type where
  | nil : Bodies S C0 []
  | cons {x : TypeIdx} {ft : V1.FuncType} {l : List (TypeIdx × V1.FuncType)}
      (b : FBody S C0 ft) (r : Bodies S C0 l) : Bodies S C0 ((x, ft) :: l)

/-- The functions. -/
def Bodies.funcs {C0 : Context} : {l : List (TypeIdx × V1.FuncType)} → Bodies S C0 l → List Lime1.Func
  | [], .nil => []
  | (x, _) :: _, .cons b r => ⟨x, b.locals, b.stmts.erase ++ b.rets.erase⟩ :: r.funcs

/-- Generate the code of every function. -/
def genBodies (S : FeatureSet) (C0 : Context) (depth : Nat) :
    (l : List (TypeIdx × V1.FuncType)) → Rand (Bodies S C0 l)
  | [] => pure .nil
  | (_, ft) :: l => do
    let vts : List VT := [I32, .int .i64, .float .f32, .float .f64]
    let locals ← Rand.list (← Rand.nat 3) (Rand.pick vts I32)
    let C := functionContext C0 ft locals
    let k ← Rand.range 1 (2 + depth)
    let stmts ← Rand.list k (genTS S depth C)
    let s : TS S C := stmts.foldr .seq .nop
    let rets ← genTA S depth C ft.results
    return .cons ⟨locals, s, rets⟩ (← genBodies S C0 depth l)

/-- Export names (at most ten functions are exported). -/
def exportNames : List String := ["f0", "f1", "f2", "f3", "f4", "f5", "f6", "f7", "f8", "f9"]

/-- The resolved functions of type indices. -/
def resolve (types : List V1.FuncType) (xs : List Nat) : List (TypeIdx × V1.FuncType) :=
  xs.filterMap fun i => (types[(idx i : TypeIdx).toNat]?).map fun ft => ((idx i : TypeIdx), ft)

theorem resolve_mem {types : List V1.FuncType} {xs : List Nat} :
    ∀ p ∈ resolve types xs, types[p.1.toNat]? = some p.2 := by
  intro p hp
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hp
  obtain ⟨ft, hft, rfl⟩ := Option.map_eq_some_iff.mp hi
  exact hft

/-- The skeleton of a seed. -/
def skel (S : FeatureSet) (size : Nat) : Rand (Skel S) := do
  let types ← (Rand.list (← Rand.range 1 (1 + min 6 (size / 4))) (funcType S))
  let types := types.filter (FuncTypeOk S)
  let nt := types.length
  let nf ← Rand.range 1 (1 + min 10 (size / 2))
  let xs ← Rand.list nf (Rand.nat nt)
  let vts : List VT := [I32, .int .i64, .float .f32, .float .f64]
  let ng ← Rand.nat 4
  let gspecs ← Rand.list ng (do return (← Rand.pick vts I32, ← Rand.bool, ← intBits 32))
  let mem ← Rand.bool
  return ⟨types, fun _ h => (List.mem_filter.mp h).2, resolve types xs, resolve_mem, gspecs, mem⟩

/-- The Lime1 module of a skeleton and its code. -/
def Skel.module (k : Skel S) (bs : Bodies S k.ctx k.funcs) (data : Option (Nat × List UInt8)) :
    Lime1.Module :=
  { k.module0 with
    funcs := bs.funcs
    data := match data with
      | some (off, bytes) => if k.mem then
          [⟨⟨0⟩, [.intConst .i32 (BitVec.ofNat _ off)], ⟨bytes.toArray⟩⟩] else []
      | none => []
    exports := (exportNames.take k.funcs.length).zipIdx.map fun (n, i) => ⟨n, .func (idx i)⟩ }

/-- An optional data segment (offset and bytes), when there is a memory. -/
def genData (k : Skel S) : Rand (Option (Nat × List UInt8)) := do
  if k.mem && (← Rand.bool) then
    let off ← Rand.nat 1024
    let bytes ← Rand.list (← Rand.nat 16) (Rand.nat 256)
    return some (off, bytes.map UInt8.ofNat)
  else return none

/-- **The typed generator**: a Lime1 module, by construction valid (`Thms`). The state is
threaded by hand so that the result is visibly `k.module bs d`. -/
def lmodule (S : FeatureSet) (size : Nat) : Rand Lime1.Module := fun r =>
  let p₁ := skel S size r
  let p₂ := genBodies S p₁.1.ctx (min 4 (1 + size / 8)) p₁.1.funcs p₁.2
  let p₃ := genData p₁.1 p₂.2
  (p₁.1.module p₂.1 p₃.1, p₃.2)

/-- **Its Core 3.0 image.** -/
def module (S : FeatureSet) (size : Nat) : Rand Module := fun r =>
  let p := lmodule S size r
  (Lime1.Module.toCore p.1, p.2)

end Silmaril.Wasm.Tools.Gen.Typed
