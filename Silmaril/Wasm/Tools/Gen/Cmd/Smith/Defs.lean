module

public import Silmaril.Wasm.Tools.Gen.Cmd.Norm.Defs
public import Silmaril.Wasm.Tools.Gen.Cmd.Sections.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# `wasm-tools smith`: a seeded generator of valid modules, at a point of the feature lattice

`rawModule S cfg` reads a seed (`Silmaril.Wasm.Tools.Gen.Seed`) as a stream of choices and
builds a Core 3.0 module that uses only the capabilities of `S`, within the limits of `cfg`
(upstream's `wasm_smith::Config` options that this generator honours):

* function types over the value types of `S` (`valTypes`: `i32`/`i64` with `intNum`,
  `f32`/`f64` with `floatNum`, `v128` with `simd`, `funcref`/`externref` with `refTypes`),
  several results only with `multiValue`;
* function and global imports (module `"m"`);
* memories (several only with `multiMemory`) and `funcref` tables (several only with
  `refTypes`; one at every model with `table`, Wasm 1.0 included);
* globals with constant initialisers (sums of constants with `extConst`), mutable ones with
  `mutGlobal`;
* exports with distinct names, a start function of type `[] → []`, active element segments
  of function indices on any table, active (on any memory) and passive data segments (passive
  with `bulkMemory`);
* function bodies built **type-directed**: `genVal t` produces code that pushes one value of
  type `t` (constants, locals, globals, numeric operators, conversions, loads, `memory.size`,
  `memory.grow`, calls, `call_indirect`, `block`/`if` with a result, `select`, `local.tee`,
  SIMD operators, splats, lane extractions and tests), and `genStmt` produces code with no
  net effect on the stack (`local.set`, `global.set`, stores, `drop`, `block`, `loop`, `if`,
  `br_if` to labels without values, `memory.fill`/`memory.copy`, calls and `call_indirect`
  whose results are dropped, `return_call` and `return_call_indirect`). An earlier step adds:
  **table instructions** (`table.get/set/size/grow/fill/copy/init`, `elem.drop`, `ref.func`,
  `ref.is_null`; `externref` tables; passive and declarative element segments),
  **memory64** (64-bit memories, their addresses, `memory.size`/`grow` at `i64`, `i64`
  data offsets), **bulk memory** `memory.init`/`data.drop`, **exceptions** (tags, `throw`
  under an `if`, `try_table` with `catch`/`catch_all` to enclosing labels of the tag's
  arity), **GC** (struct and array types with packed and mutable fields; `struct.new`,
  `struct.new_default`, `struct.get(_s/_u)`, `struct.set`, `array.new`, `array.new_default`,
  `array.get(_s/_u)`, `array.set`, `array.len` on freshly allocated, in-bounds aggregates;
  `ref.i31`, `i31.get_s/u`, `ref.eq`, `ref.test`), **relaxed SIMD** (every relaxed operator)
  and further SIMD (comparisons, shuffles, lane replacement, narrowing, extension,
  conversions, the extending, splatting and zeroing loads). Threads (shared memories, atomics)
  are not generated: silmaril's Core 3.0 syntax has no shared memories. Every instruction is
  gated by the capability `Instr.headB` asks for, and by the kinds of
  `--allowed-instructions` (`Config.allowed`). Float constants are dyadic rationals `k / 2^j`
  (`|k| < 1024`, `j ≤ 3`), whose text form the printer (`Silmaril.Wasm.Tools.Gen.Cmd.Print`)
  writes exactly.
* `--disallow-traps` (`Config.disallowTraps`): no division or remainder, no non-saturating
  truncation, no memory access or bulk memory operation, no indirect call; memories have at
  least one page and tables at least eight elements, so that active segments are in bounds.
  `--ensure-termination` (`Config.ensureTermination`): `br_if` never targets a loop, calls
  only go to lower function indices (an acyclic call graph inside the module), and no
  indirect calls. These two hold by construction; they are not proved.

The construction aims at validity; it is not trusted for it. `smith S cfg` is
`checkedGenW S (rawModule S cfg)` (`Norm`): the raw module when `validInWB S` accepts it,
else the empty module. `Thms.smith_validInW` is the generator's specification; the rate at
which the fallback fires is measured by `tools/wasm-tools/tests/gen/fuzz.sh`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Smith

open Silmaril.Wasm Silmaril.Wasm.Models

/-- wasm-smith's instruction kinds (`InstructionKind`), each split into its integer and float
halves: `numeric` is `numeric_int` and `numeric_float`, and likewise `vector` and `memory`. -/
def allKinds : List String :=
  ["numeric_int", "numeric_float", "vector_int", "vector_float", "reference", "parametric",
    "variable", "table", "memory_int", "memory_float", "control", "aggregate"]

/-- The kinds one name of `--allowed-instructions` denotes (wasm-smith's `InstructionKind::
from_str`, case-insensitive), `none` for an unknown name. -/
def kindsOf (s : String) : Option (List String) :=
  match s.toLower with
  | "numeric_non_float" => some ["numeric_int"]
  | "numeric" => some ["numeric_int", "numeric_float"]
  | "vector_non_float" => some ["vector_int"]
  | "vector" => some ["vector_int", "vector_float"]
  | "memory_non_float" => some ["memory_int"]
  | "memory" => some ["memory_int", "memory_float"]
  | "reference" => some ["reference"]
  | "parametric" => some ["parametric"]
  | "variable" => some ["variable"]
  | "table" => some ["table"]
  | "control" => some ["control"]
  | "aggregate" => some ["aggregate"]
  | _ => none

/-- The value of `--allowed-instructions` (comma-separated kinds), or the first unknown part. -/
def parseKinds (s : String) : Except String (List String) :=
  (s.splitOn ",").foldlM (init := []) fun acc part =>
    match kindsOf part with
    | some ks => .ok (acc ++ ks)
    | none => .error part

/-- The type of an imported or exported entity (`--exports`, `--module-shape`): a function
by its type, a tag by its parameters. -/
inductive Ext where
  | func (ft : FuncType)
  | global (g : GlobalType)
  | memory (m : MemoryType)
  | table (t : TableType)
  | tag (ps : List ValType)
  deriving Repr, Inhabited

/-- The `wasm_smith::Config` limits this generator honours (upstream's defaults). -/
structure Config where
  maxTypes : Nat := 100
  maxImports : Nat := 100
  maxFuncs : Nat := 100
  maxGlobals : Nat := 100
  maxExports : Nat := 100
  maxMemories : Nat := 1
  maxTables : Nat := 1
  maxDataSegments : Nat := 100
  maxElementSegments : Nat := 100
  maxElements : Nat := 100
  maxInstructions : Nat := 100
  maxNestingDepth : Nat := 10
  maxTableElements : Nat := 1000000
  /-- `max-memory32-bytes / 65536`. -/
  maxMemoryPages : Nat := 65536
  minFuncs : Nat := 0
  minGlobals : Nat := 0
  minImports : Nat := 0
  minExports : Nat := 0
  minTypes : Nat := 0
  minMemories : Nat := 0
  minTables : Nat := 0
  minDataSegments : Nat := 0
  minElementSegments : Nat := 0
  maxTags : Nat := 100
  minTags : Nat := 0
  allowStartExport : Bool := true
  exportEverything : Bool := false
  memoryMaxSizeRequired : Bool := false
  tableMaxSizeRequired : Bool := false
  /-- `--ensure-termination`: no backward branches, calls only to lower indices, no indirect
  calls. -/
  ensureTermination : Bool := false
  /-- `--disallow-traps`: no instruction that can trap (division, non-saturating truncation,
  memory accesses, indirect calls) and in-bounds active segments. -/
  disallowTraps : Bool := false
  /-- `--allowed-instructions`: the allowed instruction kinds, as `Kinds.expand` lists them. -/
  allowed : List String := allKinds
  /-- `--generate-custom-sections`. -/
  customSections : Bool := false
  /-- `--available-imports`: the function imports (module, name, type) the module may use;
  `none`: any. -/
  availFuncs : Option (List (String × String × FuncType)) := none
  /-- `--available-imports`: the global imports the module may use. -/
  availGlobals : List (String × String × GlobalType) := []
  /-- `--module-shape`: exactly these imports (module, name, type), in order. -/
  shapeImports : Option (List (String × String × Ext)) := none
  /-- `--exports` and `--module-shape`: exactly these exports (name, type), in order, each of
  a new entity of that type. -/
  reqExports : Option (List (String × Ext)) := none
  deriving Repr, Inhabited

/-! ## Indices, types and constants -/

/-- An index (taken modulo `2^32`). -/
def ix {k : IndexKind} (n : Nat) : Idx k := ⟨⟨n % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- `funcref` and `externref`. -/
def funcref : ValType := .ref ⟨true, .abstract .func⟩
def externref : ValType := .ref ⟨true, .abstract .extern⟩

/-- The numeric value types of `S`. -/
def numTypes (S : FeatureSet) : List ValType :=
  (if S.has .intNum then [.i32, .i64] else []) ++ (if S.has .floatNum then [.f32, .f64] else [])

/-- `v128` in `S` (SIMD). -/
def v128 : ValType := .vec .v128

def vecTypes (S : FeatureSet) : List ValType := if S.has .simd then [v128] else []

/-- The value types the generator uses in `S`. -/
def valTypes (S : FeatureSet) : List ValType :=
  numTypes S ++ vecTypes S ++ (if S.has .refTypes then [funcref, externref] else [])

/-- Is the value type numeric? -/
def isNum : ValType → Bool
  | .num _ => true
  | _ => false

/-- Numeric or vector (an untyped `select` takes these). -/
def isNumVec : ValType → Bool
  | .num _ | .vec _ => true
  | _ => false

/-- Is the value type a float? -/
def isFloat : ValType → Bool
  | .num (.float _) => true
  | _ => false

/-- A memory argument of natural alignment `2^a` (any smaller alignment allowed). -/
def memArg (a off : Nat) : MemArg := ⟨⟨a % 2 ^ 32, Nat.mod_lt _ (by decide)⟩,
  ⟨off % 2 ^ 64, Nat.mod_lt _ (by decide)⟩⟩

/-- The bits of the dyadic rational `(-1)^neg · k / 2^j` (`k < 1024`, `j ≤ 3`) in the format
with `mbits` fraction bits, exponent bias `bias` and width `w`. -/
def dyadicBits (w mbits bias : Nat) (neg : Bool) (k j : Nat) : Nat :=
  let sign := if neg then 2 ^ (w - 1) else 0
  if k = 0 then sign else
    let e := Nat.log2 k
    let frac := (k - 2 ^ e) * 2 ^ (mbits - e)
    sign + (bias + e - j) * 2 ^ mbits + frac

/-- A float constant `(-1)^neg · k / 2^j`. -/
def floatConst (t : FloatType) (neg : Bool) (k j : Nat) : Instr :=
  match t with
  | .f32 => .floatConst .f32 (BitVec.ofNat 32 (dyadicBits 32 23 127 neg k j))
  | .f64 => .floatConst .f64 (BitVec.ofNat 64 (dyadicBits 64 52 1023 neg k j))

/-! ## The generation monad with an instruction budget -/

/-- Generation with the remaining instruction budget of the current function. -/
abbrev B := StateT Nat G

namespace B

def choose (n : Nat) : B Nat := liftM (G.choose n)
def range (lo hi : Nat) : B Nat := liftM (G.range lo hi)
def bool : B Bool := liftM G.bool
def bytes (k : Nat) : B Nat := liftM (G.bytes k)
def pick {α : Type} (d : α) (l : List α) : B α := liftM (G.pick d l)

/-- Spend `n` instructions of the budget. -/
def spend (n : Nat) : B Unit := modify (· - n)

/-- Is there budget left? -/
def left : B Bool := return (← get) > 0

end B

/-- The indices of the elements of `l` satisfying `p`. -/
def indicesWhere' {α : Type} (p : α → Bool) (l : List α) : List Nat :=
  ((List.range l.length).zip l).filterMap fun (i, a) => if p a then some i else none

/-! ## Contexts -/

/-- What function bodies may refer to. -/
structure Ctx where
  S : FeatureSet
  /-- Function index ↦ function type (imports first). -/
  funcs : List FuncType
  /-- Global index ↦ global type (imports first). -/
  globals : List GlobalType
  hasMem : Bool
  /-- Element segments exist, so `ref.func` of their functions is declared. -/
  declared : List Nat
  /-- Type index ↦ function type. -/
  types : List FuncType := []
  /-- The number of memories (at least one when `hasMem`). -/
  nMem : Nat := 1
  /-- The number of tables. -/
  nTab : Nat := 0
  cfg : Config := {}
  /-- Table index ↦ element type (`funcref` or `externref`). -/
  tabTypes : List RefType := []
  /-- Memory index ↦ address type (`i64` with memory64). -/
  memAddr : List AddrType := []
  /-- Tag index ↦ parameters. -/
  tags : List (List ValType) := []
  /-- The struct and array types: type index and body. -/
  gc : List (Nat × CompositeType) := []
  /-- Element segment index ↦ element type. -/
  elemTypes : List RefType := []
  /-- The number of data segments. -/
  nData : Nat := 0

/-- Is an instruction kind allowed (`--allowed-instructions`)? -/
def Ctx.al (c : Ctx) (k : String) : Bool := c.cfg.allowed.contains k

/-- The value type of an address type. -/
def addrVal : AddrType → ValType
  | .i32 => .i32
  | .i64 => .i64

/-- The tables holding `funcref` (the targets of `call_indirect`). -/
def Ctx.funcTabs (c : Ctx) : List Nat :=
  if c.tabTypes.isEmpty then List.range c.nTab
  else indicesWhere' (· == ⟨true, .abstract .func⟩) c.tabTypes

/-- The tables of element type `t`. -/
def Ctx.tabsOf (c : Ctx) (t : ValType) : List Nat :=
  indicesWhere' (fun r => ValType.ref r == t) c.tabTypes

/-- The memories of address type `a`. -/
def Ctx.memsAt (c : Ctx) (a : AddrType) : List Nat :=
  if c.memAddr.isEmpty then (if a == .i32 then List.range c.nMem else [])
  else indicesWhere' (· == a) c.memAddr

/-- The address type of memory `x`. -/
def Ctx.addrOf (c : Ctx) (x : Nat) : AddrType := c.memAddr.getD x .i32

/-- The struct types with a field (index, storage, mutability) of unpacked type `t`. -/
def Ctx.structFields (c : Ctx) (t : ValType) : List (Nat × Nat × FieldType) :=
  c.gc.flatMap fun
    | (ti, .struct fs) => (fs.zipIdx.filter (fun (f, _) => f.storage.unpacked == t)).map
        fun (f, i) => (ti, i, f)
    | _ => []

/-- The array types with element of unpacked type `t` (`none`: any). -/
def Ctx.arrays (c : Ctx) (t : Option ValType) : List (Nat × FieldType) :=
  c.gc.filterMap fun
    | (ti, .array f) => if t.all (f.storage.unpacked == ·) then some (ti, f) else none
    | _ => none

/-- The mutable struct fields: type index, field index, field. -/
def mutFields (c : Ctx) : List (Nat × Nat × FieldType) :=
  c.gc.flatMap fun
    | (ti, .struct fs) => (fs.zipIdx.filter (fun (f, _) => f.mutability == .var)).map
        fun (f, i) => (ti, i, f)
    | _ => []

/-- The fields of a struct type. -/
def Ctx.fieldsOf (c : Ctx) (ti : Nat) : List FieldType :=
  match c.gc.lookup ti with
  | some (.struct fs) => fs
  | _ => []

/-- The context of one function body. -/
structure FCtx where
  /-- Parameters, then locals. -/
  locals : List ValType
  /-- The branch arity of each enclosing label, innermost first. -/
  labels : List (List ValType)
  /-- Remaining nesting depth for blocks. -/
  depth : Nat
  /-- Which enclosing labels are loops, innermost first. -/
  loops : List Bool := []
  /-- The results of the function (for `return_call`). -/
  results : List ValType := []
  /-- The index of the function (for `--ensure-termination`: calls only below it). -/
  self : Nat := 0

/-- The indices of the elements of `l` satisfying `p`. -/
def indicesWhere {α : Type} (p : α → Bool) (l : List α) : List Nat :=
  ((List.range l.length).zip l).filterMap fun (i, a) => if p a then some i else none

/-! ## Constants -/

/-- A constant of a numeric or reference type. -/
def genConst (t : ValType) : B (List Instr) := do
  match t with
  | .num (.int .i32) =>
    if (← B.choose 4) == 0 then return [.intConst .i32 (BitVec.ofNat 32 (← B.bytes 4))]
    return [.intConst .i32 (BitVec.ofInt 32 ((← B.choose 256 : Nat) - 128 : Int))]
  | .num (.int .i64) =>
    if (← B.choose 4) == 0 then return [.intConst .i64 (BitVec.ofNat 64 (← B.bytes 8))]
    return [.intConst .i64 (BitVec.ofInt 64 ((← B.choose 256 : Nat) - 128 : Int))]
  | .num (.float ft) =>
    return [floatConst ft (← B.bool) (← B.choose 1024) (← B.choose 4)]
  | .ref r => return [.refNull r.heap]
  | .vec _ => return [.vecConst (BitVec.ofNat 128 (← B.bytes 16))]

/-- A leaf: a constant or a local. Constants are generated whatever `--allowed-instructions`
says (they end every value). -/
def genLeaf (c : Ctx) (f : FCtx) (t : ValType) : B (List Instr) := do
  let locs := indicesWhere (· == t) f.locals
  if c.al "variable" && !locs.isEmpty && (← B.choose 3) == 0 then
    return [.localGet (ix (← B.pick 0 locs))]
  genConst t

/-! ## Operators -/

def intBinOps : List IntBinOp :=
  [.add, .sub, .mul, .div .signed, .div .unsigned, .rem .signed, .rem .unsigned, .and, .or,
    .xor, .shl, .shr .signed, .shr .unsigned, .rotl, .rotr]

/-- Can the integer operator trap (division by zero, overflow)? -/
def intBinTraps : IntBinOp → Bool
  | .div _ | .rem _ => true
  | _ => false

def intRelOps : List IntRelOp :=
  [.eq, .ne, .lt .signed, .lt .unsigned, .gt .signed, .gt .unsigned, .le .signed,
    .le .unsigned, .ge .signed, .ge .unsigned]

def floatBinOps : List FloatBinOp := [.add, .sub, .mul, .div, .min, .max, .copysign]
def floatUnOps : List FloatUnOp := [.abs, .neg, .sqrt, .ceil, .floor, .trunc, .nearest]
def floatRelOps : List FloatRelOp := [.eq, .ne, .lt, .gt, .le, .ge]

/-- The integer unary operators of `S` at `t`. -/
def intUnOps (S : FeatureSet) (t : IntType) : List IntUnOp :=
  [.clz, .ctz, .popcnt] ++
    (if S.has .signExt then
      [.extend .i8, .extend .i16] ++ (if t == .i64 then [.extend .i32] else [])
    else [])

/-- The conversions of `S` to `t`, with their source types. -/
def convertsTo (S : FeatureSet) : ValType → List (ConvertOp × ValType)
  | .num (.int .i32) =>
    [(.wrap, .i64)] ++
    (if S.has .floatNum then
      [(.trunc .f32 .i32 .signed, .f32), (.trunc .f64 .i32 .unsigned, .f64),
        (.reinterpretInt .f32, .f32)] ++
      (if S.has .satConv then [(.truncSat .f32 .i32 .unsigned, .f32),
        (.truncSat .f64 .i32 .signed, .f64)] else [])
    else [])
  | .num (.int .i64) =>
    [(.extend .signed, .i32), (.extend .unsigned, .i32)] ++
    (if S.has .floatNum then
      [(.trunc .f64 .i64 .signed, .f64), (.trunc .f32 .i64 .unsigned, .f32),
        (.reinterpretInt .f64, .f64)] ++
      (if S.has .satConv then [(.truncSat .f64 .i64 .unsigned, .f64)] else [])
    else [])
  | .num (.float .f32) =>
    [(.demote, .f64), (.convert .i32 .f32 .signed, .i32), (.convert .i64 .f32 .unsigned, .i64),
      (.reinterpretFloat .i32, .i32)]
  | .num (.float .f64) =>
    [(.promote, .f32), (.convert .i32 .f64 .unsigned, .i32), (.convert .i64 .f64 .signed, .i64),
      (.reinterpretFloat .i64, .i64)]
  | _ => []

/-- Can the conversion trap (non-saturating truncation)? -/
def convTraps : ConvertOp → Bool
  | .trunc .. => true
  | _ => false

/-- The conversions `genVal` may use at `t` under `c`: sources of `S`, the kinds allowed, and
no trapping one under `--disallow-traps`. -/
def convs (c : Ctx) (t : ValType) : List (ConvertOp × ValType) :=
  (convertsTo c.S t).filter fun p =>
    (numTypes c.S).contains p.2 && !(c.cfg.disallowTraps && convTraps p.1) &&
      c.al (if isFloat t || isFloat p.2 then "numeric_float" else "numeric_int")

/-- The loads producing `t`, with the log2 of their natural alignment. -/
def loadsOf : ValType → List (Instr × Nat)
  | .num (.int .i32) =>
    [(.intLoad .i32 none (ix 0) (memArg 0 0), 2),
      (.intLoad .i32 (some (.i8, .signed)) (ix 0) (memArg 0 0), 0),
      (.intLoad .i32 (some (.i8, .unsigned)) (ix 0) (memArg 0 0), 0),
      (.intLoad .i32 (some (.i16, .signed)) (ix 0) (memArg 0 0), 1),
      (.intLoad .i32 (some (.i16, .unsigned)) (ix 0) (memArg 0 0), 1)]
  | .num (.int .i64) =>
    [(.intLoad .i64 none (ix 0) (memArg 0 0), 3),
      (.intLoad .i64 (some (.i8, .unsigned)) (ix 0) (memArg 0 0), 0),
      (.intLoad .i64 (some (.i16, .signed)) (ix 0) (memArg 0 0), 1),
      (.intLoad .i64 (some (.i32, .signed)) (ix 0) (memArg 0 0), 2),
      (.intLoad .i64 (some (.i32, .unsigned)) (ix 0) (memArg 0 0), 2)]
  | .num (.float .f32) => [(.floatLoad .f32 (ix 0) (memArg 0 0), 2)]
  | .num (.float .f64) => [(.floatLoad .f64 (ix 0) (memArg 0 0), 3)]
  | .vec _ => [(.vecLoad .full (ix 0) (memArg 0 0), 4),
      (.vecLoad (.extend8x8 .signed) (ix 0) (memArg 0 0), 3),
      (.vecLoad (.extend16x4 .unsigned) (ix 0) (memArg 0 0), 3),
      (.vecLoad (.extend32x2 .signed) (ix 0) (memArg 0 0), 3),
      (.vecLoad (.splat .i8) (ix 0) (memArg 0 0), 0),
      (.vecLoad (.splat .i16) (ix 0) (memArg 0 0), 1),
      (.vecLoad (.splat .i32) (ix 0) (memArg 0 0), 2),
      (.vecLoad (.splat .i64) (ix 0) (memArg 0 0), 3),
      (.vecLoad .zero32 (ix 0) (memArg 0 0), 2),
      (.vecLoad .zero64 (ix 0) (memArg 0 0), 3)]
  | _ => []

/-- Replace the memory argument of a load or store. -/
def withArg (a : MemArg) : Instr → Instr
  | .intLoad t p x _ => .intLoad t p x a
  | .floatLoad t x _ => .floatLoad t x a
  | .intStore t p x _ => .intStore t p x a
  | .floatStore t x _ => .floatStore t x a
  | .vecLoad op x _ => .vecLoad op x a
  | .vecStore x _ => .vecStore x a
  | i => i

/-- Replace the memory index of a load or store. -/
def withMem (x : MemIdx) : Instr → Instr
  | .intLoad t p _ a => .intLoad t p x a
  | .floatLoad t _ a => .floatLoad t x a
  | .intStore t p _ a => .intStore t p x a
  | .floatStore t _ a => .floatStore t x a
  | .vecLoad op _ a => .vecLoad op x a
  | .vecStore _ a => .vecStore x a
  | i => i

/-- The stores of `t`, with the log2 of their natural alignment. -/
def storesOf : ValType → List (Instr × Nat)
  | .num (.int .i32) =>
    [(.intStore .i32 none (ix 0) (memArg 0 0), 2), (.intStore .i32 (some .i8) (ix 0) (memArg 0 0), 0),
      (.intStore .i32 (some .i16) (ix 0) (memArg 0 0), 1)]
  | .num (.int .i64) =>
    [(.intStore .i64 none (ix 0) (memArg 0 0), 3), (.intStore .i64 (some .i16) (ix 0) (memArg 0 0), 1),
      (.intStore .i64 (some .i32) (ix 0) (memArg 0 0), 2)]
  | .num (.float .f32) => [(.floatStore .f32 (ix 0) (memArg 0 0), 2)]
  | .num (.float .f64) => [(.floatStore .f64 (ix 0) (memArg 0 0), 3)]
  | .vec _ => [(.vecStore (ix 0) (memArg 0 0), 4)]
  | _ => []

/-- A random memory argument for natural alignment `2^n`. -/
def genArg (n : Nat) : B MemArg := do
  let a ← if (← B.choose 4) == 0 then B.choose (n + 1) else pure n
  let off ← if (← B.choose 3) == 0 then B.choose 64 else pure 0
  return memArg a off

/-- The memory kind of an access at `t` (`memory_int` or `memory_float`). -/
def memKind (t : ValType) : String :=
  if isFloat t then "memory_float" else "memory_int"

/-! ## SIMD -/

def intShapes : List IntShape := [.i8x16, .i16x8, .i32x4, .i64x2]
def floatShapes : List FloatShape := [.f32x4, .f64x2]

/-- A lane index. -/
def lane (k : Nat) : LaneIdx := ⟨k % 256, Nat.mod_lt _ (by decide)⟩

/-- `v128 v128 → v128` operators (integer ones only for the shapes they exist at). -/
def vbinOps : List Instr :=
  [.vecBinOp .and, .vecBinOp .andnot, .vecBinOp .or, .vecBinOp .xor] ++
  intShapes.flatMap (fun s =>
    ([VecIntBinOp.add, .sub, .mul, .addSat .signed, .addSat .unsigned, .subSat .signed,
      .subSat .unsigned, .min .signed, .min .unsigned, .max .signed, .max .unsigned,
      .avgrU].filter (VecIntBinOp.valid s)).map (.vecIntBinOp s))

def vbinFloatOps : List Instr :=
  floatShapes.flatMap fun s =>
    [VecFloatBinOp.add, .sub, .mul, .div, .min, .max, .pmin, .pmax].map (.vecFloatBinOp s)

/-- `v128 → v128` operators. -/
def vunOps : List Instr :=
  [.vecUnOp .not] ++
  intShapes.flatMap (fun s =>
    ([VecIntUnOp.abs, .neg, .popcnt].filter (VecIntUnOp.valid s)).map (.vecIntUnOp s))

def vunFloatOps : List Instr :=
  floatShapes.flatMap fun s => floatUnOps.map (.vecFloatUnOp s)

/-- The vector operators of `c` at `v128 v128 → v128` and `v128 → v128`. -/
def vbins (c : Ctx) : List Instr :=
  (if c.al "vector_int" then vbinOps else []) ++ (if c.al "vector_float" then vbinFloatOps else [])
def vuns (c : Ctx) : List Instr :=
  (if c.al "vector_int" then vunOps else []) ++ (if c.al "vector_float" then vunFloatOps else [])

/-- The splats into `v128`, with their scalar source. -/
def splats (c : Ctx) : List (Shape × ValType) :=
  ((if c.al "vector_int" then [(Shape.int .i8x16, ValType.i32), (.int .i16x8, .i32),
      (.int .i32x4, .i32), (.int .i64x2, .i64)] else []) ++
   (if c.al "vector_float" then [(Shape.float .f32x4, ValType.f32), (.float .f64x2, .f64)]
    else [])).filter fun p => (numTypes c.S).contains p.2

/-- The lane extractions producing `t`: shape, sign, lane count. -/
def extracts (c : Ctx) : ValType → List (Shape × Option Signedness × Nat)
  | .num (.int .i32) => if !c.al "vector_int" then [] else
    [(.int .i8x16, some .signed, 16), (.int .i8x16, some .unsigned, 16),
      (.int .i16x8, some .signed, 8), (.int .i16x8, some .unsigned, 8), (.int .i32x4, none, 4)]
  | .num (.int .i64) => if c.al "vector_int" then [(.int .i64x2, none, 2)] else []
  | .num (.float .f32) => if c.al "vector_float" then [(.float .f32x4, none, 4)] else []
  | .num (.float .f64) => if c.al "vector_float" then [(.float .f64x2, none, 2)] else []
  | _ => []

/-- `v128 → i32` tests. -/
def vtests : List Instr :=
  [.vecTestOp .anyTrue] ++ intShapes.map .vecAllTrue ++ intShapes.map .vecBitmask

def vshifts : List Instr :=
  intShapes.flatMap fun s => [VecShiftOp.shl, .shr .signed, .shr .unsigned].map (.vecShiftOp s)

/-- `v128 v128 → v128` comparisons. -/
def vrelOps : List Instr :=
  intShapes.flatMap (fun s => (intRelOps.filter (IntRelOp.validShape s)).map (.vecIntRelOp s)) ++
  floatShapes.flatMap fun s => floatRelOps.map (.vecFloatRelOp s)

/-- The integer narrowings `(source, target)`. -/
def narrows : List (IntShape × IntShape) := [(.i16x8, .i8x16), (.i32x4, .i16x8)]

/-- The integer extensions `(source, target)`. -/
def extends_ : List (IntShape × IntShape) := [(.i8x16, .i16x8), (.i16x8, .i32x4), (.i32x4, .i64x2)]

/-- `v128 → v128` conversions between float and integer shapes (none traps). -/
def vconvs : List (Shape × Shape × VecConvertOp) :=
  [(.int .i32x4, .float .f32x4, .convert none .signed),
   (.int .i32x4, .float .f32x4, .convert none .unsigned),
   (.int .i32x4, .float .f64x2, .convert (some .low) .signed),
   (.int .i32x4, .float .f64x2, .convert (some .low) .unsigned),
   (.float .f32x4, .int .i32x4, .truncSat .signed false),
   (.float .f32x4, .int .i32x4, .truncSat .unsigned false),
   (.float .f64x2, .int .i32x4, .truncSat .signed true),
   (.float .f64x2, .int .i32x4, .truncSat .unsigned true),
   (.float .f64x2, .float .f32x4, .demoteZero),
   (.float .f32x4, .float .f64x2, .promoteLow)]

/-- The lane replacements: shape, scalar type, lane count. -/
def replaces (c : Ctx) : List (Shape × ValType × Nat) :=
  ((if c.al "vector_int" then [(Shape.int .i8x16, ValType.i32, 16), (.int .i16x8, .i32, 8),
      (.int .i32x4, .i32, 4), (.int .i64x2, .i64, 2)] else []) ++
   (if c.al "vector_float" then [(Shape.float .f32x4, ValType.f32, 4), (.float .f64x2, .f64, 2)]
    else [])).filter fun p => (numTypes c.S).contains p.2.1

/-- The relaxed SIMD operators, by arity (`1`, `2` or `3` operands). -/
def relaxedOps : List (Nat × Instr) :=
  [(2, .vecSwizzle .relaxedSwizzle), (2, .vecIntBinOp .i16x8 .relaxedQ15mulrS),
   (2, .vecFloatBinOp .f32x4 .relaxedMin), (2, .vecFloatBinOp .f32x4 .relaxedMax),
   (2, .vecFloatBinOp .f64x2 .relaxedMin), (2, .vecFloatBinOp .f64x2 .relaxedMax),
   (2, .vecExtBinOp .i8x16 .i16x8 .relaxedDotS),
   (3, .vecFloatTernOp .f32x4 .relaxedMadd), (3, .vecFloatTernOp .f32x4 .relaxedNmadd),
   (3, .vecFloatTernOp .f64x2 .relaxedMadd), (3, .vecFloatTernOp .f64x2 .relaxedNmadd),
   (3, .vecExtTernOp .i8x16 .i32x4 .relaxedDotAddS),
   (1, .vecConvert (.float .f32x4) (.int .i32x4) (.relaxedTrunc .signed false)),
   (1, .vecConvert (.float .f32x4) (.int .i32x4) (.relaxedTrunc .unsigned false)),
   (1, .vecConvert (.float .f64x2) (.int .i32x4) (.relaxedTrunc .signed true)),
   (1, .vecConvert (.float .f64x2) (.int .i32x4) (.relaxedTrunc .unsigned true))] ++
  intShapes.map fun s => (3, .vecIntTernOp s .relaxedLaneSelect)

/-! ## Instructions -/

/-- What `genVal` may do at a type, as tags (chosen uniformly among the applicable ones). -/
inductive VOp where
  | leaf | global | binop | unop | eqz | rel | conv | load | memSize | memGrow | call
  | block | ifElse | select | tee
  | vbin | vun | vtern | splat | vshift | vtest | extract | callInd
  | tableGet | tableSize | tableGrow | refFunc | refIsNull
  | structGet | arrayLen | arrayGet | i31Get | refEq | refTest
  | vrel | shuffle | vnarrow | vext | vconv | replace | relaxed
  deriving DecidableEq, Repr, Inhabited

/-- The functions a body may call: all, or under `--ensure-termination` those below it. -/
def callees (c : Ctx) (f : FCtx) : List Nat :=
  (List.range c.funcs.length).filter fun i => !c.cfg.ensureTermination || i < f.self

/-- May `call_indirect` be used (a table, the capability, no trap or termination demand)? -/
def indirectOk (c : Ctx) : Bool :=
  !c.funcTabs.isEmpty && c.S.has .callIndirect && c.al "control" && !c.cfg.disallowTraps &&
    !c.cfg.ensureTermination

/-- The arithmetic kind of `t`. -/
def numKind (t : ValType) : String := if isFloat t then "numeric_float" else "numeric_int"

/-- The `VOp`s applicable at `t`. -/
def vops (c : Ctx) (f : FCtx) (t : ValType) : List VOp :=
  let S := c.S
  let ctl := S.has .control && c.al "control"
  let simd := S.has .simd
  let mem := c.hasMem && S.has .intNum && !c.cfg.disallowTraps
  List.flatten [
    [VOp.leaf],
    (if S.has .globals && c.al "variable" && c.globals.any (·.value == t) then [.global] else []),
    (if c.al (numKind t) then
      match t with
       | .num (.int _) => [.binop, .unop] ++ (if t == .i32 then [.eqz, .rel] else [])
       | .num (.float _) => [.binop, .unop]
       | _ => []
     else []),
    (if !(convs c t).isEmpty then [.conv] else []),
    (if mem && c.al (memKind t) && !(loadsOf t).isEmpty then [.load] else []),
    (if c.hasMem && S.has .intNum && c.al "memory_int" &&
        ((t == .i32 && !(c.memsAt .i32).isEmpty) || (t == .i64 && !(c.memsAt .i64).isEmpty))
     then [.memSize, .memGrow] else []),
    (if S.has .directCall && c.al "control" &&
        (callees c f).any (fun i => (c.funcs.getD i ⟨[], []⟩).results == [t]) then [.call]
     else []),
    (if ctl && f.depth > 0 then [.block] else []),
    (if ctl && f.depth > 0 && S.has .intNum then [.ifElse] else []),
    (if S.has .control && c.al "parametric" && S.has .intNum && (isNumVec t || S.has .refTypes)
     then [.select] else []),
    (if S.has .control && c.al "variable" && f.locals.contains t then [.tee] else []),
    (if simd && t == v128 then
      (if !(vbins c).isEmpty then [.vbin] else []) ++ (if !(vuns c).isEmpty then [.vun] else []) ++
      (if c.al "vector_int" then [.vtern, .vshift] else []) ++
      (if !(splats c).isEmpty then [.splat] else [])
     else []),
    (if simd && t == .i32 && c.al "vector_int" then [.vtest] else []),
    (if simd && !(extracts c t).isEmpty then [.extract] else []),
    (if indirectOk c && c.types.any (·.results == [t]) then [.callInd] else []),
    (if S.has .refTypes && c.al "table" && !c.cfg.disallowTraps && !(c.tabsOf t).isEmpty
     then [.tableGet] else []),
    (if S.has .refTypes && S.has .intNum && c.al "table" && c.nTab > 0 && t == .i32
     then [.tableSize, .tableGrow] else []),
    (if S.has .refTypes && c.al "reference" && t == funcref && !c.declared.isEmpty
     then [.refFunc] else []),
    (if S.has .refTypes && S.has .intNum && c.al "reference" && t == .i32 then [.refIsNull]
     else []),
    (if S.has .gcImm && c.al "aggregate" && !(c.structFields t).isEmpty then [.structGet] else []),
    (if S.has .gcImm && S.has .intNum && c.al "aggregate" && t == .i32 && !(c.arrays none).isEmpty
     then [.arrayLen] else []),
    (if S.has .gcImm && S.has .intNum && c.al "aggregate" && !(c.arrays (some t)).isEmpty
     then [.arrayGet] else []),
    (if S.has .gcImm && S.has .intNum && c.al "aggregate" && t == .i32 then [.i31Get] else []),
    (if S.has .gcImm && S.has .intNum && c.al "reference" && t == .i32 then [.refEq, .refTest]
     else []),
    (if simd && t == v128 && c.al "vector_int" then [.vrel, .shuffle, .vnarrow, .vext] else []),
    (if simd && t == v128 && !(replaces c).isEmpty then [.replace] else []),
    (if simd && t == v128 && c.al "vector_float" then [.vconv] else []),
    (if simd && t == v128 && S.has .relaxedSimd && c.al "vector_int" && c.al "vector_float"
     then [.relaxed] else [])]

/-- What `genStmt` may do, as tags. -/
inductive SOp where
  | nop | localSet | globalSet | store | drop | block | loop | ifThen | brIf | fill | copy
  | call | callInd | retCall | retCallInd
  | tableSet | tableFill | tableCopy | tableInit | elemDrop | memInit | dataDrop
  | throw | tryTable | structSet | arraySet
  deriving DecidableEq, Repr, Inhabited

/-- The labels `br_if` may target: no values, and no loop under `--ensure-termination`. -/
def brTargets (c : Ctx) (f : FCtx) : List Nat :=
  (List.range f.labels.length).filter fun i =>
    (f.labels.getD i []).isEmpty && !(c.cfg.ensureTermination && f.loops.getD i false)

/-- The value types a store may write. -/
def storeTypes (c : Ctx) : List ValType :=
  (numTypes c.S ++ vecTypes c.S).filter fun t => c.al (memKind t) &&
    (t != v128 || c.al "vector_int")

/-- The functions `return_call` may target: the results of the caller. -/
def retCallees (c : Ctx) (f : FCtx) : List Nat :=
  (callees c f).filter fun i => (c.funcs.getD i ⟨[], []⟩).results == f.results

/-- The `SOp`s applicable. -/
def sops (c : Ctx) (f : FCtx) : List SOp :=
  let S := c.S
  let ctl := S.has .control && c.al "control"
  let mem := c.hasMem && S.has .intNum && !c.cfg.disallowTraps
  List.flatten [
    (if ctl then [SOp.nop] else []),
    (if S.has .control && c.al "variable" && !f.locals.isEmpty then [.localSet] else []),
    (if S.has .mutGlobal && c.al "variable" && c.globals.any (·.mutability == .var) then
      [.globalSet] else []),
    (if mem && !(storeTypes c).isEmpty then [.store] else []),
    (if S.has .control && c.al "parametric" && !(valTypes S).isEmpty then [.drop] else []),
    (if ctl && f.depth > 0 then [.block, .loop] else []),
    (if ctl && f.depth > 0 && S.has .intNum then [.ifThen] else []),
    (if ctl && S.has .intNum && !(brTargets c f).isEmpty then [.brIf] else []),
    (if mem && S.has .bulkMemoryOpt && c.al "memory_int" then [.fill, .copy] else []),
    (if S.has .directCall && c.al "control" && !(callees c f).isEmpty then [.call] else []),
    (if indirectOk c && !c.types.isEmpty then [.callInd] else []),
    (if S.has .tailCall && c.al "control" && !(retCallees c f).isEmpty then [.retCall] else []),
    (if S.has .tailCall && indirectOk c && c.types.any (·.results == f.results) then
      [.retCallInd] else []),
    (if S.has .refTypes && S.has .intNum && c.al "table" && !c.cfg.disallowTraps && c.nTab > 0
     then [.tableSet, .tableFill, .tableCopy] else []),
    (if S.has .bulkMemory && S.has .intNum && c.al "table" && !c.cfg.disallowTraps &&
        !c.funcTabs.isEmpty && !c.elemTypes.isEmpty then [.tableInit] else []),
    (if S.has .bulkMemory && c.al "table" && !c.elemTypes.isEmpty then [.elemDrop] else []),
    (if S.has .bulkMemory && c.al "memory_int" && mem && c.nData > 0 then [.memInit] else []),
    (if S.has .bulkMemory && c.al "memory_int" && c.nData > 0 then [.dataDrop] else []),
    (if S.has .exn && S.has .intNum && c.al "control" && !c.tags.isEmpty && !c.cfg.disallowTraps
     then [.throw] else []),
    (if S.has .exn && ctl && f.depth > 0 then [.tryTable] else []),
    (if S.has .gcMut && c.al "aggregate" && !(mutFields c).isEmpty then [.structSet] else []),
    (if S.has .gcMut && S.has .intNum && c.al "aggregate" &&
        (c.arrays none).any (·.2.mutability == .var) then [.arraySet] else [])]

/-- `n` results of a `B` action. -/
def G.many' {α : Type} : Nat → B α → B (List α)
  | 0, _ => return []
  | n + 1, g => return (← g) :: (← G.many' n g)

/-- A memory index. -/
def genMem (c : Ctx) : B MemIdx := do return ix (← B.choose (max c.nMem 1))

/-- A memory index with its address value type. -/
def genMemA (c : Ctx) : B (MemIdx × ValType) := do
  let x ← B.choose (max c.nMem 1)
  return (ix x, addrVal (c.addrOf x))

/-- The labels a `catch` may target for a tag with parameters `ps` (a loop label is a backward
branch, excluded under `--ensure-termination`). -/
def catchTargets (c : Ctx) (f : FCtx) (ps : List ValType) : List Nat :=
  (List.range f.labels.length).filter fun i =>
    f.labels.getD i [] == ps && !(c.cfg.ensureTermination && f.loops.getD i false)

mutual

/-- Code that pushes one value of type `t`. -/
def genVal (c : Ctx) (f : FCtx) (t : ValType) : Nat → B (List Instr)
  | 0 => genLeaf c f t
  | fuel + 1 => do
    if !(← B.left) then return ← genLeaf c f t
    B.spend 1
    let S := c.S
    match ← B.pick .leaf (vops c f t) with
    | .leaf => genLeaf c f t
    | .global =>
      let gs := indicesWhere (·.value == t) c.globals
      return [.globalGet (ix (← B.pick 0 gs))]
    | .binop =>
      let a ← genVal c f t fuel
      let b ← genVal c f t fuel
      match t with
      | .num (.int it) =>
        let ops := intBinOps.filter fun o => !(c.cfg.disallowTraps && intBinTraps o)
        return a ++ b ++ [.intBinOp it (← B.pick .add ops)]
      | .num (.float ft) => return a ++ b ++ [.floatBinOp ft (← B.pick .add floatBinOps)]
      | _ => genLeaf c f t
    | .unop =>
      let a ← genVal c f t fuel
      match t with
      | .num (.int it) => return a ++ [.intUnOp it (← B.pick .clz (intUnOps S it))]
      | .num (.float ft) => return a ++ [.floatUnOp ft (← B.pick .abs floatUnOps)]
      | _ => genLeaf c f t
    | .eqz =>
      let u ← B.pick .i32 [.i32, .i64]
      let a ← genVal c f u fuel
      match u with
      | .num (.int it) => return a ++ [.intTestOp it .eqz]
      | _ => genLeaf c f t
    | .rel =>
      let u ← B.pick .i32 ((numTypes S).filter (c.al ∘ numKind))
      let a ← genVal c f u fuel
      let b ← genVal c f u fuel
      match u with
      | .num (.int it) => return a ++ b ++ [.intRelOp it (← B.pick .eq intRelOps)]
      | .num (.float ft) => return a ++ b ++ [.floatRelOp ft (← B.pick .eq floatRelOps)]
      | _ => genLeaf c f t
    | .conv =>
      let (op, u) ← B.pick (.wrap, .i64) (convs c t)
      return (← genVal c f u fuel) ++ [.convert op]
    | .load =>
      let (i, n) ← B.pick (.nop, 0) (loadsOf t)
      let (x, aty) ← genMemA c
      let a ← genVal c f aty fuel
      return a ++ [withMem x (withArg (← genArg n) i)]
    | .memSize =>
      let x ← B.pick 0 (c.memsAt (if t == .i64 then .i64 else .i32))
      return [.memorySize (ix x)]
    | .memGrow =>
      let x ← B.pick 0 (c.memsAt (if t == .i64 then .i64 else .i32))
      let a ← genVal c f t fuel
      return a ++ [.memoryGrow (ix x)]
    | .call =>
      let fs := (callees c f).filter fun i => (c.funcs.getD i ⟨[], []⟩).results == [t]
      let fi ← B.pick 0 fs
      let ft := c.funcs.getD fi ⟨[], []⟩
      let args ← genVals c f ft.params fuel
      return args ++ [.call (ix fi)]
    | .block =>
      let f' := { f with labels := [t] :: f.labels, loops := false :: f.loops,
                         depth := f.depth - 1 }
      let pre ← genStmts c f' fuel (← B.choose 3)
      let v ← genVal c f' t fuel
      return [.block (.value t) (pre ++ v)]
    | .ifElse =>
      let cond ← genVal c f .i32 fuel
      let f' := { f with labels := [t] :: f.labels, loops := false :: f.loops,
                         depth := f.depth - 1 }
      let a ← genVal c f' t fuel
      let b ← genVal c f' t fuel
      return cond ++ [.if_ (.value t) a b]
    | .select =>
      let a ← genVal c f t fuel
      let b ← genVal c f t fuel
      let cond ← genVal c f .i32 fuel
      return a ++ b ++ cond ++ [.select (if isNumVec t then none else some [t])]
    | .tee =>
      let ls := indicesWhere (· == t) f.locals
      return (← genVal c f t fuel) ++ [.localTee (ix (← B.pick 0 ls))]
    | .vbin =>
      let a ← genVal c f t fuel
      let b ← genVal c f t fuel
      return a ++ b ++ [← B.pick (.vecBinOp .and) (vbins c)]
    | .vun =>
      let a ← genVal c f t fuel
      return a ++ [← B.pick (.vecUnOp .not) (vuns c)]
    | .vtern =>
      let a ← genVal c f t fuel
      let b ← genVal c f t fuel
      let m ← genVal c f t fuel
      return a ++ b ++ m ++ [.vecTernOp .bitselect]
    | .vshift =>
      let a ← genVal c f t fuel
      let n ← genVal c f .i32 fuel
      return a ++ n ++ [← B.pick (.vecUnOp .not) vshifts]
    | .splat =>
      let (sh, u) ← B.pick (.int .i32x4, .i32) (splats c)
      return (← genVal c f u fuel) ++ [.vecSplat sh]
    | .vtest =>
      let a ← genVal c f v128 fuel
      return a ++ [← B.pick (.vecTestOp .anyTrue) vtests]
    | .extract =>
      let (sh, sg, n) ← B.pick (.int .i32x4, none, 4) (extracts c t)
      let a ← genVal c f v128 fuel
      return a ++ [.vecExtractLane sh sg (lane (← B.choose n))]
    | .callInd =>
      let ts := indicesWhere (·.results == [t]) c.types
      let ti ← B.pick 0 ts
      let ft := c.types.getD ti ⟨[], []⟩
      let args ← genVals c f ft.params fuel
      let i ← genVal c f .i32 fuel
      return args ++ i ++ [.callIndirect (ix (← B.pick 0 c.funcTabs)) (ix ti)]
    | .tableGet =>
      let x ← B.pick 0 (c.tabsOf t)
      return (← genVal c f .i32 fuel) ++ [.tableGet (ix x)]
    | .tableSize => return [.tableSize (ix (← B.choose c.nTab))]
    | .tableGrow =>
      let x ← B.choose c.nTab
      let et := ValType.ref (c.tabTypes.getD x ⟨true, .abstract .func⟩)
      let v ← genVal c f et fuel
      let n ← genVal c f .i32 fuel
      return v ++ n ++ [.tableGrow (ix x)]
    | .refFunc => return [.refFunc (ix (← B.pick 0 c.declared))]
    | .refIsNull =>
      let u ← B.pick funcref [funcref, externref]
      return (← genVal c f u fuel) ++ [.refIsNull]
    | .structGet =>
      let (ti, i, fld) ← B.pick (0, 0, ⟨.const, .val .i32⟩) (c.structFields t)
      let args ← genVals c f ((c.fieldsOf ti).map (·.storage.unpacked)) fuel
      let sg ← match fld.storage with
        | .packed _ => (do return some (← B.pick .signed [.signed, .unsigned]))
        | .val _ => pure none
      return args ++ [.structNew (ix ti), .structGet sg (ix ti) (ix i)]
    | .arrayLen =>
      let (ti, fld) ← B.pick (0, ⟨.const, .val .i32⟩) (c.arrays none)
      let v ← genVal c f fld.storage.unpacked fuel
      let n ← B.choose 8
      return v ++ [.intConst .i32 (BitVec.ofNat 32 n), .arrayNew (ix ti), .arrayLen]
    | .arrayGet =>
      let (ti, fld) ← B.pick (0, ⟨.const, .val .i32⟩) (c.arrays (some t))
      let v ← genVal c f fld.storage.unpacked fuel
      let n ← B.range 1 8
      let j ← B.choose n
      let sg ← match fld.storage with
        | .packed _ => (do return some (← B.pick .signed [.signed, .unsigned]))
        | .val _ => pure none
      return v ++ [.intConst .i32 (BitVec.ofNat 32 n), .arrayNew (ix ti),
        .intConst .i32 (BitVec.ofNat 32 j), .arrayGet sg (ix ti)]
    | .i31Get =>
      let a ← genVal c f .i32 fuel
      return a ++ [.refI31, .i31Get (← B.pick .signed [.signed, .unsigned])]
    | .refEq =>
      let a ← genVal c f .i32 fuel
      let b ← genVal c f .i32 fuel
      return a ++ [.refI31] ++ b ++ [.refI31, .refEq]
    | .refTest =>
      let a ← genVal c f .i32 fuel
      let h ← B.pick .i31 [.i31, .eq, .any, .struct, .array, .none]
      return a ++ [.refI31, .refTest ⟨false, .abstract h⟩]
    | .vrel =>
      let a ← genVal c f t fuel
      let b ← genVal c f t fuel
      return a ++ b ++ [← B.pick (.vecBinOp .and) vrelOps]
    | .shuffle =>
      let a ← genVal c f t fuel
      let b ← genVal c f t fuel
      let ls ← G.many' 16 (B.choose 32)
      return a ++ b ++ [.vecShuffle (ls.map lane)]
    | .vnarrow =>
      let a ← genVal c f t fuel
      let b ← genVal c f t fuel
      let (src, tgt) ← B.pick (.i16x8, .i8x16) narrows
      return a ++ b ++ [.vecNarrow src tgt (← B.pick .signed [.signed, .unsigned])]
    | .vext =>
      let a ← genVal c f t fuel
      let (src, tgt) ← B.pick (.i8x16, .i16x8) extends_
      let h ← B.pick .low [.low, .high]
      let sg ← B.pick .signed [.signed, .unsigned]
      return a ++ [.vecConvert (.int src) (.int tgt) (.extend h sg)]
    | .vconv =>
      let a ← genVal c f t fuel
      let (src, tgt, op) ← B.pick (.int .i32x4, .float .f32x4, .convert none .signed) vconvs
      return a ++ [.vecConvert src tgt op]
    | .replace =>
      let (sh, u, n) ← B.pick (.int .i32x4, .i32, 4) (replaces c)
      let a ← genVal c f t fuel
      let v ← genVal c f u fuel
      return a ++ v ++ [.vecReplaceLane sh (lane (← B.choose n))]
    | .relaxed =>
      let (k, i) ← B.pick (2, .vecSwizzle .relaxedSwizzle) relaxedOps
      let a ← genVal c f t fuel
      let b ← if k ≥ 2 then genVal c f t fuel else pure []
      let m ← if k ≥ 3 then genVal c f t fuel else pure []
      return a ++ b ++ m ++ [i]
termination_by fuel => (fuel, 0)

/-- Code that pushes values of the types `ts`, in order. -/
def genVals (c : Ctx) (f : FCtx) : List ValType → Nat → B (List Instr)
  | [], _ => return []
  | t :: ts, fuel => return (← genVal c f t fuel) ++ (← genVals c f ts fuel)
termination_by ts fuel => (fuel, ts.length + 1)

/-- Code with no net effect on the operand stack. -/
def genStmt (c : Ctx) (f : FCtx) : Nat → B (List Instr)
  | 0 => return []
  | fuel + 1 => do
    if !(← B.left) then return []
    B.spend 1
    match ← B.pick .nop (sops c f) with
    | .nop => return [.nop]
    | .localSet =>
      let i ← B.choose f.locals.length
      let t := f.locals.getD i .i32
      return (← genVal c f t fuel) ++ [.localSet (ix i)]
    | .globalSet =>
      let gs := indicesWhere (·.mutability == .var) c.globals
      let g ← B.pick 0 gs
      let t := (c.globals.getD g ⟨.const, .i32⟩).value
      return (← genVal c f t fuel) ++ [.globalSet (ix g)]
    | .store =>
      let t ← B.pick .i32 (storeTypes c)
      let (i, n) ← B.pick (.nop, 0) (storesOf t)
      let (x, aty) ← genMemA c
      let a ← genVal c f aty fuel
      let v ← genVal c f t fuel
      return a ++ v ++ [withMem x (withArg (← genArg n) i)]
    | .drop =>
      let t ← B.pick .i32 (valTypes c.S)
      return (← genVal c f t fuel) ++ [.drop]
    | .block =>
      let f' := { f with labels := [] :: f.labels, loops := false :: f.loops, depth := f.depth - 1 }
      return [.block .empty (← genStmts c f' fuel (← B.range 1 4))]
    | .loop =>
      let f' := { f with labels := [] :: f.labels, loops := true :: f.loops, depth := f.depth - 1 }
      return [.loop .empty (← genStmts c f' fuel (← B.range 1 4))]
    | .ifThen =>
      let cond ← genVal c f .i32 fuel
      let f' := { f with labels := [] :: f.labels, loops := false :: f.loops, depth := f.depth - 1 }
      let a ← genStmts c f' fuel (← B.range 1 3)
      let b ← if (← B.bool) then genStmts c f' fuel (← B.range 1 3) else pure []
      return cond ++ [.if_ .empty a b]
    | .brIf =>
      let l ← B.pick 0 (brTargets c f)
      return (← genVal c f .i32 fuel) ++ [.brIf (ix l)]
    | .fill =>
      let (x, aty) ← genMemA c
      return (← genVal c f aty fuel) ++ (← genVal c f .i32 fuel) ++ (← genVal c f aty fuel) ++
        [.memoryFill x]
    | .copy =>
      let (x, aty) ← genMemA c
      let y ← B.pick 0 (c.memsAt (c.addrOf x.toNat))
      return (← genVal c f aty fuel) ++ (← genVal c f aty fuel) ++ (← genVal c f aty fuel) ++
        [.memoryCopy x (ix y)]
    | .call =>
      let fi ← B.pick 0 (callees c f)
      let ft := c.funcs.getD fi ⟨[], []⟩
      let args ← genVals c f ft.params fuel
      return args ++ [.call (ix fi)] ++ ft.results.map fun _ => .drop
    | .callInd =>
      let ti ← B.choose c.types.length
      let ft := c.types.getD ti ⟨[], []⟩
      let args ← genVals c f ft.params fuel
      let i ← genVal c f .i32 fuel
      return args ++ i ++ [.callIndirect (ix (← B.pick 0 c.funcTabs)) (ix ti)] ++
        ft.results.map fun _ => .drop
    | .retCall =>
      let fi ← B.pick 0 (retCallees c f)
      let ft := c.funcs.getD fi ⟨[], []⟩
      return (← genVals c f ft.params fuel) ++ [.returnCall (ix fi)]
    | .retCallInd =>
      let ti ← B.pick 0 (indicesWhere (·.results == f.results) c.types)
      let ft := c.types.getD ti ⟨[], []⟩
      let args ← genVals c f ft.params fuel
      let i ← genVal c f .i32 fuel
      return args ++ i ++ [.returnCallIndirect (ix (← B.pick 0 c.funcTabs)) (ix ti)]
    | .tableSet =>
      let x ← B.choose c.nTab
      let et := ValType.ref (c.tabTypes.getD x ⟨true, .abstract .func⟩)
      let i ← genVal c f .i32 fuel
      let v ← genVal c f et fuel
      return i ++ v ++ [.tableSet (ix x)]
    | .tableFill =>
      let x ← B.choose c.nTab
      let et := ValType.ref (c.tabTypes.getD x ⟨true, .abstract .func⟩)
      let d ← genVal c f .i32 fuel
      let v ← genVal c f et fuel
      let n ← genVal c f .i32 fuel
      return d ++ v ++ n ++ [.tableFill (ix x)]
    | .tableCopy =>
      let x ← B.choose c.nTab
      let et := ValType.ref (c.tabTypes.getD x ⟨true, .abstract .func⟩)
      let y ← B.pick x (c.tabsOf et)
      let d ← genVal c f .i32 fuel
      let s ← genVal c f .i32 fuel
      let n ← genVal c f .i32 fuel
      return d ++ s ++ n ++ [.tableCopy (ix x) (ix y)]
    | .tableInit =>
      let x ← B.pick 0 c.funcTabs
      let e ← B.choose c.elemTypes.length
      let d ← genVal c f .i32 fuel
      let s ← genVal c f .i32 fuel
      let n ← genVal c f .i32 fuel
      return d ++ s ++ n ++ [.tableInit (ix x) (ix e)]
    | .elemDrop => return [.elemDrop (ix (← B.choose c.elemTypes.length))]
    | .memInit =>
      let (x, aty) ← genMemA c
      let di ← B.choose c.nData
      let d ← genVal c f aty fuel
      let s ← genVal c f .i32 fuel
      let n ← genVal c f .i32 fuel
      return d ++ s ++ n ++ [.memoryInit x (ix di)]
    | .dataDrop => return [.dataDrop (ix (← B.choose c.nData))]
    | .throw =>
      let cond ← genVal c f .i32 fuel
      let x ← B.choose c.tags.length
      let f' := { f with labels := [] :: f.labels, loops := false :: f.loops, depth := f.depth - 1 }
      let args ← genVals c f' (c.tags.getD x []) fuel
      return cond ++ [.if_ .empty (args ++ [.throw (ix x)]) []]
    | .tryTable =>
      let k ← B.choose 3
      let cs ← G.many' k (do
        let all ← B.bool
        if all || c.tags.isEmpty then
          let ls := catchTargets c f []
          if ls.isEmpty then return none
          return some (Catch.catchAll (ix (← B.pick 0 ls)))
        let x ← B.choose c.tags.length
        let ls := catchTargets c f (c.tags.getD x [])
        if ls.isEmpty then return none
        return some (Catch.catch_ (ix x) (ix (← B.pick 0 ls))))
      let f' := { f with labels := [] :: f.labels, loops := false :: f.loops, depth := f.depth - 1 }
      let body ← genStmts c f' fuel (← B.range 1 3)
      return [.tryTable .empty (cs.filterMap id) body]
    | .structSet =>
      let (ti, i, fld) ← B.pick (0, 0, ⟨.var, .val .i32⟩) (mutFields c)
      let v ← genVal c f fld.storage.unpacked fuel
      return [.structNewDefault (ix ti)] ++ v ++ [.structSet (ix ti) (ix i)]
    | .arraySet =>
      let (ti, fld) ← B.pick (0, ⟨.var, .val .i32⟩) ((c.arrays none).filter (·.2.mutability == .var))
      let n ← B.range 1 8
      let j ← B.choose n
      let v ← genVal c f fld.storage.unpacked fuel
      return [.intConst .i32 (BitVec.ofNat 32 n), .arrayNewDefault (ix ti),
        .intConst .i32 (BitVec.ofNat 32 j)] ++ v ++ [.arraySet (ix ti)]
termination_by fuel => (fuel, 0)

/-- `n` statements. -/
def genStmts (c : Ctx) (f : FCtx) (fuel : Nat) : Nat → B (List Instr)
  | 0 => return []
  | n + 1 => return (← genStmt c f fuel) ++ (← genStmts c f fuel n)
termination_by n => (fuel, n + 1)

end

/-- The expression depth of generated code. -/
def exprFuel : Nat := 6

/-- A function body of type `ft` with locals `ls`, for the function of index `self`:
statements, then the results. -/
def genBody (c : Ctx) (cfg : Config) (ft : FuncType) (ls : List ValType) (self : Nat := 0) :
    G (List Instr) := do
  let f : FCtx := { locals := ft.params ++ ls, labels := [ft.results], loops := [false],
                    depth := cfg.maxNestingDepth, results := ft.results, self }
  let budget := cfg.maxInstructions
  let run : B (List Instr) := do
    let n ← B.choose 6
    let pre ← genStmts c f exprFuel n
    let post ← genVals c f ft.results exprFuel
    return pre ++ post
  return (← run.run budget).1

/-! ## Modules -/

/-- `n` results of `g`. -/
def G.many {α : Type} (g : Nat → G α) : Nat → G (List α)
  | 0 => return []
  | n + 1 => return (← G.many g n) ++ [← g n]

/-- A function type over `vts`. -/
def genFuncType (S : FeatureSet) (vts : List ValType) : G FuncType := do
  if vts.isEmpty then return ⟨[], []⟩
  let np ← G.choose 5
  let ps ← G.many (fun _ => G.pick .i32 vts) np
  let nr ← G.choose (if S.has .multiValue then 4 else 2)
  let rs ← G.many (fun _ => G.pick .i32 vts) nr
  return ⟨ps, rs⟩

/-- A constant initialiser of type `t`: a constant, or with `extConst` a sum of two. -/
def genInit (S : FeatureSet) (t : ValType) : G Expr := do
  let (e, _) ← (genConst t).run 0
  match t with
  | .num (.int it) =>
    if S.has .extConst && (← G.choose 4) == 0 then
      let (e', _) ← (genConst t).run 0
      return e ++ e' ++ [.intBinOp it (← G.pick .add [.add, .sub, .mul])]
    return e
  | _ => return e

/-- A name from a seed: up to six characters of a printable alphabet. -/
def genName : G String := do
  let alpha := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-.$".toList
  let n ← G.choose 7
  let cs ← G.many (fun _ => G.pick 'a' alpha) n
  return String.ofList cs

/-- A memory or table limit pair `lo' ≤ min ≤ max ≤ hi` (`lo'` is `lo` capped at `hi`). -/
def genLimits (lo0 hi : Nat) (maxRequired : Bool) : G Limits := do
  let lo ← G.range (min lo0 hi) (max (min lo0 hi) (min hi 16))
  let hasMax ← if maxRequired then pure true else G.bool
  if hasMax then
    let up ← G.range lo (min hi (lo + 16))
    return ⟨⟨lo % 2 ^ 64, Nat.mod_lt _ (by decide)⟩, some ⟨up % 2 ^ 64, Nat.mod_lt _ (by decide)⟩⟩
  return ⟨⟨lo % 2 ^ 64, Nat.mod_lt _ (by decide)⟩, none⟩

/-- The single-member recursion group of a function type. -/
def recOf (ft : FuncType) : RecType := ⟨[⟨true, [], .func ft⟩]⟩

/-- A count in `[lo, hi]`, at most `cap`. -/
def count (lo hi cap : Nat) : G Nat := G.range (min lo hi) (min hi cap)

/-- **The raw generator**: a module of `S` within `cfg`, aimed at validity. -/
def genModule (S : FeatureSet) (cfg : Config) : G Module := do
  let vts := valTypes S
  -- types
  let nTypes ← count (max cfg.minTypes 1) cfg.maxTypes 8
  let types0 ← G.many (fun _ => genFuncType S vts) (if cfg.maxTypes = 0 then 0 else nTypes)
  -- `--available-imports`: a subset of the given imports whose types are in `S`
  let typeOk (t : ValType) : Bool := vts.contains t
  let availF := (cfg.availFuncs.getD []).filter fun (_, _, ft) =>
    (ft.params ++ ft.results).all typeOk && (ft.results.length ≤ 1 || S.has .multiValue)
  let availG := cfg.availGlobals.filter fun (_, _, g) =>
    S.has .globals && typeOk g.value && (g.mutability == .const || S.has .mutGlobal)
  let restricted := cfg.availFuncs.isSome
  let pickedF ← if restricted then availF.filterM (fun _ => G.bool) else pure []
  let pickedF := pickedF.take (min cfg.maxImports cfg.maxFuncs)
  -- tag types (exceptions): function types without results
  let nTags ← if S.has .exn && cfg.maxTags > 0 then count cfg.minTags cfg.maxTags 3 else pure 0
  let tagParams ← G.many (fun _ => do
    let np ← G.choose 3
    G.many (fun _ => G.pick .i32 vts) np) nTags
  -- `--module-shape` imports and `--exports` entities
  let shapeOn := cfg.shapeImports.isSome
  let shape := cfg.shapeImports.getD []
  let req := cfg.reqExports.getD []
  let shapeFT := shape.filterMap fun (_, _, e) => match e with | .func ft => some ft | _ => none
  let shapeTagPs := shape.filterMap fun (_, _, e) => match e with | .tag ps => some ps | _ => none
  let shapeMs := shape.filterMap fun (_, _, e) => match e with | .memory m => some m | _ => none
  let shapeTs := shape.filterMap fun (_, _, e) => match e with | .table t => some t | _ => none
  let reqFT := req.filterMap fun (_, e) => match e with | .func ft => some ft | _ => none
  let reqTagPs := req.filterMap fun (_, e) => match e with | .tag ps => some ps | _ => none
  let reqGs := req.filterMap fun (_, e) => match e with | .global g => some g | _ => none
  let reqMs := req.filterMap fun (_, e) => match e with | .memory m => some m | _ => none
  let reqTs := req.filterMap fun (_, e) => match e with | .table t => some t | _ => none
  let types1 := types0 ++ pickedF.map (·.2.2)
  let baseShapeF := types1.length
  let baseTag := baseShapeF + shapeFT.length
  let allTagPs := tagParams ++ shapeTagPs ++ reqTagPs
  let baseReqF := baseTag + allTagPs.length
  let types := types1 ++ shapeFT ++ allTagPs.map (fun ps => (⟨ps, []⟩ : FuncType)) ++ reqFT
  let nt := types.length
  -- struct and array types (GC), after every function type
  let nGc ← if S.has .gcImm && numTypes S ≠ [] then G.choose 4 else pure 0
  let gcBodies ← G.many (fun _ => do
    let field : G FieldType := do
      let st ← if S.has .intNum && (← G.choose 3) == 0 then
          (do return StorageType.packed (← G.pick .i8 [.i8, .i16]))
        else (do return StorageType.val (← G.pick .i32 (numTypes S)))
      let mu ← if S.has .gcMut then G.bool else pure false
      return ⟨if mu then .var else .const, st⟩
    if (← G.bool) then
      let k ← G.choose 5
      return CompositeType.struct (← G.many (fun _ => field) k)
    else return CompositeType.array (← field)) nGc
  let gc := gcBodies.zipIdx.map fun (b, i) => (nt + i, b)
  -- imports: functions, then immutable globals
  let nfi ← if shapeOn then pure shapeFT.length
    else if restricted then pure pickedF.length else if nt = 0 then pure 0
    else count cfg.minImports (min cfg.maxImports cfg.maxFuncs) 3
  let fimports ← if shapeOn then pure [] else if restricted then
      pure (pickedF.zipIdx.map fun ((mn, n, _), i) =>
        (⟨mn, n, .func (ix (types0.length + i))⟩ : Import))
    else G.many (fun i => do
      return (⟨"m", s!"f{i}", .func (ix (← G.choose nt))⟩ : Import)) nfi
  let ngi ← if shapeOn || restricted || !S.has .globals || numTypes S = [] then pure 0
    else count 0 (min (cfg.maxImports - nfi) cfg.maxGlobals) 2
  let pickedG ← if restricted then availG.filterM (fun _ => G.bool) else pure []
  let pickedG := pickedG.take (min (cfg.maxImports - nfi) cfg.maxGlobals)
  let gimports ← if restricted then
      pure (pickedG.map fun (mn, n, g) => (⟨mn, n, .global g⟩ : Import))
    else G.many (fun i => do
      let t ← G.pick .i32 (numTypes S)
      return (⟨"m", s!"g{i}", .global ⟨.const, t⟩⟩ : Import)) ngi
  -- the `--module-shape` imports, in order (function and tag types placed above)
  let shapeImps : List Import := (shape.foldl (fun (acc, fi, ti) (mn, n, e) =>
      match e with
      | .func _ => (acc ++ [⟨mn, n, .func (ix (baseShapeF + fi))⟩], fi + 1, ti)
      | .tag _ => (acc ++ [⟨mn, n, .tag (ix (baseTag + tagParams.length + ti))⟩], fi, ti + 1)
      | .global g => (acc ++ [⟨mn, n, .global g⟩], fi, ti)
      | .memory m => (acc ++ [⟨mn, n, .memory m⟩], fi, ti)
      | .table t => (acc ++ [⟨mn, n, .table t⟩], fi, ti)) (([] : List Import), 0, 0)).1
  let gimports := if shapeOn then
      shapeImps.filter (fun i => match i.type with | .global _ => true | _ => false)
    else gimports
  let ngi := gimports.length
  -- defined functions (the `--exports` ones last)
  let nf ← if nt = 0 then pure 0 else count cfg.minFuncs (cfg.maxFuncs - nfi) 10
  let ftys0 ← G.many (fun _ => G.choose nt) nf
  let ftys := ftys0 ++ (List.range reqFT.length).map (baseReqF + ·)
  let funcTypes := (if shapeOn then shapeFT else fimports.map (fun i => match i.type with
      | .func x => types.getD x.toNat ⟨[], []⟩
      | _ => ⟨[], []⟩)) ++ ftys.map (types.getD · ⟨[], []⟩)
  -- tables and memories (several only with reference types / multi-memory; under
  -- `--disallow-traps` large enough for the active segments)
  let fixedTabs := shapeTs.length + reqTs.length
  let tabCap := if S.has .refTypes then min cfg.maxTables 3
    else if fixedTabs > 0 then 0 else min cfg.maxTables 1
  let nTab ← if S.has .table && cfg.maxTables > 0 && tabCap > 0 then
      count cfg.minTables tabCap 3 else pure 0
  let tabLo := if cfg.disallowTraps then min 8 cfg.maxTableElements else 0
  let tables ← G.many (fun _ => do
    let tlim ← genLimits tabLo cfg.maxTableElements cfg.tableMaxSizeRequired
    let h : AbsHeapType ← if S.has .refTypes && (← G.choose 3) == 0 then pure .extern
      else pure .func
    return (⟨⟨.i32, tlim, ⟨true, .abstract h⟩⟩, [.refNull (.abstract h)]⟩ : Table)) nTab
  let tables := reqTs.map (fun t => (⟨t, [.refNull t.element.heap]⟩ : Table)) ++ tables
  let tabTypes := (shapeTs ++ tables.map (·.type)).map (·.element)
  let nTab := tabTypes.length
  let funcTabs := indicesWhere (· == ⟨true, .abstract .func⟩) tabTypes
  let fixedMems := shapeMs.length + reqMs.length
  let memCap := if S.has .multiMemory then min cfg.maxMemories 3
    else if fixedMems > 0 then 0 else min cfg.maxMemories 1
  let nMem ← if S.has .memory && S.has .intNum && cfg.maxMemories > 0 && memCap > 0 then
      count cfg.minMemories memCap 3 else pure 0
  let memHi := min cfg.maxMemoryPages 65536
  let memLo := if cfg.disallowTraps then min 1 memHi else 0
  let memories ← G.many (fun _ => do
    let a : AddrType ← if S.has .memory64 && (← G.choose 3) == 0 then pure .i64 else pure .i32
    return (⟨a, ← genLimits memLo memHi cfg.memoryMaxSizeRequired⟩ : MemoryType)) nMem
  let memories := reqMs ++ memories
  let memAddr := (shapeMs ++ memories).map (·.address)
  let nMem := memAddr.length
  let hasMem := nMem > 0
  -- globals
  let ng ← if !S.has .globals || vts = [] then pure 0
    else count cfg.minGlobals (cfg.maxGlobals - ngi) 6
  let globals ← G.many (fun _ => do
    let t ← G.pick .i32 vts
    let mut' ← if S.has .mutGlobal then G.bool else pure false
    return (⟨⟨if mut' then .var else .const, t⟩, ← genInit S t⟩ : Global)) ng
  let reqGlobals ← reqGs.mapM fun g => do return (⟨g, ← genInit S g.value⟩ : Global)
  let globals := globals ++ reqGlobals
  let globalTypes := gimports.map (fun i => match i.type with
      | .global g => g
      | _ => ⟨.const, .i32⟩) ++ globals.map (·.type)
  -- element segments of function indices (the Wasm 1.0 form; with `--disallow-traps` at
  -- offsets inside the table's minimum)
  let nFuncs := funcTypes.length
  let nel ← if !funcTabs.isEmpty && nFuncs > 0 && (!cfg.disallowTraps || tabLo ≥ 8) then
      count cfg.minElementSegments cfg.maxElementSegments 2 else pure 0
  let elems ← G.many (fun _ => do
    let k ← G.choose (min cfg.maxElements 4 + 1)
    let ys ← G.many (fun _ => G.choose nFuncs) k
    let off ← G.choose 4
    let tab ← G.pick 0 funcTabs
    return (⟨⟨false, .abstract .func⟩, ys.map (fun y => [.refFunc (ix y)]),
      .active (ix tab) [.intConst .i32 (BitVec.ofNat 32 off)]⟩ : Elem)) nel
  -- passive (bulk memory) and declarative (reference types) segments
  let nel2 ← if nFuncs > 0 && (S.has .bulkMemory || S.has .refTypes) &&
      cfg.maxElementSegments > nel then G.choose 3 else pure 0
  let elems2 ← G.many (fun _ => do
    let k ← G.choose (min cfg.maxElements 4 + 1)
    let ys ← G.many (fun _ => G.choose nFuncs) k
    let passive ← if S.has .bulkMemory && S.has .refTypes then G.bool
      else pure (S.has .bulkMemory)
    return (⟨⟨false, .abstract .func⟩, ys.map (fun y => [.refFunc (ix y)]),
      if passive then .passive else .declarative⟩ : Elem)) nel2
  let elems := elems ++ elems2
  let declared := elems.flatMap fun e => e.init.filterMap fun
      | [.refFunc y] => some y.toNat
      | _ => none
  -- data segments are drawn before the bodies (`memory.init` and `data.drop` name them)
  let nd ← if hasMem then count cfg.minDataSegments cfg.maxDataSegments 3 else pure 0
  let data ← G.many (fun _ => do
    let k ← G.choose 9
    let bs ← G.many (fun _ => do return (← G.choose 256).toUInt8) k
    let passive ← if S.has .bulkMemory then G.bool else pure false
    let off ← G.choose 64
    let x ← G.choose nMem
    let mode : DataMode := if passive then .passive
      else .active (ix x) [match memAddr.getD x .i32 with
        | .i32 => .intConst .i32 (BitVec.ofNat 32 off)
        | .i64 => .intConst .i64 (BitVec.ofNat 64 off)]
    return (⟨⟨bs.toArray⟩, mode⟩ : Data)) nd
  let ctx : Ctx := { S, funcs := funcTypes, globals := globalTypes, hasMem, declared,
                     types, nMem, nTab, cfg, tabTypes, memAddr,
                     tags := shapeTagPs ++ tagParams ++ reqTagPs, gc,
                     elemTypes := elems.map (·.type), nData := nd }
  -- function bodies
  let funcs ← ftys.zipIdx.mapM fun (ti, i) => do
    let ft := types.getD ti ⟨[], []⟩
    let nl ← if vts.isEmpty then pure 0 else G.choose 4
    let ls ← G.many (fun _ => G.pick .i32 vts) nl
    return (⟨ix ti, ls, ← genBody ctx cfg ft ls (nfi + i)⟩ : Func)
  -- (data segments: drawn above; with `--disallow-traps` the memory has a page, which they
  -- fit in)
  -- start
  let starts := indicesWhere (fun ft => ft.params.isEmpty && ft.results.isEmpty) funcTypes
  let start ← if !starts.isEmpty && cfg.allowStartExport && (← G.choose 4) == 0 then
      (do return some (ix (← G.pick 0 starts))) else pure none
  -- exports: distinct names
  let cands : List ExternIdx :=
    (List.range nFuncs).map (fun i => .func (ix i)) ++
    (List.range globalTypes.length).map (fun i => .global (ix i)) ++
    (List.range nMem).map (fun i => .memory (ix i)) ++ (List.range nTab).map (fun i => .table (ix i)) ++
    (List.range nTags).map (fun i => .tag (ix i))
  let ne ← if cfg.exportEverything then pure cands.length
    else count cfg.minExports (min cfg.maxExports cands.length) 8
  let exports ← G.many (fun i => do
    let x ← if cfg.exportEverything then pure (cands.getD i (.func (ix 0)))
      else G.pick (.func (ix 0)) cands
    let base ← genName
    return (⟨s!"{base}{i}", x⟩ : Export)) ne
  -- `--exports`: exactly the required ones, each naming its new entity
  let reqIdx : List Export := (req.foldl (fun (acc, f, g, m, t, x) (n, e) =>
      match e with
      | .func _ => (acc ++ [⟨n, .func (ix (nfi + nf + f))⟩], f + 1, g, m, t, x)
      | .global _ => (acc ++ [⟨n, .global (ix (ngi + ng + g))⟩], f, g + 1, m, t, x)
      | .memory _ => (acc ++ [⟨n, .memory (ix (shapeMs.length + m))⟩], f, g, m + 1, t, x)
      | .table _ => (acc ++ [⟨n, .table (ix (shapeTs.length + t))⟩], f, g, m, t + 1, x)
      | .tag _ => (acc ++ [⟨n, .tag (ix (shapeTagPs.length + nTags + x))⟩], f, g, m, t, x + 1))
      (([] : List Export), 0, 0, 0, 0, 0)).1
  let exports := if cfg.reqExports.isSome then reqIdx else exports
  let tagDefs := (List.range nTags).map (fun i => (ix (baseTag + i) : TypeIdx)) ++
    (List.range reqTagPs.length).map (fun i => ix (baseTag + tagParams.length + shapeTagPs.length + i))
  return { types := types.map recOf ++ gcBodies.map (fun b => ⟨[⟨true, [], b⟩]⟩),
           imports := if shapeOn then shapeImps else fimports ++ gimports, tags := tagDefs,
           globals, memories, tables, funcs, data, elems, start, exports }

/-- The raw module of a seed. -/
def rawModule (S : FeatureSet) (cfg : Config) (seed : ByteArray) : Module :=
  (genModule S cfg).run' seed

/-- **`wasm-tools smith` at the model `S`**: the raw module, checked against `ValidInW S`
(validity in `S` up to the Wasm 1.0 spellings of tables and function-index segments,
`Norm`). -/
def smith (S : FeatureSet) (cfg : Config) (seed : ByteArray) : Module :=
  checkedGenW S (rawModule S cfg) seed

/-- Did the check accept the raw module (no fallback)? -/
def smithRaw? (S : FeatureSet) (cfg : Config) (seed : ByteArray) : Bool :=
  validInWB S (rawModule S cfg seed)

/-- The bytes of the empty module. -/
def emptyBytes : List UInt8 := Silmaril.Wasm.Binaryen.Exe.header

/-- **The bytes `wasm-tools smith` writes**: the canonical encoding
(`Silmaril.Wasm.Binaryen.Exe.encodeModuleWith?`) of `smith S cfg seed`, with a data count
section only when `S` has bulk memory (the section does not exist in Wasm 1.0; the generator
never emits `memory.init` or `data.drop`, which would need it), or the empty module when the
encoder does not cover it. -/
def smithBytes (S : FeatureSet) (cfg : Config) (seed : ByteArray) : List UInt8 :=
  match Silmaril.Wasm.Binaryen.Exe.encodeModuleWith? (S.has .bulkMemory) (smith S cfg seed) with
  | .ok bs => bs
  | .error _ => emptyBytes

/-! ## `--exports` and `--module-shape` -/

/-- The function type at a type index of a module (`none` unless a plain function type). -/
def funcTypeAt (m : Module) (x : Nat) : Option FuncType :=
  match m.typeDefinitions[x]? with
  | some ⟨_, [], .func ft⟩ => some ft
  | _ => none

/-- The entity type of an import. -/
def importExt (m : Module) (i : Import) : Option Ext :=
  match i.type with
  | .func x => (funcTypeAt m x.toNat).map .func
  | .global g => some (.global g)
  | .memory mt => some (.memory mt)
  | .table tt => some (.table tt)
  | .tag x => (funcTypeAt m x.toNat).map (.tag ·.params)

/-- **The imports of a module with their types** (`--module-shape`). -/
def importsOf (m : Module) : Option (List (String × String × Ext)) :=
  m.imports.mapM fun i => (importExt m i).map (i.moduleName, i.name, ·)

/-- **The exports of a module with their types** (`--exports`, `--module-shape`). -/
def exportsOf (m : Module) : Option (List (String × Ext)) :=
  let fts := m.functionTypes
  let gts := (m.imports.filterMap fun i => match i.type with | .global g => some g | _ => none) ++
    m.globals.map (·.type)
  let mts := (m.imports.filterMap fun i => match i.type with | .memory t => some t | _ => none) ++
    m.memories
  let tts := (m.imports.filterMap fun i => match i.type with | .table t => some t | _ => none) ++
    m.tables.map (·.type)
  let tgs := (m.imports.filterMap fun i => match i.type with | .tag t => some t | _ => none) ++
    m.tags
  m.exports.mapM fun e => (do
    match e.index with
    | .func x => return .func (← funcTypeAt m (← fts[x.toNat]?).toNat)
    | .global x => return .global (← gts[x.toNat]?)
    | .memory x => return .memory (← mts[x.toNat]?)
    | .table x => return .table (← tts[x.toNat]?)
    | .tag x => return .tag (← funcTypeAt m (← tgs[x.toNat]?).toNat).params :
    Option Ext).map (e.name, ·)

/-! ## Custom sections -/

/-- Custom sections for `--generate-custom-sections`: one to three, each with a name of
lowercase letters and a digit, up to 16 bytes of data, and the rank of the section it follows
(`Sections.rank`; never the data count section, which has no name in the text format). Sorted
by anchor, so that `Sections.splice` keeps their order. -/
def genCustoms : G (List (Nat × Sections.Sec)) := do
  let n ← G.range 1 3
  let cs ← G.many (fun i => do
    let a ← G.pick 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13]
    let k ← G.range 1 6
    let letters ← G.many (fun _ => G.pick 'a' "abcdefghijklmnopqrstuvwxyz".toList) k
    let nb := (String.ofList letters ++ toString i).toUTF8.toList
    let len ← G.choose 17
    let data ← G.many (fun _ => do return (← G.choose 256).toUInt8) len
    return (a, (⟨0, ⟨(Sections.encLeb 5 nb.length ++ nb ++ data).toArray⟩⟩ : Sections.Sec))) n
  return cs.mergeSort (fun x y => x.1 ≤ y.1)

/-- The custom sections of a seed: drawn after the module, from the rest of the seed. -/
def rawCustoms (S : FeatureSet) (cfg : Config) (seed : ByteArray) : List (Nat × Sections.Sec) :=
  ((do let _ ← genModule S cfg; genCustoms).run' seed).filter (·.2.isCustom)

/-- **The bytes `wasm-tools smith` writes**, with `--generate-custom-sections`: `smithBytes`
with the generated custom sections put in (`Sections.restore`). -/
def smithBytesC (S : FeatureSet) (cfg : Config) (seed : ByteArray) : List UInt8 :=
  if cfg.customSections then
    (Sections.restore (rawCustoms S cfg seed) ⟨(smithBytes S cfg seed).toArray⟩).data.toList
  else smithBytes S cfg seed

end Silmaril.Wasm.Tools.Gen.Cmd.Smith
