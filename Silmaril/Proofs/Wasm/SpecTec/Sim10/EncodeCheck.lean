module

public import Silmaril.Wasm.SpecTec.Sim10.Encode.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Valid
public meta import Silmaril.Wasm.SpecTec.Sim10.Encode.Defs
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Valid

/-!
# The 1.0 encoding, checked against the wasm-1.0 IL types (build time)

`checkEncoding` reads the vendored wasm-1.0 stream `specs/spectec/wasm-1.0.ast` (the stream of
`Scripts.Wasm10.original`) and runs the IL type checker `Sem.hasTyp` (fuel 1000) on the images of a
corpus that covers **every constructor** of `V1.Instr`, `V1.Execution.Admin` and of the runtime
structure:

* every instruction at every operator and type, with packed loads at the widths the IL's
  `loadop_` side condition allows (`sz < $size(Inn)`), boundary indices (`0`, `2^32-1`) and
  floats of every IEEE shape; each image is checked against `instr` **and** `admininstr`. `STORE`
  is the exception: the checker rejects every `STORE`, for a reason in the checker, not the
  encoding (`knownRejectedInstrs`), exactly as for 2.0;
* every administrative instruction, against `admininstr`;
* configurations whose store has one instance of every kind and whose frame has locals of every
  type, against `config`.

It is compiled code run at elaboration time: a failure fails the build. It is not a kernel
theorem. The wasm-1.0 errata (`Errata/Wasm10.lean`) change `$utf8`, `Module_ok` and binary
grammars, none of which a runtime type mentions except `name` (through `$utf8`), which only export
instances use; the corpus' module instance has no exports.

`checkRejects` makes sure the check is not vacuous: an out-of-range `CONST I32`, a function
instance with a host function, and a packed load at full width are rejected.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.EncodeCheck

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Runtime (FuncInst GlobalInst TableInst MemInst ModuleInst Frame
  ExternVal Addr AddrKind AdminInstr)

/-! ## The corpus -/

/-- An index. -/
def ix {k : IndexKind} (n : Nat) : Idx k := ⟨⟨n % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- Integer types. -/
def intTypes : List IntType := [.i32, .i64]
/-- Float types. -/
def floatTypes : List FloatType := [.f32, .f64]
/-- Value types. -/
def valTypes : List V1.ValType := intTypes.map .int ++ floatTypes.map .float
/-- Signedness. -/
def sxs : List Signedness := [.signed, .unsigned]
/-- Pack sizes. -/
def packs : List V1.PackSize := [.i8, .i16, .i32]
/-- The pack sizes narrower than `t`. -/
def packsAt (t : IntType) : List V1.PackSize := packs.filter fun p => p.width < t.width

/-- Integer unary operators. -/
def intUnOps : List V1.IntUnOp := [.clz, .ctz, .popcnt]
/-- Integer binary operators. -/
def intBinOps : List IntBinOp :=
  [.add, .sub, .mul, .and, .or, .xor, .shl, .rotl, .rotr] ++
    sxs.flatMap fun s => [.div s, .rem s, .shr s]
/-- Integer comparisons. -/
def intRelOps : List IntRelOp := [.eq, .ne] ++ sxs.flatMap fun s => [.lt s, .gt s, .le s, .ge s]
/-- Float unary operators. -/
def floatUnOps : List FloatUnOp := [.abs, .neg, .sqrt, .ceil, .floor, .trunc, .nearest]
/-- Float binary operators. -/
def floatBinOps : List FloatBinOp := [.add, .sub, .mul, .div, .min, .max, .copysign]
/-- Float comparisons. -/
def floatRelOps : List FloatRelOp := [.eq, .ne, .lt, .gt, .le, .ge]
/-- Every conversion. -/
def cvtOps : List V1.ConvertOp :=
  [.wrap, .demote, .promote] ++ sxs.map .extend ++
    floatTypes.flatMap (fun f => intTypes.flatMap fun i => sxs.flatMap fun s =>
      [.trunc f i s, .convert i f s]) ++
    floatTypes.map .reinterpretInt ++ intTypes.map .reinterpretFloat
/-- Memory arguments. -/
def memargs : List V1.MemArg := [⟨0, 0⟩, ⟨3, 4294967295⟩]
/-- Block types. -/
def blockTypes : List V1.BlockType := none :: valTypes.map some

/-- Bit patterns of every IEEE shape. -/
def floatBits : FloatType → List Nat
  | .f32 => [0, 0x80000000, 0x3f800000, 0xbf800000, 1, 0x007fffff, 0x7f7fffff, 0x7f800000,
      0xff800000, 0x7fc00000, 0x7f800001, 0xffffffff]
  | .f64 => [0, 0x8000000000000000, 0x3ff0000000000000, 1, 0x000fffffffffffff,
      0x7fefffffffffffff, 0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000,
      0x7ff0000000000001, 0xffffffffffffffff]

/-- Instructions without operator families. -/
def instrsBase : List V1.Instr :=
  [.nop, .unreachable, .drop, .select, .return_, .br (ix 0), .br (ix 4294967295), .brIf (ix 3),
    .brTable [] (ix 0), .brTable [ix 0, ix 1, ix 4294967295] (ix 2), .call (ix 7),
    .callIndirect (ix 9), .localGet (ix 0), .localSet (ix 1), .localTee (ix 2),
    .globalGet (ix 3), .globalSet (ix 4), .memorySize, .memoryGrow]

/-- Blocks at every block type. -/
def instrsBlocks : List V1.Instr :=
  blockTypes.flatMap fun bt =>
    [.block bt [], .block bt [.nop, .drop], .loop bt [.br (ix 0)],
      .if_ bt [.nop] [], .if_ bt [] [.block bt [.unreachable]]]

/-- Integer instructions at one type. -/
def instrsIntAt (t : IntType) : List V1.Instr :=
  let ops : List V1.Instr :=
    [.intConst t 0, .intConst t 1, .intConst t (BitVec.allOnes _), .intTestOp t .eqz]
  let un : List V1.Instr := intUnOps.map (.intUnOp t)
  let bin : List V1.Instr := intBinOps.map (.intBinOp t)
  let rel : List V1.Instr := intRelOps.map (.intRelOp t)
  let ld : List V1.Instr := memargs.flatMap fun a =>
    .intLoad t none a :: (packsAt t).flatMap fun p => sxs.map fun s => .intLoad t (some (p, s)) a
  [ops, un, bin, rel, ld].flatten

/-- Float instructions at one type. -/
def instrsFloatAt (t : FloatType) : List V1.Instr :=
  let cs : List V1.Instr := (floatBits t).map fun b => .floatConst t (BitVec.ofNat _ b)
  let un : List V1.Instr := floatUnOps.map (.floatUnOp t)
  let bin : List V1.Instr := floatBinOps.map (.floatBinOp t)
  let rel : List V1.Instr := floatRelOps.map (.floatRelOp t)
  let mem : List V1.Instr := memargs.map (.floatLoad t)
  [cs, un, bin, rel, mem].flatten

/-- **Rejected by the checker**: every `STORE`. As in 2.0 (`Sim20.EncodeCheck.knownRejected`),
its `syntax instr` case quantifies `Inn?`, which the payload does not determine and no premise
defines by an equation, and `hasTyp`'s `bindQuants` only solves defining equations. Each is checked
to be rejected, so that the list stays accurate. -/
def knownRejectedInstrs : List V1.Instr :=
  memargs.flatMap fun a =>
    (intTypes.flatMap fun t => .intStore t none a :: (packsAt t).map fun p => .intStore t (some p) a)
      ++ floatTypes.map (.floatStore · a)

/-- The instruction corpus. -/
def instrs : List V1.Instr :=
  instrsBase ++ instrsBlocks ++ intTypes.flatMap instrsIntAt ++ floatTypes.flatMap instrsFloatAt ++
    cvtOps.map .convert

/-- A module instance with something in every field but `EXPORTS` (whose `name` needs `$utf8`). -/
def modInst : ModuleInst :=
  { types := [⟨[], []⟩, ⟨[.int .i32, .float .f64], [.int .i64]⟩], funcs := [⟨0⟩, ⟨3⟩],
    globals := [⟨1⟩], tables := [⟨0⟩], memories := [⟨0⟩] }

/-- A frame with locals of every type. -/
def frame : Frame :=
  { locals := [⟨.int .i32, 7⟩, ⟨.int .i64, 0⟩, ⟨.float .f32, 0x7fc00000⟩,
      ⟨.float .f64, 0x7ff8000000000000⟩], module := modInst }

/-- The administrative corpus. -/
def admins : List V1.Execution.Admin :=
  [.invoke ⟨3⟩, .trap, .label 0 [] [], .label 1 [.nop, .br (ix 1)] [.source (.intConst .i32 1),
    .trap, .source .drop], .frame 0 { module := {} } [],
    .frame 1 frame [.label 1 [] [.source .return_]]] ++ instrs.map .source

/-- A store with one instance of every kind (no host functions). -/
def store : V1.Execution.Store Empty :=
  { funcs := [.wasm ⟨[.int .i32], []⟩ modInst ⟨ix 0, [.float .f32], [.drop]⟩],
    globals := [⟨⟨.int .i64, 3⟩, .var⟩, ⟨⟨.float .f32, 0⟩, .const⟩],
    tables := [⟨[none, some ⟨0⟩], some 10⟩, ⟨[], none⟩],
    memories := [⟨ByteArray.mk #[0, 255, 7], none⟩, ⟨ByteArray.empty, some 2⟩] }

/-- The configuration corpus. -/
def configs : List (V1.Execution.Config Empty) :=
  [⟨{}, { module := {} }, []⟩, ⟨store, frame, [.source .nop]⟩, ⟨store, frame, admins.take 12⟩]

/-! ## The check -/

/-- Read a stream. -/
def readScript (path : String) : IO Script := do
  let contents ← IO.FS.readFile path
  let forms ← match SExp.parseStream contents with
    | .error msg => throw (IO.userError s!"{path} is not an S-expression stream: {msg}")
    | .ok forms => pure forms
  let some script := IL.decodeScript? forms
    | throw (IO.userError s!"{path} is not a printed SpecTec IL script")
  pure script

/-- Check one value against one type, failing loudly. -/
def expectTyped (env : Env) (what : String) (t : Typ) (v : Value) : IO Unit :=
  match hasTyp 1000 env VarEnv.empty t v with
  | .ok true => pure ()
  | .ok false => throw (IO.userError s!"Sim10 encoding: {what} is not of its IL type")
  | .error _ => throw (IO.userError s!"Sim10 encoding: typing {what} failed to evaluate")

/-- **The check.** Returns the number of values checked. -/
def checkEncoding (path : String) : IO Nat := do
  let env := envOfScript (← readScript path)
  let mut n := 0
  for i in instrs do
    expectTyped env s!"{repr i}" (.varT "instr" []) (instrToV i)
    expectTyped env s!"{repr i} (as admininstr)" (.varT "admininstr" []) (instrToV i)
    n := n + 2
  for a in admins do
    expectTyped env "an administrative instruction" (.varT "admininstr" []) (adminToV a)
    n := n + 1
  for c in configs do
    expectTyped env "a configuration" (.varT "config" []) (configV Empty.elim c)
    n := n + 1
  pure n

/-- Values the check must reject, so that it is not vacuous. -/
def checkRejects (path : String) : IO Unit := do
  let env := envOfScript (← readScript path)
  for i in knownRejectedInstrs do
    match hasTyp 1000 env VarEnv.empty (.varT "instr" []) (instrToV i) with
    | .ok true => throw (IO.userError s!"Sim10 encoding check: {repr i} is now accepted")
    | _ => pure ()
  let bad : Value :=
    .case "CONST" (.tuple [Equiv.Execution.caseNilV "I32", Equiv.Execution.pctV (2 ^ 32)])
  match hasTyp 1000 env VarEnv.empty (.varT "instr" []) bad with
  | .ok false => pure ()
  | _ => throw (IO.userError "Sim10 encoding check: an out-of-range CONST was not rejected")
  match hasTyp 1000 env VarEnv.empty (.varT "instr" [])
      (instrToV (.intLoad .i32 (some (.i32, .signed)) ⟨0, 0⟩)) with
  | .ok false => pure ()
  | _ => throw (IO.userError "Sim10 encoding check: a full-width packed load was not rejected")
  let hostStore : V1.Execution.Store String := { funcs := [.host ⟨[], []⟩ "h"] }
  match hasTyp 1000 env VarEnv.empty (.varT "store" []) (storeV id hostStore) with
  | .ok false => pure ()
  | _ => throw (IO.userError "Sim10 encoding check: a host function instance was not rejected")

#eval show IO Unit from do
  let n ← checkEncoding "specs/spectec/wasm-1.0.ast"
  unless 300 ≤ n do throw (IO.userError s!"Sim10 encoding check: corpus too small ({n})")
  checkRejects "specs/spectec/wasm-1.0.ast"

end Silmaril.Wasm.SpecTec.Sim10.EncodeCheck
