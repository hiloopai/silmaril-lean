module

public import Silmaril.Wasm.Wasmi.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare

/-!
# The wasmi divergences observed by the conformance harness

The differential harness (`tools/wasm-conformance`, baseline
`tests/wasm-conformance/known-failures.txt`, findings in `docs/projects/wasm-wasi.md`) runs the official
testsuite against wasmi 0.40.0. Its wasmi failures are of two kinds, both modelled here.

**Signalling NaNs in the rounding operators** (16 failures, `f32.wast`/`f64.wast` lines 2456 to
2518). wasmi 0.40.0 computes `floor`, `ceil`, `trunc` and `nearest` with the host `libm`, which
returns a NaN input unchanged, so a signalling NaN comes back signalling: `f32.floor` of
`-nan:0x200000` (bits `0xffa00000`) returns `0xffa00000`, where the spec allows only arithmetic
NaNs (quiet bit set). A local run of both crates confirms the observation for all 16 cases and
shows that wasmi 2.0.0 quiets the NaN (`wasmi_core` 2.0.0, `value.rs`, `into_quiet_nan`), while
wasmi 0.40.0 does not have the select-fusion bug of `Silmaril.Wasm.Wasmi` (`f 5 1` returns `7`).
The model:

* `IsRound`, `isNaNB`, `wUnOp`: the operators and wasmi 0.40.0's scalar result;
* `Quirk` (`roundNaN`): `t.const x; t.op` steps to `t.const x` for a rounding `op` and a NaN `x`;
* `pending`: the first redex of a code (under values, labels, handlers and frames) is a quirk
  redex;
* `Step`: **the wasmi 0.40.0 step relation**, Core 3.0 everywhere except at a pending quirk
  redex, where only the quirk fires (`Silmaril.Wasm.Atlas.Variant`'s override pattern, not a
  translation: wasmi 0.40.0 executes `floor` with a different numeric function, not a different
  program);
* `obs`: its call observations; `Loose`: Core 3.0 plus the quirk in every context;
* `AnyQuirk`, `LooseAll`: **one loose model for every wasmi version modelled here**, Core plus
  the quirks of wasmi 2.0.0 (`selectEither`) and of wasmi 0.40.0 (`roundNaN`).

**Version gaps** (the other 40 wasmi entries of the baseline that are not text-format or
float-literal issues): wasmi 0.40.0 refuses modules that Wasm 3.0 accepts. The modelled one is
`global.get` of a module-defined global in a constant expression (`global.wast:373-374`,
`data.wast:89-90`; extended constants and GC). Both wasmi 0.40.0 and 2.0.0 reject
`gapMod` with "constant expression required: global.get of locally defined global":

* `constGetOk`, `ConstOk`: every `global.get` of every constant expression reads an imported
  global;
* `instantiate?`: **wasmi's instantiation**, refusing modules that are not `ConstOk`, else the
  spec's `prepare?`;
* `gapMod`: the module of `global.wast:373`.

**The witnesses** (`roundMod`): one module with the eight rounding functions
`f32.floor`, …, `f64.nearest`, each `local.get 0; t.op`, as in the testsuite; `roundStore`, the
spec's allocation of it; `sNaN32`, `sNaN64`: the four signalling inputs of the testsuite;
`nanIns`: all eight NaN inputs the testsuite gives a rounding operator; `posNaN`: the positive
canonical NaN.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.Observed

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas

variable {H : Type}

/-! ## wasmi 0.40.0's rounding operators -/

/-- The rounding operators `ceil`, `floor`, `trunc`, `nearest`. -/
def IsRound : FloatUnOp → Bool
  | .ceil | .floor | .trunc | .nearest => true
  | _ => false

/-- The value is a NaN. -/
def isNaNB : (t : FloatType) → FloatValue t → Bool
  | .f32, x => (asF32 x).isNaN
  | .f64, x => (asF64 x).isNaN

/-- The value is a signalling NaN (quiet bit clear). -/
def isSNaNB : (t : FloatType) → FloatValue t → Bool
  | .f32, x => (asF32 x).isSignalingNaN
  | .f64, x => (asF64 x).isSignalingNaN

/-- **wasmi 0.40.0's scalar unary operator**: a rounding operator returns a NaN input unchanged
(the host `libm`); otherwise the correctly rounded result. -/
def wUnOp (t : FloatType) (op : FloatUnOp) (x : FloatValue t) : FloatValue t :=
  if IsRound op && isNaNB t x then x else floatUnOp t op x

/-- The quirk redex: `t.const x; t.op` with the operator's type equal to the constant's. -/
def redexB : (t : FloatType) → FloatValue t → FloatType → FloatUnOp → Bool
  | .f32, x, .f32, op => IsRound op && isNaNB .f32 x
  | .f64, x, .f64, op => IsRound op && isNaNB .f64 x
  | _, _, _, _ => false

/-- **The quirk `roundNaN`**: a rounding operator on a NaN returns its input. -/
inductive Quirk : Config H → Config H → Prop where
  | roundNaN {s : Store H} {f : Frame} {t : FloatType} {op : FloatUnOp} {x : FloatValue t}
      (hop : IsRound op = true) (hx : isNaNB t x = true) :
      Quirk ⟨s, f, [.plain (.floatConst t x), .plain (.floatUnOp t op)]⟩
        ⟨s, f, [.plain (.floatConst t x)]⟩

mutual
/-- The first redex inside an administrative instruction is a quirk redex. -/
def pendingA : Admin → Bool
  | .label _ _ b => pending b
  | .handler _ _ b => pending b
  | .frame _ _ b => pending b
  | _ => false

/-- **The first redex of a code is a quirk redex**: after the leading values, the code is
`t.const x; t.op` with `redexB`, or a label, handler or frame whose body's first redex is one. -/
def pending : List Admin → Bool
  | [] => false
  | .plain (.floatConst t x) :: .plain (.floatUnOp t' op) :: _ => redexB t x t' op
  | a :: rest =>
    match a.val? with
    | some _ => pending rest
    | none => pendingA a
end

/-- **The wasmi 0.40.0 step relation**: a Core 3.0 step from a configuration whose first redex
is not a quirk redex, or a quirk step in an evaluation context. -/
def Step (P : Profile) (host : HostSemantics H) (c c' : Config H) : Prop :=
  (pending c.code = false ∧ Execution.Core.Step P host c c') ∨ Variant.Ctx Quirk c c'

/-- **wasmi 0.40.0's observations** of a call. -/
def obs (P : Profile) (x : Core.Pt H) (c : Core.Call) : Set (Behaviour Val) :=
  Variant.obsR (Step P) x c

namespace Loose

/-- **The loose step relation of wasmi 0.40.0**: Core 3.0 plus `roundNaN` in every context. -/
abbrev Step (P : Profile) (host : HostSemantics H) : Config H → Config H → Prop :=
  Variant.loose (Execution.Core.Step P host) Quirk

/-- The loose observations of a call. -/
def obs (P : Profile) (x : Core.Pt H) (c : Core.Call) : Set (Behaviour Val) :=
  Variant.obsR (Step P) x c

end Loose

/-! ## One loose model for wasmi 0.40.0 and 2.0.0 -/

/-- The quirks of both modelled wasmi versions. -/
inductive AnyQuirk : Config H → Config H → Prop where
  /-- wasmi 2.0.0's `selectEither` (issue #2046). -/
  | select {c c' : Config H} (h : Wasmi.Loose.Quirk c c') : AnyQuirk c c'
  /-- wasmi 0.40.0's `roundNaN`. -/
  | round {c c' : Config H} (h : Quirk c c') : AnyQuirk c c'

namespace LooseAll

/-- **The loose model of all modelled wasmi versions**: Core 3.0 plus both quirks. -/
abbrev Step (P : Profile) (host : HostSemantics H) : Config H → Config H → Prop :=
  Variant.loose (Execution.Core.Step P host) AnyQuirk

/-- Its observations of a call. -/
def obs (P : Profile) (x : Core.Pt H) (c : Core.Call) : Set (Behaviour Val) :=
  Variant.obsR (Step P) x c

end LooseAll

/-! ## The constant-expression gap -/

/-- The number of imported globals of a module. -/
def importedGlobals (m : Module) : Nat :=
  (m.imports.filter fun i => match i.type with | .global _ => true | _ => false).length

/-- A constant instruction that wasmi accepts: `global.get` only of an imported global. -/
def constGetOk (ng : Nat) : Instr → Bool
  | .globalGet x => decide (x.toNat < ng)
  | _ => true

/-- Every instruction of a constant expression is accepted by wasmi. -/
def exprOk (ng : Nat) (e : Expr) : Bool := e.all (constGetOk ng)

/-- **wasmi's constant-expression check**: global initialisers, table initialisers, element
expressions and offsets, and data offsets read only imported globals. -/
def ConstOk (m : Module) : Bool :=
  let ng := importedGlobals m
  m.globals.all (fun g => exprOk ng g.init) &&
  m.tables.all (fun t => exprOk ng t.init) &&
  m.elems.all (fun e => e.init.all (exprOk ng) &&
    match e.mode with | .active _ o => exprOk ng o | _ => true) &&
  m.data.all (fun d => match d.mode with | .active _ o => exprOk ng o | _ => true)

/-- **wasmi's instantiation** (0.40.0 and 2.0.0): refuse a module that is not `ConstOk`,
otherwise the spec's allocation. -/
def instantiate? (s : Store Empty) (m : Module) : Option (Config Empty × Option FuncIdx) :=
  if ConstOk m then prepare? evalConst? s m [] else none

/-- `i32`. -/
abbrev i32 : ValType := .num (.int .i32)

/-- The module of `global.wast:373`: `(global i32 (i32.const 0)) (global i32 (global.get 0))`. -/
def gapMod : Module where
  globals := [⟨⟨.const, i32⟩, [.intConst .i32 0]⟩, ⟨⟨.const, i32⟩, [.globalGet ⟨0⟩]⟩]

/-! ## The witnesses -/

/-- The value type of a float type. -/
abbrev fty (t : FloatType) : ValType := .num (.float t)

/-- The function `local.get 0; t.op` of type `[t] → [t]` (type index `0` for `f32`, `1` for
`f64`). -/
def roundFunc (t : FloatType) (op : FloatUnOp) : Silmaril.Wasm.Func :=
  ⟨⟨match t with | .f32 => 0 | .f64 => 1⟩, [], [.localGet ⟨0⟩, .floatUnOp t op]⟩

/-- The four rounding operators, in the order of the module's functions. -/
def roundOps : List FloatUnOp := [.floor, .ceil, .trunc, .nearest]

/-- **The witness module**: `f32.floor`, `f32.ceil`, `f32.trunc`, `f32.nearest` at addresses
`0..3`, the `f64` ones at `4..7`. -/
def roundMod : Module where
  types := [⟨[⟨true, [], .func ⟨[fty .f32], [fty .f32]⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[fty .f64], [fty .f64]⟩⟩]⟩]
  funcs := roundOps.map (roundFunc .f32) ++ roundOps.map (roundFunc .f64)

/-- The spec's allocation of `roundMod` into the empty store. -/
def roundPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) roundMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the witness instance. -/
def roundStore : Store Empty := roundPrep.1.store

/-- The witness point: the store, with no host functions. -/
def roundPt : Core.Pt Empty := (roundStore, fun _ _ _ _ => False)

/-- The address of the function computing `op` at type `t`. -/
def roundAddr (t : FloatType) (op : FloatUnOp) : Nat :=
  (match t with | .f32 => 0 | .f64 => 4) + match op with
    | .floor => 0 | .ceil => 1 | .trunc => 2 | _ => 3

/-- The testsuite's signalling NaN inputs: `-nan:0x200000` and `nan:0x200000`. -/
def sNaN32 : List (FloatValue .f32) := [0xffa00000#32, 0x7fa00000#32]

/-- `-nan:0x4000000000000` and `nan:0x4000000000000`. -/
def sNaN64 : List (FloatValue .f64) := [0xfff4000000000000#64, 0x7ff4000000000000#64]

/-- The signalling NaN inputs at a float type. -/
def sNaNs : (t : FloatType) → List (FloatValue t)
  | .f32 => sNaN32
  | .f64 => sNaN64

/-- The testsuite's NaN inputs of the rounding operators (`f32.wast` lines 2455-2458 and
alike): `-nan`, `-nan:0x200000`, `nan`, `nan:0x200000`. -/
def nanIns32 : List (FloatValue .f32) :=
  [0xffc00000#32, 0xffa00000#32, 0x7fc00000#32, 0x7fa00000#32]

/-- The `f64` ones: `-nan`, `-nan:0x4000000000000`, `nan`, `nan:0x4000000000000`. -/
def nanIns64 : List (FloatValue .f64) :=
  [0xfff8000000000000#64, 0xfff4000000000000#64, 0x7ff8000000000000#64, 0x7ff4000000000000#64]

/-- The testsuite's NaN inputs of the rounding operators at a float type. -/
def nanIns : (t : FloatType) → List (FloatValue t)
  | .f32 => nanIns32
  | .f64 => nanIns64

/-- The positive canonical NaN, the result of the spec's deterministic rounding functions on
every NaN. -/
def posNaN : (t : FloatType) → FloatValue t
  | .f32 => 0x7fc00000#32
  | .f64 => 0x7ff8000000000000#64

/-- The float value `x` of type `t`. -/
abbrev fval (t : FloatType) (x : FloatValue t) : Val := .num ⟨.float t, x⟩

end Silmaril.Wasm.Wasmi.Observed
