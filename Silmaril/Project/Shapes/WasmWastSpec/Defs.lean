module

public import Silmaril.Project.Shapes.WasmWast.Defs
public import Silmaril.Wasm.Execution.StraightLine.Defs

/-!
# Standard problem shapes: WAST commands under the specification profile

The `silmaril.shapes.wasm.wast.returns_only`/`traps_only` shapes (`….WasmWast.Defs`) are stated
at the deterministic profile `profile o` (canonical NaNs). The specification leaves NaN payloads
to the implementation: a float operator returns a *set* of results (`$fadd_N` etc. are
`fN*`), and the profile `Profile.spec nd r` (`nan := .spec`, `Silmaril.Wasm.Numerics.Profile`)
takes every member of it. Under `Profile.spec` a command has many runs, and a WAST expectation is
an *allowed set* per result:

* `nan:canonical` (`ValPat.canonicalNaN t`): a canonical NaN of type `t`, of either sign: the
  exponent field all ones and the payload exactly `2^(M-1)` (`CanonicalBits`);
* `nan:arithmetic` (`ValPat.arithmeticNaN t`): an arithmetic NaN of type `t`, of either sign:
  the exponent field all ones and the payload at least `2^(M-1)`, i.e. the quiet bit set
  (`ArithmeticBits`). Every canonical NaN is arithmetic, not conversely;
* any other expected value (`ValPat.exact v`): exactly the value `v`, compared as bits (so
  `-0 ≠ +0`, and a NaN constant is its exact bit pattern).

`M` is the number of trailing significand bits (23, 52). The definitions are over the bits of
the value, as in the specification's text (`Allowed ps vs`: the results `vs` match the patterns
`ps`, position by position).

The claims are three separate shapes, at `Profile.spec nd r`, over the script semantics of
`….WasmWast.Defs` with `profile o` replaced by `Profile.spec nd r` (`InvokeNFS`, `RunS`,
`ScriptAtS`):

| name | statement |
|---|---|
| `silmaril.shapes.wasm.wast.returns_allowed_exists` | `ReturnsAllowedExists nd r m pre act ps`: **some** host-free run of `act` reaches a normal form returning values in the allowed set `ps` |
| `silmaril.shapes.wasm.wast.returns_allowed_all` | `ReturnsAllowedAll nd r m pre act ps`: `ReturnsAllowedExists`, and **every** host-free normal form of `act` (at every state the earlier actions can leave) returns values in `ps`: no trap, no other values, no stuck or host-call state |
| `silmaril.shapes.wasm.wast.traps_all` | `TrapsAll nd r m pre act`: some host-free run of `act` traps, and every host-free normal form of `act` is a trap |
| `silmaril.shapes.wasm.wast.terminates_all` | `TerminatesAll nd r m pre act`: at every state the earlier actions can leave, **no** host-free run of `act` is infinite, and every finite run extends to a normal form |

`…_all` quantifies over normal forms only; termination is the separate claim `TerminatesAll`
(not a consequence of the others: under `Profile.spec` there is no determinism to derive it
from). `ReturnsAllowedExists` is the weakest claim and is what a run at the deterministic
profile gives by refinement (`Reaches.spec`, `….WasmWastSpec.Thms`).

**The kernel checker** `scriptSK m cmds` validates `m`, checks that it has no element or data
segments and no start function (so the specification's instantiation configuration has no code
and the instantiated state is unique under `Profile.spec`), instantiates it (as `scriptK`) and, for
every command, checks that the exported function is a straight-line numeric function
(`StraightLine.fn?`: `local.get 0 … local.get (k-1); op`), computes the class of the
specification's result set of `op` on the arguments (`numericSet?`: one exact value, the
canonical NaNs of a type, the arithmetic NaNs of a type, or a trap, by the same case split as
`floatUnOpRel`/`floatBinOpRel`/`convertRel`), and checks that the class is contained in the
expectation (`NumSet.sub`). It runs no interpreter: every run under `Profile.spec` is described
by the theorems of `Silmaril.Wasm.Execution.StraightLine.Thms`, and these functions leave the
store unchanged, so every command runs from the instantiated store.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWastSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Numerics Silmaril.Project.Shapes.WasmWast

/-! ## Allowed results -/

/-- The number of exponent bits of a float type. -/
def expBits : FloatType → Nat
  | .f32 => 8
  | .f64 => 11

/-- The number of trailing significand bits `M` of a float type. -/
def sigBits : FloatType → Nat
  | .f32 => 23
  | .f64 => 52

/-- The bits `n` of a float of type `t` are a canonical NaN (either sign): the exponent field is
all ones and the payload is `2^(M-1)`. -/
def CanonicalBits (t : FloatType) (n : Nat) : Prop :=
  n / 2 ^ sigBits t % 2 ^ expBits t = 2 ^ expBits t - 1 ∧ n % 2 ^ sigBits t = 2 ^ (sigBits t - 1)

/-- The bits `n` of a float of type `t` are an arithmetic NaN (either sign): the exponent field
is all ones and the payload is at least `2^(M-1)` (the quiet bit is set). -/
def ArithmeticBits (t : FloatType) (n : Nat) : Prop :=
  n / 2 ^ sigBits t % 2 ^ expBits t = 2 ^ expBits t - 1 ∧ 2 ^ (sigBits t - 1) ≤ n % 2 ^ sigBits t

instance (t : FloatType) (n : Nat) : Decidable (CanonicalBits t n) := by
  unfold CanonicalBits; infer_instance

instance (t : FloatType) (n : Nat) : Decidable (ArithmeticBits t n) := by
  unfold ArithmeticBits; infer_instance

/-- The expectation for one result of an `assert_return`. -/
inductive ValPat where
  /-- Exactly this value, as bits. -/
  | exact (v : Val)
  /-- `nan:canonical`. -/
  | canonicalNaN (t : FloatType)
  /-- `nan:arithmetic`. -/
  | arithmeticNaN (t : FloatType)
  deriving DecidableEq, Repr

/-- The value `w` matches the pattern. -/
def ValPat.Matches : ValPat → Val → Prop
  | .exact v, w => w = v
  | .canonicalNaN t, .num n => n.type = .float t ∧ CanonicalBits t n.bits.toNat
  | .arithmeticNaN t, .num n => n.type = .float t ∧ ArithmeticBits t n.bits.toNat
  | _, _ => False

instance (p : ValPat) (w : Val) : Decidable (p.Matches w) := by
  unfold ValPat.Matches; split <;> infer_instance

/-- The values `vs` are in the allowed set: they match the patterns `ps` position by
position. -/
def Allowed (ps : List ValPat) (vs : List Val) : Prop := List.Forall₂ ValPat.Matches ps vs

/-! ## The script semantics under the specification profile -/

/-- `c` is a host-free normal form of `$invoke(s, a, args)` under `Profile.spec nd r`. -/
def InvokeNFS (nd : Bool) (r : RelaxedChoice) (s : Store Nat) (a : Nat) (args : List Val)
    (c : Config Nat) : Prop :=
  Steps (Profile.spec nd r) Det.noHost (invoke s a args) c ∧
    ∀ x, ¬ Step (Profile.spec nd r) Det.noHost c x

/-- `Run` under `Profile.spec nd r`: each action runs to some host-free normal form whose code is
a result; its store is the next one. -/
inductive RunS (nd : Bool) (r : RelaxedChoice) (mi : ModuleInst) :
    Store Nat → List Action → Store Nat → Prop
  | nil (s : Store Nat) : RunS nd r mi s [] s
  | cons {s s' : Store Nat} {act : Action} {acts : List Action} {a : Nat} {c : Config Nat}
      {res : Result} (ha : exportFunc? mi act.name = some a) (hc : InvokeNFS nd r s a act.args c)
      (hr : c.outcome? = some res) (h : RunS nd r mi c.store acts s') :
      RunS nd r mi s (act :: acts) s'

/-- The script `m`, `pre` can be in the state `(mi, s)` under `Profile.spec nd r` (any of the
runs of the earlier actions). -/
def ScriptAtS (nd : Bool) (r : RelaxedChoice) (m : Module) (pre : List Action) (mi : ModuleInst)
    (s : Store Nat) : Prop :=
  ∃ s₀, Instance (Profile.spec nd r) m s₀ mi ∧ RunS nd r mi s₀ pre s

/-- Some host-free normal form of `act`, at some state of the script, has an outcome in `R`. -/
def ReachesS (nd : Bool) (r : RelaxedChoice) (m : Module) (pre : List Action) (act : Action)
    (R : Result → Prop) : Prop :=
  ∃ mi s a c res, ScriptAtS nd r m pre mi s ∧ exportFunc? mi act.name = some a ∧
    InvokeNFS nd r s a act.args c ∧ c.outcome? = some res ∧ R res

/-- Every host-free normal form of `act`, at every state of the script, has an outcome in `R`. -/
def AllS (nd : Bool) (r : RelaxedChoice) (m : Module) (pre : List Action) (act : Action)
    (R : Result → Prop) : Prop :=
  ∀ mi s a c, ScriptAtS nd r m pre mi s → exportFunc? mi act.name = some a →
    InvokeNFS nd r s a act.args c → ∃ res, c.outcome? = some res ∧ R res

/-- The outcome returns values in the allowed set `ps`. -/
def ReturnsIn (ps : List ValPat) (res : Result) : Prop := ∃ vs, res = .values vs ∧ Allowed ps vs

/-- **`assert_return` under `Profile.spec`, existence**: after the script `m`, `pre`, some
host-free run of `act` under `Profile.spec nd r` returns values in the allowed set `ps`. -/
@[problem "silmaril.shapes.wasm.wast.returns_allowed_exists"
  (title := "A WAST action returns allowed values under the specification profile (some run)")]
def ReturnsAllowedExists (nd : Bool) (r : RelaxedChoice) (m : Module) (pre : List Action)
    (act : Action) (ps : List ValPat) : Prop :=
  ReachesS nd r m pre act (ReturnsIn ps)

/-- **`assert_return` under `Profile.spec`, every normal form**: `ReturnsAllowedExists`, and
every host-free normal form of `act` under `Profile.spec nd r`, at every state the earlier
actions can leave, returns values in the allowed set `ps` (no trap, no other values, no stuck or
host-call state). About normal forms only; termination is `TerminatesAll`. -/
@[problem "silmaril.shapes.wasm.wast.returns_allowed_all"
  (title := "A WAST action returns allowed values under the specification profile, at every host-free normal form")]
def ReturnsAllowedAll (nd : Bool) (r : RelaxedChoice) (m : Module) (pre : List Action)
    (act : Action) (ps : List ValPat) : Prop :=
  ReachesS nd r m pre act (ReturnsIn ps) ∧ AllS nd r m pre act (ReturnsIn ps)

/-- **`assert_trap` under `Profile.spec`**: some host-free run of `act` under
`Profile.spec nd r` traps, and every host-free normal form of `act` is a trap. -/
@[problem "silmaril.shapes.wasm.wast.traps_all"
  (title := "A WAST action traps under the specification profile, at every host-free normal form")]
def TrapsAll (nd : Bool) (r : RelaxedChoice) (m : Module) (pre : List Action) (act : Action) :
    Prop :=
  ReachesS nd r m pre act (· = .trap) ∧ AllS nd r m pre act (· = .trap)

/-- **Termination of every run under `Profile.spec`**: at every state the earlier actions can
leave, no host-free run of `act` under `Profile.spec nd r` is infinite, and every finite run
extends to a host-free normal form. -/
@[problem "silmaril.shapes.wasm.wast.terminates_all"
  (title := "Every run of a WAST action terminates under the specification profile")]
def TerminatesAll (nd : Bool) (r : RelaxedChoice) (m : Module) (pre : List Action)
    (act : Action) : Prop :=
  ∀ mi s a, ScriptAtS nd r m pre mi s → exportFunc? mi act.name = some a →
    ¬ Diverges (Profile.spec nd r) Det.noHost (invoke s a act.args) ∧
    ∀ c', Steps (Profile.spec nd r) Det.noHost (invoke s a act.args) c' →
      ∃ c, Steps (Profile.spec nd r) Det.noHost c' c ∧
        ∀ x, ¬ Step (Profile.spec nd r) Det.noHost c x

/-! ## Scripts -/

/-- The expectation of a command under `Profile.spec`. -/
inductive ExpectS where
  /-- `assert_return` with one pattern per result. -/
  | values (ps : List ValPat)
  /-- `assert_trap`. -/
  | trap
  deriving DecidableEq, Repr

/-- The outcomes an expectation allows. -/
def ExpectS.Out : ExpectS → Result → Prop
  | .values ps, res => ReturnsIn ps res
  | .trap, res => res = .trap

/-- A command: an action and, for an assertion, its expectation (`none`: kept as an action). -/
structure CmdS where
  act : Action
  expect : Option ExpectS
  deriving DecidableEq, Repr

/-- The claims of a command, after the actions `pre`: its expectation at every normal form (with
existence), and termination of every run. -/
def CmdS.Holds (nd : Bool) (r : RelaxedChoice) (m : Module) (pre : List Action) : CmdS → Prop
  | ⟨act, some (.values ps)⟩ => ReturnsAllowedAll nd r m pre act ps ∧ TerminatesAll nd r m pre act
  | ⟨act, some .trap⟩ => TrapsAll nd r m pre act ∧ TerminatesAll nd r m pre act
  | ⟨act, none⟩ => TerminatesAll nd r m pre act

/-- The actions of the first `k` commands. -/
def preS (cmds : List CmdS) (k : Nat) : List Action := (cmds.take k).map CmdS.act

/-- Every command of the script `m`, `cmds` holds after the commands before it. -/
def ScriptHoldsS (nd : Bool) (r : RelaxedChoice) (m : Module) (cmds : List CmdS) : Prop :=
  ∀ k (cmd : CmdS), cmds[k]? = some cmd → cmd.Holds nd r m (preS cmds k)

/-! ## The specification's result sets of scalar numeric instructions -/

/-- A class of results of a numeric step (one instruction list each). -/
inductive NumSet where
  /-- Exactly the value `v`. -/
  | exact (v : Val)
  /-- Canonical NaNs of type `t` (either sign). -/
  | canonical (t : FloatType)
  /-- Arithmetic NaNs of type `t` (either sign). -/
  | arithmetic (t : FloatType)
  /-- A trap. -/
  | trap
  deriving DecidableEq, Repr

/-- `is'` is in the class. -/
def NumSet.Mem : NumSet → List Admin → Prop
  | .exact v, is' => is' = [v.toAdmin]
  | .canonical t, is' => ∃ b, is' = [.plain (.floatConst t b)] ∧ CanonicalBits t b.toNat
  | .arithmetic t, is' => ∃ b, is' = [.plain (.floatConst t b)] ∧ ArithmeticBits t b.toNat
  | .trap, is' => is' = [.trap]

/-- The NaN class of a float operator's result when it is a NaN: canonical if every NaN operand
is canonical (`allCanon`), arithmetic otherwise (`floatUnOpRel`/`floatBinOpRel`). -/
def nanSet (t : FloatType) (allCanon : Bool) : NumSet :=
  if allCanon then .canonical t else .arithmetic t

/-- The class of `floatUnOpRel t op x`. -/
def unSet (t : FloatType) (op : FloatUnOp) (x : BitVec t.width) : NumSet :=
  match op with
  | .abs | .neg => .exact (.num ⟨.float t, floatUnOp t op x⟩)
  | _ =>
    match t, x with
    | .f32, x =>
      if (floatUnOp32 op (asF32 x)).IsNaN then nanSet .f32 (asF32 x).IsNonNaNOrCanonicalNaN
      else .exact (.num ⟨.float .f32, floatUnOp .f32 op x⟩)
    | .f64, x =>
      if (floatUnOp64 op (asF64 x)).IsNaN then nanSet .f64 (asF64 x).IsNonNaNOrCanonicalNaN
      else .exact (.num ⟨.float .f64, floatUnOp .f64 op x⟩)

/-- The class of `floatBinOpRel t op x y`. -/
def binSet (t : FloatType) (op : FloatBinOp) (x y : BitVec t.width) : NumSet :=
  match op with
  | .copysign => .exact (.num ⟨.float t, floatBinOp t op x y⟩)
  | _ =>
    match t, x, y with
    | .f32, x, y =>
      if (floatBinOp32 op (asF32 x) (asF32 y)).IsNaN then
        nanSet .f32 (Silmaril.Numeric.Ieee754.F32.canonicalNaNInputs (asF32 x) (asF32 y))
      else .exact (.num ⟨.float .f32, floatBinOp .f32 op x y⟩)
    | .f64, x, y =>
      if (floatBinOp64 op (asF64 x) (asF64 y)).IsNaN then
        nanSet .f64 (Silmaril.Numeric.Ieee754.F64.canonicalNaNInputs (asF64 x) (asF64 y))
      else .exact (.num ⟨.float .f64, floatBinOp .f64 op x y⟩)

/-- The class of `convertRel op x`. -/
def convSet : (op : ConvertOp) → BitVec op.source.width → NumSet
  | .demote, x =>
    if (asF64 x).toF32.IsNaN then nanSet .f32 (asF64 x).IsNonNaNOrCanonicalNaN
    else .exact (.num ⟨.float .f32, (asF64 x).toF32.bits.toBitVec⟩)
  | .promote, x =>
    if (asF32 x).toF64.IsNaN then nanSet .f64 (asF32 x).IsNonNaNOrCanonicalNaN
    else .exact (.num ⟨.float .f64, (asF32 x).toF64.bits.toBitVec⟩)
  | op, x =>
    match convert op x with
    | .ok z => .exact (.num ⟨op.target, z⟩)
    | .error _ => .trap

/-- The bits of a numeric value at an equal type. -/
def castBits {nt nt' : NumType} (h : nt = nt') (x : BitVec nt.width) : BitVec nt'.width := h ▸ x

/-- The class of the results of `NumericStep (Profile.spec nd r) (vals args ++ [op])`, for the
float operators, float comparisons and conversions (`none` otherwise or on mistyped
arguments). -/
def numericSet? : Instr → List Val → Option NumSet
  | .floatUnOp t op, [.num ⟨nt, x⟩] =>
    if h : nt = .float t then some (unSet t op (castBits h x)) else none
  | .floatBinOp t op, [.num ⟨nt₁, x⟩, .num ⟨nt₂, y⟩] =>
    if h : nt₁ = .float t ∧ nt₂ = .float t then some (binSet t op (castBits h.1 x) (castBits h.2 y)) else none
  | .floatRelOp t op, [.num ⟨nt₁, x⟩, .num ⟨nt₂, y⟩] =>
    if h : nt₁ = .float t ∧ nt₂ = .float t then
      some (.exact (.i32 (floatRelOp t op (castBits h.1 x) (castBits h.2 y))))
    else none
  | .convert op, [.num ⟨nt, x⟩] =>
    if h : nt = op.source then some (convSet op (castBits h x)) else none
  | _, _ => none

/-- The class is contained in the pattern of one result. -/
def NumSet.subPat : NumSet → ValPat → Bool
  | .exact v, p => decide (p.Matches v)
  | .canonical t, .canonicalNaN t' => t == t'
  | .canonical t, .arithmeticNaN t' => t == t'
  | .arithmetic t, .arithmeticNaN t' => t == t'
  | _, _ => false

/-- The class is contained in the expectation. -/
def NumSet.sub (S : NumSet) : ExpectS → Bool
  | .trap => S == .trap
  | .values [p] => S.subPat p
  | .values _ => false

/-! ## The kernel checker -/

/-- One command: the export is a straight-line numeric function whose result class is
contained in the expectation. -/
def cmdSK (s : Store Nat) (mi : ModuleInst) (cmd : CmdS) : Bool :=
  match exportFunc? mi cmd.act.name with
  | some a =>
    match s.funcs[a]? with
    | some fi =>
      match StraightLine.fn? fi cmd.act.args.length with
      | some op =>
        match numericSet? op cmd.act.args with
        | some S =>
          match cmd.expect with
          | some e => S.sub e
          | none => true
        | none => false
      | none => false
    | none => false
  | none => false

/-- Validate `m` (no imports, no element or data segments, no start function, so the
specification's instantiation configuration has no code), instantiate it as the specification
does (`instantiateCfg?`), then check every command from the instantiated store. -/
def scriptSK (m : Module) (cmds : List CmdS) : Bool :=
  match validate? m with
  | some mt =>
    mt.imports.isEmpty && m.elems.isEmpty && m.data.isEmpty && m.start.isNone &&
      match instantiateCfg? (Game.importStore []) m [] with
      | some (c, mi) => c.code.isEmpty && cmds.all (cmdSK c.store mi)
      | none => false
  | none => false

end Silmaril.Project.Shapes.WasmWastSpec

end
