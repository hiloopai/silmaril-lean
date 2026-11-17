module

public import Silmaril.Project.Defs
public import Silmaril.Wasm.Game.Instance.Defs
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.SingleThreaded.Exec.Run
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Wasm.Game.Signature.Defs
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Execution.MemRep.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# Standard problem shapes: WAST script commands

The commands of a WAST script (the format of the WebAssembly specification test suite), stated
over the Core semantics `Silmaril.Wasm.Execution.Core.Step` and not over an interpreter:

| name | statement |
|---|---|
| `silmaril.shapes.wasm.wast.returns` | `Returns o m pre act vs`: some host-free normal form of `act` returns `vs` |
| `silmaril.shapes.wasm.wast.returns_only` | `ReturnsOnly o m pre act vs`: `Returns`, and every host-free normal form of `act` returns `vs` (no divergence: theorem `ReturnsOnly.always`) |
| `silmaril.shapes.wasm.wast.traps` | `Traps o m pre act`: some host-free normal form of `act` is a trap |
| `silmaril.shapes.wasm.wast.traps_only` | `TrapsOnly o m pre act`: `Traps`, and every host-free normal form of `act` is a trap (no divergence: theorem `TrapsOnly.always`) |
| `silmaril.shapes.wasm.wast.validator_rejects` | `ValidatorRejects b`: silmaril-lean's decoder `decode?` reads the bytes `b` as some module `m`, and silmaril-lean's validator `validate?` rejects `m` (tool-level) |
| `silmaril.shapes.wasm.wast.decoder_rejects` | `DecoderRejects b`: silmaril-lean's decoder `decode?` rejects the bytes `b` (tool-level) |

**Script state.** `m` is the script's current module: it must be valid (`ModuleOk m ⟨[], _⟩`),
have no imports and no start function. Its instance and initial store are those of
`instantiateOnce?` from the empty store (`Instance`, which runs the element and data segment
initialisation). `pre` lists the actions of the script that come before the command, after
`m`, in order: every earlier action, whether it was a bare `invoke`, an `assert_return` or an
`assert_trap`. Each action `invoke name args` calls the function export `name` and runs to a
host-free normal form (`InvokeNF`) whose code is a result (values, a trap or an exception).
The store of that normal form is the next state (`Run`), so stores persist across calls, also
after a trap, as in the reference interpreter. `ScriptAt o m pre mi s` relates the script to
every state it can reach; at `profile o` there is at most one (`ScriptAt.unique`).

A command's claim is therefore relative to the *actual* run of the earlier actions, not to their
expected outcomes: `pre` records only the actions, and the state is whatever their runs leave,
whatever their outcomes were. The expectations of earlier assertions are separate claims (their
own rows). The `Reaches` part of a claim does require every earlier action to end at a result
(values, trap or exception); if one of them had no such normal form, `ScriptAt` would be empty,
`Only` vacuous and `Reaches` false. `register`, named modules, `get` and other modules are not
part of this fragment.

**Profile.** Every step is a Core step `Step (profile o) noHost`: the deterministic profile
(canonical NaNs, `$ND = false`, `memory.grow`/`table.grow` failing exactly when the grow oracle
`o` says so) and no host function. A "normal form" is a configuration with no such step: a
result, a stuck configuration, or a call to a host function. Under `profile o` the machine is
deterministic up to bubbling, so the `…_only` shapes are the meaningful ones; the plain shapes
are the weaker existence claims.

**What the quantifiers cover.** `Only` quantifies over host-free *normal forms* only: "every
normal outcome is `r`". By itself it says nothing about infinite runs. Divergence is excluded
by a theorem, not by the shapes: `Reaches.always` (`….Thms`) derives `Always` (no infinite
host-free run, and every finite run extends to a normal form with the outcome `r`) from the
existence part, by the one-step diamond `Det.DStep.join'` and the fact that the two sides of a
non-trivial peak have smaller code (`Det.DStep.shrink`). So every `returns_only`/`traps_only` row
also excludes divergence at `profile o` (`ScriptHolds.always`).

**Rejections are tool-level.** `ValidatorRejects` and `DecoderRejects` are about silmaril-lean's
functions `decode?` and `validate?`, not about the specification: their titles do not claim that
the module is invalid or the bytes malformed. What follows from them is exactly:

* `ValidatorRejects b` with the validator's completeness `validate?_complete` and the decoder's
  soundness `decode?_sound` and functionality: no module that `b` encodes in silmaril-lean's
  binary grammar `Binary.Core.Encodes` is `ModuleValid` in silmaril-lean's validation relation
  `ModuleOk` (`ValidatorRejects.not_valid`, `….Thms`). The validator's soundness
  `validate?_sound` gives nothing about a rejection. That `Encodes` and `ModuleOk` are the
  specification's binary format and validation rules is a transcription, not a theorem here.
* `DecoderRejects b`: nothing beyond the decoder's output; `decode?` is sound, not complete, so
  a rejection does not exclude that `b` encodes a module.

The NaN payloads of the specification profile `Profile.spec` are covered by the allowed-set
shapes of `Silmaril.Project.Shapes.WasmWastSpec.Defs` (for straight-line numeric functions).
Relaxed SIMD and grow nondeterminism, `assert_exhaustion` (no resource bounds are modelled),
`assert_malformed` on text (no binary exists; silmaril-lean's WAT front end has no completeness
theorem), `assert_unlinkable` and `assert_uninstantiable` have no shape here
(`docs/projects/wasm-wast.md`).

`Silmaril.Project.Shapes.WasmWast.Thms` proves every command of a script at once from one
kernel evaluation (`ScriptHolds.of_kernel`), through silmaril-lean's verified interpreter
(`runInvoke?_sound`, `runInvoke?_stopped`) and determinism (`DStep.join'`). For modules whose
instantiation writes data segments into a memory, the kernel evaluation runs on `KMem` stores
(`scriptKM`, `ScriptHolds.of_kernelKM`); the claims stay the ones above, over `ByteArray`
stores.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWast

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-- A WAST action `(invoke name args)` on the current module. -/
structure Action where
  /-- The export name. -/
  name : String
  /-- The arguments. -/
  args : List Val
  deriving DecidableEq, Repr

/-- The function address of the function export `name` of `mi` (the first export of that
name). -/
def exportFunc? (mi : ModuleInst) (name : String) : Option Nat :=
  match mi.exports.find? (·.name == name) with
  | some ⟨_, .func a⟩ => some a
  | _ => none

/-- `m` is valid, has no imports and no start function, and its instantiation from the empty
store (including segment initialisation) is the store `s` with the module instance `mi`. -/
def Instance (m : Module) (s : Store Nat) (mi : ModuleInst) : Prop :=
  (∃ xtE, ModuleOk m ⟨[], xtE⟩) ∧
    ∃ f : Frame, instantiateOnce? (Game.importStore []) m [] = some (s, f, none) ∧ f.module = mi

/-- `c` is a host-free normal form of `$invoke(s, a, args)` under `profile o`: reachable by host-free
steps and with no host-free step (a result, a stuck configuration or a pending host call). -/
def InvokeNF (o : GrowOracle) (s : Store Nat) (a : Nat) (args : List Val) (c : Config Nat) :
    Prop :=
  Steps (profile o) Det.noHost (invoke s a args) c ∧ ∀ x, ¬ Step (profile o) Det.noHost c x

/-- Running the actions of a script from the store `s` can end with the store `s'`: each action
runs to a host-free normal form whose code is a result, whose store is the next one. -/
inductive Run (o : GrowOracle) (mi : ModuleInst) : Store Nat → List Action → Store Nat → Prop
  | nil (s : Store Nat) : Run o mi s [] s
  | cons {s s' : Store Nat} {act : Action} {acts : List Action} {a : Nat} {c : Config Nat}
      {r : Result} (ha : exportFunc? mi act.name = some a) (hc : InvokeNF o s a act.args c)
      (hr : c.outcome? = some r) (h : Run o mi c.store acts s') :
      Run o mi s (act :: acts) s'

/-- The script made of the module `m` and the actions `pre` can be in the state `(mi, s)`. -/
def ScriptAt (o : GrowOracle) (m : Module) (pre : List Action) (mi : ModuleInst)
    (s : Store Nat) : Prop :=
  ∃ s₀, Instance m s₀ mi ∧ Run o mi s₀ pre s

/-- After the script `m`, `pre`, some host-free normal form of `act` has the outcome `r`. -/
def Reaches (o : GrowOracle) (m : Module) (pre : List Action) (act : Action) (r : Result) :
    Prop :=
  ∃ mi s a c, ScriptAt o m pre mi s ∧ exportFunc? mi act.name = some a ∧
    InvokeNF o s a act.args c ∧ c.outcome? = some r

/-- After the script `m`, `pre`, every host-free normal form of `act` has the outcome `r`. This
quantifies over normal forms only and is vacuous if there are none; it does not exclude infinite
runs (for those, `Always` and `Reaches.always`). -/
def Only (o : GrowOracle) (m : Module) (pre : List Action) (act : Action) (r : Result) :
    Prop :=
  ∀ mi s a c, ScriptAt o m pre mi s → exportFunc? mi act.name = some a →
    InvokeNF o s a act.args c → c.outcome? = some r

/-- **`assert_return`, existence**: after the script `m`, `pre`, some host-free run of `act`
under `profile o` returns `vs`. -/
@[problem "silmaril.shapes.wasm.wast.returns"
  (title := "A WAST action returns given values (some run)")]
def Returns (o : GrowOracle) (m : Module) (pre : List Action) (act : Action) (vs : List Val) :
    Prop :=
  Reaches o m pre act (.values vs)

/-- **`assert_return`**: after the script `m`, `pre`, some host-free run of `act` under
`profile o` returns `vs`, and every host-free normal form of `act` returns `vs` (no normal form
is a trap, other values, a stuck or a host-call state). The statement is about normal forms;
that no run of `act` diverges is the theorem `ReturnsOnly.always`. -/
@[problem "silmaril.shapes.wasm.wast.returns_only"
  (title := "A WAST action returns given values, at every host-free normal form")]
def ReturnsOnly (o : GrowOracle) (m : Module) (pre : List Action) (act : Action)
    (vs : List Val) : Prop :=
  Reaches o m pre act (.values vs) ∧ Only o m pre act (.values vs)

/-- **`assert_trap`, existence**: after the script `m`, `pre`, some host-free run of `act`
under `profile o` traps. -/
@[problem "silmaril.shapes.wasm.wast.traps"
  (title := "A WAST action traps (some run)")]
def Traps (o : GrowOracle) (m : Module) (pre : List Action) (act : Action) : Prop :=
  Reaches o m pre act .trap

/-- **`assert_trap`**: after the script `m`, `pre`, some host-free run of `act` under
`profile o` traps, and every host-free normal form of `act` is a trap. The trap message is not
part of the claim. The statement is about normal forms; that no run of `act` diverges is the
theorem `TrapsOnly.always`. -/
@[problem "silmaril.shapes.wasm.wast.traps_only"
  (title := "A WAST action traps, at every host-free normal form")]
def TrapsOnly (o : GrowOracle) (m : Module) (pre : List Action) (act : Action) : Prop :=
  Reaches o m pre act .trap ∧ Only o m pre act .trap

/-- **Termination and determinacy of the outcome.** After the script `m`, `pre`, no host-free
run of `act` under `profile o` is infinite, and every finite host-free run of `act` extends to a
host-free normal form whose outcome is `r`. Not a problem shape: by
`Reaches.always` (`….Thms`) it follows from `Reaches o m pre act r` at `profile o`, so every
`returns_only`/`traps_only` row has it. -/
def Always (o : GrowOracle) (m : Module) (pre : List Action) (act : Action) (r : Result) :
    Prop :=
  ∀ mi s a, ScriptAt o m pre mi s → exportFunc? mi act.name = some a →
    ¬ Diverges (profile o) Det.noHost (invoke s a act.args) ∧
    ∀ c', Steps (profile o) Det.noHost (invoke s a act.args) c' →
      ∃ c, Steps (profile o) Det.noHost c' c ∧ InvokeNF o s a act.args c ∧ c.outcome? = some r

/-! ## Rejections (tool-level) -/

/-- **`assert_invalid`, tool-level**: silmaril-lean's decoder `decode?` reads the bytes `b` as some
module, and silmaril-lean's validator `validate?` rejects that module. A statement about the two
functions, not about the specification's validity; with `validate?_complete` it gives
`ValidatorRejects.not_valid` (`….Thms`). -/
@[problem "silmaril.shapes.wasm.wast.validator_rejects"
  (title := "silmaril-lean's validator rejects the module that silmaril-lean's decoder reads from given bytes")]
def ValidatorRejects (b : ByteArray) : Prop :=
  ∃ m, Binary.Core.decode? b = some m ∧ validate? m = none

/-- **`assert_malformed` on a binary, tool-level**: silmaril-lean's decoder `decode?` rejects the
bytes `b`. The decoder is sound, not complete, so this does not say that `b` encodes no
module. -/
@[problem "silmaril.shapes.wasm.wast.decoder_rejects"
  (title := "silmaril-lean's decoder rejects given bytes")]
def DecoderRejects (b : ByteArray) : Prop :=
  Binary.Core.decode? b = none

/-- The kernel checker of `ValidatorRejects`: decode, then validate. -/
def validatorRejectsB (b : ByteArray) : Bool :=
  match Binary.Core.decode? b with
  | some m => (validate? m).isNone
  | none => false

/-! ## Scripts -/

/-- The expected outcome of a command. -/
inductive Expect where
  /-- `assert_return` with exact values. -/
  | values (vs : List Val)
  /-- `assert_trap`. -/
  | trap
  deriving DecidableEq, Repr

/-- A command after the module: an action and, for an assertion, its expected outcome (`none`:
a bare `invoke`, or an assertion outside the fragment, kept as an action for the state). -/
structure Cmd where
  act : Action
  expect : Option Expect
  deriving DecidableEq, Repr

/-- The claim of a command, after the actions `pre`. -/
def Cmd.Holds (o : GrowOracle) (m : Module) (pre : List Action) : Cmd → Prop
  | ⟨act, some (.values vs)⟩ => ReturnsOnly o m pre act vs
  | ⟨act, some .trap⟩ => TrapsOnly o m pre act
  | ⟨_, none⟩ => True

/-- The actions of the first `k` commands. -/
def pre (cmds : List Cmd) (k : Nat) : List Action := (cmds.take k).map Cmd.act

/-- Every command of the script `m`, `cmds` holds after the commands before it. -/
def ScriptHolds (o : GrowOracle) (m : Module) (cmds : List Cmd) : Prop :=
  ∀ k (cmd : Cmd), cmds[k]? = some cmd → cmd.Holds o m (pre cmds k)

/-! ## The kernel checker

`scriptK o fuel m cmds` validates `m`, instantiates it, checks that its function exports have
scalar types, then runs every command with `fuel` steps of the kernel-evaluable interpreter
`runInvokeK`, checking that each run stops at a result, that its arguments are typed, and the
expected outcome. `ScriptHolds.of_kernel` (`….Thms`) turns `scriptK … = true` into
`ScriptHolds`. -/

/-- The result an expectation asks for. -/
def Expect.result : Expect → Result
  | .values vs => .values vs
  | .trap => .trap

/-- Numeric arguments of the parameter types `ps`. -/
def argsOk : List Val → List CValType → Bool
  | [], [] => true
  | .num n :: vs, p :: ps => decide (p = .num n.type) && argsOk vs ps
  | _, _ => false

/-- The function `a` of `s` has a function type whose parameters `args` match. Only the
functions of `s` are read, so it is stated over any memory representation `R`. -/
def invokeOkB {R : Type} (s : Store Nat R) (a : Nat) (args : List Val) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.type.funcType? with
    | some (ps, _) => argsOk args ps
    | none => false
  | none => false

/-- Every function export of `mi` has a scalar function type in `s` (any memory representation
`R`: only the functions are read). -/
def exportsScalar {R : Type} (s : Store Nat R) (mi : ModuleInst) : Bool :=
  ((Game.exportFuncAddrs mi).mapM fun a =>
    (s.funcs[a]?).bind fun fi => Game.FnType.ofDefType? fi.type).isSome

/-- Run one action with `fuel` steps: the stopped configuration, if it is a result. -/
noncomputable def actK (o : GrowOracle) (fuel : Nat) (mi : ModuleInst) (s : Store Nat)
    (act : Action) : Option (Config Nat) :=
  match exportFunc? mi act.name with
  | some a =>
    if invokeOkB s a act.args then
      match Silmaril.Wasm.Verify.Kernel.runInvokeK o fuel s a act.args with
      | some (c, true, some _) => some c
      | _ => none
    else none
  | none => none

/-- Run the commands from `s`, checking each expectation. -/
noncomputable def cmdsK (o : GrowOracle) (fuel : Nat) (mi : ModuleInst) :
    Store Nat → List Cmd → Bool
  | _, [] => true
  | s, cmd :: cmds =>
    match actK o fuel mi s cmd.act with
    | some c =>
      (match cmd.expect with
        | some e => decide (c.outcome? = some e.result)
        | none => true) && cmdsK o fuel mi c.store cmds
    | none => false

/-- Validate and instantiate `m`, then run and check the commands. -/
noncomputable def scriptK (o : GrowOracle) (fuel : Nat) (m : Module) (cmds : List Cmd) : Bool :=
  match validate? m with
  | some mt =>
    mt.imports.isEmpty &&
      match instantiateOnce? (Game.importStore []) m [] with
      | some (s, f, none) => exportsScalar s f.module && cmdsK o fuel f.module s cmds
      | _ => false
  | none => false

/-! ## The kernel checker on `KMem`

`scriptK` keeps every memory as a `ByteArray`. The kernel evaluates `ByteArray` operations
through their logical definitions (`ByteArray.copySlice`, `Array.extract`), element by element
over the whole memory, so a module whose instantiation writes a data segment into a 64 KiB
memory is out of its reach. `scriptKM` is `scriptK` with the store over `KMem`
(`Silmaril.Wasm.Execution.MemRep`), a balanced tree of bytes whose reads and writes touch only
the leaves they need: it instantiates `m` from `importStoreKM` with the generic
`instantiateOnce?`, and runs each command with the generic interpreter head step `interpHead o`
under the structural driver `Verify.Kernel.runK`. `scriptK_of_scriptKM` (`….Thms`) shows that
`scriptKM … = true` implies `scriptK … = true`, through the simulation lemmas
`instantiateOnce?_toBytes` and `runI_toBytes`; so `ScriptHolds.of_kernelKM` proves the same
`ScriptHolds` claims, which stay about `ByteArray` stores and `Step (profile o)`. -/

open Silmaril.Wasm.Execution (KMem) in
/-- The empty store with `KMem` memories (it has none): `importStoreKM.toBytes` is
`Game.importStore []`. -/
def importStoreKM : Store Nat KMem := { funcs := [] }

/-- `runInvoke?` at any memory representation, with the structural driver `Verify.Kernel.runK`
over the interpreter's head step `interpHead o`. -/
noncomputable def runInvokeKR {R : Type} [Silmaril.Wasm.Execution.MemRep R] (o : GrowOracle)
    (n : Nat) (s : Store Nat R) (a : Nat) (vs : List Val) :
    Option (Config Nat R × Bool × Option Result) :=
  let r := Silmaril.Wasm.Verify.Kernel.runK (Exec.interpHead o) n (invoke s a vs)
  some (r.1, r.2, r.1.outcome?)

section KM

open Silmaril.Wasm.Execution (KMem)

/-- `actK` on a `KMem` store. -/
noncomputable def actKM (o : GrowOracle) (fuel : Nat) (mi : ModuleInst) (s : Store Nat KMem)
    (act : Action) : Option (Config Nat KMem) :=
  match exportFunc? mi act.name with
  | some a =>
    if invokeOkB s a act.args then
      match runInvokeKR o fuel s a act.args with
      | some (c, true, some _) => some c
      | _ => none
    else none
  | none => none

/-- `cmdsK` on a `KMem` store. -/
noncomputable def cmdsKM (o : GrowOracle) (fuel : Nat) (mi : ModuleInst) :
    Store Nat KMem → List Cmd → Bool
  | _, [] => true
  | s, cmd :: cmds =>
    match actKM o fuel mi s cmd.act with
    | some c =>
      (match cmd.expect with
        | some e => decide (c.outcome? = some e.result)
        | none => true) && cmdsKM o fuel mi c.store cmds
    | none => false

/-- `scriptK` on a `KMem` store: validate and instantiate `m` from `importStoreKM`, then run and
check the commands. -/
noncomputable def scriptKM (o : GrowOracle) (fuel : Nat) (m : Module) (cmds : List Cmd) :
    Bool :=
  match validate? m with
  | some mt =>
    mt.imports.isEmpty &&
      match instantiateOnce? importStoreKM m [] with
      | some (s, f, none) => exportsScalar s f.module && cmdsKM o fuel f.module s cmds
      | _ => false
  | none => false

end KM

end Silmaril.Project.Shapes.WasmWast

end
