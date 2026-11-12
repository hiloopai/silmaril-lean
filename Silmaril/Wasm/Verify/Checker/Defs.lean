module

public import Silmaril.Wasm.Verify.Reach.Defs
public import Silmaril.Wasm.Verify.Guard.Defs
public import Silmaril.Wasm.Verify.Flow.Defs
public import Silmaril.Wasm.Spec.Verdict.Defs
public import Silmaril.Wasm.Game.Instance.Defs
public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Execution.Core.Exec.Prepare

@[expose] public section

/-!
# An automated verifier for import-call properties of Core 3.0 modules: the checker

`check m φ : Report` decides, conservatively, properties of the import calls of a Core 3.0
module `m` (silmaril-lean's `Module`). It is a pure, computable function: it validates `m`
(`validate?`), instantiates it against fresh host functions (`instantiateOnce?` into
`importStore`, exactly as `Silmaril.Wasm.Game.IsInstance`), and runs a function-reachability
analysis over the instantiated store.

## The analysis

* **Roots** (`rootsOf`): every function address held by the store (globals, tables, element
  segments, struct, array and exception fields: everything a `call_indirect`, `call_ref`,
  `table.get` or `global.get` can ever produce) and the addresses of the function exports.
* **Successors** (`succs`): the functions a Wasm function's body names with `call`,
  `return_call` and `ref.func` (`exprCallees`), resolved through the module's function list.
  `ref.func` targets are treated as callable, so every function whose address escapes into a
  value is reachable; `call_indirect`/`call_ref`/`return_call_ref` targets are values, so they
  are covered by the store roots and the `ref.func` targets.
* **Closure** (`closure`): iterated successors of the roots, `|funcs| + 1` rounds.
* **Certificate check**: the result is accepted only if it is closed (`closedB`: every Wasm
  function in the set belongs to the instance and names only functions in the set), contains
  the roots (`rootsB`), and contains no host function `.host i` (`avoidsB`). Soundness only
  depends on this check, not on how the set was computed.

## Verdicts

`Report` pairs a `Verdict` (`proved`, `refuted`, `unknown`; `Silmaril.Wasm.Spec.Verdict`) with a
`Reason`, and renders as JSON (`Report.toJson`) for a web or command-line service.

* `proved` (`Reason.unreachable G`): the module never calls import `i`, for every profile and
  every environment (`check_sound`, `Silmaril.Wasm.Verify.Check.Thms`). For a module with a start
  function, the analysis runs on the configuration of the specification's `$instantiate`
  (`checkSpec`, `decideSpec`: the reachable set also contains the start function and what the
  segment-initialisation code names, and `cfgInB` checks the invariant of that configuration);
  the result holds of the strategy with the instantiation phase (`check_start_sound`).
* `proved` for assertions (`Reason.guarded G`: guarded calls of `Silmaril.Wasm.Verify.Guard`;
  `Reason.flowGuarded G`: the flow analysis of `Silmaril.Wasm.Verify.Flow`, nonzero facts through
  constants, `if` tests and stable locals, `stableLocals`, `funcOkF`).
* `refuted` (`Reason.counterexample x`): the refuter of `Silmaril.Wasm.Verify.Refute` found an export
  call whose host-free Core run, by silmaril-lean's verified interpreter, reaches a bad call of the
  import (`check_refuted_sound`, `check_assert_refuted_sound`). Only for start-free modules.
* `unknown` otherwise, with the reason: the module does not validate, imports something other
  than functions, fails to instantiate, the import is reachable (`Reason.reaches path`, a call
  path from a root) but no counterexample was found, or (assertions with a start function)
  `startFunction`. Reachability is an over-approximation, so `reaches` is not a refutation.

The checker imports only executable definitions (`Silmaril.Wasm.Game.Instance`,
`Silmaril.Wasm.Spec.Verdict`), not the game semantics it is proved against;
`Silmaril.Wasm.Verify.Check` adds the specification side (`progOf`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Spec (Verdict)

/-! ## Function addresses held by a store -/

/-- The function addresses in a value. -/
def valFuncs : Val → List Nat
  | .ref r => refFuncs r
  | _ => []

/-- The function addresses in a field value. -/
def fieldFuncs : FieldVal → List Nat
  | .val v => valFuncs v
  | _ => []

/-- Every function address held by the store. -/
def storeFuncs {H : Type} (s : Store H) : List Nat :=
  s.globals.flatMap (fun g => valFuncs g.value) ++
  s.tables.flatMap (fun t => t.refs.flatMap refFuncs) ++
  s.elems.flatMap (fun e => e.refs.flatMap refFuncs) ++
  s.structs.flatMap (fun si => si.fields.flatMap fieldFuncs) ++
  s.arrays.flatMap (fun ai => ai.fields.flatMap fieldFuncs) ++
  s.exns.flatMap (fun e => e.fields.flatMap valFuncs)

/-! ## The call graph -/

/-- The functions named by the body of the function at address `a`. -/
def succs (s : Store Nat) (fs : List Nat) (a : Nat) : List Nat :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm code => (exprCallees code.body).filterMap fun x => fs[x]?
    | .host _ => []
  | none => []

/-- One round of the closure: add the successors not yet in the set. -/
def grow (s : Store Nat) (fs : List Nat) (G : List Nat) : List Nat :=
  (G.flatMap (succs s fs)).foldl (fun acc b => if acc.contains b then acc else acc ++ [b]) G

/-- The functions reachable from `roots` (`|funcs| + 1` rounds). -/
def closure (s : Store Nat) (fs : List Nat) (roots : List Nat) : List Nat :=
  (s.funcs.length + 1).repeat (grow s fs) (roots.foldl (fun acc b => if acc.contains b then acc
    else acc ++ [b]) [])

/-- A call path from a root to each reachable function (reversed), breadth first. -/
def paths (s : Store Nat) (fs : List Nat) (roots : List Nat) : List (Nat × List Nat) :=
  (s.funcs.length + 1).repeat (fun ps => ps.foldl (fun acc (a, p) =>
      (succs s fs a).foldl (fun acc b => if acc.any (·.1 == b) then acc else acc ++ [(b, b :: p)])
        acc) ps)
    (roots.map fun a => (a, [a]))

/-- The host functions of import `i`. -/
def isHost (s : Store Nat) (i a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi => match fi.code with
    | .host h => h == i
    | .wasm _ => false
  | none => false

/-! ## The certificate check -/

/-- Every Wasm function in `G` belongs to the instance with function list `fs` and names only
functions in `G`. -/
def closedB (s : Store Nat) (fs : List Nat) (G : List Nat) : Bool :=
  G.all fun a => match s.funcs[a]? with
    | some fi => match fi.code with
      | .wasm code => fi.module.funcs == fs && (exprCallees code.body).all fun x =>
          match fs[x]? with
          | some b => G.contains b
          | none => true
      | .host _ => true
    | none => true

/-- No function in `G` is the host function of import `i`. -/
def avoidsB (s : Store Nat) (G : List Nat) (i : Nat) : Bool := G.all fun a => !isHost s i a

/-- `G` contains the roots. -/
def rootsB (G roots : List Nat) : Bool := roots.all G.contains

/-- The roots of an instance: function addresses held by the store and the function exports. -/
def rootsOf (s : Store Nat) (addrs : List Nat) : List Nat := storeFuncs s ++ addrs

/-! ## Properties, reasons and reports -/

/-- The properties the verifier decides. Imports are named by their index. -/
inductive Property where
  /-- Import `imp` is never called. -/
  | neverCall (imp : Nat)
  /-- The assertion import `imp` (of type `[i32] → …`) is never called with `i32 0`. -/
  | assertNeverFalse (imp : Nat)
  deriving DecidableEq, Repr

/-- Why the verifier reached its verdict. -/
inductive Reason where
  /-- The module does not validate. -/
  | invalidModule
  /-- The module imports something other than a function. -/
  | nonFunctionImport
  /-- The import index is out of range. -/
  | importOutOfRange
  /-- Instantiation failed. -/
  | instantiationFailed
  /-- The module has a start function (outside `wasmSem`); `reaches` records whether the
  import is reachable from the start function or the other roots. -/
  | startFunction (reaches : Bool)
  /-- **Proved**: the reachable functions (store addresses) do not include the import. -/
  | unreachable (reachable : List Nat)
  /-- The import is reachable along this call path (store addresses, from a root). -/
  | reaches (path : List Nat)
  /-- The computed set failed the certificate check. -/
  | notClosed
  /-- **Proved** (assertions): the reachable functions call the assertion only at guarded call
  sites (`i32.const c` with `c ≠ 0` immediately before the `call`). -/
  | guarded (reachable : List Nat)
  /-- The assertion is held by the store or exported (it may be called through a reference). -/
  | escapes
  /-- These reachable functions call the assertion without a guard, or name it with
  `ref.func`/`return_call`. -/
  | unguarded (funcs : List Nat)
  /-- The assertion import does not take exactly one parameter. -/
  | assertArity
  /-- **Proved** (assertions): the reachable functions pass the flow analysis (arguments of the
  assertion are nonzero `i32`s, through constants and stable locals). -/
  | flowGuarded (reachable : List Nat)
  /-- **Refuted**: a concrete counterexample, an export call whose host-free Core run reaches a
  bad call of the import (`Silmaril.Wasm.Verify.Refute`). -/
  | counterexample (cex : Cex)
  /-- The export index is out of range (`checkFrom`). -/
  | exportOutOfRange
  /-- **Proved** (`checkFrom`): the functions callable while the export is active (store
  addresses) do not include the import; `escaping` are the functions whose references may be
  values. -/
  | unreachableFrom (callable escaping : List Nat)
  deriving DecidableEq, Repr

/-- A verdict with its reason. -/
structure Report where
  verdict : Verdict
  reason : Reason
  deriving DecidableEq, Repr

/-- The scalar type of import `i` of a module type. -/
def importType? (mt : CModuleType) (i : Nat) : Option FnType :=
  ((CExternType.funcs mt.imports)[i]?).bind FnType.ofDefType?

/-- A counterexample whose import call satisfies `bad`, if the refuter finds one. -/
def refuteOpt (s : Store Nat) (addrs : List Nat) (imp : Option FnType) (i : Nat)
    (bad : List Val → Bool) : Option Cex :=
  imp.bind fun ft => refuteStore s addrs ft i bad

/-- The decision on an instantiated store without a start function. -/
def decideStore (s : Store Nat) (fs addrs : List Nat) (i : Nat) (imp : Option FnType) : Report :=
  let G := closure s fs (rootsOf s addrs)
  if closedB s fs G && rootsB G (rootsOf s addrs) && avoidsB s G i then
    ⟨.proved, .unreachable G⟩
  else
    match refuteOpt s addrs imp i anyCall with
    | some x => ⟨.refuted, .counterexample x⟩
    | none =>
      match (paths s fs (rootsOf s addrs)).find? (fun (a, _) => isHost s i a) with
      | some (_, p) => ⟨.unknown, .reaches p.reverse⟩
      | none => ⟨.unknown, .notClosed⟩

/-! ## Guarded calls -/

/-- The successors for the assertion analysis: calls of the assertion are not followed. -/
def succsA (s : Store Nat) (fs : List Nat) (i a : Nat) : List Nat :=
  (succs s fs a).filter fun b => !isHost s i b

/-- The functions reachable from `roots` without entering the assertion. -/
def closureA (s : Store Nat) (fs : List Nat) (i : Nat) (roots : List Nat) : List Nat :=
  (s.funcs.length + 1).repeat
    (fun G => (G.flatMap (succsA s fs i)).foldl (fun acc b => if acc.contains b then acc
      else acc ++ [b]) G)
    (roots.foldl (fun acc b => if acc.contains b then acc else acc ++ [b]) [])

/-- The previous instruction is a guard (`i32.const c`, `c ≠ 0`). -/
def isGuard : Option Instr → Bool
  | some (.intConst .i32 c) => c != 0
  | _ => false

/-- Every bad call of the sequence is immediately preceded by a guard. -/
def guardedB (bad : Nat → Bool) (fs : List Nat) : Option Instr → List Instr → Bool
  | _, [] => true
  | prev, i :: is =>
    (match i with
      | .call y =>
        match fs[y.toNat]? with
        | some a => !bad a || isGuard prev
        | none => true
      | _ => true) && guardedB bad fs (some i) is

/-- The function at address `a` passes the guarded-call check. -/
def funcOkA (s : Store Nat) (fs G : List Nat) (i a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm code => fi.module.funcs == fs &&
        (exprRF code.body).all (fun x => match fs[x]? with
          | some b => G.contains b
          | none => true) &&
        (exprCalls code.body).all (fun x => match fs[x]? with
          | some b => G.contains b || isHost s i b
          | none => true) &&
        (code.body :: exprBodies code.body).all (guardedB (isHost s i) fs none)
    | .host _ => true
  | none => true

/-- Every function of `G` passes the guarded-call check. -/
def closedBA (s : Store Nat) (fs G : List Nat) (i : Nat) : Bool := G.all (funcOkA s fs G i)

/-! ## Assertion arguments through locals (`Silmaril.Wasm.Verify.Flow`) -/

/-- The previous instruction is `i32.const c` with `c ≠ 0`. -/
def isNonzeroConst : Option Instr → Bool
  | some (.intConst .i32 c) => c != 0
  | _ => false

mutual

/-- The locals written by `local.set`/`local.tee` without `i32.const c` (`c ≠ 0`) right before,
including nested bodies. -/
def unguardedSets (prev : Option Instr) : List Instr → List Nat
  | [] => []
  | i :: is => instrUnguarded prev i ++ unguardedSets (some i) is

/-- `unguardedSets` of one instruction. -/
def instrUnguarded (prev : Option Instr) : Instr → List Nat
  | .localSet x => if isNonzeroConst prev then [] else [x.toNat]
  | .localTee x => if isNonzeroConst prev then [] else [x.toNat]
  | .block _ b => unguardedSets none b
  | .loop _ b => unguardedSets none b
  | .tryTable _ _ b => unguardedSets none b
  | .if_ _ b₁ b₂ => unguardedSets none b₁ ++ unguardedSets none b₂
  | _ => []

end

mutual

/-- The locals read by `local.get`, including nested bodies. -/
def localsRead : List Instr → List Nat
  | [] => []
  | i :: is => instrRead i ++ localsRead is

/-- `localsRead` of one instruction. -/
def instrRead : Instr → List Nat
  | .localGet x => [x.toNat]
  | .block _ b => localsRead b
  | .loop _ b => localsRead b
  | .tryTable _ _ b => localsRead b
  | .if_ _ b₁ b₂ => localsRead b₁ ++ localsRead b₂
  | _ => []

end

/-- The candidate stable locals of a body: locals read and only written right after a nonzero
`i32` constant. Soundness does not depend on this choice: the flow check `okL` verifies it. -/
def stableLocals (body : List Instr) : List Nat :=
  (localsRead body).filter fun k => !(unguardedSets none body).contains k

/-- The function at address `a` passes the flow check for the assertion `i`. -/
def funcOkF (s : Store Nat) (fs G : List Nat) (i a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm code => fi.module.funcs == fs &&
        (exprRF code.body).all (fun x => match fs[x]? with
          | some b => G.contains b
          | none => true) &&
        (exprCalls code.body).all (fun x => match fs[x]? with
          | some b => G.contains b || isHost s i b
          | none => true) &&
        okL (stableLocals code.body) (isHost s i) fs ⟨[], .other⟩ code.body
    | .host _ => true
  | none => true

/-- Every function of `G` passes the flow check. -/
def closedBF (s : Store Nat) (fs G : List Nat) (i : Nat) : Bool := G.all (funcOkF s fs G i)

/-- The decision for assertions on an instantiated store without a start function: the guarded
calls of `Silmaril.Wasm.Verify.Guard`, else the flow analysis of `Silmaril.Wasm.Verify.Flow`, else a
counterexample search. -/
def decideAssert (s : Store Nat) (fs addrs : List Nat) (i : Nat) (imp : Option FnType) :
    Report :=
  let G := closureA s fs i (rootsOf s addrs)
  if closedBA s fs G i && rootsB G (rootsOf s addrs) && avoidsB s G i then
    ⟨.proved, .guarded G⟩
  else if closedBF s fs G i && rootsB G (rootsOf s addrs) && avoidsB s G i then
    ⟨.proved, .flowGuarded G⟩
  else
    match refuteOpt s addrs imp i falseCall with
    | some x => ⟨.refuted, .counterexample x⟩
    | none =>
      if !avoidsB s G i then ⟨.unknown, .escapes⟩
      else ⟨.unknown, .unguarded (G.filter fun a => !funcOkF s fs G i a)⟩

/-- The assertion import takes exactly one parameter. -/
def arityOne (mt : CModuleType) (i : Nat) : Bool :=
  match (CExternType.funcs mt.imports)[i]? with
  | some d =>
    match FnType.ofDefType? d with
    | some ft => ft.params.length == 1
    | none => false
  | none => false

/-- Whether an extern type is a function. -/
def isFuncImport : CExternType → Bool
  | .func _ => true
  | _ => false

/-! ## Modules with a start function: the specification's instantiation -/

/-- The function addresses held by optional locals. -/
def localsFuncs (ls : List (Option Val)) : List Nat := ls.flatMap fun o => o.toList.flatMap valFuncs

/-- A frame of the module with function list `fs` (or of no module) whose locals hold only
references to functions of `G`. -/
def frameB (G fs : List Nat) (fr : Frame) : Bool :=
  (fr.module.funcs == fs || fr.module.funcs.isEmpty) && (localsFuncs fr.locals).all G.contains

/-- Every function index named by the instruction resolves into `G`. -/
def instrB (G fs : List Nat) (i : Instr) : Bool :=
  (instrCallees i).all fun x => match fs[x]? with
    | some a => G.contains a
    | none => true

/-- The source instructions of administrative code made of source instructions only (as the
configuration of `$instantiate` is). Structural, so that the kernel reduces it. -/
def plainsOf? : List Admin → Option (List Instr)
  | [] => some []
  | .plain i :: rest => (plainsOf? rest).map (i :: ·)
  | _ :: _ => none

/-- **The reachability invariant `CfgIn`, decided** on a configuration whose code is made of
source instructions. -/
def cfgInB (G fs : List Nat) (c : Config Nat) : Bool :=
  (storeFuncs c.store).all G.contains && frameB G fs c.frame &&
    match plainsOf? c.code with
    | some is => is.all (instrB G fs)
    | none => false

/-- The function addresses a configuration names: the targets of its source instructions and the
references in its locals. -/
def configFuncs (fs : List Nat) (c : Config Nat) : List Nat :=
  (match plainsOf? c.code with
    | some is => (exprCallees is).filterMap (fs[·]?)
    | none => []) ++ localsFuncs c.frame.locals

/-- The configuration of the specification's `$instantiate` against fresh host functions
(`Silmaril.Wasm.Game.SpecInst`: segment initialisation, then the call of the start function), and
the export function addresses. -/
def specConfig? (m : Module) (mt : CModuleType) : Option (Config Nat × List Nat) :=
  match prepare? evalConst? (importStore (CExternType.funcs mt.imports)) m (importAddrs mt) with
  | some (c, st) => some (c.withStart st, exportFuncAddrs c.frame.module)
  | none => none

/-- The decision for "never calls import `i`" with the instantiation phase: the reachable set is
grown from the store, the exports **and the configuration of `$instantiate`** (so the start
function and everything it reaches), and the invariant must hold of that configuration. -/
def decideSpec (c₀ : Config Nat) (addrs : List Nat) (i : Nat) : Report :=
  let fs := c₀.frame.module.funcs
  let roots := rootsOf c₀.store addrs ++ configFuncs fs c₀
  let G := closure c₀.store fs roots
  if closedB c₀.store fs G && rootsB G (rootsOf c₀.store addrs) && cfgInB G fs c₀ &&
      avoidsB c₀.store G i then
    ⟨.proved, .unreachable G⟩
  else ⟨.unknown, .startFunction (G.any (isHost c₀.store i))⟩

/-- The verifier with the instantiation phase (used for modules with a start function). -/
def checkSpec (m : Module) (mt : CModuleType) (i : Nat) : Report :=
  match specConfig? m mt with
  | some (c₀, addrs) => decideSpec c₀ addrs i
  | none => ⟨.unknown, .instantiationFailed⟩

/-- **The verifier.** -/
def check (m : Module) : Property → Report
  | .neverCall i =>
    match validate? m with
    | none => ⟨.unknown, .invalidModule⟩
    | some mt =>
      if !(mt.imports.all isFuncImport) then ⟨.unknown, .nonFunctionImport⟩
      else if mt.imports.length ≤ i then ⟨.unknown, .importOutOfRange⟩
      else if m.start.isSome then checkSpec m mt i
      else
        match instantiateOnce? (importStore (CExternType.funcs mt.imports)) m
            ((List.range mt.imports.length).map ExternAddr.func) with
        | none => ⟨.unknown, .instantiationFailed⟩
        | some (s, f, none) =>
          decideStore s f.module.funcs (exportFuncAddrs f.module) i (importType? mt i)
        | some (_, _, some _) => ⟨.unknown, .startFunction true⟩
  | .assertNeverFalse i =>
    match validate? m with
    | none => ⟨.unknown, .invalidModule⟩
    | some mt =>
      if !(mt.imports.all isFuncImport) then ⟨.unknown, .nonFunctionImport⟩
      else if mt.imports.length ≤ i then ⟨.unknown, .importOutOfRange⟩
      else if !arityOne mt i then ⟨.unknown, .assertArity⟩
      else
        match instantiateOnce? (importStore (CExternType.funcs mt.imports)) m
            ((List.range mt.imports.length).map ExternAddr.func) with
        | none => ⟨.unknown, .instantiationFailed⟩
        | some (s, f, none) =>
          decideAssert s f.module.funcs (exportFuncAddrs f.module) i (importType? mt i)
        | some (s, f, some x) =>
          let roots := (f.module.funcs[x.toNat]?).toList ++ rootsOf s (exportFuncAddrs f.module)
          ⟨.unknown, .startFunction ((closure s f.module.funcs roots).any (isHost s i))⟩

/-! ## The instance of a module -/

/-- The instance from its instantiated store and frame: the export types are read off the
store. -/
def instFrom (mt : CModuleType) (imps : List FnType) (s : Store Nat) (f : Frame) :
    Option (CModuleType × ScalarInstance) :=
  ((exportFuncAddrs f.module).mapM fun a =>
      s.funcs[a]?.bind fun fi => FnType.ofDefType? fi.type).map
    fun exps => (mt, ⟨imps, exps, exportFuncAddrs f.module, s⟩)

/-- Instantiate against fresh host functions; start functions are not supported. -/
def instImps (m : Module) (mt : CModuleType) (imps : List FnType) :
    Option (CModuleType × ScalarInstance) :=
  match instantiateOnce? (importStore (CExternType.funcs mt.imports)) m
      ((List.range mt.imports.length).map ExternAddr.func) with
  | some (s, f, none) => instFrom mt imps s f
  | _ => none

/-- The scalar instance of a start-free module with scalar function imports and exports,
computed exactly as `IsInstance` describes it (`isInstance_of_instance?`). -/
def instance? (m : Module) : Option (CModuleType × ScalarInstance) :=
  (validate? m).bind fun mt =>
    if mt.imports.all isFuncImport then
      ((CExternType.funcs mt.imports).mapM FnType.ofDefType?).bind (instImps m mt)
    else none

/-- The instance of a module (an empty instance when `instance?` fails). -/
def instOf (m : Module) : ScalarInstance :=
  ((instance? m).map (·.2)).getD ⟨[], [], [], {}⟩

/-- The scalar instance of a module with scalar function imports and exports **before its
instantiation phase**, and the configuration of `$instantiate`, computed exactly as
`IsSpecInstance` describes them (`isSpecInstance_of_specInstance?`). Modules with a start
function are allowed. -/
def specInstance? (m : Module) : Option (CModuleType × ScalarInstance × Config Nat) :=
  (validate? m).bind fun mt =>
    if mt.imports.all isFuncImport then
      ((CExternType.funcs mt.imports).mapM FnType.ofDefType?).bind fun imps =>
        match prepare? evalConst? (importStore (CExternType.funcs mt.imports)) m
            (importAddrs mt) with
        | some (c, st) =>
          ((exportFuncAddrs c.frame.module).mapM fun a =>
              c.store.funcs[a]?.bind fun fi => FnType.ofDefType? fi.type).map
            fun exps => (mt, ⟨imps, exps, exportFuncAddrs c.frame.module, c.store⟩,
              c.withStart st)
        | none => none
    else none

/-! ## JSON -/

/-- A JSON array of numbers. -/
def jsonNats (l : List Nat) : String := "[" ++ ",".intercalate (l.map toString) ++ "]"

/-- The name of a number type. -/
def numTypeName : NumType → String
  | .int .i32 => "i32"
  | .int .i64 => "i64"
  | .float .f32 => "f32"
  | .float .f64 => "f64"

/-- A value as a JSON object (numbers and vectors by their bits, as unsigned integers). -/
def valJson : Val → String
  | .num ⟨t, b⟩ => "{\"type\":\"" ++ numTypeName t ++ "\",\"bits\":" ++ toString b.toNat ++ "}"
  | .vec b => "{\"type\":\"v128\",\"bits\":" ++ toString b.toNat ++ "}"
  | .ref (.i31 b) => "{\"type\":\"i31\",\"bits\":" ++ toString b.toNat ++ "}"
  | .ref .null => "{\"type\":\"null\"}"
  | .ref _ => "{\"type\":\"ref\"}"

/-- A JSON array of values. -/
def valsJson (vs : List Val) : String := "[" ++ ",".intercalate (vs.map valJson) ++ "]"

/-- The verdict as a JSON string. -/
def verdictJson : Verdict → String
  | .proved => "\"proved\""
  | .refuted => "\"refuted\""
  | .unknown => "\"unknown\""

/-- The reason as a JSON object. -/
def Reason.toJson : Reason → String
  | .invalidModule => "{\"kind\":\"invalidModule\"}"
  | .nonFunctionImport => "{\"kind\":\"nonFunctionImport\"}"
  | .importOutOfRange => "{\"kind\":\"importOutOfRange\"}"
  | .instantiationFailed => "{\"kind\":\"instantiationFailed\"}"
  | .startFunction b => "{\"kind\":\"startFunction\",\"reaches\":" ++ toString b ++ "}"
  | .unreachable G => "{\"kind\":\"unreachable\",\"reachable\":" ++ jsonNats G ++ "}"
  | .reaches p => "{\"kind\":\"reaches\",\"path\":" ++ jsonNats p ++ "}"
  | .notClosed => "{\"kind\":\"notClosed\"}"
  | .guarded G => "{\"kind\":\"guarded\",\"reachable\":" ++ jsonNats G ++ "}"
  | .escapes => "{\"kind\":\"escapes\"}"
  | .unguarded l => "{\"kind\":\"unguarded\",\"funcs\":" ++ jsonNats l ++ "}"
  | .assertArity => "{\"kind\":\"assertArity\"}"
  | .flowGuarded G => "{\"kind\":\"flowGuarded\",\"reachable\":" ++ jsonNats G ++ "}"
  | .counterexample x => "{\"kind\":\"counterexample\",\"export\":" ++ toString x.exp ++
      ",\"args\":" ++ valsJson x.args ++ ",\"callArgs\":" ++ valsJson x.callArgs ++ "}"
  | .exportOutOfRange => "{\"kind\":\"exportOutOfRange\"}"
  | .unreachableFrom G V => "{\"kind\":\"unreachableFrom\",\"callable\":" ++ jsonNats G ++
      ",\"escaping\":" ++ jsonNats V ++ "}"

/-- The report as a JSON object. -/
def Report.toJson (r : Report) : String :=
  "{\"verdict\":" ++ verdictJson r.verdict ++ ",\"reason\":" ++ r.reason.toJson ++ "}"

end Silmaril.Wasm.Verify
