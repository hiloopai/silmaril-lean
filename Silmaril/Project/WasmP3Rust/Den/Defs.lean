module

public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Component.Async.Cabi.Defs
public import Silmaril.Wasi.Versions.P3.Defs
public import Silmaril.Games.LTS.Defs

/-!
# A semantics of async (WASI 0.3) components: callback lifts, async lowers, streams and futures

`den K c : p3World.Model` denotes a component AST `c` of `BinaryP3` (component-model `d095e2f`)
as a strategy of the WASI 0.3 slice `Silmaril.Wasi.Versions.P3.p3World`, given a semantics `K` of
its **core layer** (`CoreExec`): the core instances of the component, run by some core Wasm
semantics. `den` adds what the Component Model puts around core code:

* **the callback lift of `run`** (`canon lift … async (callback cb)`, `definitions.py`
  L2085–2114 at `d095e2f`): the export call enters the lifted core function; each time core code
  returns a packed code (`unpackCallback`), `EXIT` returns the value given to
  `task.return`, `YIELD` re-enters the callback with `EVENT_NONE`, and `WAIT s` calls
  `waitable-set.wait s` on the host and re-enters the callback with the event
  `(code, index, payload)`;
* **lowers** (`canon lower`) of the world's WASI imports, reached through the component's
  instance imports (`wasi:cli/stdout@0.3.0` → `p3World`'s `@0.3.2` names, which have the same
  stdio functions); a result tuple of two `u32`s is stored at the return pointer (the last
  argument), as the Canonical ABI stores more than one flat result;
* **stream and future built-ins** (`stream.new`, `stream.read`, `stream.write`,
  `stream.drop-readable`, `stream.drop-writable`, `future.read`, `future.drop-readable`,
  `waitable-set.new`, `waitable.join`, `waitable-set.wait`): calls of the world's `$root`
  imports (the runtime is part of the host of `p3World`); the bytes of a `stream.write` are read
  from the core layer's memory, the bytes of a `stream.read`, the value of a `future.read` and
  the event of `waitable-set.wait` are stored into it; `stream.new` returns the two ends packed
  in one `i64` (`readable | writable << 32`);
* **built-ins local to the task**: `context.get`/`context.set` (two slots), `task.return` (the
  value `run` returns), `waitable-set.drop` (no host event).

Indices are resolved from the AST (`spaces`): the core function index space (`canon` built-ins
and `alias core export`), the component function and instance spaces, and nested components
(the shim component `wit-component` puts around the `run` export).

## Abstractions (stated, not hidden)

* **Core execution is the parameter `K`.** A `CoreExec` has configurations, entry into a core
  function of the component's core function index space, silent steps, calls out to a core
  function defined by `canon` (with flat arguments), resumption with flat results, returns,
  traps, and access to the memory the `canon` options name (one memory). Shims and `call_indirect`
  through the fixup table are internal to `K`: its calls out are to the `canon`-defined functions
  themselves. The intended `K` is a core Wasm interpreter (silmaril's Core 3.0 machine) run on the
  component's core modules; it is not built here.
* **Each `run` call starts from `K.init`** (`Silmaril.Games.Reduction`: no state persists between
  export calls). A `wasi:cli/command` host calls `run` once.
* **Outside the fragment, `den` traps**: built-ins not in `p3World` (`waitable-set.poll`,
  `future.new`, `future.write`, cancellation, `subtask.*`, `thread.*`, `error-context.*`,
  `backpressure.*`), async lowers of imports, results other than none, one `u32` or a pair of
  `u32`s, and lifts other than an async callback lift of `run`. Theorems about `den` therefore
  say nothing about runs that use them.
* **Completions delivered by `waitable-set.wait` carry no data in `p3World`'s encoding**: a
  `stream.read` or `future.read` that blocked and completes through an event stores nothing.
* Handles are the `u32` values the host answers; the per-instance handle tables of
  `definitions.py` are the host's (as in `p3World`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.Den

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.BinaryP3 (Ast Section Canon)
open Silmaril.Wasm.Component.Binary (CanonOpt ItemSort CoreSort AliasTarget InstanceExpr ExternDesc
  ExternName SortIdx Export Import Alias)
open Silmaril.Wasm.Component.Async.Cabi (unpackCallback)

/-! ## Index spaces -/

/-- An entry of the core function index space. -/
inductive CoreFn where
  /-- Defined by a `canon` built-in or `canon lower`. -/
  | canon (k : Canon)
  /-- `alias core export i n` (a function of a core instance). -/
  | alias (inst : Nat) (name : String)
  /-- Anything else. -/
  | other

/-- An entry of the component function index space. -/
inductive CompFn where
  /-- `canon lift`. -/
  | lift (coreFunc : Nat) (opts : List CanonOpt) (type : Nat)
  /-- `alias export i n`. -/
  | alias (inst : Nat) (name : String)
  /-- An imported function. -/
  | imported (name : String)
  /-- Anything else. -/
  | other

/-- An entry of the component instance index space. -/
inductive CompInst where
  /-- An imported instance. -/
  | imported (name : String)
  /-- Inline exports. -/
  | exports (es : List (ExternName × SortIdx))
  /-- An instance of the component `comp` of the component index space. -/
  | inst (comp : Nat) (args : List (String × SortIdx))
  /-- Anything else. -/
  | other

/-- The index spaces of a component that `den` reads. -/
structure Spaces where
  coreFns : List CoreFn := []
  fns : List CompFn := []
  insts : List CompInst := []
  comps : List Ast := []
  exports : List Export := []

namespace Spaces

/-- A `canon` definition: `lift` defines a component function, the others a core function. -/
def addCanon (S : Spaces) : Canon → Spaces
  | .lift cf os t => { S with fns := S.fns ++ [.lift cf os t] }
  | k => { S with coreFns := S.coreFns ++ [.canon k] }

/-- An alias. -/
def addAlias (S : Spaces) (a : Alias) : Spaces :=
  match a.sort, a.target with
  | .core .func, .coreExport i n => { S with coreFns := S.coreFns ++ [.alias i n] }
  | .core .func, _ => { S with coreFns := S.coreFns ++ [.other] }
  | .func, .export i n => { S with fns := S.fns ++ [.alias i n] }
  | .func, _ => { S with fns := S.fns ++ [.other] }
  | .instance, _ => { S with insts := S.insts ++ [.other] }
  | .component, _ => { S with comps := S.comps ++ [default] }
  | _, _ => S

/-- An import. -/
def addImport (S : Spaces) (i : Import) : Spaces :=
  match i.desc with
  | .func _ => { S with fns := S.fns ++ [.imported i.name.name] }
  | .instance _ => { S with insts := S.insts ++ [.imported i.name.name] }
  | .component _ => { S with comps := S.comps ++ [default] }
  | _ => S

/-- An instance definition. -/
def addInstance (S : Spaces) : InstanceExpr → Spaces
  | .exports es => { S with insts := S.insts ++ [.exports es] }
  | .instantiate c args => { S with insts := S.insts ++ [.inst c args] }

/-- An export: it also defines a new index of its sort (a copy of the exported item). -/
def addExport (S : Spaces) (e : Export) : Spaces :=
  let S := { S with exports := S.exports ++ [e] }
  match e.item.sort with
  | .func => { S with fns := S.fns ++ [S.fns.getD e.item.idx .other] }
  | .instance => { S with insts := S.insts ++ [S.insts.getD e.item.idx .other] }
  | .component => { S with comps := S.comps ++ [S.comps.getD e.item.idx default] }
  | _ => S

/-- A section. -/
def add (S : Spaces) : Section → Spaces
  | .canons xs => xs.foldl addCanon S
  | .aliases xs => xs.foldl addAlias S
  | .imports xs => xs.foldl addImport S
  | .instances xs => xs.foldl addInstance S
  | .exports xs => xs.foldl addExport S
  | .component c => { S with comps := S.comps ++ [c] }
  | _ => S

end Spaces

/-- The index spaces of a component. -/
def spaces (c : Ast) : Spaces := c.sections.foldl Spaces.add {}

/-- The component function a component exports under `name`. -/
def exportedFn (S : Spaces) (name : String) : Option Nat :=
  match S.exports.find? (·.name.name = name) with
  | some e => if e.item.sort = .func then some e.item.idx else none
  | none => none

/-- The component function the instance `i` exports under `name`: an inline export, or an export
of an instantiated component that re-exports one of its imported functions. -/
def instFn (S : Spaces) (i : Nat) (name : String) : Option Nat :=
  match S.insts[i]? with
  | some (.exports es) =>
    match es.find? (·.1.name = name) with
    | some (_, si) => if si.sort = .func then some si.idx else none
    | none => none
  | some (.inst comp args) =>
    match S.comps[comp]? with
    | some nc =>
      let N := spaces nc
      match exportedFn N name with
      | some j =>
        match N.fns[j]? with
        | some (.imported arg) =>
          match args.find? (·.1 = arg) with
          | some (_, si) => if si.sort = .func then some si.idx else none
          | none => none
        | _ => none
      | none => none
    | none => none
  | _ => none

/-- The callback of a list of `canon` options. -/
def callbackOf (os : List CanonOpt) : Option Nat :=
  os.findSome? fun | .callback i => some i | _ => none

/-- **The lift of `run`**: the exported instance `wasi:cli/run@0.3.0`, its function `run`, an
async callback lift `canon lift cf async (callback cb)`; the core functions `(cf, cb)`. -/
def runLift (S : Spaces) : Option (Nat × Nat) :=
  match S.exports.find? (·.name.name = "wasi:cli/run@0.3.0") with
  | some e =>
    if e.item.sort = .instance then
      match instFn S e.item.idx "run" with
      | some j =>
        match S.fns[j]? with
        | some (.lift cf os _) =>
          if CanonOpt.async ∈ os then (callbackOf os).map fun cb => (cf, cb) else none
        | _ => none
      | none => none
    else none
  | none => none

/-! ## The world's imports -/

/-- `stream.new()`. -/
def opNew : P3Op := (⟨cStreamNew, Or.inr (Or.inl rfl)⟩, [])
/-- `stream.write(w, bytes)`. -/
def opWrite (w : Nat) (bs : List (BitVec 8)) : P3Op :=
  (⟨cStreamWrite, Or.inr (Or.inr (Or.inl rfl))⟩, [natV w, bytesV bs])
/-- `stream.read(r, n)`. -/
def opRead (r n : Nat) : P3Op :=
  (⟨cStreamRead, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩, [natV r, natV n])
/-- `stream.drop-readable(r)`. -/
def opDropR (r : Nat) : P3Op :=
  (⟨cStreamDropR, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩, [natV r])
/-- `stream.drop-writable(w)`. -/
def opDropW (w : Nat) : P3Op :=
  (⟨cStreamDropW, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩, [natV w])
/-- `future.read(f)`. -/
def opFRead (f : Nat) : P3Op :=
  (⟨cFutureRead, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩, [natV f])
/-- `future.drop-readable(f)`. -/
def opFDropR (f : Nat) : P3Op :=
  (⟨cFutureDropR, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))⟩,
    [natV f])
/-- `waitable-set.new()`. -/
def opWsNew : P3Op :=
  (⟨cWsNew, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))⟩,
    [])
/-- `waitable.join(w, s)`. -/
def opJoin (w s : Nat) : P3Op :=
  (⟨cJoin, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl rfl)))))))))⟩, [natV w, natV s])
/-- `waitable-set.wait(s)`. -/
def opWait (s : Nat) : P3Op :=
  (⟨cWait, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr rfl)))))))))⟩, [natV s])

/-- `write-via-stream` is an import of `p3World` (`wasiFns3` is read from the vendored WIT;
`wasiFns3_eq` lists it). -/
theorem stdoutWrite3_mem : stdoutWrite3 ∈ p3World.imports := by
  show stdoutWrite3 ∈ wasiFns3 ∪ canonFns
  rw [wasiFns3_eq]
  exact Or.inl (Or.inl rfl)

/-- `read-via-stream` (stdin) is an import of `p3World`. -/
theorem stdinRead3_mem : stdinRead3 ∈ p3World.imports := by
  show stdinRead3 ∈ wasiFns3 ∪ canonFns
  rw [wasiFns3_eq]
  exact Or.inl (Or.inr (Or.inl rfl))

/-- The WASI functions a component reaches through its imported instances: the `@0.3.0`
interfaces the examples import, as `p3World`'s `@0.3.2` functions. -/
def wasiFn (iface fn : String) : Option {f // f ∈ p3World.imports} :=
  if iface = "wasi:cli/stdout@0.3.0" ∧ fn = "write-via-stream" then
    some ⟨stdoutWrite3, stdoutWrite3_mem⟩
  else if iface = "wasi:cli/stdin@0.3.0" ∧ fn = "read-via-stream" then
    some ⟨stdinRead3, stdinRead3_mem⟩
  else none

/-! ## Built-ins -/

/-- What a core function defined by `canon` does in `den`. -/
inductive Builtin where
  | streamNew | streamWrite | streamRead | streamDropR | streamDropW
  | futureRead | futureDropR | wsNew | wsWait | join
  | taskReturn | ctxGet (i : Nat) | ctxSet (i : Nat) | wsDrop
  /-- A sync `canon lower` of a WASI function of the world. -/
  | wasi (f : {f // f ∈ p3World.imports})
  /-- Outside the fragment. -/
  | unsupported
  deriving DecidableEq

/-- The built-in of a `canon` definition. -/
def builtinOf (S : Spaces) : Canon → Builtin
  | .streamNew _ => .streamNew
  | .streamWrite _ _ => .streamWrite
  | .streamRead _ _ => .streamRead
  | .streamDropReadable _ => .streamDropR
  | .streamDropWritable _ => .streamDropW
  | .futureRead _ _ => .futureRead
  | .futureDropReadable _ => .futureDropR
  | .waitableSetNew => .wsNew
  | .waitableSetWait _ => .wsWait
  | .waitableJoin => .join
  | .waitableSetDrop => .wsDrop
  | .taskReturn _ _ => .taskReturn
  | .contextGet _ i => .ctxGet i
  | .contextSet _ i => .ctxSet i
  | .lower f os =>
    if CanonOpt.async ∈ os then .unsupported
    else match S.fns[f]? with
      | some (.alias i n) =>
        match S.insts[i]? with
        | some (.imported iface) => (wasiFn iface n).elim .unsupported .wasi
        | _ => .unsupported
      | _ => .unsupported
  | _ => .unsupported

/-- The built-in of the core function `k`. -/
def builtin (S : Spaces) (k : Nat) : Builtin :=
  match S.coreFns[k]? with
  | some (.canon c) => builtinOf S c
  | _ => .unsupported

/-! ## Core execution -/

/-- **A semantics of the core layer of a component.** See the module documentation. -/
structure CoreExec where
  /-- Configurations (core store, and the running thread when core code runs). -/
  Conf : Type
  /-- After instantiation (start functions run). -/
  init : Conf
  /-- Call the core function `k` (of the component's core function index space) with flat
  arguments; `none` when it is not a function of the core layer. -/
  enter : Conf → Nat → List Nat → Option Conf
  /-- A silent step of core code. -/
  step : Conf → Conf → Prop
  /-- Core code calls the `canon`-defined core function `k` with flat arguments. -/
  callOut : Conf → Nat → List Nat → Prop
  /-- The called function answers with flat results. -/
  resume : Conf → List Nat → Conf
  /-- Core code returns flat results. -/
  ret : Conf → List Nat → Prop
  /-- Core code traps. -/
  trap : Conf → Prop
  /-- The bytes `[p, p + n)` of the memory (`none`: out of bounds). -/
  load : Conf → Nat → Nat → Option (List (BitVec 8))
  /-- Store bytes at `p` (`none`: out of bounds). -/
  store : Conf → Nat → List (BitVec 8) → Option Conf

/-- The four little-endian bytes of a `u32`. -/
def le32 (n : Nat) : List (BitVec 8) :=
  [BitVec.ofNat 8 n, BitVec.ofNat 8 (n / 256), BitVec.ofNat 8 (n / 65536),
    BitVec.ofNat 8 (n / 16777216)]

/-- The `i64` of `stream.new`: `readable | writable << 32`. -/
def packEnds (r w : Nat) : Nat := r + w * 2 ^ 32

variable (K : CoreExec)

/-- **A forwarded built-in**: the world import it calls, and how the answer resumes core code
(`none`: a trap, for an answer of the wrong shape or a store out of bounds). `none` when the
built-in is not forwarded or its arguments have the wrong shape. -/
def forward (B : Builtin) (args : List Nat) (x : K.Conf) :
    Option (P3Op × (Option (List Val) → Option K.Conf)) :=
  match B, args with
  | .streamNew, [] => some (opNew, fun
      | some [rv, wv] => match natOf rv, natOf wv with
        | some r, some w => some (K.resume x [packEnds r w])
        | _, _ => none
      | _ => none)
  | .streamWrite, [w, p, n] =>
    (K.load x p n).map fun bs => (opWrite w bs, fun
      | some [pv] => (natOf pv).map fun c => K.resume x [c]
      | _ => none)
  | .streamRead, [r, p, n] => some (opRead r n, fun
      | some [pv, items] =>
        match natOf pv with
        | some c => (K.store x p (bytesOf items)).map fun x' => K.resume x' [c]
        | none => none
      | _ => none)
  | .streamDropR, [r] => some (opDropR r, fun | some [] => some (K.resume x []) | _ => none)
  | .streamDropW, [w] => some (opDropW w, fun | some [] => some (K.resume x []) | _ => none)
  | .futureRead, [f, p] => some (opFRead f, fun
      | some [pv] => (natOf pv).map fun c => K.resume x [c]
      | some [pv, v] =>
        match natOf pv with
        | some c => (K.store x p [if v matches .variant 0 none then 0 else 1]).map
            fun x' => K.resume x' [c]
        | none => none
      | _ => none)
  | .futureDropR, [f] => some (opFDropR f, fun | some [] => some (K.resume x []) | _ => none)
  | .wsNew, [] => some (opWsNew, fun
      | some [sv] => (natOf sv).map fun s => K.resume x [s]
      | _ => none)
  | .join, [w, s] => some (opJoin w s, fun | some [] => some (K.resume x []) | _ => none)
  | .wsWait, [s, p] => some (opWait s, fun
      | some [cv, iv, pv] =>
        match natOf cv, natOf iv, natOf pv with
        | some c, some i, some q => (K.store x p (le32 i ++ le32 q)).map fun x' => K.resume x' [c]
        | _, _, _ => none
      | _ => none)
  | .wasi f, args => some ((f, args.map natV), fun
      | some [] => some (K.resume x [])
      | some [.record [a, b]] =>
        match natOf a, natOf b, args.getLast? with
        | some a', some b', some p => (K.store x p (le32 a' ++ le32 b')).map fun x' => K.resume x' []
        | _, _, _ => none
      | some [v] => (natOf v).map fun n => K.resume x [n]
      | _ => none)
  | _, _ => none

/-! ## The callback driver -/

/-- What the lifted task is doing. -/
inductive Mode where
  /-- Core code runs. -/
  | run
  /-- Core code returned `WAIT s`: the driver calls `waitable-set.wait s`. -/
  | wait (s : Nat)
  /-- Core code returned `EXIT`. -/
  | exit
  /-- Trapped. -/
  | trap

/-- A configuration of `den`: the core layer, the driver's mode, the two context slots, and the
values given to `task.return`. -/
structure DConf where
  core : K.Conf
  mode : Mode := .run
  ctx : Nat × Nat := (0, 0)
  result : Option (List Nat) := none

variable {K}

/-- Trap. -/
def DConf.trapped (d : DConf K) : DConf K := { d with mode := .trap }

/-- A built-in local to the task (`some`), with its effect (`none` inside: a trap). -/
def internal (B : Builtin) (args : List Nat) (d : DConf K) : Option (Option (DConf K)) :=
  match B, args with
  | .ctxGet 0, [] => some (some { d with core := K.resume d.core [d.ctx.1] })
  | .ctxGet 1, [] => some (some { d with core := K.resume d.core [d.ctx.2] })
  | .ctxSet 0, [v] => some (some { d with core := K.resume d.core [], ctx := (v, d.ctx.2) })
  | .ctxSet 1, [v] => some (some { d with core := K.resume d.core [], ctx := (d.ctx.1, v) })
  | .taskReturn, vs =>
    match d.result with
    | none => some (some { d with core := K.resume d.core [], result := some vs })
    | some _ => some none
  | .wsDrop, [_] => some (some { d with core := K.resume d.core [] })
  | _, _ => none

/-- Re-enter the callback `cb` with an event. -/
def reenter (cb : Nat) (d : DConf K) (ev : List Nat) : DConf K :=
  match K.enter d.core cb ev with
  | some y => { d with core := y, mode := .run }
  | none => d.trapped

/-- The value `run` returns: `result<_, _>` from the flat value given to `task.return`. -/
def runResult : Option (List Nat) → Option (List Val)
  | some [0] => some [okV none]
  | some [1] => some [errV none]
  | _ => none

/-- How the answer to a forwarded built-in resumes core code (`none`: a trap). -/
def contWith (d : DConf K) (kont : Option (List Val) → Option K.Conf) (n : Option (List Val)) :
    DConf K :=
  match kont n with
  | some y => { d with core := y }
  | none => d.trapped

/-- How the driver continues after `waitable-set.wait` answered `(code, index, payload)`: it
re-enters the callback `cb` with the event. -/
def afterWait (cb : Nat) (d : DConf K) (n : Option (List Val)) : DConf K :=
  match n with
  | some [cv, iv, pv] =>
    match natOf cv, natOf iv, natOf pv with
    | some c, some i, some q => reenter cb d [c, i, q]
    | _, _, _ => d.trapped
  | _ => d.trapped

variable (K)

/-- Silent steps of `den` (the lifted function's core function is `cb`'s partner; `S` the
index spaces). -/
inductive DStep (S : Spaces) (cb : Nat) : DConf K → DConf K → Prop
  /-- A silent core step. -/
  | core {d : DConf K} {y : K.Conf} : d.mode = .run → K.step d.core y →
      DStep S cb d { d with core := y }
  /-- A built-in local to the task. -/
  | internal {d d' : DConf K} {k : Nat} {args : List Nat} : d.mode = .run →
      K.callOut d.core k args → internal (builtin S k) args d = some (some d') →
      DStep S cb d d'
  /-- A built-in that traps, or is outside the fragment. -/
  | bad {d : DConf K} {k : Nat} {args : List Nat} : d.mode = .run → K.callOut d.core k args →
      internal (builtin S k) args d = some none ∨
        (internal (builtin S k) args d = none ∧ forward K (builtin S k) args d.core = none) →
      DStep S cb d d.trapped
  /-- Core code returned `YIELD`: re-enter the callback with `EVENT_NONE`. -/
  | yield {d : DConf K} {p : Nat} {s : Nat} : d.mode = .run → K.ret d.core [p] →
      unpackCallback p = .ok (.yield, s) → DStep S cb d (reenter cb d [0, 0, 0])
  /-- Core code returned `WAIT s`. -/
  | wait {d : DConf K} {p s : Nat} : d.mode = .run → K.ret d.core [p] →
      unpackCallback p = .ok (.wait, s) → DStep S cb d { d with mode := .wait s }
  /-- Core code returned `EXIT`. -/
  | exit {d : DConf K} {p s : Nat} : d.mode = .run → K.ret d.core [p] →
      unpackCallback p = .ok (.exit, s) → DStep S cb d { d with mode := .exit }
  /-- Core code returned something else (a packed code above `WAIT`, or not one value). -/
  | badRet {d : DConf K} {vs : List Nat} : d.mode = .run → K.ret d.core vs →
      (∀ p, vs = [p] → ∃ e, unpackCallback p = .error e) → DStep S cb d d.trapped
  /-- Core code trapped. -/
  | trap {d : DConf K} : d.mode = .run → K.trap d.core → DStep S cb d d.trapped

/-- Calls of `den` to the world. -/
inductive DCall (S : Spaces) (cb : Nat) :
    DConf K → (m : P3Op) → (Option (List Val) → DConf K) → Prop
  /-- A forwarded built-in. -/
  | fwd {d : DConf K} {k : Nat} {args : List Nat} {m : P3Op}
      {kont : Option (List Val) → Option K.Conf} : d.mode = .run → K.callOut d.core k args →
      internal (builtin S k) args d = none → forward K (builtin S k) args d.core = some (m, kont) →
      DCall S cb d m (contWith d kont)
  /-- The driver waits on the set `s`, then re-enters the callback with the event. -/
  | wait {d : DConf K} {s : Nat} : d.mode = .wait s → DCall S cb d (opWait s) (afterWait cb d)

/-- Returns of `den`. -/
inductive DDone : DConf K → Option (List Val) → Prop
  | exit {d : DConf K} : d.mode = .exit → DDone d (runResult d.result)
  | trap {d : DConf K} : d.mode = .trap → DDone d none

/-- The first configuration of a `run` call. -/
def start (S : Spaces) : DConf K :=
  match runLift S with
  | some (cf, _) =>
    match K.enter K.init cf [] with
    | some x => { core := x }
    | none => { core := K.init, mode := .trap }
  | none => { core := K.init, mode := .trap }

/-- The callback of the lift of `run` (`0` when there is none; `start` then traps). -/
def cbOf (S : Spaces) : Nat := ((runLift S).map (·.2)).getD 0

/-- **The reduction semantics of an async component**, question by question. -/
def red (c : Ast) : Reduction (nsig p3World.imports) (nsig p3World.exports) where
  Conf _ := DConf K
  start _ := start K (spaces c)
  step := DStep K (spaces c) (cbOf (spaces c))
  call := DCall K (spaces c) (cbOf (spaces c))
  done := DDone K

/-- The denotation of an async component with the core layer semantics `K`. -/
def denWith (c : Ast) : p3World.Model := Strategy.ofLTS (red K c).toLTS

/-- **The denotation of async components**, given a semantics `K c` of the core layer of each
component `c` (`Ks c`). -/
def den (Ks : Ast → CoreExec) (c : Ast) : p3World.Model := denWith (Ks c) c

end Silmaril.Project.WasmP3Rust.Den

end
