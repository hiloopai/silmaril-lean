module

public import Silmaril.Wasm.JcoTool.Tool.Defs
public import Silmaril.Wasm.Component.Streams.Proc.Defs

/-!
# The meaning of `wasm-jco`'s stream outputs, in the `Proc` model of the streams track

`Silmaril.Wasm.Component.Streams.Proc` proves a pipeline `producer → transformer → consumer`
correct when its three components are step functions over the stream built-ins of
`Silmaril.Wasm.Component.Async` (`pipeline_correct`). A stream transformer component that
`wasm-jco` builds is a core module, lifted async, whose built-ins are the canonical ones. This
module relates the two:

* **Operation kinds** (`OpKind`): the `Async` operations a `Proc` transformer performs, and
  for each output built-in (`Builtin`) and each planned request (`New.Req`) the kind it
  realizes (`builtinKind`, `reqKind`; `Op.kind` for the model's operations).
* **The shape check** `xfShape p name`: export `name` of the plan is an async
  `stream<T> → stream<U>`, implemented by an async lift, and the module imports, at their
  canonical types (checked by the plan), a built-in of every kind a `Proc` transformer needs:
  `stream.read` and `stream.drop-readable` on the parameter's stream type, `stream.new`,
  `stream.write` and `stream.drop-writable` on the result's, `waitable-set.new`,
  `waitable.join` and `task.return`, and `waitable-set.wait` in the stackful ABI (in the
  callback ABI the runtime waits, on the callback's `WAIT` code).
* **Implementations** (`Impl σ T N`): any machine `M` with a step function over the shared
  `Async` store, related to the transformer `tStep T N` by a forward simulation `R` with
  stuttering (each machine step is a step of `tStep` with the same effect on the store, or a
  local step that leaves the store unchanged), and finished only where `tStep` is.
  `SysM`, `StepM`, `ReachM` are the pipeline with the transformer replaced by the machine.

`Silmaril.Wasm.JcoTool.StreamSem.Thms` proves that every such implementation is correct and safe
in every interleaving (`impl_correct`, `impl_safe`), and states the meaning of a
`wasm-jco new` output at the tool's entry point (`newWith_stream_semantics`): the bytes are
read back with their built-ins, the export has the shape of a `Proc` transformer, and a
pipeline through any implementation of the export by a machine simulating `tStep T N` computes
`T.run` of its input. **Not proved**: that the core module's export, run under a Wasm
semantics with the canonical built-ins, is such a machine (no executable semantics of core
modules with async built-ins is connected here); the stream components of
`tools/wasm-jco/tests` are tested under wasmtime instead.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.StreamSem

open Silmaril.Wasm.Wit.Binary (Ty Func)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Op)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Proc

/-! ## Operation kinds -/

/-- The kinds of `Async` operations of the stream pipeline. -/
inductive OpKind where
  | streamNew | streamRead | streamWrite | dropReadable | dropWritable | setNew | join | wait
  deriving Repr, DecidableEq, Inhabited

/-- The kind of an `Async` operation. -/
def Op.kind : Op → Option OpKind
  | .streamNew => some .streamNew
  | .streamRead _ _ => some .streamRead
  | .streamWrite _ _ => some .streamWrite
  | .streamDropR _ => some .dropReadable
  | .streamDropW _ => some .dropWritable
  | .wsNew => some .setNew
  | .join _ _ => some .join
  | .wait _ => some .wait
  | _ => none

/-- The kind of an output built-in, with the stream type it operates on. -/
def builtinKind : Builtin → Option (OpKind × Option Nat)
  | .streamNew t => some (.streamNew, some t)
  | .streamRead t _ => some (.streamRead, some t)
  | .streamWrite t _ => some (.streamWrite, some t)
  | .streamDropReadable t => some (.dropReadable, some t)
  | .streamDropWritable t => some (.dropWritable, some t)
  | .waitableSetNew => some (.setNew, none)
  | .waitableJoin => some (.join, none)
  | .waitableSetWait _ _ => some (.wait, none)
  | _ => none

/-- The kind of a planned request, with the stream (of a function) it operates on. -/
def reqKind : New.Req → Option (OpKind × Option Chan)
  | .chan .new _ c _ => some (.streamNew, some c)
  | .chan .read _ c _ => some (.streamRead, some c)
  | .chan .write _ c _ => some (.streamWrite, some c)
  | .chan .dropReadable _ c _ => some (.dropReadable, some c)
  | .chan .dropWritable _ c _ => some (.dropWritable, some c)
  | .waitableSetNew => some (.setNew, none)
  | .waitableJoin => some (.join, none)
  | .waitableSetWait => some (.wait, none)
  | _ => none

/-! ## The shape of a stream transformer export -/

/-- The parameter and result streams of an async `stream<T> → stream<U>`. -/
def xfStreams (f : Func) : Option (Chan × Chan) :=
  match f.async, f.params, f.result with
  | true, [(_, .stream t)], some (.stream u) => some (.stream t, .stream u)
  | _, _, _ => none

/-- Whether the plan requests a built-in of kind `k` on stream `c` of function `name`. -/
def hasReq (p : New.Plan) (name : String) (k : OpKind) (c : Option Chan) : Bool :=
  p.reqs.any fun (_, r) => match r with
    | .chan _ _ _ f => f.name == name && reqKind r == some (k, c)
    | _ => reqKind r == some (k, c)

/-- Whether the plan requests `task.return` of `name`. -/
def hasTaskReturn (p : New.Plan) (name : String) : Bool :=
  p.reqs.any fun (_, r) => match r with
    | .taskReturn f => f.name == name
    | _ => false

/-- **The shape check** of export `name`: an async stream transformer, lifted async, with
the built-ins of every kind a `Proc` transformer performs. -/
def xfShape (p : New.Plan) (name : String) : Bool :=
  match (p.exports.zip p.lifts).find? (·.1.name == name) with
  | some (f, l) =>
    match xfStreams f with
    | some (a, b) =>
      (match l with
        | .stackful _ => hasReq p name .wait none
        | .callback _ _ => true
        | .sync _ _ => false) &&
      hasReq p name .streamRead (some a) && hasReq p name .dropReadable (some a) &&
      hasReq p name .streamNew (some b) && hasReq p name .streamWrite (some b) &&
      hasReq p name .dropWritable (some b) &&
      hasReq p name .setNew none && hasReq p name .join none &&
      hasTaskReturn p name
    | none => false
  | none => false

/-! ## Implementations of a transformer -/

variable {σ : Type}

/-- **An implementation of the transformer `tStep T N`**: a machine over the shared store,
related to `tStep T N` by a forward simulation with stuttering. -/
structure Impl (σ : Type) (T : Tr σ Val Val) (N : Nat) where
  M : Type
  step : Store → M → Option (Store × M)
  init : M
  done : M → Bool
  R : M → TPc σ → Prop
  init_R : R init (.rd T.init)
  step_R : ∀ {m t st st' m'}, R m t → step st m = some (st', m') →
    (∃ t', tStep T N st t = some (st', t') ∧ R m' t') ∨ (st' = st ∧ R m' t)
  done_R : ∀ {m t}, R m t → done m = true → t = .fin

/-- The pipeline with the transformer replaced by a machine. -/
structure SysM (M : Type) where
  st : Store
  p : PPc
  m : M
  c : CPc

variable {T : Tr σ Val Val} {N : Nat}

/-- One step of the pipeline through an implementation. -/
inductive StepM (I : Impl σ T N) : SysM I.M → SysM I.M → Prop where
  | prod {s : SysM I.M} {st' p'} : pStep s.st s.p = some (st', p') →
      StepM I s { s with st := st', p := p' }
  | impl {s : SysM I.M} {st' m'} : I.step s.st s.m = some (st', m') →
      StepM I s { s with st := st', m := m' }
  | cons {s : SysM I.M} {st' c'} (n : Nat) : 0 < n → cStep n s.st s.c = some (st', c') →
      StepM I s { s with st := st', c := c' }

inductive StepsM (I : Impl σ T N) : SysM I.M → SysM I.M → Prop where
  | refl (s : SysM I.M) : StepsM I s s
  | tail {s s' s'' : SysM I.M} : StepsM I s s' → StepM I s' s'' → StepsM I s s''

/-- The systems reachable from the setup store with the producer about to write `cs`. -/
def ReachM (I : Impl σ T N) (cs : List (List Val)) (s : SysM I.M) : Prop :=
  ∃ st₀, runOps Store.empty setupOps = some st₀ ∧
    StepsM I { st := st₀, p := .send cs, m := I.init, c := .recv [] } s

/-- `tStep T N` itself is an implementation (the simulation is equality). -/
def Impl.self (T : Tr σ Val Val) (N : Nat) : Impl σ T N where
  M := TPc σ
  step st t := tStep T N st t
  init := .rd T.init
  done t := match t with
    | .fin => true
    | _ => false
  R m t := m = t
  init_R := rfl
  step_R := by
    intro m t st st' m' hR h
    subst hR
    exact .inl ⟨m', h, rfl⟩
  done_R := by
    intro m t hR hd
    subst hR
    cases m <;> first | rfl | cases hd

end Silmaril.Wasm.JcoTool.StreamSem

namespace Silmaril.Wasm.JcoTool.StreamSem

/-- The report of `wasm-jco new`: the exports that pass the shape check (for which
`newWith_stream_semantics` gives a meaning). -/
def report (core : ByteArray) (w : Silmaril.Wasm.Wit.Binary.World) : List String :=
  match New.plan core w with
  | .ok p => (p.exports.filter fun f => xfShape p f.name).map fun f =>
      s!"proc:  export {f.name} has the shape of a Proc stream transformer (StreamSem.newWith_stream_semantics)"
  | .error _ => []

end Silmaril.Wasm.JcoTool.StreamSem
