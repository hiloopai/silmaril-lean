module

public import Silmaril.Wasm.Component.Reference.Canon.Prog.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Defs
public import Silmaril.Wasm.Component.Reference.Value.Nan.Defs
public import Silmaril.Wasm.Component.Reference.Value.Typing.Defs
public import Silmaril.Wasm.Component.Reference.Trap.Defs
public import Silmaril.Wasm.Component.Reference.Instantiate.Items.Defs

/-!
# The effect signature `Eff E σ` of the Canonical ABI specification

Every function of the reference `definitions.py` (component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF") is transcribed by the `Canon` and `Runtime` modules as a program `P E σ α := Prog (Eff E σ)
α` over the effect signature fixed here. `E : Engine.CoreEngine` is the core engine and `σ` the type
of the host (embedder / test harness) state. This file fixes:

1. **Choices** `ChoiceKind` with response types `ChoiceKind.Resp` and the per-profile gate
   `Allowed prof k r` (decidable). These are the nondeterministic choice points C1-C7 and the
   host nondeterminism E1 (the `Oracle` answering them is `Machine/Oracle.lean`).
2. **The universal call result** `Ret E` of every late-bound call, with decoding helpers
   (`callNat`, `callVals`, ...) that trap with `TrapReason.internal` on a shape mismatch
   (unreachable in well-formed runs: the dispatcher `Canon.dispatch` returns the documented shape).
3. **Defunctionalized closures**: `ThreadBody E` (REF `thread_func`s), `LoopPoint E` (REF
   `while` loops), `HostBufOp` (host `ReadableBuffer`/`WritableBuffer` methods of
   `run_tests.py`) and host observations `HostObs`.
4. **Late-bound calls** `Call E` (see the contract table below).
5. **Operations** `Op E σ` and `Eff E σ`, `P E σ`.
6. **Helpers** in `P`: traps, store access, choices, `currentTask?`/`currentInst?` (REF
   `current_task`/`current_instance`), instance access, handle/thread tables of an instance
   (REF `Table.add/get/remove` on `inst.handles` and `inst.threads`), arena access, and typed
   late-bound calls.
7. **Program-logic hook**: `Op.PreservesInv I` and `P.Inv I p := Prog.Every
   (Op.PreservesInv I) p`, with bind/mapM/forM/foldlM lemmas and one lemma per helper.

## Operations (`Op E σ`) and their responses

| Op | Resp | Meaning |
| --- | --- | --- |
| `get` | `CStore E` | read the component store |
| `modify f` | `Unit` | apply the (named, pure) store update `f` |
| `trap r` | `Empty` | trap: the machine locks the store down (REF `trap()`; `r` informative) |
| `choose k` | `k.Resp` | nondeterministic choice, gated by `Allowed prof k` |
| `callCore f args` | `List FlatValue` | REF `call_and_trap_on_throw` of a core function |
| `call c` | `Ret E` | late-bound call (defunctionalized closure or loop), see below |
| `currentThread` | `Option ThreadId` | REF `current_thread()`; `none` on host frames |
| `newThread b` | `ThreadId` | REF `Thread(task, thread_func)`: a new blocked, suspended thread |
| `block sw` | `Unit` | REF `block(switch_to = sw)` |
| `resumeThread t` | `Unit` | REF `Thread.resume` (resume site, R1-R4) |
| `hostGet` / `hostSet s` | `σ` / `Unit` | host state (E1) |
| `emit o` | `Unit` | record a host-visible observation |

`newThread b` allocates the `Runtime.Thread` object (status blocked, no ready condition, task
`b.task`) whose saved continuation, held by the machine (never by `CStore`), is
`call (.threadBody b)`. The machine rules are `Machine/Step.lean`.

## Call contract table

Every late-bound call returns the universal `Ret E`; the shape each constructor returns is
fixed here and is what the typed helper decodes.

| `Call` constructor | REF counterpart (see notes) | `Ret` | helper |
| --- | --- | --- | --- |
| `reallocate cx old oldLen align newLen` | `LiftLowerContext.reallocate` | `nat` | `callNat` |
| `funcInst f caller` | `FuncInst(on_start, on_resolve)` (L387-390) (a) | `cancel` | `callCancel` |
| `onStart c` | `on_start()` of caller record `c` | `vals` | `callVals` |
| `onResolve c r` | `on_resolve(r)` of caller record `c` | `unit` | `callUnit` |
| `onCancel r` | `OnCancel()` (b) | `unit` | `callUnit` |
| `hostCallout h args` | a core call of a canon host function (c) | `flat` | `callFlat` |
| `threadBody b` | `thread_func()` of a new thread (d) | `unit` | `callUnit` |
| `loop l` | one REF `while` loop from its head (`LoopPoint`) | `unit` | `callUnit` |
| `hostFunc fn caller` | a host `FuncInst` (E1; `mk_host_func`) | `cancel` | `callCancel` |
| `hostBuffer op` | host buffer `read` / `write` / pump (e) | `vals` / `unit` | `callVals` |
| `hostInvoke f args` | `Store.invoke` in a host function (f) | `invoked` | `callInvoke` |
| `hostCancel r` | the `on_cancel` returned by `Store.invoke` (L530-534) (g) | `unit` | `callUnit` |
| `instantiate c args` | nested `instance (instantiate c args)` (h) | `items` | `callItems` |

Notes: `reallocate` is L625-641; (a) `Store.lift`'s `func_inst` (L539-543) for a lifted function,
or a host `FuncInst`;
(b) `Task.request_cancellation`, a host hook, or nothing (`CancelRef`); (c) `Store.lower`'s
`core_func_inst` (L547, i.e. `canon_lower`), a canon built-in, or an embedder import: the
result is what core code sees; (d) `canon_lift`'s `thread_func` (L2077) of a core callee or of
the no-op destructor `lambda rep: []` (L2257), `canon_thread_new_indirect`, or run_tests
`mk_host_func`; (e) run_tests
`HostReadableBuffer.read` (`vals`), `HostWritableBuffer.write` (`unit`) and
`pump_after_other_end_makes_progress` (`unit`);
(f) `Store.invoke` is L524-536. The result `Ret.invoked r res` carries the `on_cancel` handle
`r` returned by `invoke` together with the resolution status observed when `invoke` returned:
`res = none` means the call has not resolved yet (the resolution reaches the host caller
record's `on_resolve` later), `res = some none` means it resolved by cancellation (REF
`on_resolve(None)`), and `res = some (some vs)` means it returned `vs`;
(g) `hostCancel r` consumes a handle `r` obtained from `hostInvoke`; the dispatcher
brackets it with `nesting_depth += 1` / `-= 1` as REF `on_cancel` (L530-534) does;
(h) no REF function (the Python reference has no instantiation): instantiate the component
closure `c` (`Instantiate.Closure`) with the argument map `args` in a fresh component instance
and return its export map (`Ret.items`); the dispatcher runs `Instantiate.instantiateClosure`
with this very call as the nested-instantiation tie, so nesting depth is bounded only by the
machine's fuel.

`Ret.optVals` and `Ret.thread` are reserved for dispatch-internal calls (no `Call`
constructor above returns them).

Every REF `while` loop is a *tail* `call (.loop l)`: the loop body runs one iteration and
re-issues `call (.loop l')`, so `Prog` stays a finite tree and only the machine's fuel loop
recurses. The REF loops are exactly:
* `canon_lift`'s callback loop (L2108-2134): `LoopPoint.callbackLoop`;
* `canon_lift`'s synchronous mini-scheduler (L2141-2144): `LoopPoint.syncLiftLoop`;
* `Thread.resume`'s `switch_to` chain (L334-337, resume site R4): handled by the machine rule
  of `block (some t)`, not a `LoopPoint`.

## Deviations and non-claims

* Choices among `n + 1` alternatives: `tickPick`, `syncLoopPick` and `host` carry the index
  `last` of the last alternative and respond with `Fin (last + 1)`, so every response type is
  inhabited (an oracle is a total function). REF `random.choice` is only applied to nonempty
  candidate sets (`Store.tick` L560, `canon_lift` L2143 traps first), so no choice among zero
  alternatives is ever needed.
* The handle-table limit is the fixed `Runtime.Table.maxLength` (REF `Table.MAX_LENGTH`, equal
  in wasmtime); `Limits` has no handle field, so the table helpers take no `Limits`.
* `HostObs` is defined here (it is an operand of `Op.emit`); `Machine/Oracle.lean` reuses it.
* C6b responds with a REF `String` tuple (`StrVal`, not a bare Lean `String`), so a host
  transformation may change the encoding and tagged code-unit count; `Allowed` only requires
  the result to be consistent (`StringValue.Consistent` for its source pointer width).
* `Call.hostInvoke` returns `Ret.invoked r res` (the `on_cancel` handle and a three-way
  resolution status), not `Ret.optVals`: REF `invoke` returns `on_cancel`, and
  `on_resolve(None)` (cancelled) must be distinguishable from a pending call.
* `Op.PreservesInv I` only constrains `modify`. The store effects of `trap`, `callCore`,
  `newThread`, `block`, `resumeThread` and `call` are the machine's (`Machine/Step.lean`);
  invariants across them are proved against the machine (`Machine/Invariant.lean`), not here.
* `Call` and `Ret` have no `DecidableEq`: `Call.instantiate` and `Ret.items` carry
  instantiation-time item values (`Instantiate.ItemVal`), which contain semantic types and
  engine modules without decidable equality. They get hand-written Boolean comparisons
  instead (`Call.beq`, `Ret.beq`), which are `false` whenever either side is
  `instantiate`/`items` (so they are not reflexive on those constructors) and are decidable
  equality elsewhere (`Call.beq_iff_eq`, `Ret.beq_iff_eq` for the other constructors). They
  are deliberately NOT registered as `BEq` instances, so `==` on `Call`/`Ret` does not
  elaborate and callers must opt in to the non-reflexive comparison explicitly.
* Nothing here gives a semantics to `Op`; this file is an interface.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value

/-! ## Choices -/

/-- The nondeterministic choice points of the REF (C1-C7) and of the host.
The argument `last` of the picking choices is the index of the last alternative
(`last + 1` alternatives; see the module docstring). -/
inductive ChoiceKind where
  /-- C1, REF `Thread.wait_until` (L347): the ready function already holds; `true` returns
  early without blocking. The wait site lets policies tell e.g. K9 from K4. -/
  | earlyReturn (site : WaitSite)
  /-- C2, REF `Store.tick` (L561): which of the `last + 1` ready threads to resume. -/
  | tickPick (last : Nat)
  /-- C3, REF `canon_lift` sync loop (L2144): which of the `last + 1` ready same-instance
  threads to resume. -/
  | syncLoopPick (last : Nat)
  /-- C4, REF `WaitableSet.get_pending_event` `random.shuffle(self.elems)` (L779): the
  permutation of `range n` applied (and persisted) to the `n` elements. -/
  | shuffle (n : Nat)
  /-- C5, REF `End.cancel` (L984-988) with a host-owned peer: `true` notifies now. -/
  | cancelNow
  /-- C6a, REF `canon_error_context_new` (L2670): `true` keeps the (transformed) message,
  `false` discards it (REF deterministic profile). -/
  | errCtxKeep
  /-- C6b, REF `host_defined_transformation(s)` (L2675) of the loaded message `s`. The REF
  string is the tuple `(str, encoding, tagged_code_units)` (here `StrVal`, D-a), so the host
  may change the encoding and code-unit count too; these decide which `store_string` path
  `error-context.debug-message` later takes. -/
  | errCtxMessage (s : StrVal)
  /-- C7, REF `maybe_scramble_nan32/64` (L1491-1507): the bits a float `x` lowers to. -/
  | nan (t : FloatType) (x : BitVec t.width)
  /-- E1: a host choice among `last + 1` alternatives (host function programs). -/
  | host (last : Nat)
  deriving DecidableEq

/-- The response type of each choice. -/
@[reducible] def ChoiceKind.Resp : ChoiceKind → Type
  | .earlyReturn _ => Bool
  | .tickPick last => Fin (last + 1)
  | .syncLoopPick last => Fin (last + 1)
  | .shuffle _ => List Nat
  | .cancelNow => Bool
  | .errCtxKeep => Bool
  | .errCtxMessage _ => StrVal
  | .nan t _ => BitVec t.width
  | .host last => Fin (last + 1)

/-- Admissible answers per profile.
* `nondet`: any answer; a shuffle must be a permutation of `range n`; NaN lowering follows
  `NanLower .nondet`.
* `refStrict`: as `nondet`, except NaN lowering follows `NanLower .refStrict` (the image of
  REF `random_nan_bits`).
* `deterministic` (REF `DETERMINISTIC_PROFILE = True`): `earlyReturn` is `false` (always
  block), `cancelNow` is `true`, `errCtxKeep` is `false`, NaNs are canonical. Picks and
  shuffles stay unrestricted: the Python deterministic profile does not fix C2-C4.
In every profile a transformed error-context message (C6b) must be a consistent REF string
(`StringValue.Consistent` for its source pointer width), i.e. a well-formed REF `String` tuple,
and valid (`StrVal.Valid`: also within `MAX_STRING_BYTE_LENGTH`) whenever the message it
transforms is: REF `canon_error_context_new` transforms a string lifted by
`load_string_from_range`, and `canon_error_context_debug_message` stores the result with
`store_string`, which asserts `MAX_STRING_BYTE_LENGTH`; the deterministic profile never
reaches C6b. -/
def Allowed (prof : ProfileKind) : (k : ChoiceKind) → k.Resp → Prop
  | .earlyReturn _, r => prof = .deterministic → r = false
  | .tickPick _, _ => True
  | .syncLoopPick _, _ => True
  | .shuffle n, r => List.Perm r (List.range n)
  | .cancelNow, r => prof = .deterministic → r = true
  | .errCtxKeep, r => prof = .deterministic → r = false
  | .errCtxMessage s, r => r.v.Consistent r.srcAddr ∧ (s.Valid → r.Valid)
  | .nan t x, r => NanLower prof t x r
  | .host _, _ => True

instance instDecidableAllowed (prof : ProfileKind) :
    (k : ChoiceKind) → (r : k.Resp) → Decidable (Allowed prof k r)
  | .earlyReturn _, r => inferInstanceAs (Decidable (prof = .deterministic → r = false))
  | .tickPick _, _ => instDecidableTrue
  | .syncLoopPick _, _ => instDecidableTrue
  | .shuffle n, r => inferInstanceAs (Decidable (List.Perm (α := Nat) r (List.range n)))
  | .cancelNow, r => inferInstanceAs (Decidable (prof = .deterministic → r = true))
  | .errCtxKeep, r => inferInstanceAs (Decidable (prof = .deterministic → r = false))
  | .errCtxMessage s, r =>
    inferInstanceAs (Decidable (r.v.Consistent r.srcAddr ∧ (s.Valid → r.Valid)))
  | .nan t x, r => inferInstanceAs (Decidable (NanLower prof t x r))
  | .host _, _ => instDecidableTrue

/-! ## Universal call results and defunctionalized closures -/

/-- The universal result of a late-bound call (see the call contract table). `E` is a phantom
parameter kept for uniformity with `Call E`. -/
inductive Ret (E : CoreEngine) where
  | unit
  | nat (n : Nat)
  | flat (vs : List FlatValue)
  | vals (vs : List Val)
  | optVals (o : Option (List Val))
  | cancel (r : CancelRef)
  | thread (t : ThreadId)
  /-- The result of `Call.hostInvoke`: the `on_cancel` handle and the resolution status
  (`none`: pending; `some none`: cancelled; `some (some vs)`: returned `vs`). -/
  | invoked (r : CancelRef) (res : Option (Option (List Val)))
  /-- The result of `Call.instantiate`: the export map of the new component instance. -/
  | items (exports : List (String × Instantiate.ItemVal E))

/-- A REF `thread_func` closure, as data. -/
inductive ThreadBody (E : CoreEngine) where
  /-- The implicit thread of `canon_lift` (`thread_func`, L2077-2135) of task `task` calling
  `callee`. -/
  | liftImplicit (task : TaskId) (callee : E.FuncAddr)
  /-- A `thread.new-indirect` thread of `task`: call `f` with the context argument `arg`. -/
  | newIndirect (task : TaskId) (f : E.FuncAddr) (arg : FlatValue)
  /-- A host function running on its own thread (run_tests `mk_host_func`). -/
  | host (fn : HostFuncId) (task : TaskId)
  /-- The implicit thread of the `canon_lift` of REF's no-op destructor `lambda rep: []`
  (`canon_resource_drop`, L2257) of task `task`: `thread_func` with a callee that returns
  `[]` without running core code. -/
  | liftNoop (task : TaskId)
  deriving DecidableEq

/-- The task a thread body belongs to (REF `Thread.task`). -/
def ThreadBody.task {E : CoreEngine} : ThreadBody E → TaskId
  | .liftImplicit t _ => t
  | .newIndirect t _ _ => t
  | .host _ t => t
  | .liftNoop t => t

/-- A REF `while` loop, entered at its head (one constructor per loop; see the module
docstring). -/
inductive LoopPoint (E : CoreEngine) where
  /-- `canon_lift` callback loop (L2108-2134): `while code != EXIT` for task `task` on its
  implicit thread `thread`, with the last unpacked callback code and waitable-set index. -/
  | callbackLoop (task : TaskId) (thread : ThreadId) (code si : Nat)
  /-- `canon_lift` synchronous mini-scheduler (L2141-2144): `while task.state != RESOLVED`. -/
  | syncLiftLoop (task : TaskId)
  deriving DecidableEq

/-- Host buffer operations (E1): the methods of run_tests' `HostReadableBuffer` and
`HostWritableBuffer` (L1341-1370) and the `pump` hook of
`pump_after_other_end_makes_progress` (run_tests L1374-1393). -/
inductive HostBufOp where
  /-- `ReadableBuffer.read(n)` of host buffer `b` (`Ret.vals`). -/
  | read (b : HostBufId) (n : Nat)
  /-- `WritableBuffer.write(vs)` of host buffer `b` (`Ret.unit`). -/
  | write (b : HostBufId) (vs : List Val)
  /-- The host reacts after the peer of end `e` copied or dropped (`Ret.unit`). -/
  | pump (e : EndId)
  deriving DecidableEq

/-- Host-visible observations recorded by `Op.emit` (used by traces and tests). -/
inductive HostObs where
  /-- The `on_start` of top-level host call `call` handed its arguments over. -/
  | started (call : CallId)
  /-- The `on_resolve` of top-level host call `call` (`none`: cancelled). -/
  | resolved (call : CallId) (r : Option (List Val))
  /-- Host buffer `b` received values. -/
  | received (b : HostBufId) (vs : List Val)
  /-- A free-form observation of a host function (tests). -/
  | note (tag : String) (vs : List Val)
  deriving DecidableEq

/-- Late-bound calls: defunctionalized Python closures and loops, resolved by the
non-recursive dispatcher (`Canon.dispatch`). See the call contract table in the module docstring. -/
inductive Call (E : CoreEngine) where
  /-- REF `LiftLowerContext.reallocate` (`Ret.nat`). -/
  | reallocate (cx : LiftLowerContext E) (old oldLen align newLen : Nat)
  /-- REF `FuncInst(on_start, on_resolve)` of function value `f` (`Ret.cancel`). -/
  | funcInst (f : FuncId) (caller : CallerId)
  /-- REF `on_start()` (`Ret.vals`). -/
  | onStart (c : CallerId)
  /-- REF `on_resolve(r)` (`Ret.unit`). -/
  | onResolve (c : CallerId) (r : Option (List Val))
  /-- REF `OnCancel()` (`Ret.unit`). -/
  | onCancel (r : CancelRef)
  /-- A core call of a canon host function (`Ret.flat`: what core code sees). -/
  | hostCallout (h : CanonHost E) (args : List FlatValue)
  /-- REF `thread_func()` (`Ret.unit`). -/
  | threadBody (b : ThreadBody E)
  /-- A REF `while` loop from its head (`Ret.unit`). -/
  | loop (l : LoopPoint E)
  /-- A host `FuncInst` (`Ret.cancel`). -/
  | hostFunc (fn : HostFuncId) (caller : CallerId)
  /-- A host buffer operation. -/
  | hostBuffer (op : HostBufOp)
  /-- REF `Store.invoke` from inside a host function (`Ret.invoked`: the `on_cancel`
  handle and the resolution status). -/
  | hostInvoke (f : FuncId) (args : List Val)
  /-- REF `Store.invoke`'s `on_cancel` for a handle returned by `hostInvoke` (`Ret.unit`). -/
  | hostCancel (r : CancelRef)
  /-- Nested instantiation `instance (instantiate c args)`: instantiate the closure `c` with
  the argument map `args` in a fresh component instance (`Ret.items`: its exports). -/
  | instantiate (c : Instantiate.Closure E) (args : List (String × Instantiate.ItemVal E))

/-- Boolean equality of results: decidable equality on every constructor except `items`,
which is never equal (item values have no decidable equality). -/
def Ret.beq {E : CoreEngine} : Ret E → Ret E → Bool
  | .unit, .unit => true
  | .nat a, .nat b => decide (a = b)
  | .flat a, .flat b => decide (a = b)
  | .vals a, .vals b => decide (a = b)
  | .optVals a, .optVals b => decide (a = b)
  | .cancel a, .cancel b => decide (a = b)
  | .thread a, .thread b => decide (a = b)
  | .invoked a r, .invoked b r' => decide (a = b) && decide (r = r')
  | _, _ => false

/-- Boolean equality of late-bound calls: decidable equality on every constructor except
`instantiate`, which is never equal (closures have no decidable equality). -/
def Call.beq {E : CoreEngine} : Call E → Call E → Bool
  | .reallocate cx o l a n, .reallocate cx' o' l' a' n' =>
    decide (cx = cx') && decide ((o, l, a, n) = (o', l', a', n'))
  | .funcInst f c, .funcInst f' c' => decide (f = f') && decide (c = c')
  | .onStart c, .onStart c' => decide (c = c')
  | .onResolve c r, .onResolve c' r' => decide (c = c') && decide (r = r')
  | .onCancel r, .onCancel r' => decide (r = r')
  | .hostCallout h as, .hostCallout h' as' => decide (h = h') && decide (as = as')
  | .threadBody b, .threadBody b' => decide (b = b')
  | .loop l, .loop l' => decide (l = l')
  | .hostFunc fn c, .hostFunc fn' c' => decide (fn = fn') && decide (c = c')
  | .hostBuffer op, .hostBuffer op' => decide (op = op')
  | .hostInvoke f as, .hostInvoke f' as' => decide (f = f') && decide (as = as')
  | .hostCancel r, .hostCancel r' => decide (r = r')
  | _, _ => false

/-! ## Operations and the signature -/

/-- The operations of the specification carrier (see the table in the module docstring). -/
inductive Op (E : CoreEngine) (σ : Type) where
  | get
  | modify (f : CStore E → CStore E)
  | trap (r : TrapReason)
  | choose (k : ChoiceKind)
  | callCore (f : E.FuncAddr) (args : List FlatValue)
  | call (c : Call E)
  | currentThread
  | newThread (b : ThreadBody E)
  | block (switchTo : Option ThreadId)
  | resumeThread (t : ThreadId)
  | hostGet
  | hostSet (s : σ)
  | emit (o : HostObs)

/-- Response types of the operations. -/
def Op.Resp {E : CoreEngine} {σ : Type} : Op E σ → Type
  | .get => CStore E
  | .modify _ => Unit
  | .trap _ => Empty
  | .choose k => k.Resp
  | .callCore _ _ => List FlatValue
  | .call _ => Ret E
  | .currentThread => Option ThreadId
  | .newThread _ => ThreadId
  | .block _ => Unit
  | .resumeThread _ => Unit
  | .hostGet => σ
  | .hostSet _ => Unit
  | .emit _ => Unit

/-- The effect signature of the Canonical ABI specification. -/
def Eff (E : CoreEngine) (σ : Type) : Sig := ⟨Op E σ, Op.Resp⟩

/-- Specification programs. -/
abbrev P (E : CoreEngine) (σ : Type) := Prog (Eff E σ)

variable {E : CoreEngine} {σ : Type} {α β : Type}

/-! ## Primitive operations -/

/-- Issue one operation. -/
def perform (o : Op E σ) : P E σ o.Resp := Prog.lift (S := Eff E σ) o

/-- REF `trap()`: trap with an informative reason. -/
def trap (r : TrapReason) : P E σ α := .op (S := Eff E σ) (.trap r) (fun e => nomatch e)

/-- REF `trap_if(c)`. -/
def trapIf (c : Bool) (r : TrapReason) : P E σ Unit := if c then trap r else pure ()

/-- An internal error (unreachable in well-formed runs). -/
def internal (msg : String) : P E σ α := trap (.internal msg)

/-- Read the component store. -/
def getStore : P E σ (CStore E) := perform .get

/-- Apply a store update. -/
def modifyStore (f : CStore E → CStore E) : P E σ Unit := perform (.modify f)

/-- A nondeterministic choice. -/
def choose (k : ChoiceKind) : P E σ k.Resp := perform (.choose k)

/-- REF `call_and_trap_on_throw` of a core function. -/
def callCore (f : E.FuncAddr) (args : List FlatValue) : P E σ (List FlatValue) :=
  perform (.callCore f args)

/-- A late-bound call. -/
def callRet (c : Call E) : P E σ (Ret E) := perform (.call c)

/-- REF `current_thread()`; `none` on host frames. -/
def currentThread : P E σ (Option ThreadId) := perform .currentThread

/-- REF `Thread(task, thread_func)`. -/
def newThread (b : ThreadBody E) : P E σ ThreadId := perform (.newThread b)

/-- REF `block(switch_to)`. -/
def block (switchTo : Option ThreadId) : P E σ Unit := perform (.block switchTo)

/-- REF `Thread.resume` of `t`. -/
def resumeThread (t : ThreadId) : P E σ Unit := perform (.resumeThread t)

/-- Read the host state. -/
def hostGet : P E σ σ := perform .hostGet

/-- Replace the host state. -/
def hostSet (s : σ) : P E σ Unit := perform (.hostSet s)

/-- Record a host-visible observation. -/
def emit (o : HostObs) : P E σ Unit := perform (.emit o)

/-- Read a projection of the store. -/
def gets (f : CStore E → α) : P E σ α := do return f (← getStore)

/-- Embed an `Option`, trapping with `r` on `none`. -/
def orTrap (r : TrapReason) : Option α → P E σ α
  | some a => pure a
  | none => trap r

/-! ## Choices over lists -/

/-- C2: pick one of the nonempty candidate list `c :: cs` (REF `Store.tick`). -/
def pickTick (c : α) (cs : List α) : P E σ α := do
  let i : Fin (cs.length + 1) ← choose (.tickPick cs.length)
  return (c :: cs)[i.val]'(by simp only [List.length_cons]; exact i.isLt)

/-- C3: pick one of the nonempty candidate list `c :: cs` (REF `canon_lift` sync loop). -/
def pickSyncLoop (c : α) (cs : List α) : P E σ α := do
  let i : Fin (cs.length + 1) ← choose (.syncLoopPick cs.length)
  return (c :: cs)[i.val]'(by simp only [List.length_cons]; exact i.isLt)

/-- E1: a host pick among the nonempty list `c :: cs`. -/
def pickHost (c : α) (cs : List α) : P E σ α := do
  let i : Fin (cs.length + 1) ← choose (.host cs.length)
  return (c :: cs)[i.val]'(by simp only [List.length_cons]; exact i.isLt)

/-- Apply a permutation `perm` of `range xs.length` to `xs` (indices out of range are
dropped; admissible answers are permutations, for which this is a permutation of `xs`). -/
def applyPerm (perm : List Nat) (xs : List α) : List α := perm.filterMap (xs[·]?)

/-- C4: REF `random.shuffle(xs)`. -/
def shuffle (xs : List α) : P E σ (List α) := do
  let perm : List Nat ← choose (.shuffle xs.length)
  return applyPerm perm xs

/-! ## Typed late-bound calls -/

/-- A late-bound call returning `Ret.unit`. -/
def callUnit (c : Call E) : P E σ Unit := do
  match ← callRet c with
  | .unit => pure ()
  | _ => internal "late-bound call: expected Ret.unit"

/-- A late-bound call returning `Ret.nat`. -/
def callNat (c : Call E) : P E σ Nat := do
  match ← callRet c with
  | .nat n => pure n
  | _ => internal "late-bound call: expected Ret.nat"

/-- A late-bound call returning `Ret.flat`. -/
def callFlat (c : Call E) : P E σ (List FlatValue) := do
  match ← callRet c with
  | .flat vs => pure vs
  | _ => internal "late-bound call: expected Ret.flat"

/-- A late-bound call returning `Ret.vals`. -/
def callVals (c : Call E) : P E σ (List Val) := do
  match ← callRet c with
  | .vals vs => pure vs
  | _ => internal "late-bound call: expected Ret.vals"

/-- A late-bound call returning `Ret.optVals`. -/
def callOptVals (c : Call E) : P E σ (Option (List Val)) := do
  match ← callRet c with
  | .optVals o => pure o
  | _ => internal "late-bound call: expected Ret.optVals"

/-- A late-bound call returning `Ret.cancel`. -/
def callCancel (c : Call E) : P E σ CancelRef := do
  match ← callRet c with
  | .cancel r => pure r
  | _ => internal "late-bound call: expected Ret.cancel"

/-- A late-bound call returning `Ret.invoked` (`Call.hostInvoke`): the `on_cancel` handle and
the resolution status (`none`: pending; `some none`: cancelled; `some (some vs)`: returned). -/
def callInvoke (c : Call E) : P E σ (CancelRef × Option (Option (List Val))) := do
  match ← callRet c with
  | .invoked r res => pure (r, res)
  | _ => internal "late-bound call: expected Ret.invoked"

/-- A late-bound call returning `Ret.thread`. -/
def callThread (c : Call E) : P E σ ThreadId := do
  match ← callRet c with
  | .thread t => pure t
  | _ => internal "late-bound call: expected Ret.thread"

/-- A late-bound call returning `Ret.items` (`Call.instantiate`): an export map. -/
def callItems (c : Call E) : P E σ (List (String × Instantiate.ItemVal E)) := do
  match ← callRet c with
  | .items es => pure es
  | _ => internal "late-bound call: expected Ret.items"

/-! ## Arena access -/

namespace ArenaOps

variable {Id : Type} (F : ArenaField E Id α)

/-- The store update of `allocObj`: append `x` to the arena of `F`. -/
def allocSt (x : α) (s : CStore E) : CStore E := (F.alloc s x).1

/-- The store update of `modifyObj`: update object `i` of the arena of `F`. -/
def updateSt (i : Id) (f : α → α) (s : CStore E) : CStore E := F.modify s i f

end ArenaOps

/-- Allocate `x` in the arena `F`; returns its fresh id. -/
def allocObj {Id : Type} (F : ArenaField E Id α) (x : α) : P E σ Id := do
  let s ← getStore
  modifyStore (ArenaOps.allocSt F x)
  return F.mkId (F.size s)

/-- The object `i` of arena `F`; a dangling id is an internal error (arena ids are never
freed, so a dangling id is unreachable in well-formed runs). -/
def getObj {Id : Type} (F : ArenaField E Id α) (i : Id) : P E σ α := do
  match F.get? (← getStore) i with
  | some x => pure x
  | none => internal "dangling arena id"

/-- Update the object `i` of arena `F` with the named function `f`. -/
def modifyObj {Id : Type} (F : ArenaField E Id α) (i : Id) (f : α → α) : P E σ Unit :=
  modifyStore (ArenaOps.updateSt F i f)

/-! ## Current thread, task and instance -/

/-- The thread `t`. -/
def getThread (t : ThreadId) : P E σ Thread := getObj ArenaField.threads t

/-- The task `t`. -/
def getTask (t : TaskId) : P E σ (Task E) := getObj ArenaField.tasks t

/-- The component instance `i`. -/
def getInst (i : InstId) : P E σ InstState := getObj ArenaField.insts i

/-- REF `current_task()`: the task of the current thread; `none` on host frames. -/
def currentTask? : P E σ (Option TaskId) := do
  match ← currentThread with
  | none => pure none
  | some t => return some (← getThread t).task

/-- REF `current_instance()`: the instance of the current task; `none` on host frames. -/
def currentInst? : P E σ (Option InstId) := do
  match ← currentTask? with
  | none => pure none
  | some t => return some (← getTask t).inst

/-- REF `current_thread()` where the REF asserts it exists (canon built-ins). -/
def currentThreadId : P E σ ThreadId := do
  match ← currentThread with
  | some t => pure t
  | none => internal "no current thread"

/-- REF `current_task()` where the REF asserts it exists. -/
def currentTask : P E σ TaskId := do
  match ← currentTask? with
  | some t => pure t
  | none => internal "no current task"

/-- REF `current_instance()` where the REF asserts it exists. -/
def currentInst : P E σ InstId := do
  match ← currentInst? with
  | some i => pure i
  | none => internal "no current instance"

/-- Run `f` on the state of instance `inst`. -/
def withInst (inst : InstId) (f : InstState → P E σ α) : P E σ α := do
  f (← getInst inst)

/-- Update instance `inst` with the named function `f`. -/
def modifyInst (inst : InstId) (f : InstState → InstState) : P E σ Unit :=
  modifyObj ArenaField.insts inst f

/-! ## Handle and thread tables of an instance -/

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Runtime.InstState

/-- REF `inst.handles.add(e)` on the instance state (`none`: the table is full). -/
def addHandle? (e : HandleEntry) (st : InstState) : Option (Nat × InstState) :=
  (st.handles.add? e).map fun (i, t) => (i, { st with handles := t })

/-- REF `inst.handles.remove(i)` on the instance state (`none`: unknown index). -/
def removeHandle? (i : Nat) (st : InstState) : Option (HandleEntry × InstState) :=
  (st.handles.remove? i).map fun (e, t) => (e, { st with handles := t })

/-- REF `inst.threads.add(t)` on the instance state (`none`: the table is full). -/
def addThread? (t : ThreadId) (st : InstState) : Option (Nat × InstState) :=
  (st.threads.add? t).map fun (i, tb) => (i, { st with threads := tb })

/-- REF `inst.threads.remove(i)` on the instance state (`none`: unknown index). -/
def removeThread? (i : Nat) (st : InstState) : Option (ThreadId × InstState) :=
  (st.threads.remove? i).map fun (t, tb) => (t, { st with threads := tb })

/-- The update of `addHandle?` (unchanged when full). -/
def addHandle (e : HandleEntry) (st : InstState) : InstState :=
  ((addHandle? e st).map Prod.snd).getD st

/-- The update of `removeHandle?` (unchanged when unknown). -/
def removeHandle (i : Nat) (st : InstState) : InstState :=
  ((removeHandle? i st).map Prod.snd).getD st

/-- The update of `addThread?` (unchanged when full). -/
def addThread (t : ThreadId) (st : InstState) : InstState :=
  ((addThread? t st).map Prod.snd).getD st

/-- The update of `removeThread?` (unchanged when unknown). -/
def removeThread (i : Nat) (st : InstState) : InstState :=
  ((removeThread? i st).map Prod.snd).getD st

end Silmaril.Wasm.Component.Runtime.InstState

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type} {α β : Type}

/-- REF `inst.handles.add(e)` (L670-679): trap `tableFull` past `Table.MAX_LENGTH`. -/
def handlesAdd (inst : InstId) (e : HandleEntry) : P E σ Nat := do
  match (← getInst inst).addHandle? e with
  | none => trap .tableFull
  | some (i, _) =>
    modifyInst inst (InstState.addHandle e)
    pure i

/-- REF `inst.handles.get(i)` (L665-668): trap `unknownHandle i`. -/
def handlesGet (inst : InstId) (i : Nat) : P E σ HandleEntry := do
  orTrap (.unknownHandle i) ((← getInst inst).handles.get? i)

/-- REF `inst.handles.remove(i)` (L681-685): trap `unknownHandle i`. -/
def handlesRemove (inst : InstId) (i : Nat) : P E σ HandleEntry := do
  match (← getInst inst).removeHandle? i with
  | none => trap (.unknownHandle i)
  | some (e, _) =>
    modifyInst inst (InstState.removeHandle i)
    pure e

/-- REF `inst.threads.add(t)` (`Table.add`, L670-679): trap `tableFull` past `Table.MAX_LENGTH`. -/
def threadsAdd (inst : InstId) (t : ThreadId) : P E σ Nat := do
  match (← getInst inst).addThread? t with
  | none => trap .tableFull
  | some (i, _) =>
    modifyInst inst (InstState.addThread t)
    pure i

/-- REF `inst.threads.get(i)` (`Table.get`, L665-668): trap `unknownHandle i`. -/
def threadsGet (inst : InstId) (i : Nat) : P E σ ThreadId := do
  orTrap (.unknownHandle i) ((← getInst inst).threads.get? i)

/-- REF `inst.threads.remove(i)` (`Table.remove`, L681-685): trap `unknownHandle i`. -/
def threadsRemove (inst : InstId) (i : Nat) : P E σ ThreadId := do
  match (← getInst inst).removeThread? i with
  | none => trap (.unknownHandle i)
  | some (t, _) =>
    modifyInst inst (InstState.removeThread i)
    pure t

/-! ## Program-logic hook -/

/-- An operation preserves the store invariant `I`: only `modify f` constrains (`f` must
preserve `I`); every other operation is accepted here, its store effect being the machine's
(proved against the machine in `Machine/Invariant.lean`). -/
def Op.PreservesInv (I : CStore E → Prop) : Op E σ → Prop
  | .modify f => ∀ s, I s → I (f s)
  | _ => True

/-- Every store update a program can issue preserves `I`. -/
def P.Inv (I : CStore E → Prop) (p : P E σ α) : Prop :=
  Prog.Every (S := Eff E σ) (Op.PreservesInv I) p

namespace P.Inv

variable {I : CStore E → Prop}

theorem pure (a : α) : P.Inv I (Pure.pure a : P E σ α) := Prog.Every.pure a

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon
