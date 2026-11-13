module

public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Prog
public import Silmaril.Raw.Wasm.Component.Runtime.Store
public import Silmaril.Raw.Wasm.Component.Value.Nan
public import Silmaril.Raw.Wasm.Component.Value.Typing
public import Silmaril.Raw.Wasm.Component.Trap
public import Silmaril.Raw.Wasm.Component.Instantiate.Items

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

/-- Every answer admissible in some profile is admissible in `nondet`. -/
theorem Allowed.to_nondet {prof : ProfileKind} {k : ChoiceKind} {r : k.Resp}
    (h : Allowed prof k r) : Allowed .nondet k r := by
  cases k with
  | earlyReturn _ => exact fun h' => nomatch h'
  | cancelNow => exact fun h' => nomatch h'
  | errCtxKeep => exact fun h' => nomatch h'
  | nan t x => exact NanLower.to_nondet (prof := prof) h
  | shuffle n => exact h
  | tickPick _ => trivial
  | syncLoopPick _ => trivial
  | errCtxMessage _ => exact h
  | host _ => trivial

/-- `refStrict` answers are `nondet` answers. -/
theorem Allowed.refStrict_to_nondet {k : ChoiceKind} {r : k.Resp}
    (h : Allowed .refStrict k r) : Allowed .nondet k r := h.to_nondet

example : Allowed .deterministic (.earlyReturn .yield_) (false : Bool) := by decide
example : ¬ Allowed .deterministic (.earlyReturn .yield_) (true : Bool) := by decide
example : Allowed .nondet (.earlyReturn .waitableSetWait) (true : Bool) := by decide
example : Allowed .deterministic (.shuffle 3) ([2, 0, 1] : List Nat) := by decide
example : ¬ Allowed .nondet (.shuffle 3) ([0, 0, 1] : List Nat) := by decide
example : ¬ Allowed .deterministic .errCtxKeep (true : Bool) := by decide
example : Allowed .deterministic (.nan .f32 negQuietNaN32)
    (ABI.canonicalNaN .f32 : BitVec FloatType.f32.width) := by decide

/-! ## Universal call results and defunctionalized closures -/

/-- Off `items`, `Ret.beq` is equality. -/
theorem Ret.beq_iff_eq {E : CoreEngine} {a b : Ret E} (ha : ∀ es, a ≠ .items es) :
    Ret.beq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp_all [Ret.beq]

/-- Off `instantiate`, `Call.beq` is equality. -/
theorem Call.beq_iff_eq {E : CoreEngine} {a b : Call E} (ha : ∀ c as, a ≠ .instantiate c as) :
    Call.beq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp_all [Call.beq]

/-! ## Operations and the signature -/

variable {E : CoreEngine} {σ : Type} {α β : Type}

/-! ## Primitive operations -/

/-! ## Choices over lists -/

example : applyPerm [2, 0, 1] ['a', 'b', 'c'] = ['c', 'a', 'b'] := by decide

/-! ## Typed late-bound calls -/

/-! ## Arena access -/

namespace ArenaOps

variable {Id : Type} (F : ArenaField E Id α)

end ArenaOps

/-! ## Current thread, task and instance -/

/-! ## Handle and thread tables of an instance -/

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Runtime.InstState

end Silmaril.Wasm.Component.Runtime.InstState

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type} {α β : Type}

/-! ## Program-logic hook -/

namespace P.Inv

variable {I : CStore E → Prop}

theorem pure' (a : α) : P.Inv I (Prog.pure a : P E σ α) := Prog.Every.pure a

theorem bind' {p : P E σ α} {f : α → P E σ β} (hp : P.Inv I p) (hf : ∀ a, P.Inv I (f a)) :
    P.Inv I (p.bind f) := Prog.Every.bind hp hf

theorem seq {p : P E σ Unit} {q : P E σ β} (hp : P.Inv I p) (hq : P.Inv I q) :
    P.Inv I (p >>= fun _ => q) := bind hp fun _ => hq

theorem mono {J : CStore E → Prop} {p : P E σ α} (hp : P.Inv I p)
    (h : ∀ o : Op E σ, Op.PreservesInv I o → Op.PreservesInv J o) : P.Inv J p :=
  Prog.Every.mono hp h

theorem listMapM {f : α → P E σ β} {xs : List α} (h : ∀ a ∈ xs, P.Inv I (f a)) :
    P.Inv I (List.mapM f xs) := by
  rw [← Prog.mapM_eq_list_mapM]; exact mapM h

theorem listForM {f : α → P E σ PUnit} {xs : List α} (h : ∀ a ∈ xs, P.Inv I (f a)) :
    P.Inv I (List.forM xs f) := by
  rw [← Prog.forM_eq_list_forM]; exact forM h

theorem pickHost (c : α) (cs : List α) : P.Inv I (Canon.pickHost c cs : P E σ α) :=
  bind (choose _) fun _ => pure _

private theorem callDecode {γ : Type} (c : Call E) (g : Ret E → P E σ γ)
    (hg : ∀ r, P.Inv I (g r)) : P.Inv I (Canon.callRet c >>= g) := bind (callRet c) hg

theorem callFlat (c : Call E) : P.Inv I (Canon.callFlat c : P E σ _) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem callOptVals (c : Call E) : P.Inv I (Canon.callOptVals c : P E σ _) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem callInvoke (c : Call E) : P.Inv I (Canon.callInvoke c : P E σ _) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem callThread (c : Call E) : P.Inv I (Canon.callThread c : P E σ _) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem withInst (inst : InstId) {f : InstState → P E σ α} (hf : ∀ st, P.Inv I (f st)) :
    P.Inv I (Canon.withInst inst f) := bind (getInst inst) hf

theorem threadsAdd (inst : InstId) (t : ThreadId)
    (h : ∀ s, I s → I (ArenaField.insts.modify s inst (InstState.addThread t))) :
    P.Inv I (Canon.threadsAdd inst t : P E σ Nat) :=
  bind (getInst inst) fun st => by
    cases st.addThread? t with
    | none => exact trap _
    | some r => exact bind (modifyInst inst h) fun _ => pure _

theorem threadsRemove (inst : InstId) (i : Nat)
    (h : ∀ s, I s → I (ArenaField.insts.modify s inst (InstState.removeThread i))) :
    P.Inv I (Canon.threadsRemove inst i : P E σ ThreadId) :=
  bind (getInst inst) fun st => by
    cases st.removeThread? i with
    | none => exact trap _
    | some r => exact bind (modifyInst inst h) fun _ => pure _

end P.Inv

/-- A program without `modify` preserves every invariant. -/
theorem P.Inv.of_no_modify {I : CStore E → Prop} {p : P E σ α}
    (h : Prog.Every (S := Eff E σ) (fun o => ∀ f, o ≠ Op.modify f) p) : P.Inv I p :=
  Prog.Every.mono h fun o ho => by
    cases o with
    | modify f => exact absurd rfl (ho f)
    | _ => trivial

/-! ## Examples -/

section Examples

/-- A small program: add a waitable-set handle to the current instance, then read it back. -/
example : P E σ HandleEntry := do
  let inst ← currentInst
  let i ← handlesAdd inst (.wset ⟨0⟩)
  handlesGet inst i

/-- A small host program: invoke a guest function reentrantly and cancel it if it is still
pending (REF Concurrency.md "Reentrance"). -/
example (f : FuncId) (args : List Val) : P E σ Unit := do
  let (r, res) ← callInvoke (.hostInvoke f args)
  if res.isNone then callUnit (.hostCancel r)

/-- A small program: a C2-style pick among ready threads, then resume it. -/
example (t : ThreadId) (ts : List ThreadId) : P E σ Unit := do
  let u ← pickTick t ts
  resumeThread u

/-- Programs issuing no `modify` preserve every invariant. -/
example (I : CStore E → Prop) (k : ChoiceKind) : P.Inv I (do
    let _ ← Canon.choose (E := E) (σ := σ) k
    let _ ← currentInst?
    Canon.callUnit (.onCancel .none)) :=
  P.Inv.bind (P.Inv.choose k) fun _ =>
    P.Inv.bind P.Inv.currentInst? fun _ => P.Inv.callUnit _

end Examples

end Silmaril.Wasm.Component.Canon
