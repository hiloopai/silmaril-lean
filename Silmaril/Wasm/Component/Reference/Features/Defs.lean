module

public import Silmaril.Wasm.Component.Reference.ABI.String.Defs
public import Silmaril.Wasm.Component.Reference.Async.Codes.Defs

/-!
# Feature gates, limits, quirks and profile kinds

The static and dynamic parameters every Component Model module takes as explicit
arguments.

* `Features`: one `Bool` per emoji gate of `Explainer.md` §"Gated Features" at
  component-model `a25fc0b`
  (<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Explainer.md>).
  The ungated base is WASI 0.2 (`Features.p2`); `Features.p3` is the shipped WASI 0.3.x
  set (🔀 + 🗺️ + 🏷️); `Features.p3plus` adds the unstable gates implemented by both
  `definitions.py` and wasmtime `a7b4f29`. `Features.le` is pointwise implication.
  **Out of scope:** the shared-everything threads gate 🧵② (`thread.spawn-*`,
  `available-parallelism`): it needs a shared-reference/GC core and has no field here.
  The 🪙 (values) and 🪺 (nested names) gates are represented but not implemented by
  wasmtime.
* `Limits`: the numeric size limits of the Canonical ABI. `Limits.spec` is exactly the
  `definitions.py` constants (`MAX_STRING_BYTE_LENGTH`, `MAX_LIST_BYTE_LENGTH`,
  `Buffer.MAX_LENGTH`, the backpressure counter bound `2^16`, and the two context
  slots), each stated against the constant by an `rfl` theorem. `Limits.wasmtime`
  is wasmtime's larger string/list limits (`crates/environ/src/fact/trampoline.rs`). The handle and
  thread table limit is *not* a field: it is the fixed `Runtime.Table.maxLength`, on which REF and
  wasmtime agree.
* `Quirks`: switches that reproduce implementation behaviour outside the
  specification, for differential replay only. Only `Quirks.none` is the
  specification.
* `ProfileKind`: which oracle answers are admissible (`nondet`, `refStrict`,
  `deterministic`); see `Value.NanLower` for its NaN component.

Nothing here has dynamic semantics of its own; no conformance claim is made.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

/-! ## Feature gates -/

/-- One Boolean per Component Model feature gate (`Explainer.md` §"Gated Features").
All gates default to off, i.e. the WASI 0.2 base. The shared-everything threads gate
🧵② is deliberately absent (out of scope). -/
structure Features where
  /-- 🔀 async functions, `stream`, `future`, the core concurrency builtins. -/
  async_ : Bool := false
  /-- 🗺️ `map<K, V>`. -/
  map : Bool := false
  /-- 🏷️ `implements` and `external-id` annotations. -/
  implements : Bool := false
  /-- 🔧 fixed-length lists `list<T, N>`. -/
  fixedLists : Bool := false
  /-- 📝 the `error-context` type and builtins. -/
  errorContext : Bool := false
  /-- 🚝 more canonical options on async builtins (sync stream/future ops, async
  cancels). -/
  moreAsyncBuiltins : Bool := false
  /-- 🚟 stackful async lift (`async` without `callback`). -/
  stackful : Bool := false
  /-- 🧵 cooperative thread builtins (`thread.new-indirect`, `thread.suspend`, ...). -/
  threads : Bool := false
  /-- ➡️ `stream.forward` / `future.forward`. -/
  forward : Bool := false
  /-- 🐘 memory64 in the ABI (`i64` addresses, resource reps and context slots). -/
  memory64 : Bool := false
  /-- 📡 `[get]` / `[set]` names. -/
  getters : Bool := false
  /-- 🔗 canonical interface names and `versionsuffix`. -/
  canonicalNames : Bool := false
  /-- 🪙 value imports/exports, value definitions, component `start`. -/
  values : Bool := false
  /-- 🪺 nested namespaces and packages in names. -/
  nestedNames : Bool := false
  deriving Repr, DecidableEq, BEq

namespace Features

/-- The ungated WASI 0.2 base: every gate off. -/
def p2 : Features := {}

/-- WASI 0.3.x (Preview 3): 🔀 (0.3.0) plus 🗺️ and 🏷️ (0.3.1). -/
def p3 : Features := { async_ := true, map := true, implements := true }

/-- `p3` plus the unstable gates implemented by `definitions.py` and wasmtime:
📝 🔧 🚝 🚟 🧵 ➡️ 🐘. -/
def p3plus : Features :=
  { p3 with errorContext := true, fixedLists := true, moreAsyncBuiltins := true,
            stackful := true, threads := true, forward := true, memory64 := true }

/-- Every modelled gate on. -/
def all : Features :=
  { async_ := true, map := true, implements := true, fixedLists := true,
    errorContext := true, moreAsyncBuiltins := true, stackful := true, threads := true,
    forward := true, memory64 := true, getters := true, canonicalNames := true,
    values := true, nestedNames := true }

/-- Pointwise implication: every gate enabled in `a` is enabled in `b`. -/
def le (a b : Features) : Prop :=
  (a.async_ = true → b.async_ = true) ∧ (a.map = true → b.map = true) ∧
  (a.implements = true → b.implements = true) ∧
  (a.fixedLists = true → b.fixedLists = true) ∧
  (a.errorContext = true → b.errorContext = true) ∧
  (a.moreAsyncBuiltins = true → b.moreAsyncBuiltins = true) ∧
  (a.stackful = true → b.stackful = true) ∧ (a.threads = true → b.threads = true) ∧
  (a.forward = true → b.forward = true) ∧ (a.memory64 = true → b.memory64 = true) ∧
  (a.getters = true → b.getters = true) ∧
  (a.canonicalNames = true → b.canonicalNames = true) ∧
  (a.values = true → b.values = true) ∧ (a.nestedNames = true → b.nestedNames = true)

instance : LE Features := ⟨le⟩

instance (a b : Features) : Decidable (le a b) := by
  unfold le
  infer_instance

instance (a b : Features) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (le a b))

end Features

/-! ## Limits -/

/-- Numeric limits of the Canonical ABI. The handle/thread table limit is the fixed
`Runtime.Table.maxLength` (REF `Table.MAX_LENGTH`; wasmtime agrees), not a field. -/
structure Limits where
  /-- Maximum string byte length (REF `MAX_STRING_BYTE_LENGTH`). -/
  maxStringBytes : Nat
  /-- Maximum list byte length (REF `MAX_LIST_BYTE_LENGTH`). -/
  maxListBytes : Nat
  /-- Maximum stream/future buffer length (REF `Buffer.MAX_LENGTH`). -/
  maxBufferLength : Nat
  /-- Backpressure counter bound (REF `backpressure.inc` traps at `2^16`). -/
  maxBackpressure : Nat
  /-- Number of `context.get/set` slots (REF `ContextLocalStorage.LENGTH`). -/
  maxContextSlots : Nat
  deriving Repr, DecidableEq, BEq

namespace Limits

/-- The `definitions.py` limits: this is the specification. -/
def spec : Limits where
  maxStringBytes := ABI.maxStringByteLength
  maxListBytes := 2 ^ 28 - 1
  maxBufferLength := AsyncRef.bufferMaxLength
  maxBackpressure := AsyncRef.backpressureLimit
  maxContextSlots := AsyncRef.contextSlotCount

/-- wasmtime `a7b4f29`: strings up to `2^31-1` bytes, lists up to `2^32-1` bytes
(`crates/environ/src/fact/trampoline.rs`); the rest as `spec`. Differential replay only. -/
def wasmtime : Limits :=
  { spec with maxStringBytes := 2 ^ 31 - 1, maxListBytes := 2 ^ 32 - 1 }

end Limits

/-! ## Quirks -/

/-- Implementation quirks, all off by default. **Only `Quirks.none` is the
specification.** The wasmtime quirks reproduce behaviour of wasmtime `a7b4f29` that the
reference (component-model `a25fc0b`) forbids or does not exhibit
(docs/projects/wasm-components.md, divergences 2-5; divergence 1 is `Limits.wasmtime`); they are for differential replay and are *not*
refinements of the specification. -/
structure Quirks where
  /-- Raw REF behaviour of decoding a `latin1+utf16` tag with the destination pointer width
  (deviation D-a). -/
  refUtf16TagBug : Bool := false
  /-- wasmtime's weaker `task.return` option check: no `memory` option matches any
  (`task_return`, `crates/wasmtime/src/runtime/component/concurrent.rs`). -/
  weakTaskReturnMemCheck : Bool := false
  /-- wasmtime releases borrow lends at the callee's `task.return` rather than at
  subtask resolution delivery (`validate_scope_exit`). -/
  lendReleaseAtReturn : Bool := false
  /-- wasmtime has no `num_waiting_to_enter` fairness check on entry
  (`GuestCall::is_ready`, `crates/wasmtime/src/runtime/component/concurrent.rs`). -/
  noEntryFairness : Bool := false
  /-- wasmtime's `*-then-promote` only promotes yield-ready threads
  (`resume_thread`, `crates/wasmtime/src/runtime/component/concurrent.rs`). -/
  promoteYieldOnly : Bool := false
  deriving Repr, DecidableEq, BEq

namespace Quirks

/-- The specification: no quirks. -/
def none : Quirks := {}

/-- wasmtime `a7b4f29` replay: all wasmtime quirks on; `refUtf16TagBug` off. The size limits
are not a quirk: a wasmtime replay passes `Limits.wasmtime` as the `lim` argument. -/
def wasmtime : Quirks :=
  { weakTaskReturnMemCheck := true, lendReleaseAtReturn := true, noEntryFairness := true,
    promoteYieldOnly := true }

end Quirks

/-! ## Profiles -/

/-- Which oracle answers are admissible.
* `nondet`: every behaviour the reference's nondeterminism and prose admit (e.g. a
  lowered NaN may be any NaN, including the input bits: wasmtime passthrough);
* `refStrict`: as `nondet`, but NaN bits on lowering are restricted to the range of
  REF `random_nan_bits`;
* `deterministic`: REF `DETERMINISTIC_PROFILE` (canonical NaN, ...). -/
inductive ProfileKind where
  | nondet
  | refStrict
  | deterministic
  deriving Repr, DecidableEq, BEq

end Silmaril.Wasm.Component
