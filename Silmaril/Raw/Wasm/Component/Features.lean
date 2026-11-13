module

public import Silmaril.Wasm.Component.Reference.Features.Defs

public import Silmaril.Raw.Wasm.Component.ABI.String
public import Silmaril.Raw.Wasm.Component.Async.Codes

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

namespace Features

theorem le_refl (a : Features) : le a a := by
  simp only [le, imp_self, and_self]

theorem le_trans {a b c : Features} (hab : le a b) (hbc : le b c) : le a c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hab
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hbc
  exact ⟨g1 ∘ h1, g2 ∘ h2, g3 ∘ h3, g4 ∘ h4, g5 ∘ h5, g6 ∘ h6, g7 ∘ h7, g8 ∘ h8,
    g9 ∘ h9, g10 ∘ h10, g11 ∘ h11, g12 ∘ h12, g13 ∘ h13, g14 ∘ h14⟩

theorem p2_le (a : Features) : le p2 a := by
  simp only [le, p2, Bool.false_eq_true, false_implies, and_self]

theorem le_all (a : Features) : le a all := by
  simp only [le, all, implies_true, and_self]

theorem p2_le_p3 : le p2 p3 := by decide

theorem p3_le_p3plus : le p3 p3plus := by decide

theorem p3plus_le_all : le p3plus all := by decide

end Features

/-! ## Limits -/

namespace Limits

theorem spec_maxStringBytes_eq : spec.maxStringBytes = ABI.maxStringByteLength := rfl
theorem spec_maxListBytes_eq : spec.maxListBytes = 2 ^ 28 - 1 := rfl
theorem spec_maxBufferLength_eq : spec.maxBufferLength = AsyncRef.bufferMaxLength := rfl
theorem spec_maxBackpressure_eq : spec.maxBackpressure = AsyncRef.backpressureLimit := rfl
theorem spec_maxContextSlots_eq : spec.maxContextSlots = AsyncRef.contextSlotCount := rfl

theorem spec_maxStringBytes : spec.maxStringBytes = 268435455 := rfl

end Limits

/-! ## Quirks -/

namespace Quirks

end Quirks

/-! ## Profiles -/

end Silmaril.Wasm.Component
