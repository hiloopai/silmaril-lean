module

public import Silmaril.Wasm.Component.Reference.Wasm.Semantics.Defs
import Silmaril.Wasm.Component.Reference.Wasm.Semantics.Memory.Defs

/-!
# The laws of a `WasmSemantics`, and the lawfulness of its engine view

`WasmSemantics.Lawful` is what a semantics must prove. `WasmSemantics.toCoreEngine_lawful` is
the payoff: a semantics proving these fourteen obligations gets all twenty-three
`Component.Engine.CoreEngine.Lawful` fields for its engine view, for free.

The fourteen are not a renaming of the twenty-three. Two groups collapse.

* **Parking (3 → 1).** `CoreEngine.Lawful` asks separately that a `returned`, a `callout` and a
  `stuck` thread take no internal step. The content is the single statement that *only running
  threads step* (`internal_running`), which is also exactly the form every engine's proof takes
  and the form `CoreEngine.status_running_of_internal` immediately recovers.
* **Linear memory (9 → 5).** Eight of the nine memory laws are consequences of the four
  pointwise coherence facts of `MemoryView.Lawful` (`Semantics/Memory.lean`), which are about
  `setInst`/`withData` alone and mention neither the component runtime nor store extension. The
  ninth, `memWrite_extends`, genuinely does mention function types, table address types and
  thread status, so it stays here.

The rest -- flat signatures, the `ExternSub` preorder, `asFunc?`/`ofFunc`, the three
store-extension laws and the five `allocHost` laws -- are carried across unchanged, because
they are already in semantics-level vocabulary.

Deliberately **not** a field: `CoreEngine.ResumeLawful` (resuming a parked thread leaves it
running or returned). It is false for every real engine in this development -- Lime1, V1, 2.0
and Core 3.0 all decline it, since an ill-typed host result can leave the resumed thread stuck
-- so building it into `WasmSemantics.Lawful` would make the class uninhabited in practice.
-/

@[expose] public section

namespace Silmaril.Wasm.Semantics

open Silmaril.Wasm.Component.Engine

namespace WasmSemantics

/-- The laws of a core-level WebAssembly semantics. See the module docstring for the two places
where these are genuinely weaker than `CoreEngine.Lawful`. -/
class Lawful (S : WasmSemantics) : Prop where
  /-- The flat signature of an embedded flat signature is itself. -/
  flatType?_ofFlatType : ∀ ft, S.flatType? (S.ofFlatType ft) = some ft
  /-- Only running threads step: a parked (returned, callout) or stuck activation is final for
  the host-free step relation. -/
  internal_running : ∀ {H : Type} {s : S.Store H} {t c'},
    S.Internal (s, t) c' → S.status s t = .running
  /-- `ExternSub` is reflexive. -/
  externSub_refl : ∀ τ, S.ExternSub τ τ
  /-- `ExternSub` is transitive. -/
  externSub_trans : ∀ {τ₁ τ₂ τ₃}, S.ExternSub τ₁ τ₂ → S.ExternSub τ₂ τ₃ → S.ExternSub τ₁ τ₃
  /-- A function address read back out of its external value is itself. -/
  asFunc?_ofFunc : ∀ a, S.asFunc? (S.ofFunc a) = some a
  /-- Stepping extends the store. -/
  internal_extends : ∀ {H : Type} {s s' : S.Store H} {t t'},
    S.Internal (s, t) (s', t') → S.Extends s s'
  /-- Instantiation extends the store. -/
  prepare_extends : ∀ {H : Type} {s s' : S.Store H} {m imps i st},
    S.prepare? s m imps = some (s', i, st) → S.Extends s s'
  /-- Host-function allocation extends the store. -/
  allocHost_extends : ∀ {H : Type} {s s' : S.Store H} {ft h a},
    S.allocHost s ft h = (s', a) → S.Extends s s'
  /-- The allocated address was not in use. -/
  allocHost_fresh : ∀ {H : Type} {s s' : S.Store H} {ft h a},
    S.allocHost s ft h = (s', a) → S.funcType? s a = none
  /-- Frame law: allocation changes no other function type. -/
  allocHost_frame : ∀ {H : Type} {s s' : S.Store H} {ft h a b},
    S.allocHost s ft h = (s', a) → b ≠ a → S.funcType? s' b = S.funcType? s b
  /-- The allocated address has the embedded flat type. -/
  allocHost_funcType : ∀ {H : Type} {s s' : S.Store H} {ft h a},
    S.allocHost s ft h = (s', a) → S.funcType? s' a = some (S.ofFlatType ft)
  /-- Invoking an allocated host function with matching arity is immediately a callout. -/
  allocHost_callout : ∀ {H : Type} {s s' : S.Store H} {ft h a} {args : List FlatValue},
    S.allocHost s ft h = (s', a) → args.length = ft.params.length →
      S.status s' (S.invoke a args) = .callout h args
  /-- The memory view is coherent. Eight of the nine `CoreEngine` memory laws follow. -/
  memView : S.mem.Lawful
  /-- A memory write extends the store: it is the one memory law that mentions function types,
  table address types and thread status, so it cannot live in `MemoryView`. -/
  memWrite_extends : ∀ {H : Type} {s s' : S.Store H} {m st bs},
    S.mem.write? s m st bs = some s' → S.Extends s s'

/-- A lawful semantics has a coherent memory view. -/
instance instMemoryViewLawful (S : WasmSemantics) [L : S.Lawful] : S.mem.Lawful := L.memView

/-- **The adapter is lawful.** A semantics satisfying `WasmSemantics.Lawful` gives a core engine
satisfying all twenty-three fields of `CoreEngine.Lawful`. -/
theorem toCoreEngine_lawful (S : WasmSemantics) [L : S.Lawful] : S.toCoreEngine.Lawful where
  flatType?_ofFlatType := L.flatType?_ofFlatType
  returned_no_step h step := by
    have e := h.symm.trans (L.internal_running step)
    simp at e
  callout_no_step h step := by
    have e := h.symm.trans (L.internal_running step)
    simp at e
  stuck_no_step h step := by
    have e := h.symm.trans (L.internal_running step)
    simp at e
  externSub_refl := L.externSub_refl
  externSub_trans := L.externSub_trans
  asFunc?_ofFunc := L.asFunc?_ofFunc
  internal_extends := L.internal_extends
  prepare_extends := L.prepare_extends
  allocHost_extends := L.allocHost_extends
  allocHost_fresh := L.allocHost_fresh
  allocHost_frame := L.allocHost_frame
  allocHost_funcType := L.allocHost_funcType
  allocHost_callout := L.allocHost_callout
  memWrite_extends := L.memWrite_extends
  memWrite_memSize h := MemoryView.size?_write? h
  memWrite_memAddrType h := MemoryView.addrType?_write? h
  memWrite_read h := MemoryView.read?_write? h
  memWrite_read_other h hd := MemoryView.read?_write?_other h hd
  memRead_isSome_iff := MemoryView.read?_isSome_iff
  memRead_size h := MemoryView.read?_size h
  memWrite_isSome_iff := MemoryView.write?_isSome_iff
  memAddrType_isSome_iff := MemoryView.addrType?_isSome_iff

end WasmSemantics

end Silmaril.Wasm.Semantics
