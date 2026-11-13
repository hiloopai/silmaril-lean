module

public import Silmaril.Wasm.Component.Reference.Runtime.Builtin.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Options
public import Silmaril.Raw.Wasm.Component.Syntax.Basic
public import Silmaril.Raw.Wasm.Component.ABI.Predicates

/-!
# Resolved canonical built-ins and canon host code

* `ResolvedBuiltin E` mirrors `Syntax.Builtin` (the `canon` built-ins of `Binary.md` at
  component-model `a25fc0b`) constructor by constructor, with every immediate resolved to a
  runtime entity: resource type indices become `RtId`s, component type indices of
  `stream`/`future` built-ins become their element type `Option (WIT.ClosedType RtId)`,
  `task.return`'s result type becomes a closed type, `canonopt` lists become `CanonOpts E`,
  core memory indices become `E.MemAddr`, and `thread.new-indirect`'s core type and table
  indices become the expected flat function type `(func (param T))` and an `E.TableAddr`.
  Boolean `async_` flags (`subtask.cancel`, `*.cancel-read/write`) are kept as they are.
* `CanonHost E` is the host-code identifier type `H` of the shared core store
  (`E.Store (CanonHost E)`): one per lowering site. `lowered` is a `canon lower` of a component
  function, `builtin` a canon built-in (with the instance it was defined in), and `embedder` a
  host function supplied directly by the embedding.
* `CanonHost.coreType` is the flat core signature each site is allocated with
  (`E.allocHost` converts it with `E.ofFlatType`): for `lowered`, REF
  `flatten_functype(opts, ft, 'lower')` (`ABI.flattenFunc`, definitions.py L2169-2175); for
  built-ins, the "`$f` is given type" clauses of `CanonicalABI.md` §Canonical Definitions (lines
  3770-4760 at `a25fc0b`), where `T`/`A` is the address type of the relevant memory (or `i32`
  without one, deviation D-g) and `U` that of `thread.new-indirect`'s table. Address types come from
  an `AddrTypes E` argument because they live in the core store.

Design notes:
* `resourceNew`/`resourceRep` also carry the resource's `rep : AddrType` (`i32`, or `i64` under
  🐘), which their core types `[rep] → [i32]` / `[i32] → [rep]` need; REF reads it from the
  type definition.
* `CanonHost.embedder` also carries its flat signature `ft`, so that `coreType` is total.

Not modelled here: validation of built-ins, resolution from syntax (instantiation items), and
any built-in behaviour (canon items). No claim is made that the signatures are validated.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

namespace ResolvedBuiltin

variable {E : CoreEngine}

end ResolvedBuiltin

namespace CanonHost

variable {E : CoreEngine}

/-- Every canon host site returns at most one core value (`ABI.flattenFunc_results_le_one`
for `lower`; by inspection of the table for built-ins). -/
theorem coreType_results_le_one (at_ : AddrTypes E) (h : CanonHost E)
    (hh : ∀ n ft, h ≠ .embedder n ft) : (h.coreType at_).results.length ≤ 1 := by
  cases h with
  | lowered => exact ABI.flattenFunc_results_le_one ..
  | builtin b =>
    cases b <;> simp only [coreType, ResolvedBuiltin.coreType, List.length_cons,
      List.length_nil] <;> first | omega | exact ABI.flattenFunc_results_le_one ..
  | embedder n ft => exact absurd rfl (hh n ft)

example (at_ : AddrTypes E) (t : Option (WIT.ClosedType RtId)) :
    (ResolvedBuiltin.streamNew t).coreType at_ = ⟨[], [.int .i64]⟩ := rfl

example (at_ : AddrTypes E) :
    (ResolvedBuiltin.streamRead none ({} : CanonOpts E)).coreType at_ =
      ⟨[.int .i32, .int .i32, .int .i32], [.int .i32]⟩ := rfl

/-- `canon lower` of `func(x: u32, s: string) -> u64` without options: three flat parameters
and the single flat `u64` result returned directly (no out-pointer). -/
example (at_ : AddrTypes E) :
    (CanonHost.lowered ⟨0⟩ ⟨[("x", .prim .u32), ("s", .prim .string)], some (.prim .u64), false⟩
      ({} : CanonOpts E) ⟨0⟩).coreType at_ =
      ⟨[.int .i32, .int .i32, .int .i32], [.int .i64]⟩ := by
  simp only [CanonHost.coreType, CanonOpts.abiOptions, CanonOpts.ptrType, Option.isSome_none]
  decide +kernel

/-- The same function lowered `async`: flat parameters (3 ≤ 4) plus a result out-pointer, and
the `i32` status result. -/
example (at_ : AddrTypes E) :
    (CanonHost.lowered ⟨0⟩ ⟨[("x", .prim .u32), ("s", .prim .string)], some (.prim .u64), true⟩
      ({ async_ := true } : CanonOpts E) ⟨0⟩).coreType at_ =
      ⟨[.int .i32, .int .i32, .int .i32, .int .i32], [.int .i32]⟩ := by
  simp only [CanonHost.coreType, CanonOpts.abiOptions, CanonOpts.ptrType, Option.isSome_none]
  decide +kernel

end CanonHost

end Silmaril.Wasm.Component.Runtime
