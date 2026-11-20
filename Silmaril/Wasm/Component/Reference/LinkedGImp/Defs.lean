module

public import Silmaril.Wasm.Component.Reference.LinkedGRef.Defs

/-!
# The importer's side of linking with an abstract exporter: definitions

**Scope.** The exporter interface `ExpSpec.RefAdeq` of `LinkedGRef` (R1–R5), as used by an
importer running beside the exporter in the shared core store of the reference machine
(`Machine.Step` over `core3P P`).

## Why R1–R5 do not suffice for the importer's side

The importer keeps the exporter's `Hold` through R1 (`Frame.agree`): its steps must leave the
exporter's footprint `F` unchanged (`CoreFoot.Agree`). Its steps allocate structs and arrays at
the end of the shared store, so this needs `F` to contain no address that is not yet allocated.
R1–R5 do not say so: from any data `d` meeting R1–R5, the data `d∞` with
`d∞.Hold pl s S F := ∃ F₀, d.Hold pl s S F₀ ∧ F.gl = F₀.gl ∧ (∀ a, F₀.ar a → F.ar a) ∧
∀ a, F.st a` (the same placements, records and instances; the footprint owns **every** struct
address) meets R1–R5 as well (R1: `Agree` on all structs is equality of the struct lists, so
`d`'s R1 applies to `F₀ ⊆ F`; R2/R3: `Within F₀` implies `Within F`, and
`⟨F₀'.gl, F.ar ∪ F₀'.ar, everything⟩` grows from `F` by fresh addresses; R4 with
`⟨F₀.gl, F₀.ar, everything⟩`; R5 is `d`'s). With `d∞` no importer that allocates or owns a
struct has a footprint disjoint from the exporter's, and an importer's `struct.new` breaks
`Agree`, so no importer invariant can be kept through R1 (`ExpSpec.refAdeq_allStructs` in
`Thms`; there `d∞`'s footprint `F` has `F₀`'s globals and at least `F₀`'s arrays).

**The correction** is one more law, `RefData.Bounded`: the footprint of a `Hold` lies inside
the allocated structs and arrays of its core store (globals are never allocated by a run and
are unconstrained). A simple exporter's data meets it (`Thms`); `RefAdeqB` is R1–R5 with it.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

/-- **`F` lies inside the allocated part of `σ`**: its structs and arrays are allocated. -/
structure CoreFoot.Bounded {H : Type} (F : CoreFoot) (σ : Store H) : Prop where
  st : ∀ a, F.st a → a < σ.structs.length
  ar : ∀ a, F.ar a → a < σ.arrays.length

/-- **R6: footprints are allocated**: the footprint of every `Hold` lies inside the allocated
structs and arrays of its core store. -/
def ExpSpec.RefData.Bounded {P : Profile} {e : ExpSpec} (d : e.RefData P) : Prop :=
  ∀ (pl : d.Pl) (s : e.St) (S : RefStore (core3P P)) (F : CoreFoot), d.Hold pl s S F →
    F.Bounded (S.core : Store (CanonHost (core3P P)))

/-- **The reference interface of an exporter, with allocated footprints** (R1–R6). -/
def ExpSpec.RefAdeqB (P : Profile) (e : ExpSpec) : Prop :=
  ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.Bwd ∧ d.Init ∧ d.Resume ∧ d.Bounded

end Silmaril.Wasm.Component.Reference
