module

public import Silmaril.Wasm.Component.Param.Defs

/-!
# Hereditary soundness properties of a core engine: definitions

`Param.RefToSpec E ofCore P` (and its three siblings) is a property of the reference component
machine over **one** engine record `E`. A restriction `restrict E r` is a different record, and
the machine's types are indexed by the whole record: the core store of the machine over
`restrict E r` has host type `CanonHost (restrict E r)`, a different inductive from
`CanonHost E`. So `RefToSpec E → RefToSpec (restrict E r)` is not provable for an abstract `E`
without a transport of every machine structure along a host-type change, which an abstract
`CoreEngine` does not support (it has no `Store.mapH`; see Track I4 in `docs/projects/spectec/README.md`).

The machine uses the engine's internal step only positively (the premise of
`Step.coreInternal`; a core activation without an internal step takes no step and produces no
outcome) and never consults `Valid`. So the property that proofs of `RefToSpec` actually
establish, and the one that is closed under restriction, is the **hereditary** one:

* `withRel E V IR`: the engine `E` with validity `V` and internal step `IR`. Every other field
  is `E`'s. `E` itself is `withRel E E.Valid E.Internal`, and `restrict E r` is
  `withRel E (E.Valid ∧ r.Mod) (E.Internal ∧ r.Rt)`, both definitionally;
* `SubRel E IR`: `IR` is contained in `E.Internal`;
* `RefToSpecH E ofCore P`: `RefToSpec (withRel E V IR) ofCore P` for every validity `V` and
  every `IR` contained in `E.Internal`; likewise `SeqRefToSpecH`, `Link2SoundH` and
  `Link2SoundSeqH`.

`Hered.Thms` proves that the hereditary properties imply the plain ones, are closed under
`restrict` and `withRel` (by definition, with no transport), that Core 3.0 has all four at
every profile (they are exactly the `core3R` theorems of Tracks I4/I5), and soundness of the
IR for every restriction of every engine with the hereditary properties.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Hered

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

/-- **The engine `E` with validity `V` and internal step `IR`.** Every other field (stores,
threads, instantiation, memories, tables, status, resumption) is `E`'s. -/
abbrev withRel (E : Engine) (V : E.Module → Prop)
    (IR : {H : Type} → E.Config H → E.Config H → Prop) : Engine :=
  { E with Valid := V, Internal := IR }

instance withRel_decExternSub (E : Engine) [d : ∀ a b, Decidable (E.ExternSub a b)]
    (V : E.Module → Prop) (IR : {H : Type} → E.Config H → E.Config H → Prop) :
    ∀ a b, Decidable ((withRel E V IR).ExternSub a b) := d

/-- The internal step `IR` is contained in the engine's internal step. -/
def SubRel (E : Engine) (IR : {H : Type} → E.Config H → E.Config H → Prop) : Prop :=
  ∀ {H : Type} {c c' : E.Config H}, IR c c' → E.Internal c c'

variable (E : Engine) [∀ a b, Decidable (E.ExternSub a b)]
  (ofCore : Silmaril.Wasm.Module → E.Module) (P : Profile)

/-- **The hereditary reference-machine half**: every engine obtained from `E` by changing its
validity and shrinking its internal step has the reference-machine half `RefToSpec`. -/
def RefToSpecH : Prop :=
  ∀ (V : E.Module → Prop) (IR : {H : Type} → E.Config H → E.Config H → Prop), SubRel E IR →
    RefToSpec (withRel E V IR) ofCore P

/-- The hereditary reference-machine half for sequences of calls. -/
def SeqRefToSpecH : Prop :=
  ∀ (V : E.Module → Prop) (IR : {H : Type} → E.Config H → E.Config H → Prop), SubRel E IR →
    SeqRefToSpec (withRel E V IR) ofCore P

/-- Hereditary soundness of two linked components. -/
def Link2SoundH : Prop :=
  ∀ (V : E.Module → Prop) (IR : {H : Type} → E.Config H → E.Config H → Prop), SubRel E IR →
    Link2Sound (withRel E V IR) ofCore P

/-- Hereditary soundness of two linked components for sequences of calls. -/
def Link2SoundSeqH : Prop :=
  ∀ (V : E.Module → Prop) (IR : {H : Type} → E.Config H → E.Config H → Prop), SubRel E IR →
    Link2SoundSeq (withRel E V IR) ofCore P

end Silmaril.Wasm.Component.Hered
