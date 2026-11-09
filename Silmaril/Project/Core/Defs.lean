module

public import Silmaril.Formats.Bytes

/-!
# Silmaril projects: the definitions

The object-level vocabulary of a silmaril project.
The registry that names these objects (the `silmaril` command and the dump) is
`Silmaril.Project.Registry.Defs`; `Silmaril.Project.Defs` is the header importing both.

* An `ArtifactType` is what kind of content an artifact has (its carrier). `blob` is bytes
  (CID codec `raw`); the type stays the open extension point for later artifact kinds.
* A `Format T V` is a partial parser from the carrier of `T` to a value type `V`, with an
  optional printer. Its laws are the propositions `RoundTrip` and `SoundFor`.
* `Equivalent F G a b`: two artifacts parse, through formats into one value type (a *data
  model*), to the same value.
* `Holds 𝓜 s a`: the judgement template `𝓜 ⊨ a : s`.
* A `Value V` is bytes read under a format into `V`; `Value.Parses`, `Value.Satisfies`,
  `Value.Is` and `Value.Agrees` are how statements talk about it. Their lemmas and
  the tactic `silmaril_decide` are in `Silmaril.Project.Core.Thms`.
-/

@[expose] public section

namespace Silmaril.Project

/-- What kind of content an artifact has. -/
structure ArtifactType : Type 1 where
  /-- The type of an artifact's content. -/
  Carrier : Type

/-- A blob: bytes identified by a raw-codec CID. Where it was found (a path) is metadata. -/
def blob : ArtifactType := ⟨Silmaril.Formats.Bytes⟩

/-- A named partial parser from an artifact type to a value type, with an optional printer. -/
structure Format (T : ArtifactType) (V : Type) : Type where
  /-- Read an artifact; `none` rejects it. -/
  parse : T.Carrier → Option V
  /-- An optional printer; `none` when the format has none. -/
  print : Option (V → Option T.Carrier) := none

namespace Format

variable {T : ArtifactType} {V W : Type}

/-- Compose a format with a value-level decoder (S-expressions to a WAT module, …). The
composite has no printer. -/
def andThen (F : Format T V) (d : V → Option W) : Format T W :=
  ⟨fun a => F.parse a >>= d, none⟩

/-- Law `roundtrip`: whatever the printer produces parses back to the printed value. -/
def RoundTrip (F : Format T V) : Prop :=
  ∀ p, F.print = some p → ∀ v a, p v = some a → F.parse a = some v

/-- Law `sound`: the parser is sound for a specification relation. -/
def SoundFor (F : Format T V) (R : T.Carrier → V → Prop) : Prop :=
  ∀ a v, F.parse a = some v → R a v

end Format

/-- Two artifacts are equivalent under formats into one value type (a data model) when both
parse to the same value. -/
def Equivalent {S T : ArtifactType} {V : Type} (F : Format S V) (G : Format T V)
    (a : S.Carrier) (b : T.Carrier) : Prop :=
  ∃ v, F.parse a = some v ∧ G.parse b = some v

/-- The judgement template `𝓜 ⊨ a : s`: every model in the class satisfies the spec on `a`. -/
def Holds {M A : Type} (𝓜 : M → Prop) (s : M → A → Prop) (a : A) : Prop :=
  ∀ m, 𝓜 m → s m a

/-- The identity format `bytes`: a blob read as its bytes. -/
def bytes : Format blob Silmaril.Formats.Bytes := ⟨some, some some⟩

/-- A value: bytes read under a blob format. `silmaril value` declares one per source. -/
structure Value (V : Type) where
  /-- The format the bytes are read under. -/
  format : Format blob V
  /-- The bytes (an `include_bytes` of the source artifact). -/
  bytes : Silmaril.Formats.Bytes

namespace Value

variable {V : Type}

/-- The parse of a value's bytes. -/
def parse (x : Value V) : Option V := x.format.parse x.bytes

/-- The obligation `X.parses`: the bytes parse. -/
def Parses (x : Value V) : Prop := x.parse.isSome = true

/-- The bytes parse and the value satisfies `P`. Not vacuous: it implies `Parses`. -/
def Satisfies (x : Value V) (P : V → Prop) : Prop := ∃ v, x.parse = some v ∧ P v

/-- A certificate: the value is `v`. -/
def Is (x : Value V) (v : V) : Prop := x.parse = some v

/-- The obligation `X.agrees.k`: two sources denote the same value. -/
def Agrees (x y : Value V) : Prop := Equivalent x.format y.format x.bytes y.bytes

end Value

end Silmaril.Project
