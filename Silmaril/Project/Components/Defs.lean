module

public import Silmaril.Project.Formats.Wit.Defs
public import Silmaril.Crypto.SHA256.Defs

/-!
# Component registry records

The Lean side of a registry of WebAssembly components in the style of wa.dev: a **release**
`namespace:name@version` (the package naming of WIT, warg and wasm-pkg-tools) whose content is
identified by its **SHA-256 digest** (the `sha256:<hex>` digests of OCI distribution and of
warg's package logs). The silmaril records it becomes (`docs/projects/wasm-wasi.md`):

| registry notion | silmaril record | Lean |
|---|---|---|
| release `ns:name@version`, digest `sha256:…` | `[[artifact]]` (keyed by CID; `sha256` an alias) | `Release`, `Release.Pins` |
| the release read as a component, a module, a WIT package | `[[value]]` under `wasm.component`, `wasm.module`, `wit.binary` | `Release.value` |
| the world of the release | `[[value]]` under `wasm.component.world` or `wasm.module.world` | `Release.world`, `Release.embeddedWorld` |
| how the release was built | `[[derivation]]` (op `compile`/`fetch`, toolchain, inputs) | `Build` |
| two builds of one source with different digests | a reproducibility finding | `ReproducibilityFinding` |

**Studying by hash.** A value is a function of the bytes, so identical bytes give identical
digests and identical values, worlds and verdicts (`Silmaril.Project.Components.Thms`). The
converse, that one digest names one blob, is SHA-256 collision resistance, a computational
assumption no proof provides: the theorems that use it take `CollisionFree b₁ b₂` for the two
blobs at hand. `mor project check` establishes the digest of every registered file (rule P1),
outside Lean; in Lean, `Release.Pins` is decidable but the kernel evaluates SHA-256 only on
small blobs.

Digests are written in lowercase hex (`Digest.hex`, `Digest.ofHex?`, a proved round trip).
-/

@[expose] public section
namespace Silmaril.Project.Components

open Silmaril.Wasm

/-! ## Digests -/

/-- A SHA-256 digest (32 bytes for a digest computed by `Digest.of`). -/
structure Digest where
  bytes : List UInt8
  deriving Repr, DecidableEq, Inhabited

/-- The SHA-256 digest of a blob. -/
def Digest.of (b : Silmaril.Formats.Bytes) : Digest := ⟨Silmaril.Crypto.sha256 b.data.data.toList⟩

/-- A lowercase hex digit. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The value of a lowercase hex digit. -/
def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else none

/-- The two hex digits of a byte. -/
def byteHex (b : UInt8) : List Char := [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- The byte of two lowercase hex digits. -/
def byteOfHex? (a b : Char) : Option UInt8 := do
  let x ← hexVal? a
  let y ← hexVal? b
  pure (UInt8.ofNat (16 * x + y))

/-- Bytes from pairs of lowercase hex digits. -/
def ofHexChars? : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← byteOfHex? a b
    let r ← ofHexChars? rest
    pure (x :: r)
  | [_] => none

/-- A digest in lowercase hex (64 digits for SHA-256), as in `artifacts.toml`. -/
def Digest.hex (d : Digest) : String := String.ofList (d.bytes.flatMap byteHex)

/-- A digest from lowercase hex. -/
def Digest.ofHex? (s : String) : Option Digest := (ofHexChars? s.toList).map Digest.mk

/-! ## Releases -/

/-- A release of a registry package: `ns:name@version` (a WIT package name with its version)
and the SHA-256 digest of its content. -/
structure Release where
  /-- The package and version, `ns:name@version`. -/
  pkg : Wit.PackageName
  /-- The digest of the released blob. -/
  digest : Digest
  deriving Repr, DecidableEq, Inhabited

/-- The reference `ns:name@version` of a release. -/
def Release.ref (r : Release) : String :=
  r.pkg.ns ++ ":" ++ r.pkg.name ++ (match r.pkg.version with
    | some v => "@" ++ Wit.Version.str v
    | none => "")

/-- The blob `b` is the content of the release `r`: its digest is the release's. -/
def Release.Pins (r : Release) (b : Silmaril.Formats.Bytes) : Prop := Digest.of b = r.digest

instance (r : Release) (b : Silmaril.Formats.Bytes) : Decidable (r.Pins b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The release's content read under a format (a component, a module, a WIT package). -/
def Release.value {V : Type} (_ : Release) (F : Format blob V) (b : Silmaril.Formats.Bytes) :
    Value V := ⟨F, b⟩

/-- The world of a released component (`wasm.component.world`). -/
def Release.world (r : Release) (b : Silmaril.Formats.Bytes) : Value Wit.Project.WorldType :=
  r.value Silmaril.Project.Formats.wasmComponentWorld b

/-- The world a released core module embeds (`wasm.module.world`), such as the
`wasi_snapshot_preview1` adapter. -/
def Release.embeddedWorld (r : Release) (b : Silmaril.Formats.Bytes) :
    Value Silmaril.Project.Formats.EmbeddedWorld :=
  r.value Silmaril.Project.Formats.wasmModuleWorld b

/-- The collision-resistance assumption for two blobs: equal digests only for equal blobs.
Not provable (SHA-256 is not injective); it holds trivially for one blob (`b₁ = b₂`). -/
def CollisionFree (b₁ b₂ : Silmaril.Formats.Bytes) : Prop := Digest.of b₁ = Digest.of b₂ → b₁ = b₂

/-! ## Builds and reproducibility -/

/-- The provenance of a built artifact, as a `[[derivation]]` records it: the digest of the
source, the toolchain (name and version of each tool), the flags and the digest of the output. -/
structure Build where
  source : Digest
  toolchain : List (String × String)
  flags : List String
  output : Digest
  deriving Repr, DecidableEq, Inhabited

/-- What a build depends on, if it is reproducible: source, toolchain and flags. -/
def Build.recipe (d : Build) : Digest × List (String × String) × List String :=
  (d.source, d.toolchain, d.flags)

/-- **A reproducibility finding**: two builds of one recipe (same source, toolchain and flags)
whose outputs have different digests. -/
def ReproducibilityFinding (d₁ d₂ : Build) : Prop := d₁.recipe = d₂.recipe ∧ d₁.output ≠ d₂.output

instance (d₁ d₂ : Build) : Decidable (ReproducibilityFinding d₁ d₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A set of builds is reproducible when the output is a function of the recipe. -/
def Reproducible (bs : List Build) : Prop :=
  ∃ f : Digest × List (String × String) × List String → Digest, ∀ d ∈ bs, d.output = f d.recipe

/-- Every reproducibility finding among a list of builds. -/
def findings (bs : List Build) : List (Build × Build) :=
  bs.flatMap fun d₁ => (bs.filter fun d₂ => decide (ReproducibilityFinding d₁ d₂)).map (d₁, ·)

end Silmaril.Project.Components
