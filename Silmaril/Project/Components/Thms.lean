module

public import Silmaril.Project.Components.Defs
public import Silmaril.Project.Core.Thms
public import Silmaril.Project.Formats.Component.Thms

/-!
# Component registry records: studying by hash, reproducibility

* `Digest.ofHex?_hex`: the hex spelling of a digest reads back.
* **Identical blobs, identical everything.** `Release.digest_eq_of_pins`: a blob pins one
  digest, so two releases of the same bytes (a re-publication under another name or version)
  have one digest; `Release.value_eq_of_bytes_eq`: their values under any format are equal, and
  so are their worlds and the answers of every problem about them.
* **Different digests, different blobs** (`Release.bytes_ne_of_digest_ne`), unconditionally.
* **Equal digests, equal values** (`Release.bytes_eq_of_digest_eq`, `Release.parse_eq_of_digest_eq`,
  `Release.satisfies_iff_of_digest_eq`, `Release.world_parse_eq_of_digest_eq`) under the
  collision-resistance assumption `CollisionFree b₁ b₂` for the two blobs.
* **Reproducibility.** `not_reproducible_of_finding`: a finding refutes `Reproducible`;
  `reproducible_iff`: builds are reproducible exactly when no two of them form a finding, and
  `findings_eq_nil_iff`: exactly when `findings` (a computable list) is empty.
* **Example.** The release `silmaril:run@0.1.0` of `examples/project-formats/component-run.wasm`:
  its digest is checked by one kernel evaluation of SHA-256 (about 1 s on 138 bytes; the hex
  is the one `sha256sum` prints), and its value under `wasm.component` parses. Two illustrative
  builds of one recipe with different outputs form a finding, so they are not reproducible.
-/

@[expose] public section
namespace Silmaril.Project.Components

open Silmaril.Wasm

/-! ## Hex -/

theorem byteOfHex?_byteHex : ∀ b : UInt8,
    byteOfHex? (hexDigit (b.toNat / 16)) (hexDigit (b.toNat % 16)) = some b := by
  decide

theorem ofHexChars?_flatMap (l : List UInt8) : ofHexChars? (l.flatMap byteHex) = some l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.flatMap_cons, byteHex, List.cons_append, List.nil_append, ofHexChars?,
      byteOfHex?_byteHex, ih]
    rfl

theorem Digest.ofHex?_hex (d : Digest) : Digest.ofHex? d.hex = some d := by
  simp [Digest.ofHex?, Digest.hex, ofHexChars?_flatMap]

/-! ## Studying by hash -/

namespace Release

variable {r₁ r₂ : Release} {b₁ b₂ : Silmaril.Formats.Bytes}

/-- A blob has one digest: two releases pinned to the same bytes have the same digest. -/
theorem digest_eq_of_pins (h₁ : r₁.Pins b₁) (h₂ : r₂.Pins b₁) : r₁.digest = r₂.digest :=
  h₁.symm.trans h₂

/-- Values are functions of the bytes: whatever the release names, the same bytes under the
same format are the same value. -/
theorem value_eq_of_bytes_eq {V : Type} (F : Format blob V) (h : b₁ = b₂) :
    r₁.value F b₁ = r₂.value F b₂ := by
  subst h; rfl

/-- Different digests are different blobs (no assumption). -/
theorem bytes_ne_of_digest_ne (h₁ : r₁.Pins b₁) (h₂ : r₂.Pins b₂) (h : r₁.digest ≠ r₂.digest) :
    b₁ ≠ b₂ := by
  rintro rfl
  exact h (digest_eq_of_pins h₁ h₂)

/-- Equal digests are equal blobs, under collision resistance for the two blobs. -/
theorem bytes_eq_of_digest_eq (hc : CollisionFree b₁ b₂) (h₁ : r₁.Pins b₁) (h₂ : r₂.Pins b₂)
    (h : r₁.digest = r₂.digest) : b₁ = b₂ :=
  hc (h₁.trans (h.trans h₂.symm))

/-- Equal digests, equal parses under any format (collision resistance for the two blobs). -/
theorem parse_eq_of_digest_eq {V : Type} (F : Format blob V) (hc : CollisionFree b₁ b₂)
    (h₁ : r₁.Pins b₁) (h₂ : r₂.Pins b₂) (h : r₁.digest = r₂.digest) :
    (r₁.value F b₁).parse = (r₂.value F b₂).parse := by
  rw [value_eq_of_bytes_eq (r₂ := r₂) F (bytes_eq_of_digest_eq hc h₁ h₂ h)]

/-- Equal digests, equal answers: a property holds of one release's value exactly when it
holds of the other's (collision resistance for the two blobs). -/
theorem satisfies_iff_of_digest_eq {V : Type} (F : Format blob V) (P : V → Prop)
    (hc : CollisionFree b₁ b₂) (h₁ : r₁.Pins b₁) (h₂ : r₂.Pins b₂)
    (h : r₁.digest = r₂.digest) :
    (r₁.value F b₁).Satisfies P ↔ (r₂.value F b₂).Satisfies P := by
  rw [value_eq_of_bytes_eq (r₂ := r₂) F (bytes_eq_of_digest_eq hc h₁ h₂ h)]

/-- Equal digests, equal worlds (collision resistance for the two blobs). -/
theorem world_parse_eq_of_digest_eq (hc : CollisionFree b₁ b₂) (h₁ : r₁.Pins b₁)
    (h₂ : r₂.Pins b₂) (h : r₁.digest = r₂.digest) :
    (r₁.world b₁).parse = (r₂.world b₂).parse :=
  parse_eq_of_digest_eq _ hc h₁ h₂ h

end Release

/-! ## Reproducibility -/

/-- A finding refutes reproducibility of any set of builds containing both builds. -/
theorem not_reproducible_of_finding {bs : List Build} {d₁ d₂ : Build} (h : ReproducibilityFinding d₁ d₂)
    (h₁ : d₁ ∈ bs) (h₂ : d₂ ∈ bs) : ¬ Reproducible bs := by
  rintro ⟨f, hf⟩
  exact h.2 ((hf d₁ h₁).trans (h.1 ▸ (hf d₂ h₂).symm))

/-- Builds are reproducible exactly when no two of them form a finding. -/
theorem reproducible_iff {bs : List Build} :
    Reproducible bs ↔ ∀ d₁ ∈ bs, ∀ d₂ ∈ bs, ¬ ReproducibilityFinding d₁ d₂ := by
  constructor
  · intro hr d₁ h₁ d₂ h₂ hf
    exact not_reproducible_of_finding hf h₁ h₂ hr
  · intro hn
    refine ⟨fun k => ((bs.find? fun d => decide (d.recipe = k)).map Build.output).getD default, ?_⟩
    intro d hd
    have hs : (bs.find? fun d' => decide (d'.recipe = d.recipe)).isSome := by
      rw [List.find?_isSome]
      exact ⟨d, hd, by simp⟩
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
    have hem := List.mem_of_find?_eq_some he
    have hrec : e.recipe = d.recipe := by simpa using List.find?_some he
    show d.output = ((bs.find? fun d' => decide (d'.recipe = d.recipe)).map Build.output).getD default
    rw [he]
    by_contra hne
    exact hn e hem d hd ⟨hrec, Ne.symm (by simpa using hne)⟩

/-- The computable check: no findings exactly when the builds are reproducible. -/
theorem findings_eq_nil_iff {bs : List Build} : findings bs = [] ↔ Reproducible bs := by
  rw [reproducible_iff]
  simp [findings, List.flatMap_eq_nil_iff, List.filter_eq_nil_iff]

/-! ## Example -/

/-- `silmaril:run@0.1.0`, the release of `examples/project-formats/component-run.wasm`. -/
def runRelease : Release where
  pkg := { ns := "silmaril", name := "run", version := some { major := 0, minor := 1, patch := 0 } }
  digest := ((Digest.ofHex?
    "a0e91d45b494f00088010cb9c890851d0c29b4ad3f51bb907cfe89b68f3a8bd6").getD default)

theorem runRelease_ref : runRelease.ref = "silmaril:run@0.1.0" := by decide +kernel

theorem runRelease_pins : runRelease.Pins Silmaril.Project.Formats.runComponent := by
  decide +kernel

theorem runRelease_parses :
    (runRelease.value Silmaril.Project.Formats.wasmComponent
      Silmaril.Project.Formats.runComponent).Parses := by
  simp only [Release.value, Silmaril.Project.Value.Parses, Silmaril.Project.Value.parse]
  exact Silmaril.Project.Formats.runComponent_parses

/-- Two builds of one recipe with different outputs (illustrative: the source and output
digests are the zero digest and the digest of `component-run.wasm`). -/
def flakyBuilds : List Build :=
  [⟨⟨List.replicate 32 0⟩, [("wasm-tools", "1.263.0")], [], runRelease.digest⟩,
   ⟨⟨List.replicate 32 0⟩, [("wasm-tools", "1.263.0")], [], ⟨List.replicate 32 0⟩⟩]

theorem flakyBuilds_findings : (findings flakyBuilds).length = 2 := by decide +kernel

theorem flakyBuilds_not_reproducible : ¬ Reproducible flakyBuilds := by
  rw [← findings_eq_nil_iff]
  intro h
  have := flakyBuilds_findings
  rw [h] at this
  cases this

end Silmaril.Project.Components
