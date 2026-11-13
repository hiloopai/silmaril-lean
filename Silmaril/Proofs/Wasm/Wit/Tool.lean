module

public import Silmaril.Wasm.Wit.Tool.Defs
public import Silmaril.Wasm.Wit.Binary.Thms
public import Silmaril.Wasm.Component.Wat.Thms
public import Silmaril.Wasm.Wit.Project.Thms

/-!
# The core of `wasm-wit`: proofs

See `Silmaril.Wasm.Wit.Tool.Thms` for the statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Tool

open Silmaril.Wasm.Component
open Silmaril.Wasm.Wit.Binary (Package Env decodePackage decodeEnv encodePackage)

/-! ## Component WAT -/

theorem printWat_eq_ok {b : ByteArray} {t : String} :
    printWat b = .ok t ↔ ∃ c, Binary.parse b = .ok c ∧ Wat.print c = t := by
  unfold printWat
  split <;> rename_i h <;> simp [h]

theorem parseWat_eq_ok {t : String} {b : ByteArray} :
    parseWat t = .ok b ↔ ∃ c, Wat.read t = some c ∧ Binary.encode c = some b := by
  unfold parseWat
  split <;> rename_i h
  · simp [h]
  · split <;> rename_i h' <;> simp [h, h']

/-- The bytes `parse` writes for the text `print` wrote parse back to the normal
form of the component. -/
theorem parse_parseWat_printWat {b b' : ByteArray} {t : String} {c : Binary.Ast}
    (hc : Binary.parse b = .ok c) (ht : printWat b = .ok t) (hb : parseWat t = .ok b') :
    Binary.parse b' = .ok (Wat.norm c) := by
  obtain ⟨c₁, h₁, rfl⟩ := printWat_eq_ok.1 ht
  rw [hc] at h₁
  cases h₁
  obtain ⟨c₂, h₂, h₃⟩ := parseWat_eq_ok.1 hb
  rw [Wat.read_print] at h₂
  cases h₂
  exact Binary.parse_encode h₃

/-- `print ∘ parse ∘ print = print`: the text is a fixed point. -/
theorem printWat_parseWat_printWat {b b' : ByteArray} {t : String}
    (ht : printWat b = .ok t) (hb : parseWat t = .ok b') : printWat b' = .ok t := by
  obtain ⟨c, hc, rfl⟩ := printWat_eq_ok.1 ht
  rw [printWat_eq_ok]
  exact ⟨Wat.norm c, parse_parseWat_printWat hc ht hb, Wat.print_norm c⟩

/-! ## WIT packages -/

theorem decode_eq_ok {b : ByteArray} {d : Decoded} :
    decode b = .ok d ↔ decodePackage b = .ok d.pkg ∧ decodeEnv b = .ok d.env := by
  unfold decode
  cases h₁ : decodePackage b <;> cases h₂ : decodeEnv b <;>
    simp [bind, Except.bind, pure, Except.pure]
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem check_eq_ok {b : ByteArray} {r : Report} (h : check b = .ok r) :
    decode b = .ok r.decoded ∧
    (r.valid = true ↔ r.decoded.pkg.Valid r.decoded.env) ∧
    (r.unique = true ↔ r.decoded.pkg.NamesUnique) ∧
    (r.canonical = true ↔ r.decoded.pkg.canon = r.decoded.pkg) ∧
    (∀ b', r.reencoded = some b' ↔ encodePackage r.decoded.env r.decoded.pkg = .ok b') ∧
    (r.fixpoint = true ↔ r.reencoded = some b) := by
  unfold check at h
  cases hd : decode b with
  | error e => rw [hd] at h; cases h
  | ok d =>
    rw [hd] at h
    cases h
    refine ⟨rfl, by simp, by simp, by simp, fun b' => ?_, by simp⟩
    cases encodePackage d.env d.pkg <;> simp

/-- **Soundness of `encode`.** When `check` finds the decoded package valid
with distinct names, the re-encoded bytes decode to its canonical form. -/
theorem reencode_sound {b b' : ByteArray} {r : Report} (h : check b = .ok r)
    (hv : r.valid = true) (hu : r.unique = true) (hb : r.reencoded = some b') :
    decodePackage b' = .ok r.decoded.pkg.canon := by
  obtain ⟨-, hV, hU, -, hR, -⟩ := check_eq_ok h
  exact Binary.decodePackage_encodePackage_canon (hV.1 hv) (hU.1 hu) ((hR b').1 hb)

/-- A fixed point of `encode` is canonical: `canonical` follows from the other
checks. -/
theorem canonical_of_fixpoint {b : ByteArray} {r : Report} (h : check b = .ok r)
    (hv : r.valid = true) (hu : r.unique = true) (hf : r.fixpoint = true) :
    r.canonical = true := by
  have hb : r.reencoded = some b := ((check_eq_ok h).2.2.2.2.2).1 hf
  have h₁ := reencode_sound h hv hu hb
  have h₂ := ((decode_eq_ok).1 (check_eq_ok h).1).1
  rw [h₁] at h₂
  exact ((check_eq_ok h).2.2.2.1).2 (Except.ok.inj h₂)

/-- **Soundness of `check`.** Bytes that pass every check are the encoding of a
valid, canonical package with distinct names in the environment they show; they
decode to it, and encode ∘ decode is the identity on them. -/
theorem check_ok_sound {b : ByteArray} {r : Report} (h : check b = .ok r) (hok : r.ok = true) :
    decodePackage b = .ok r.decoded.pkg ∧ decodeEnv b = .ok r.decoded.env ∧
    r.decoded.pkg.Valid r.decoded.env ∧ r.decoded.pkg.NamesUnique ∧
    r.decoded.pkg.canon = r.decoded.pkg ∧
    encodePackage r.decoded.env r.decoded.pkg = .ok b ∧ reencode b = .ok b := by
  obtain ⟨hd, hV, hU, hC, hR, hF⟩ := check_eq_ok h
  simp only [Report.ok, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hv, hu⟩, hc⟩, hf⟩ := hok
  have he : encodePackage r.decoded.env r.decoded.pkg = .ok b := (hR b).1 (hF.1 hf)
  refine ⟨(decode_eq_ok.1 hd).1, (decode_eq_ok.1 hd).2, hV.1 hv, hU.1 hu, hC.1 hc, he, ?_⟩
  simp [reencode, hd, bind, Except.bind, he]

/-! ## Projection -/

/-- The projection reads the same world from a binary and from its WAT. -/
theorem projectWat_printWat {b : ByteArray} {t : String} (ht : printWat b = .ok t) :
    projectWat t = projectBytes b := by
  obtain ⟨c, hc, rfl⟩ := printWat_eq_ok.1 ht
  have h := Project.project_read_print c
  unfold projectWat projectBytes
  rw [hc]
  cases hr : Wat.read (Wat.print c) with
  | none => rw [Wat.read_print] at hr; cases hr
  | some c' =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    simp only [h]
