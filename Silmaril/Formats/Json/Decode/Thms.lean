module
public import Silmaril.Formats.Json.Decode.Defs
public section
namespace Silmaril.Formats.Json.Decode
variable {A : Type}

/-- The byte relation exposes the intermediate standard JSON value. -/
theorem text_iff {schema : Schema A} {bytes : Bytes} {ast : A} :
    text schema bytes ast ↔ ∃ json, Json.parse? bytes = some json ∧ schema json ast := Iff.rfl

theorem parse?_iff {decode : Ast Decimal → Option A} {bytes : Bytes} {ast : A} :
    parse? decode bytes = some ast ↔ text (graph decode) bytes ast := by
  cases h : Json.parse? bytes <;> simp [parse?, text, graph, Silmaril.EncRel.comp,
    Silmaril.EncRel.ofDecoder, h]

theorem text_functional {schema : Schema A} (h : schema.Functional) :
    (text schema).Functional := by
  rintro bytes a b ⟨json, hj, ha⟩ ⟨json', hj', hb⟩
  have heq : json = json' := Option.some.inj (hj.symm.trans hj')
  subst json'
  exact h ha hb

theorem graph_functional (decode : Ast Decimal → Option A) :
    (graph decode).Functional := Silmaril.EncRel.ofDecoder_functional decode

/-- JSON-level soundness composes with the chosen RFC JSON parser. -/
theorem parse?_sound {schema : Schema A} {decode : Ast Decimal → Option A}
    (sound : schema.DecoderSound decode) :
    (text schema).DecoderSound (parse? decode) := by
  intro bytes ast h
  obtain ⟨json, hjson, hast⟩ := parse?_iff.mp h
  exact ⟨json, hjson, sound json ast hast⟩

/-- JSON-level completeness supplies byte-level completeness for this parser. -/
theorem parse?_complete {schema : Schema A} {decode : Ast Decimal → Option A}
    (complete : schema.DecoderComplete decode) :
    (text schema).DecoderComplete (parse? decode) := by
  rintro bytes ast ⟨json, hjson, hast⟩
  exact parse?_iff.mpr ⟨json, hjson, complete json ast hast⟩

theorem Certified.parse?_iff {schema : Schema A} (decoder : Certified A schema)
    (bytes : Bytes) (ast : A) :
    parse? decoder.decode bytes = some ast ↔ text schema bytes ast :=
  ⟨parse?_sound decoder.sound bytes ast, parse?_complete decoder.complete bytes ast⟩

theorem Certified.functional {schema : Schema A} (decoder : Certified A schema) :
    schema.Functional := by
  intro json a b ha hb
  exact Option.some.inj ((decoder.complete json a ha).symm.trans
    (decoder.complete json b hb))

/-- Schema refinement is preserved by the outer JSON syntax layer. -/
theorem text_mono {first second : Schema A}
    (h : ∀ json ast, first json ast → second json ast) :
    ∀ bytes ast, text first bytes ast → text second bytes ast := by
  rintro bytes ast ⟨json, hjson, hast⟩
  exact ⟨json, hjson, h json ast hast⟩

theorem leanDecode?_iff {decode : Lean.Json → Except String A}
    {json : Ast Decimal} {ast : A} :
    leanDecode? decode json = some ast ↔ fromLeanDecoder decode json ast := by
  cases h : toLean? json with
  | none => simp [leanDecode?, fromLeanDecoder, fromLean, Silmaril.EncRel.pullPartial, h]
  | some value =>
    cases hd : decode value <;>
      simp [leanDecode?, fromLeanDecoder, fromLean, Silmaril.EncRel.pullPartial,
        h, hd, Except.toOption]

theorem fromLeanDecoder_functional (decode : Lean.Json → Except String A) :
    (fromLeanDecoder decode).Functional := by
  intro json a b ha hb
  exact Option.some.inj ((leanDecode?_iff.mpr ha).symm.trans (leanDecode?_iff.mpr hb))

theorem parseLean?_iff {decode : Lean.Json → Except String A} {bytes : Bytes} {ast : A} :
    parseLean? decode bytes = some ast ↔ text (fromLeanDecoder decode) bytes ast := by
  rw [parseLean?, parse?_iff]
  constructor
  · rintro ⟨json, hjson, hast⟩
    exact ⟨json, hjson, leanDecode?_iff.mp hast⟩
  · rintro ⟨json, hjson, hast⟩
    exact ⟨json, hjson, leanDecode?_iff.mpr hast⟩

end Silmaril.Formats.Json.Decode
