module

public import Silmaril.Formats.Arrow.FooterWriter.Defs
import Silmaril.Formats.Arrow.MetadataWriter.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.FooterWriter

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.FooterWriter MetadataWriter.Wire

private theorem append_length (left right : KBytes) : (left ++ right).len = left.len + right.len := rfl

private theorem wordsLength (blocks : List FileBlock) :
    (blocks.flatMap fun block => [block.offset, block.metadataLength, block.bodyLength]).length =
      3 * blocks.length := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons, ih]
    omega

private theorem encode_length (footer : FileFooter) : (encode footer).len = wireSize footer := by
  simp only [encode, encodeWithSchema, wireSize, words, longs, Writer.emitWords_length, append_length,
    List.length_cons, List.length_nil, wordsLength, schemaPayload_size]
  omega

theorem serialize_extent {limits : Limits} {footer : FileFooter} {bytes : KBytes}
    (written : serialize limits footer = .ok bytes) :
    bytes.wf = true ∧ bytes.len = wireSize footer ∧ 0 < bytes.len ∧
      bytes.len % 8 = 0 ∧ bytes.len < 2^31 ∧ bytes.len ≤ limits.metadataBytes := by
  simp only [serialize] at written
  split at written <;> try contradiction
  split at written <;> try contradiction
  split at written <;> try contradiction
  split at written <;> try contradiction
  split at written <;> try contradiction
  cases written
  refine ⟨KBytes.wf_append (Writer.emitWords_wf _ _)
    (KBytes.wf_append (Writer.emitWords_wf _ _) (schemaPayload_wf _)),
    encode_length footer, ?_, ?_, ?_, ?_⟩
  all_goals rw [encode_length]
  · unfold wireSize
    omega
  · unfold wireSize
    have aligned := schemaPayload_aligned footer.fields
    omega
  · omega
  · omega

theorem emit_exact {limits : Limits} {footer : FileFooter} {bytes : KBytes}
    (written : emit limits footer = .ok bytes) :
    serialize limits footer = .ok bytes ∧
      readFileFooter limits (bytes.slice 0 bytes.len) = .ok footer := by
  cases encoded : serialize limits footer with
  | error error => simp [emit, encoded, bind, Except.bind] at written
  | ok data =>
    cases decoded : readFileFooter limits (data.slice 0 data.len) with
    | error error => simp [emit, encoded, decoded, bind, Except.bind] at written
    | ok result =>
      simp [emit, encoded, decoded, bind, Except.bind, pure, Except.pure] at written
      split at written <;> try contradiction
      rename_i same
      subst result
      cases written
      exact ⟨rfl, decoded⟩

end Silmaril.Proofs.Formats.Arrow.FooterWriter
