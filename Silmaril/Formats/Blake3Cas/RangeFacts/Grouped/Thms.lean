module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Grouped.Defs
import Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Grouped

public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.Grouped

open Silmaril.Crypto.Blake3

/-- A raw group verifies exactly as its explicit leaf/pair expansion. The top
compression uses the caller's ROOT flag; all its descendants use non-ROOT. -/
theorem Evidence.check_expand {shape : Shape} (grouped : Evidence shape) (root : Bool) :
    grouped.check? root = eval? (some ∘ compress32) root shape grouped.expand :=
  Proofs.Formats.Blake3Cas.RangeFacts.check_expand grouped root

theorem Evidence.check_iff_trace {shape : Shape} (grouped : Evidence shape) {root : Bool} {cv : CV} :
    grouped.check? root = some cv ↔ Trace concrete root shape grouped.expand cv :=
  grouped.check_expand root ▸ eval_graph

/-- An omitted pair layer is not an omitted byte layer: every accepted raw group
supplies the exact byte width of its original subtree. -/
theorem raw_width {shape : Shape} {bytes : Bytes} {root : Bool} {cv : CV}
    (hit : (Evidence.raw (shape := shape) bytes).check? root = some cv) : bytes.length = shape.size :=
  Proofs.Formats.Blake3Cas.RangeFacts.raw_width hit

theorem Cut.forLayers_reveals (layers : Nat) (selected : Nat → Bool) {shape : Shape} {root : Bool}
    {index : Nat} (inside : index ∈ chunkIndices shape) (wanted : selected index = true) :
    index ∈ (forLayers layers selected root shape).revealed :=
  Proofs.Formats.Blake3Cas.RangeFacts.forLayers_reveals layers selected inside wanted

theorem Cut.emit_checked {root : Bool} {shape : Shape} (cut : Cut root shape) {bytes : Bytes} {cv : CV}
    (full : subtreeCV? root shape bytes = some cv) :
    ∃ grouped, cut.emit? bytes = some grouped ∧ grouped.check? root = some cv ∧
      grouped.expand.exposesEOF = cut.opensEdge ∧
      Refines concrete shape grouped.expand (disclose shape bytes) :=
  Proofs.Formats.Blake3Cas.RangeFacts.emit_checked cut full

/-- Completeness for every cut of a fully named canonical tree. This is about
grouped proof evidence, not the serialization/framing of an Iroh or Bao stream. -/
theorem Cut.emit_named {digest bytes : Bytes} (cut : Cut true (geometry 0 bytes.length))
    (named : Named concrete digest bytes) :
    ∃ grouped, cut.emit? bytes = some grouped ∧ Root concrete bytes.length digest grouped.expand ∧
      grouped.expand.exposesEOF = cut.opensEdge :=
  let ⟨valid, cv, trace, digestEq⟩ := named
  let ⟨grouped, emitted, hit, edge, _⟩ := cut.emit_checked (eval_graph.mpr trace)
  ⟨grouped, emitted, ⟨valid, cv, eval_graph.mp ((grouped.check_expand true).symm ▸ hit), digestEq⟩, edge⟩

end Silmaril.Formats.Blake3Cas.RangeFacts.Grouped
