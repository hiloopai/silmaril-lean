module

public import Silmaril.Formats.Json.Fast.Wire.Defs
public import Silmaril.Formats.Json.Fast.Parser.Defs
public import Silmaril.Formats.JsonWire.Thms
import Silmaril.Proofs.Formats.Json.Fast.ParserSound

public section
namespace Silmaril.Formats.Json.Fast

/-- Success of the production reader implies that the independent RFC 8259 reader
accepts the same bytes and returns the same ordered, exact-decimal AST. This is
one-way: Unicode and depth/number limits can make the fast reader reject more. -/
theorem parseBytes_sound {bytes : ByteArray} {limits : Limits} {result : Value}
    (parsed : parseBytes bytes limits = .ok result) :
    ∃ ast, result.toWire? limits.depth = some ast ∧ JsonWire.parse? ⟨bytes⟩ = some ast :=
  Proofs.Json.Fast.ParserSound.parseBytes_sound parsed

theorem parseBytes_isJson {bytes : ByteArray} {limits : Limits} {result : Value}
    (parsed : parseBytes bytes limits = .ok result) : (Bytes.mk bytes).IsJson .rfc8259 := by
  obtain ⟨_, _, wire⟩ := parseBytes_sound parsed
  exact (JsonWire.parse?_isSome_iff_isJson ⟨bytes⟩).mp (by simp [wire])

end Silmaril.Formats.Json.Fast
