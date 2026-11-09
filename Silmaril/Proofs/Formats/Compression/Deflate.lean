module

public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Raw.Formats.Compression.Deflate.Stored

/-! Proofs for `Silmaril.Formats.Compression.Deflate.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Deflate

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

theorem decoder_eq_some {bytes out rest : List UInt8} :
    decoder bytes = some (out, rest) ↔ deflateTake bytes = .ok (out, rest) := by
  simp only [Decoder.ofExcept]
  cases deflateTake bytes <;> simp [Except.toOption]

theorem decoder_consumes : decoder.Consumes := fun _ _ _ h =>
  deflateTake_suffix (decoder_eq_some.mp h)

theorem roundTrip : RoundTrip decoder encoder := fun data rest =>
  decoder_eq_some.mpr (deflateTake_storedBytes data rest)

end Silmaril.Proofs.Formats.Compression.Deflate
