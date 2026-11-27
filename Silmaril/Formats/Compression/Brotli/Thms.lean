module

public import Silmaril.Formats.Compression.Brotli.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Contracts
import Init.Omega

public section

namespace Silmaril.Formats.Compression.Brotli

theorem WindowWire.range {wbits : Nat} {code : List Bool} (wire : WindowWire wbits code) :
    10 ≤ wbits ∧ wbits ≤ 24 := by
  cases wire <;> omega

/-- A raw body begins at a byte boundary after the checked zero fill. -/
theorem bodyStart_aligned (position : Nat) (header : MetaHeader) :
    bodyStart position header % 8 = 0 := by
  simp [bodyStart, padding]
  omega

/-- The step count includes one empty last meta-block. -/
theorem BlocksWire.stepCount {position steps : Nat} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : BlocksWire position bits chunks steps) : steps = chunks.length + 1 := by
  induction wire <;> simp_all

namespace Internal

theorem take_sound {width value : Nat} {reader next : LSBReader} {bits : List Bool}
    (cursor : Cursor reader bits) (read : take reader width = .ok (value, next)) :
    ∃ tail, bits = natBits value width ++ tail ∧ Cursor next tail ∧
      value < 2 ^ width ∧ next.totalRead = reader.totalRead + width :=
  Proofs.Formats.Compression.Brotli.take_sound cursor read

theorem readWindow_sound {reader next : LSBReader} {bits : List Bool} {wbits : Nat}
    (cursor : Cursor reader bits) (read : readWindow reader = .ok (wbits, next)) :
    ∃ code tail, WindowWire wbits code ∧ bits = code ++ tail ∧ Cursor next tail ∧
      next.totalRead = reader.totalRead + code.length :=
  Proofs.Formats.Compression.Brotli.readWindow_sound cursor read

theorem alignZero_sound {reader aligned : LSBReader} {bits : List Bool}
    (cursor : Cursor reader bits) (read : alignZero reader = .ok aligned) :
    ∃ tail, bits = padding reader.totalRead ++ tail ∧ Cursor aligned tail ∧ aligned.count = 0 ∧
      aligned.totalRead = reader.totalRead + (padding reader.totalRead).length :=
  Proofs.Formats.Compression.Brotli.alignZero_sound cursor read

theorem takeBody_sound {size : Nat} {reader next : LSBReader} {bits : List Bool} {body : List UInt8}
    (cursor : Cursor reader bits) (aligned : reader.count = 0)
    (read : takeBody size reader = .ok (body, next)) :
    ∃ tail, body.length = size ∧ bits = bytesBits body ++ tail ∧ Cursor next tail ∧
      next.totalRead = reader.totalRead + 8 * body.length :=
  Proofs.Formats.Compression.Brotli.takeBody_sound cursor aligned read

theorem emptyCursor {reader : LSBReader} {bits : List Bool}
    (cursor : Cursor reader bits) (count : reader.count = 0) (input : reader.input = []) : bits = [] :=
  Proofs.Formats.Compression.Brotli.emptyCursor cursor count input

end Internal

/-- Success accounts for all original bits through the empty terminal,
    concatenates the raw bodies in order, and satisfies all caller limits. -/
theorem decode_sound {limits : Limits} {input output : List UInt8}
    (read : decode limits input = .ok output) :
    ∃ wbits steps, StreamWire input output wbits steps ∧ input.length ≤ limits.input ∧
      output.length ≤ limits.output ∧ windowSize wbits ≤ limits.window ∧ steps ≤ limits.steps :=
  Proofs.Formats.Compression.Brotli.decode_sound read

end Silmaril.Formats.Compression.Brotli
