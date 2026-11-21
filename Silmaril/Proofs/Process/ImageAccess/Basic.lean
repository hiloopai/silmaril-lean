module

public import Silmaril.Process.ImageAccess.Defs

@[expose] public section

namespace Silmaril.Proofs.Process.ImageAccess

open Silmaril.Process.ImageAccess

theorem full_refines_owned (memory : Silmaril.Process.Memory) (owns : Read → Bool)
    (outside : Outside) :
    Reader.Refines (Image.full memory).localReader (Image.owned memory owns outside).localReader := by
  intro request bytes answer
  cases route : owns request
  · cases outside <;> simp [Image.localReader, Image.reader, Image.owned, route] at answer
  · simpa [Image.localReader, Image.reader, Image.owned, Image.full, route] using answer

end Silmaril.Proofs.Process.ImageAccess
