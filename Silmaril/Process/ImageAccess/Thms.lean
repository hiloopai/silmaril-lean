module

public import Silmaril.Process.ImageAccess.Contract.Thms
public import Silmaril.Process.ImageAccess.Defs
import Silmaril.Proofs.Process.ImageAccess.Basic

@[expose] public section

namespace Silmaril.Process.ImageAccess

/-- Lifting an ownership restriction on the same snapshot preserves every successful reply. -/
theorem Image.full_refines_owned (memory : Memory) (owns : Read → Bool) (outside : Outside) :
    Reader.Refines (Image.full memory).localReader (Image.owned memory owns outside).localReader :=
  Proofs.Process.ImageAccess.full_refines_owned memory owns outside

end Silmaril.Process.ImageAccess
