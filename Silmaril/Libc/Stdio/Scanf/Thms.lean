module

public import Silmaril.Libc.Stdio.Scanf.Defs
import Silmaril.Proofs.Libc.Stdio.Scanf

/-!
# C99 `scanf` formats: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Libc.Stdio.Scanf`): **the tiers are
nested**, `Spec.leet_intc`, `Spec.inTier_mono`, `InTier.mono`.
-/

@[expose] public section

namespace Silmaril.Libc.Stdio.Scanf

open Silmaril.Libc.Stdio.Printf (Tier)

theorem Spec.leet_intc {c : Spec} (h : c.leet = true) : c.intc = true :=
  Proofs.Libc.Stdio.Scanf.Spec.leet_intc h

theorem Spec.inTier_mono {t t' : Tier} (ht : t.le t') {c : Spec} (h : c.inTier t = true) :
    c.inTier t' = true :=
  Proofs.Libc.Stdio.Scanf.Spec.inTier_mono ht h

theorem InTier.mono {t t' : Tier} (ht : t.le t') {is : List Item} (h : InTier t is) :
    InTier t' is :=
  Proofs.Libc.Stdio.Scanf.InTier.mono ht h

end Silmaril.Libc.Stdio.Scanf
