module

public import Silmaril.Libc.Stdio.Printf.Defs
import Silmaril.Proofs.Libc.Stdio.Printf

/-!
# C99 `printf` formats: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Libc.Stdio.Printf`):

* **The tiers are nested**: `Spec.leet_intc`, `Spec.intc_c99`, `Spec.inTier_mono` (a
  specification of a tier is in every higher tier), `InTier.mono`;
* **A fixed `%p` keeps every text**: `convText_mono`, `renderSpec_mono`, `render_mono` (a text rendered with the
  `%p` choice `pt` is rendered the same with any `pt'` that fixes it where `pt` does: in
  particular every text without `%p` is the same for every choice);
* `Text.mono`: a valid `printf` text of a tier is one of every higher tier and stronger choice.
-/

@[expose] public section

namespace Silmaril.Libc.Stdio.Printf

open Silmaril.X86 (Byte)

theorem Spec.leet_intc {c : Spec} (h : c.leet = true) : c.intc = true :=
  Proofs.Libc.Stdio.Printf.Spec.leet_intc h

theorem Spec.intc_c99 {c : Spec} (h : c.intc = true) : c.c99 = true :=
  Proofs.Libc.Stdio.Printf.Spec.intc_c99 h

theorem Spec.inTier_mono {t t' : Tier} (ht : t.le t') {c : Spec} (h : c.inTier t = true) :
    c.inTier t' = true :=
  Proofs.Libc.Stdio.Printf.Spec.inTier_mono ht h

theorem convText_mono {pt pt' : Option (Nat → List Byte)} (hp : PtrLe pt pt') {c : Spec}
    {fl : Flags} {wn : Nat} {pn : Option Nat} {a : PArg} {t : List Byte}
    (h : convText pt c fl wn pn a = some t) : convText pt' c fl wn pn a = some t :=
  Proofs.Libc.Stdio.Printf.convText_mono hp h

theorem renderSpec_mono {pt pt' : Option (Nat → List Byte)} (hp : PtrLe pt pt') {c : Spec}
    {as : List PArg} {x : List Byte × List PArg} (h : renderSpec pt c as = some x) :
    renderSpec pt' c as = some x :=
  Proofs.Libc.Stdio.Printf.renderSpec_mono hp h

theorem render_mono {pt pt' : Option (Nat → List Byte)} (hp : PtrLe pt pt') {is : List Item}
    {as : List PArg} {out : List Byte} (h : render pt is as = some out) :
    render pt' is as = some out :=
  Proofs.Libc.Stdio.Printf.render_mono hp h

theorem InTier.mono {t t' : Tier} {pt pt' : Option (Nat → List Byte)} (ht : t.le t')
    (hp : PtrLe pt pt') {is : List Item} (h : InTier t pt is) : InTier t' pt' is :=
  Proofs.Libc.Stdio.Printf.InTier.mono ht hp h

theorem Text.mono {t t' : Tier} {pt pt' : Option (Nat → List Byte)} (ht : t.le t')
    (hp : PtrLe pt pt') {fmt : List Byte} {as : List PArg} {out : List Byte}
    (h : Text t pt fmt as out) : Text t' pt' fmt as out :=
  Proofs.Libc.Stdio.Printf.Text.mono ht hp h

/-- The order of the tiers is reflexive. -/
theorem Tier.le_refl (t : Tier) : t.le t := Nat.le_refl _

end Silmaril.Libc.Stdio.Printf
