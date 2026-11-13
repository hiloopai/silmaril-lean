module

public import Silmaril.X86.Sep.BI.Defs
import Silmaril.Proofs.X86.Sep.BI
/-!
# The BI laws for `SProp` and for any separation algebra

* `laws : Laws (ops α)` for every `[SepAlg α]`: predicates over a separation algebra form a
  classical, non-affine BI with the non-OFE laws of iris-lean's `BI` (`fb21a8af`). With the
  `SepAlg.prod` instance this covers CP-10a's `XSProp` once its `XFrag` is a product.
* `sprop_laws : Laws sprop`, through `sprop_eq_ops : sprop = ops Frag` (`Sep.sep` and
  `Sep.wand` are the generic `sep`/`wand` at the partial-map algebra: `sep_eq`, `wand_eq`).
* `spure_eq`: The affine `spure φ` is iris's `<affine> ⌜φ⌝ = emp ∧ ⌜φ⌝`.
* `not_affine`: `emp` is not `True`, so the logic is linear (leaks are written `∗ strue`).
* `pure_persistent`, `spure_persistent`: pure facts are persistent (`P ⊢ <pers> P`), the
  property a function-pointer assertion needs for `fnptr Γ p S = ⌜…⌝`.

The D1 adapter (deferred, human-gated) builds `Iris.BI SProp` from `sprop_laws` plus
`COFE.ofDiscrete`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.BI

open Silmaril.X86.Sep (SProp Frag)

/-- Predicates over any separation algebra satisfy the BI laws. -/
theorem laws {α : Type _} [SepAlg α] : Laws (ops α) := Silmaril.Proofs.X86.Sep.BI.laws

theorem sep_eq : Silmaril.X86.Sep.sep = sep (α := Frag) :=
  Silmaril.Proofs.X86.Sep.BI.sep_eq

theorem wand_eq : Silmaril.X86.Sep.wand = wand (α := Frag) :=
  Silmaril.Proofs.X86.Sep.BI.wand_eq

theorem sprop_eq_ops : sprop = ops Frag := Silmaril.Proofs.X86.Sep.BI.sprop_eq_ops

/-- `SProp` is a (classical, non-affine, discrete) BI in iris-lean's sense. -/
theorem sprop_laws : Laws sprop := Silmaril.Proofs.X86.Sep.BI.sprop_laws

/-- The affine pure is iris's `<affine> ⌜φ⌝`. -/
theorem spure_eq (φ : Prop) :
    Silmaril.X86.Sep.spure φ = sprop.and sprop.emp (sprop.pure φ) :=
  Silmaril.Proofs.X86.Sep.BI.spure_eq φ

/-- `SProp` is not affine: `emp` is not `True`. -/
theorem not_affine : sprop.emp ≠ (fun _ => True) := Silmaril.Proofs.X86.Sep.BI.not_affine

theorem pure_persistent (φ : Prop) :
    sprop.Entails (sprop.pure φ) (sprop.persistently (sprop.pure φ)) :=
  Silmaril.Proofs.X86.Sep.BI.pure_persistent φ

theorem spure_persistent (φ : Prop) :
    sprop.Entails (Silmaril.X86.Sep.spure φ)
      (sprop.persistently (Silmaril.X86.Sep.spure φ)) :=
  Silmaril.Proofs.X86.Sep.BI.spure_persistent φ

/-- The shape of CP-10a's `XFrag` (`Frag` × sixteen 128-bit registers) gets the laws from the
product and partial-map instances alone. -/
example : Laws (ops (Frag × (Fin 16 → Option (BitVec 128)))) := laws

end Silmaril.X86.Sep.BI
