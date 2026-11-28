module

public import Silmaril.Logic.ACL2.LegacyOrdinals.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.LegacyOrdinals

open Silmaril.Logic.ACL2.Ordinals Silmaril.Logic.ACL2.LegacyOrdinals
open Ordinal Order

private noncomputable def denote : Encoding → Ordinal.{0}
  | .natural n => n
  | .otherAtom => 0
  | .cons e r => ω ^ denote e + denote r

private def head : Encoding → Encoding
  | .cons e _ => e
  | _ => .natural 0

/-- The weak exponent ordering stated in the ordinal semantics. -/
private inductive Canonical : Encoding → Prop where
  | natural (n : Nat) : Canonical (.natural n)
  | cons {e r : Encoding} (expt : Canonical e) (rest : Canonical r)
      (nonzero : e ≠ .natural 0) (ordered : denote (head r) ≤ denote e) :
      Canonical (.cons e r)

private theorem cons_lower (e r : Encoding) : ω ^ denote e ≤ denote (.cons e r) :=
  le_self_add

private theorem Canonical.pos {x : Encoding} (h : Canonical x) (hn : x ≠ .natural 0) :
    0 < denote x := by
  cases h with
  | natural n =>
    have h : 0 < n := Nat.pos_of_ne_zero (fun he => hn (he ▸ rfl))
    simpa only [denote, Nat.cast_zero] using (Nat.cast_lt (α := Ordinal)).2 h
  | cons => exact (opow_pos _ omega0_pos).trans_le (cons_lower _ _)

private theorem Canonical.bound {x : Encoding} (h : Canonical x) :
    denote x < ω ^ succ (denote (head x)) := by
  induction h with
  | natural n => simp [denote, head]
  | @cons e r _ _ _ hor _ ihr =>
    apply isPrincipal_add_omega0_opow
    · exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_succ _)
    · exact ihr.trans_le (opow_le_opow_right omega0_pos (succ_le_succ hor))

private theorem nat_lt_cons {e r : Encoding} (h : Canonical e) (hn : e ≠ .natural 0) (n : Nat) :
    denote (.natural n) < denote (.cons e r) :=
  (natCast_lt_omega0 n).trans_le
    ((show ω ≤ ω ^ denote e from by
      simpa only [opow_one] using
        opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 (ne_of_gt (h.pos hn)))).trans
      (cons_lower e r))

private theorem cons_lt_of_exp_lt {e r f s : Encoding} (h : Canonical (.cons e r))
    (hlt : denote e < denote f) : denote (.cons e r) < denote (.cons f s) :=
  h.bound.trans_le ((opow_le_opow_right omega0_pos (succ_le_of_lt hlt)).trans (cons_lower f s))

/-- Equality in this comparison is structural equality, as in ACL2 EQUAL. -/
private def Compares (x y : Encoding) : Ordering → Prop
  | .lt => denote x < denote y
  | .eq => x = y
  | .gt => denote y < denote x

private theorem compare_repr {x y : Encoding} (hx : Canonical x) (hy : Canonical y) :
    Compares x y (cmp x y) := by
  induction hx generalizing y with
  | natural m =>
    cases hy with
    | natural n =>
      rw [Silmaril.Logic.ACL2.LegacyOrdinals.cmp]
      cases h : compare m n with
      | lt => exact Nat.cast_lt.2 (Nat.compare_eq_lt.1 h)
      | eq => exact congrArg Encoding.natural (Nat.compare_eq_eq.1 h)
      | gt => exact Nat.cast_lt.2 (Nat.compare_eq_gt.1 h)
    | cons he _ hn _ => exact nat_lt_cons he hn m
  | @cons e r he hr hn hor ihe ihr =>
    cases hy with
    | natural n => exact nat_lt_cons he hn n
    | @cons f s hf hs hfn hfo =>
      have h := ihe hf
      rw [Silmaril.Logic.ACL2.LegacyOrdinals.cmp]
      cases hc : cmp e f <;> rw [hc] at h
      case lt => exact cons_lt_of_exp_lt (Canonical.cons he hr hn hor) h
      case gt => exact cons_lt_of_exp_lt (Canonical.cons hf hs hfn hfo) h
      case eq =>
        have hef : e = f := h
        subst f
        have hh := ihr hs
        simp only [Ordering.eq_then]
        cases ht : cmp r s <;> rw [ht] at hh
        · exact add_lt_add_right hh _
        · exact congrArg (Encoding.cons e) hh
        · exact add_lt_add_right hh _

private theorem lt_denote {x y : Encoding} (hx : Canonical x) (hy : Canonical y) :
    lt x y ↔ denote x < denote y := by
  have h := compare_repr hx hy
  unfold lt
  cases hc : cmp x y <;> rw [hc] at h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · have he : x = y := h
    simp [he]
  · constructor
    · intro hgt
      cases hgt
    · intro hlt
      exact (not_lt_of_gt (show denote y < denote x from h) hlt).elim

private theorem canonical_of_valid (x : Encoding) (h : valid x = true) : Canonical x := by
  match x with
  | .natural n => exact .natural n
  | .otherAtom => contradiction
  | .cons e r =>
    simp only [valid, Bool.and_eq_true, bne_iff_ne] at h
    obtain ⟨⟨⟨he, hn⟩, hr⟩, ho⟩ := h
    have ce := canonical_of_valid e he
    have cr := canonical_of_valid r hr
    refine .cons ce cr hn ?_
    cases cr with
    | natural => exact zero_le
    | cons cf _ _ _ =>
      apply le_of_not_gt
      exact fun hf => (bne_iff_ne.mp ho) ((lt_denote ce cf).2 hf)

private theorem toNote_nf {x : Encoding} (h : Canonical x) : (toNote x).NF := by
  induction h with
  | natural n => exact ONote.nf_ofNat n
  | @cons e r _ _ _ _ ie ir =>
    exact @ONote.add_nf (ONote.oadd (toNote e) 1 0) (toNote r) (ie.oadd 1 .zero) ir

private theorem repr_toNote {x : Encoding} (h : Canonical x) : (toNote x).repr = denote x := by
  induction h with
  | natural n => exact ONote.repr_ofNat n
  | @cons e r he hr _ _ ie ir =>
    change ONote.repr (ONote.oadd (toNote e) 1 0 + toNote r) = _
    rw [@ONote.repr_add _ _ ((toNote_nf he).oadd 1 .zero) (toNote_nf hr)]
    simp [denote, ie, ir]

theorem ordinal_valid (x : Encoding) (h : valid x = true) : (ordinalMeasure x).oP = true :=
  Encoding.oP_ofNote (toNote_nf (canonical_of_valid x h))

theorem lt_iff (x y : Encoding) (hx : valid x = true) (hy : valid y = true) :
    lt x y ↔ (ordinalMeasure x).oLt (ordinalMeasure y) = true := by
  have cx := canonical_of_valid x hx
  have cy := canonical_of_valid y hy
  let ox : ValidOrdinal := ⟨ordinalMeasure x, ordinal_valid x hx⟩
  let oy : ValidOrdinal := ⟨ordinalMeasure y, ordinal_valid y hy⟩
  change lt x y ↔ ox.lt oy
  rw [lt_denote cx cy, ValidOrdinal.lt_iff]
  change denote x < denote y ↔ (ValidOrdinal.toNote ⟨Encoding.ofNote (toNote x), _⟩) <
    (ValidOrdinal.toNote ⟨Encoding.ofNote (toNote y), _⟩)
  rw (config := { transparency := .default })
    [ValidOrdinal.toNote_ofNote _ (toNote_nf cx), ValidOrdinal.toNote_ofNote _ (toNote_nf cy),
    ONote.lt_def, repr_toNote cx, repr_toNote cy]

theorem cmp_eq_eq (x y : Encoding) (hx : valid x = true) (hy : valid y = true) :
    cmp x y = .eq ↔ x = y := by
  have h := compare_repr (canonical_of_valid x hx) (canonical_of_valid y hy)
  cases hc : cmp x y <;> rw [hc] at h
  · simp [show x ≠ y from fun he => (ne_of_lt (show denote x < denote y from h)) (congrArg denote he)]
  · simp [show x = y from h]
  · simp [show x ≠ y from fun he => (ne_of_gt (show denote y < denote x from h)) (congrArg denote he)]

end Silmaril.Proofs.Logic.ACL2.LegacyOrdinals
