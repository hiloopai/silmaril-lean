module

public import Silmaril.Logic.ACL2.Ordinals.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Ordinals

open Silmaril.Logic.ACL2.Ordinals
open Encoding

/-- Syntactic correspondence before checking the descending exponent condition. -/
private inductive Shape : Encoding → ONote → Prop where
  | natural (n : Nat) : Shape (.natural n) (ONote.ofNat n)
  | sum {e r : Encoding} {E R : ONote} (c : Nat)
      (expt : Shape e E) (rest : Shape r R) (nonzero : E ≠ 0) :
      Shape (makeOrd e (c + 1) r) (.oadd E c.succPNat R)

private theorem Shape.encode {x : Encoding} {X : ONote} (h : Shape x X) : ofNote X = x := by
  induction h with
  | natural n => cases n <;> rfl
  | sum c he hr hn ie ir =>
    simp [ofNote, hn, ie, ir]

private theorem shape_of_oP (x : Encoding) (h : x.oP = true) :
    Shape x (ValidOrdinal.toNote.convert x) := by
  match x with
  | .natural n => exact .natural n
  | .cons (.cons e (.natural (c + 1))) r =>
    simp only [oP, Bool.and_eq_true, bne_iff_ne] at h
    obtain ⟨⟨⟨he, hn⟩, hr⟩, _⟩ := h
    refine .sum c (shape_of_oP e he) (shape_of_oP r hr) ?_
    intro hz
    apply hn
    simpa [hz, ofNote] using (shape_of_oP e he).encode.symm
  | .otherAtom | .cons (.natural _) _ | .cons .otherAtom _ |
    .cons (.cons _ (.natural 0)) _ | .cons (.cons _ .otherAtom) _ |
    .cons (.cons _ (.cons _ _)) _ => contradiction

private theorem shape_of_nf (x : ONote) (h : x.NF) : Shape (ofNote x) x := by
  induction x with
  | zero => exact .natural 0
  | oadd e c r ie ir =>
    obtain ⟨_ | c, hc⟩ := c
    · contradiction
    have hc' : (⟨c + 1, hc⟩ : PNat) = c.succPNat := Subtype.ext rfl
    rw [hc'] at h ⊢
    by_cases he : e = 0
    · have hr := h.zero_of_zero he
      subst e r
      simpa [ofNote] using Shape.natural (c + 1)
    · simpa only [ofNote, ite_eq_right he, Nat.succPNat_coe] using Shape.sum c (ie h.fst) (ir h.snd) he

private theorem Shape.convert {x : Encoding} {X : ONote} (h : Shape x X) :
    ValidOrdinal.toNote.convert x = X := by
  induction h with
  | natural => rfl
  | sum c he hr hn ie ir => simp [makeOrd, ValidOrdinal.toNote.convert, ie, ir]

private theorem cmp_natural (m n : Nat) :
    ONote.cmp (ONote.ofNat m) (ONote.ofNat n) = compare m n := by
  cases m <;> cases n <;>
    simp [ONote.cmp, cmp_eq_compare, Nat.compare_eq_ite_lt, Ordering.then]
  split <;> simp_all

private theorem Shape.compare {x y : Encoding} {X Y : ONote} (hx : Shape x X) (hy : Shape y Y) :
    x.cmp y = ONote.cmp X Y := by
  induction hx generalizing y Y with
  | natural m =>
    cases hy with
    | natural n => exact (cmp_natural m n).symm
    | @sum e r E R c he hr hn =>
      cases m <;> cases E <;> simp_all [makeOrd, Encoding.cmp, ONote.cmp, Ordering.then]
  | @sum e r E R c he hr hn ie ir =>
    cases hy with
    | natural n =>
      cases n <;> cases E <;> simp_all [makeOrd, Encoding.cmp, ONote.cmp, Ordering.then]
    | sum d he' hr' hn' =>
      simp [makeOrd, Encoding.cmp, ONote.cmp, ie he', ir hr', cmp_eq_compare]

private theorem Shape.nonzero {x : Encoding} {X : ONote} (h : Shape x X) (hn : X ≠ 0) :
    x ≠ .natural 0 := by
  cases h with
  | natural n => rintro h; obtain rfl := Encoding.natural.inj h; exact hn rfl
  | sum => exact fun h => nomatch h

private theorem Shape.topBelow {e r : Encoding} {E R : ONote} (he : Shape e E) (hr : Shape r R)
    (hn : E ≠ 0) : r.firstExpt.oLt e = true ↔ ONote.TopBelow E R := by
  cases hr with
  | natural n =>
    have hc := (Shape.natural 0).compare he
    cases E <;> cases n <;>
      simp_all [firstExpt, oLt, ONote.TopBelow, ONote.cmp]
  | sum c hhead htail hpos =>
    simp only [firstExpt, makeOrd, oLt, ONote.TopBelow, hhead.compare he, beq_iff_eq]

private theorem Shape.oP_iff_nf {x : Encoding} {X : ONote} (h : Shape x X) :
    x.oP = true ↔ X.NF := by
  induction h with
  | natural n => exact ⟨fun _ => inferInstance, fun _ => rfl⟩
  | sum c he hr hn ie ir =>
    simp only [makeOrd, oP, Bool.and_eq_true, bne_iff_ne]
    rw [ie, ir, he.topBelow hr hn]
    constructor
    · rintro ⟨⟨⟨ne, _⟩, nr⟩, hb⟩
      exact ne.oadd _ ((@ONote.nfBelow_iff_topBelow _ ne _).2 ⟨nr, hb⟩)
    · intro h
      have hb := (@ONote.nfBelow_iff_topBelow _ h.fst _).1 h.snd'
      exact ⟨⟨⟨h.fst, he.nonzero hn⟩, hb.1⟩, hb.2⟩

theorem oP_ofNote {x : ONote} (h : x.NF) : (ofNote x).oP = true :=
  (shape_of_nf x h).oP_iff_nf.2 h

theorem toNote_nf (x : ValidOrdinal) : x.toNote.NF :=
  (shape_of_oP x.val x.property).oP_iff_nf.1 x.property

theorem ofNote_toNote (x : ValidOrdinal) : ofNote x.toNote = x.val :=
  (shape_of_oP x.val x.property).encode

theorem toNote_ofNote (x : ONote) (h : x.NF) :
    (ValidOrdinal.toNote ⟨ofNote x, oP_ofNote h⟩) = x :=
  (shape_of_nf x h).convert

theorem cmp_toNote (x y : ValidOrdinal) : x.val.cmp y.val = ONote.cmp x.toNote y.toNote :=
  (shape_of_oP x.val x.property).compare (shape_of_oP y.val y.property)

theorem lt_iff (x y : ValidOrdinal) : x.lt y ↔ x.toNote < y.toNote := by
  simpa only [ValidOrdinal.lt, oLt, cmp_toNote, beq_iff_eq] using
    (@ONote.cmp_compares x.toNote y.toNote (toNote_nf x) (toNote_nf y)).eq_lt

theorem cmp_eq_eq (x y : ValidOrdinal) : x.val.cmp y.val = .eq ↔ x.val = y.val := by
  rw [cmp_toNote, (@ONote.cmp_compares x.toNote y.toNote (toNote_nf x) (toNote_nf y)).eq_eq]
  exact ⟨fun h => by rw [← ofNote_toNote x, ← ofNote_toNote y, h],
    fun h => congrArg ValidOrdinal.toNote (Subtype.ext h)⟩

theorem wellFounded : WellFounded ValidOrdinal.lt :=
  Subrelation.wf (fun h => (lt_iff _ _).1 h) (InvImage.wf ValidOrdinal.toNote (WellFoundedRelation.wf))

end Silmaril.Proofs.Logic.ACL2.Ordinals
