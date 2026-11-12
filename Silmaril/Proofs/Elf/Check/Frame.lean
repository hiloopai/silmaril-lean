module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.Proofs.Elf.Check.Sound

/-! # The parse frame: the parse depends only on the bytes it reads

* `run_frame`: a reading program gives the same result on two byte sources that agree on its
  footprint (`Parse.trace`);
* `trace_sub`: on a source that answers as the file (`Check.Sub`, e.g. the pages), a successful
  run has the footprint it has on the file, so `AvoidsCode` is checkable on pages;
* `parse_frame`: `Task.parse_frame`.

Standard axioms only.
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.X86.Link (Blob)

theorem run_frame {α : Type} {r r' : Nat → Nat → Option Nat} :
    ∀ (p : Rd α), (∀ x ∈ Parse.trace r p, r x.1 x.2 = r' x.1 x.2) → p.run r = p.run r'
  | .pure _, _ => rfl
  | .fail, _ => rfl
  | .read o w k, h => by
    have h0 : r o w = r' o w := h (o, w) (by simp [Parse.trace])
    cases e : r o w with
    | none =>
      rw [Rd.run_read_none _ e, Rd.run_read_none _ (h0 ▸ e)]
    | some v =>
      rw [Rd.run_read_some _ e, Rd.run_read_some _ (h0 ▸ e)]
      exact run_frame (k v) fun x hx => h x (by simp [Parse.trace, e, hx])

theorem trace_sub {α : Type} {r : Nat → Nat → Option Nat} {F : Blob} (hs : Check.Sub r F) :
    ∀ (p : Rd α) (a : α), p.run r = some a → Parse.trace r p = Parse.trace (blobRead F) p
  | .pure _, _, _ => rfl
  | .fail, _, h => by cases h
  | .read o w k, a, h => by
    cases e : r o w with
    | none =>
      rw [Rd.run_read_none _ e] at h; cases h
    | some v =>
      have hb := hs _ _ _ e
      have hk : (k v).run r = some a := by rw [← Rd.run_read_some _ e]; exact h
      simp only [Parse.trace, e, hb]
      rw [trace_sub hs (k v) a hk]

/-- **`Task.parse_frame`.** -/
theorem parse_frame : Task.parse_frame := by
  intro F G A hF hav _ hout
  unfold Parses parse at *
  rw [← hF]
  symm
  apply run_frame
  intro x hx
  exact hout x.1 x.2 (hav x hx)

/-- `AvoidsCode` from a run on pages (or any source answering as the file). -/
theorem avoidsCode_of_sub {r : Nat → Nat → Option Nat} {F : Blob} (hs : Check.Sub r F) {A : File}
    (hrun : read.run r = some A)
    (h : (Parse.trace r read).all (fun x => A.codeSpans.all fun s =>
      decide (s.off + s.len ≤ x.1 ∨ x.1 + x.2 ≤ s.off)) = true) :
    AvoidsCode F A := by
  unfold AvoidsCode
  rw [← trace_sub hs read A hrun]
  intro x hx s hs'
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h x hx s hs'

end Silmaril.Elf
