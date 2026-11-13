module

public import Silmaril.Wasm.FX.Asyncify.Shadow.Defs
public import Mathlib.Data.List.Forall2

/-!
# The shadow-stack strategy: the encoding, and the relation to `fstep`

* `encBuf_append`, `takeSV_map`, **`popRev_enc`**: a record written at the end of a memory prefix
  is read back by `popRev`, with the prefix before it;
* `Saved mem recs ent`: the table entry `ent` (end address, count) is the buffer of `recs` in
  `mem`, somewhere followed by more memory; it survives appending to the memory (`saved_append`);
* `RBuf`: the mode-dependent part of the relation: while unwinding, the records saved so far are
  the end of the memory; while rewinding, the records still to read end at `top`;
* **`MR`**: `fstep` and `mstep` configurations with equal stacks and registers, a table of saved
  buffers for the heap, and `RBuf`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Shadow

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC Silmaril.Wasm.FX.Asyncify.Shadow

variable {V : Type}

/-! ## The encoding -/

theorem encBuf_append (a b : List (Rec V)) : encBuf (a ++ b) = encBuf a ++ encBuf b := by
  induction a with
  | nil => rfl
  | cons q qs ih => simp only [List.cons_append, encBuf, ih, List.append_assoc]

theorem encBuf_single (q : Rec V) : encBuf [q] = enc q := by
  simp only [encBuf, List.append_nil]

theorem takeSV_map (xs : List (SV V)) (l : List (Cell V)) :
    takeSV xs.length (xs.map .sv ++ l) = some (xs, l) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons, List.map_cons, List.cons_append, takeSV, ih,
      Option.map_some]

/-- **A record at the end of a prefix is read back.** -/
theorem popRev_enc (L : List (Cell V)) (q : Rec V) :
    popRev (L ++ enc q).reverse = some (q, L.reverse) := by
  have hrev : (L ++ enc q).reverse =
      .num q.ops.length :: .num q.r :: .num q.fn :: (q.ops.reverse.map .sv ++ L.reverse) := by
    simp only [enc, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.map_reverse, List.cons_append]
  have htake : takeSV q.ops.length (q.ops.reverse.map .sv ++ L.reverse) =
      some (q.ops.reverse, L.reverse) := by
    rw [← List.length_reverse]; exact takeSV_map _ _
  rw [hrev]
  simp only [popRev, htake, Option.map_some, List.reverse_reverse]

/-! ## The relation -/

/-- A table entry for the buffer of `recs` in `mem`. -/
def Saved (mem : List (Cell V)) (recs : List (Rec V)) (ent : Nat × Nat) : Prop :=
  ent.2 = recs.length ∧
    ∃ pre rest, mem = pre ++ encBuf recs ++ rest ∧ ent.1 = (pre ++ encBuf recs).length

/-- The heap and the table. -/
abbrev HeapR (mem : List (Cell V)) (h : List (Option (List (Rec V))))
    (tbl : List (Option (Nat × Nat))) : Prop :=
  List.Forall₂ (Option.Rel (Saved mem)) h tbl

/-- The buffer register and the memory, by mode. -/
def RBuf (mode : Nat) (buf : List (Rec V)) (z : MCfg V) : Prop :=
  match mode with
  | 1 => z.cnt = buf.length ∧ ∃ pre, z.mem = pre ++ encBuf buf
  | 2 => z.cnt = buf.length ∧ ∃ pre rest, z.mem = pre ++ encBuf buf.reverse ++ rest ∧
      z.top = (pre ++ encBuf buf.reverse).length
  | _ => True

/-- **Related configurations.** -/
def MR (y : FCfg V) (z : MCfg V) : Prop :=
  HeapR z.mem y.heap z.tbl ∧ y.mode = z.mode ∧ y.tag = z.tag ∧ y.pay = z.pay ∧
    y.stack = z.stack ∧ RBuf y.mode y.buf z

theorem saved_append {mem : List (Cell V)} {recs : List (Rec V)} {ent : Nat × Nat}
    (h : Saved mem recs ent) (x : List (Cell V)) : Saved (mem ++ x) recs ent := by
  obtain ⟨hn, pre, rest, hm, he⟩ := h
  exact ⟨hn, pre, rest ++ x, by rw [hm]; simp only [List.append_assoc], he⟩

theorem heapR_append {mem : List (Cell V)} {h : List (Option (List (Rec V)))}
    {tbl : List (Option (Nat × Nat))} (hh : HeapR mem h tbl) (x : List (Cell V)) :
    HeapR (mem ++ x) h tbl := by
  refine List.Forall₂.imp (fun a b hab => ?_) hh
  cases hab with
  | some hs => exact .some (saved_append hs x)
  | none => exact .none

/-- The buffer just completed by an unwinding, at the end of the memory. -/
theorem saved_end {mem pre : List (Cell V)} {recs : List (Rec V)}
    (hm : mem = pre ++ encBuf recs) : Saved mem recs (mem.length, recs.length) :=
  ⟨rfl, pre, [], by rw [hm, List.append_nil], by rw [hm]⟩

/-- A one-record buffer written at the end of the memory. -/
theorem saved_one (mem : List (Cell V)) (q : Rec V) :
    Saved (mem ++ enc q) [q] ((mem ++ enc q).length, 1) :=
  saved_end (pre := mem) (by rw [encBuf_single])

end Silmaril.Proofs.Wasm.FX.Asyncify.Shadow
