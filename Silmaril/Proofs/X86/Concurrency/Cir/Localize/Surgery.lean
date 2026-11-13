module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Embed
public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Basic

/-!
# Localisation: replacing the fragment's units by the block's

The units of a candidate are `A ++ F ++ C` (`F`: the fragment's units in
thread `i`, at positions `p1, p1 + 1, ...`); the new units are `A ++ G ++ C'` (`G`: the block's
reads then writes, at positions `p1, p1 + 1, ...`; `C'`: `C` with the positions of thread `i`
moved by `|G| - |F|`). The fragment's and the block's memory units touch only cell bytes
(`cb`), the others none. `Surg.exec x` keeps `rf` and `co` of the kept units, gives the block's
reads the initial value and its writes the coherence order of their positions.

* `Surg.wf`, `Surg.readsOk`: the new candidate is well-formed and its reads are right;
* `Surg.sc`, `Surg.tso`, `Surg.xl`: it is consistent under SC, TSO and XL when the old one is (XL
  needs the stores of thread `i` in `C` to be write-back);
* `Surg.final_off`, `Surg.final_on`: the final bytes off the cells are unchanged; on the cells
  they are the block's last writes.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte dummyEv rmwPairs writtenByte)
open Relation

/-- The data of a surgery. -/
structure Surg where
  A : List (Ev × List Byte)
  F : List (Ev × List Byte)
  G : List (Ev × List Byte)
  C : List (Ev × List Byte)
  i : Nat
  p1 : Nat
  cb : Nat → Bool

namespace Surg

variable (S : Surg)

/-- Move a unit of thread `i` after the fragment to its place after the block. -/
def mv (e : Ev) : Ev :=
  if e.tid = S.i then { e with pos := e.pos + S.G.length - S.F.length } else e

/-- The units after the block. -/
def C' : List (Ev × List Byte) := S.C.map fun u => (S.mv u.1, u.2)

/-- The old units. -/
def old : List (Ev × List Byte) := S.A ++ S.F ++ S.C

/-- The new units. -/
def new : List (Ev × List Byte) := S.A ++ S.G ++ S.C'

/-- The new index of an old (kept) unit; the fragment's units go out of range. -/
def σ (k : Nat) : Nat :=
  if k < S.A.length then k
  else if k < S.A.length + S.F.length then S.new.length + k
  else k - S.F.length + S.G.length

/-- The block's writes covering byte `y`, in order. -/
def gW (y : Nat) : List Nat :=
  ((List.range S.G.length).filter fun k =>
    (S.G[k]?.map fun u => u.1.isW && u.1.covers y).getD false).map (S.A.length + ·)

/-- **The new candidate.** -/
def exec (x : Exec) : Exec where
  evs := S.new.map Prod.fst
  rf := fun r y =>
    if r < S.A.length then (x.rf r y).map S.σ
    else if r < S.A.length + S.G.length then none
    else (x.rf (r - S.G.length + S.F.length) y).map S.σ
  co := fun y => if S.cb y then S.gW y else (x.co y).map S.σ
  rmw := rmwPairs (S.new.map Prod.fst)

/-! ## Indexing -/

theorem length_C' : S.C'.length = S.C.length := by simp [C']

theorem length_new : (S.new.map Prod.fst).length = S.A.length + S.G.length + S.C.length := by
  simp [new, length_C']; omega

theorem length_old : (S.old.map Prod.fst).length = S.A.length + S.F.length + S.C.length := by
  simp [old]; omega

theorem new_A {k : Nat} (hk : k < S.A.length) (h : k < (S.new.map Prod.fst).length) :
    (S.new.map Prod.fst)[k] = (S.A[k]).1 := by
  simp only [new, List.getElem_map, List.append_assoc]
  rw [List.getElem_append_left hk]

theorem new_G {k : Nat} (h1 : S.A.length ≤ k) (h2 : k < S.A.length + S.G.length)
    (h : k < (S.new.map Prod.fst).length) :
    (S.new.map Prod.fst)[k] = (S.G[k - S.A.length]'(by omega)).1 := by
  simp only [new, List.getElem_map, List.append_assoc]
  rw [List.getElem_append_right h1, List.getElem_append_left (by omega)]

theorem new_C {k : Nat} (h1 : S.A.length + S.G.length ≤ k) (h : k < (S.new.map Prod.fst).length) :
    (S.new.map Prod.fst)[k] =
      S.mv (S.C[k - S.A.length - S.G.length]'(by rw [length_new] at h; omega)).1 := by
  simp only [new, List.getElem_map, List.append_assoc]
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
  simp [C', Nat.sub_sub]

theorem old_A {k : Nat} (hk : k < S.A.length) (h : k < (S.old.map Prod.fst).length) :
    (S.old.map Prod.fst)[k] = (S.A[k]).1 := by
  simp only [old, List.getElem_map, List.append_assoc]
  rw [List.getElem_append_left hk]

theorem old_F {k : Nat} (h1 : S.A.length ≤ k) (h2 : k < S.A.length + S.F.length)
    (h : k < (S.old.map Prod.fst).length) :
    (S.old.map Prod.fst)[k] = (S.F[k - S.A.length]'(by omega)).1 := by
  simp only [old, List.getElem_map, List.append_assoc]
  rw [List.getElem_append_right h1, List.getElem_append_left (by omega)]

theorem old_C {k : Nat} (h1 : S.A.length + S.F.length ≤ k) (h : k < (S.old.map Prod.fst).length) :
    (S.old.map Prod.fst)[k] =
      (S.C[k - S.A.length - S.F.length]'(by rw [length_old] at h; omega)).1 := by
  simp only [old, List.getElem_map, List.append_assoc]
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]

theorem new_snd {k : Nat} (hk : k < S.new.length) :
    (S.new[k]).2 = if h : k < S.A.length then (S.A[k]).2
      else if h' : k < S.A.length + S.G.length then (S.G[k - S.A.length]'(by omega)).2
      else (S.C[k - S.A.length - S.G.length]'(by simp [new, length_C'] at hk; omega)).2 := by
  simp only [new, List.append_assoc]
  split
  · rename_i h; rw [List.getElem_append_left h]
  · rename_i h
    rw [List.getElem_append_right (by omega)]
    split
    · rename_i h'; rw [List.getElem_append_left (by omega)]
    · rename_i h'
      rw [List.getElem_append_right (by omega)]
      simp [C', Nat.sub_sub]

theorem old_snd {k : Nat} (hk : k < S.old.length) :
    (S.old[k]).2 = if h : k < S.A.length then (S.A[k]).2
      else if h' : k < S.A.length + S.F.length then (S.F[k - S.A.length]'(by omega)).2
      else (S.C[k - S.A.length - S.F.length]'(by simp [old] at hk; omega)).2 := by
  simp only [old, List.append_assoc]
  split
  · rename_i h; rw [List.getElem_append_left h]
  · rename_i h
    rw [List.getElem_append_right (by omega)]
    split
    · rename_i h'; rw [List.getElem_append_left (by omega)]
    · rename_i h'
      rw [List.getElem_append_right (by omega)]

theorem same_mv (e : Ev) : Same (S.mv e) e := by
  unfold mv; split <;> rfl

/-! ## Hypotheses -/

/-- What a surgery needs of its parts (`ib`: the initial bytes). -/
structure Hyp (ib : Nat → Byte) : Prop where
  posA : ∀ u ∈ S.A, u.1.tid = S.i → u.1.pos < S.p1
  posC : ∀ u ∈ S.C, u.1.tid = S.i → S.p1 + S.F.length ≤ u.1.pos
  lockC : ∀ u ∈ S.C, u.1.tid = S.i → u.1.isW = true → u.1.locked = true →
    S.p1 + S.F.length < u.1.pos
  posG : ∀ k (h : k < S.G.length), (S.G[k]).1.tid = S.i ∧ (S.G[k]).1.pos = S.p1 + k
  offAC : ∀ u ∈ S.A ++ S.C, u.1.isM = true → ∀ y, u.1.covers y = true → S.cb y = false
  onF : ∀ u ∈ S.F, u.1.isM = true → ∀ y, u.1.covers y = true → S.cb y = true
  onG : ∀ u ∈ S.G, ∀ y, u.1.covers y = true → S.cb y = true
  ovG : ∀ u ∈ S.A ++ S.C, ∀ v ∈ S.G, u.1.isM = true → u.1.accOverlap v.1 = false
  ovF : ∀ u ∈ S.A ++ S.C, ∀ v ∈ S.F, u.1.isM = true → v.1.isM = true →
    u.1.accOverlap v.1 = false
  memG : ∀ u ∈ S.G, (u.1.isR = true ∨ u.1.isW = true) ∧ u.1.locked = false ∧ u.1.ann = .wb ∧
    0 < u.1.size ∧ u.1.accAddr = u.1.addr ∧ u.1.accSize = u.1.size ∧
    (u.1.isW = true → u.1.data.length = u.1.size)
  rwG : ∀ k k' (hk : k < S.G.length) (hk' : k' < S.G.length), k ≤ k' →
    (S.G[k]).1.isW = true → (S.G[k']).1.isW = true
  readG : ∀ u ∈ S.G, u.1.isR = true → u.2 = u.1.bytes.map ib

end Surg

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
