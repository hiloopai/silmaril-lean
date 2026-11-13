module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs

/-!
# CSL with a release rule for plain stores on TSO

The logic (`Csl.Safe`) lets ownership leave
a thread only at a **draining** label (a locked read-modify-write, `mfence`, a futex call): a
non-draining atomic label (a plain `mov`) may write only owned cells and gives up none. That
rejects the textbook unlock, a plain release store of `0` to the lock word. This module adds
the missing rule, for the CIR-native TSO machine (`OStep .tso`).

## The logic `SafeR`

Threads own a physical heap `h` and a **ghost heap** `g` (cells no instruction touches; used as
exclusive tokens). The resource invariant `I : GProp` constrains the invariant's physical and
ghost heaps. A thread state carries a **pending flag** `p`: `true` after a release store until
the thread's next draining label. A label step meets `LabOkR` by one of three clauses:

* **local**: it touches only owned cells (as the non-atomic rule); the flag is kept, or reset by
  a draining label;
* **shared** (the atomic rule, with ghost re-split): only when the flag is clear or the label
  drains; for every invariant state disjoint from the thread it touches only the thread's and
  the invariant's cells, and re-splits both heaps;
* **release** (new): an atomic plain store `[a] := v` (any mode but `na`) that gives up a fixed
  part `hR`/`gR` of the thread's resources and keeps `h'`/`g'`, provided the
  **release obligation** `Oblig` holds: for *every* invariant state `hI, gI` disjoint from the
  thread's resources, `a` is in `hR ∪ hI` and `I` holds again of `hR ∪ hI` with the store
  applied and of `gR ∪ gI`. The flag is set.

## The side condition (triangular race freedom, Owens 2010, in the strong form)

While the flag is set the thread may take local labels and further releases only: **between a
release store and the thread's next draining label, the thread touches no cell it does not
own** (it reads no shared cell). Draining labels clear the flag; on the machine they need an
empty buffer, so every pending release has been flushed by then.

## Why it is sound on TSO (`Csl.Rel.rel_tso`)

A buffered release is installed in the invariant only when its buffer entry is **flushed**
(delayed release). The obligation is quantified over every invariant state, so it holds at the
flush, whatever other threads did meanwhile. FIFO flushing makes every earlier store of the
thread visible first, so memory then holds the released cells' values. Until the flush, the
released cells are owned by the buffer entry (`PRec`): nobody touches them. Other threads still
see the old value of the release's target in memory, which is what the invariant still says.
The side condition keeps the releasing thread from reading shared cells whose invariant view is
stale for it (it sees its own buffered store). XL is not covered: an XL write-back store may
pass an earlier `nt`/`str` store, so a release could be flushed before the stores it publishes.

The global invariant `XInvR` annotates each buffer entry with `none` or its release record and
keeps, per thread, the view agreement of owned cells and, per record, the agreement of the
released cells with the memory seen through the entries before it.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Csl.Rel

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-- Invariants and assertions over a physical heap and a ghost heap. -/
abbrev GProp := Heap → Heap → Prop

/-- The invariant as a `GProp`: the ghost heap is ignored. -/
def liftI (I0 : HProp) : GProp := fun hI _ => I0 hI

/-- **Separating conjunction of `GProp`s**: the physical and the ghost heap both
split into disjoint parts, one satisfying `P` and one satisfying `Q`. -/
def gsep (P Q : GProp) : GProp := fun h g =>
  ∃ h₁ h₂ g₁ g₂, Heap.Disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ Heap.Disjoint g₁ g₂ ∧
    g = Heap.union g₁ g₂ ∧ P h₁ g₁ ∧ Q h₂ g₂

/-- The cells of `h` are cells of `s` (domain containment). -/
def Dom (h s : Heap) : Prop := ∀ a, (h a).isSome → (s a).isSome

/-- **The release obligation** of the buffer entry `e`, which releases `hR`/`gR` and was issued
by a thread owning `H`/`G`: in every invariant state disjoint from `H`/`G`, the store's cell is
in `hR ∪ hI` and the invariant holds of the store applied to `hR ∪ hI` and of `gR ∪ gI`. -/
def Oblig (I : GProp) (e : Ent) (hR gR H G : Heap) : Prop :=
  ∀ hI gI, I hI gI → Heap.Disjoint H hI → Heap.Disjoint G gI →
    (∃ a v w, e = .st a v w ∧ (Heap.union hR hI a).isSome) ∧
      I (e.apply (Heap.union hR hI)) (Heap.union gR gI)

/-- **The obligations of one label step** of a thread with pending flag `p`, owning `h` and
`g`; `K p' h' g'` is the successor's requirement. See the module documentation. -/
def LabOkR (I : GProp) (K : Bool → Heap → Heap → Prop) (p : Bool) (l : Lab) (h g : Heap) :
    Prop :=
  l.isMem = true ∧
    (((∀ a, l.Touches a → (h a).isSome) ∧ (l.okH h → K (p && !l.drains) (l.updH h) g)) ∨
    (l.na = false ∧ (p = false ∨ l.drains = true) ∧
      ∀ hI gI, I hI gI → Heap.Disjoint h hI → Heap.Disjoint g gI →
        (∀ a, l.Touches a → (Heap.union h hI a).isSome) ∧
        (l.drains = false → ∀ a, (l.wval a).isSome → (h a).isSome) ∧
        (l.okH (Heap.union h hI) → ∃ h' hI' g' gI', Heap.Disjoint h' hI' ∧
          Heap.union h' hI' = l.updH (Heap.union h hI) ∧ Heap.Disjoint g' gI' ∧
          Heap.union g' gI' = Heap.union g gI ∧ I hI' gI' ∧ K false h' g' ∧
          (l.drains = false → Dom h h'))) ∨
    (∃ m fl a sz v, l = .wr m fl a sz v ∧ m ≠ .na ∧
      ∃ h' hR g' gR, Heap.Disjoint h' hR ∧ h = Heap.union h' hR ∧ Heap.Disjoint g' gR ∧
        g = Heap.union g' gR ∧ K true h' g' ∧
        Oblig I (.st a v (fl != .wb)) hR gR h g))

/-- **The safety functional** of `SafeR`: at `skip` the postcondition (which sees the flag)
holds, silent steps keep everything, and every label step meets `LabOkR`. -/
def SafeFR (I : GProp) (Q : Bool → Regs → Heap → Heap → Prop)
    (R : Bool → Stmt → Regs → Heap → Heap → Prop) (p : Bool) (s : Stmt) (rs : Regs)
    (h g : Heap) : Prop :=
  (s = .skip → Q p rs h g) ∧
  (∀ s' rs', TStep s rs none s' rs' → R p s' rs' h g) ∧
  (∀ l s' rs', TStep s rs (some l) s' rs' →
    LabOkR I (fun p' h' g' => R p' s' rs' h' g') p l h g)

/-- **Ownership safety with release stores** (greatest fixed point of `SafeFR`). -/
def SafeR (I : GProp) (Q : Bool → Regs → Heap → Heap → Prop) (p : Bool) (s : Stmt) (rs : Regs)
    (h g : Heap) : Prop :=
  ∃ R : Bool → Stmt → Regs → Heap → Heap → Prop, R p s rs h g ∧
    ∀ p s rs h g, R p s rs h g → SafeFR I Q R p s rs h g

/-- **The global start condition**: disjoint owned and invariant heaps (physical and ghost),
agreeing with memory, the invariant holding, each thread `SafeR` with its flag clear. -/
def GInvR (I : GProp) (Q : Nat → Bool → Regs → Heap → Heap → Prop) (N : Nat) (C : Cfg)
    (hs gs : Nat → Heap) (hI gI : Heap) : Prop :=
  (∀ t u, t ≠ u → Heap.Disjoint (hs t) (hs u)) ∧ (∀ t, Heap.Disjoint (hs t) hI) ∧
  (∀ t u, t ≠ u → Heap.Disjoint (gs t) (gs u)) ∧ (∀ t, Heap.Disjoint (gs t) gI) ∧
  (∀ t, Heap.Le (hs t) C.mem) ∧ Heap.Le hI C.mem ∧ I hI gI ∧
  ∀ t < N, SafeR I (Q t) false (C.ts t).1 (C.ts t).2 (hs t) (gs t)

/-- **Drains first**: the statement is not `skip`, every labelled step it can take drains, and
every silent step leads to such a statement (a finite silent prefix, then a draining label). Such
code is safe whatever its starting pending flag (`Csl.Rel.safeR_flag`). -/
inductive DF : Stmt → Regs → Prop
  | intro {s : Stmt} {rs : Regs} (hs : s ≠ .skip)
      (hl : ∀ l s' rs', TStep s rs (some l) s' rs' → l.drains = true)
      (ht : ∀ s' rs', TStep s rs none s' rs' → DF s' rs') : DF s rs

/-! ## The buffered invariant -/

/-- A release record: the released physical and ghost heaps and the issuer's resources. -/
structure PRec where
  hR : Heap
  gR : Heap
  H : Heap
  G : Heap

/-- An annotated store buffer: each entry with its release record, if it is a release. -/
abbrev ABuf := List (Ent × Option PRec)

/-- The physical cells held by the pending releases of a buffer. -/
def pH : ABuf → Heap
  | [] => Heap.empty
  | (_, some r) :: b => Heap.union r.hR (pH b)
  | (_, none) :: b => pH b

/-- The ghost cells held by the pending releases of a buffer. -/
def pG : ABuf → Heap
  | [] => Heap.empty
  | (_, some r) :: b => Heap.union r.gR (pG b)
  | (_, none) :: b => pG b

/-- The pending releases of a buffer hold disjoint cells. -/
def PDisj : ABuf → Prop
  | [] => True
  | (_, some r) :: b => Heap.Disjoint r.hR (pH b) ∧ Heap.Disjoint r.gR (pG b) ∧ PDisj b
  | (_, none) :: b => PDisj b

/-- **The buffer annotation is consistent**, read oldest first with `V` the memory as seen
through the entries before the current one: a plain store is to a cell the thread owns or a
later release holds; a release's cell is neither owned nor held by a later release, its
obligation holds, its released cells hold their values in `V`, and its issuer's resources are
still owned or held by it or a later release. -/
def AOk (I : GProp) (hs gs : Heap) : Heap → ABuf → Prop
  | _, [] => True
  | V, (e, none) :: b =>
      (match e with
        | .st c _ _ => (hs c).isSome ∨ (pH b c).isSome
        | .bar => True) ∧ AOk I hs gs (e.apply V) b
  | V, (e, some r) :: b =>
      (∃ a v w, e = .st a v w ∧ hs a = none ∧ pH b a = none) ∧ Oblig I e r.hR r.gR r.H r.G ∧
      Heap.Le r.hR V ∧ Dom r.H (Heap.union hs (pH ((e, some r) :: b))) ∧
      Dom r.G (Heap.union gs (pG ((e, some r) :: b))) ∧ AOk I hs gs (e.apply V) b

/-- **The buffered invariant** over the TSO machine, with ghost heaps `hs`/`gs` (threads),
`hI`/`gI` (invariant), flags `ps` and annotated buffers `ab`. `G0` is the ghost that must not
get lost (ghost conservation). -/
def XInvR (I : GProp) (Q : Nat → Bool → Regs → Heap → Heap → Prop) (N : Nat) (G0 : Heap)
    (C : OCfg) (hs gs : Nat → Heap) (hI gI : Heap) (ps : Nat → Bool) (ab : Nat → ABuf) : Prop :=
  (∀ t, (ab t).map Prod.fst = C.buf t) ∧
  (∀ t u, t ≠ u → Heap.Disjoint (Heap.union (hs t) (pH (ab t))) (Heap.union (hs u) (pH (ab u)))) ∧
  (∀ t, Heap.Disjoint (hs t) (pH (ab t)) ∧ PDisj (ab t)) ∧
  (∀ t, Heap.Disjoint (Heap.union (hs t) (pH (ab t))) hI) ∧
  (∀ t u, t ≠ u → Heap.Disjoint (Heap.union (gs t) (pG (ab t))) (Heap.union (gs u) (pG (ab u)))) ∧
  (∀ t, Heap.Disjoint (gs t) (pG (ab t))) ∧
  (∀ t, Heap.Disjoint (Heap.union (gs t) (pG (ab t))) gI) ∧
  Heap.Le hI C.mem ∧ I hI gI ∧
  (∀ t a v, hs t a = some v → view C.mem (C.buf t) a = some v) ∧
  (∀ t, AOk I (hs t) (gs t) C.mem (ab t)) ∧
  (∀ t, ps t = false → ∀ x ∈ ab t, x.2 = none) ∧
  (∀ t, N ≤ t → ab t = []) ∧
  (∀ t < N, SafeR I (Q t) (ps t) (C.ts t).1 (C.ts t).2 (hs t) (gs t)) ∧
  (∀ c, (G0 c).isSome →
    (gI c).isSome ∨ ∃ t < N, (gs t c).isSome ∨ (pG (ab t) c).isSome)

end Silmaril.X86.Concurrency.Cir.Csl.Rel
