module

/-!
# Cells and fragments over an abstract byte memory

A small, executable separation-logic kernel for low-level data structures, independent of any
ISA: an abstract byte memory `MemView` (value and write permission per byte), **cells**
(`width` bytes at `addr` holding `val`, little-endian) and **fragments** (lists of cells). A
data-structure predicate is a *function* from the abstract structure to its fragment, so

* holding is decidable (`instDecidableFragHolds`): a concrete memory dump can be checked;
* the footprint is explicit (`Frag.bytes`);
* the frame rule is one lemma (`Frag.holds_frame`): a fragment holds after any change outside
  its bytes.

Used by `Silmaril.Data.SepList`, `Silmaril.Data.Bitmap` and `Silmaril.Data.BoundaryTag`. Not yet related
to the byte-memory lenses of `Silmaril.Data.Layout`.
-/

@[expose] public section

namespace Silmaril.Data

/-- **An abstract byte memory**: each byte's value (`none`: unmapped or unbacked) and whether it
is writable. -/
structure MemView where
  byte : Nat → Option Nat
  writable : Nat → Bool

/-- Little-endian load of `k` bytes. -/
def MemView.load (v : MemView) : Nat → Nat → Option Nat
  | _, 0 => some 0
  | a, k + 1 => do
    let b ← v.byte a
    let r ← v.load (a + 1) k
    pure (b + 256 * r)

/-- **A cell**: `width` bytes at `addr` hold `val` (little-endian) and are writable. -/
structure Cell where
  addr : Nat
  width : Nat
  val : Nat
  deriving DecidableEq, Repr

/-- **A fragment**: the cells some part of a representation owns. -/
abbrev Frag := List Cell

/-- One cell holds in `v`. -/
def Cell.Holds (v : MemView) (c : Cell) : Prop :=
  v.load c.addr c.width = some c.val ∧ ∀ i < c.width, v.writable (c.addr + i) = true

instance instDecidableCellHolds (v : MemView) (c : Cell) : Decidable (c.Holds v) := by
  unfold Cell.Holds; exact inferInstance

/-- **A fragment holds** in `v`: every cell does. -/
def Frag.Holds (v : MemView) (f : Frag) : Prop := ∀ c ∈ f, c.Holds v

instance instDecidableFragHolds (v : MemView) (f : Frag) : Decidable (f.Holds v) := by
  unfold Frag.Holds; exact inferInstance

/-- The bytes a fragment owns. -/
def Frag.bytes (f : Frag) : List Nat := f.flatMap fun c => List.range' c.addr c.width

/-- Two fragments own disjoint bytes. -/
def Frag.Disjoint (f g : Frag) : Prop := ∀ a ∈ f.bytes, a ∉ g.bytes

/-- **A separated fragment**: its cells own pairwise disjoint bytes (no byte is owned twice).
The separating conjunction of its cells; decidable. -/
def Frag.Sep (f : Frag) : Prop := f.bytes.Nodup

instance instDecidableFragSep (f : Frag) : Decidable f.Sep := by
  unfold Frag.Sep; exact inferInstance

/-- Adjacent cells of an address-sorted fragment do not overlap. -/
def Frag.sepSortedB : List Cell → Bool
  | c :: d :: rest => decide (c.addr + c.width ≤ d.addr) && Frag.sepSortedB (d :: rest)
  | _ => true

/-- **Executable separation check** (`O(n log n)`, for memory dumps): sort the cells by address
and compare neighbours. Sound for `Frag.Sep` (`Silmaril.Data.Frag.sep_of_sepB`). -/
def Frag.sepB (f : Frag) : Bool :=
  Frag.sepSortedB (f.mergeSort fun c d => decide (c.addr ≤ d.addr))

/-- Two cells own disjoint bytes (arithmetic form of `Frag.Disjoint [c] [d]`). -/
def Cell.Apart (c d : Cell) : Prop :=
  ∀ a, c.addr ≤ a → a < c.addr + c.width → d.addr ≤ a → a < d.addr + d.width → False

/-- `v` and `v'` agree (values and permissions) at every byte of `S`. -/
def MemView.AgreeOn (v v' : MemView) (S : List Nat) : Prop :=
  ∀ a ∈ S, v.byte a = v'.byte a ∧ v.writable a = v'.writable a

/-- Write one cell (little-endian) into a view. -/
def MemView.store (v : MemView) (c : Cell) : MemView where
  byte a := if c.addr ≤ a ∧ a < c.addr + c.width then some (c.val / 256 ^ (a - c.addr) % 256)
    else v.byte a
  writable := v.writable

/-- Write cells in order. -/
def MemView.storeAll (v : MemView) (cs : List Cell) : MemView := cs.foldl MemView.store v

/-- Every byte of the spans `(start, length)` is backed and writable. -/
def MemView.Backs (v : MemView) (spans : List (Nat × Nat)) : Prop :=
  ∀ s ∈ spans, ∀ i < s.2, (v.byte (s.1 + i)).isSome ∧ v.writable (s.1 + i) = true

instance instDecidableBacks (v : MemView) (spans : List (Nat × Nat)) : Decidable (v.Backs spans) := by
  unfold MemView.Backs; exact inferInstance

/-! ## The frame rule -/

theorem MemView.load_congr (v v' : MemView) :
    ∀ (k a : Nat), (∀ i < k, v.byte (a + i) = v'.byte (a + i)) → v.load a k = v'.load a k
  | 0, _, _ => rfl
  | k + 1, a, h => by
    have h0 : v.byte a = v'.byte a := by simpa using h 0 (Nat.succ_pos k)
    have hr : v.load (a + 1) k = v'.load (a + 1) k :=
      MemView.load_congr v v' k (a + 1) fun i hi => by
        have := h (i + 1) (Nat.succ_lt_succ hi)
        rwa [show a + (i + 1) = a + 1 + i by omega] at this
    simp only [MemView.load, h0, hr]

/-- **The frame rule**: a fragment that holds in `v` holds in every `v'` agreeing with `v` on
the fragment's bytes. -/
theorem Frag.holds_frame {v v' : MemView} {f : Frag} (h : f.Holds v)
    (hag : v.AgreeOn v' f.bytes) : f.Holds v' := by
  intro c hc
  obtain ⟨hl, hw⟩ := h c hc
  have hb : ∀ i < c.width, c.addr + i ∈ f.bytes := fun i hi =>
    List.mem_flatMap.2 ⟨c, hc, List.mem_range'.2 ⟨i, hi, by omega⟩⟩
  refine ⟨?_, fun i hi => ?_⟩
  · rw [← MemView.load_congr v v' c.width c.addr fun i hi => (hag _ (hb i hi)).1]; exact hl
  · rw [← (hag _ (hb i hi)).2]; exact hw i hi

theorem Frag.holds_append {v : MemView} {f g : Frag} :
    (f ++ g).Holds v ↔ f.Holds v ∧ g.Holds v := by
  simp only [Frag.Holds, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-- A fragment's sub-fragment holds. -/
theorem Frag.holds_sub {v : MemView} {f g : Frag} (h : f.Holds v) (hs : ∀ c ∈ g, c ∈ f) :
    g.Holds v := fun c hc => h c (hs c hc)

end Silmaril.Data
