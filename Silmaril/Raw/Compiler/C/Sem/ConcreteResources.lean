module

public import Silmaril.Cerberus.Assertion.RefinedC.Defs
public import Silmaril.Compiler.C.Sem.C1.Defs
/-! Byte ownership interpreted in actual flat C1 memory. This is not allocation/
provenance adequacy for Cerberus or Iris. Heap permissions remain proof-side. -/
@[expose] public section
namespace Silmaril.Cerberus.Assertion.ConcreteResources
open Silmaril.Compile.C.Sem
set_option maxRecDepth 4096

/-- A duplicable observation of one readable/writable byte. Exclusivity is imposed
by the resource footprint in `Realizes`, not by this proposition alone.
Bounds include physical backing: C1 permits constructing malformed memories. -/
structure OwnedByte (m : C1.Memory) (a : Nat) (v : UInt8) : Prop where
  lower : C1.base ≤ a
  upper : a + 1 ≤ m.sp
  writable : m.roTop ≤ a
  bytes_bound : a - C1.base < m.bytes.size
  init_bound : a - C1.base < m.init.size
  initialized : m.init[a - C1.base]! ≠ 0
  value : m.bytes[a - C1.base]! = v

def writeByte (m : C1.Memory) (a : Nat) (v : UInt8) : C1.Memory :=
  ⟨m.bytes.set! (a - C1.base) v, m.init.set! (a - C1.base) 1, m.roTop, m.sp⟩

theorem readBytes_owned {m : C1.Memory} {a : Nat} {v : UInt8} (h : OwnedByte m a v) :
    m.readBytes a 1 = .ok #[v] := by
  simp [C1.Memory.readBytes, C1.Memory.valid, h.lower, h.upper,
    h.initialized, h.value, pure, Except.pure, Bind.bind, Except.bind]

theorem writeBytes_owned {m : C1.Memory} {a : Nat} {old : UInt8}
    (h : OwnedByte m a old) (v : UInt8) :
    m.writeBytes a #[v] = .ok (writeByte m a v) := by
  simp [C1.Memory.writeBytes, C1.Memory.valid, h.lower, h.upper,
    Nat.not_lt.mpr h.writable, writeByte, pure, Except.pure, Bind.bind, Except.bind]

private theorem wrap_byte (v : UInt8) : C1.wrap 1 false (v.toNat : Int) = v.toNat := by
  have h := v.toNat_lt_size
  have hr : C1.inRange 1 false (v.toNat : Int) = true := by
    simp [C1.inRange, C1.lo, C1.hi]
    omega
  simp [C1.wrap, hr]

theorem load_ownedByte {m : C1.Memory} {a : Nat} {v : UInt8} (h : OwnedByte m a v) :
    C1.load m (.int 1 false) a = .ok (v.toNat : Int) := by
  simp only [C1.load, C1.width]
  rw [readBytes_owned h]
  simp [C1.Memory.ofLE, wrap_byte, pure, Except.pure, Bind.bind, Except.bind]

theorem store_ownedByte {m : C1.Memory} {a : Nat} {old : UInt8}
    (h : OwnedByte m a old) (v : UInt8) :
    C1.store m (.int 1 false) a (v.toNat : Int) = .ok (writeByte m a v) := by
  have enc : C1.Memory.le 1 (v.toNat : Int) = #[v] := by
    simp [C1.Memory.le, wrap_byte, Nat.mod_eq_of_lt v.toNat_lt_size]
  simpa only [C1.store, C1.width, enc, Bind.bind, Except.bind] using writeBytes_owned h v

theorem ownedByte_write {m : C1.Memory} {a : Nat} {old : UInt8}
    (h : OwnedByte m a old) (v : UInt8) : OwnedByte (writeByte m a v) a v := by
  refine ⟨h.lower, h.upper, h.writable, ?_, ?_, ?_, ?_⟩
  · simpa [writeByte] using h.bytes_bound
  · simpa [writeByte] using h.init_bound
  · simp [writeByte, h.init_bound]
  · simp [writeByte, h.bytes_bound]

/-- Writing one exclusive byte preserves a separately owned byte exactly. -/
theorem ownedByte_frame {m : C1.Memory} {a b : Nat} {old other : UInt8}
    (ha : OwnedByte m a old) (hb : OwnedByte m b other) (hne : a ≠ b)
    (v : UInt8) : OwnedByte (writeByte m a v) b other := by
  have hoff : a - C1.base ≠ b - C1.base := by
    have := ha.lower
    have := hb.lower
    omega
  refine ⟨hb.lower, hb.upper, hb.writable, ?_, ?_, ?_, ?_⟩
  · simpa [writeByte] using hb.bytes_bound
  · simpa [writeByte] using hb.init_bound
  · simpa [writeByte, ByteArray.getElem!_set!_ne, hoff] using hb.initialized
  · simpa [writeByte, ByteArray.getElem!_set!_ne, hoff] using hb.value

/-- A finite exclusive resource footprint interpreted in actual C1 byte memory.
One abstract address denotes exactly one byte in this initial interpretation. -/
def Realizes (m : C1.Memory) (h : Resources.Heap) : Prop :=
  (h.map Prod.fst).Nodup ∧ ∀ a n, (a, n) ∈ h →
    ∃ v : UInt8, n = (v.toNat : Int) ∧ OwnedByte m a v

/-- Spatial splitting is the existing resource logic; memory is the executable C1 state. -/
def Holds (ρ : Pure.Env) (p : Resources.Formula) (m : C1.Memory) : Prop :=
  ∃ h, p.holds ρ h ∧ Realizes m h

/-- Generated spatial goals use the same concrete footprint witnesses. -/
def LeanGoal (ρ : Pure.Env) (p : Resources.Formula) (m : C1.Memory) : Prop :=
  ∃ h, p.leanGoal ρ h ∧ Realizes m h

theorem leanGoal_correct (ρ : Pure.Env) (p : Resources.Formula) (m : C1.Memory) :
    LeanGoal ρ p m ↔ Holds ρ p m := by
  simp only [LeanGoal, Holds, Resources.Formula.leanGoal_correct]

theorem realizes_singleton (m : C1.Memory) (a : Nat) (n : Int) :
    Realizes m [(a, n)] ↔ ∃ v : UInt8, n = (v.toNat : Int) ∧ OwnedByte m a v := by
  simp [Realizes]

theorem pointsTo_iff (ρ : Pure.Env) (a : Nat) (term : Pure.Term) (m : C1.Memory) :
    Holds ρ (.pointsTo a term) m ↔
      ∃ v : UInt8, term.eval ρ = (v.toNat : Int) ∧ OwnedByte m a v := by
  simp only [Holds, Resources.Formula.holds, exists_eq_left, realizes_singleton]

/-- The existing RefinedC owned goal now has a concrete byte-memory reading.
The refinement's range still matters: interpreting this footprint does not silently
turn a wider integer cell into a byte cell. -/
theorem refinedC_owned_iff (ρ : Pure.Env) (r : RefinedC.IntRefinement)
    (a : Nat) (term : Pure.Term) (m : C1.Memory) :
    Holds ρ (r.owned a term) m ↔
      r.holds ρ (term.eval ρ) ∧
      ∃ v : UInt8, term.eval ρ = (v.toNat : Int) ∧ OwnedByte m a v := by
  simp only [Holds, RefinedC.IntRefinement.owned_correct]
  constructor
  · rintro ⟨h, ⟨hr, rfl⟩, concrete⟩
    exact ⟨hr, (realizes_singleton _ _ _).mp concrete⟩
  · rintro ⟨hr, concrete⟩
    exact ⟨_, ⟨hr, rfl⟩, (realizes_singleton _ _ _).mpr concrete⟩

/-- Any interpreted resource cell gives a successful real primitive load. -/
theorem realizes_load {m : C1.Memory} {h : Resources.Heap} (concrete : Realizes m h)
    {a : Nat} {n : Int} (member : (a, n) ∈ h) :
    C1.load m (.int 1 false) a = .ok n := by
  obtain ⟨v, rfl, owned⟩ := concrete.2 a n member
  exact load_ownedByte owned

/-- An interpreted RefinedC owned assertion justifies a real executable load. -/
theorem refinedC_owned_load {ρ : Pure.Env} {r : RefinedC.IntRefinement}
    {a : Nat} {term : Pure.Term} {m : C1.Memory}
    (owned : Holds ρ (r.owned a term) m) :
    C1.load m (.int 1 false) a = .ok (term.eval ρ) := by
  obtain ⟨_, v, value, concrete⟩ := (refinedC_owned_iff _ _ _ _ _).mp owned
  rw [value]
  exact load_ownedByte concrete

/-- Permissions are linear in the resource footprint, not runtime metadata. -/
theorem duplicate_impossible (ρ : Pure.Env) (a : Nat) (v w : Pure.Term) (m : C1.Memory) :
    ¬Holds ρ (.sep (.pointsTo a v) (.pointsTo a w)) m := by
  rintro ⟨h, holds, _⟩
  exact Resources.duplicate_ownership_impossible ρ a v w h holds

/-- A store preserves any disjoint finite resource footprint, including byte values. -/
theorem realizes_frame {m : C1.Memory} {h : Resources.Heap} {a : Nat} {old : UInt8}
    (owned : OwnedByte m a old) (concrete : Realizes m h)
    (outside : ∀ n, (a, n) ∉ h) (v : UInt8) : Realizes (writeByte m a v) h := by
  refine ⟨concrete.1, ?_⟩
  intro b n member
  obtain ⟨w, hn, hb⟩ := concrete.2 b n member
  refine ⟨w, hn, ownedByte_frame owned hb ?_ v⟩
  intro hab
  subst b
  exact outside n member

/-- Concrete two-byte initialized memory, with no assumed load/store equations. -/
def pairMemory (v w : UInt8) : C1.Memory :=
  ⟨ByteArray.mk #[v, w], ByteArray.mk #[1, 1], C1.base, C1.base + 2⟩

theorem pair_left (v w : UInt8) : OwnedByte (pairMemory v w) C1.base v := by
  refine ⟨le_rfl, ?_, le_rfl, ?_, ?_, ?_, ?_⟩
  · change C1.base + 1 ≤ C1.base + 2
    omega
  · change 0 < 2
    decide
  · change 0 < 2
    decide
  · change (1 : UInt8) ≠ 0
    decide
  · rfl

theorem pair_right (v w : UInt8) : OwnedByte (pairMemory v w) (C1.base + 1) w := by
  refine ⟨by omega, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change C1.base ≤ C1.base + 1
    omega
  · change 1 < 2
    decide
  · change 1 < 2
    decide
  · change (1 : UInt8) ≠ 0
    decide
  · rfl

/-- Every pair of byte values has a nonempty separated concrete footprint. -/
theorem pair_realizes (v w : UInt8) :
    Realizes (pairMemory v w)
      [(C1.base, (v.toNat : Int)), (C1.base + 1, (w.toNat : Int))] := by
  refine ⟨by simp, ?_⟩
  intro a n member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h
  · cases h
    exact ⟨v, rfl, pair_left v w⟩
  · cases h
    exact ⟨w, rfl, pair_right v w⟩

/-- RefinedC u8 singleton ownership has concrete initialized witnesses for every byte. -/
theorem refinedC_byte_realizable (ρ : Pure.Env) (v w : UInt8) :
    Holds ρ ((RefinedC.IntRefinement.mk .u8 (some (.literal (v.toNat : Int)))).owned
      C1.base (.literal (v.toNat : Int))) (pairMemory v w) := by
  apply (refinedC_owned_iff _ _ _ _ _).mpr
  refine ⟨?_, v, rfl, pair_left v w⟩
  have h := v.toNat_lt_size
  simp [RefinedC.IntRefinement.holds, RefinedC.IntegerType.admits,
    RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
    RefinedC.IntegerType.signed, RefinedC.IntegerType.bits, Pure.Term.eval]
  omega

/-- Boundary values exercise actual reading, writing, and the disjoint frame. -/
theorem boundary_example :
    C1.load (pairMemory 0 255) (.int 1 false) C1.base = .ok 0 ∧
    C1.load (writeByte (pairMemory 0 255) C1.base 254) (.int 1 false)
      (C1.base + 1) = .ok 255 := by
  exact ⟨load_ownedByte (pair_left 0 255),
    load_ownedByte (ownedByte_frame (pair_left 0 255) (pair_right 0 255) (by omega) 254)⟩

end Silmaril.Cerberus.Assertion.ConcreteResources
