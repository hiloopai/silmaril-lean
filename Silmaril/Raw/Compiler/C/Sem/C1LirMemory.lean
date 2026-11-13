module

public import Silmaril.Compiler.C.Sem.ConcreteResources.Defs
public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
/-! A reusable connection from initialized flat C1 byte resources to actual LIR
loads/stores. Addresses are preserved, with C1's array based at C1.base. Target
linear memory has no initialization or readonly metadata: successful source
accesses transfer, while their permission/initialization evidence remains an
explicit proof-side condition. No converse of source/target definedness or
allocation-provenance correspondence is claimed. -/

@[expose] public section
namespace Silmaril.Compile.C.Sem.C1LirMemory

open Silmaril.Machine
open Silmaril.Cerberus.Assertion
open ConcreteResources

def word (value : UInt8) : Lir.Word := value.toBitVec.setWidth 64

/-- All physically backed source bytes agree, including unspecified bytes. The
source's own initialization/permission checks are not erased by this relation. -/
structure Rel (source : C1.Memory) (target : Lir.Memory) : Prop where
  fits : C1.base + source.bytes.size ≤ target.size
  bytes : ∀ offset < source.bytes.size,
    target.bytes (C1.base + offset) = source.bytes[offset]!.toBitVec

/-- A concrete target witness for every C1 memory, including malformed memories
whose safe accesses still require the independent OwnedByte hypotheses. -/
def embed (source : C1.Memory) : Lir.Memory :=
  ⟨C1.base + source.bytes.size, fun address =>
    if C1.base ≤ address then source.bytes[address - C1.base]!.toBitVec else 0⟩

theorem embed_related (source : C1.Memory) : Rel source (embed source) := by
  refine ⟨le_rfl, ?_⟩
  intro offset _
  simp [embed]

def stored (target : Lir.Memory) (address : Nat) (value : UInt8) : Lir.Memory :=
  ⟨target.size, Lir.writeLE target.bytes address 1 (word value)⟩

theorem stored_byte (target : Lir.Memory) (address other : Nat) (value : UInt8) :
    (stored target address value).bytes other =
      if other = address then value.toBitVec else target.bytes other := by
  by_cases same : other = address
  · subst other
    simp [stored, Lir.writeLE, LittleEndian.wordByte, word]
  · change (if address ≤ other ∧ other < address + 1 then _ else _) = _
    rw [ite_eq_right (by omega), ite_eq_right same]

theorem Rel.byte {source : C1.Memory} {target : Lir.Memory} (related : Rel source target)
    {address : Nat} {value : UInt8} (owned : OwnedByte source address value) :
    target.bytes address = value.toBitVec := by
  have read := related.bytes (address - C1.base) owned.bytes_bound
  rw [Nat.add_sub_of_le owned.lower, owned.value] at read
  exact read

theorem Rel.inBounds {source : C1.Memory} {target : Lir.Memory} (related : Rel source target)
    {address : Nat} {value : UInt8} (owned : OwnedByte source address value) :
    target.InBounds address .b1 := by
  have lower := owned.lower
  have bound := owned.bytes_bound
  have fits := related.fits
  change address + 1 ≤ target.size
  omega

/-- The real source primitive and the real target load return the same byte. -/
theorem Rel.load_owned {source : C1.Memory} {target : Lir.Memory} (related : Rel source target)
    {address : Nat} {value : UInt8} (owned : OwnedByte source address value) :
    C1.load source (.int 1 false) address = .ok (value.toNat : Int) ∧
      target.load .b1 .zero address = some (word value) := by
  refine ⟨load_ownedByte owned, ?_⟩
  simp [Lir.Memory.load, related.inBounds owned, Lir.extend, Lir.Width.bytes,
    Lir.readLE, related.byte owned, word]

/-- One actual target store preserves the memory relation to the source byte
update. All other target bytes, including bytes outside the C1 backing, survive. -/
private theorem write_size (source : C1.Memory) (address : Nat) (value : UInt8) :
    (writeByte source address value).bytes.size = source.bytes.size :=
  ByteArray.size_set! _ _ _

private theorem write_bytes (source : C1.Memory) (address : Nat) (value : UInt8) :
    (writeByte source address value).bytes = source.bytes.set! (address - C1.base) value := rfl

private theorem write_at (source : C1.Memory) (address : Nat) (value : UInt8)
    (offset : Nat) (bound : address - C1.base < source.bytes.size) :
    (writeByte source address value).bytes[offset]! =
      if address - C1.base = offset then value else source.bytes[offset]! := by
  rw [write_bytes]
  exact ByteArray.getElem!_set! _ _ _ _ bound

private theorem write_agrees {source : C1.Memory} {target : Lir.Memory} (related : Rel source target)
    {address : Nat} {old : UInt8} (owned : OwnedByte source address old) (value : UInt8) :
    ∀ offset < (writeByte source address value).bytes.size,
      (stored target address value).bytes (C1.base + offset) =
        (writeByte source address value).bytes[offset]!.toBitVec := by
  intro offset bound
  rw [write_size] at bound
  rw [stored_byte]
  rw [write_at source address value offset owned.bytes_bound]
  by_cases same : C1.base + offset = address
  · have index : address - C1.base = offset := by omega
    rw [ite_eq_left same, ite_eq_left index]
  · have different : address - C1.base ≠ offset := by
      have lower := owned.lower
      omega
    rw [ite_eq_right same, ite_eq_right different]
    exact related.bytes offset bound

theorem Rel.write {source : C1.Memory} {target : Lir.Memory} (related : Rel source target)
    {address : Nat} {old : UInt8} (owned : OwnedByte source address old) (value : UInt8) :
    Rel (writeByte source address value) (stored target address value) := by
  refine ⟨?_, write_agrees related owned value⟩
  rw [write_size]
  exact related.fits

theorem Rel.store_owned {source : C1.Memory} {target : Lir.Memory} (related : Rel source target)
    {address : Nat} {old : UInt8} (owned : OwnedByte source address old) (value : UInt8) :
    C1.store source (.int 1 false) address (value.toNat : Int) =
        .ok (writeByte source address value) ∧
      target.store .b1 address (word value) = some (stored target address value) ∧
      Rel (writeByte source address value) (stored target address value) := by
  exact ⟨store_ownedByte owned value,
    by simp [Lir.Memory.store, related.inBounds owned, Lir.Width.bytes, stored],
    related.write owned value⟩

/-- An exclusive resource footprint over target bytes. Runtime permissions are
absent from LIR; distinctness here remains part of the proof-side resource model. -/
def Realizes (target : Lir.Memory) (heap : Resources.Heap) : Prop :=
  (heap.map Prod.fst).Nodup ∧ ∀ address integer, (address, integer) ∈ heap →
    ∃ value : UInt8, integer = (value.toNat : Int) ∧ address < target.size ∧
      target.bytes address = value.toBitVec

def Access (source : C1.Memory) (heap : Resources.Heap) : Prop :=
  ∀ address integer, (address, integer) ∈ heap → ∃ value, OwnedByte source address value

theorem Rel.realizes {source : C1.Memory} {target : Lir.Memory} (related : Rel source target)
    {heap : Resources.Heap} (concrete : ConcreteResources.Realizes source heap) :
    Realizes target heap := by
  refine ⟨concrete.1, ?_⟩
  intro address integer member
  obtain ⟨value, equality, owned⟩ := concrete.2 address integer member
  have inside := related.inBounds owned
  exact ⟨value, equality, by change address + 1 ≤ target.size at inside; omega,
    related.byte owned⟩

/-- Initialization and writable access cannot be recovered from LIR bytes.
Keeping that evidence explicit gives an exact resource interpretation theorem. -/
theorem Rel.realizes_iff {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) (heap : Resources.Heap) :
    ConcreteResources.Realizes source heap ↔ Access source heap ∧ Realizes target heap := by
  constructor
  · intro concrete
    refine ⟨?_, related.realizes concrete⟩
    intro address integer member
    obtain ⟨value, _, owned⟩ := concrete.2 address integer member
    exact ⟨value, owned⟩
  · rintro ⟨access, concrete⟩
    refine ⟨concrete.1, ?_⟩
    intro address integer member
    obtain ⟨old, owned⟩ := access address integer member
    obtain ⟨value, equality, _, byte⟩ := concrete.2 address integer member
    have same : value = old := by
      apply UInt8.toNat_inj.mp
      exact congrArg BitVec.toNat (byte.symm.trans (related.byte owned))
    subst value
    exact ⟨old, equality, owned⟩

/-- Concrete C1 spatial assertions are equivalent to the same resource formula
over target bytes plus the source access evidence, for every supported formula. -/
theorem Rel.holds_iff {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) (valuation : Pure.Env) (formula : Resources.Formula) :
    ConcreteResources.Holds valuation formula source ↔
      ∃ heap, formula.holds valuation heap ∧ Access source heap ∧ Realizes target heap := by
  simp only [ConcreteResources.Holds, related.realizes_iff]

end Silmaril.Compile.C.Sem.C1LirMemory
