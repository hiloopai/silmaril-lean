module
public import Silmaril.Compiler.C.Sem.C1LirMemory.Defs
public import Silmaril.Machine.X86.Lir.LinMem.Defs
/-! Initialized scalar and raw pointer loads in the flat source/target memories.
Actual read loops are derived from per-byte ownership; no successful-load premise
or scalar alignment requirement is added. Target bytes do not supply the source's
initialization, access permissions, or pointer provenance. -/

@[expose] public section
namespace Silmaril.Compile.C.Sem.C1LirScalarMemory
open Silmaril.Machine Silmaril.Cerberus.Assertion.ConcreteResources
open C1LirMemory

/-- Eight initialized writable bytes. Exclusivity remains a separate footprint
condition, as for OwnedByte. These models impose no scalar alignment check. -/
def OwnedBytes (source : C1.Memory) (address : Nat) (bytes : Fin 8 → UInt8) : Prop :=
  ∀ index, OwnedByte source (address + index.val) (bytes index)

def array (bytes : Fin 8 → UInt8) : Array UInt8 := Array.ofFn bytes

private theorem read_loop (source : C1.Memory) (indices : List Nat)
    (initialized : ∀ i ∈ indices, source.init[i]! ≠ 0) (out : Array UInt8) :
    (forIn indices out fun i acc => do
      if source.init[i]! == (0 : UInt8) then C0.ub "a read of uninitialised memory"
      pure (ForInStep.yield (acc.push source.bytes[i]!))) =
      (Except.ok (out ++ (indices.map fun i => source.bytes[i]!).toArray) : Except C0.Stop (Array UInt8)) := by
  induction indices generalizing out with
  | nil => simp [pure, Except.pure]
  | cons i rest ih =>
    have hi := initialized i (by simp)
    have tail := ih (fun j hj => initialized j (by simp [hj])) (out.push source.bytes[i]!)
    simp only [List.forIn_cons]
    simp only [hi, beq_iff_eq, ↓reduceIte, Bind.bind, Except.bind, pure, Except.pure]
    simp only [beq_iff_eq, Bind.bind, Except.bind, pure, Except.pure] at tail
    rw [tail]
    congr 1
    simp only [List.map_cons]
    rw [List.toArray_cons, Array.push_eq_append, Array.append_assoc]

private theorem readBytes_loop (source : C1.Memory) (address n : Nat)
    (valid : source.valid address n = true) :
    source.readBytes address n =
      forIn (List.range' (address - C1.base) n) (#[] : Array UInt8) (fun i acc => do
        if source.init[i]! == (0 : UInt8) then C0.ub "a read of uninitialised memory"
        pure (ForInStep.yield (acc.push source.bytes[i]!))) := by
  simp [C1.Memory.readBytes, valid, C0.ub]

theorem readBytes_span {source : C1.Memory} {address n : Nat} {bytes : Fin n → UInt8}
    (positive : 0 < n)
    (owned : ∀ index, OwnedByte source (address + index.val) (bytes index)) :
    source.readBytes address n = .ok (Array.ofFn bytes) := by
  have lower : C1.base ≤ address := by
    have h := (owned ⟨0, positive⟩).lower
    simpa only [Nat.add_zero] using h
  have upper : address + n ≤ source.sp := by
    have h := (owned ⟨n - 1, by omega⟩).upper
    change address + (n - 1) + 1 ≤ source.sp at h
    omega
  have initialized : ∀ i ∈ List.range' (address - C1.base) n, source.init[i]! ≠ 0 := by
    intro i member
    have bounds := List.mem_range'.mp member
    have ix : i - (address - C1.base) < n := by omega
    have initializedByte := (owned ⟨i - (address - C1.base), ix⟩).initialized
    have offset : address + (i - (address - C1.base)) - C1.base = i := by omega
    simpa only [offset] using initializedByte
  have values : ((List.range' (address - C1.base) n).map fun i => source.bytes[i]!).toArray =
      Array.ofFn bytes := by
    apply Array.ext
    · simp
    · intro i firstBound secondBound
      have bound : i < n := by simpa using secondBound
      have value := (owned ⟨i, bound⟩).value
      have offset : address + i - C1.base = address - C1.base + i := by omega
      simpa [offset] using value
  have valid : source.valid address n = true := by simp [C1.Memory.valid, lower, upper]
  rw [readBytes_loop source address n valid, read_loop source _ initialized]
  simp only [Array.empty_append, values]

theorem readBytes_owned {source : C1.Memory} {address : Nat} {bytes : Fin 8 → UInt8}
    (owned : OwnedBytes source address bytes) :
    source.readBytes address 8 = .ok (array bytes) :=
  readBytes_span (by decide) owned

private theorem fold_bytes (bytes : List UInt8) :
    bytes.foldr (fun byte acc => acc * 256 + byte.toNat) 0 =
      Silmaril.X86.Ext.leValue (bytes.map UInt8.toBitVec) := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih => simp [Silmaril.X86.Ext.leValue, ih, Nat.add_comm, Nat.mul_comm]

theorem ofLE_array {n : Nat} (bytes : Fin n → UInt8) :
    C1.Memory.ofLE (Array.ofFn bytes) =
      Silmaril.X86.Ext.leValue (List.ofFn fun i => (bytes i).toBitVec) := by
  unfold C1.Memory.ofLE
  rw [← Array.foldr_toList, Array.toList_ofFn, fold_bytes]
  simp only [List.map_ofFn]
  rfl

theorem value_agreement {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) {address : Nat} {bytes : Fin 8 → UInt8}
    (owned : OwnedBytes source address bytes) :
    C1.Memory.ofLE (array bytes) = (Lir.readLE target.bytes address 8).toNat := by
  rw [array, ofLE_array, Silmaril.X86.Backend.readLE_toNat target.bytes 8 address (by decide)]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact (related.byte (owned i)).symm

private theorem wrap_word (word : Lir.Word) :
    C1.wrap 8 false (word.toNat : Int) = word.toNat := by
  have bound := word.isLt
  have range : C1.inRange 8 false (word.toNat : Int) = true := by
    simp [C1.inRange, C1.lo, C1.hi]
    omega
  unfold C1.wrap
  rw [range]
  rfl

/-- Actual unsigned64 scalar loads agree from initialized byte ownership. The
source has no success premise; target initialization/permissions are not inferred. -/
theorem load_owned {source : C1.Memory} {target : Lir.Memory} (related : Rel source target)
    {address : Nat} {bytes : Fin 8 → UInt8} (owned : OwnedBytes source address bytes) :
    C1.load source (.int 8 false) address =
      .ok ((Lir.readLE target.bytes address 8).toNat : Int) ∧
    target.load .b8 .zero address = some (Lir.readLE target.bytes address 8) := by
  have lower := (owned 7).lower
  have backing := (owned 7).bytes_bound
  have fits := related.fits
  have inside : target.InBounds address .b8 := by
    change address + 8 ≤ target.size
    change address + 7 - C1.base < source.bytes.size at backing
    omega
  refine ⟨?_, ?_⟩
  · simp only [C1.load, C1.width]
    rw [readBytes_owned owned]
    simp only [Bind.bind, Except.bind]
    rw [value_agreement related owned]
    simp [wrap_word, pure, Except.pure]
  · simp [Lir.Memory.load, inside, Lir.Width.bytes, Lir.extend]

/-- Pointer metadata uses the same unsigned64 byte decoding in flat C1. This
establishes representation agreement, without pointer provenance. -/
theorem load_pointer_owned {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) {address : Nat} {bytes : Fin 8 → UInt8}
    (owned : OwnedBytes source address bytes) (pointee : Silmaril.Cerberus.Ctype) :
    C1.load source (.ptr pointee) address =
      .ok ((Lir.readLE target.bytes address 8).toNat : Int) ∧
    target.load .b8 .zero address = some (Lir.readLE target.bytes address 8) := by
  refine ⟨?_, (load_owned related owned).2⟩
  simp only [C1.load, C1.width]
  rw [readBytes_owned owned]
  simp only [Bind.bind, Except.bind]
  rw [value_agreement related owned]
  rfl

end Silmaril.Compile.C.Sem.C1LirScalarMemory
