module

public import Silmaril.Machine.Abi.Win64.Defs
public import Silmaril.Proofs.Machine.Abi.SystemV.Entry
/-!
# Microsoft x64 integer fragment: every argument tuple has an entry state

Proofs for `Silmaril.Machine.Abi.Win64.Thms`. The witness `stateOf` sets RSP = 8,
writes return address 0 at RSP, 32 zero bytes of shadow space above it and the
stack arguments (index ≥ 4) in 8-byte slots above that, maps one read/write
region over the whole address space, and puts the first four arguments,
zero-extended, in RCX, RDX, R8 and R9. It reuses the byte-image helpers of the
System V witness (same topic).
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.Win64

open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV
open Silmaril.Machine.Abi.Win64
open Silmaril.Proofs.Machine.Abi.SystemV (toByte pad8 cells cells_length cells_small pad8_length
  flat_get register_bytes drop_cons)
open Silmaril.Cerberus.NativeTypes (Bytes)
open Silmaril.X86 (Reg)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- Return address, shadow space, then the stack arguments. -/
def image (cs : List (BitVec 64 × Bytes)) : List (BitVec 8) :=
  encodeWords [0] ++ List.replicate 32 0 ++ (cs.drop 4).flatMap (fun c => pad8 c.2)

def stateOf (cs : List (BitVec 64 × Bytes)) : Silmaril.Machine.SystemV.Abi.Ffi.State where
  machine :=
    { core :=
        { regs := fun r => if r = .rsp then 8 else (cs.getD (msArguments.idxOf r) (0, [])).1
          rip := 0
          flags := ⟨none, none, none, none, none, none⟩ }
      memory :=
        { regions := [⟨0, 2 ^ 64, ⟨true, true, false⟩⟩]
          bytes := Memory.install ∅ 8 (image cs) } }
  vectors _ := 0
  x87 _ := 0
  direction := false
  x87Mode := true
  mxcsr := 0
  x87Control := 0
  fsBase := 0

theorem image_get (cs : List (BitVec 64 × Bytes)) (small : ∀ c ∈ cs, c.2.length ≤ 8)
    (i t : Nat) (hi : 4 ≤ i) (hlen : i < cs.length) (ht : t < cs[i].2.length) :
    (image cs)[8 + 8 * i + t]? = some (toByte cs[i].2[t]) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = 4 + m := ⟨i - 4, by omega⟩
  unfold image
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, Silmaril.Machine.LittleEndian.encodeWords_length,
    List.length_cons, List.length_nil, List.length_replicate]
  rw [show 8 + 8 * (4 + m) + t - (8 * (0 + 1) + 32) = 8 * m + t by omega]
  have := flat_get (cs.drop 4) (fun c h => small c (List.mem_of_mem_drop h)) m t
    (by simp; omega) (by simpa only [List.getElem_drop] using ht)
  rw [this]
  simp only [List.getElem_drop]

theorem image_head (cs : List (BitVec 64 × Bytes)) (t : Nat) (ht : t < 8) :
    (image cs)[t]? = (encodeWords [0])[t]? := by
  unfold image
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]

/-- Reads from the witness memory are reads of the image. -/
theorem read_image (cs : List (BitVec 64 × Bytes)) (off len : Nat) (bs : List (BitVec 8))
    (hl : bs.length = len) (small : 8 + off + len < 2 ^ 64)
    (h : ∀ t (ht : t < len), (image cs)[off + t]? = some (bs[t]'(by omega))) :
    (stateOf cs).machine.memory.readBytes (8 + off) len = some bs := by
  unfold Memory.readBytes
  refine Silmaril.X86.Memory.readWith_eq_some_iff.mpr ⟨hl, ?_, ?_⟩
  · rw [Memory.Permitted, Memory.checkSpan_iff]
    refine ⟨by simp [Silmaril.Process.addressLimit]; omega,
      by simp [Silmaril.Process.addressLimit]; omega, ?_⟩
    intro offset hoff
    simp [Memory.permits, stateOf, Silmaril.Process.Region.Contains,
      Silmaril.Process.Permissions.allows]
    omega
  · intro index bound
    have hget := h index (by omega)
    have hb : off + index < (image cs).length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hget
      cases hget
    have := Memory.install_get ∅ 8 (image cs) (off + index) hb
    simp only [stateOf]
    rw [show 8 + off + index = 8 + (off + index) by omega, this]
    rw [List.getElem?_eq_getElem hb] at hget
    simpa using hget

theorem idxOf_msArguments : ∀ j : Fin 4,
    msArguments.idxOf (msArguments[j.val]'(by simp [msArguments])) = j.val := by decide

theorem read_rsp (cs : List (BitVec 64 × Bytes)) :
    (stateOf cs).machine.core.read .rsp = 8 := by
  simp [stateOf, Silmaril.X86.State.read]

theorem read_gp (cs : List (BitVec 64 × Bytes)) (i : Nat) (hi : i < 4) (hc : i < cs.length) :
    (stateOf cs).machine.core.read (msArguments[i]'(by simp [msArguments]; omega)) = cs[i].1 := by
  have hidx := idxOf_msArguments ⟨i, hi⟩
  have hall : ∀ j : Fin 4, msArguments[j.val]'(by simp [msArguments]) ≠ .rsp := by decide
  have hne := hall ⟨i, hi⟩
  simp only [stateOf, Silmaril.X86.State.read, hne, ite_false] at hidx ⊢
  rw [hidx]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]

theorem argumentsAt (cs : List (BitVec 64 × Bytes)) (small : ∀ c ∈ cs, c.2.length ≤ 8)
    (bound : cs.length ≤ 127) :
    ∀ {ks : List Scalar} (a : Arguments ks) (i : Nat), cs.drop i = cells a →
      Silmaril.Machine.SystemV.Abi.Ffi.ArgumentsAt (stateOf cs) (ks.map Kind.spec) (toValues a)
        (msArgs (ks.map Kind.object) i)
  | [], .nil, _, _ => trivial
  | k :: ks, .cons v t, i, hdrop => by
    obtain ⟨hi, hci, hrest⟩ := drop_cons hdrop
    refine ⟨?_, argumentsAt cs small bound t (i + 1) hrest⟩
    unfold msArg
    split
    · rename_i r hr
      have hi4 : i < 4 := by
        by_contra hn
        rw [List.getElem?_eq_none (by simp [msArguments]; omega)] at hr
        cases hr
      have hreg : r = msArguments[i]'(by simp [msArguments]; omega) := by
        rw [List.getElem?_eq_getElem (by simp [msArguments]; omega)] at hr
        exact (Option.some.inj hr).symm
      refine ⟨rfl, Kind.encode k v, rfl, ?_⟩
      intro chunk mem
      simp only [List.mem_singleton] at mem
      subst mem hreg
      have hsize : (Kind.object k).size ≤ 8 := by cases k <;> decide
      refine ⟨?_, ?_⟩
      · simp [Kind.encode, Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat, Kind.object_size]
      · simp only [Silmaril.Machine.SystemV.Abi.Ffi.locationBytes, hsize, ite_true,
          read_gp cs i hi4 hi, hci, List.drop_zero]
        rw [register_bytes]
        simp [Kind.encode, Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat, Kind.object_size]
    · rename_i hr
      have hi4 : 4 ≤ i := by
        by_contra hn
        rw [List.getElem?_eq_getElem (by simp [msArguments]; omega)] at hr
        cases hr
      refine ⟨rfl, Kind.encode k v, rfl, ?_⟩
      have hlen : (Kind.encode k v).length ≤ 8 := by
        have := small cs[i] (List.getElem_mem hi)
        rwa [hci] at this
      refine ⟨by rw [read_rsp]; simp; omega, ?_⟩
      rw [read_rsp]
      have := read_image cs (8 + 8 * i) (Kind.encode k v).length
        ((Kind.encode k v).map fun byte => BitVec.ofNat 8 byte.toNat) (by simp)
        (by omega) (by
          intro t ht
          rw [image_get cs small i t hi4 hi (by rw [hci]; exact ht)]
          simp [hci, toByte])
      convert this using 2
      have h8 : (8 : BitVec 64).toNat = 8 := rfl
      rw [h8]
      omega

/-- The witness state is a Microsoft x64 entry state for its arguments. -/
theorem entry_stateOf (p : Proto) (a : Arguments p.signature.arguments) :
    Entry p a (stateOf (cells a)) := by
  have small := cells_small a
  have bound : (cells a).length ≤ 127 := by rw [cells_length]; exact p.arity
  constructor
  · exact argumentsAt (cells a) small bound a 0 rfl
  · show (((stateOf (cells a)).machine.core.read .rsp).toNat + 8) % 16 = 0
    rw [read_rsp]; rfl
  · show ((stateOf (cells a)).machine.core.read .rsp).toNat + 8 +
      alignUp (8 * max p.signature.arguments.length 4) 16 ≤ 2 ^ 64
    have : p.signature.arguments.length ≤ 127 := p.arity
    rw [read_rsp]
    simp only [alignUp, show (16 : Nat) ≠ 0 by omega, ite_false]
    simp
    omega
  · refine ⟨0, ?_⟩
    show (stateOf (cells a)).machine.memory.readBytes
      ((stateOf (cells a)).machine.core.read .rsp).toNat 8 = some (encodeWords [0])
    rw [read_rsp]
    have := read_image (cells a) 0 8 (encodeWords [0]) (by simp) (by omega) (by
      intro t ht
      rw [Nat.zero_add, image_head _ t ht, List.getElem?_eq_getElem])
    simpa using this
  · rfl
  · rfl

/-- Every argument tuple of the fragment has a Microsoft x64 entry state. -/
theorem entry_inhabited (p : Proto) (a : Arguments p.signature.arguments) :
    ∃ s, Entry p a s :=
  ⟨_, entry_stateOf p a⟩

end Silmaril.Proofs.Machine.Abi.Win64
