module

public import Silmaril.Machine.Abi.SystemV.Defs
public import Silmaril.Proofs.Machine.Abi.SystemV.Basic
import Mathlib.Tactic.IntervalCases

/-!
# System V integer fragment: every argument tuple has an entry state

Proofs for `Silmaril.Machine.Abi.SystemV.Thms`. The witness `stateOf` sets RSP = 8,
writes return address 0 at RSP and the stack arguments in 8-byte slots above it,
maps one read/write region over the whole address space, and puts the first six
arguments, zero-extended, in RDI, RSI, RDX, RCX, R8 and R9.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.SystemV

open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV
open Silmaril.Cerberus.NativeTypes (Bytes)
open Silmaril.X86 (Reg)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

def toByte (b : UInt8) : BitVec 8 := BitVec.ofNat 8 b.toNat

def pad8 (b : Bytes) : List (BitVec 8) := b.map toByte ++ List.replicate (8 - b.length) 0

/-- The 64-bit word and object bytes of each argument. -/
def cells : {ks : List Scalar} → Arguments ks → List (BitVec 64 × Bytes)
  | [], .nil => []
  | k :: _, .cons v t => (Kind.word k v, Kind.encode k v) :: cells t

def image (cs : List (BitVec 64 × Bytes)) : List (BitVec 8) :=
  encodeWords [0] ++ (cs.drop 6).flatMap (fun c => pad8 c.2)

def stateOf (cs : List (BitVec 64 × Bytes)) : Silmaril.Machine.SystemV.Abi.Ffi.State where
  machine :=
    { core :=
        { regs := fun r => if r = .rsp then 8 else (cs.getD (gpArguments.idxOf r) (0, [])).1
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

theorem cells_length : ∀ {ks : List Scalar} (a : Arguments ks), (cells a).length = ks.length
  | [], .nil => rfl
  | _ :: _, .cons _ t => by simp [cells, cells_length t]

theorem cells_small : ∀ {ks : List Scalar} (a : Arguments ks), ∀ c ∈ cells a, c.2.length ≤ 8
  | [], .nil => by simp [cells]
  | k :: _, .cons v t => by
    intro c mem
    simp only [cells, List.mem_cons] at mem
    rcases mem with rfl | mem
    · cases k <;> simp [Kind.encode, Kind.bytes, Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat]
    · exact cells_small t c mem

theorem pad8_length {b : Bytes} (h : b.length ≤ 8) : (pad8 b).length = 8 := by
  simp [pad8]; omega

theorem flat_get (L : List (BitVec 64 × Bytes)) (small : ∀ c ∈ L, c.2.length ≤ 8)
    (m t : Nat) (hm : m < L.length) (ht : t < L[m].2.length) :
    (L.flatMap (fun c => pad8 c.2))[8 * m + t]? = some (toByte L[m].2[t]) := by
  induction L generalizing m with
  | nil => simp at hm
  | cons c L ih =>
    have hsmall := small c (by simp)
    have hc : (pad8 c.2).length = 8 := pad8_length hsmall
    cases m with
    | zero =>
      simp only [List.flatMap_cons, List.getElem_cons_zero] at ht ⊢
      rw [List.getElem?_append_left (by omega)]
      simp [pad8, List.getElem?_append_left, ht]
    | succ m =>
      simp only [List.flatMap_cons, List.getElem_cons_succ] at ht ⊢
      rw [List.getElem?_append_right (by omega), hc,
        show 8 * (m + 1) + t - 8 = 8 * m + t by omega]
      exact ih (fun c' h => small c' (by simp [h])) m (by simp at hm; omega) ht

theorem image_get (cs : List (BitVec 64 × Bytes)) (small : ∀ c ∈ cs, c.2.length ≤ 8)
    (i t : Nat) (hi : 6 ≤ i) (hlen : i < cs.length) (ht : t < cs[i].2.length) :
    (image cs)[8 + 8 * (i - 6) + t]? = some (toByte cs[i].2[t]) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = 6 + m := ⟨i - 6, by omega⟩
  unfold image
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons, List.length_nil,
    Nat.add_sub_cancel_left]
  rw [show 8 + 8 * m + t - 8 * (0 + 1) = 8 * m + t by omega]
  have := flat_get (cs.drop 6) (fun c h => small c (List.mem_of_mem_drop h)) m t
    (by simp; omega) (by simpa only [List.getElem_drop] using ht)
  rw [this]
  simp only [List.getElem_drop]

theorem image_head (cs : List (BitVec 64 × Bytes)) (t : Nat) (ht : t < 8) :
    (image cs)[t]? = (encodeWords [0])[t]? := by
  unfold image
  rw [List.getElem?_append_left (by simp; omega)]

theorem image_length (cs : List (BitVec 64 × Bytes)) (small : ∀ c ∈ cs, c.2.length ≤ 8) :
    (image cs).length = 8 + 8 * (cs.length - 6) := by
  have : ∀ L : List (BitVec 64 × Bytes), (∀ c ∈ L, c.2.length ≤ 8) →
      (L.flatMap (fun c => pad8 c.2)).length = 8 * L.length := by
    intro L h
    induction L with
    | nil => rfl
    | cons c L ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        pad8_length (h c (by simp)), ih (fun c' m => h c' (by simp [m]))]
      omega
  simp [image, this _ (fun c h => small c (List.mem_of_mem_drop h))]

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

theorem idxOf_gpArguments : ∀ j : Fin 6,
    gpArguments.idxOf (gpArguments[j.val]'(by simp [gpArguments])) = j.val := by decide

theorem read_rsp (cs : List (BitVec 64 × Bytes)) :
    (stateOf cs).machine.core.read .rsp = 8 := by
  simp [stateOf, Silmaril.X86.State.read]

theorem read_gp (cs : List (BitVec 64 × Bytes)) (i : Nat) (hi : i < 6) (hc : i < cs.length) :
    (stateOf cs).machine.core.read (gpArguments[i]'(by simp [gpArguments]; omega)) = cs[i].1 := by
  have hidx := idxOf_gpArguments ⟨i, hi⟩
  have hall : ∀ j : Fin 6, gpArguments[j.val]'(by simp [gpArguments]) ≠ .rsp := by decide
  have hne := hall ⟨i, hi⟩
  simp only [stateOf, Silmaril.X86.State.read, hne, ite_false] at hidx ⊢
  rw [hidx]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]

theorem register_bytes (k : Scalar) (v : k.Value) :
    Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat
        ((Kind.word k v).setWidth (8 * (Kind.object k).size)).toNat 0 (Kind.object k).size =
      Kind.encode k v := by
  rw [Kind.object_size]
  cases k
  all_goals
    simp only [Kind.word, Kind.encode, Kind.bytes]
    congr 1
  · change BitVec 32 at v
    have := v.isLt
    simp [BitVec.toNat_setWidth]; omega
  · change BitVec 32 at v
    have := v.isLt
    simp [BitVec.toNat_setWidth]; omega

theorem drop_cons {α : Type} {cs : List α} {i : Nat} {c : α} {rest : List α}
    (h : cs.drop i = c :: rest) : ∃ hi : i < cs.length, cs[i] = c ∧ cs.drop (i + 1) = rest := by
  have hi : i < cs.length := by
    by_contra hn
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  refine ⟨hi, ?_, ?_⟩
  · have := congrArg List.head? h
    rw [List.head?_drop, List.getElem?_eq_getElem hi] at this
    simpa using this
  · rw [← List.tail_drop, h]
    rfl

theorem argumentsAt (cs : List (BitVec 64 × Bytes)) (small : ∀ c ∈ cs, c.2.length ≤ 8)
    (bound : cs.length ≤ 127) :
    ∀ {ks : List Scalar} (a : Arguments ks) (i : Nat), cs.drop i = cells a →
      Silmaril.Machine.SystemV.Abi.Ffi.ArgumentsAt (stateOf cs) (ks.map Kind.spec) (toValues a)
        (intArgs (ks.map Kind.object) i)
  | [], .nil, _, _ => trivial
  | k :: ks, .cons v t, i, hdrop => by
    obtain ⟨hi, hci, hrest⟩ := drop_cons hdrop
    refine ⟨?_, argumentsAt cs small bound t (i + 1) hrest⟩
    unfold intArg
    split
    · rename_i r hr
      have hi6 : i < 6 := by
        by_contra hn
        rw [List.getElem?_eq_none (by simp [gpArguments]; omega)] at hr
        cases hr
      have hreg : r = gpArguments[i]'(by simp [gpArguments]; omega) := by
        rw [List.getElem?_eq_getElem (by simp [gpArguments]; omega)] at hr
        exact (Option.some.inj hr).symm
      refine ⟨rfl, Kind.encode k v, rfl, ?_⟩
      intro chunk mem
      simp only [List.mem_singleton] at mem
      subst mem hreg
      have hsize : (Kind.object k).size ≤ 8 := by cases k <;> decide
      refine ⟨?_, ?_⟩
      · simp [Kind.encode, Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat, Kind.object_size]
      · simp only [Silmaril.Machine.SystemV.Abi.Ffi.locationBytes, hsize, ite_true,
          read_gp cs i hi6 hi, hci, List.drop_zero]
        rw [register_bytes]
        simp [Kind.encode, Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat, Kind.object_size]
    · rename_i hr
      have hi6 : 6 ≤ i := by
        by_contra hn
        rw [List.getElem?_eq_getElem (by simp [gpArguments]; omega)] at hr
        cases hr
      refine ⟨rfl, Kind.encode k v, rfl, ?_⟩
      have hlen : (Kind.encode k v).length ≤ 8 := by
        have := small cs[i] (List.getElem_mem hi)
        rwa [hci] at this
      refine ⟨by rw [read_rsp]; simp; omega, ?_⟩
      rw [read_rsp]
      have := read_image cs (8 + 8 * (i - 6)) (Kind.encode k v).length
        ((Kind.encode k v).map fun byte => BitVec.ofNat 8 byte.toNat) (by simp)
        (by omega) (by
          intro t ht
          rw [image_get cs small i t hi6 hi (by rw [hci]; exact ht)]
          simp [hci, toByte])
      convert this using 2
      have h8 : (8 : BitVec 64).toNat = 8 := rfl
      rw [h8]
      omega

/-- Every argument tuple of the fragment has a System V entry state. -/
theorem entry_inhabited (profile : Profile) (planned : Planned profile) (p : Proto)
    (a : Arguments p.signature.arguments) : ∃ s, p.Entry profile planned a s := by
  have small := cells_small a
  have bound : (cells a).length ≤ 127 := by rw [cells_length]; exact p.arity
  refine ⟨stateOf (cells a), 0, ?_⟩
  constructor
  · rfl
  · exact argumentsAt (cells a) small bound a 0 rfl
  · show (((stateOf (cells a)).machine.core.read .rsp).toNat + 8) % 16 = 0
    rw [read_rsp]; rfl
  · show ((stateOf (cells a)).machine.core.read .rsp).toNat + 8 +
      alignUp (8 * (p.objects.length - 6)) 16 ≤ 2 ^ 64
    have : p.objects.length ≤ 127 := by simpa [Proto.objects, maxArity] using p.arity
    rw [read_rsp]
    simp only [alignUp, show (16 : Nat) ≠ 0 by omega, ite_false]
    simp
    omega
  · show (stateOf (cells a)).machine.memory.readBytes
      ((stateOf (cells a)).machine.core.read .rsp).toNat 8 = some (encodeWords [0])
    rw [read_rsp]
    have := read_image (cells a) 0 8 (encodeWords [0]) (by simp) (by omega) (by
      intro t ht
      rw [Nat.zero_add, image_head _ t ht, List.getElem?_eq_getElem])
    simpa using this
  · unfold Silmaril.Machine.SystemV.Abi.Ffi.SretAt
    split
    · rename_i size align h
      exact absurd h (intReturn_not_indirect p.signature.result size align)
    · rfl
  · rfl
  · rfl
  · intro count h
    cases h

end Silmaril.Proofs.Machine.Abi.SystemV
