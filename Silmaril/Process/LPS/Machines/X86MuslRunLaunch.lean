module

public import Silmaril.Process.LPS.Machines.X86MuslRunImage

/-! # The musl launch as an explicit state with a computable memory view

`initial_ms` identifies the actual flag-oracle launch of the pinned executable
(`X86MuslStartup.initialOracle`) with `running c0 R M0 0`: an explicit core,
the launch's mapped regions as a literal list, and the launch byte map `M0`,
which is left symbolic. `realizes0` shows that `M0` holds exactly the bytes of
`V0`: the entry stack at `0x7fffffffe000`, zeros below it down to the 8 MiB
stack reservation, and the four loaded segments.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Silmaril.Process.LPS.Machines.X86MuslRun

open Silmaril.Process (Memory ByteMemory Region)
open Silmaril.Process.LPS.Machines.X86MuslStartup

/-! ## Packed bytes -/

/-- Byte `i` of the little-endian packing `n`. -/
def natByte (n i : Nat) : Byte := BitVec.ofNat 8 (n >>> (8 * i))

theorem leBytesOfNat_length (n N : Nat) : (leBytesOfNat n N).length = n := by
  induction n generalizing N with
  | zero => rfl
  | succ n ih => simp [leBytesOfNat, ih]

theorem leBytesOfNat_getElem? (n N i : Nat) (h : i < n) :
    (leBytesOfNat n N)[i]? = some (natByte N i) := by
  induction n generalizing N i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [leBytesOfNat, natByte]
    | succ i =>
      simp only [leBytesOfNat, List.getElem?_cons_succ]
      rw [ih _ _ (by omega)]
      simp only [natByte, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.mul_succ,
        Nat.pow_add, Nat.mul_comm (2 ^ (8 * i))]

/-! ## The launch memory -/

def spBase : Nat := 0x7fffffffe000

/-- The loaded segments, last segment first, as `segmentsView` resolves them. -/
def segView (a : Nat) : Option Byte :=
  if 0x403fd0 ≤ a ∧ a < 0x403fd0 + 0x2a8 then some (natByte seg3Nat (a - 0x403fd0))
  else if 0x402000 ≤ a ∧ a < 0x402000 + 0x54 then some (natByte seg2Nat (a - 0x402000))
  else if 0x401000 ≤ a ∧ a < 0x401000 + 0x874 then some (natByte seg1Nat (a - 0x401000))
  else if 0x400000 ≤ a ∧ a < 0x400000 + 0x190 then some (natByte seg0Nat (a - 0x400000))
  else none

theorem segmentsView_eq (a : Nat) : segmentsView segsLit a none = segView a := by
  unfold segmentsView segsLit
  rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  simp only [leBytesOfNat_length]
  unfold segView
  split_ifs <;> first
    | exact leBytesOfNat_getElem? _ _ _ (by omega)
    | rfl

/-- The launch view: entry stack, zero-filled stack reservation, segments. -/
def V0 : View := fun a =>
  if spBase ≤ a ∧ a < spBase + 4096 then some (natByte stackNat (a - spBase))
  else if 0x7fffff7fe000 ≤ a ∧ a < spBase then some 0
  else segView a

/-- The launch byte map, left symbolic. -/
def M0 : ByteMemory :=
  (initialMemory snapshot.image.segments entry.sp
    (X86Launch.entryStack snapshot.image entry input)).bytes

theorem realizes0 : Realizes M0 V0 := by
  intro a
  have sp : entry.sp.toNat = spBase := rfl
  have low : spBase - stackMaxSize.toNat = 0x7fffff7fe000 := rfl
  have stackLength : (X86Launch.entryStack snapshot.image entry input).length = 4096 := by
    rw [stack_eq, stackLit, leBytesOfNat_length]
  change (installWrapping (installWrapping (snapshot.image.segments.foldl
      (fun acc segment => installWrapping acc segment.base segment.bytes) ∅)
      (entry.sp.toNat - stackMaxSize.toNat)
      (List.replicate (entry.sp.toNat - (entry.sp.toNat - stackMaxSize.toNat)) 0))
      entry.sp.toNat (X86Launch.entryStack snapshot.image entry input)).get? a = V0 a
  rw [installWrapping_get_ite _ _ _ _ stack_nowrap,
    installWrapping_get_ite _ _ _ _ (by rw [List.length_replicate, sp, low]; decide),
    segments_foldl_get _ _ _ segments_nowrap, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.getElem?_empty, segments_eq, segmentsView_eq, stackLength, sp, low,
    List.length_replicate, stack_eq, stackLit]
  simp only [List.getElem?_replicate]
  clear sp low stackLength
  unfold V0 spBase
  split_ifs
  · exact leBytesOfNat_getElem? _ _ _ (by omega)
  · rfl
  · omega
  · rfl

/-! ## The launch state -/

/-- The launch's mapped regions: four segments and the stack reservation. -/
def R : List Region := imageRegions ++ [⟨0x7fffff7fe000, 0x801000, ⟨true, true, false⟩⟩]

theorem initial_regions :
    (initialMemory snapshot.image.segments entry.sp
      (X86Launch.entryStack snapshot.image entry input)).regions = R := by
  rw [initialMemory_regions, stack_eq]
  decide +kernel

/-- The launch core: RSP at the entry block, RIP at the ELF entry, flags clear. -/
def c0 : Silmaril.X86.State :=
  ⟨canonRegs 0x0 0x0 0x0 0x0 0x7fffffffe000 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0,
    0x401062, ⟨some false, some false, some false, some false, some false, some false⟩, 0x0⟩

/-- The actual flag-oracle launch is this explicit state. -/
theorem initial_ms (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) :
    (initialOracle platform oracle).ms = running c0 R M0 0 := by
  have memory : initialMemory snapshot.image.segments entry.sp
      (X86Launch.entryStack snapshot.image entry input) = ⟨R, M0⟩ := by
    rw [← initial_regions]
    rfl
  change (⟨⟨⟨_, initialMemory snapshot.image.segments entry.sp
      (X86Launch.entryStack snapshot.image entry input)⟩, none⟩, 0⟩ : X86FlagChoices.State) = _
  rw [memory, ← normCore_eq (Silmaril.X86.State.write _ _ _)]
  rfl

theorem initial_halted (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) : (initialOracle platform oracle).model.halted = none :=
  rfl

theorem initial_lazy (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) : (initialOracle platform oracle).model.vmLazy = [] :=
  rfl

theorem initial_tid (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) : (initialOracle platform oracle).model.tid = none :=
  rfl

end Silmaril.Process.LPS.Machines.X86MuslRun
