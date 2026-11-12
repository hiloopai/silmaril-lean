module

public import Silmaril.Libc.X86Alloc.Ladder.BumpAlign.Defs
public import Silmaril.Libc.X86Alloc.Pinned.BumpAlign
public import Silmaril.Libc.X86Alloc.Spec.Thms
public import Silmaril.X86.Ladder.Pinned.Thms
import Silmaril.Raw.Libc.X86Alloc.Ladder.BumpAlign

/-!
# Rung 03 (`bump-align`): results

* `malloc_sat`, `free_sat`: the code meets the reference model `ref` (functional strength) on
  `Open.isa`, through the canonical-frame steps (`Silmaril/Raw/Libc/X86Alloc/Ladder/Bump.lean`).
* `init`: the loaded static state (all zero) is the state `used = 0`.
* `code_loaded`, `data_loaded`: the pinned executable loads `layout.code` (`rx`) and
  `layout.data` (`rw`) where the layout says (kernel evaluation of the LPS loader).
* `sim`: `ref` simulates the bump capacity model with cost `roundUp 16` at `4096 - used`, on
  `used ≤ 4096 ∧ used % 16 = 0`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.BumpAlign

open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc (roundUp)

theorem malloc_sat :
    (mallocSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.BumpAlign.malloc_sat

theorem free_sat :
    (freeSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.BumpAlign.free_sat

/-- The initial state. -/
def s0 : ref.St := (0 : Nat)

theorem init : layout.Init ⊢ₛ iface.mmS s0 := Silmaril.Raw.Libc.X86Alloc.Ladder.BumpAlign.init

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.BumpAlign.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.BumpAlign.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

/-- The invariant: `used ≤ 4096` and 16-aligned. -/
def Inv : ref.St → Prop := fun (u : Nat) => u ≤ size ∧ u % 16 = 0

theorem sim : ref.Sim cap α Inv where
  avail s n hI ha := by
    change Nat at s
    have ha' : roundUp 16 n ≤ size - s := ha
    have hI' : s ≤ 4096 := hI.1
    have hn : n ≤ size - s := by simp only [roundUp] at ha'; omega
    simp only [ref, hn, ite_true]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat, arena] at this
    rw [show (0 : Silmaril.X86.Word).toNat = 0 from rfl] at this
    simp only [size] at hn
    omega
  alloc s n hI hm := by
    change Nat at s
    have hI' : s ≤ 4096 := hI.1
    have h16 : s % 16 = 0 := hI.2
    have hn : n ≤ size - s := by
      by_contra hc; exact hm (by simp only [ref, hc, ite_false])
    have hn' : n ≤ 4096 - s := hn
    refine ⟨⟨show s + roundUp 16 n ≤ size by simp only [size, roundUp]; omega,
      show (s + roundUp 16 n) % 16 = 0 by simp only [roundUp]; omega⟩, ?_⟩
    show size - (s + roundUp 16 n) = size - s - roundUp 16 n
    omega
  dealloc s _ _ hI _ := ⟨hI, rfl⟩

theorem inv_s0 : Inv s0 := ⟨Nat.zero_le size, rfl⟩

end Silmaril.Libc.X86Alloc.Ladder.BumpAlign
