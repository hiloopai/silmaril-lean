module

public import Silmaril.Libc.X86Alloc.Ladder.Bump.Defs
public import Silmaril.Libc.X86Alloc.Pinned.Bump
public import Silmaril.Libc.X86Alloc.Spec.Thms
public import Silmaril.X86.Ladder.Pinned.Thms
import Silmaril.Raw.Libc.X86Alloc.Ladder.Bump

/-!
# Rung 02 (`bump`): results

* `malloc_sat`, `free_sat`: the code meets the reference model `ref` (functional strength) on
  `Open.isa`, through the canonical-frame steps (`Silmaril/Raw/Libc/X86Alloc/Ladder/Bump.lean`).
* `init`: the loaded static state (all zero) is the state `used = 0`.
* `code_loaded`, `data_loaded`: the pinned executable loads `layout.code` (`rx`) and
  `layout.data` (`rw`) where the layout says (kernel evaluation of the LPS loader).
* `sim`: `ref` simulates the bump capacity model at `4096 - used`, on `used ≤ 4096`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.Bump

open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc

theorem malloc_sat :
    (mallocSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.Bump.malloc_sat

theorem free_sat :
    (freeSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.Bump.free_sat

/-- The initial state. -/
def s0 : ref.St := (0 : Nat)

theorem init : layout.Init ⊢ₛ iface.mmS s0 := Silmaril.Raw.Libc.X86Alloc.Ladder.Bump.init

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Bump.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Bump.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

/-- The invariant: `used ≤ 4096`. -/
def Inv : ref.St → Prop := fun (u : Nat) => u ≤ size

theorem sim : ref.Sim cap α Inv where
  avail s n hI ha := by
    change Nat at s
    have ha' : n ≤ size - s := ha
    have hI' : s ≤ 4096 := hI
    simp only [ref, ha', ite_true]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat, arena] at this
    rw [show (0 : Silmaril.X86.Word).toNat = 0 from rfl] at this
    simp only [size] at ha'
    omega
  alloc s n hI hm := by
    change Nat at s
    have hI' : s ≤ 4096 := hI
    have hn : n ≤ size - s := by
      by_contra hc; exact hm (by simp only [ref, hc, ite_false])
    have hn' : n ≤ 4096 - s := hn
    refine ⟨show s + n ≤ size by simp only [size]; omega, ?_⟩
    show size - (s + n) = size - s - n
    omega
  dealloc s _ _ hI _ := ⟨hI, rfl⟩

theorem inv_s0 : Inv s0 := Nat.zero_le size

end Silmaril.Libc.X86Alloc.Ladder.Bump
