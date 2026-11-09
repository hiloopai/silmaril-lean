module

public import Silmaril.X86.FnContract.Defs
public import Silmaril.X86.Ext.SymExec
public import Silmaril.Project.Shapes.X86.Defs

/-!
# Proofs: a System V entry state with given code loaded

`exists_entry`: for code `code` at `base` that leaves 32 bytes below the top of the address
space, a machine state with `code` fetchable at `base` (`Ext.Loaded`), `rip` at any given word
and the System V entry obligations (`FnContract.AbiEntry`). One region maps every address
read/write/execute; the return address `0` is stored at the first `8 mod 16` address at least
nine bytes above the code, which is `rsp`. Used by `Silmaril.Project.Shapes.X86.Thms`
(`Nonvacuous.of_entered`); `rip_inside`, the arithmetic of `EntersCode.of_entersAt`.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.X86

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region addressLimit)
open Silmaril.X86.FnContract (AbiEntry retOf)

/-- One region mapping every address read/write/execute. -/
def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩

/-- The return address `0`, as stack bytes. -/
def retEnc : List Byte := Silmaril.Machine.LittleEndian.encodeWords [0]

/-- The stack pointer of the witness: `8 mod 16`, above the code. -/
def stackAt (base : Word) (n : Nat) : Nat := 16 * ((base.toNat + n) / 16) + 24

/-- The return address at `stackAt`, then the code at `base`. -/
def mem (base : Word) (code : List Byte) : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ (stackAt base code.length) retEnc)
    base.toNat code⟩

/-- The witness: `rsp` at `stackAt`, `rip` at `rip`, every other register zero. -/
def st (base : Word) (code : List Byte) (rip : Word) : MState :=
  ⟨⟨fun r => match r with
      | .rsp => BitVec.ofNat 64 (stackAt base code.length) | _ => 0,
    rip, ⟨none, none, none, none, none, none⟩, 0⟩, mem base code⟩

theorem permitted (base : Word) (code : List Byte) (acc) (a n : Nat) (h : a + n ≤ 2 ^ 64)
    (ha : a < 2 ^ 64) : (mem base code).Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  refine ⟨by simp only [addressLimit]; omega, by simp only [addressLimit]; omega, ?_⟩
  intro i hi
  have hlt : a + i < 18446744073709551616 := by omega
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Region.Contains,
      Silmaril.Process.Permissions.allows, hlt]

theorem retEnc_length : retEnc.length = 8 := by
  simp [retEnc]

/-- **A System V entry state with `code` at `base` and `rip` at `rip`.** -/
theorem exists_entry (base : Word) (code : List Byte) (rip : Word)
    (fits : base.toNat + code.length + 32 ≤ 2 ^ 64) :
    ∃ s : MState, Silmaril.X86.Ext.Loaded s.memory base code ∧ s.core.rip = rip ∧
      AbiEntry s.core s.memory := by
  have hsp : base.toNat + code.length + 9 ≤ stackAt base code.length := by
    simp only [stackAt]; omega
  have hsp' : stackAt base code.length + 8 ≤ 2 ^ 64 := by
    simp only [stackAt]; omega
  have hspn : (BitVec.ofNat 64 (stackAt base code.length)).toNat = stackAt base code.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have loaded : Silmaril.X86.Ext.Loaded (mem base code) base code :=
    Memory.readWith_eq _ _ _ code (permitted _ _ _ _ _ (by omega) base.isLt)
      fun i hi => Memory.install_get _ _ _ _ hi
  have ret : (mem base code).readBytes (stackAt base code.length) 8 = some retEnc := by
    have := Memory.readWith_eq (mem base code) .read (stackAt base code.length) retEnc
      (by rw [retEnc_length]; exact permitted _ _ _ _ _ hsp' (by omega))
      fun i hi => by
        rw [retEnc_length] at hi
        show (Memory.install _ _ _).get? _ = _
        rw [Memory.install_outside _ _ _ _ (by omega)]
        exact Memory.install_get _ _ _ _ (by rw [retEnc_length]; exact hi)
    rwa [retEnc_length] at this
  have hrsp : (st base code rip).core.read .rsp = BitVec.ofNat 64 (stackAt base code.length) :=
    rfl
  have hretOf : retOf (st base code rip).core (st base code rip).memory = 0 := by
    have hm : (st base code rip).memory = mem base code := rfl
    unfold retOf
    rw [hrsp, hspn, hm, ret]
    simp [retEnc]
  refine ⟨st base code rip, loaded, rfl, ⟨?_, ?_⟩⟩
  · rw [hrsp, hspn]; simp only [stackAt]; omega
  · rw [hretOf, hrsp, hspn]; exact ret

end Silmaril.Proofs.Project.Shapes.X86

/-! ## The code conditions of the x86 shapes -/

namespace Silmaril.Proofs.Project.Shapes.X86

open Silmaril.X86 (MState Word Byte)
open Silmaril.Project.Shapes

/-- A function entered at `base + off`, with `code` loaded at `base` and `off` inside it, has
`rip` inside the code. -/
theorem rip_inside {M : Model} {s : MState} {base : Word} {code : List Byte} {off : Nat}
    (hoff : off < code.length) (hl : Silmaril.X86.Ext.Loaded (M.mem s) base code)
    (hr : (M.core s).rip = base + BitVec.ofNat 64 off) :
    Silmaril.X86.Ext.Loaded (M.mem s) (BitVec.ofNat 64 base.toNat) code ∧
      base.toNat ≤ (M.core s).rip.toNat ∧ (M.core s).rip.toNat < base.toNat + code.length := by
  have hw := hl.noWrap
  simp only [Silmaril.Process.addressLimit] at hw
  have hrip : (M.core s).rip.toNat = base.toNat + off := by
    rw [hr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hl, ?_, ?_⟩ <;> omega

end Silmaril.Proofs.Project.Shapes.X86

end
