module

public import Silmaril.Project.Shapes.SysV.Defs
public import Silmaril.Proofs.Project.Shapes.X86
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: a System V call entry for every argument tuple

`exists_callEntry`: for a placement whose code leaves room for a `frame`-byte stack frame and a
return address below the top of the address space, and a signature with at most six INTEGER
arguments (all in registers), every argument tuple has a machine state that is a `CallEntry`
and meets the System V entry obligations. One region maps every address read/write/execute;
`rsp` is the first `8 mod 16` address at least `frame + 9` bytes above the code; the arguments
are zero-extended into `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9`. Used by
`Silmaril.Project.Shapes.SysV.Enterable.of_fits`.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.SysV

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.FnContract (AbiEntry retOf)
open Silmaril.X86.SystemV.CApi (Signature Scalar Arguments)
open Silmaril.Project.Shapes (Placement)
open Silmaril.Project.Shapes.SysV
open Silmaril.Proofs.Project.Shapes.X86 (allRegion retEnc retEnc_length)

/-- The word an argument is passed in: zero-extended. -/
def argWord : (kind : Scalar) → kind.Value → Word
  | .int32, v => v.setWidth 64
  | .uint32, v => v.setWidth 64
  | .int64, v => v
  | .uint64, v => v
  | .pointer, v => v

theorem setWidth_setWidth32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt this]

theorem encodes_argWord : (kind : Scalar) → (v : kind.Value) →
    Silmaril.X86.SystemV.Encodes kind v (argWord kind v)
  | .int32, v => setWidth_setWidth32 v
  | .uint32, v => setWidth_setWidth32 v
  | .int64, _ => rfl
  | .uint64, _ => rfl
  | .pointer, _ => rfl

/-- The argument words, in order. -/
def argWords : {kinds : List Scalar} → Arguments kinds → List Word
  | _, .nil => []
  | _, .cons (kind := kind) v rest => argWord kind v :: argWords rest

theorem argWords_length : {kinds : List Scalar} → (a : Arguments kinds) →
    (argWords a).length = kinds.length
  | _, .nil => rfl
  | _, .cons _ rest => by simp [argWords, argWords_length rest]

/-- The stack pointer of the witness: `8 mod 16`, at least `frame + 9` bytes above the code. -/
def stackAt (p : Placement) (frame : Nat) : Nat :=
  16 * ((p.base.toNat + p.code.length + frame) / 16) + 24

/-- The return address at `stackAt`, then the code at its base. -/
def mem (p : Placement) (frame : Nat) : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ (stackAt p frame) retEnc) p.base.toNat p.code⟩

/-- The registers of the witness: `rsp`, and the argument words `W` in `rdi` … `r9`. -/
def regs (sp : Word) (W : List Word) : Reg → Word
  | .rsp => sp
  | .rdi => W.getD 0 0
  | .rsi => W.getD 1 0
  | .rdx => W.getD 2 0
  | .rcx => W.getD 3 0
  | .r8 => W.getD 4 0
  | .r9 => W.getD 5 0
  | _ => 0

/-- The witness state. -/
def st (p : Placement) (frame : Nat) (W : List Word) : MState :=
  ⟨⟨regs (BitVec.ofNat 64 (stackAt p frame)) W, p.entry, ⟨none, none, none, none, none, none⟩, 0⟩,
    mem p frame⟩

theorem permitted (p : Placement) (frame : Nat) (acc) (a n : Nat) (h : a + n ≤ 2 ^ 64)
    (ha : a < 2 ^ 64) : (mem p frame).Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  refine ⟨by simp only [Silmaril.Process.addressLimit]; omega,
    by simp only [Silmaril.Process.addressLimit]; omega, ?_⟩
  intro i hi
  have hlt : a + i < 18446744073709551616 := by omega
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Silmaril.Process.Region.Contains,
      Silmaril.Process.Permissions.allows, hlt]

/-- The argument registers hold the argument words, from index `i` on. -/
theorem argumentsAt (m : MState) (W : List Word)
    (hreg : ∀ j, j < 6 → ∀ r, Silmaril.X86.sysv64.intArgRegs[j]? = some r →
      m.core.read r = W.getD j 0) :
    ∀ {kinds : List Scalar} (a : Arguments kinds) (i : Nat), i + kinds.length ≤ 6 →
      W.drop i = argWords a → Silmaril.X86.SystemV.ArgumentsAt m a i
  | _, .nil, _, _, _ => trivial
  | _, .cons (kind := kind) v rest, i, hlen, hW => by
    have hi : i < 6 := by simp at hlen; omega
    have hd : W.getD i 0 = argWord kind v := by
      have h1 : (W.drop i).getD 0 0 = W.getD i 0 := by simp [List.getD_eq_getElem?_getD]
      rw [← h1, hW]; rfl
    have hrest : W.drop (i + 1) = argWords rest := by
      rw [← List.drop_drop, hW]; rfl
    refine ⟨⟨argWord kind v, ?_, encodes_argWord kind v⟩,
      argumentsAt m W hreg rest (i + 1) (by simp at hlen; omega) hrest⟩
    unfold Silmaril.X86.SystemV.ArgumentWord
    have : ∃ r, Silmaril.X86.sysv64.intArgRegs[i]? = some r := by
      interval_cases i <;> exact ⟨_, rfl⟩
    obtain ⟨r, hr⟩ := this
    rw [hr]; simp only; rw [hreg i hi r hr, hd]

/-- **A System V call entry for every argument tuple** (see the module docstring). -/
theorem exists_callEntry (p : Placement) (sig : Signature) (frame : Nat)
    (hargs : sig.arguments.length ≤ 6)
    (fits : p.base.toNat + p.code.length + frame + 48 ≤ 2 ^ 64)
    (hoff : p.off ≤ p.code.length) (a : Arguments sig.arguments) :
    ∃ m : MState, AbiEntry m.core m.memory ∧ CallEntry p sig frame a m := by
  let m := st p frame (argWords a)
  have hsp1 : p.base.toNat + p.code.length + frame + 9 ≤ stackAt p frame := by
    simp only [stackAt]; omega
  have hsp2 : stackAt p frame + 8 ≤ 2 ^ 64 := by simp only [stackAt]; omega
  have hspn : (BitVec.ofNat 64 (stackAt p frame)).toNat = stackAt p frame := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hrsp : rspOf m = stackAt p frame := hspn
  have hcode := p.base.isLt
  have loaded : Silmaril.X86.Ext.Loaded (mem p frame) p.base p.code :=
    Memory.readWith_eq _ _ _ p.code (permitted _ _ _ _ _ (by omega) p.base.isLt)
      fun i hi => Memory.install_get _ _ _ _ hi
  have ret : (mem p frame).readBytes (stackAt p frame) 8 = some retEnc := by
    have := Memory.readWith_eq (mem p frame) .read (stackAt p frame) retEnc
      (by rw [retEnc_length]; exact permitted _ _ _ _ _ hsp2 (by omega))
      fun i hi => by
        rw [retEnc_length] at hi
        show (Memory.install _ _ _).get? _ = _
        rw [Memory.install_outside _ _ _ _ (by omega)]
        exact Memory.install_get _ _ _ _ (by rw [retEnc_length]; exact hi)
    rwa [retEnc_length] at this
  have hretOf : retOf m.core m.memory = 0 := by
    have hm : m.memory = mem p frame := rfl
    unfold retOf
    have : m.core.read .rsp = BitVec.ofNat 64 (stackAt p frame) := rfl
    rw [this, hspn, hm, ret]
    simp [retEnc]
  refine ⟨m, ⟨?_, ?_⟩, ⟨⟨loaded, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show (BitVec.ofNat 64 (stackAt p frame)).toNat % 16 = 8
    rw [hspn]; simp only [stackAt]; omega
  · rw [hretOf]; show (mem p frame).readBytes (BitVec.ofNat 64 (stackAt p frame)).toNat 8 = _
    rw [hspn]; exact ret
  · refine argumentsAt m (argWords a) ?_ a 0 (by omega) (by simp)
    intro j hj r hr
    interval_cases j <;> (simp [Silmaril.X86.sysv64] at hr; subst hr; rfl)
  · rw [hrsp]; omega
  · rw [hrsp]; exact permitted _ _ _ _ _ (by omega) (by omega)
  · rw [hrsp]; exact permitted _ _ _ _ _ (by omega) (by omega)
  · left; rw [hrsp]; omega

end Silmaril.Proofs.Project.Shapes.SysV

end
