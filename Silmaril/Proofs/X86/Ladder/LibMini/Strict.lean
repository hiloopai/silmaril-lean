module

public import Silmaril.Proofs.X86.Ladder.LibMini.Memcpy
public import Silmaril.Proofs.X86.Ladder.LibMini.Memset
public import Silmaril.Proofs.X86.Ladder.LibMini.Strlen
public import Silmaril.X86.Cert.Kinds.Thms
public import Silmaril.Proofs.X86.Ladder.LibMini.NonVacuity

/-!
# libmini: first-return (strict) contracts

The certificates `memcpyCert`, `memsetCert`, `strlenCert` and their VCs (`cpy_vc`, `set_vc`,
`len_vc`), unchanged, through the generic certificate (`BlockCert.FunCert.strictW`): each
contract is strictly totally correct (its result is the *first* return) on entries whose
return address lies outside the function's code.

Non-vacuity of the restricted entry (`retOutside_st`, `*_strict_concrete`): the concrete entry
states of `NonVacuity.lean` (code at `0x400000`, return address `0x401000`) satisfy
`RetOutside`, so each strict spec applies to them and their result is the **first** return.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.LibMini

open Silmaril.X86 (MState Word Byte)
open Silmaril.X86
open Silmaril.X86.BlockCert
open Silmaril.X86.Ladder.LibMini
open Silmaril.X86.Stencils.ByteLoop

theorem memcpy_strict (entry : Word) :
    ((copyContract memcpyCode entry).restrict
      (FnContract.RetOutside Open.isa entry memcpyCode.length)).Strict Open.isa :=
  FunCert.strictW (F := memcpyCert entry) _ (entry := ⟨0x00, Bir.memcpy.L_401300⟩) (by simp [memcpyCert])
    (cpy_checked entry) (cpy_vc entry)
    fun m hab he => ⟨he.2.1, by rw [he.1]; simp [memcpyCert], rfl, hab, he⟩

theorem memset_strict (entry : Word) :
    ((fillContract memsetCode entry).restrict
      (FnContract.RetOutside Open.isa entry memsetCode.length)).Strict Open.isa :=
  FunCert.strictW (F := memsetCert entry) _ (entry := ⟨0x00, Bir.memset.L_401380⟩) (by simp [memsetCert])
    (set_checked entry) (set_vc entry)
    fun m hab he => ⟨he.2.1, by rw [he.1]; simp [memsetCert], rfl, hab, he⟩

theorem strlen_strict (entry : Word) :
    ((scanContract strlenCode entry).restrict
      (FnContract.RetOutside Open.isa entry strlenCode.length)).Strict Open.isa :=
  FunCert.strictW (F := strlenCert entry) _ (entry := ⟨0x00, lenL00⟩) (by simp [strlenCert])
    (len_checked entry) (len_vc entry)
    fun m hab he => ⟨he.2.1, by rw [he.1]; simp [strlenCert], rfl, hab, he⟩

/-! ## Non-vacuity of the strict (restricted) entries -/

namespace NonVacuity

open Silmaril.Machine.Execution (Reaches)

/-- The concrete return address `0x401000` lies outside any code shorter than `0x1000` bytes
at `0x400000`. -/
theorem retOutside_st {code data : List Byte} {a b c : Word} (hc : code.length < 0x1000) :
    FnContract.RetOutside Open.isa codeAt code.length (st code data a b c) := by
  intro o ho h
  have h' : retAt = codeAt + BitVec.ofNat 64 o :=
    (retOf_st (code := code) (data := data) (a := a) (b := b) (c := c)).symm.trans h
  have := congrArg BitVec.toNat h'
  simp [retAt, codeAt, BitVec.toNat_add] at this
  omega

theorem memcpy_strict_concrete : ∃ fin,
    FnContract.FirstReturn Open.isa (st memcpyCode [0x68, 0x69] 0xa000 0x9000 2) fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 0xa000 ∧ fin.core.read .rsp = 0x9000 ∧
    fin.memory.bytes.get? 0xa000 = some 0x68 ∧ fin.memory.bytes.get? 0xa001 = some 0x69 := by
  obtain ⟨fin, first, hres⟩ := FnContract.Spec.Strict.firstReturn (memcpy_strict codeAt) trivial
    memcpy_witness.1 ⟨memcpy_witness.2, retOutside_st (by decide)⟩
  have hp := hres.post.2.2
  exact ⟨fin, first, by rw [hres.abi.pc]; exact retOf_st, hres.post.1, hres.abi.stack,
    (hp 0 (by decide)).trans (data_get (by decide) 0 (by decide)),
    (hp 1 (by decide)).trans (data_get (by decide) 1 (by decide))⟩

theorem memset_strict_concrete : ∃ fin,
    FnContract.FirstReturn Open.isa (st memsetCode [] 0xa000 0x12345641 3) fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 0xa000 ∧ fin.core.read .rsp = 0x9000 ∧
    ∀ i < 3, fin.memory.bytes.get? (0xa000 + i) = some 0x41 := by
  obtain ⟨fin, first, hres⟩ := FnContract.Spec.Strict.firstReturn (memset_strict codeAt) trivial
    memset_witness.1 ⟨memset_witness.2, retOutside_st (by decide)⟩
  exact ⟨fin, first, by rw [hres.abi.pc]; exact retOf_st, hres.post.1, hres.abi.stack,
    fun i hi => hres.post.2.2 i hi⟩

theorem strlen_strict_concrete : ∃ fin,
    FnContract.FirstReturn Open.isa (st strlenCode [0x68, 0x69, 0] 0x9000 0 0) fin ∧
    fin.core.rip = retAt ∧ fin.core.read .rax = 2 ∧ fin.core.read .rsp = 0x9000 := by
  obtain ⟨fin, first, hres⟩ := FnContract.Spec.Strict.firstReturn (strlen_strict codeAt) trivial
    strlen_witness.1 ⟨⟨rfl, loaded (by decide), 2, strlen_witness.2⟩, retOutside_st (by decide)⟩
  exact ⟨fin, first, by rw [hres.abi.pc]; exact retOf_st, hres.post.1 2 strlen_witness.2,
    hres.abi.stack⟩

end NonVacuity

end Silmaril.Proofs.X86.Ladder.LibMini
