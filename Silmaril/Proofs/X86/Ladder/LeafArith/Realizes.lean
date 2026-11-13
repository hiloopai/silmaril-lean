module

public import Silmaril.X86.Ladder.LeafArith.Defs
import Silmaril.X86.FnContract.SystemV.Thms
import Silmaril.Proofs.X86.Ladder.LeafArith.Bswap
import Silmaril.Proofs.X86.Ladder.LeafArith.SatAdd
import Silmaril.Proofs.X86.Ladder.LeafArith.Clamp
import Silmaril.Proofs.X86.Ladder.LeafArith.Gcd
/-!
# Rung 01 contracts as integer System V `Realizes` certificates

Each contract goes through `FnContract.toRealizes`; the obligations are the argument
registers (`r32_of_arg`: an ABI argument word in `rdi`/`rsi`/`rdx` has the C value as its low
32 bits) and the result encoding (`rax` low 32 bits). The footprint is empty, so unlike
`right_rot` the certificate is not indexed by the entry stack pointer.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.LeafArith

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86 Silmaril.X86.BlockCert Silmaril.X86.Ladder.LeafArith

/-- An ABI argument held in a register has the C value as the register's low 32 bits. -/
theorem r32_of_arg {m : MState} {i : Nat} {r : Reg} {v : BitVec 32}
    (hr : Silmaril.X86.sysv64.intArgRegs[i]? = some r)
    (h : ∃ word, Silmaril.C.Api.SysV.ArgumentWord m i word ∧
      (word.setWidth 32 = v)) : r32 r m = v := by
  obtain ⟨word, hw, he⟩ := h
  simp only [Silmaril.C.Api.SysV.ArgumentWord, hr] at hw
  rw [r32, hw, he]

theorem bswap_realizes :
    Silmaril.Machine.SystemV.Realizes sigU1 bswapResult noWrites (loadedAt 0xb0)
      (fun call final => Reaches Open.step call.initial final) := by
  refine FnContract.toRealizes ⟨bswapSpec, bswap_total⟩ sigU1 bswapResult noWrites
    (loadedAt 0xb0) ?_ ?_ ?_
  · intro _ call admitted d
    exact ⟨d.1, admitted.pc.trans d.2⟩
  · intro arguments call final admitted _ hpost
    match arguments, admitted, hpost with
    | .cons x .nil, admitted, hpost =>
      have hx : r32 .rdi call.initial = x := r32_of_arg rfl admitted.arguments.1
      change (final.core.read .rax).setWidth 32 = bswap32Spec x
      rw [show final.core.read .rax = _ from hpost, ← hx]
      simp
  · intro _ _ _ _ _ ha; exact ha.elim

theorem sat_realizes :
    Silmaril.Machine.SystemV.Realizes sigU2 satResult noWrites (loadedAt 0x90)
      (fun call final => Reaches Open.step call.initial final) := by
  refine FnContract.toRealizes ⟨satSpec, sat_total⟩ sigU2 satResult noWrites
    (loadedAt 0x90) ?_ ?_ ?_
  · intro _ call admitted d
    exact ⟨d.1, admitted.pc.trans d.2⟩
  · intro arguments call final admitted _ hpost
    match arguments, admitted, hpost with
    | .cons a (.cons b .nil), admitted, hpost =>
      have ha : r32 .rdi call.initial = a := r32_of_arg rfl admitted.arguments.1
      have hb : r32 .rsi call.initial = b := r32_of_arg rfl admitted.arguments.2.1
      change (final.core.read .rax).setWidth 32 = satAddSpec a b
      rw [show final.core.read .rax = _ from hpost, ← ha, ← hb]
      simp
  · intro _ _ _ _ _ ha; exact ha.elim

theorem gcd_realizes :
    Silmaril.Machine.SystemV.Realizes sigU2 gcdResult noWrites (loadedAt 0x0)
      (fun call final => Reaches Open.step call.initial final) := by
  refine FnContract.toRealizes ⟨gcdSpec', gcd_total⟩ sigU2 gcdResult noWrites
    (loadedAt 0x0) ?_ ?_ ?_
  · intro _ call admitted d
    exact ⟨d.1, admitted.pc.trans d.2⟩
  · intro arguments call final admitted _ hpost
    match arguments, admitted, hpost with
    | .cons a (.cons b .nil), admitted, hpost =>
      have ha : r32 .rdi call.initial = a := r32_of_arg rfl admitted.arguments.1
      have hb : r32 .rsi call.initial = b := r32_of_arg rfl admitted.arguments.2.1
      change (final.core.read .rax).setWidth 32 = gcdSpec a b
      rw [show final.core.read .rax = _ from hpost, ← ha, ← hb]
      simp
  · intro _ _ _ _ _ ha; exact ha.elim

theorem clamp_realizes :
    Silmaril.Machine.SystemV.Realizes sigI3 clampResult noWrites (loadedAt 0x30)
      (fun call final => Reaches Open.step call.initial final) := by
  refine FnContract.toRealizes ⟨clampSpec', clamp_total⟩ sigI3 clampResult noWrites
    (loadedAt 0x30) ?_ ?_ ?_
  · intro _ call admitted d
    exact ⟨d.1, admitted.pc.trans d.2⟩
  · intro arguments call final admitted _ hpost
    match arguments, admitted, hpost with
    | .cons x (.cons lo (.cons hi .nil)), admitted, hpost =>
      have hx : r32 .rdi call.initial = x := r32_of_arg rfl admitted.arguments.1
      have hl : r32 .rsi call.initial = lo := r32_of_arg rfl admitted.arguments.2.1
      have hh : r32 .rdx call.initial = hi := r32_of_arg rfl admitted.arguments.2.2.1
      change (final.core.read .rax).setWidth 32 = clampSpec x lo hi
      rw [show final.core.read .rax = _ from hpost, ← hx, ← hl, ← hh]
      simp
  · intro _ _ _ _ _ ha; exact ha.elim

end Silmaril.Proofs.X86.Ladder.LeafArith
