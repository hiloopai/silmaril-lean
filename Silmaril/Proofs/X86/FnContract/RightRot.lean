module

public import Silmaril.X86.FnContract.RightRot.Defs
/-! The first concrete System V `Realizes` certificate from a generic function contract. -/

@[expose] public section

namespace Silmaril.Proofs.X86.FnContract.RightRot

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Decompile.RightRot
open Silmaril.X86
open Silmaril.X86.FnContract.RightRot
open Silmaril.Machine.Execution (Reaches)

/-- The ABI places the two arguments in `edi` and `esi`. -/
theorem args_of {m : MState} {value count : BitVec 32}
    (h : Silmaril.C.Api.SysV.ArgumentsAt m
      (Silmaril.C.Api.Arguments.cons (kind := .uint32) value
        (Silmaril.C.Api.Arguments.cons (kind := .uint32) count .nil)) 0) :
    args m = (value, count.toNat) := by
  obtain ⟨⟨w0, h0, e0⟩, ⟨w1, h1, e1⟩, -⟩ := h
  simp only [Silmaril.C.Api.SysV.ArgumentWord, Silmaril.X86.sysv64] at h0 h1
  simp only [Silmaril.C.Api.SysV.Encodes] at e0 e1
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at h0 h1
  subst e0 e1
  simp only [args, Silmaril.X86.Ext.Sz.read, h0, h1]
  rfl

theorem realizes (sp0 : Word) :
    Silmaril.Machine.SystemV.Realizes signature result (writes sp0) (Domain sp0)
      (fun call final => Reaches Open.step call.initial final) := by
  refine FnContract.toRealizes contract signature result (writes sp0) (Domain sp0) ?_ ?_ ?_
  · intro arguments call admitted d
    match arguments, admitted, d with
    | .cons value (.cons count .nil), admitted, d =>
      refine ⟨call.entry, ?_⟩
      have hargs := args_of admitted.arguments
      have hret := FnContract.retOf_of_readBytes admitted.returnAddress
      have h2 : (Silmaril.X86.Ext.Sz.d.read call.initial.core .rsi).toNat = count.toNat :=
        congrArg Prod.snd hargs
      refine ⟨admitted.pc, d.image, ?_, d.frameWrite, d.frameRead, d.spLow, d.apart, ?_, ?_⟩
      · rw [hret]; exact admitted.returnAddress
      · rw [h2]; exact d.countPos
      · rw [h2]; exact d.countLt
  · intro arguments call final admitted _ hpost
    match arguments, admitted, hpost with
    | .cons value (.cons count .nil), admitted, hpost =>
      have hargs := args_of admitted.arguments
      have h1 := hpost.1
      change Silmaril.X86.Ext.Sz.read .d final.core .rax =
        rightRotSpec (args call.initial).1 (args call.initial).2 at h1
      rw [hargs] at h1
      exact h1
  · intro arguments call a _ d ha
    simpa [writes, footprint, contract, FnContract.ofDecompiled, FnContract.decompiledSpec,
      d.sp] using ha

end Silmaril.Proofs.X86.FnContract.RightRot
