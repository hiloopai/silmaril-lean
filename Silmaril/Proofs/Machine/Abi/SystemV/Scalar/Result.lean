module

public import Silmaril.Machine.Abi.SystemV.Scalar.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Thms

/-!
# System V scalar fragment: result read-back

Proofs for `Silmaril.Machine.Abi.SystemV.Scalar.Thms`: a scalar result is the object
representation of the value in the low bytes of RAX (INTEGER) or XMM0 (SSE); an aggregate in
registers is its eightbytes in RAX/RDX and XMM0/XMM1; a MEMORY aggregate is its bytes at the
hidden pointer passed in RDI, which RAX returns.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.SystemV.Scalar

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (callOf Options)
open Silmaril.Machine.Abi.SystemV.Scalar

theorem placeReturn_scalar (k : Kind) :
    placeReturn (some (.scalar k)) =
      .direct [⟨0, k.bytes, if k.sse then .vector 0 0 else .gp .rax⟩] := by
  cases k <;> rfl

theorem resultAt_some (profile : Profile) (planned : Planned profile) (args : List Arg)
    (k : Kind) (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State)
    (r : k.Value) :
    Ffi.ResultAt ((⟨args, some (.scalar k), h⟩ : Proto).ffi profile planned)
        ((⟨args, some (.scalar k), h⟩ : Proto).call s 0) s' r ↔
      Ffi.locationBytes s' (if k.sse then .vector 0 0 else .gp .rax) k.bytes =
        some (k.encode r) := by
  have hlen : (k.encode r).length = k.bytes := by simp [Kind.encode, Ffi.bytesOfNat]
  have hp : ((⟨args, some (.scalar k), h⟩ : Proto).ffi profile planned).callPlan.result =
      .direct [⟨0, k.bytes, if k.sse then .vector 0 0 else .gp .rax⟩] := placeReturn_scalar k
  constructor
  · rintro ⟨bytes, enc, ch⟩
    change bytes = k.encode r at enc
    subst enc
    rw [hp] at ch
    have := (ch _ (List.mem_singleton_self _)).2
    rw [List.drop_zero, List.take_of_length_le (by rw [hlen])] at this
    exact this
  · intro e
    refine ⟨k.encode r, rfl, ?_⟩
    rw [hp]
    intro chunk mem
    simp only [List.mem_singleton] at mem
    subst mem
    refine ⟨by simp [hlen], ?_⟩
    rw [List.drop_zero, List.take_of_length_le (by rw [hlen])]
    exact e

theorem resultAt_none (profile : Profile) (planned : Planned profile) (args : List Arg)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State)
    (r : PUnit) :
    Ffi.ResultAt ((⟨args, none, h⟩ : Proto).ffi profile planned)
      ((⟨args, none, h⟩ : Proto).call s 0) s' r := rfl

/-- A MEMORY aggregate result: its bytes at the hidden pointer passed in RDI, which RAX
returns. -/
theorem resultAt_indirect (profile : Profile) (planned : Planned profile) (args : List Arg)
    (g : Agg) (ok : g.ok = true) (hm : g.eights = .memory)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State)
    (r : g.Value) :
    Ffi.ResultAt ((⟨args, some (.agg g ok), h⟩ : Proto).ffi profile planned)
        ((⟨args, some (.agg g ok), h⟩ : Proto).call s 0) s' r ↔
      Ffi.StoredAt s' (s.machine.core.read .rdi).toNat r.1 ∧
        (s'.machine.core.read .rax).toNat = (s.machine.core.read .rdi).toNat := by
  have hp : ((⟨args, some (.agg g ok), h⟩ : Proto).ffi profile planned).callPlan.result = .indirect g.size g.align := by
    show placeReturn (some (.agg g ok)) = _
    simp [placeReturn, Arg.eights, hm, Arg.size, Arg.align]
  have hi : (⟨args, some (.agg g ok), h⟩ : Proto).indirect = true := by
    simp [Proto.indirect, Arg.eights, hm]
  constructor
  · rintro ⟨bytes, enc, ch⟩
    change bytes = r.1 at enc
    subst enc
    rw [hp] at ch
    obtain ⟨address, ha, hs, hr⟩ := ch
    simp only [Proto.call, hi, ite_true, Option.some.injEq] at ha
    subst ha
    exact ⟨hs, hr⟩
  · rintro ⟨hs, hr⟩
    refine ⟨r.1, rfl, ?_⟩
    rw [hp]
    exact ⟨_, by simp [Proto.call, hi], hs, hr⟩

/-- An aggregate result in registers: its INTEGER eightbytes in RAX then RDX, its SSE ones in
XMM0 then XMM1. -/
theorem resultAt_direct (profile : Profile) (planned : Planned profile) (args : List Arg)
    (g : Agg) (ok : g.ok = true) (hm : g.eights ≠ .memory)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State)
    (r : g.Value) :
    Ffi.ResultAt ((⟨args, some (.agg g ok), h⟩ : Proto).ffi profile planned)
        ((⟨args, some (.agg g ok), h⟩ : Proto).call s 0) s' r ↔
      Ffi.ChunksAt s' r.1 (eightChunks g.size gpReturns g.eights.classes 0 0 0) := by
  have hp : ((⟨args, some (.agg g ok), h⟩ : Proto).ffi profile planned).callPlan.result =
      .direct (eightChunks g.size gpReturns g.eights.classes 0 0 0) := by
    show placeReturn (some (.agg g ok)) = _
    simp [placeReturn, Arg.eights, hm, Arg.size, Arg.object, Agg.object]
  constructor
  · rintro ⟨bytes, enc, ch⟩
    change bytes = r.1 at enc
    subst enc
    rw [hp] at ch
    exact ch
  · intro hc
    refine ⟨r.1, rfl, ?_⟩
    rw [hp]
    exact hc

end Silmaril.Proofs.Machine.Abi.SystemV.Scalar
