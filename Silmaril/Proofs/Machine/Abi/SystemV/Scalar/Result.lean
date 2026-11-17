module

public import Silmaril.Machine.Abi.SystemV.Scalar.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Thms

/-!
# System V scalar fragment: result read-back

Proofs for `Silmaril.Machine.Abi.SystemV.Scalar.Thms`: a scalar result is the object
representation of the value in the low bytes of RAX (INTEGER) or XMM0 (SSE).
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.SystemV.Scalar

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (callOf Options)
open Silmaril.Machine.Abi.SystemV.Scalar

theorem resultAt_some (profile : Profile) (planned : Planned profile) (args : List Kind)
    (k : Kind) (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State)
    (r : k.Value) :
    Ffi.ResultAt ((⟨args, some k, h⟩ : Proto).ffi profile planned) (callOf s 0) s' r ↔
      Ffi.locationBytes s' (if k.sse then .vector 0 0 else .gp .rax) k.bytes =
        some (k.encode r) := by
  have hlen : (k.encode r).length = k.bytes := by simp [Kind.encode, Ffi.bytesOfNat]
  constructor
  · rintro ⟨bytes, enc, ch⟩
    change bytes = k.encode r at enc
    subst enc
    have := (ch _ (List.mem_singleton_self _)).2
    rw [List.drop_zero, List.take_of_length_le (by rw [hlen])] at this
    exact this
  · intro e
    refine ⟨k.encode r, rfl, ?_⟩
    intro chunk mem
    simp only [List.mem_singleton] at mem
    subst mem
    refine ⟨by simp [hlen], ?_⟩
    rw [List.drop_zero, List.take_of_length_le (by rw [hlen])]
    exact e

theorem resultAt_none (profile : Profile) (planned : Planned profile) (args : List Kind)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State)
    (r : PUnit) :
    Ffi.ResultAt ((⟨args, none, h⟩ : Proto).ffi profile planned) (callOf s 0) s' r := rfl

end Silmaril.Proofs.Machine.Abi.SystemV.Scalar
