module

import Silmaril.Wasm.Execution.Core.Intrinsic.Observation.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms

open Silmaril.Wasm Silmaril.Wasm.Execution.Core.Intrinsic

private def dividend : Code [.i32] [] [.i32] := .seq (.localGet .here (by decide)) .done
private def without : Code [.i32] [.i32] [.i32] := .done
private def withNop : Code [.i32] [.i32] [.i32] := .seq .nop without

private def oracle : Oracle := fun _ _ _ _ => false

example : Quotient.mk (Code.obsSetoid oracle [.i32] [] [.i32]) (dividend.append withNop) =
    Quotient.mk (Code.obsSetoid oracle [.i32] [] [.i32]) (dividend.append without) := by
  apply Quotient.sound
  exact Code.append_congr dividend ⟨fun values stack => ⟨.cons (Slot.here.get values) stack, rfl⟩, trivial⟩
    (Code.nop_obsEq without)

example : (dividend.append withNop).erase ≠ (dividend.append without).erase := by
  simp [Code.erase_append, withNop, without, Code.erase]

#print axioms Code.append_congr
#print axioms Code.nop_quotient
