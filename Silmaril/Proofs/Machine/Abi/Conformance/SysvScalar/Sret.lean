module

public import Silmaril.Machine.Abi.Conformance.SysvScalar.Sret.Defs
public import Silmaril.Proofs.Machine.Abi.Conformance.LeafArith

/-!
# `sysvScalar`: an admitted call with a MEMORY result, and calls that are not admitted

Proofs for `Silmaril.Machine.Abi.Conformance.SysvScalar.Sret.Thms`. The state is the leaf-arith
witness (`Proofs.Machine.Abi.Conformance.LeafArith`: its code placement, return address and
permissions) with RDI pointing at `0x10000`, 24 bytes apart from the stack window
`[0x8ff8, 0x9000)`, the code `[0x401370, 0x401425)` and the image (from `0x400000`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.Sret

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.SysvScalar.Sret
open Silmaril.Machine.Abi.Conformance.LeafArith
open Silmaril.Machine.Abi.Conformance.LeafArith.Witness
open Silmaril.Proofs.Machine.Abi.Conformance.LeafArith

theorem owned_iff (r : Silmaril.X86.Word) (x : Nat) :
    sysvScalar.owned sretProto (sretSt r) x ↔ r.toNat ≤ x ∧ x < r.toNat + 24 := Iff.rfl

theorem argArea : sysvScalar.argArea sretProto = 0 := rfl

theorem code_len : sretCode.bytes.length = 181 := code_length

theorem code_base : sretCode.base.toNat = 0x401370 := rfl

theorem image_above : ∀ r ∈ sretCode.image, 0x400000 ≤ r.1.toNat := by decide

theorem entry : sysvScalar.conv.Entry sretProto sretArgs (sretSt 0x10000) := by
  refine ⟨retAt, ⟨rfl, trivial, ?_, ?_, ret_read, ?_, rfl, rfl, (fun _ h => nomatch h)⟩⟩
  · show ((0x8ff8 : Silmaril.X86.Word).toNat + 8) % 16 = 0
    decide
  · show (0x8ff8 : Silmaril.X86.Word).toNat + 8 + 0 ≤ 2 ^ 64
    decide
  · exact ⟨0x10000, rfl, by decide, by decide, by decide, rfl, trivial⟩

theorem stack : Stack sysvScalar sretProto sretCode 0 (fun _ => False) (sretSt 0x10000) := by
  have hsp : sp (sretSt 0x10000) = 0x8ff8 := rfl
  have ho : ∀ x, sysvScalar.owned sretProto (sretSt 0x10000) x → 0x10000 ≤ x ∧ x < 0x10018 :=
    fun x h => by simpa using (owned_iff _ x).1 h
  refine ⟨by omega, ?_, ?_, ?_, ?_, (fun _ h => nomatch h), ?_, (fun _ h => nomatch h),
    (fun x h => permitted _ _ _ (by have := ho x h; omega)),
    (fun x h => permitted _ _ _ (by have := ho x h; omega)), ?_, ?_,
    (fun _ _ _ h => nomatch h), ?_, (fun _ _ h => h)⟩
  · rw [argArea, hsp]; decide
  · rw [argArea, hsp]; exact permitted _ _ _ (by decide)
  · rw [argArea, hsp]; exact permitted _ _ _ (by decide)
  · right
    rw [argArea, hsp]
    show 0x8ff8 - 0 + (0 + 8 + 0) ≤ Silmaril.X86.Ladder.LeafArith.base.toNat
    decide
  · intro r hr
    rw [argArea, hsp]
    simp only [sretCode, region, image, List.mem_cons, List.not_mem_nil, or_false] at hr
    right
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · intro x h
    rw [argArea, hsp]
    have := ho x h
    omega
  · intro x h
    have := ho x h
    rw [code_len, code_base]
    omega
  · intro x h r hr
    have := ho x h
    have := image_above r hr
    omega

theorem admitted (M : Mach) (hl : M.isa.live (M.load (sretSt 0x10000))) :
    Admit sysvScalar M sretProto sretCode 0 (CallSpec.abiPure _ _) sretArgs (sretSt 0x10000) :=
  ⟨hl, entry, placed _ _ _ _ _, stack, rfl⟩

/-- An admitted call's result storage is apart from the code: RDI at the code is refused. -/
theorem not_admitted_code (M : Mach) (S : CallSpec sysvScalar.V sretProto) (a) :
    ¬ Admit sysvScalar M sretProto sretCode 0 S a
      (sretSt Silmaril.X86.Ladder.LeafArith.base) := by
  intro ad
  refine ad.stack.ownedApartCode 0x401370 ((owned_iff _ _).2 (by decide)) ?_
  rw [code_len, code_base]
  omega

/-- An admitted call's result storage is apart from the stack window: RDI at the return
address is refused. -/
theorem not_admitted_stack (M : Mach) (S : CallSpec sysvScalar.V sretProto) (a) :
    ¬ Admit sysvScalar M sretProto sretCode 0 S a (sretSt 0x8ff8) := by
  intro ad
  exact ad.stack.ownedApartStack 0x8ff8 ((owned_iff _ _).2 (by decide)) (by
    show 0x8ff8 - 0 ≤ 0x8ff8 ∧ 0x8ff8 < 0x8ff8 + 8 + sysvScalar.argArea sretProto
    rw [argArea]; decide)

/-- An admitted call's result storage is apart from the caller-visible objects. -/
theorem not_admitted_objects (M : Mach) (S : CallSpec sysvScalar.V sretProto) (a)
    (h : S.objects a (sretSt 0x10000).machine.memory 0x10008) :
    ¬ Admit sysvScalar M sretProto sretCode 0 S a (sretSt 0x10000) :=
  fun ad => ad.stack.ownedApartObjects 0x10008 ((owned_iff _ _).2 (by decide)) h

end Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.Sret

end
