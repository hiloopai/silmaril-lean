module

public import Silmaril.X86.FnContract.Defs
public import Silmaril.X86.Extends.Thms
import Silmaril.Proofs.X86.FnContract.Lift

/-!
# System V function contracts: calls, frames and transfer along extensions

* `toCall_pre`, `toCall_post`, `Result.rip_eq`: a contracted call in a caller's segment VCs;
  `Result.rsp_ne`, `Result.ne_self`: a call result is never its entry state (non-vacuity);
* `Spec.Sub.refl`, `Spec.Sub.trans`, `mono`, `frame`, `Result.readBytes`, `Result.reg`,
  `Result.stable`: refinement and frame reasoning;
* `retOf_of_readBytes`, `abiEntry_of`: the ABI entry obligations from an encoded stack slot;
* **`Spec.Total.lift`, `lift`: a contract on `I` is a contract on every extension `J` of
  `I`**, for the spec read through the extension's view (`Spec.comap`). On an extension
  with the same states and the identity lens (`Open.isa` to `Open9.isa`) it is the same
  spec.
-/

@[expose] public section

namespace Silmaril.X86.FnContract

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.X86.SegVC (Isa Call)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

variable {σ τ : Type} {I : Isa σ}

/-! ## Calls -/

@[simp] theorem toCall_pre (C : FnContract I) (s : σ) :
    C.toCall.pre s ↔ AbiEntry (I.core s) (I.mem s) ∧ C.entry s := Iff.rfl

@[simp] theorem toCall_post (C : FnContract I) (s t : σ) :
    C.toCall.post s t ↔ C.Result s t := Iff.rfl

/-- The callee returns to the caller's return offset. -/
theorem Result.rip_eq {S : Spec σ} {s t : σ} (h : S.Result I s t) {base : Word} {o : Nat}
    (hret : retOf (I.core s) (I.mem s) = base + BitVec.ofNat 64 o) :
    (I.core t).rip = base + BitVec.ofNat 64 o :=
  h.abi.pc.trans hret

/-- A call result always moves `rsp` (by the eight bytes of the popped return address). -/
theorem Result.rsp_ne {S : Spec σ} {s t : σ} (h : S.Result I s t) :
    (I.core t).read .rsp ≠ (I.core s).read .rsp :=
  Silmaril.Proofs.X86.FnContract.rsp_ne h.abi.stack

/-- No call result is its own entry state, so every `total` proof takes a step. -/
theorem Result.ne_self {S : Spec σ} {s : σ} (h : S.Result I s s) : False :=
  Result.rsp_ne h rfl

/-! ## Refinement and frames -/

theorem Spec.Sub.refl (S : Spec σ) : S.Sub S :=
  ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem Spec.Sub.trans {S T U : Spec σ} (h₁ : S.Sub T) (h₂ : T.Sub U) : S.Sub U :=
  ⟨fun s h => h₁.entry s (h₂.entry s h),
   fun s a h ha => h₂.footprint s a h (h₁.footprint s a (h₂.entry s h) ha),
   fun s t h hp => h₂.post s t h (h₁.post s t (h₂.entry s h) hp)⟩

/-- Total correctness is kept by a refinement of the spec. -/
theorem Spec.Total.mono {S T : Spec σ} (h : S.Total I) (hs : S.Sub T) : T.Total I :=
  Silmaril.Proofs.X86.FnContract.total_mono h hs

/-- Total correctness with a stable memory predicate added before and after. -/
theorem Spec.Total.frame {S : Spec σ} (h : S.Total I) {F : Memory → Prop}
    (hF : ∀ s, Stable (S.footprint s) F) :
    Spec.Total I ⟨fun s => S.entry s ∧ F (I.mem s), S.footprint,
      fun s t => S.post s t ∧ F (I.mem t)⟩ :=
  Silmaril.Proofs.X86.FnContract.total_frame h hF

/-- Weaken a contract along a refinement of its spec. -/
def mono (C : FnContract I) (T : Spec σ) (h : C.toSpec.Sub T) : FnContract I :=
  ⟨T, C.total.mono h⟩

@[simp] theorem mono_toSpec (C : FnContract I) (T : Spec σ) (h : C.toSpec.Sub T) :
    (C.mono T h).toSpec = T := rfl

/-- **The frame rule.** A memory predicate untouched by the footprint holds after the call
if it held before. -/
def frame (C : FnContract I) (F : Memory → Prop) (hF : ∀ s, Stable (C.footprint s) F) :
    FnContract I :=
  ⟨⟨fun s => C.entry s ∧ F (I.mem s), C.footprint, fun s t => C.post s t ∧ F (I.mem t)⟩,
    C.total.frame hF⟩

/-- Bytes outside the footprint read back unchanged after the call. -/
theorem Result.readBytes {S : Spec σ} {s t : σ} (h : S.Result I s t) {address length : Nat}
    (outside : ∀ k < length, ¬ S.footprint s (address + k)) :
    (I.mem t).readBytes address length = (I.mem s).readBytes address length :=
  Silmaril.Process.Memory.WritesWithin.readBytes h.frame outside

/-- Callee-saved registers are unchanged by the call. -/
theorem Result.reg {S : Spec σ} {s t : σ} (h : S.Result I s t) {r : Reg}
    (hr : r ∈ sysv64.calleeSaved) : (I.core t).read r = (I.core s).read r :=
  h.abi.calleeSaved r hr

/-- A stable memory predicate is kept by the call. -/
theorem Result.stable {S : Spec σ} {s t : σ} (h : S.Result I s t) {F : Memory → Prop}
    (hF : Stable (S.footprint s) F) (hs : F (I.mem s)) : F (I.mem t) :=
  hF _ _ h.frame hs

/-- Every byte-equality outside a footprint is stable. -/
theorem stable_readBytes {fp : Nat → Prop} {address length : Nat} {bytes : List Byte}
    (outside : ∀ k < length, ¬ fp (address + k)) :
    Stable fp (fun m => m.readBytes address length = some bytes) :=
  fun _ _ hw h => (Silmaril.Process.Memory.WritesWithin.readBytes hw outside).trans h

/-! ## Stack slots -/

/-- The return address read from a stack slot holding its encoding. -/
theorem retOf_of_readBytes {core : State} {memory : Memory} {x : Word}
    (h : memory.readBytes (core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [x])) :
    retOf core memory = x :=
  Silmaril.Proofs.X86.FnContract.retOf_of_readBytes h

/-- The ABI entry obligations from an aligned stack and an encoded return address. -/
theorem abiEntry_of {core : State} {memory : Memory} {x : Word}
    (aligned : (core.read .rsp).toNat % 16 = 8)
    (h : memory.readBytes (core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [x])) :
    AbiEntry core memory :=
  ⟨aligned, by rw [retOf_of_readBytes h]; exact h⟩

/-! ## Transfer along machine extensions -/

/-- **Total correctness moves up along an extension**: a spec total on `I` is total on `J`,
read through the extension's view. -/
theorem Spec.Total.lift {J : Isa τ} (E : I.Extends J) {S : Spec σ} (h : S.Total I) :
    (S.comap E.view).Total J :=
  Silmaril.Proofs.X86.FnContract.total_lift E h

/-- On the same states with the identity lens, the spec is unchanged. -/
theorem Spec.Total.lift_same {J : Isa σ} (E : I.Extends J) (hv : E.view = id) {S : Spec σ}
    (h : S.Total I) : S.Total J := by
  have := h.lift E; rw [hv] at this; exact this

/-- **Every contract on `I` is a contract on an extension `J`.** -/
def lift {J : Isa τ} (E : I.Extends J) (C : FnContract I) : FnContract J :=
  ⟨C.toSpec.comap E.view, C.total.lift E⟩

@[simp] theorem lift_toSpec {J : Isa τ} (E : I.Extends J) (C : FnContract I) :
    (C.lift E).toSpec = C.toSpec.comap E.view := rfl

end Silmaril.X86.FnContract
