module

public import Silmaril.X86.FnContract.Defs
public import Silmaril.X86.Extends.Thms
import Silmaril.Proofs.X86.FnContract.Lift
import Silmaril.Proofs.X86.FnContract.Strict

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
  spec;
* **first return**: `runsIn_mono`, `runsIn_trans`, `runsIn_reaches`, `runsIn_live`,
  `RunsIn.of_run` (an `n`-step run is a run inside `True`), `runsIn_map`; `Spec.TotalIn.total`, `Spec.Total.totalIn`; `Spec.Strict.total` (**strict
  implies total**); `Spec.Strict.firstReturn` (**a strict spec's result is the first
  return**); `firstReturn_unique`; `Spec.strict_of_totalIn`, `Spec.StrictBelow.strict`,
  `Spec.strict_of_inCode`; `not_returned_of_below`, `not_returned_of_inCode`;
  `Strict.ofStrict`, `Strict.firstReturn`;
* **first return along extensions**: `RunsIn.lift`, `Returned.lift_iff`, `Below.lift_iff`,
  `Spec.TotalIn.lift`, `Spec.Strict.lift`, `Spec.StrictBelow.lift`, `Strict.lift` (and the
  `_same` forms for the identity lens).
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

/-! ## First return -/

theorem runsIn_mono {P Q : σ → Prop} (h : ∀ m, P m → Q m) {s t : σ} (r : RunsIn I P s t) :
    RunsIn I Q s t :=
  Silmaril.Proofs.X86.FnContract.runsIn_mono h r

theorem runsIn_trans {P : σ → Prop} {s t u : σ} (r₁ : RunsIn I P s t) (r₂ : RunsIn I P t u) :
    RunsIn I P s u :=
  Silmaril.Proofs.X86.FnContract.runsIn_trans r₁ r₂

theorem runsIn_reaches {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) : Reaches I.step s t :=
  Silmaril.Proofs.X86.FnContract.runsIn_reaches r

theorem runsIn_live {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) (h : I.live s) : I.live t :=
  Silmaril.Proofs.X86.FnContract.runsIn_live r h

/-- **A run of `n` steps is a run inside `True`.** -/
theorem RunsIn.of_run {n : Nat} {s t : σ} (h : Silmaril.Machine.Execution.run I.step n s = some t) :
    RunsIn I (fun _ => True) s t :=
  Silmaril.Proofs.X86.FnContract.runsIn_of_run n h

/-- Runs carry over to a machine with more steps on the same states. -/
theorem runsIn_map {J : Isa σ} (hJ : ∀ {s s'}, I.step s = some s' → J.step s = some s')
    {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) : RunsIn J P s t :=
  Silmaril.Proofs.X86.FnContract.runsIn_map hJ r

/-- The first return is unique (the machine is a function). -/
theorem firstReturn_unique {s t t' : σ} (h : FirstReturn I s t) (h' : FirstReturn I s t') :
    t = t' :=
  Silmaril.Proofs.X86.FnContract.firstReturn_unique h h'

/-- A call result is a returned state. -/
theorem returned_of_result {S : Spec σ} {s t : σ} (h : S.Result I s t) : Returned I s t :=
  ⟨h.abi.pc, h.abi.stack⟩

theorem Spec.totalIn_mono {S : Spec σ} {P Q : σ → σ → Prop} (h : ∀ s m, P s m → Q s m)
    (hP : S.TotalIn I P) : S.TotalIn I Q :=
  Silmaril.Proofs.X86.FnContract.totalIn_mono h hP

/-- A `TotalIn` proof is a total-correctness proof. -/
theorem Spec.TotalIn.total {S : Spec σ} {P : σ → σ → Prop} (h : S.TotalIn I P) : S.Total I :=
  Silmaril.Proofs.X86.FnContract.totalIn_total h

/-- Every total spec is `TotalIn` the trivial predicate. -/
theorem Spec.Total.totalIn {S : Spec σ} (h : S.Total I) : S.TotalIn I fun _ _ => True :=
  Silmaril.Proofs.X86.FnContract.total_totalIn h

/-- **Strict implies total** (`Spec.Total`, the angelic reading). -/
theorem Spec.Strict.total {S : Spec σ} (h : S.Strict I) : S.Total I :=
  Spec.TotalIn.total h

/-- **A strict spec's result is the first return** of the run from the entry state. -/
theorem Spec.Strict.firstReturn {S : Spec σ} (h : S.Strict I) {s : σ} (hl : I.live s)
    (ha : AbiEntry (I.core s) (I.mem s)) (he : S.entry s) :
    ∃ t, FirstReturn I s t ∧ S.Result I s t :=
  Silmaril.Proofs.X86.FnContract.strict_firstReturn h hl ha he

/-- A `TotalIn` whose run predicate excludes the entry's returned states is strict. -/
theorem Spec.strict_of_totalIn {S : Spec σ} {P : σ → σ → Prop}
    (hP : ∀ s m, P s m → ¬ Returned I s m) (h : S.TotalIn I P) : S.Strict I :=
  Spec.totalIn_mono hP h

theorem Spec.StrictBelow.strict {S : Spec σ} (h : S.StrictBelow I) : S.Strict I :=
  Spec.strict_of_totalIn (fun _ _ h => h.1) h

/-- The stack-depth invariant excludes the entry's return when `rsp + 8` does not wrap. -/
theorem not_returned_of_below {s m : σ} (hb : Below I s m)
    (hw : ((I.core s).read .rsp).toNat + 8 < 2 ^ 64) : ¬ Returned I s m :=
  Silmaril.Proofs.X86.FnContract.not_returned_of_below hb hw

/-- A state inside the code is not returned when the return address lies outside the code. -/
theorem not_returned_of_inCode {base : Word} {len : Nat} {s m : σ}
    (hout : RetOutside I base len s) (hin : InCode I base len m) : ¬ Returned I s m :=
  Silmaril.Proofs.X86.FnContract.not_returned_of_inCode hout hin

@[simp] theorem Spec.restrict_entry (S : Spec σ) (P : σ → Prop) (s : σ) :
    (S.restrict P).entry s ↔ S.entry s ∧ P s := Iff.rfl

/-- A result for `S` is a result for `S.restrict P`. -/
theorem Spec.Result.restrict {S : Spec σ} {P : σ → Prop} {s t : σ} (h : S.Result I s t) :
    (S.restrict P).Result I s t := ⟨h.silent, h.abi, h.frame, h.post⟩

/-- **Runs inside the code with the return address outside give a strict spec**, for the
entry strengthened by `RetOutside`. -/
theorem Spec.strict_of_inCode {S : Spec σ} {base : Word} {len : Nat}
    (h : (S.restrict (RetOutside I base len)).TotalIn I fun _ => InCode I base len) :
    (S.restrict (RetOutside I base len)).Strict I :=
  fun s hl ha he =>
    let ⟨t, r, res⟩ := h s hl ha he
    ⟨t, runsIn_mono (fun _ hin => not_returned_of_inCode he.2 hin) r, res⟩

/-- A strict contract from a strict spec. -/
def Strict.ofStrict (S : Spec σ) (h : S.Strict I) : FnContract.Strict I :=
  ⟨⟨S, h.total⟩, h⟩

@[simp] theorem Strict.ofStrict_toSpec (S : Spec σ) (h : S.Strict I) :
    (Strict.ofStrict S h).toSpec = S := rfl

/-- A strict contract's result is the first return. -/
theorem Strict.firstReturn (C : FnContract.Strict I) {s : σ} (hl : I.live s)
    (ha : AbiEntry (I.core s) (I.mem s)) (he : C.entry s) :
    ∃ t, FirstReturn I s t ∧ C.Result s t :=
  C.strict.firstReturn hl ha he

/-! ## First return along machine extensions -/

/-- **A run of `I` inside `P` from the view of `x` is a run of `J` inside `P ∘ view`.** -/
theorem RunsIn.lift {J : Isa τ} (E : I.Extends J) {P : σ → Prop} {x : τ} {t : σ}
    (r : RunsIn I P (E.view x) t) : RunsIn J (fun y => P (E.view y)) x (E.put x t) :=
  Silmaril.Proofs.X86.FnContract.runsIn_lift E r x rfl

/-- Having returned reads only the core and memory, which are the view's. -/
theorem Returned.lift_iff {J : Isa τ} (E : I.Extends J) (x y : τ) :
    Returned J x y ↔ Returned I (E.view x) (E.view y) :=
  Silmaril.Proofs.X86.FnContract.returned_iff E x y

theorem Below.lift_iff {J : Isa τ} (E : I.Extends J) (x y : τ) :
    Below J x y ↔ Below I (E.view x) (E.view y) :=
  Silmaril.Proofs.X86.FnContract.below_iff E x y

/-- `TotalIn` moves up along an extension, with the run predicate read through the view. -/
theorem Spec.TotalIn.lift {J : Isa τ} (E : I.Extends J) {S : Spec σ} {P : σ → σ → Prop}
    (h : S.TotalIn I P) : (S.comap E.view).TotalIn J fun x y => P (E.view x) (E.view y) :=
  Silmaril.Proofs.X86.FnContract.totalIn_lift E h

/-- **Strict total correctness moves up along an extension.** -/
theorem Spec.Strict.lift {J : Isa τ} (E : I.Extends J) {S : Spec σ} (h : S.Strict I) :
    (S.comap E.view).Strict J :=
  Spec.totalIn_mono (fun x y h' => (Returned.lift_iff E x y).not.mpr h') (Spec.TotalIn.lift E h)

/-- Strict total correctness with the stack-depth invariant moves up along an extension. -/
theorem Spec.StrictBelow.lift {J : Isa τ} (E : I.Extends J) {S : Spec σ}
    (h : S.StrictBelow I) : (S.comap E.view).StrictBelow J :=
  Spec.totalIn_mono
    (fun x y h' => ⟨(Returned.lift_iff E x y).not.mpr h'.1, (Below.lift_iff E x y).mpr h'.2⟩)
    (Spec.TotalIn.lift E h)

theorem Spec.Strict.lift_same {J : Isa σ} (E : I.Extends J) (hv : E.view = id) {S : Spec σ}
    (h : S.Strict I) : S.Strict J := by
  have := h.lift E; rw [hv] at this; exact this

theorem Spec.StrictBelow.lift_same {J : Isa σ} (E : I.Extends J) (hv : E.view = id)
    {S : Spec σ} (h : S.StrictBelow I) : S.StrictBelow J := by
  have := h.lift E; rw [hv] at this; exact this

/-- **Every strict contract on `I` is a strict contract on an extension `J`.** -/
def Strict.lift {J : Isa τ} (E : I.Extends J) (C : FnContract.Strict I) : FnContract.Strict J :=
  ⟨C.toFnContract.lift E, C.strict.lift E⟩

@[simp] theorem Strict.lift_toSpec {J : Isa τ} (E : I.Extends J) (C : FnContract.Strict I) :
    (C.lift E).toSpec = C.toSpec.comap E.view := rfl

end Silmaril.X86.FnContract
