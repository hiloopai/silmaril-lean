module

public import Silmaril.Machine.X86.FnContract.Defs
import Silmaril.Proofs.Machine.X86.FnContract.Open
import Silmaril.Proofs.Machine.X86.FnContract.Strict

/-!
# Generic System V function contracts: calls, frames, constructors, first return

* `toCall_pre`, `toCall_post`, `Result.rip_eq`: a contracted call in a caller's segment VCs;
  `Result.rsp_ne`, `Result.ne_self`: a call result is never its entry state (non-vacuity);
* `Sub.refl`, `Sub.trans`, `mono`, `frame`, `Result.readBytes`, `Result.reg`: refinement and
  frame reasoning;
* `ofReturns`, `ofExtReturns`: open-machine contracts from `Ext8.Returns` and `Ext.Returns`;
* **first return** (generic over the machine): `runsIn_mono`, `runsIn_trans`,
  `runsIn_reaches`, `runsIn_live`, `runsIn_map`; `Spec.TotalIn.total`;
  `Spec.Strict.total` (**strict implies `Spec.Total`**); `Spec.Strict.firstReturn` (**a strict
  spec's result is the first return**); `firstReturn_unique`; `Spec.strict_of_totalIn`;
  `Spec.StrictBelow.strict`; `not_returned_of_below`, `not_returned_of_inCode`;
  `Strict.ofTotalIn`, `Strict.toFnContract`.

The System V and decompilation bridges (`toRealizes`, `toFfiRealizes`, `ofDecompiled`,
`total_of_decompiled`) are in `FnContract/SystemV/Thms.lean` (same names), so this core does not
import Cerberus closure.
-/

@[expose] public section

namespace Silmaril.Machine.X86.FnContract

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.X86.SegVC (Isa Call)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

variable {σ : Type} {I : Isa σ}

/-! ## Calls -/

@[simp] theorem toCall_pre (C : FnContract I) (s : σ) :
    C.toCall.pre s ↔ AbiEntry (I.core s) (I.mem s) ∧ C.entry s := Iff.rfl

@[simp] theorem toCall_post (C : FnContract I) (s t : σ) :
    C.toCall.post s t ↔ C.Result s t := Iff.rfl

/-- The callee returns to the caller's return offset: if the return address at the callee's
entry is `base + o`, so is `rip` after the call. -/
theorem Result.rip_eq {S : Spec σ} {s t : σ} (h : S.Result I s t) {base : Word} {o : Nat}
    (hret : Open.retOf (I.core s) (I.mem s) = base + BitVec.ofNat 64 o) :
    (I.core t).rip = base + BitVec.ofNat 64 o :=
  h.abi.pc.trans hret

/-- Non-vacuity of `Spec.Result`: a call result always moves `rsp` (by the eight bytes of the
popped return address), so no call result is its own entry state and every `total` proof
takes at least one step. -/
theorem Result.rsp_ne {S : Spec σ} {s t : σ} (h : S.Result I s t) :
    (I.core t).read .rsp ≠ (I.core s).read .rsp := by
  rw [h.abi.stack]
  intro e
  bv_omega

theorem Result.ne_self {S : Spec σ} {s : σ} (h : S.Result I s s) : False :=
  Result.rsp_ne h rfl

/-! ## Refinement and frames -/

theorem Spec.Sub.refl (S : Spec σ) : S.Sub S :=
  ⟨fun _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem Spec.Sub.trans {S T U : Spec σ} (h₁ : S.Sub T) (h₂ : T.Sub U) : S.Sub U :=
  ⟨fun s h => h₁.entry s (h₂.entry s h),
   fun s a h ha => h₂.footprint s a h (h₁.footprint s a (h₂.entry s h) ha),
   fun s t h hp => h₂.post s t h (h₁.post s t (h₂.entry s h) hp)⟩

@[simp] theorem mono_toSpec (C : FnContract I) (T : Spec σ) (h : C.toSpec.Sub T) :
    (C.mono T h).toSpec = T := rfl

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

/-! ## Constructors on the open machine -/

theorem total_of_returns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Silmaril.X86.Ext8.Returns (Open.retOf m.core m.memory) m fin ∧
        ReturnsPost S m fin) :
    S.Total Open.isa :=
  Silmaril.Proofs.Machine.X86.FnContract.total_of_returns S h

theorem total_of_ext_returns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Silmaril.X86.Ext.Returns (Open.retOf m.core m.memory) m fin ∧
        ReturnsPost S m fin) :
    S.Total Open.isa :=
  Silmaril.Proofs.Machine.X86.FnContract.total_of_ext_returns S h

/-- A contract from an `Ext8.Returns` proof to the entry state's return address. -/
def ofReturns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Silmaril.X86.Ext8.Returns (Open.retOf m.core m.memory) m fin ∧
        ReturnsPost S m fin) :
    FnContract Open.isa :=
  ⟨S, total_of_returns S h⟩

/-- A contract from an `X86.Ext.Returns` proof. -/
def ofExtReturns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Silmaril.X86.Ext.Returns (Open.retOf m.core m.memory) m fin ∧
        ReturnsPost S m fin) :
    FnContract Open.isa :=
  ⟨S, total_of_ext_returns S h⟩

/-! ## First return -/

theorem runsIn_mono {P Q : σ → Prop} (h : ∀ m, P m → Q m) {s t : σ} (r : RunsIn I P s t) :
    RunsIn I Q s t :=
  Silmaril.Proofs.Machine.X86.FnContract.runsIn_mono h r

theorem runsIn_trans {P : σ → Prop} {s t u : σ} (r₁ : RunsIn I P s t) (r₂ : RunsIn I P t u) :
    RunsIn I P s u :=
  Silmaril.Proofs.Machine.X86.FnContract.runsIn_trans r₁ r₂

theorem runsIn_reaches {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) : Reaches I.step s t :=
  Silmaril.Proofs.Machine.X86.FnContract.runsIn_reaches r

theorem runsIn_live {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) (h : I.live s) : I.live t :=
  Silmaril.Proofs.Machine.X86.FnContract.runsIn_live r h

/-- Runs carry over to a machine with more steps on the same states (for instance from
`Open.isa` to `Open9.isa`). -/
theorem runsIn_map {J : Isa σ} (hJ : ∀ {s s'}, I.step s = some s' → J.step s = some s')
    {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) : RunsIn J P s t :=
  Silmaril.Proofs.Machine.X86.FnContract.runsIn_map hJ r

/-- The first return is unique (the machine is a function). -/
theorem firstReturn_unique {s t t' : σ} (h : FirstReturn I s t) (h' : FirstReturn I s t') :
    t = t' :=
  Silmaril.Proofs.Machine.X86.FnContract.firstReturn_unique h h'

theorem returned_of_result {S : Spec σ} {s t : σ} (h : S.Result I s t) : Returned I s t :=
  Silmaril.Proofs.Machine.X86.FnContract.returned_of_result h

theorem Spec.totalIn_mono {S : Spec σ} {P Q : σ → σ → Prop} (h : ∀ s m, P s m → Q s m)
    (hP : S.TotalIn I P) : S.TotalIn I Q :=
  Silmaril.Proofs.Machine.X86.FnContract.totalIn_mono h hP

/-- A `TotalIn` proof is a total-correctness proof. -/
theorem Spec.TotalIn.total {S : Spec σ} {P : σ → σ → Prop} (h : S.TotalIn I P) : S.Total I :=
  Silmaril.Proofs.Machine.X86.FnContract.TotalIn.total h

/-- Every total spec is `TotalIn` the trivial predicate. -/
theorem Spec.Total.totalIn {S : Spec σ} (h : S.Total I) : S.TotalIn I fun _ _ => True :=
  fun s hl ha he => by
    obtain ⟨t, r, res⟩ := h s hl ha he
    obtain ⟨n, hn⟩ := r
    exact ⟨t, Silmaril.Proofs.Machine.X86.FnContract.runsIn_of_run n hn, res⟩

/-- **Strict implies total** (`Spec.Total`, the angelic reading). -/
theorem Spec.Strict.total {S : Spec σ} (h : S.Strict I) : S.Total I :=
  Spec.TotalIn.total h

/-- **A strict spec's result is the first return** of the run from the entry state. -/
theorem Spec.Strict.firstReturn {S : Spec σ} (h : S.Strict I) {s : σ} (hl : I.live s)
    (ha : AbiEntry (I.core s) (I.mem s)) (he : S.entry s) :
    ∃ t, FirstReturn I s t ∧ S.Result I s t :=
  Silmaril.Proofs.Machine.X86.FnContract.Strict.firstReturn h hl ha he

/-- A `TotalIn` whose run predicate excludes the entry's returned states is strict. -/
theorem Spec.strict_of_totalIn {S : Spec σ} {P : σ → σ → Prop}
    (hP : ∀ s m, P s m → ¬ Returned I s m) (h : S.TotalIn I P) : S.Strict I :=
  Silmaril.Proofs.Machine.X86.FnContract.strict_of_totalIn hP h

theorem Spec.StrictBelow.strict {S : Spec σ} (h : S.StrictBelow I) : S.Strict I :=
  Spec.strict_of_totalIn (fun _ _ h => h.1) h

/-- The stack-depth invariant excludes the entry's return when `rsp + 8` does not wrap. -/
theorem not_returned_of_below {s m : σ} (hb : Below I s m)
    (hw : ((I.core s).read .rsp).toNat + 8 < 2 ^ 64) : ¬ Returned I s m :=
  Silmaril.Proofs.Machine.X86.FnContract.not_returned_of_below hb hw

/-- A state inside the code is not returned when the return address lies outside the code. -/
theorem not_returned_of_inCode {base : Word} {len : Nat} {s m : σ}
    (hout : RetOutside I base len s) (hin : InCode I base len m) : ¬ Returned I s m :=
  Silmaril.Proofs.Machine.X86.FnContract.not_returned_of_inCode hout hin

/-- **Runs inside the code with the return address outside give a strict spec**: the entry
strengthened by `RetOutside` (the form every block-certificate `totalIn` produces). -/
theorem Spec.strict_of_inCode {S : Spec σ} {base : Word} {len : Nat}
    (h : (S.restrict (RetOutside I base len)).TotalIn I fun _ => InCode I base len) :
    (S.restrict (RetOutside I base len)).Strict I :=
  fun s hl ha he => by
    obtain ⟨t, r, res⟩ := h s hl ha he
    exact ⟨t, runsIn_mono (fun _ hin => not_returned_of_inCode he.2 hin) r, res⟩

@[simp] theorem Spec.restrict_entry (S : Spec σ) (P : σ → Prop) (s : σ) :
    (S.restrict P).entry s ↔ S.entry s ∧ P s := Iff.rfl

/-- A result for `S` is a result for `S.restrict P`. -/
theorem Spec.Result.restrict {S : Spec σ} {P : σ → Prop} {s t : σ} (h : S.Result I s t) :
    (S.restrict P).Result I s t := ⟨h.silent, h.abi, h.frame, h.post⟩

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

/-! ## Stack slots -/

/-- The return address read from a stack slot holding its encoding. -/
theorem retOf_of_readBytes {core : State} {memory : Memory} {x : Word}
    (h : memory.readBytes (core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [x])) :
    Open.retOf core memory = x :=
  Silmaril.Proofs.Machine.X86.FnContract.retOf_of_readBytes h

end Silmaril.Machine.X86.FnContract
