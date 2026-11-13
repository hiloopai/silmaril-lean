module

public import Silmaril.Machine.Abi.CallFootprint.Defs
public import Silmaril.X86.FnContract.RightRot.Thms
public import Silmaril.X86.Ladder.LibMini.Thms
public import Silmaril.X86.Ladder.LibMini.SystemV.Thms
/-! # Call-dependent footprints: theorems

PROVED (standard axioms):

* `realizesCall_iff`, `ffiRealizesCall_iff`: **`Realizes` is the special case** of
  `RealizesCall` (`FfiRealizesCall`) with footprint and result constant in the call;
* `RealizesCall.of_family`, `FfiRealizesCall.of_family`: a family of certificates indexed by
  a function of the call is one call-dependent certificate;
* `RealizesCall.restrict`: conversely, a call-dependent certificate gives every member of a
  family whose domain fixes the footprint and result;
* `RealizesCall.mono_domain`, `RealizesCall.mono_writes`: weakening;
* round 4 (F7): `FfiRealizesCall.restrict`, `FfiRealizesCall.mono_domain`: the typed forms
  (an exported `FfiRealizesCall` gives back each the ABI model `Ffi.Realizes` family member);
* `toRealizesCall`, `toFfiRealizesCall`: an open-machine `FnContract` is a call-dependent
  certificate whose footprint is the contract's own footprint at the entry state, with no
  footprint obligation (proved through A's `toRealizes`/`toFfiRealizes`);
* `rightRot_realizesCall`: A's `right_rot` family `RightRot.realizes sp0` as one certificate
  with footprint "the sixteen bytes below the entry `rsp`", and `rightRot_realizes_of_call`
  recovering each member;
* `cstrLen_eq`: the string length is unique; `strlen_realizesCall`: A's `strlen` family
  `strlen_realizes entry k` as one certificate with result `cstrLen` of the argument string.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.CallFootprint

open Silmaril.C.Api (Signature Arguments ReturnValue)
open Silmaril.X86 (MState Word)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.SystemV (Call Footprint Realizes)
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86

/-! ## The special case and families -/

theorem realizesCall_iff (signature : Signature)
    (result : Arguments signature.arguments → ReturnValue signature.result)
    (writes : Arguments signature.arguments → Footprint)
    (domain : Arguments signature.arguments → Call → Prop)
    (execute : Call → MState → Prop) :
    RealizesCall signature (fun a _ => result a) (fun a _ => writes a) domain execute ↔
      Realizes signature result writes domain execute := Iff.rfl

theorem ffiRealizesCall_iff (signature : Ffi.Signature)
    (result : Ffi.Values signature.arguments → Ffi.ResultValue signature.result)
    (writes : Ffi.Values signature.arguments → Ffi.Footprint)
    (unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop)
    (domain : Ffi.Values signature.arguments → Ffi.Call → Prop)
    (execute : Ffi.Call → Ffi.State → Prop) :
    FfiRealizesCall signature (fun a _ => result a) (fun a _ => writes a) unaliased domain
      execute ↔ Ffi.Realizes signature result writes unaliased domain execute := Iff.rfl

variable {signature : Signature} {execute : Call → MState → Prop}

/-- A family indexed by a function of the call is one call-dependent certificate. -/
theorem RealizesCall.of_family {ι : Type} (idx : Arguments signature.arguments → Call → ι)
    {result : ι → Arguments signature.arguments → ReturnValue signature.result}
    {writes : ι → Arguments signature.arguments → Footprint}
    {domain : ι → Arguments signature.arguments → Call → Prop}
    (h : ∀ i, Realizes signature (result i) (writes i) (domain i) execute) :
    RealizesCall signature (fun a call => result (idx a call) a)
      (fun a call => writes (idx a call) a) (fun a call => domain (idx a call) a call)
      execute :=
  fun a call entry inDomain => h (idx a call) a call entry inDomain

/-- A call-dependent certificate gives each member of a family whose domain fixes the result
and footprint. -/
theorem RealizesCall.restrict
    {result : Arguments signature.arguments → Call → ReturnValue signature.result}
    {writes : Arguments signature.arguments → Call → Footprint}
    {domain : Arguments signature.arguments → Call → Prop}
    (h : RealizesCall signature result writes domain execute)
    {result' : Arguments signature.arguments → ReturnValue signature.result}
    {writes' : Arguments signature.arguments → Footprint}
    {domain' : Arguments signature.arguments → Call → Prop}
    (hdom : ∀ a call, domain' a call → domain a call)
    (hres : ∀ a call, domain' a call → result a call = result' a)
    (hwr : ∀ a call, domain' a call → writes a call = writes' a) :
    Realizes signature result' writes' domain' execute := by
  intro a call entry inDomain
  obtain ⟨final, run, res⟩ := h a call entry (hdom a call inDomain)
  rw [hres a call inDomain, hwr a call inDomain] at res
  exact ⟨final, run, res⟩

theorem RealizesCall.mono_domain
    {result : Arguments signature.arguments → Call → ReturnValue signature.result}
    {writes : Arguments signature.arguments → Call → Footprint}
    {domain domain' : Arguments signature.arguments → Call → Prop}
    (h : RealizesCall signature result writes domain execute)
    (hdom : ∀ a call, domain' a call → domain a call) :
    RealizesCall signature result writes domain' execute :=
  fun a call entry inDomain => h a call entry (hdom a call inDomain)

theorem RealizesCall.mono_writes
    {result : Arguments signature.arguments → Call → ReturnValue signature.result}
    {writes writes' : Arguments signature.arguments → Call → Footprint}
    {domain : Arguments signature.arguments → Call → Prop}
    (h : RealizesCall signature result writes domain execute)
    (hwr : ∀ a call x, domain a call → writes a call x → writes' a call x) :
    RealizesCall signature result writes' domain execute := by
  intro a call entry inDomain
  obtain ⟨final, run, res⟩ := h a call entry inDomain
  exact ⟨final, run, res.returned, res.valueAt,
    Silmaril.Process.Memory.WritesWithin.mono res.frame (hwr a call · inDomain)⟩

theorem FfiRealizesCall.of_family {signature : Ffi.Signature}
    {execute : Ffi.Call → Ffi.State → Prop} {ι : Type}
    (idx : Ffi.Values signature.arguments → Ffi.Call → ι)
    {result : ι → Ffi.Values signature.arguments → Ffi.ResultValue signature.result}
    {writes : ι → Ffi.Values signature.arguments → Ffi.Footprint}
    {unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop}
    {domain : ι → Ffi.Values signature.arguments → Ffi.Call → Prop}
    (h : ∀ i, Ffi.Realizes signature (result i) (writes i) unaliased (domain i) execute) :
    FfiRealizesCall signature (fun a call => result (idx a call) a)
      (fun a call => writes (idx a call) a) unaliased
      (fun a call => domain (idx a call) a call) execute :=
  fun a call entry inDomain => h (idx a call) a call entry inDomain

/-- The typed form of `RealizesCall.restrict`: a call-dependent certificate gives each member
of a family whose domain fixes the result and footprint. -/
theorem FfiRealizesCall.restrict {signature : Ffi.Signature}
    {execute : Ffi.Call → Ffi.State → Prop}
    {result : Ffi.Values signature.arguments → Ffi.Call → Ffi.ResultValue signature.result}
    {writes : Ffi.Values signature.arguments → Ffi.Call → Ffi.Footprint}
    {unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop}
    {domain : Ffi.Values signature.arguments → Ffi.Call → Prop}
    (h : FfiRealizesCall signature result writes unaliased domain execute)
    {result' : Ffi.Values signature.arguments → Ffi.ResultValue signature.result}
    {writes' : Ffi.Values signature.arguments → Ffi.Footprint}
    {domain' : Ffi.Values signature.arguments → Ffi.Call → Prop}
    (hdom : ∀ a call, domain' a call → domain a call)
    (hres : ∀ a call, domain' a call → result a call = result' a)
    (hwr : ∀ a call, domain' a call → writes a call = writes' a) :
    Ffi.Realizes signature result' writes' unaliased domain' execute := by
  intro a call entry inDomain
  obtain ⟨final, run, res⟩ := h a call entry (hdom a call inDomain)
  rw [hres a call inDomain, hwr a call inDomain] at res
  exact ⟨final, run, res⟩

theorem FfiRealizesCall.mono_domain {signature : Ffi.Signature}
    {execute : Ffi.Call → Ffi.State → Prop}
    {result : Ffi.Values signature.arguments → Ffi.Call → Ffi.ResultValue signature.result}
    {writes : Ffi.Values signature.arguments → Ffi.Call → Ffi.Footprint}
    {unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop}
    {domain domain' : Ffi.Values signature.arguments → Ffi.Call → Prop}
    (h : FfiRealizesCall signature result writes unaliased domain execute)
    (hdom : ∀ a call, domain' a call → domain a call) :
    FfiRealizesCall signature result writes unaliased domain' execute :=
  fun a call entry inDomain => h a call entry (hdom a call inDomain)

/-! ## Function contracts -/

/-- **An open-machine contract is a call-dependent certificate** whose footprint is the
contract's footprint at the entry state; only the entry and value obligations remain. -/
theorem toRealizesCall (C : FnContract Open.isa) (signature : Signature)
    (result : Arguments signature.arguments → ReturnValue signature.result)
    (domain : Arguments signature.arguments → Call → Prop)
    (entry : ∀ arguments call, Silmaril.C.Api.SysV.Entry signature arguments call →
      domain arguments call → C.entry call.initial)
    (value : ∀ arguments call final, Silmaril.C.Api.SysV.Entry signature arguments call →
      domain arguments call → C.post call.initial final →
        Silmaril.C.Api.SysV.ResultAt final signature.result (result arguments)) :
    RealizesCall signature (fun a _ => result a) (fun _ call => C.footprint call.initial)
      domain (fun call final => Reaches Open.step call.initial final) := by
  intro a call admitted inDomain
  have h := FnContract.toRealizes C signature result (fun _ => C.footprint call.initial)
    (fun a' call' => domain a' call' ∧ call' = call)
    (fun a' _ e d => by obtain ⟨d1, rfl⟩ := d; exact entry a' _ e d1)
    (fun a' _ final e d hp => by obtain ⟨d1, rfl⟩ := d; exact value a' _ final e d1 hp)
    (fun _ _ _ _ d hx => by obtain ⟨-, rfl⟩ := d; exact hx)
  exact h a call admitted ⟨inDomain, rfl⟩

/-- The typed FFI form of `toRealizesCall`. -/
theorem toFfiRealizesCall (C : FnContract Open.isa) (signature : Ffi.Signature)
    (result : Ffi.Values signature.arguments → Ffi.ResultValue signature.result)
    (unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop)
    (domain : Ffi.Values signature.arguments → Ffi.Call → Prop)
    (stackAlign : 16 ∣ signature.callPlan.stackAlign)
    (entry : ∀ arguments call, Ffi.Entry signature arguments call (unaliased arguments) →
      domain arguments call → C.entry call.initial.machine)
    (value : ∀ arguments call (final : MState),
      Ffi.Entry signature arguments call (unaliased arguments) → domain arguments call →
      C.post call.initial.machine final →
        Ffi.ResultAt signature call { call.initial with machine := final } (result arguments)) :
    FfiRealizesCall signature (fun a _ => result a)
      (fun _ call => C.footprint call.initial.machine) unaliased domain Open.ffiExecute := by
  intro a call admitted inDomain
  have h := FnContract.toFfiRealizes C signature result
    (fun _ => C.footprint call.initial.machine) unaliased
    (fun a' call' => domain a' call' ∧ call' = call) stackAlign
    (fun a' _ e d => by obtain ⟨d1, rfl⟩ := d; exact entry a' _ e d1)
    (fun a' _ final e d hp => by obtain ⟨d1, rfl⟩ := d; exact value a' _ final e d1 hp)
    (fun _ _ _ _ d hx => by obtain ⟨-, rfl⟩ := d; exact hx)
  exact h a call admitted ⟨inDomain, rfl⟩

/-! ## `right_rot` -/

open Silmaril.X86.FnContract.RightRot in
/-- **`right_rot` with a call-dependent footprint**: the sixteen bytes below the entry stack
pointer of each call, in one certificate (A's `RightRot.realizes` is a family over `sp0`). -/
theorem rightRot_realizesCall :
    RealizesCall FnContract.RightRot.signature (fun a _ => result a)
      (fun a call => writes (call.initial.core.read .rsp) a)
      (fun a call => Domain (call.initial.core.read .rsp) a call)
      (fun call final => Reaches Open.step call.initial final) :=
  RealizesCall.of_family (result := fun _ => result) (fun _ call => call.initial.core.read .rsp)
    realizes

open Silmaril.X86.FnContract.RightRot in
/-- Each member of A's family is recovered from the call-dependent certificate. -/
theorem rightRot_realizes_of_call (sp0 : Word) :
    Realizes FnContract.RightRot.signature result (writes sp0) (Domain sp0)
      (fun call final => Reaches Open.step call.initial final) :=
  rightRot_realizesCall.restrict (fun a call d => d.sp ▸ d) (fun _ _ _ => rfl)
    (fun _ _ d => by simp only [d.sp])

/-! ## `strlen` -/

open Silmaril.X86.Stencils.ByteLoop in
/-- A NUL-terminated string has one length. -/
theorem cstr_unique {mem : Silmaril.Process.Memory} {s k k' : Nat} (h : CStr mem s k)
    (h' : CStr mem s k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with lt | eq | gt
  · exact absurd h.2.2 (h'.2.1 k lt)
  · exact eq
  · exact absurd h'.2.2 (h.2.1 k' gt)

open Silmaril.X86.Stencils.ByteLoop in
theorem cstrLen_eq {mem : Silmaril.Process.Memory} {s k : Nat} (h : CStr mem s k) :
    cstrLen mem s = k := by
  have ex : ∃ k, CStr mem s k := ⟨k, h⟩
  simp only [cstrLen, ex, dite_true]
  exact cstr_unique (Classical.choose_spec ex) h

open Silmaril.X86.Stencils.ByteLoop Silmaril.X86.Ladder.LibMini in
/-- **`strlen` with a call-dependent result**: the length of the argument string, in one
certificate (A's `strlen_realizes entry k` is a family over the length `k`). -/
theorem strlen_realizesCall (entry : Word) :
    RealizesCall sigScan
      (fun _ call => BitVec.ofNat 64 (cstrLen call.initial.memory (arg0 call.initial)))
      (fun _ _ => fun _ => False)
      (fun _ call => (scanContract strlenCode entry).entry call.initial ∧
        ∃ k, CStr call.initial.memory (arg0 call.initial) k)
      (fun call final => Reaches Open.step call.initial final) := by
  have h := RealizesCall.of_family (signature := sigScan)
    (fun _ call => cstrLen call.initial.memory (arg0 call.initial))
    (result := fun k _ => BitVec.ofNat 64 k) (writes := fun _ _ _ => False)
    (domain := fun k _ call => (scanContract strlenCode entry).entry call.initial ∧
      CStr call.initial.memory (arg0 call.initial) k)
    (strlen_realizes entry)
  refine h.mono_domain fun _ call ⟨he, k, hk⟩ => ⟨he, ?_⟩
  rw [cstrLen_eq hk]
  exact hk

end Silmaril.Machine.Abi.CallFootprint
