module

public import Silmaril.Machine.Abi.LibMini.Thms
public import Silmaril.X86.Sep.SysV.Thms
/-! # One spec stack: the canonical bridges

 The stack has three canonical notions:

1. **`Sep.FnSpec`** (`FnSpec.Sat C entry S`) is the spec authors write.
2. **`FnContract`** (`FnContract.Spec`, total, and `FnContract.Strict`, first-return) is its
   compiled, state-level form.
3. **`CallFootprint.FfiRealizesCall`** is the exported certificate: the ABI model's typed FFI
   signature, with a result and footprint that may depend on the call.

Every other notion is derived from these. This module gives the derivations canonical names;
most are thin compositions of existing lemmas. PROVED (standard axioms):

* `fnSpec_contract`: author spec ⇒ compiled form (`FnSpec.Sat.toFnContract`, total only);
* `contract_export`: compiled form ⇒ export (`CallFootprint.toFfiRealizesCall`);
* `fnSpec_export`: author spec ⇒ export, the composition of the two;
* `export_ffiRealizes`, `ffiRealizes_export`: export ⇔ the ABI model's `Ffi.Realizes` when the
  result and footprint do not depend on the call (`FfiRealizesCall.restrict`,
  `ffiRealizesCall_iff`);
* `strict_sysv_sat`: strict compiled form ⇒ track C's institution sentence
  `Contracts.Sat callModel (within ((sysv o).translate p c) room)` (`sat_of_strict`);
* `strlen_spine`: **the whole stack on one real function**, libmini's `strlen`.

**Not derivable:** `FnSpec.Sat` alone does not give the
institution sentence. `SPEC` is reachability of *some* return, and `callModel` reads the
*first* return, so strictness has to come from the certificate (`FunCert.strictW`). The
link logic's `Safe` (partial correctness) gives neither of the total notions back.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.SpecNotions

open Silmaril.X86 (MState Word)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Sep (FnSpec SProp)
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options)
open Silmaril.Machine.Abi.OpenMachine (callModel)
open Silmaril.Machine.Abi.CallFootprint (FfiRealizesCall)

/-- **Author spec ⇒ compiled form** (total, not strict). -/
def fnSpec_contract {S : FnSpec} {C : SProp} {entry : Word} (hS : S.Sat Open.isa C entry) :
    FnContract Open.isa :=
  hS.toFnContract Silmaril.X86.Sep.flat_open

/-- **Compiled form ⇒ export.** -/
theorem contract_export (K : FnContract Open.isa) (signature : Ffi.Signature)
    (result : Ffi.Values signature.arguments → Ffi.ResultValue signature.result)
    (unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop)
    (domain : Ffi.Values signature.arguments → Ffi.Call → Prop)
    (stackAlign : 16 ∣ signature.callPlan.stackAlign)
    (entry : ∀ arguments call, Ffi.Entry signature arguments call (unaliased arguments) →
      domain arguments call → K.entry call.initial.machine)
    (value : ∀ arguments call (final : MState),
      Ffi.Entry signature arguments call (unaliased arguments) → domain arguments call →
      K.post call.initial.machine final →
        Ffi.ResultAt signature call { call.initial with machine := final } (result arguments)) :
    FfiRealizesCall signature (fun a _ => result a)
      (fun _ call => K.footprint call.initial.machine) unaliased domain Open.ffiExecute :=
  CallFootprint.toFfiRealizesCall K signature result unaliased domain stackAlign entry value

/-- **Author spec ⇒ export**: the obligations are about the compiled contract
`S.contractSpec Open.isa C entry`. -/
theorem fnSpec_export {S : FnSpec} {C : SProp} {e : Word} (hS : S.Sat Open.isa C e)
    (signature : Ffi.Signature)
    (result : Ffi.Values signature.arguments → Ffi.ResultValue signature.result)
    (unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop)
    (domain : Ffi.Values signature.arguments → Ffi.Call → Prop)
    (stackAlign : 16 ∣ signature.callPlan.stackAlign)
    (entry : ∀ arguments call, Ffi.Entry signature arguments call (unaliased arguments) →
      domain arguments call → (S.contractSpec Open.isa C e).entry call.initial.machine)
    (value : ∀ arguments call (final : MState),
      Ffi.Entry signature arguments call (unaliased arguments) → domain arguments call →
      (S.contractSpec Open.isa C e).post call.initial.machine final →
        Ffi.ResultAt signature call { call.initial with machine := final } (result arguments)) :
    FfiRealizesCall signature (fun a _ => result a)
      (fun _ call => (S.contractSpec Open.isa C e).footprint call.initial.machine) unaliased domain
      Open.ffiExecute :=
  contract_export (fnSpec_contract hS) signature result unaliased domain stackAlign entry value

/-- **Export ⇒ the ABI model's `Ffi.Realizes`** for a call-independent member. -/
theorem export_ffiRealizes {signature : Ffi.Signature} {execute : Ffi.Call → Ffi.State → Prop}
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
    Ffi.Realizes signature result' writes' unaliased domain' execute :=
  h.restrict hdom hres hwr

/-- **the ABI model's `Ffi.Realizes` ⇒ export** (constant in the call). -/
theorem ffiRealizes_export {signature : Ffi.Signature} {execute : Ffi.Call → Ffi.State → Prop}
    {result : Ffi.Values signature.arguments → Ffi.ResultValue signature.result}
    {writes : Ffi.Values signature.arguments → Ffi.Footprint}
    {unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop}
    {domain : Ffi.Values signature.arguments → Ffi.Call → Prop}
    (h : Ffi.Realizes signature result writes unaliased domain execute) :
    FfiRealizesCall signature (fun a _ => result a) (fun a _ => writes a) unaliased domain
      execute :=
  (CallFootprint.ffiRealizesCall_iff _ _ _ _ _ _).2 h

/-- **Strict compiled form ⇒ institution sentence** (track C's System V comorphism under
the first-return call relation). -/
theorem strict_sysv_sat {o : Options} {p : Proto} (K : FnContract.Strict Open.isa)
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))} {room : Ffi.State → Prop}
    (entry : ∀ a s, (sysv o).Entry p a s → c.pre a → room s → K.entry s.machine)
    (post : ∀ a s t, (sysv o).Entry p a s → c.pre a → room s → K.post s.machine t →
      (∃ r, (sysv o).ResultAt p s { s with machine := t } r) ∧
        ∀ r, (sysv o).ResultAt p s { s with machine := t } r → c.post a (some r)) :
    Contracts.Sat callModel (within ((sysv o).translate p c) room) :=
  OpenMachine.sat_of_strict K.strict entry post

open Silmaril.X86.Stencils.ByteLoop Silmaril.X86.Ladder.LibMini in
/-- libmini's `strlen` as a strict compiled contract (entries with the return address outside
the code). -/
def strlenStrict (entry : Word) : FnContract.Strict Open.isa where
  toSpec := (scanContract strlenCode entry).restrict
    (FnContract.RetOutside Open.isa entry strlenCode.length)
  total := (strlen_strict entry).total
  strict := strlen_strict entry

open Silmaril.X86.Stencils.ByteLoop Silmaril.X86.Ladder.LibMini
  Silmaril.Machine.Abi.LibMini in
/-- **The whole stack on libmini's `strlen`**, from one certificate: the author spec, the
strict compiled form, the export, a derived the ABI model certificate per length and a derived
institution sentence per length. -/
theorem strlen_spine (o : Options) (profile : Profile) (entry : Word) :
    scanSpec.Sat Open.isa (Silmaril.X86.Sep.codePt entry.toNat strlenCode) entry ∧
    (strlenStrict entry).toSpec = (scanContract strlenCode entry).restrict
      (FnContract.RetOutside Open.isa entry strlenCode.length) ∧
    FfiRealizesCall (strlenProto.ffi profile (SystemV.plan_intPlan profile))
      (fun _ call => BitVec.ofNat 64
        (CallFootprint.cstrLen call.initial.machine.memory (arg0 call.initial.machine)))
      (fun _ _ _ => False) (fun _ _ _ => True)
      (fun a call => strlenDomain entry
        (CallFootprint.cstrLen call.initial.machine.memory (arg0 call.initial.machine)) a call)
      Open.ffiExecute ∧
    (∀ k, Ffi.Realizes (strlenProto.ffi profile (SystemV.plan_intPlan profile))
      (fun _ => BitVec.ofNat 64 k) (fun _ _ => False) (fun _ _ _ => True)
      (strlenDomain entry k) Open.ffiExecute) ∧
    ∀ k, Contracts.Sat callModel
      (within ((sysv o).translate strlenProto (strlenC k)) (StrlenRoom entry k)) := by
  refine ⟨strlen_sat entry, rfl, strlen_ffiRealizesCall profile entry,
    strlen_ffiRealizes_of_call profile entry, fun k => ?_⟩
  refine strict_sysv_sat (strlenStrict entry) (fun _ _ _ _ roomy => ⟨roomy.1, roomy.2.1⟩) ?_
  intro a s t _ _ roomy hpost
  have hrax : t.core.read .rax = BitVec.ofNat 64 k := hpost.1 k roomy.2.2
  refine ⟨⟨BitVec.ofNat 64 k,
    (OpenMachine.resultAt_word64 _ .uint64 (.inl rfl) _ _ _ _).2 hrax⟩, fun r at_ => ?_⟩
  have := (OpenMachine.resultAt_word64 _ .uint64 (.inl rfl) _ _ _ _).1 at_
  exact congrArg some (this.symm.trans hrax)

end Silmaril.Machine.Abi.SpecNotions
