module

public import Silmaril.Machine.Abi.Win64.Defs
public import Silmaril.Machine.Abi.SystemV.Thms
import Silmaril.Proofs.Machine.Abi.Win64.Entry
/-! # The Microsoft x64 comorphism on the INTEGER/pointer fragment

* `ms64_wellFormed`: the convention data passes Silmaril's sanity checks.
* `entry_inhabited`: every argument tuple has a Microsoft x64 entry state
  (RCX, RDX, R8, R9, shadow space, then 8-byte slots).
* `win64`: the convention, and `win64CoHom` its institution comorphism, with the
  same source institution (`SystemV.vocab.logic.inst`) and the same target
  institution as `sysv`.
* `win64_sat`: its satisfaction condition (the generic `sat_translate`, whose
  only semantic premise `entry_inhabited` is discharged here).
* `sysv_resultAt_iff`, `win64_resultAt_iff`: both conventions read results from
  the low bytes of RAX in the same way.
* `not_agree`: System V and Microsoft x64 do *not* agree on `long f(long)`, so
  linking across them needs a thunk (`Silmaril.Machine.Abi.CrossAbi`).
-/

@[expose] public section
namespace Silmaril.Machine.Abi.Win64

open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (Proto CallSite toValues vocab sysv Options)
open Silmaril.Logic.Institution.Bridges

theorem ms64_wellFormed : ms64.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- System V callee-saved registers are Microsoft x64 callee-saved too. -/
theorem sysv_calleeSaved_sub :
    ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ∈ ms64.calleeSaved := by decide

/-- Every C argument tuple of the fragment is placed by some machine entry state. -/
theorem entry_inhabited (p : Proto) (a : Arguments p.signature.arguments) : ∃ s, Entry p a s :=
  Silmaril.Proofs.Machine.Abi.Win64.entry_inhabited p a

/-- The Microsoft x64 convention on the INTEGER/pointer fragment. -/
def win64 : Convention vocab Ffi.State CallSite := convention entry_inhabited

/-- The Microsoft x64 institution comorphism from C interfaces to machine interfaces. -/
abbrev win64CoHom := win64.coHom

theorem win64_desc (p : Proto) : win64.desc p = ⟨.win64, .ok (msPlan p.objects p.resultObject)⟩ :=
  rfl

/-- The satisfaction condition of the Microsoft x64 comorphism. -/
theorem win64_sat (p : Proto) (model : Contracts.Model Ffi.State Ffi.State)
    (c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))) :
    Contracts.Sat model (win64.translate p c) ↔ Contracts.Sat (win64.reduce p model) c :=
  win64.sat_translate p model c

theorem win64_resultAt_iff (p : Proto) (s s' : Ffi.State) (r : vocab.Ret p) :
    win64.ResultAt p s s' r ↔ RaxResult p.signature.result r s' := Iff.rfl

/-- System V reads fragment results exactly as Microsoft x64 does. -/
theorem sysv_resultAt_iff (options : Options) (p : Proto) (s s' : Ffi.State) (r : vocab.Ret p) :
    (sysv options).ResultAt p s s' r ↔ RaxResult p.signature.result r s' := by
  obtain ⟨⟨args, res⟩, arity⟩ := p
  cases res with
  | none =>
    simp only [RaxResult, iff_true]
    show (Silmaril.Machine.Abi.SystemV.intPlan _ none).result = .void
    rfl
  | some k => exact Iff.rfl

/-- `long f(long)`. -/
def unary : Proto := ⟨⟨[.int64], some .int64⟩, by decide⟩

/-- System V and Microsoft x64 place the argument of `long f(long)` differently:
the Microsoft x64 witness entry for `f(1)` (RCX = 1, RDI = 0) is no System V
entry. -/
theorem not_agree (options : Options) : ¬ (sysv options).Agree win64 unary := by
  intro agree
  let a : Arguments unary.signature.arguments := .cons (1#64 : BitVec 64) .nil
  have entry := Silmaril.Proofs.Machine.Abi.Win64.entry_stateOf unary a
  obtain ⟨exit, h⟩ := (agree.1 a _).2 entry
  have args : Ffi.ArgumentAt (Silmaril.Proofs.Machine.Abi.Win64.stateOf
        (Silmaril.Proofs.Machine.Abi.SystemV.cells a))
      (SystemV.Kind.spec .int64) (1#64 : BitVec 64)
      ⟨SystemV.Kind.object .int64, [⟨0, (SystemV.Kind.object .int64).size, .gp .rdi⟩], none⟩ ∧
      True := h.argumentsAt
  obtain ⟨⟨-, bytes, enc, chunks⟩, -⟩ := args
  have hrdi := (chunks _ (List.mem_singleton_self _)).2
  change bytes = SystemV.Kind.encode .int64 (1#64 : BitVec 64) at enc
  subst enc
  revert hrdi
  decide

end Silmaril.Machine.Abi.Win64
