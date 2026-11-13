module

public import Silmaril.Proofs.Machine.Abi.OpenMachine.Sat
public import Silmaril.X86.Ladder.LeafArith.Thms
public import Silmaril.Machine.Abi.Win64.Thms
/-!
# Rung 01 against the System V comorphism, on the decoded open machine

`clamp_i32` and `sat_add_u32` of the pinned gcc `-O2` executable (track A's `FunCert`s
`clampCert`, `satCert`) satisfy `(sysv o).translate p c` for their exact C contracts, with the
first-return call relation `callModel` of the open machine, on entry states with the code
loaded, the entry at the function and the return address outside the 181 code bytes.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.OpenMachine

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Ladder.LeafArith
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options CallSite callOf)
open Silmaril.Machine.Abi.OpenMachine

variable {o : Options}

/-! ## Read-back of 32-bit results -/

theorem resultAt_int32 (args : List Scalar) (h : args.length ≤ SystemV.maxArity)
    (s s' : Ffi.State) (r : BitVec 32) :
    (sysv o).ResultAt ⟨⟨args, some .int32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r := by
  refine (Win64.sysv_resultAt_iff _ _ _ _ _).trans ?_
  constructor
  · rintro ⟨w, enc, ch⟩
    change w = _ at enc
    subst enc
    exact (chunk32_iff s' .rax r).1 ch
  · exact fun e => ⟨_, rfl, (chunk32_iff s' .rax r).2 e⟩

theorem resultAt_uint32 (args : List Scalar) (h : args.length ≤ SystemV.maxArity)
    (s s' : Ffi.State) (r : BitVec 32) :
    (sysv o).ResultAt ⟨⟨args, some .uint32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r := by
  refine (Win64.sysv_resultAt_iff _ _ _ _ _).trans ?_
  constructor
  · rintro ⟨w, enc, ch⟩
    change w = _ at enc
    subst enc
    exact (chunk32_iff s' .rax r).1 ch
  · exact fun e => ⟨_, rfl, (chunk32_iff s' .rax r).2 e⟩

/-! ## Arguments -/

theorem clamp_ffi_args {profile : Profile} {planned : SystemV.Planned profile}
    {v : Ffi.Values (clampProto.ffi profile planned).arguments} {call : Ffi.Call}
    {u : Nat → Nat → Prop} (e : Ffi.Entry (clampProto.ffi profile planned) v call u) :
    r32 .rdi call.initial.machine = v.1 ∧ r32 .rsi call.initial.machine = v.2.1 ∧
      r32 .rdx call.initial.machine = v.2.2.1 := by
  obtain ⟨⟨-, b0, e0, c0⟩, ⟨-, b1, e1, c1⟩, ⟨-, b2, e2, c2⟩, -⟩ := e.argumentsAt
  subst e0 e1 e2
  exact ⟨(chunk32_iff _ .rdi _).1 c0, (chunk32_iff _ .rsi _).1 c1, (chunk32_iff _ .rdx _).1 c2⟩

theorem sat_ffi_args {profile : Profile} {planned : SystemV.Planned profile}
    {v : Ffi.Values (satProto.ffi profile planned).arguments} {call : Ffi.Call}
    {u : Nat → Nat → Prop} (e : Ffi.Entry (satProto.ffi profile planned) v call u) :
    r32 .rdi call.initial.machine = v.1 ∧ r32 .rsi call.initial.machine = v.2.1 := by
  obtain ⟨⟨-, b0, e0, c0⟩, ⟨-, b1, e1, c1⟩, -⟩ := e.argumentsAt
  subst e0 e1
  exact ⟨(chunk32_iff _ .rdi _).1 c0, (chunk32_iff _ .rsi _).1 c1⟩

theorem clamp_args {x lo hi : BitVec 32} {s : Ffi.State}
    (entry : (sysv o).Entry clampProto (.cons x (.cons lo (.cons hi .nil))) s) :
    r32 .rdi s.machine = x ∧ r32 .rsi s.machine = lo ∧ r32 .rdx s.machine = hi := by
  obtain ⟨exit, e⟩ := entry
  exact clamp_ffi_args e

theorem sat_args {a b : BitVec 32} {s : Ffi.State}
    (entry : (sysv o).Entry satProto (.cons a (.cons b .nil)) s) :
    r32 .rdi s.machine = a ∧ r32 .rsi s.machine = b := by
  obtain ⟨exit, e⟩ := entry
  exact sat_ffi_args e

/-! ## Runs to the first return -/

theorem returned_of_result {S : FnContract.Spec MState} {m t : MState}
    (res : S.Result Open.isa m t) : Returned m t :=
  ⟨res.abi.pc, res.abi.stack⟩

theorem clamp_totalIn : TotalIn clampSpec' fun _ => InCode base code.length :=
  totalIn_of_funCert (F := clampCert) clampSpec' (entry := ⟨0x30, clampL30⟩)
    (by simp [clampCert]) clamp_i32_checked clamp_i32_vc fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

theorem sat_totalIn : TotalIn satSpec fun _ => InCode base code.length :=
  totalIn_of_funCert (F := satCert) satSpec (entry := ⟨0x90, Bir.sat_add_u32.L_401400⟩)
    (by simp [satCert]) sat_add_u32_checked sat_add_u32_vc fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

/-! ## ABI correctness -/

theorem clamp_sat (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) := by
  refine sat_of_firstReturn (S := clampSpec') ?_ ?_
  · intro a s entry _ roomy
    obtain ⟨t, runs, res⟩ := clamp_totalIn s.machine (abiEntry_of_entry entry)
      ⟨roomy.loaded, roomy.pc⟩
    exact ⟨t, firstReturn_of_runsIn runs (returned_of_result res) roomy.retOutside, res⟩
  · intro a s t entry _ _ hpost
    match a, entry with
    | .cons x (.cons lo (.cons hi .nil)), entry =>
      obtain ⟨hx, hl, hh⟩ := clamp_args entry
      have hrax : (t.core.read .rax).setWidth 32 = clampSpec x lo hi := by
        rw [show t.core.read .rax = _ from hpost, ← hx, ← hl, ← hh]
        simp
      refine ⟨⟨clampSpec x lo hi, (resultAt_int32 _ _ _ _ _).2 hrax⟩, fun r at_ => ?_⟩
      have := (resultAt_int32 _ _ _ _ _).1 at_
      exact congrArg some (this.symm.trans hrax)

theorem sat_sat (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate satProto satC) (Room base code 0x90)) := by
  refine sat_of_firstReturn (S := satSpec) ?_ ?_
  · intro a s entry _ roomy
    obtain ⟨t, runs, res⟩ := sat_totalIn s.machine (abiEntry_of_entry entry)
      ⟨roomy.loaded, roomy.pc⟩
    exact ⟨t, firstReturn_of_runsIn runs (returned_of_result res) roomy.retOutside, res⟩
  · intro a s t entry _ _ hpost
    match a, entry with
    | .cons x (.cons y .nil), entry =>
      obtain ⟨hx, hy⟩ := sat_args entry
      have hrax : (t.core.read .rax).setWidth 32 = satAddSpec x y := by
        rw [show t.core.read .rax = _ from hpost, ← hx, ← hy]
        simp
      refine ⟨⟨satAddSpec x y, (resultAt_uint32 _ _ _ _ _).2 hrax⟩, fun r at_ => ?_⟩
      have := (resultAt_uint32 _ _ _ _ _).1 at_
      exact congrArg some (this.symm.trans hrax)

/-! ## Typed FFI certificates (`Silmaril.Machine.SystemV.Abi`) through A's `toFfiRealizes`

The `uint32`/`int32` object specifications are track C's `SystemV.Kind.spec`, and the call
plan is the ABI model's `plan` (`SystemV.plan_intPlan`). -/

theorem stackAlign16 (profile : Profile) (p : Proto) :
    16 ∣ (p.ffi profile (SystemV.plan_intPlan profile)).callPlan.stackAlign :=
  Nat.dvd_refl 16

theorem clamp_ffiRealizes (profile : Profile) :
    Ffi.Realizes (clampProto.ffi profile (SystemV.plan_intPlan profile))
      (fun v => clampSpec v.1 v.2.1 v.2.2.1) (fun _ _ => False) (fun _ _ _ => True)
      (ffiLoadedAt 0x30) Open.ffiExecute := by
  refine FnContract.toFfiRealizes clamp_i32_contract _ _ _ _ _ (stackAlign16 profile _)
    ?_ ?_ ?_
  · intro _ call e d
    exact ⟨d.1, e.pc.trans d.2⟩
  · intro v call final e _ hpost
    obtain ⟨hx, hl, hh⟩ := clamp_ffi_args e
    refine ⟨_, rfl, (chunk32_iff _ .rax _).2 ?_⟩
    change (final.core.read .rax).setWidth 32 = _
    rw [show final.core.read .rax = _ from hpost, hx, hl, hh]
    simp
  · intro _ _ _ _ _ h
    exact h

theorem sat_ffiRealizes (profile : Profile) :
    Ffi.Realizes (satProto.ffi profile (SystemV.plan_intPlan profile))
      (fun v => satAddSpec v.1 v.2.1) (fun _ _ => False) (fun _ _ _ => True)
      (ffiLoadedAt 0x90) Open.ffiExecute := by
  refine FnContract.toFfiRealizes sat_add_u32_contract _ _ _ _ _ (stackAlign16 profile _)
    ?_ ?_ ?_
  · intro _ call e d
    exact ⟨d.1, e.pc.trans d.2⟩
  · intro v call final e _ hpost
    obtain ⟨hx, hy⟩ := sat_ffi_args e
    refine ⟨_, rfl, (chunk32_iff _ .rax _).2 ?_⟩
    change (final.core.read .rax).setWidth 32 = _
    rw [show final.core.read .rax = _ from hpost, hx, hy]
    simp
  · intro _ _ _ _ _ h
    exact h

end Silmaril.Proofs.Machine.Abi.OpenMachine
