module

public import Silmaril.Proofs.Machine.Abi.OpenMachine.LeafArith
public import Silmaril.X86.Cert.Kinds.Thms
/-!
# Strict (first-return) contracts and `callModel`

* `runsIn_iff`, `firstReturn_iff`: this module's `RunsIn`/`FirstReturn` on the open machine
  are the generic `FnContract.RunsIn Open.isa`/`FnContract.FirstReturn Open.isa`;
* `callModel_of_strict`: **a strict spec is read by `callModel` exactly**: from an entry
  state, `callModel` has an outcome, and every outcome is a `Spec.Result`;
* `sat_of_strict`: the generic bridge `sat_of_firstReturn`, from a strict spec;
* `clamp_strict`, `sat_strict`: rung 01's certificates give strict specs through the generic
  `BlockCert.FunCert.strict` (no new block VC), and `clamp_sat_strict`, `sat_sat_strict`
  re-derive `clamp_i32_sat`/`sat_add_u32_sat` from them.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.OpenMachine

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Ladder.LeafArith
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options)
open Silmaril.Machine.Abi.OpenMachine

theorem runsIn_of_generic {P : MState → Prop} {s t : MState}
    (r : FnContract.RunsIn Open.isa P s t) : RunsIn P s t := by
  induction r with
  | refl m => exact .refl m
  | step hp hs _ ih => exact .step hp hs ih

theorem runsIn_to_generic {P : MState → Prop} {s t : MState} (r : RunsIn P s t) :
    FnContract.RunsIn Open.isa P s t := by
  induction r with
  | refl m => exact .refl m
  | step hp hs _ ih => exact .step hp hs ih

theorem runsIn_iff {P : MState → Prop} {s t : MState} :
    RunsIn P s t ↔ FnContract.RunsIn Open.isa P s t :=
  ⟨runsIn_to_generic, runsIn_of_generic⟩

theorem firstReturn_iff {s t : MState} :
    FirstReturn s t ↔ FnContract.FirstReturn Open.isa s t :=
  ⟨fun h => ⟨runsIn_to_generic h.1, h.2⟩, fun h => ⟨runsIn_of_generic h.1, h.2⟩⟩

theorem callModel_of_strict {S : FnContract.Spec MState} (h : S.Strict Open.isa)
    {s : Ffi.State} (ha : FnContract.AbiEntry s.machine.core s.machine.memory)
    (he : S.entry s.machine) :
    (∃ t, t ∈ callModel s) ∧ ∀ t ∈ callModel s, S.Result Open.isa s.machine t.machine := by
  obtain ⟨u, first, res⟩ := FnContract.Spec.Strict.firstReturn h trivial ha he
  have first' := firstReturn_iff.mpr first
  refine ⟨⟨{ s with machine := u }, first', rfl⟩, fun t ht => ?_⟩
  rw [mem_callModel first' ht]
  exact res

variable {o : Options} {p : Proto}

theorem sat_of_strict {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))}
    {S : FnContract.Spec MState} {room : Ffi.State → Prop} (h : S.Strict Open.isa)
    (entry : ∀ a s, (sysv o).Entry p a s → c.pre a → room s → S.entry s.machine)
    (post : ∀ a s t, (sysv o).Entry p a s → c.pre a → room s → S.post s.machine t →
      (∃ r, (sysv o).ResultAt p s { s with machine := t } r) ∧
        ∀ r, (sysv o).ResultAt p s { s with machine := t } r → c.post a (some r)) :
    Contracts.Sat callModel (within ((sysv o).translate p c) room) := by
  refine sat_of_firstReturn (S := S) (fun a s e pre roomy => ?_) post
  obtain ⟨t, first, res⟩ :=
    FnContract.Spec.Strict.firstReturn h trivial (abiEntry_of_entry e) (entry a s e pre roomy)
  exact ⟨t, firstReturn_iff.mpr first, res⟩

/-! ## Rung 01 through the generic certificate -/

theorem clamp_strict :
    (clampSpec'.restrict (FnContract.RetOutside Open.isa base code.length)).Strict Open.isa :=
  BlockCert.FunCert.strict (F := clampCert) clampSpec' (entry := ⟨0x30, clampL30⟩)
    (by simp [clampCert]) clamp_i32_checked clamp_i32_vc fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

theorem sat_strict :
    (satSpec.restrict (FnContract.RetOutside Open.isa base code.length)).Strict Open.isa :=
  BlockCert.FunCert.strict (F := satCert) satSpec (entry := ⟨0x90, Bir.sat_add_u32.L_401400⟩)
    (by simp [satCert]) sat_add_u32_checked sat_add_u32_vc fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

theorem clamp_sat_strict (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) := by
  refine sat_of_strict clamp_strict
    (fun _ _ _ _ roomy => ⟨⟨roomy.loaded, roomy.pc⟩, roomy.retOutside⟩) ?_
  intro a s t entry _ _ hpost
  match a, entry with
  | .cons x (.cons lo (.cons hi .nil)), entry =>
    obtain ⟨hx, hl, hh⟩ := clamp_args entry
    have hrax : (t.core.read .rax).setWidth 32 = clampSpec x lo hi := by
      rw [show t.core.read .rax = _ from hpost, ← hx, ← hl, ← hh]
      simp
    refine ⟨⟨clampSpec x lo hi, (resultAt_int32 _ _ _ _ _).2 hrax⟩, fun r at_ => ?_⟩
    have := (resultAt_int32 _ _ _ _ _).1 at_
    exact congrArg some (this.symm.trans hrax)

theorem sat_sat_strict (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate satProto satC) (Room base code 0x90)) := by
  refine sat_of_strict sat_strict
    (fun _ _ _ _ roomy => ⟨⟨roomy.loaded, roomy.pc⟩, roomy.retOutside⟩) ?_
  intro a s t entry _ _ hpost
  match a, entry with
  | .cons x (.cons y .nil), entry =>
    obtain ⟨hx, hy⟩ := sat_args entry
    have hrax : (t.core.read .rax).setWidth 32 = satAddSpec x y := by
      rw [show t.core.read .rax = _ from hpost, ← hx, ← hy]
      simp
    refine ⟨⟨satAddSpec x y, (resultAt_uint32 _ _ _ _ _).2 hrax⟩, fun r at_ => ?_⟩
    have := (resultAt_uint32 _ _ _ _ _).1 at_
    exact congrArg some (this.symm.trans hrax)

end Silmaril.Proofs.Machine.Abi.OpenMachine
