module

public import Silmaril.Proofs.Machine.Process.LpsBridge.Syscall

/-!
# Proofs: the `write` arm of the open-machine/LPS bridge

* `write_dispatch`: number 1 of the native table is LPS `write_spec`.
* `write_channel_iff`: on a descriptor bound to a live channel `ch` (`ch ≠ 0`), with a
  modelled range, a nonzero count and a non-empty readable source, the outcomes of LPS
  `write_spec` are exactly: some non-empty prefix `ds` of the readable source, at most the
  clamped count, is written, with one `writeEv ch` per byte, return value `|ds|`, the copy-in
  `(buf, |ds|)` recorded and the model unchanged. Nothing is `unmodeled`.
* `writeArm_holds : Task.writeArm` (the corrected statement, see `Defs`).
* **`psafe_write`**: an aligned configuration at `0F 05` with `rax = 1` on such a channel is
  process-safe if, for every such prefix `ds`, every aligned configuration of the state LPS
  resumes with is process-safe for the traces after `ds.map (writeEv ch)`.

Copied (adapted to any channel): `input_getModel_iff`, `bind_choose_iff`,
`emit_recordCopyins_retOnly_iff`, `write_channel_iff` from silmaril-lean
`Process/LPS/Problems/Sha256Cli/WriteSpec.lean` and `write_dispatch` from
`Sha256Cli/WriteStep.lean` (pinned `silmaril` package); those modules are not imported because
they pull in the sha256 filter's middle model.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Sys
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge

theorem input_getModel_iff {β : Type} (k : SyscallInput → Model → Sys β) (i : SyscallInput)
    (m : Model) (o : Outcome β) :
    (do let i' ← input; let m' ← getModel; k i' m') i m o ↔ k i m i m o := by
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, e₁, e₂, hx, ⟨x', m₁', e₁', e₂', hx', hk, rfl⟩, rfl⟩
      cases hx; cases hx'; simpa using hk
    · intro hk
      exact ⟨i, m, [], evs, rfl, ⟨m, m, [], evs, rfl, hk, rfl⟩, rfl⟩
  | unmodeled =>
    constructor
    · rintro (hx | ⟨x, m₁, e₁, hx, hk⟩)
      · cases hx
      · cases hx
        rcases hk with hx' | ⟨x', m₁', e₁', hx', hk'⟩
        · cases hx'
        · cases hx'; exact hk'
    · intro hk
      exact .inr ⟨i, m, [], rfl, .inr ⟨m, m, [], rfl, hk⟩⟩

theorem bind_choose_iff {α β : Type} (P : α → Prop) (k : α → Sys β) (i : SyscallInput)
    (m : Model) (o : Outcome β) : (Sys.choose P >>= k) i m o ↔ ∃ x, P x ∧ k x i m o := by
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, e₁, e₂, ⟨x', hx, hc⟩, hk, rfl⟩
      cases hc; exact ⟨x, hx, by simpa using hk⟩
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, m, [], evs, ⟨x, hx, rfl⟩, hk, rfl⟩
  | unmodeled =>
    constructor
    · rintro (⟨x, -, hc⟩ | ⟨x, m₁, e₁, ⟨x', hx, hc⟩, hk⟩)
      · cases hc
      · cases hc; exact ⟨x, hx, hk⟩
    · rintro ⟨x, hx, hk⟩
      exact .inr ⟨x, m, [], ⟨x, hx, rfl⟩, hk⟩

theorem emit_recordCopyins_retOnly_iff (evs : List Event) (reads : List (Word × Nat)) (r : Word)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect) :
    (emit evs >>= fun _ => recordCopyins reads (retOnly r)) i m o ↔
      o = .ok ((mkEffect r [] []).withCopyins (reads ++ [])) m evs := by
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ e =>
    constructor
    · rintro ⟨u, m₁, e₁, e₂, he, ⟨eff, m₃, e₃, e₄, hr, hp, rfl⟩, rfl⟩
      cases he; cases hr; cases hp; simp [mkEffect]
    · intro h
      rw [h]
      exact ⟨(), m, evs, [], rfl, ⟨_, m, [], [], rfl, rfl, rfl⟩, by simp⟩
  | unmodeled =>
    constructor
    · rintro (he | ⟨u, m₁, e₁, he, hr⟩)
      · cases he
      · cases he
        rcases hr with hr | ⟨eff, m₃, e₃, hr, hp⟩
        · cases hr
        · cases hr; cases hp
    · intro h; cases h

/-- **LPS `write` on a live channel, closed form.** -/
theorem write_channel_iff (fd buf count : Word) (ch : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (lookup : fdLookup m.fds fd = some (.channel ch))
    (live : wIs0 ch = false)
    (modeled : modeledRwRangeWith accessOkb buf count = true) (nonzero : wIs0 count = false)
    (source : writeSource i.mem buf count ≠ []) :
    writeSpec fd buf count i m o ↔
      ∃ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp count ∧
        ds = (writeSource i.mem buf count).take ds.length) ∧
        o = .ok ((mkEffect (lenWord ds) [] []).withCopyins ([(buf, ds.length)] ++ [])) m
          (ds.map (.writeEv ch)) := by
  have len : ((writeSource i.mem buf count).length == 0) = false := by
    cases h : writeSource i.mem buf count with
    | nil => exact absurd h source
    | cons => rfl
  unfold writeSpec writeSpecWith
  rw [input_getModel_iff]
  simp only [lookup, live, modeled, nonzero, len, Bool.not_true, Bool.false_eq_true,
    ite_false]
  rw [bind_choose_iff]
  simp only [emit_recordCopyins_retOnly_iff]

/-- Number 1 of the native table is LPS `write_spec`. -/
theorem write_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (number : i.sysno.toNat = 1) :
    NativeX86.extendedSyscallSpec i m o ↔
      writeSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)
        (NativeX86.referenceInputFor ⟨64, 1, "write"⟩ i) m o := by
  simp only [NativeX86.extendedSyscallSpec, dispatch, number]
  rfl

/-- **The `write` arm** (the corrected `Task.writeArm`). -/
theorem writeArm_holds : Task.writeArm := by
  intro i model ch o number lookup live modeled nonzero source
  exact (write_dispatch i model o number).trans
    (write_channel_iff _ _ _ ch _ model o lookup live modeled nonzero source)

variable {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}

/-- **The `write` arm of the bridge.** -/
theorem psafe_write {Allowed : List Event → Prop} {c : Config (machine oracle)} {m : MState}
    {ch : Word} (al : Aligned c m) (ht : AtSyscall m) (hA : Allowed [])
    (number : (m.core.read .rax).toNat = 1)
    (lookup : fdLookup c.model.fds (fd32 ((trapRequest (segs := segs) c m).arg 0)) =
      some (.channel ch))
    (live : wIs0 ch = false)
    (modeled : modeledRwRangeWith accessOkb ((trapRequest (segs := segs) c m).arg 1)
      ((trapRequest (segs := segs) c m).arg 2) = true)
    (nonzero : wIs0 ((trapRequest (segs := segs) c m).arg 2) = false)
    (source : writeSource (trapRequest (segs := segs) c m).mem
      ((trapRequest (segs := segs) c m).arg 1) ((trapRequest (segs := segs) c m).arg 2) ≠ [])
    (hk : ∀ ds : List Byte, 1 ≤ ds.length →
      ∀ c' : Config (machine oracle),
        Aligned c' (resume (trapped ⟨m, none⟩ (oracle c.ms.counter))
          ((mkEffect (lenWord ds) [] []).withCopyins
            ([((trapRequest (segs := segs) c m).arg 1, ds.length)] ++ []))) →
        c'.model = c.model →
        PSafe segs refused (fun tr => Allowed (ds.map (.writeEv ch) ++ tr)) c') :
    PSafe segs refused Allowed c := by
  have hno : (trapRequest (segs := segs) c m).sysno.toNat = 1 := number
  have iff := fun o => writeArm_holds _ c.model ch o hno lookup live modeled nonzero source
  refine psafe_syscall al ht hA ?_ ?_
  · intro hs
    obtain ⟨ds, -, h⟩ := (iff _).1 hs
    cases h
  · intro eff model' evs hs
    obtain ⟨ds, ⟨h1, -, -⟩, h⟩ := (iff _).1 hs
    cases h
    have halive := al.alive
    refine ⟨?_, fun _ => ⟨al.lazy, fun _ c' hal hmod => hk ds h1 c' hal hmod⟩, ?_⟩
    · simp [Model.killedBy, Model.halted] at halive ⊢; simp [halive]
    · intro code hc; rw [halive] at hc; cases hc

end Silmaril.Proofs.Machine.Process.LpsBridge
