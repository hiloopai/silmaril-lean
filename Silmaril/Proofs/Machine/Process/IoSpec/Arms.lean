module

public import Silmaril.Proofs.Machine.Process.IoSpec.Psafe

/-!
# Proofs: the LPS arms of `IoSpec` are sound

Names in `Silmaril.Proofs.Machine.Process.IoSpec`.

* **`sound_ofArms`**: a list of sound arms is a sound environment.
* **`armSound_exit`**, **`armSound_write`**, **`armSound_read`**: the `exit`/`exit_group`
  arm (from `exit_dispatch`), the `write` arm (from `writeArm_holds`) and the `read` arm (from
  `readArm_holds` the corrected `Task.readArm`).
* **`sound_lpsEnv`**: `Sound (lpsEnv segs) segs refused`, for every segment list and refusal
  filter.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.IoSpec

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Proofs.Machine.Process.LpsBridge

variable {segs : List Segment} {refused : RefusalFilter}

/-- **A list of sound arms is a sound environment.** -/
theorem sound_ofArms {arms : List Arm} (h : ∀ a ∈ arms, ArmSound segs refused a) :
    Sound (ofArms arms) segs refused := by
  intro m ch model e he hh hl ht ⟨a, ha, hH⟩
  obtain ⟨hu, hk⟩ := h a ha m ch model e he hh hl ht ⟨a, List.mem_singleton_self a, hH⟩
  refine ⟨hu, fun eff model' evs hs => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk eff model' evs hs
  refine ⟨h1, fun hh' => ?_, fun code hc => ?_⟩
  · obtain ⟨hl', hr⟩ := h2 hh'
    refine ⟨hl', fun hnr => ?_⟩
    obtain ⟨e', he', a', ha', hH', ho⟩ := hr hnr
    rw [List.mem_singleton] at ha'
    subst a'
    exact ⟨e', he', _, ha, hH', ho⟩
  · obtain ⟨a', ha', hH', ho⟩ := h3 code hc
    rw [List.mem_singleton] at ha'
    subst a'
    exact ⟨_, ha, hH', ho⟩

/-- **The `exit`/`exit_group` arm is sound.** -/
theorem armSound_exit : ArmSound segs refused exitArm := by
  intro m ch model e he hh hl ht ⟨a, ha, hH⟩
  rw [List.mem_singleton] at ha
  subst ha
  have hno : (reqOf segs (trapped ⟨m, none⟩ ch)).sysno.toNat = 60 ∨
      (reqOf segs (trapped ⟨m, none⟩ ch)).sysno.toNat = 231 := hH
  have hH0 := hH
  change e = model at he
  subst he
  refine ⟨fun hs => ?_, fun eff model' evs hs => ?_⟩
  · have := (exit_dispatch _ _ _ hno).1 hs
    cases this
  have := (exit_dispatch _ _ _ hno).1 hs
  cases this
  refine ⟨by simp [Model.withHalted, Model.killedBy],
    fun hh' => by simp [Model.withHalted, Model.halted] at hh', fun code hc => ?_⟩
  simp only [Model.withHalted, Model.halted, Option.some.injEq] at hc
  subst hc
  exact ⟨exitArm, List.mem_singleton_self _, hH0, rfl⟩

/-- **The `write` arm is sound.** -/
theorem armSound_write : ArmSound segs refused (writeArm segs) := by
  intro m ch model e he hh hl ht ⟨a, ha, hH⟩
  rw [List.mem_singleton] at ha
  subst ha
  have hH0 := hH
  change e = model at he
  subst he
  obtain ⟨hno, c, lookup, live, modeled, nonzero, source⟩ := hH
  have iff := fun o => writeArm_holds _ e c o hno lookup live modeled nonzero source
  refine ⟨fun hs => ?_, fun eff model' evs hs => ?_⟩
  · obtain ⟨ds, -, h⟩ := (iff _).1 hs
    cases h
  · obtain ⟨ds, ⟨h1, h2, h3⟩, h⟩ := (iff _).1 hs
    cases h
    refine ⟨?_, fun _ => ⟨hl, fun _ => ⟨e, rfl, writeArm segs, List.mem_singleton_self _, hH0,
      c, lookup, ds, h1, h2, h3, rfl⟩⟩, fun code hc => ?_⟩
    · simp [Model.killedBy, Model.halted] at hh ⊢; simp [hh]
    · rw [hh] at hc; cases hc

/-- **The `read` arm is sound.** -/
theorem armSound_read : ArmSound segs refused (readArm segs) := by
  intro m ch model e he hh hl ht ⟨a, ha, hH⟩
  rw [List.mem_singleton] at ha
  subst ha
  have hH0 := hH
  change e = model at he
  subst he
  obtain ⟨hno, lookup, ok, writable⟩ := hH
  have iff := fun o => readArm_holds _ e o hno lookup ok writable
  refine ⟨fun hs => ?_, fun eff model' evs hs => ?_⟩
  · rcases (iff _).1 hs with ⟨-, h⟩ | ⟨-, bs, -, h⟩ <;> cases h
  · rcases (iff _).1 hs with ⟨hz, h⟩ | ⟨hz, bs, ⟨h1, h2, h3⟩, h⟩
    · cases h
      refine ⟨?_, fun _ => ⟨hl, fun _ => ⟨e, rfl, readArm segs, List.mem_singleton_self _, hH0,
        .inl ⟨hz, rfl⟩⟩⟩, fun code hc => ?_⟩
      · simp [Model.killedBy, Model.halted] at hh ⊢; simp [hh]
      · rw [hh] at hc; cases hc
    · cases h
      refine ⟨?_, fun _ => ⟨by simpa [Model.withStdin, Model.vmLazy] using hl,
        fun _ => ⟨_, rfl, readArm segs, List.mem_singleton_self _, hH0,
        .inr ⟨hz, bs, h1, h2, h3, rfl⟩⟩⟩, fun code hc => ?_⟩
      · simp [Model.halted] at hh; simp [Model.withStdin, Model.killedBy, hh]
      · simp [Model.withStdin, Model.halted] at hc hh; rw [hh] at hc; cases hc

/-- **The LPS environment is sound.** -/
theorem sound_lpsEnv : Sound (lpsEnv segs) segs refused :=
  sound_ofArms fun a ha => by
    simp only [lpsArms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact armSound_exit
    · exact armSound_write
    · exact armSound_read

end Silmaril.Proofs.Machine.Process.IoSpec
