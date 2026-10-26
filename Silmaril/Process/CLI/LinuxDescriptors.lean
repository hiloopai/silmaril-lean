module

public import Silmaril.Process.CLI.Process

/-! # Linux descriptor modes through actual finite process runs

The syscall contract keeps descriptor membership and readable/writable modes
fixed. Lift that existing fact through all actual process steps and silent
memory replacements, without specializing to an ISA or a favorable trace.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Proc

open Silmaril.Process.Syscall

/-- Retirements, returning calls and exits all retain descriptor modes. -/
theorem Step.linux_descriptor_modes {I : Isa} {before after : PState I Env.linux}
    {events : List Event} (step : Step I Env.linux before events after) (fd : Nat) :
    (after.env.descriptors fd).map (fun descriptor => (descriptor.readable, descriptor.writable)) =
      (before.env.descriptors fd).map (fun descriptor => (descriptor.readable, descriptor.writable)) := by
  cases step with
  | retire => rfl
  | call _ _ _ effect _ => exact effect.descriptor_modes fd
  | exit _ _ _ effect => exact effect.descriptor_modes fd

/-- The endpoint of the caller's original finite run retains open modes. -/
theorem runs_linux_descriptor_modes {I : Isa} {before after : PState I Env.linux}
    {events : List Event} (run : Runs I Env.linux before events after) (fd : Nat) :
    (after.env.descriptors fd).map (fun descriptor => (descriptor.readable, descriptor.writable)) =
      (before.env.descriptors fd).map (fun descriptor => (descriptor.readable, descriptor.writable)) := by
  induction run with
  | refl => rfl
  | cons head _ ih => exact ih.trans (head.linux_descriptor_modes fd)

/-- Recover a writable endpoint descriptor from the original launch. This is
availability of a descriptor, not a promise that a write syscall completes. -/
theorem runs_linux_writable {I : Isa} {before after : PState I Env.linux}
    {events : List Event} (run : Runs I Env.linux before events after) {fd : Nat}
    {descriptor : Descriptor} (opened : before.env.descriptors fd = some descriptor)
    (writable : descriptor.writable = true) :
    ∃ finalDescriptor, after.env.descriptors fd = some finalDescriptor ∧
      finalDescriptor.writable = true := by
  have modes := runs_linux_descriptor_modes run fd
  rw [opened] at modes
  cases final : after.env.descriptors fd with
  | none => simp only [final, Option.map_none, Option.map_some, reduceCtorEq] at modes
  | some finalDescriptor =>
    rw [final] at modes
    have same := congrArg Prod.snd (Option.some.inj modes)
    exact ⟨finalDescriptor, rfl, same.trans writable⟩

end Silmaril.Process.CLI.Proc
