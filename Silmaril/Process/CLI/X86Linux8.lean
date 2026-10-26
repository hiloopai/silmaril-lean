module

public import Silmaril.Process.CLI.X86Linux
public import Silmaril.Process.CLI.X86Linux.ExtStep
public import Silmaril.X86.Ext8.Basic

/-! # x86-64 Linux over the `Ext8` variant

`step` is `Process.CLI.X86Linux.step` with the `X86.Ext8` fetch (the `X86.Ext`
decoder first, then the 8-bit forms and legacy high-byte registers). Everything
else -- the `syscall` recogniser, the request decoder, the kernel's return -- is
`X86Linux`'s.

`step_eq_or_unmodeled`: at every state the variant's step is the `X86Linux`
step, unless the `X86Linux` step is the `unmodeled` fault. So every run of
`X86Linux` that never reaches an `unmodeled` fault is a run of the variant
(`isa` steps agree), and the variant only adds behaviour where `X86Linux` was
stuck on bytes outside `X86.Ext`.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux8

open Silmaril.Process.Syscall
open Silmaril.X86 (Reg Word)
open Silmaril.Process.CLI.X86Linux (Core syscallBytes execResult request Resume)

/-- One step of `X86.Ext8` with `syscall` recognised first. -/
def step (core : Core) (memory : Memory) : Step Core :=
  if memory.fetchBytes core.rip.toNat 2 = some syscallBytes then
    .syscall { core with rip := core.rip + 2 }
  else
    match X86.Ext8.fetch memory core.rip.toNat with
    | .inl .undecodable => .fault .unmodeled
    | .inl .truncated => .fault .memory
    | .inl (.decoded instr length) => execResult (X86.Ext.exec instr core memory length)
    | .inr (i, n) => execResult (X86.Ext8.execNew i core memory (core.rip + BitVec.ofNat 64 n))

/-- **Agreement with `X86Linux`**: the steps coincide wherever `X86.Ext` decodes. -/
theorem step_eq_of_fetch {core : Core} {memory : Memory}
    (h : X86.Ext.fetch memory core.rip.toNat ≠ .undecodable) :
    step core memory = X86Linux.step core memory := by
  unfold step X86Linux.step
  rw [X86.Ext8.fetch_of_ne_undecodable h]
  cases e : X86.Ext.fetch memory core.rip.toNat with
  | undecodable => exact absurd e h
  | truncated => rfl
  | decoded i n => rfl

/-- **Agreement with `X86Linux`**: the variant's step is `X86Linux`'s, or
`X86Linux` faulted as `unmodeled`. -/
theorem step_eq_or_unmodeled (core : Core) (memory : Memory) :
    step core memory = X86Linux.step core memory ∨
      X86Linux.step core memory = .fault .unmodeled := by
  by_cases h : X86.Ext.fetch memory core.rip.toNat = .undecodable
  · by_cases hs : memory.fetchBytes core.rip.toNat 2 = some syscallBytes
    · left; simp [step, X86Linux.step, hs]
    · right; simp [X86Linux.step, hs, h]
  · exact .inl (step_eq_of_fetch h)

/-- Every non-`unmodeled` step of `X86Linux` is a step of the variant. -/
theorem step_of_x86Linux {core : Core} {memory : Memory} {o : Step Core}
    (h : X86Linux.step core memory = o) (ho : o ≠ .fault .unmodeled) : step core memory = o := by
  rcases step_eq_or_unmodeled core memory with e | e
  · rw [e, h]
  · exact absurd (h ▸ e) ho

/-- Successful `X86.Ext` steps (retirements and the designated return) are
retirements of the variant's Linux step. -/
theorem step_retired_of_ext_success {exit : Word} {initial final : X86.MState}
    (success : X86.Ext.step exit initial = .retired final ∨
      X86.Ext.step exit initial = .returned final) :
    step initial.core initial.memory = .retired final.core final.memory :=
  step_of_x86Linux (X86Linux.step_retired_of_ext_success success) (fun h => by cases h)

def isa : Isa where
  Core := Core
  step core memory o := o = step core memory
  request := request
  resume := Resume

theorem isa_total : isa.Total := fun core memory => ⟨step core memory, rfl⟩

end Silmaril.Process.CLI.X86Linux8
