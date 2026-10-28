module

public import Silmaril.Process.LPS.Problems.X86Probes.Budget
public import Silmaril.Process.LPS.Problems.X86Probes.Corpus
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.Split

/-! # Agreement between probes

`StatementProfile.agrees` on two probes (`Corpus.Pairs`) says: on every valid input, for
any valid entries of the two, if the first is not refused for budget then both runs are
error free and their observable traces are the same. To refute it we need one input and
two entries with the first run not budget refused (`Probe.NoBudget`, the budget kit of
`Problems.X86Probes.Budget`) and a trace of one run that is not a trace of the other.

* `exit42` and `exit43` disagree: `exit42` shows `exit(42)`, which no execution of `exit43`
  shows (`exit42_vs_exit43_refuted`).
* `write_hello` and `write_hello_split` disagree, although Linux prints `hello\n` for both.
  LPS writes a channel byte by byte and may cut any write short, so the split probe may
  print `h` and then `lo\n` (`WriteHelloSplit.admits_short`); every output of `write_hello`
  is a prefix of `hello\n` (`writeHello_vs_split_refuted`). The two agree on the full
  writes; they differ only in the short-write alternatives, which the single write cannot
  interleave.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

theorem nativeX86_refusals_none : nativeX86.refusals none = noFilter := rfl

/-- No reachable configuration of `exit42`'s launch is budget refused. -/
theorem exit42_noBudget (lim : Int) : Data.Exit42.probe.NoBudget (Data.Exit42.probe.initialAt lim) := by
  rw [Probe.initialAt_eq]
  nb_instr 120 5 (.movI32 .rax 60)
  nb_instr 125 5 (.movI32 .rdi 42)
  nb_trap 130
  nb_exit 42

/-- No reachable configuration of `write_hello`'s launch is budget refused. -/
theorem writeHello_noBudget (lim : Int) :
    Data.WriteHello.probe.NoBudget (Data.WriteHello.probe.initialAt lim) := by
  rw [Probe.initialAt_eq]
  nb_instr 120 5 (.movI32 .rax 1)
  nb_instr 125 5 (.movI32 .rdi 1)
  nb_instr 130 5 (.movI32 .rsi 0x40009a)
  nb_instr 135 5 (.movI32 .rdx 6)
  nb_trap 140
  nb_write 154 6
  intro ds _
  nb_instr 142 5 (.movI32 .rax 60)
  nb_instr 147 5 (.movI32 .rdi 0)
  nb_trap 152
  nb_exit 0

/-- A probe whose launch reaches no budget refusal is not budget refused in the native
profile's plain reading. -/
theorem not_budgetRefused_of_noBudget (P : Probe) (lim : Int) (noBudget : P.NoBudget (P.initialAt lim)) :
    ¬ nativeX86.budgetRefused none P.snapshot lim P.entry P.input := by
  rintro ⟨trace, c, star, refused⟩
  exact noBudget trace c star refused

theorem exit42_vs_exit43_refuted : ¬ Corpus.Pairs.exit42_vs_exit43 := by
  intro agrees
  have first := nativeLaunch_self Data.Exit42.probe rfl
  have second := nativeLaunch_self Data.Exit43.probe rfl
  obtain ⟨_, _, same⟩ := agrees Data.Exit42.probe.entry Data.Exit43.probe.entry Data.Exit42.probe.input
    first.entry second.entry (nativeLaunch_valid first).2
    (not_budgetRefused_of_noBudget _ _ (exit42_noBudget _))
  obtain ⟨fs, traced⟩ := (Exit42.admits noFilter).traces
  have shown := (same _).mp traced
  obtain ⟨rest, _, pre, post⟩ :=
    Omni.Exec.obsTrace (exit43_exec Data.Exit43.probe.entry Data.Exit43.probe.input _ second) shown
  obtain ⟨_, _, rfl, _, _⟩ := post
  simp [Probes.Observed.events, Probes.Observed.terminal, Data.Exit42.observed] at pre

theorem writeHello_vs_split_refuted : ¬ Corpus.Pairs.write_hello_vs_split := by
  intro agrees
  have first := nativeLaunch_self Data.WriteHello.probe rfl
  have second := nativeLaunch_self Data.WriteHelloSplit.probe rfl
  obtain ⟨_, _, same⟩ := agrees Data.WriteHello.probe.entry Data.WriteHelloSplit.probe.entry
    Data.WriteHello.probe.input first.entry second.entry (nativeLaunch_valid first).2
    (not_budgetRefused_of_noBudget _ _ (writeHello_noBudget _))
  obtain ⟨_, fs, _, run⟩ := WriteHelloSplit.admits_short targetAllocLimit
  have shown := (same _).mpr ⟨_, _, run.star, List.prefix_refl _⟩
  obtain ⟨rest, _, pre, post⟩ :=
    Omni.Exec.obsTrace (writeHello_exec Data.WriteHello.probe.entry Data.WriteHello.probe.input _ first) shown
  obtain ⟨ds, _, delivered, rfl⟩ := post.delivered
  have cases : ds ∈ [[], [104], [104, 101], [104, 101, 108], [104, 101, 108, 108],
      [104, 101, 108, 108, 111], [104, 101, 108, 108, 111, 10]] := (List.mem_inits ds _).mpr delivered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [List.cons_prefix_cons] at pre

end Silmaril.Process.LPS.Problems.X86Probes
