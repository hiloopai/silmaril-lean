module

public import Silmaril.Machine.Process.LpsBridge.Defs
public import Silmaril.Machine.X86.Safe.Defs
public import Silmaril.Process.CLI.X86Linux.ExtStep

/-!
# Proofs: the instruction half of the open-machine/LPS bridge

* `open_step_trap`: the open machine is stuck at `0F 05` (neither `X86.Ext` nor the `Ext8`
  forms decode it), so a run that is `SafeN` reaches its postcondition before a `syscall`.
* `account_open`: a non-`syscall` open step is the LPS accounted instruction, with the same
  state, the same model and the same oracle counter.
* `sstep_open`: from an aligned configuration, that is the only LPS step.
* `account_trap`, `sstep_trap`: at `0F 05` the only LPS step records the pending number,
  completing the flags with the oracle's next choice.
* **`psafe_of_safeN`** (the instruction half): if the open state `m` of an aligned
  configuration is `SafeN Q n` for every `n`, and every aligned configuration with the same
  model whose state satisfies `Q` is process-safe, then so is the configuration. Before `Q`
  the trace is empty and nothing goes wrong.

Program-independent: nothing here mentions an image, a function or a syscall number.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.X86.Safe (SafeN)

variable {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}

/-- **The open machine is stuck at a `syscall`.** -/
theorem open_step_trap {m : MState} (h : AtSyscall m) : Silmaril.Machine.X86.Open.step m = none := by
  obtain ⟨more, window⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow h
    (limit := Silmaril.X86.maxInstrLength) (by decide)
  have hdec : Silmaril.X86.Ext.decode
      (Silmaril.X86.fetchWindow m.memory Silmaril.X86.maxInstrLength m.core.rip.toNat) = none := by
    rw [← window]; exact Silmaril.Process.CLI.X86Linux.ext_decode_syscall_prefix more
  have hnew : Silmaril.X86.Ext8.decodeNew
      (Silmaril.X86.fetchWindow m.memory Silmaril.X86.maxInstrLength m.core.rip.toNat) = none := by
    rw [← window]; rfl
  have hfetch : Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = .truncated ∨
      Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = .undecodable := by
    unfold Silmaril.X86.Ext.fetch
    rw [hdec]
    dsimp only
    split
    · split
      · exact .inl rfl
      · exact .inr rfl
    · exact .inr rfl
  unfold Silmaril.Machine.X86.Open.step Silmaril.X86.Ext8.fetch
  rcases hfetch with e | e <;> simp only [e, hnew]

theorem ext_fetch_of_ext8 {memory : Silmaril.Process.Memory} {a : Nat}
    {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (h : Silmaril.X86.Ext8.fetch memory a = .inl (.decoded i n)) :
    Silmaril.X86.Ext.fetch memory a = .decoded i n := by
  unfold Silmaril.X86.Ext8.fetch at h
  cases e : Silmaril.X86.Ext.fetch memory a with
  | decoded i' n' => rw [e] at h; cases h; rfl
  | truncated => rw [e] at h; cases h
  | undecodable =>
    rw [e] at h
    dsimp only at h
    split at h
    · split at h <;> cases h
    · cases h

/-- A non-`syscall` open step, as the native `Ext8` step of LPS. -/
theorem native8_open {m m' : MState} (hs : Silmaril.Machine.X86.Open.step m = some m')
    (nt : ¬ AtSyscall m) :
    ∃ acc, x86NativeStep8 ⟨m, none⟩ = .ok ⟨⟨m', none⟩, acc⟩ := by
  unfold x86NativeStep8
  dsimp only
  rw [ite_eq_right (show ¬ (m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05]) from nt)]
  unfold Silmaril.Machine.X86.Open.step at hs
  split at hs
  · rename_i i n hf
    rw [hf]
    have hn := Silmaril.X86.Ext.fetch_length (ext_fetch_of_ext8 hf)
    subst hn
    cases e : Silmaril.X86.Ext.exec i m.core m.memory <;>
      rw [e] at hs <;> simp only [Silmaril.Machine.X86.Open.ofResult, reduceCtorEq,
        Option.some.injEq] at hs
    subst hs
    exact ⟨_, by simp only [x86ExecResult, e]; rfl⟩
  · rename_i i n hf
    rw [hf]
    cases e : Silmaril.X86.Ext8.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n) <;>
      rw [e] at hs <;> simp only [Silmaril.Machine.X86.Open.ofResult, reduceCtorEq,
        Option.some.injEq] at hs
    subst hs
    exact ⟨_, by simp only [x86ExecResult, e]; rfl⟩
  · cases hs

/-! ## LPS steps from an aligned configuration -/

/-- **A non-`syscall` open step is the LPS accounted instruction** (same model, same oracle
counter). -/
theorem account_open {m m' : MState} (hs : Silmaril.Machine.X86.Open.step m = some m')
    (nt : ¬ AtSyscall m) (k : Nat) {model : Model} (lazy : model.vmLazy = []) :
    accountStep (machine oracle) segs ⟨⟨m, none⟩, k⟩ model = .ok (⟨⟨m', none⟩, k⟩, model) := by
  obtain ⟨acc, h⟩ := native8_open hs nt
  have st : (machine oracle).step segs ⟨⟨m, none⟩, k⟩ = .ok ⟨⟨⟨m', none⟩, k⟩, acc⟩ := by
    show X86FlagChoices.step8 oracle _ = _
    unfold X86FlagChoices.step8
    dsimp only
    rw [ite_eq_right (show ¬ (m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05]) from nt),
      h]
    rfl
  simp only [accountStep, st]
  rw [show (machine oracle).reportsAccesses = true from rfl]
  simp [X86Launch.materializeModelAccesses_no_lazy _ _ lazy]

/-- **The trap**: at `0F 05` LPS completes the flags with the oracle's next choice, records
the pending number `rax`, and advances the counter. -/
theorem account_trap {m : MState} (ht : AtSyscall m) (k : Nat) {model : Model}
    (lazy : model.vmLazy = []) :
    accountStep (machine oracle) segs ⟨⟨m, none⟩, k⟩ model =
      .ok (⟨trapped ⟨m, none⟩ (oracle k), k + 1⟩, model) := by
  have st : (machine oracle).step segs ⟨⟨m, none⟩, k⟩ =
      .ok ⟨⟨trapped ⟨m, none⟩ (oracle k), k + 1⟩, [(m.core.rip, 2)]⟩ := by
    show X86FlagChoices.step8 oracle _ = _
    unfold X86FlagChoices.step8
    dsimp only
    rw [ite_eq_left (show m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05] from ht)]
    unfold x86NativeStep8
    have ht' : (X86FlagChoices.completeState ⟨m, none⟩ (oracle k)).m.memory.fetchBytes
        (X86FlagChoices.completeState ⟨m, none⟩ (oracle k)).m.core.rip.toNat 2 =
        some [0x0f, 0x05] := ht
    rw [ite_eq_left ht']
    have hr := X86FlagChoices.completeFlags_rflagsImage m.core.flags (oracle k)
    cases e : rflagsImage (X86FlagChoices.completeState ⟨m, none⟩ (oracle k)).m.core.flags with
    | none =>
      exfalso
      have : (X86FlagChoices.completeState ⟨m, none⟩ (oracle k)).m.core.flags =
          X86FlagChoices.completeFlags m.core.flags (oracle k) := rfl
      rw [this] at e; rw [e] at hr; cases hr
    | some w => rfl
  simp only [accountStep, st]
  rw [show (machine oracle).reportsAccesses = true from rfl]
  simp [X86Launch.materializeModelAccesses_no_lazy _ _ lazy]

/-- With no syscall pending, the only LPS step is the accounted instruction. -/
theorem sstep_of_account {c : Config (machine oracle)} {ms' : (machine oracle).State}
    {model' : Model} (alive : c.model.halted = none) (pending : c.ms.native.pending = none)
    (account : accountStep (machine oracle) segs c.ms c.model = .ok (ms', model')) :
    SStep segs spec refused c [] (.next ⟨ms', model'⟩) ∧
      ∀ evs st, SStep segs spec refused c evs st → evs = [] ∧ st = .next ⟨ms', model'⟩ := by
  obtain ⟨ms, model⟩ := c
  have svc : (machine oracle).svcPending ms = none := pending
  refine ⟨.instr alive svc account, fun evs st s => ?_⟩
  cases s with
  | instr _ _ a => rw [account] at a; cases a; exact ⟨rfl, rfl⟩
  | instrFault _ _ a => rw [account] at a; cases a
  | instrUnmodeled _ _ a => rw [account] at a; cases a
  | syscall _ p => rw [svc] at p; cases p
  | syscallMaterializationFault _ p => rw [svc] at p; cases p
  | exit _ p => rw [svc] at p; cases p
  | killed _ p => rw [svc] at p; cases p
  | syscallUnmodeled _ p => rw [svc] at p; cases p

/-- **An open step from an aligned configuration is the only LPS step.** -/
theorem sstep_open {c : Config (machine oracle)} {m m' : MState} (al : Aligned c m)
    (hs : Silmaril.Machine.X86.Open.step m = some m') :
    SStep segs spec refused c [] (.next ⟨⟨⟨m', none⟩, c.ms.counter⟩, c.model⟩) ∧
      ∀ evs st, SStep segs spec refused c evs st →
        evs = [] ∧ st = .next ⟨⟨⟨m', none⟩, c.ms.counter⟩, c.model⟩ := by
  have nt : ¬ AtSyscall m := fun ht => by rw [open_step_trap ht] at hs; cases hs
  have hms : c.ms = ⟨⟨m, none⟩, c.ms.counter⟩ := by
    obtain ⟨⟨n, k⟩, model⟩ := c
    have := al.native
    simp only at this
    subst this
    rfl
  have acc := account_open (segs := segs) (oracle := oracle) hs nt c.ms.counter al.lazy
  rw [← hms] at acc
  refine sstep_of_account al.alive ?_ acc
  rw [al.native]

/-- **The trap from an aligned configuration is the only LPS step.** -/
theorem sstep_trap {c : Config (machine oracle)} {m : MState} (al : Aligned c m)
    (ht : AtSyscall m) :
    SStep segs spec refused c []
        (.next ⟨⟨trapped ⟨m, none⟩ (oracle c.ms.counter), c.ms.counter + 1⟩, c.model⟩) ∧
      ∀ evs st, SStep segs spec refused c evs st →
        evs = [] ∧ st = .next ⟨⟨trapped ⟨m, none⟩ (oracle c.ms.counter), c.ms.counter + 1⟩,
          c.model⟩ := by
  have hms : c.ms = ⟨⟨m, none⟩, c.ms.counter⟩ := by
    obtain ⟨⟨n, k⟩, model⟩ := c
    have := al.native
    simp only at this
    subst this
    rfl
  have acc := account_trap (segs := segs) (oracle := oracle) ht c.ms.counter al.lazy
  rw [← hms] at acc
  refine sstep_of_account al.alive ?_ acc
  rw [al.native]

/-! ## The instruction half -/

/-- One step of `SafeN` on the deterministic open machine. -/
theorem safeN_succ {Q : MState → Prop} {m m' : MState} (hq : ¬ Q m)
    (hs : Silmaril.Machine.X86.Open.step m = some m')
    (h : ∀ n, SafeN Silmaril.Machine.X86.Open.step Q n m) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step Q n m' := by
  intro n
  rcases h (n + 1) with h | ⟨m'', hs', hn⟩
  · exact absurd h hq
  · rw [hs] at hs'; cases hs'; exact hn

/-- Not yet at `Q`, a `SafeN` state steps. -/
theorem safeN_step {Q : MState → Prop} {m : MState} (hq : ¬ Q m)
    (h : ∀ n, SafeN Silmaril.Machine.X86.Open.step Q n m) :
    ∃ m', Silmaril.Machine.X86.Open.step m = some m' := by
  rcases h 1 with h | ⟨m', hs, -⟩
  · exact absurd h hq
  · exact ⟨m', hs⟩

/-- **The instruction half of the bridge.** An aligned configuration whose open state is
`SafeN Q n` for every `n` is process-safe, provided every aligned configuration with the same
model at a `Q` state is. Before `Q` the run makes LPS instruction steps only: the trace is
empty and no error is reachable. -/
theorem psafe_of_safeN {Q : MState → Prop} {Allowed : List Event → Prop} {model : Model}
    (hA : Allowed [])
    (hQ : ∀ (c' : Config (machine oracle)) m', Aligned c' m' → c'.model = model → Q m' →
      PSafe segs refused Allowed c')
    {c : Config (machine oracle)} {m : MState} (al : Aligned c m) (hm : c.model = model)
    (h : ∀ n, SafeN Silmaril.Machine.X86.Open.step Q n m) : PSafe segs refused Allowed c := by
  constructor
  · intro tr c' hstar
    induction hstar generalizing m with
    | refl => exact hA
    | @step c₁ evs c₂ tr c₃ s rest ih =>
      by_cases hq : Q m
      · exact (hQ c₁ m al hm hq).1 _ _ (.step s rest)
      · obtain ⟨m₁, hs⟩ := safeN_step hq h
        obtain ⟨-, uniq⟩ := sstep_open (segs := segs) (refused := refused) al hs
        obtain ⟨rfl, e⟩ := uniq _ _ s
        cases e
        exact ih ⟨rfl, al.alive, al.lazy⟩ hm (safeN_succ hq hs h)
  · intro tr c' evs hstar
    induction hstar generalizing m with
    | refl c₀ =>
      intro herr
      by_cases hq : Q m
      · exact (hQ c₀ m al hm hq).2 [] c₀ evs (.refl _) herr
      · obtain ⟨m₁, hs⟩ := safeN_step hq h
        obtain ⟨-, uniq⟩ := sstep_open (segs := segs) (refused := refused) al hs
        cases (uniq _ _ herr).2
    | @step c₁ evs' c₂ tr c₃ s rest ih =>
      by_cases hq : Q m
      · exact (hQ c₁ m al hm hq).2 _ _ evs (.step s rest)
      · obtain ⟨m₁, hs⟩ := safeN_step hq h
        obtain ⟨-, uniq⟩ := sstep_open (segs := segs) (refused := refused) al hs
        obtain ⟨rfl, e⟩ := uniq _ _ s
        cases e
        exact ih ⟨rfl, al.alive, al.lazy⟩ hm (safeN_succ hq hs h)

end Silmaril.Proofs.Machine.Process.LpsBridge
