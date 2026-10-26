module

public import Silmaril.Process.LPS.RunHelpers

/-!
# LPS in Lean: the rest of `Run.v`

`Run.lean` translates the definitions of LPS `Run.v` (upstream commit `f1006fe8`) that the
statements are written with. This file adds the remaining definitions of `Run.v` (and
`Fs.v:151` `fs_lt_head`) and the lemmas of `Run.v` that the run outcomes, budget
classification and progress rest on:

* `IsPrefix` (`is_prefix`), proved to be `List.IsPrefix`, which `ObsTrace` uses;
* the configured relations `SStepCfg`, `StarCfg`, `ObsTraceCfg`, `ReachesErrorCfg`,
  `AllTracesErrorCfg`, `ReachesUnmodeledCfg` (`Run.v:1618-1814`): LPS states a second copy
  of each relation with the filter premise, `Run.lean` has one relation parametric in the
  filter, and these names are its instances;
* the subset and may-fail lemmas: a filtered step is a step (`sstep_cfg_sub`), at
  `mayFailCfg` the filter removes nothing (`sstep_cfg_may_fail`, `run_scfg_may_fail`);
* **progress** (`Run.v:1714` `sstep_cfg_progress`): where the filter's question is decided, a
  configuration with a step has a filtered step;
* the abort-path frame `DeclOffFrame` (`decl_off_frame`), its refuted one-sided form, and its
  consequence that a run with the declaration off never records a kill;
* the budget observables `ReachesBudgetRefused`, `ReachesBudgetRefusedCfg`, the dispatcher's
  number list `allocMarkSysnos` and its completeness pins;
* `lookupInjected`, `EntryStackFits`, `entryStackSpanMax` and the span bound.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-! ## Prefixes (LPS `Run.v:41`) -/

/-- LPS `Run.v:41` `is_prefix`. -/
def IsPrefix {α : Type} : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ IsPrefix xs ys

/-- `is_prefix` is `List.IsPrefix`, the relation `ObsTrace` is written with. -/
theorem isPrefix_iff {α : Type} : ∀ l₁ l₂ : List α, IsPrefix l₁ l₂ ↔ l₁ <+: l₂
  | [], l => by simp [IsPrefix]
  | _ :: _, [] => by simp [IsPrefix]
  | x :: xs, y :: ys => by simp [IsPrefix, isPrefix_iff xs ys, List.cons_prefix_cons]

/-! ## The file system's head-key clause (LPS `Fs.v:151`) -/

namespace Fs

/-- LPS `Fs.v:151` `fs_lt_head`. -/
def ltHead (a : Path) : FileSystem → Bool
  | [] => true
  | (q, _) :: _ => pathLtb a q

/-- LPS `Fs.v:157` `fs_sorted_cons`. -/
theorem sorted_cons (p : Path) (d : List Byte) (r : FileSystem) :
    sorted ((p, d) :: r) = (ltHead p r && sorted r) := by
  cases r with
  | nil => rfl
  | cons x r => obtain ⟨q, e⟩ := x; rfl

end Fs

/-! ## Steps and stars -/

section Steps

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {refused r₁ r₂ : RefusalFilter}

/-- Every step starts from a running configuration. -/
theorem SStep.halted_none {c : Config isa} {evs : List Event} {st : StepTo isa}
    (s : SStep segs spec refused c evs st) : c.model.halted = none := by
  cases s <;> assumption

/-- A stronger filter admits fewer steps. -/
theorem SStep.relax (h : ∀ i m e, r₁ i m e → r₂ i m e) {c : Config isa} {evs : List Event}
    {st : StepTo isa} (s : SStep segs spec r₂ c evs st) : SStep segs spec r₁ c evs st := by
  cases s with
  | instr a b c => exact .instr a b c
  | instrFault a b c => exact .instrFault a b c
  | instrUnmodeled a b c => exact .instrUnmodeled a b c
  | syscall a b c d e f => exact .syscall a b c (fun x => d (h _ _ _ x)) e f
  | syscallMaterializationFault a b c d e f =>
    exact .syscallMaterializationFault a b c (fun x => d (h _ _ _ x)) e f
  | exit a b c d e => exact .exit a b c d e
  | killed a b c d => exact .killed a b c d
  | syscallUnmodeled a b c => exact .syscallUnmodeled a b c

theorem Star.relax (h : ∀ i m e, r₁ i m e → r₂ i m e) {c c' : Config isa} {tr : List Event}
    (s : Star segs spec r₂ c tr c') : Star segs spec r₁ c tr c' := by
  induction s with
  | refl c => exact .refl c
  | step st _ ih => exact .step (st.relax h) ih

/-- LPS `Run.v:475` `star_one`. -/
theorem Star.one {c c' : Config isa} {evs : List Event}
    (s : SStep segs spec refused c evs (.next c')) : Star segs spec refused c evs c' := by
  simpa using Star.step s (.refl c')

/-- LPS `Run.v:482` `star_trans`. -/
theorem Star.trans {c₁ c₂ c₃ : Config isa} {t₁ t₂ : List Event}
    (h₁ : Star segs spec refused c₁ t₁ c₂) (h₂ : Star segs spec refused c₂ t₂ c₃) :
    Star segs spec refused c₁ (t₁ ++ t₂) c₃ := by
  revert h₂
  induction h₁ with
  | refl c => intro h₂; simpa using h₂
  | step s _ ih => intro h₂; rw [List.append_assoc]; exact .step s (ih h₂)

/-- LPS `Run.v:2140` `star_invariant`. -/
theorem Star.invariant (I : Config isa → Prop)
    (hstep : ∀ c evs c', I c → SStep segs spec refused c evs (.next c') → I c')
    {c₀ c : Config isa} {tr : List Event} (s : Star segs spec refused c₀ tr c) (h₀ : I c₀) :
    I c := by
  revert h₀
  induction s with
  | refl => exact id
  | step st _ ih => exact fun h => ih (hstep _ _ _ h st)

/-- A halted configuration reaches only itself. -/
theorem Star.from_halted {c c' : Config isa} {tr : List Event} (h : c.model.halted ≠ none)
    (s : Star segs spec refused c tr c') : c' = c ∧ tr = [] := by
  cases s with
  | refl => exact ⟨rfl, rfl⟩
  | step st _ => exact absurd st.halted_none h

end Steps

/-! ## Observations (LPS `Run.v:496-950`) -/

section Observations

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter}

/-- LPS `Run.v:499` `obs_trace_nil`. -/
theorem obsTrace_nil (c₀ : Config isa) : ObsTrace segs spec refused c₀ [] :=
  ⟨[], c₀, .refl c₀, List.nil_prefix⟩

/-- LPS `Run.v:504` `obs_trace_prefix_closed`. -/
theorem obsTrace_prefix_closed {c₀ : Config isa} {tr tr' : List Event}
    (h : ObsTrace segs spec refused c₀ tr) (p : tr' <+: tr) : ObsTrace segs spec refused c₀ tr' :=
  let ⟨t, c, s, q⟩ := h
  ⟨t, c, s, p.trans q⟩

/-- LPS `Run.v:821` `unmodeled_at_sstep_error`. -/
theorem unmodeledAt_sstep_error {c : Config isa} (h : UnmodeledAt segs spec c) :
    ∃ evs, SStep segs spec refused c evs .error := by
  cases c with
  | mk ms model =>
    obtain ⟨hh, ⟨hsvc, hstep⟩ | ⟨x8, hsvc, hspec⟩⟩ := h
    · exact ⟨[], .instrUnmodeled hh hsvc hstep⟩
    · exact ⟨[], .syscallUnmodeled hh hsvc hspec⟩

/-- LPS `Run.v:829` `reaches_unmodeled_reaches_error`. -/
theorem reachesUnmodeled_reachesError {c₀ : Config isa}
    (h : ReachesUnmodeled segs spec refused c₀) : ReachesError segs spec refused c₀ := by
  obtain ⟨tr, c, s, u⟩ := h
  obtain ⟨evs, e⟩ := unmodeledAt_sstep_error (refused := refused) u
  exact ⟨tr, c, evs, s, e⟩

/-- LPS `Run.v:837` `no_error_no_unmodeled`. -/
theorem no_error_no_unmodeled {c₀ : Config isa} (h : ¬ ReachesError segs spec refused c₀) :
    ¬ ReachesUnmodeled segs spec refused c₀ :=
  fun u => h (reachesUnmodeled_reachesError u)

/-- LPS `Run.v:889` `all_traces_error_reaches_error`. -/
theorem allTracesError_reachesError {c : Config isa} (h : AllTracesError segs spec refused c) :
    ReachesError segs spec refused c := by
  induction h with
  | intro prog _ ih =>
    obtain ⟨evs, st, s⟩ := prog
    cases st with
    | next c' =>
      obtain ⟨tr, d, e, st', err⟩ := ih evs c' s
      exact ⟨evs ++ tr, d, e, .step s st', err⟩
    | error => exact ⟨[], _, evs, .refl _, s⟩

/-- Universal error is preserved by any filter change that preserves the steps. -/
theorem AllTracesError.congr {r₁ r₂ : RefusalFilter}
    (h : ∀ {c : Config isa} {evs st}, SStep segs spec r₁ c evs st ↔ SStep segs spec r₂ c evs st)
    {c : Config isa} (a : AllTracesError segs spec r₁ c) : AllTracesError segs spec r₂ c := by
  induction a with
  | intro prog _ ih =>
    obtain ⟨evs, st, s⟩ := prog
    exact .intro ⟨evs, st, h.1 s⟩ fun evs c' s' => ih evs c' (h.2 s')

end Observations

/-! ## The abort path's frame (LPS `Run.v:570-685`) -/

/-- LPS `Run.v:570` `decl_off_frame`: with the declaration and the pending bit clear, no arm
sets either, records a kill or emits a kill event. A named hypothesis in LPS too. -/
def DeclOffFrame (spec : Sys SyscallEffect) : Prop :=
  ∀ i m eff m' evs, spec i m (.ok eff m' evs) → m.abortTerminal = false →
    m.sigabrtPending = false →
    m'.abortTerminal = false ∧ m'.sigabrtPending = false ∧ m'.killedBy = none ∧
      ∀ sig fs, Event.killEv sig fs ∉ evs

/-- LPS `Run.v:587` `decl_off_frame_one_sided`: the form LPS refutes
(`Checks.Cases.Kernel.Signal.decl_off_frame_one_sided_refuted`). Nothing may consume it. -/
def DeclOffFrameOneSided (spec : Sys SyscallEffect) : Prop :=
  ∀ i m eff m' evs, spec i m (.ok eff m' evs) → m.abortTerminal = false →
    m'.abortTerminal = false ∧ m'.killedBy = none ∧ ∀ sig fs, Event.killEv sig fs ∉ evs

/-- Materializing accesses changes only the backing ledgers. -/
theorem materializeModelAccesses_proc {m m' : Model} {acc : List (Word × Nat)}
    (h : materializeModelAccesses m acc = some m') : m'.proc = m.proc := by
  unfold materializeModelAccesses at h
  cases hm : materializeAccesses m.vmLazy m.vmMaterialized (vmBackingUsed m) m.vmmaps.limit acc with
  | none => simp [hm] at h
  | some pages => simp [hm] at h; subst h; rfl

/-- LPS `State.v:4681` `materialize_model_accesses_no_lazy`, at the empty access list. -/
theorem materializeModelAccesses_nil (m : Model) : materializeModelAccesses m [] = some m := by
  simp [materializeModelAccesses, materializeAccesses, newlyMaterializedPages, accessesPages]
  rfl

section Frame

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter}

/-- LPS `Run.v:347` `mi_account_step_model_frame` (the process part). -/
theorem accountStep_proc {ms ms' : isa.State} {model model' : Model}
    (h : accountStep isa segs ms model = .ok (ms', model')) : model'.proc = model.proc := by
  unfold accountStep at h
  by_cases g : (!isa.reportsAccesses && !model.vmLazy.isEmpty) = true
  · simp only [g, ↓reduceIte] at h; cases h
  · simp only [g] at h
    cases hs : isa.step segs ms with
    | ok r =>
      rw [hs] at h
      cases hm : materializeModelAccesses model r.accessed with
      | none => simp [hm] at h
      | some m₁ =>
        simp [hm] at h
        obtain ⟨-, rfl⟩ := h
        exact materializeModelAccesses_proc hm
    | fault => rw [hs] at h; cases h
    | unmodeled => rw [hs] at h; cases h

/-- LPS `Run.v:608` `sstep_off_no_kill`. -/
theorem SStep.off_noKill (hframe : DeclOffFrame spec) {c c' : Config isa} {evs : List Event}
    (hoff : c.model.abortTerminal = false) (hpend : c.model.sigabrtPending = false)
    (s : SStep segs spec refused c evs (.next c')) :
    c'.model.abortTerminal = false ∧ c'.model.sigabrtPending = false ∧
      ∀ sig fs, Event.killEv sig fs ∉ evs := by
  cases s with
  | instr _ _ hacc =>
    have hp := accountStep_proc hacc
    refine ⟨?_, ?_, fun _ _ h => by simp at h⟩
    · show _ = false; simp only [Model.abortTerminal, hp]; exact hoff
    · show _ = false; simp only [Model.sigabrtPending, hp]; exact hpend
  | syscall _ _ hspec _ _ hmat =>
    obtain ⟨hoff', hpend', -, hev⟩ := hframe _ _ _ _ _ hspec hoff hpend
    have hp := materializeModelAccesses_proc hmat
    refine ⟨?_, ?_, hev⟩
    · show _ = false; simp only [Model.abortTerminal, hp]; exact hoff'
    · show _ = false; simp only [Model.sigabrtPending, hp]; exact hpend'
  | exit _ _ hspec _ _ =>
    obtain ⟨hoff', hpend', -, hev⟩ := hframe _ _ _ _ _ hspec hoff hpend
    refine ⟨hoff', hpend', fun sig fs h => ?_⟩
    rcases List.mem_append.1 h with h | h
    · exact hev _ _ h
    · simp at h
  | killed _ _ hspec hk =>
    obtain ⟨-, -, hk', -⟩ := hframe _ _ _ _ _ hspec hoff hpend
    rw [hk'] at hk
    cases hk

/-- LPS `Run.v:660` `star_off_no_kill`: with the abort declaration off, no execution records a
kill. -/
theorem Star.off_noKill (hframe : DeclOffFrame spec) {c c' : Config isa} {tr : List Event}
    (hoff : c.model.abortTerminal = false) (hpend : c.model.sigabrtPending = false)
    (s : Star segs spec refused c tr c') : ∀ sig fs, Event.killEv sig fs ∉ tr := by
  revert hoff hpend
  induction s with
  | refl => intro _ _ _ _ h; simp at h
  | step st _ ih =>
    intro hoff hpend sig fs h
    obtain ⟨h₁, h₂, h₃⟩ := st.off_noKill hframe hoff hpend
    rcases List.mem_append.1 h with h | h
    · exact h₃ _ _ h
    · exact ih h₁ h₂ sig fs h

end Frame

/-! ## The configured relations (LPS `Run.v:1618-1814`) -/

section Cfg

variable {isa : UserIsa}

/-- LPS `Run.v:1618` `sstep_cfg`. -/
abbrev SStepCfg (segs : List Segment) (spec : Sys SyscallEffect) (cfg : SpuriousCfg) :
    Config isa → List Event → StepTo isa → Prop :=
  SStep segs spec (spuriousRefusalCfg spec cfg)

/-- LPS `Run.v:1779` `star_cfg`. -/
abbrev StarCfg (segs : List Segment) (spec : Sys SyscallEffect) (cfg : SpuriousCfg) :
    Config isa → List Event → Config isa → Prop :=
  Star segs spec (spuriousRefusalCfg spec cfg)

/-- LPS `Run.v:1802` `obs_trace_cfg`. -/
abbrev ObsTraceCfg (segs : List Segment) (spec : Sys SyscallEffect) (cfg : SpuriousCfg) :
    Config isa → List Event → Prop :=
  ObsTrace segs spec (spuriousRefusalCfg spec cfg)

/-- LPS `Run.v:1805` `reaches_error_cfg`. -/
abbrev ReachesErrorCfg (segs : List Segment) (spec : Sys SyscallEffect) (cfg : SpuriousCfg) :
    Config isa → Prop :=
  ReachesError segs spec (spuriousRefusalCfg spec cfg)

/-- LPS `Run.v:1808` `all_traces_error_cfg`. -/
abbrev AllTracesErrorCfg (segs : List Segment) (spec : Sys SyscallEffect) (cfg : SpuriousCfg) :
    Config isa → Prop :=
  AllTracesError segs spec (spuriousRefusalCfg spec cfg)

/-- LPS `Run.v:1814` `reaches_unmodeled_cfg`. -/
abbrev ReachesUnmodeledCfg (segs : List Segment) (spec : Sys SyscallEffect) (cfg : SpuriousCfg) :
    Config isa → Prop :=
  ReachesUnmodeled segs spec (spuriousRefusalCfg spec cfg)

variable {segs : List Segment} {spec : Sys SyscallEffect}

/-- LPS `Run.v:1334` `cfg_le_refl`. -/
theorem cfgLe_refl (cfg : SpuriousCfg) : cfgLe cfg cfg := fun _ h => h

/-- LPS `Run.v:1337` `forced_only_cfg_least`. -/
theorem forcedOnlyCfg_least (cfg : SpuriousCfg) : cfgLe forcedOnlyCfg cfg := by
  intro f h; cases f <;> cases h

/-- LPS `Run.v:1340` `may_fail_cfg_greatest`. -/
theorem mayFailCfg_greatest (cfg : SpuriousCfg) : cfgLe cfg mayFailCfg := by
  intro f _; cases f <;> rfl

/-- LPS `Run.v:1574` `spurious_refusal_may_fail`. -/
theorem spuriousRefusal_mayFail (i : SyscallInput) (m : Model) (eff : SyscallEffect) :
    ¬ spuriousRefusalCfg spec mayFailCfg i m eff := fun ⟨h, _, _⟩ => by
  rw [injectedFamilyOff_mayFail] at h; cases h

/-- LPS `Run.v:1582` `spurious_refusal_not_refusal`. -/
theorem spuriousRefusal_not_refusal (cfg : SpuriousCfg) {i : SyscallInput} {m : Model}
    {eff : SyscallEffect} (h : refusalB i m eff.ret = false) :
    ¬ spuriousRefusalCfg spec cfg i m eff := fun ⟨_, hr, _⟩ => by rw [h] at hr; cases hr

/-- LPS `Run.v:1590` `spurious_refusal_family_on`. -/
theorem spuriousRefusal_family_on (cfg : SpuriousCfg) {i : SyscallInput} {m : Model}
    {eff : SyscallEffect} (h : injectedFamilyOff cfg i = false) :
    ¬ spuriousRefusalCfg spec cfg i m eff := fun ⟨hoff, _, _⟩ => by rw [h] at hoff; cases hoff

/-- LPS `Run.v:1598` `spurious_refusal_mono`. -/
theorem spuriousRefusal_mono {cfg₁ cfg₂ : SpuriousCfg} (hle : cfgLe cfg₁ cfg₂)
    {i : SyscallInput} {m : Model} {eff : SyscallEffect}
    (h : spuriousRefusalCfg spec cfg₂ i m eff) : spuriousRefusalCfg spec cfg₁ i m eff := by
  obtain ⟨hoff, hr, hex⟩ := h
  refine ⟨?_, hr, hex⟩
  unfold injectedFamilyOff at hoff ⊢
  cases ha : injectedArm i.sysno.toNat with
  | none => rw [ha] at hoff; cases hoff
  | some a =>
    rw [ha] at hoff
    cases h₁ : familyMayFail cfg₁ a.family with
    | false => simp [h₁]
    | true => simp [hle _ h₁] at hoff

/-- LPS `Run.v:1674` `sstep_cfg_sub`: a filtered step is a step. -/
theorem SStepCfg.sub {cfg : SpuriousCfg} {c : Config isa} {evs : List Event} {st : StepTo isa}
    (s : SStepCfg segs spec cfg c evs st) : SStep segs spec noFilter c evs st :=
  s.relax fun _ _ _ h => h.elim

/-- LPS `Run.v:1685` `sstep_cfg_may_fail`. -/
theorem sstepCfg_mayFail {c : Config isa} {evs : List Event} {st : StepTo isa} :
    SStep segs spec noFilter c evs st ↔ SStepCfg segs spec mayFailCfg c evs st :=
  ⟨SStep.relax fun i m e h => (spuriousRefusal_mayFail i m e h).elim, SStepCfg.sub⟩

/-- LPS `Run.v:1701` `sstep_cfg_mono`. -/
theorem SStepCfg.mono {cfg₁ cfg₂ : SpuriousCfg} (hle : cfgLe cfg₁ cfg₂) {c : Config isa}
    {evs : List Event} {st : StepTo isa} (s : SStepCfg segs spec cfg₁ c evs st) :
    SStepCfg segs spec cfg₂ c evs st :=
  s.relax fun _ _ _ h => spuriousRefusal_mono hle h

/-- The syscall case of progress: an outcome of the spec yields a filtered step. -/
theorem progress_syscall (cfg : SpuriousCfg) {ms : isa.State} {model : Model} {x8 : Word}
    {eff : SyscallEffect} {model' : Model} {evs : List Event}
    (hdec : RefusalDecided spec cfg (sysInput isa segs ms x8) model)
    (hh : model.halted = none) (hsvc : isa.svcPending ms = some x8)
    (hspec : spec (sysInput isa segs ms x8) model (.ok eff model' evs)) :
    ∃ evs' st', SStepCfg segs spec cfg ⟨ms, model⟩ evs' st' := by
  have stepWith : ∀ {eff' : SyscallEffect} {m' : Model} {evs' : List Event},
      spec (sysInput isa segs ms x8) model (.ok eff' m' evs') →
      ¬ spuriousRefusalCfg spec cfg (sysInput isa segs ms x8) model eff' →
      ∃ evs'' st', SStepCfg segs spec cfg ⟨ms, model⟩ evs'' st' := by
    intro eff' m' evs' hs hns
    cases hh₂ : m'.halted with
    | some code =>
      cases hk : m'.killedBy with
      | some sig => exact ⟨_, _, .killed hh hsvc hs hk⟩
      | none => exact ⟨_, _, .exit hh hsvc hs hh₂ hk⟩
    | none =>
      cases hm : materializeModelAccesses m' (syscallEffectAccesses eff') with
      | some m'' => exact ⟨_, _, .syscall hh hsvc hs hns hh₂ hm⟩
      | none => exact ⟨_, _, .syscallMaterializationFault hh hsvc hs hns hh₂ hm⟩
  by_cases hoff : injectedFamilyOff cfg (sysInput isa segs ms x8) = true
  · rcases hdec hoff with ⟨eff', m', evs', hs', hnr⟩ | hall
    · exact stepWith hs' (spuriousRefusal_not_refusal cfg hnr)
    · exact stepWith hspec fun ⟨_, _, eff', m', evs', hs', hnr⟩ => by
        rw [hall _ _ _ hs'] at hnr; cases hnr
  · exact stepWith hspec fun ⟨h, _⟩ => hoff h

/-- LPS `Run.v:1721` `sstep_cfg_progress`: **progress**. Where the filter's question is
decided at every pending syscall, a configuration with a step has a filtered step; so the
forced-only readings never get stuck where the may-fail reading moves. -/
theorem sstepCfg_progress (cfg : SpuriousCfg) {ms : isa.State} {model : Model}
    {evs : List Event} {st : StepTo isa}
    (hdec : ∀ x8, isa.svcPending ms = some x8 →
      RefusalDecided spec cfg (sysInput isa segs ms x8) model)
    (s : SStep segs spec noFilter ⟨ms, model⟩ evs st) :
    ∃ evs' st', SStepCfg segs spec cfg ⟨ms, model⟩ evs' st' := by
  cases s with
  | instr a b c => exact ⟨_, _, .instr a b c⟩
  | instrFault a b c => exact ⟨_, _, .instrFault a b c⟩
  | instrUnmodeled a b c => exact ⟨_, _, .instrUnmodeled a b c⟩
  | syscall hh hsvc hspec _ _ _ => exact progress_syscall cfg (hdec _ hsvc) hh hsvc hspec
  | syscallMaterializationFault hh hsvc hspec _ _ _ =>
    exact progress_syscall cfg (hdec _ hsvc) hh hsvc hspec
  | exit a b c d e => exact ⟨_, _, .exit a b c d e⟩
  | killed a b c d => exact ⟨_, _, .killed a b c d⟩
  | syscallUnmodeled a b c => exact ⟨_, _, .syscallUnmodeled a b c⟩

/-- LPS `Run.v:1786` `star_cfg_sub`. -/
theorem StarCfg.sub {cfg : SpuriousCfg} {c c' : Config isa} {tr : List Event}
    (s : StarCfg segs spec cfg c tr c') : Star segs spec noFilter c tr c' :=
  s.relax fun _ _ _ h => h.elim

/-- LPS `Run.v:1793` `star_cfg_may_fail`. -/
theorem starCfg_mayFail {c c' : Config isa} {tr : List Event} :
    Star segs spec noFilter c tr c' ↔ StarCfg segs spec mayFailCfg c tr c' :=
  ⟨Star.relax fun i m e h => (spuriousRefusal_mayFail i m e h).elim, StarCfg.sub⟩

/-- LPS `Run.v:1824` `obs_trace_cfg_sub`. -/
theorem ObsTraceCfg.sub {cfg : SpuriousCfg} {c₀ : Config isa} {tr : List Event}
    (h : ObsTraceCfg segs spec cfg c₀ tr) : ObsTrace segs spec noFilter c₀ tr :=
  let ⟨t, c, s, p⟩ := h
  ⟨t, c, StarCfg.sub s, p⟩

/-- LPS `Run.v:1830` `reaches_error_cfg_sub`. -/
theorem ReachesErrorCfg.sub {cfg : SpuriousCfg} {c₀ : Config isa}
    (h : ReachesErrorCfg segs spec cfg c₀) : ReachesError segs spec noFilter c₀ :=
  let ⟨t, c, evs, s, e⟩ := h
  ⟨t, c, evs, StarCfg.sub s, SStepCfg.sub e⟩

/-- LPS `Run.v:1837` `reaches_unmodeled_cfg_sub`. -/
theorem ReachesUnmodeledCfg.sub {cfg : SpuriousCfg} {c₀ : Config isa}
    (h : ReachesUnmodeledCfg segs spec cfg c₀) : ReachesUnmodeled segs spec noFilter c₀ :=
  let ⟨t, c, s, u⟩ := h
  ⟨t, c, StarCfg.sub s, u⟩

/-- LPS `Run.v:1846-1880`: at `mayFailCfg` each observation is the unfiltered one. -/
theorem runWith_mayFail (spec : Sys SyscallEffect) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    BehaviorEquiv (runWith isa spec (spuriousRefusalCfg spec mayFailCfg) img lim en inp)
      (runWith isa spec noFilter img lim en inp) := by
  refine ⟨fun tr => ⟨fun ⟨t, c, s, p⟩ => ⟨t, c, StarCfg.sub s, p⟩,
      fun ⟨t, c, s, p⟩ => ⟨t, c, starCfg_mayFail.1 s, p⟩⟩,
    ⟨fun ⟨t, c, evs, s, e⟩ => ⟨t, c, evs, StarCfg.sub s, SStepCfg.sub e⟩,
      fun ⟨t, c, evs, s, e⟩ => ⟨t, c, evs, starCfg_mayFail.1 s, sstepCfg_mayFail.1 e⟩⟩,
    ⟨AllTracesError.congr sstepCfg_mayFail.symm, AllTracesError.congr sstepCfg_mayFail⟩,
    ⟨fun ⟨t, c, s, u⟩ => ⟨t, c, StarCfg.sub s, u⟩,
      fun ⟨t, c, s, u⟩ => ⟨t, c, starCfg_mayFail.1 s, u⟩⟩⟩

/-- LPS `Run.v:1947` `run_scfg_may_fail`, in LPS's form (`behavior_equiv`). `Equivalence`
proves the stronger equality `runScfg_mayFail`. -/
theorem runScfg_mayFail_behaviorEquiv (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    BehaviorEquiv (runScfg isa mayFailCfg img lim en inp) (run isa img lim en inp) :=
  runWith_mayFail syscallSpec img lim en inp

end Cfg

/-! ## Budgets (LPS `Run.v:1449-1531`, `Run.v:2100-2257`) -/

/-- LPS `Run.v:1449` `alloc_mark_sysnos`. -/
def allocMarkSysnos : List Nat := [214, 216, 222, 226]

/-- LPS `Run.v:1386` `lookup_injected`. -/
def lookupInjected : List InjectedArm → Nat → Option InjectedArm
  | [], _ => none
  | a :: r, n => if a.no = n then some a else lookupInjected r n

theorem find?_eq_lookupInjected (t : List InjectedArm) (n : Nat) :
    t.find? (·.no = n) = lookupInjected t n := by
  induction t with
  | nil => rfl
  | cons a r ih => by_cases h : a.no = n <;> simp [lookupInjected, h, ih]

/-- `injected_arm` is `lookup_injected injected_table` (LPS `Run.v:1394`). -/
theorem injectedArm_eq (no : Nat) : injectedArm no = lookupInjected injectedTable no :=
  find?_eq_lookupInjected _ _

/-- LPS `Run.v:1482` `alloc_family_dispatched`: every allocation-family arm is dispatched. -/
theorem allocFamily_dispatched {no : Nat} {a : InjectedArm} (h : injectedArm no = some a)
    (hf : a.family = .alloc) : no ∈ allocMarkSysnos := by
  have hmem := List.mem_of_find?_eq_some h
  have hno : a.no = no := by simpa using List.find?_some h
  have key : ∀ b ∈ injectedTable, b.family = .alloc → b.no ∈ allocMarkSysnos := by decide
  exact hno ▸ key a hmem hf

/-- LPS `Run.v:1516` `alloc_budget_refused_b_outside`: off the list the dispatcher is
`false`. -/
theorem allocBudgetRefusedB_outside (i : SyscallInput) (m : Model)
    (h : i.sysno.toNat ∉ allocMarkSysnos) : allocBudgetRefusedB i m = false := by
  simp only [allocMarkSysnos, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [allocBudgetRefusedB, h.1, h.2.1, h.2.2.1, h.2.2.2]

section Budget

variable {isa : UserIsa} (segs : List Segment) (spec : Sys SyscallEffect)
  (refused : RefusalFilter)

/-- LPS `Run.v:2100` `reaches_budget_refused` (and `Run.v:2222` `reaches_budget_refused_cfg`
with the configured filter). The mark reads the unfiltered spec in both, as in LPS. -/
def ReachesBudgetRefused (c₀ : Config isa) : Prop :=
  ∃ tr c, Star segs spec refused c₀ tr c ∧ BudgetRefusedAt isa segs spec c

/-- LPS `Run.v:2222` `reaches_budget_refused_cfg`. -/
abbrev ReachesBudgetRefusedCfg (cfg : SpuriousCfg) (c₀ : Config isa) : Prop :=
  ReachesBudgetRefused segs spec (spuriousRefusalCfg spec cfg) c₀

variable {segs spec refused}

theorem runBudgetRefusedWith_iff {img : Image} {lim : Int} {en : ExecEntry} {inp : ProcInput} :
    RunBudgetRefusedWith isa spec refused img lim en inp ↔
      ReachesBudgetRefused img.segments spec refused (initConfig isa img en lim inp) :=
  Iff.rfl

/-- LPS `Run.v:2103` `reaches_budget_refused_intro`. -/
theorem reachesBudgetRefused_intro {c : Config isa} (h : BudgetRefusedAt isa segs spec c) :
    ReachesBudgetRefused segs spec refused c :=
  ⟨[], c, .refl c, h⟩

/-- LPS `Run.v:2107` `reaches_budget_refused_star`. -/
theorem reachesBudgetRefused_star {c₀ c : Config isa} {tr : List Event}
    (s : Star segs spec refused c₀ tr c) (h : ReachesBudgetRefused segs spec refused c) :
    ReachesBudgetRefused segs spec refused c₀ :=
  let ⟨tr', c', s', b⟩ := h
  ⟨tr ++ tr', c', s.trans s', b⟩

/-- LPS `Run.v:2115` `budget_fault_instr_sstep_error`: an instruction refused at first touch
takes the error transition (`instrFault`, or `instrUnmodeled` on a machine that does not
report its accesses). -/
theorem budgetFault_instr_sstep_error {ms : isa.State} {model : Model}
    {report : AccessReport isa.State} (hh : model.halted = none)
    (hsvc : isa.svcPending ms = none) (hstep : isa.step segs ms = .ok report)
    (hmat : materializeModelAccesses model report.accessed = none) :
    ∃ evs, SStep segs spec refused ⟨ms, model⟩ evs .error := by
  by_cases g : (!isa.reportsAccesses && !model.vmLazy.isEmpty) = true
  · exact ⟨[], .instrUnmodeled hh hsvc (by unfold accountStep; simp only [g, ↓reduceIte])⟩
  · exact ⟨[], .instrFault hh hsvc (by
      unfold accountStep; simp only [g, hstep]; simp [hmat])⟩

/-- LPS `Run.v:2149` `never_budget_refused_ind`. -/
theorem never_budget_refused_ind (I : Config isa → Prop) {c₀ : Config isa} (h₀ : I c₀)
    (hstep : ∀ c evs c', I c → SStep segs spec refused c evs (.next c') → I c')
    (hno : ∀ c, I c → ¬ BudgetRefusedAt isa segs spec c) :
    ¬ ReachesBudgetRefused segs spec refused c₀ :=
  fun ⟨_, c, s, b⟩ => hno c (s.invariant I hstep h₀) b

/-- LPS `Run.v:2225` `reaches_budget_refused_cfg_sub`. -/
theorem ReachesBudgetRefusedCfg.sub {cfg : SpuriousCfg} {c₀ : Config isa}
    (h : ReachesBudgetRefusedCfg segs spec cfg c₀) : ReachesBudgetRefused segs spec noFilter c₀ :=
  let ⟨tr, c, s, b⟩ := h
  ⟨tr, c, StarCfg.sub s, b⟩

end Budget

/-! ## Entry stack bounds (LPS `Run.v:2551-2600`) -/

/-- LPS `Run.v:2551` `entry_stack_fits`: the Sv48 form of `entry_stack_fits_va`. -/
def EntryStackFits (sp : Word) (argv envp : List (List Byte)) : Prop :=
  uns sp + entryStackSpan argv envp ≤ spWindowHi

/-- LPS `Run.v:2590` `entry_stack_span_bound`, both halves: `Equivalence.entryStackSpan_bound`
under the name the run audit uses. -/
theorem entryStackSpan_bound_max {argv envp : List (List Byte)} (ha : ValidArgv argv)
    (he : ValidEnvp envp) :
    0 ≤ entryStackSpan argv envp ∧ entryStackSpan argv envp ≤ entryStackSpanMax :=
  entryStackSpan_bound ha he

end Silmaril.Process.LPS
