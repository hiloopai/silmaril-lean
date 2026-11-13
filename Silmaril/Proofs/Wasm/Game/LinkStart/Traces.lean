module

public import Silmaril.Proofs.Wasm.Game.Start.Main
public import Silmaril.Proofs.Wasm.Game.GamesAux.Inst
public import Silmaril.Proofs.Wasm.Game.Linking.Split.GameSub
public import Silmaril.Wasm.Game.LinkStart.Defs

/-!
# Traces of the instantiable systems of a link

For every profile `P`, the traces of the three instantiable systems that M3 with start
functions compares, read in Core terms:

* the instantiable system of an instance with one start function, `I.instSys P s start`
  (the provider): ready after a host-free run of its start thread to `values []`
  (`StartsReach`), failing after one to a trap or exception (`StartFails`), then the plays of
  `I.strategy P s'` (`instSys_ready_traces`, from the export bisimulation `exportB`);
* the instantiable system with a start sequence, `I.instSysSeq P s starts` (the linked
  module): ready after the start functions all returned in order (`SeqDone`), failing after
  some returned and the next failed (`SeqFail`); for the sequence `o₁.toList ++ o₂.toList`
  these are `StartsReach`/`StartFails` of `o₁`, then of `o₂` (`seqDone_pair_iff`,
  `seqFail_pair_iff`); then the plays at the store left (`instSysSeq_ready_traces`);
* the consumer system of a link, `(I.instSys P s start).consumerLTS`: its instantiation runs
  along import calls are the runs `LRun` of the joint machine (`irun_iff_lrun`), and after
  instantiation it plays the plays of `I.strategy P s'`, lower and upper moves lifted
  (`exportBc`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStart

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux
  Silmaril.Proofs.Wasm.Game.Start Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable {I : ScalarInstance} {P : Profile}

/-! ## Start phases in Core -/

/-- The start thread `startThread o` runs host-free from `s` to `values []` at `s'`. -/
def StartsReach (P : Profile) (s : Store Nat) (o : Option Nat) (s' : Store Nat) : Prop :=
  ∃ t', Reach P (s, startThread o) (s', t') ∧ ResultAt s' t' (.values [])

/-- The start thread `startThread o` runs host-free from `s` to a trap or exception `b`. -/
def StartFails (P : Profile) (s : Store Nat) (o : Option Nat) (b : Behaviour Val) : Prop :=
  ∃ c, Reach P (s, startThread o) c ∧ StartFailed c b

/-- The finished empty thread has no step. -/
theorem reach_finished {s : Store Nat} {y : Store Nat × Thread}
    (h : Reach P (s, .active {} []) y) : y = (s, .active {} []) :=
  (Silmaril.Proofs.Wasm.Game.Linking.Split.reach_eq_of_normal h
    (resultAt_no_internal (r := .values []) rfl)).symm

theorem startsReach_none {s s' : Store Nat} : StartsReach P s none s' ↔ s' = s := by
  constructor
  · rintro ⟨t', h, -⟩
    exact (Prod.mk.inj (reach_finished h)).1
  · rintro rfl
    exact ⟨_, .refl, rfl⟩

theorem not_startFails_none {s : Store Nat} {b : Behaviour Val} : ¬ StartFails P s none b := by
  rintro ⟨c, h, hf⟩
  rw [reach_finished h] at hf
  rcases hf with ⟨h, -⟩ | ⟨a, h, -⟩ <;> cases h

/-! ## Closed instantiable systems -/

theorem instSys_no_icall (hI : I.imports = []) {s : Store Nat} {start : Option Nat} :
    ∀ c m k, ¬ (I.instSys P s start).icall c m k := by
  intro c m k
  have hl : I.imports.length = 0 := by rw [hI]; rfl
  have hm : m.1.val < I.imports.length := m.1.2
  exact absurd hm (by omega)

theorem instSysSeq_no_icall (hI : I.imports = []) {s : Store Nat} {starts : List Nat} :
    ∀ c m k, ¬ (I.instSysSeq P s starts).icall c m k := by
  intro c m k
  have hl : I.imports.length = 0 := by rw [hI]; rfl
  have hm : m.1.val < I.imports.length := m.1.2
  exact absurd hm (by omega)

/-- Runs of the export phase are runs of the instance system, relabelled. -/
theorem instSys_export_run {s₀ s' : Store Nat} {start : Option Nat}
    {w : List (Move I.E (I.F.withInst (Behaviour Val)))} {z : (I.instSys P s₀ start).St}
    (h : (I.instSys P s₀ start).toLTS.Run (.ready s') w z) :
    ∃ q, w = q.map liftMove ∧ q ∈ I.plays P s' := by
  obtain ⟨q, y, rfl, -, hr⟩ := (exportB I P s₀ s' start).run_bwd (x := .idle s') h
  exact ⟨q, rfl, (ScalarInstance.traces_dlts P s') ▸ ⟨y, hr⟩⟩

theorem instSys_export_run_of {s₀ s' : Store Nat} {start : Option Nat}
    {q : List (Move I.E I.F)} (hq : q ∈ I.plays P s') :
    ∃ z, (I.instSys P s₀ start).toLTS.Run (.ready s') (q.map liftMove) z := by
  rw [← ScalarInstance.traces_dlts P s'] at hq
  obtain ⟨y, hy⟩ := hq
  exact ⟨_, (exportB I P s₀ s' start).run_fwd hy⟩

/-- **Ready traces of an instantiable instance**: a start phase returning at `s'`, then the
plays of the instance from `s'`. -/
theorem instSys_ready_traces {s : Store Nat} {start : Option Nat}
    {w : List (Move I.E (I.F.withInst (Behaviour Val)))} :
    [askInst, ansInst .ready] ++ w ∈ (I.instSys P s start).toLTS.Traces ↔
      ∃ s', StartsReach P s start s' ∧ ∃ q, w = q.map liftMove ∧ q ∈ I.plays P s' := by
  rw [InstSystem.toLTS_ready_iff]
  constructor
  · rintro ⟨c, st, z, hc, ⟨hres, rfl⟩, hrun⟩
    exact ⟨c.1, ⟨c.2, hc, hres⟩, instSys_export_run hrun⟩
  · rintro ⟨s', ⟨t', hc, hres⟩, q, rfl, hq⟩
    obtain ⟨z, hz⟩ := instSys_export_run_of (s₀ := s) (start := start) hq
    exact ⟨(s', t'), s', z, hc, ⟨hres, rfl⟩, hz⟩

/-- **Failing traces of an instantiable instance.** -/
theorem instSys_fail_traces {s : Store Nat} {start : Option Nat} {b : Behaviour Val}
    {w : List (Move I.E (I.F.withInst (Behaviour Val)))} :
    [askInst, ansInst (.fail b)] ++ w ∈ (I.instSys P s start).toLTS.Traces ↔
      StartFails P s start b ∧ w = [] := by
  rw [InstSystem.toLTS_fail_iff]
  exact Iff.rfl

/-! ## Start sequences -/

/-- The start sequence from `(s, t, rest)` returns at `s'`: the running thread returns
`values []`, then each start function of `rest` in turn. -/
inductive SeqDone (P : Profile) : SeqConf → Store Nat → Prop where
  /-- The last start function returns. -/
  | fin {s s' : Store Nat} {t t' : Thread} :
      Reach P (s, t) (s', t') → ResultAt s' t' (.values []) → SeqDone P (s, t, []) s'
  /-- The running start function returns; the next one runs. -/
  | next {s s₁ s' : Store Nat} {t t₁ : Thread} {a : Nat} {rest : List Nat} :
      Reach P (s, t) (s₁, t₁) → ResultAt s₁ t₁ (.values []) →
      SeqDone P (s₁, .pending a [], rest) s' → SeqDone P (s, t, a :: rest) s'

/-- The start sequence from `(s, t, rest)` fails with `b`. -/
inductive SeqFail (P : Profile) : SeqConf → Behaviour Val → Prop where
  /-- The running start function fails. -/
  | here {s : Store Nat} {t : Thread} {rest : List Nat} {c : Store Nat × Thread}
      {b : Behaviour Val} : Reach P (s, t) c → StartFailed c b → SeqFail P (s, t, rest) b
  /-- The running start function returns; a later one fails. -/
  | next {s s₁ : Store Nat} {t t₁ : Thread} {a : Nat} {rest : List Nat} {b : Behaviour Val} :
      Reach P (s, t) (s₁, t₁) → ResultAt s₁ t₁ (.values []) →
      SeqFail P (s₁, .pending a [], rest) b → SeqFail P (s, t, a :: rest) b

theorem seq_lift {s s' : Store Nat} {t t' : Thread} {rest : List Nat}
    (h : Reach P (s, t) (s', t')) :
    Relation.ReflTransGen (SeqStep P) (s, t, rest) (s', t', rest) := by
  generalize hx : (s, t) = x at h
  generalize hy : (s', t') = y at h
  induction h generalizing s' t' with
  | refl => subst hx; cases hy; exact .refl
  | @tail y₁ y₂ _ hst ih =>
    subst hy
    exact (ih (s' := y₁.1) (t' := y₁.2) rfl).tail (.run hst)

/-- The shape of a run of a start sequence. -/
theorem seq_inv {x c : SeqConf} (h : Relation.ReflTransGen (SeqStep P) x c) :
    (Reach P (x.1, x.2.1) (c.1, c.2.1) ∧ c.2.2 = x.2.2) ∨
      ∃ s₁ t₁ a rest', x.2.2 = a :: rest' ∧ Reach P (x.1, x.2.1) (s₁, t₁) ∧
        ResultAt s₁ t₁ (.values []) ∧ Relation.ReflTransGen (SeqStep P) (s₁, .pending a [], rest') c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl ⟨.refl, rfl⟩
  | @head x y hxy hyc ih =>
    cases hxy with
    | run hi =>
      rcases ih with ⟨hr, hc⟩ | ⟨s₁, t₁, a, rest', hrest, hr, hres, hc⟩
      · exact .inl ⟨.head hi hr, hc⟩
      · exact .inr ⟨s₁, t₁, a, rest', hrest, .head hi hr, hres, hc⟩
    | next hres => exact .inr ⟨_, _, _, _, rfl, .refl, hres, hyc⟩

theorem seqDone_of_rtg {x c : SeqConf} (hc : Relation.ReflTransGen (SeqStep P) x c)
    (hres : ResultAt c.1 c.2.1 (.values [])) (hnil : c.2.2 = []) : SeqDone P x c.1 := by
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨s, t, rest⟩ := c
    have hr : rest = [] := hnil
    rw [hr]
    exact .fin .refl hres
  | @head x y hxy hyc ih =>
    cases hxy with
    | run hi =>
      cases ih with
      | fin hr hres' => exact .fin (.head hi hr) hres'
      | next hr hres' hd => exact .next (.head hi hr) hres' hd
    | next hres' => exact .next .refl hres' ih

theorem rtg_of_seqDone {x : SeqConf} {s' : Store Nat} (h : SeqDone P x s') :
    ∃ c, Relation.ReflTransGen (SeqStep P) x c ∧ ResultAt c.1 c.2.1 (.values []) ∧
      c.2.2 = [] ∧ s' = c.1 := by
  induction h with
  | @fin s s' t t' hr hres => exact ⟨(s', t', []), seq_lift hr, hres, rfl, rfl⟩
  | next hr hres _ ih =>
    obtain ⟨c, hc, hres', hnil, hs⟩ := ih
    exact ⟨c, (seq_lift hr).trans (.head (.next hres) hc), hres', hnil, hs⟩

/-- **Ready runs of a start sequence.** -/
theorem seqDone_iff {x : SeqConf} {s' : Store Nat} :
    (∃ c, Relation.ReflTransGen (SeqStep P) x c ∧ ResultAt c.1 c.2.1 (.values []) ∧
      c.2.2 = [] ∧ s' = c.1) ↔ SeqDone P x s' := by
  constructor
  · rintro ⟨c, hc, hres, hnil, hs⟩
    rw [hs]
    exact seqDone_of_rtg hc hres hnil
  · exact rtg_of_seqDone

/-- **Failing runs of a start sequence.** -/
theorem seqFail_iff {x : SeqConf} {b : Behaviour Val} :
    (∃ c, Relation.ReflTransGen (SeqStep P) x c ∧ StartFailed (c.1, c.2.1) b) ↔
      SeqFail P x b := by
  constructor
  · rintro ⟨c, hc, hf⟩
    induction hc using Relation.ReflTransGen.head_induction_on with
    | refl => exact .here .refl hf
    | @head x y hxy hyc ih =>
      cases hxy with
      | run hi =>
        cases ih with
        | here hr hf' => exact .here (.head hi hr) hf'
        | next hr hres' hd => exact .next (.head hi hr) hres' hd
      | next hres' => exact .next .refl hres' ih
  · intro h
    induction h with
    | @here s t rest c b hr hf => exact ⟨(c.1, c.2, rest), seq_lift hr, hf⟩
    | next hr hres _ ih =>
      obtain ⟨c, hc, hf⟩ := ih
      exact ⟨c, (seq_lift hr).trans (.head (.next hres) hc), hf⟩

theorem seqDone_nil {s s' : Store Nat} {t : Thread} :
    SeqDone P (s, t, []) s' ↔ ∃ t', Reach P (s, t) (s', t') ∧ ResultAt s' t' (.values []) := by
  constructor
  · intro h
    cases h with
    | fin hr hres => exact ⟨_, hr, hres⟩
  · rintro ⟨t', hr, hres⟩
    exact .fin hr hres

theorem seqDone_cons {s s' : Store Nat} {t : Thread} {a : Nat} {rest : List Nat} :
    SeqDone P (s, t, a :: rest) s' ↔ ∃ s₁ t₁, Reach P (s, t) (s₁, t₁) ∧
      ResultAt s₁ t₁ (.values []) ∧ SeqDone P (s₁, .pending a [], rest) s' := by
  constructor
  · intro h
    cases h with
    | next hr hres hd => exact ⟨_, _, hr, hres, hd⟩
  · rintro ⟨s₁, t₁, hr, hres, hd⟩
    exact .next hr hres hd

theorem seqFail_nil {s : Store Nat} {t : Thread} {b : Behaviour Val} :
    SeqFail P (s, t, []) b ↔ ∃ c, Reach P (s, t) c ∧ StartFailed c b := by
  constructor
  · intro h
    cases h with
    | here hr hf => exact ⟨_, hr, hf⟩
  · rintro ⟨c, hr, hf⟩
    exact .here hr hf

theorem seqFail_cons {s : Store Nat} {t : Thread} {a : Nat} {rest : List Nat}
    {b : Behaviour Val} :
    SeqFail P (s, t, a :: rest) b ↔ (∃ c, Reach P (s, t) c ∧ StartFailed c b) ∨
      ∃ s₁ t₁, Reach P (s, t) (s₁, t₁) ∧ ResultAt s₁ t₁ (.values []) ∧
        SeqFail P (s₁, .pending a [], rest) b := by
  constructor
  · intro h
    cases h with
    | here hr hf => exact .inl ⟨_, hr, hf⟩
    | next hr hres hd => exact .inr ⟨_, _, hr, hres, hd⟩
  · rintro (⟨c, hr, hf⟩ | ⟨s₁, t₁, hr, hres, hd⟩)
    · exact .here hr hf
    · exact .next hr hres hd

/-- From the finished empty thread, the start sequence `a :: rest` is `rest` after `a`. -/
theorem seqDone_finished_cons {s s' : Store Nat} {a : Nat} {rest : List Nat} :
    SeqDone P (s, .active {} [], a :: rest) s' ↔ SeqDone P (s, .pending a [], rest) s' := by
  rw [seqDone_cons]
  constructor
  · rintro ⟨s₁, t₁, hr, -, hd⟩
    obtain ⟨rfl, -⟩ := Prod.mk.inj (reach_finished hr)
    exact hd
  · intro hd
    exact ⟨s, _, .refl, rfl, hd⟩

theorem seqFail_finished_cons {s : Store Nat} {a : Nat} {rest : List Nat} {b : Behaviour Val} :
    SeqFail P (s, .active {} [], a :: rest) b ↔ SeqFail P (s, .pending a [], rest) b := by
  rw [seqFail_cons]
  constructor
  · rintro (⟨c, hr, hf⟩ | ⟨s₁, t₁, hr, -, hd⟩)
    · rw [reach_finished hr] at hf
      rcases hf with ⟨h, -⟩ | ⟨x, h, -⟩ <;> cases h
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (reach_finished hr)
      exact hd
  · intro hd
    exact .inr ⟨s, _, .refl, rfl, hd⟩

theorem seqDone_finished_single {s s' : Store Nat} {a : Nat} {rest : List Nat} :
    SeqDone P (s, .pending a [], rest) s' ↔
      ∃ s₁, StartsReach P s (some a) s₁ ∧ SeqDone P (s₁, .active {} [], rest) s' := by
  cases rest with
  | nil =>
    rw [seqDone_nil]
    constructor
    · rintro ⟨t', hr, hres⟩
      exact ⟨s', ⟨t', hr, hres⟩, seqDone_nil.2 ⟨_, .refl, rfl⟩⟩
    · rintro ⟨s₁, ⟨t₁, hr, hres⟩, h⟩
      obtain ⟨t', hr', -⟩ := seqDone_nil.1 h
      have hs : s' = s₁ := (Prod.mk.inj (reach_finished hr')).1
      exact ⟨t₁, hs ▸ hr, hs ▸ hres⟩
  | cons b rest =>
    rw [seqDone_cons]
    constructor
    · rintro ⟨s₁, t₁, hr, hres, hd⟩
      exact ⟨s₁, ⟨t₁, hr, hres⟩, seqDone_finished_cons.2 hd⟩
    · rintro ⟨s₁, ⟨t₁, hr, hres⟩, h⟩
      exact ⟨s₁, t₁, hr, hres, seqDone_finished_cons.1 h⟩

/-- A single optional start function from the finished empty thread. -/
theorem seqDone_single {s s' : Store Nat} {o : Option Nat} {rest : List Nat} :
    SeqDone P (s, .active {} [], o.toList ++ rest) s' ↔
      ∃ s₁, StartsReach P s o s₁ ∧ SeqDone P (s₁, .active {} [], rest) s' := by
  cases o with
  | none =>
    simp only [Option.toList_none, List.nil_append]
    exact ⟨fun h => ⟨s, startsReach_none.2 rfl, h⟩,
      fun ⟨s₁, h₁, h⟩ => startsReach_none.1 h₁ ▸ h⟩
  | some a =>
    simp only [Option.toList_some, List.singleton_append]
    rw [seqDone_finished_cons]
    exact seqDone_finished_single

/-- **A pair of optional start functions returns.** -/
theorem seqDone_pair_iff {s s' : Store Nat} {o₁ o₂ : Option Nat} :
    SeqDone P (s, .active {} [], o₁.toList ++ o₂.toList) s' ↔
      ∃ s₁, StartsReach P s o₁ s₁ ∧ StartsReach P s₁ o₂ s' := by
  rw [seqDone_single]
  have h₂ : ∀ s₁, SeqDone P (s₁, .active {} [], o₂.toList) s' ↔ StartsReach P s₁ o₂ s' := by
    intro s₁
    have h := seqDone_single (P := P) (s := s₁) (s' := s') (o := o₂) (rest := [])
    rw [List.append_nil] at h
    rw [h]
    constructor
    · rintro ⟨s₂, h₂, hd⟩
      obtain ⟨t', hr, -⟩ := seqDone_nil.1 hd
      obtain ⟨rfl, -⟩ := Prod.mk.inj (reach_finished hr)
      exact h₂
    · intro h₂
      exact ⟨s', h₂, seqDone_nil.2 ⟨_, .refl, rfl⟩⟩
  simp only [h₂]

theorem not_seqFail_finished_nil {s : Store Nat} {b : Behaviour Val} :
    ¬ SeqFail P (s, .active {} [], []) b := by
  intro h
  obtain ⟨c, hr', hf⟩ := seqFail_nil.1 h
  rw [reach_finished hr'] at hf
  rcases hf with ⟨h, -⟩ | ⟨x, h, -⟩ <;> cases h

theorem seqFail_finished_single {s : Store Nat} {a : Nat} {rest : List Nat} {b : Behaviour Val} :
    SeqFail P (s, .pending a [], rest) b ↔
      StartFails P s (some a) b ∨ ∃ s₁, StartsReach P s (some a) s₁ ∧
        SeqFail P (s₁, .active {} [], rest) b := by
  cases rest with
  | nil =>
    rw [seqFail_nil]
    constructor
    · exact .inl
    · rintro (h | ⟨s₁, -, h⟩)
      · exact h
      · exact absurd h not_seqFail_finished_nil
  | cons b' rest =>
    rw [seqFail_cons]
    constructor
    · rintro (h | ⟨s₁, t₁, hr, hres, hd⟩)
      · exact .inl h
      · exact .inr ⟨s₁, ⟨t₁, hr, hres⟩, seqFail_finished_cons.2 hd⟩
    · rintro (h | ⟨s₁, ⟨t₁, hr, hres⟩, h⟩)
      · exact .inl h
      · exact .inr ⟨s₁, t₁, hr, hres, seqFail_finished_cons.1 h⟩

/-- A single optional start function from the finished empty thread, failing. -/
theorem seqFail_single {s : Store Nat} {o : Option Nat} {rest : List Nat} {b : Behaviour Val} :
    SeqFail P (s, .active {} [], o.toList ++ rest) b ↔
      StartFails P s o b ∨ ∃ s₁, StartsReach P s o s₁ ∧ SeqFail P (s₁, .active {} [], rest) b := by
  cases o with
  | none =>
    simp only [Option.toList_none, List.nil_append]
    constructor
    · intro h
      exact .inr ⟨s, startsReach_none.2 rfl, h⟩
    · rintro (h | ⟨s₁, h₁, h⟩)
      · exact absurd h not_startFails_none
      · exact startsReach_none.1 h₁ ▸ h
  | some a =>
    simp only [Option.toList_some, List.singleton_append]
    rw [seqFail_finished_cons]
    exact seqFail_finished_single

/-- **A pair of optional start functions fails**: the first, or the second after the first
returned. -/
theorem seqFail_pair_iff {s : Store Nat} {o₁ o₂ : Option Nat} {b : Behaviour Val} :
    SeqFail P (s, .active {} [], o₁.toList ++ o₂.toList) b ↔
      StartFails P s o₁ b ∨ ∃ s₁, StartsReach P s o₁ s₁ ∧ StartFails P s₁ o₂ b := by
  rw [seqFail_single]
  have h₂ : ∀ s₁, SeqFail P (s₁, .active {} [], o₂.toList) b ↔ StartFails P s₁ o₂ b := by
    intro s₁
    have h := seqFail_single (P := P) (s := s₁) (b := b) (o := o₂) (rest := [])
    rw [List.append_nil] at h
    rw [h]
    constructor
    · rintro (h₂ | ⟨s₂, -, hd⟩)
      · exact h₂
      · obtain ⟨c, hr, hf⟩ := seqFail_nil.1 hd
        rw [reach_finished hr] at hf
        rcases hf with ⟨h, -⟩ | ⟨x, h, -⟩ <;> cases h
    · exact .inl
  simp only [h₂]

/-! ## The export phase of a start sequence -/

/-- The states of the instance system as states of the system with a start sequence. -/
noncomputable def phiSeq (I : ScalarInstance) (P : Profile) (s₀ : Store Nat) (starts : List Nat) :
    I.HState → (I.instSysSeq P s₀ starts).St
  | .idle s => .ready s
  | .running f s t => .run f (s, t)
  | .waiting f s t e => .wait f e (I.resumeK s t e)

/-- **The export phase of the system with a start sequence is the instance system.** -/
noncomputable def exportBSeq (I : ScalarInstance) (P : Profile) (s₀ s : Store Nat)
    (starts : List Nat) : FBisim (I.dlts P s) (I.instSysSeq P s₀ starts).toLTS where
  φ := phiSeq I P s₀ starts
  ρ := liftMove
  inj := upperMap_injective liftEv_injective
  fwd := by
    intro x l y h
    cases h with
    | call s f => exact InstSystem.Step.askEx (S := I.instSysSeq P s₀ starts) s f
    | tau h => exact InstSystem.Step.tau h
    | ucall callout op => exact InstSystem.Step.call ⟨⟨_, _, callout, op⟩, rfl⟩
    | uret v => exact InstSystem.Step.resume _ _ _ v
    | oret final answer => exact InstSystem.Step.ret ⟨_, final, answer, rfl⟩
  bwd := by
    intro x l z h
    cases x with
    | idle s =>
      cases (h : InstSystem.Step (I.instSysSeq P s₀ starts) (.ready s) l z) with
      | askEx _ q =>
        exact ⟨some (.inr (.ask q)), .running q s (I.initThread q), rfl, rfl,
          Silmaril.Wasm.Game.ScalarInstance.DTrans.call s q⟩
    | running f s t =>
      cases (h : InstSystem.Step (I.instSysSeq P s₀ starts) (.run f (s, t)) l z) with
      | tau hi =>
        exact ⟨none, .running f _ _, rfl, rfl, Silmaril.Wasm.Game.ScalarInstance.DTrans.tau hi⟩
      | call hc =>
        obtain ⟨⟨_, _, hco, hop⟩, rfl⟩ := hc
        exact ⟨some (.inl (.ask _)), .waiting f s t _, rfl, rfl,
          Silmaril.Wasm.Game.ScalarInstance.DTrans.ucall hco hop⟩
      | ret hd =>
        obtain ⟨r, hr, hv, hst⟩ := hd
        exact ⟨some (.inr (.ans f _)), .idle s, rfl, by rw [hst]; rfl,
          Silmaril.Wasm.Game.ScalarInstance.DTrans.oret hr hv⟩
    | waiting f s t e =>
      cases (h : InstSystem.Step (I.instSysSeq P s₀ starts) (.wait f e (I.resumeK s t e)) l z) with
      | resume _ _ _ n =>
        exact ⟨some (.inl (.ans e n)),
          .running f s (resumeResult s t (Answer.toResult (ft := I.imports.get e.1) n)), rfl, rfl,
          Silmaril.Wasm.Game.ScalarInstance.DTrans.uret n⟩

/-- **Ready traces of a system with a start sequence.** -/
theorem instSysSeq_ready_traces {s : Store Nat} {starts : List Nat}
    {w : List (Move I.E (I.F.withInst (Behaviour Val)))} :
    [askInst, ansInst .ready] ++ w ∈ (I.instSysSeq P s starts).toLTS.Traces ↔
      ∃ s', SeqDone P (s, .active {} [], starts) s' ∧ ∃ q, w = q.map liftMove ∧ q ∈ I.plays P s' := by
  rw [InstSystem.toLTS_ready_iff]
  constructor
  · rintro ⟨c, st, z, hc, ⟨hres, hnil, rfl⟩, hrun⟩
    obtain ⟨q, y, rfl, -, hr⟩ := (exportBSeq I P s c.1 starts).run_bwd (x := .idle c.1) hrun
    exact ⟨c.1, seqDone_iff.1 ⟨c, hc, hres, hnil, rfl⟩, q, rfl,
      (ScalarInstance.traces_dlts P c.1) ▸ ⟨y, hr⟩⟩
  · rintro ⟨s', hd, q, rfl, hq⟩
    obtain ⟨c, hc, hres, hnil, rfl⟩ := seqDone_iff.2 hd
    rw [← ScalarInstance.traces_dlts P c.1] at hq
    obtain ⟨y, hy⟩ := hq
    exact ⟨c, c.1, _, hc, ⟨hres, hnil, rfl⟩, (exportBSeq I P s c.1 starts).run_fwd hy⟩

/-- **Failing traces of a system with a start sequence.** -/
theorem instSysSeq_fail_traces {s : Store Nat} {starts : List Nat} {b : Behaviour Val}
    {w : List (Move I.E (I.F.withInst (Behaviour Val)))} :
    [askInst, ansInst (.fail b)] ++ w ∈ (I.instSysSeq P s starts).toLTS.Traces ↔
      SeqFail P (s, .active {} [], starts) b ∧ w = [] := by
  rw [InstSystem.toLTS_fail_iff]
  constructor
  · rintro ⟨⟨c, hc, hf⟩, rfl⟩
    exact ⟨seqFail_iff.1 ⟨c, hc, hf⟩, rfl⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨seqFail_iff.2 hf, rfl⟩

/-! ## The consumer system of a link -/

/-- **Instantiation runs of the consumer are runs of the joint machine.** -/
theorem irun_iff_lrun {s : Store Nat} {start : Option Nat} {x y : (I.instSys P s start).IConf}
    {l : List (Ev I.E)} :
    InstSystem.IRun (I.instSys P s start) x l y ↔
      Silmaril.Proofs.Wasm.Game.Linking.Split.LRun I P x l y := by
  constructor
  · intro h
    induction h with
    | refl => exact .done .refl
    | step hs _ ih =>
      cases ih with
      | done hr => exact .done (.head hs hr)
      | call hr hco hop hrest => exact .call (.head hs hr) hco hop hrest
    | call hc _ ih =>
      obtain ⟨⟨h, args, hco, hop⟩, rfl⟩ := hc
      exact .call .refl hco hop ih
  · intro h
    induction h with
    | done hr => exact InstSystem.irun_of_rtg _ hr
    | @call x y s₁ t₁ h args e w l hr hco hop _ ih =>
      have hc : (I.instSys P s start).icall (s₁, t₁) e (I.resumeK s₁ t₁ e) :=
        ⟨⟨_, _, hco, hop⟩, rfl⟩
      exact irun_trans (InstSystem.irun_of_rtg _ hr) (.call (n := w) hc ih)
where
  irun_trans {x y z : (I.instSys P s start).IConf} {l : List (Ev I.E)}
      (h₁ : InstSystem.IRun (I.instSys P s start) x [] y)
      (h₂ : InstSystem.IRun (I.instSys P s start) y l z) :
      InstSystem.IRun (I.instSys P s start) x l z := by
    generalize hn : ([] : List (Ev I.E)) = n at h₁
    induction h₁ with
    | refl => exact h₂
    | step hs _ ih => exact .step hs (ih h₂ hn)
    | call _ _ _ => cases hn

/-- The lifting of the moves of the consumer to the moves of its link system. -/
def liftC {E F : Sig.{0}} {R : Type} : Move E F → Move (E.withInst R) (F.withInst R) :=
  Sum.map liftEv liftEv

theorem liftC_injective {E F : Sig.{0}} {R : Type} :
    Function.Injective (liftC (E := E) (F := F) (R := R)) :=
  Sum.map_injective.2 ⟨liftEv_injective, liftEv_injective⟩

/-- **The export phase of the consumer system is the instance system**, lower and upper moves
lifted. -/
noncomputable def exportBc (I : ScalarInstance) (P : Profile) (s₀ s : Store Nat)
    (start : Option Nat) : FBisim (I.dlts P s) (I.instSys P s₀ start).consumerLTS where
  φ := phi I P s₀ (startThread start)
  ρ := liftC
  inj := liftC_injective
  fwd := by
    intro x l y h
    cases h with
    | call s f => exact InstSystem.LinkStep.askEx (S := I.instSys P s₀ start) s f
    | tau h => exact InstSystem.LinkStep.tau h
    | ucall callout op => exact InstSystem.LinkStep.call ⟨⟨_, _, callout, op⟩, rfl⟩
    | uret v => exact InstSystem.LinkStep.resume _ _ _ v
    | oret final answer => exact InstSystem.LinkStep.ret ⟨_, final, answer, rfl⟩
  bwd := by
    intro x l z h
    cases x with
    | idle s =>
      cases (h : InstSystem.LinkStep (I.instSys P s₀ start) (.ready s) l z) with
      | askEx _ q =>
        exact ⟨some (.inr (.ask q)), .running q s (I.initThread q), rfl, rfl,
          Silmaril.Wasm.Game.ScalarInstance.DTrans.call s q⟩
    | running f s t =>
      cases (h : InstSystem.LinkStep (I.instSys P s₀ start) (.run f (s, t)) l z) with
      | tau hi =>
        exact ⟨none, .running f _ _, rfl, rfl, Silmaril.Wasm.Game.ScalarInstance.DTrans.tau hi⟩
      | call hc =>
        obtain ⟨⟨_, _, hco, hop⟩, rfl⟩ := hc
        exact ⟨some (.inl (.ask _)), .waiting f s t _, rfl, rfl,
          Silmaril.Wasm.Game.ScalarInstance.DTrans.ucall hco hop⟩
      | ret hd =>
        obtain ⟨r, hr, hv, hst⟩ := hd
        exact ⟨some (.inr (.ans f _)), .idle s, rfl, by rw [hst]; rfl,
          Silmaril.Wasm.Game.ScalarInstance.DTrans.oret hr hv⟩
    | waiting f s t e =>
      cases (h : InstSystem.LinkStep (I.instSys P s₀ start) (.wait f e (I.resumeK s t e)) l z) with
      | resume _ _ _ n =>
        exact ⟨some (.inl (.ans e n)),
          .running f s (resumeResult s t (Answer.toResult (ft := I.imports.get e.1) n)), rfl, rfl,
          Silmaril.Wasm.Game.ScalarInstance.DTrans.uret n⟩

/-- Runs of the consumer's export phase are plays of the consumer, lifted. -/
theorem consumer_export_run {s₀ s' : Store Nat} {start : Option Nat}
    {w : List (Move (I.E.withInst (Behaviour Val)) (I.F.withInst (Behaviour Val)))}
    {z : (I.instSys P s₀ start).St} (h : (I.instSys P s₀ start).consumerLTS.Run (.ready s') w z) :
    ∃ q, w = q.map liftC ∧ q ∈ I.plays P s' := by
  obtain ⟨q, y, rfl, -, hr⟩ := (exportBc I P s₀ s' start).run_bwd (x := .idle s') h
  exact ⟨q, rfl, (ScalarInstance.traces_dlts P s') ▸ ⟨y, hr⟩⟩

theorem consumer_export_run_of {s₀ s' : Store Nat} {start : Option Nat}
    {q : List (Move I.E I.F)} (hq : q ∈ I.plays P s') :
    ∃ z, (I.instSys P s₀ start).consumerLTS.Run (.ready s') (q.map liftC) z := by
  rw [← ScalarInstance.traces_dlts P s'] at hq
  obtain ⟨y, hy⟩ := hq
  exact ⟨_, (exportBc I P s₀ s' start).run_fwd hy⟩

end Silmaril.Proofs.Wasm.Game.LinkStart
