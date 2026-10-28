module

public import Silmaril.X86.Features.Embed
public import Silmaril.X86.Features.Restrict
public import Mathlib.Order.Defs.PartialOrder

/-!
# The lattice of x86 machine configurations

A *configuration* `Config` is what the feature-parametric machine
(`Features.step F exts`) is instantiated with: a feature set `F` and a list of
pairwise-disjoint extension decoders `exts`. This file orders configurations
and proves that everything proved about a smaller configuration holds about
every larger one.

## The order

`c ≤ d` (`Config.Le`) when `c.features ⊆ d.features` and every extension of `c`
embeds into one of `d` (`Included`, built from `Extension.Embeds`). This is a
preorder (`instance : Preorder Config`); it is not antisymmetric, since two
lists that embed into each other may differ.

Two configurations are *compatible* (`Config.Compatible`) when the
concatenation of their extension lists is pairwise disjoint
(`compatible_iff`: each is disjoint, and every extension of one is disjoint
from every extension of the other). Compatible configurations have a join
`Config.join` (features `F ∪ G`, extensions `c.exts ++ d.exts`), which is a
least upper bound (`le_join_left`, `le_join_right`, `join_le`). `Config.base F`
(no extensions) is below every configuration with more features (`base_le`),
and `Config.bot` is below every configuration.

## What transfers, and under which hypothesis

The step of a larger configuration differs from the step of a smaller one
only where the smaller one stops: a feature fault (`featureUD`,
`featureAlias`), an encoding it cannot decode (`undecodable`, chaos), or a
truncated encoding (`fetchFault`, which a new decoder may read as a shorter
instruction). `Settled o` excludes exactly these outcomes.

* **One step** (`step_le`): if the step of `c` at `m` is `Settled`, every
  `d ≥ c` takes the same step.
* **Existential judgments, unconditionally.** A retirement and a return are
  settled, so runs (`run_le`), reachability (`reaches_le`) and returns
  (`returns_le`) transfer from `c` to every `d ≥ c` with no hypothesis.
* **Universal judgments, under `Stable`.** `Stable c exit m₀` says that every
  state reachable under `c` has a settled step. Then every `d ≥ c` has the same
  runs, the same outcome at every reachable state, the same returns, and is
  stable too (`Stable.same_behaviour`). `Stable` implies
  `FeatureFree` (`Stable.featureFree`); it is the extension-list analogue of
  `FeatureFree.same_behaviour` of `Transport.lean`, combined with it.
* **Safety** (`Safe`): a safety judgment whose good outcomes are all settled
  (it rules out chaos and feature faults, as every statement about real
  hardware must) implies `Stable` (`Stable.of_safe`) and therefore transfers
  (`Safe.le`). A safety judgment that *allows* an undecodable or feature-fault
  outcome does not transfer in general: a larger configuration executes those
  bytes, and anything can follow.
* **Total correctness** (`TotalOn`): a family of launches, each safe (with
  settled good outcomes) and returning with a final state in a goal; it
  transfers (`TotalOn.le`).
* **Leads-to, cut-point and relational judgments** look at the transition
  relation only at states satisfying their invariant. `stepOpt_iff_le` says
  that the retirement relations of `c` and `d` agree at every state whose
  `c`-step is settled, so such a judgment transfers as soon as its invariant
  implies `Settled` (`Settled` is exactly the hypothesis needed).
* **Problems.** `Upward J` says that a judgment on configurations is preserved
  by `≤`. `returns_upward`, `safe_upward` and `totalOn_upward` show that the
  judgments above are; a `@[problem]` stated at a configuration `c` through an
  upward judgment is therefore solved at every `d ≥ c` by `Upward.transfer`
  (one line per solution).

The LPS process judgments (behaviours, `MustExitInAt`) and the `Sys.Machine`
judgments of the `sha256sum` statements (`Satisfies`, `Live`) are transferred
in `Features/Lattice/LPS.lean` and `Features/Lattice/Sys.lean` from the same
one-step fact.

## The existing machines

* `X86.Ext` is `Config.base F` for any `F ⊇ baseFeatures`
  (`step_nil_of_baseFeatures`), and its runs and returns embed into every
  configuration with those features (`run_of_base`, `returns_of_base`).
* `X86.Float`'s scalar SSE machine is `floatConfig F` (`[floatExt]`); see
  `step_floatExt_le` for its steps inside every larger configuration.
* `X86.Ext.Wire` is the extension `wireExt` (`Features/Lattice/Wire.lean`):
  the integer decoder embeds into it, not the reverse.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory)

/-! ## Inclusion of extension lists is a preorder -/

theorem Included.refl (exts : List Extension) : Included exts exts :=
  Included.of_subset (List.Subset.refl _)

-- `Included.trans` is in `Restrict.lean`.

theorem Included.append {a b c : List Extension} (ha : Included a c) (hb : Included b c) :
    Included (a ++ b) c := fun e he => (List.mem_append.mp he).elim (ha e) (hb e)

theorem Included.nil (c : List Extension) : Included [] c := fun _ h => nomatch h

-- `Extension.Disjoint.symm` is in `Restrict.lean`.

/-- An extension that decodes the bytes makes the list decode them. -/
theorem extDecode_isSome_of_mem {exts : List Extension} {e : Extension} (he : e ∈ exts)
    {bytes : List Byte} {x : e.Syntax} {n : Nat} (h : e.decoder.decode bytes = some (x, n)) :
    (extDecode exts bytes).isSome := by
  induction exts with
  | nil => cases he
  | cons d ds ih =>
    unfold extDecode
    split
    · rfl
    · rename_i hd
      rcases List.mem_cons.mp he with rfl | hin
      · rw [h] at hd; cases hd
      · exact ih hin

/-- What a list decodes, a list it is included in decodes. -/
theorem Decodes.mono {exts exts' : List Extension} (hinc : Included exts exts') {m : MState}
    (h : Decodes exts m) : Decodes exts' m := by
  rcases h with h | h
  · exact .inl h
  · right
    obtain ⟨⟨e, x, n⟩, hx⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨he, hdx⟩ := extDecode_sound hx
    obtain ⟨e', he', ι, hdι, -, -⟩ := hinc e he
    exact extDecode_isSome_of_mem he' (hdι _ x n hdx)

/-! ## Configurations -/

/-- A machine configuration: a feature set and pairwise-disjoint extensions. -/
structure Config where
  features : FeatureSet
  exts : List Extension
  disjoint : Extension.PairwiseDisjoint exts

namespace Config

/-- `c ≤ d`: more features, and every extension of `c` embeds into one of `d`. -/
def Le (c d : Config) : Prop := c.features ⊆ d.features ∧ Included c.exts d.exts

instance : Preorder Config where
  le := Le
  le_refl c := ⟨FeatureSet.subset_refl _, Included.refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨FeatureSet.subset_trans h₁.1 h₂.1, h₁.2.trans h₂.2⟩

theorem le_def {c d : Config} : c ≤ d ↔ c.features ⊆ d.features ∧ Included c.exts d.exts :=
  Iff.rfl

theorem le_of_subset {c d : Config} (hF : c.features ⊆ d.features) (hx : c.exts ⊆ d.exts) :
    c ≤ d := ⟨hF, Included.of_subset hx⟩

/-- No extensions. -/
def base (F : FeatureSet) : Config := ⟨F, [], List.Pairwise.nil⟩

/-- No features and no extensions. -/
def bot : Config := base FeatureSet.empty

theorem base_le {F : FeatureSet} {c : Config} (h : F ⊆ c.features) : base F ≤ c :=
  ⟨h, Included.nil _⟩

theorem bot_le (c : Config) : bot ≤ c := base_le fun _ h => nomatch h

theorem base_mono {F G : FeatureSet} (h : F ⊆ G) : base F ≤ base G := base_le h

/-- More features, same extensions. -/
def withFeatures (c : Config) (G : FeatureSet) : Config := ⟨G, c.exts, c.disjoint⟩

theorem le_withFeatures (c : Config) {G : FeatureSet} (h : c.features ⊆ G) :
    c ≤ c.withFeatures G := ⟨h, Included.refl _⟩

/-! ### Joins of compatible configurations -/

/-- The extensions of `c` and `d` together are pairwise disjoint. -/
def Compatible (c d : Config) : Prop := Extension.PairwiseDisjoint (c.exts ++ d.exts)

theorem compatible_iff {c d : Config} :
    c.Compatible d ↔ ∀ e ∈ c.exts, ∀ e' ∈ d.exts, e.Disjoint e' := by
  unfold Compatible Extension.PairwiseDisjoint
  rw [List.pairwise_append]
  exact ⟨fun h => h.2.2, fun h => ⟨c.disjoint, d.disjoint, h⟩⟩

theorem Compatible.symm {c d : Config} (h : c.Compatible d) : d.Compatible c :=
  compatible_iff.mpr fun e he e' he' => (compatible_iff.mp h e' he' e he).symm

theorem compatible_base_left (F : FeatureSet) (c : Config) : (base F).Compatible c := by
  simpa [Compatible, base] using c.disjoint

/-- The join of compatible configurations. -/
def join (c d : Config) (h : c.Compatible d) : Config :=
  ⟨c.features ∪ d.features, c.exts ++ d.exts, h⟩

theorem le_join_left (c d : Config) (h : c.Compatible d) : c ≤ c.join d h :=
  le_of_subset (FeatureSet.subset_union_left _ _) (List.subset_append_left _ _)

theorem le_join_right (c d : Config) (h : c.Compatible d) : d ≤ c.join d h :=
  le_of_subset (FeatureSet.subset_union_right _ _) (List.subset_append_right _ _)

/-- The join is the least upper bound. -/
theorem join_le {c d e : Config} (h : c.Compatible d) (hc : c ≤ e) (hd : d ≤ e) :
    c.join d h ≤ e :=
  ⟨fun f hf => ((FeatureSet.mem_union _ _ f).mp hf).elim (hc.1 f) (hd.1 f), hc.2.append hd.2⟩

theorem join_le_iff {c d e : Config} (h : c.Compatible d) : c.join d h ≤ e ↔ c ≤ e ∧ d ≤ e :=
  ⟨fun hj => ⟨(le_join_left c d h).trans hj, (le_join_right c d h).trans hj⟩,
    fun ⟨hc, hd⟩ => join_le h hc hd⟩

/-- Joins are commutative up to the preorder. -/
theorem join_comm_le {c d : Config} (h : c.Compatible d) : c.join d h ≤ d.join c h.symm :=
  join_le h (le_join_right d c h.symm) (le_join_left d c h.symm)

/-! ### The machine of a configuration -/

variable (c : Config) (exit : Word)

def step (m : MState) : Outcome := Features.step c.features c.exts exit m

def stepOpt (m : MState) : Option MState := Features.stepOpt c.features c.exts exit m

def run (n : Nat) (m : MState) : Option MState := Features.run c.features c.exts exit n m

def Returns (initial final : MState) : Prop := Features.Returns c.features c.exts exit initial final

/-- `m` is reachable from `initial` by retirements. -/
def Reaches (initial m : MState) : Prop := ∃ n, c.run exit n initial = some m

variable {c exit}

theorem run_succ' (n : Nat) (m : MState) :
    c.run exit (n + 1) m = (c.stepOpt exit m).bind (c.run exit n) := rfl

theorem stepOpt_eq_some_iff' {m next : MState} :
    c.stepOpt exit m = some next ↔ c.step exit m = .retired next :=
  Features.stepOpt_eq_some_iff

end Config

/-! ## Settled outcomes -/

/-- An outcome that no larger configuration can change: not a feature fault,
not undecodable, and not a fetch fault. -/
def Outcome.Settled (o : Outcome) : Prop :=
  o.featureFault? = none ∧ o ≠ .undecodable ∧ o ≠ .fetchFault

@[simp] theorem Outcome.settled_retired (m : MState) : (Outcome.retired m).Settled :=
  ⟨rfl, nofun, nofun⟩

@[simp] theorem Outcome.settled_returned (m : MState) : (Outcome.returned m).Settled :=
  ⟨rfl, nofun, nofun⟩

@[simp] theorem Outcome.settled_fault (f : Fault) : (Outcome.fault f).Settled :=
  ⟨rfl, nofun, nofun⟩

@[simp] theorem Outcome.settled_unmodeled : Outcome.unmodeled.Settled :=
  ⟨rfl, nofun, nofun⟩

@[simp] theorem Outcome.settled_undefinedCondition (c : Ext.Cond) :
    (Outcome.undefinedCondition c).Settled := ⟨rfl, nofun, nofun⟩

instance (o : Outcome) : Decidable o.Settled := by
  unfold Outcome.Settled
  cases o <;> simp [Outcome.featureFault?] <;> infer_instance

/-- A step other than a fetch fault or undecodable bytes was decoded. -/
theorem decodes_of_step {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    (hf : step F exts exit m ≠ .fetchFault) (hu : step F exts exit m ≠ .undecodable) :
    Decodes exts m := by
  unfold step at hf hu
  cases hfe : Ext.fetch m.memory m.state.core.rip.toNat with
  | decoded i n => exact .inl ⟨i, n, hfe⟩
  | truncated =>
    cases hx : extDecode exts (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) with
    | some p => exact .inr (by rw [hx]; rfl)
    | none => simp [hfe, hx] at hf
  | undecodable =>
    cases hx : extDecode exts (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) with
    | some p => exact .inr (by rw [hx]; rfl)
    | none => simp [hfe, hx] at hu

/-! ## One step -/

namespace Config

variable {c d : Config} {exit : Word}

/-- **One step**: a settled step is the same in every larger configuration. -/
theorem step_le (h : c ≤ d) {m : MState} (hs : (c.step exit m).Settled) :
    d.step exit m = c.step exit m := by
  have hd := decodes_of_step hs.2.2 hs.2.1
  unfold Config.step at *
  rw [step_conservative d.disjoint h.2 hd]
  exact step_mono h.1 hs.1

theorem stepOpt_le (h : c ≤ d) {m next : MState} (hs : c.stepOpt exit m = some next) :
    d.stepOpt exit m = some next := by
  rw [stepOpt_eq_some_iff'] at hs ⊢
  rw [step_le h (hs ▸ Outcome.settled_retired next), hs]

/-- At a state whose step is settled, the retirement relations of `c` and `d ≥ c` agree. -/
theorem stepOpt_iff_le (h : c ≤ d) {m : MState} (hs : (c.step exit m).Settled)
    (next : MState) : d.stepOpt exit m = some next ↔ c.stepOpt exit m = some next := by
  rw [stepOpt_eq_some_iff', stepOpt_eq_some_iff', step_le h hs]

/-! ## Existential judgments transfer unconditionally -/

theorem run_le (h : c ≤ d) {n : Nat} {initial m : MState} (hr : c.run exit n initial = some m) :
    d.run exit n initial = some m := by
  induction n generalizing initial with
  | zero => exact hr
  | succ n ih =>
    rw [run_succ'] at hr ⊢
    cases hs : c.stepOpt exit initial with
    | none => rw [hs] at hr; cases hr
    | some next =>
      rw [hs] at hr
      rw [stepOpt_le h hs]
      exact ih hr

theorem reaches_le (h : c ≤ d) {initial m : MState} (hr : c.Reaches exit initial m) :
    d.Reaches exit initial m :=
  let ⟨n, hn⟩ := hr; ⟨n, run_le h hn⟩

theorem returns_le (h : c ≤ d) {initial final : MState} (hr : c.Returns exit initial final) :
    d.Returns exit initial final := by
  obtain ⟨n, mid, hrun, hstep⟩ := hr
  refine ⟨n, mid, run_le h hrun, ?_⟩
  have : (c.step exit mid).Settled := by
    unfold Config.step; rw [hstep]; exact Outcome.settled_returned final
  have e := step_le h this
  unfold Config.step at e
  rw [e, hstep]

/-! ## Stability: universal judgments -/

/-- Every state reachable under `c` has a settled step. -/
def Stable (c : Config) (exit : Word) (initial : MState) : Prop :=
  ∀ n m, c.run exit n initial = some m → (c.step exit m).Settled

namespace Stable

variable {initial : MState}

theorem next (hs : c.Stable exit initial) {m : MState} (h : c.stepOpt exit initial = some m) :
    c.Stable exit m := fun n m' hr => hs (n + 1) m' (by rw [run_succ', h]; exact hr)

theorem featureFree (hs : c.Stable exit initial) :
    FeatureFree c.features c.exts exit initial := fun n m hr => (hs n m hr).1

/-- Same runs in every larger configuration. -/
theorem run_eq (hs : c.Stable exit initial) (h : c ≤ d) (n : Nat) :
    d.run exit n initial = c.run exit n initial := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
    rw [run_succ', run_succ']
    have hstep : d.stepOpt exit initial = c.stepOpt exit initial := by
      unfold Config.stepOpt Features.stepOpt
      have := step_le h (hs 0 initial rfl)
      unfold Config.step at this
      rw [this]
    rw [hstep]
    cases hn : c.stepOpt exit initial with
    | none => rfl
    | some next => exact ih (hs.next hn)

/-- Same outcome at every reachable state. -/
theorem step_eq (hs : c.Stable exit initial) (h : c ≤ d) {n : Nat} {m : MState}
    (hr : c.run exit n initial = some m) : d.step exit m = c.step exit m :=
  step_le h (hs n m hr)

theorem reaches_iff (hs : c.Stable exit initial) (h : c ≤ d) {m : MState} :
    d.Reaches exit initial m ↔ c.Reaches exit initial m := by
  simp only [Reaches, hs.run_eq h]

theorem returns_iff (hs : c.Stable exit initial) (h : c ≤ d) {final : MState} :
    d.Returns exit initial final ↔ c.Returns exit initial final := by
  refine ⟨fun ⟨n, mid, hr, hstep⟩ => ?_, returns_le h⟩
  have hr' : c.run exit n initial = some mid := (hs.run_eq h n).symm.trans hr
  refine ⟨n, mid, hr', ?_⟩
  have := hs.step_eq h hr'
  unfold Config.step at this
  rw [← this]; exact hstep

/-- Stable in every larger configuration. -/
theorem mono (hs : c.Stable exit initial) (h : c ≤ d) : d.Stable exit initial := by
  intro n m hr
  rw [hs.run_eq h] at hr
  rw [hs.step_eq h hr]
  exact hs n m hr

/-- **The headline**: a program stable under `c` has exactly the same
behaviour (runs, outcome at every reachable state, reachable states, returns)
in every configuration `d ≥ c`, and is stable there. -/
theorem same_behaviour (hs : c.Stable exit initial) (h : c ≤ d) :
    (∀ n, d.run exit n initial = c.run exit n initial) ∧
      (∀ n m, c.run exit n initial = some m → d.step exit m = c.step exit m) ∧
      (∀ m, d.Reaches exit initial m ↔ c.Reaches exit initial m) ∧
      (∀ final, d.Returns exit initial final ↔ c.Returns exit initial final) ∧
      d.Stable exit initial :=
  ⟨hs.run_eq h, fun _ _ hr => hs.step_eq h hr, fun _ => hs.reaches_iff h,
    fun _ => hs.returns_iff h, hs.mono h⟩

end Stable

/-! ## Safety and total correctness -/

/-- Safety: at every reachable state, the state and its outcome satisfy `good`. -/
def Safe (c : Config) (exit : Word) (initial : MState) (good : MState → Outcome → Prop) :
    Prop :=
  ∀ n m, c.run exit n initial = some m → good m (c.step exit m)

/-- A safety judgment whose good outcomes are settled makes the program stable. -/
theorem Stable.of_safe {initial : MState} {good : MState → Outcome → Prop}
    (h : c.Safe exit initial good) (hg : ∀ m o, good m o → o.Settled) : c.Stable exit initial :=
  fun n m hr => hg m _ (h n m hr)

/-- **Safety transfers** to every larger configuration when its good outcomes
are settled. -/
theorem Safe.le {initial : MState} {good : MState → Outcome → Prop}
    (hsafe : c.Safe exit initial good) (hg : ∀ m o, good m o → o.Settled) (h : c ≤ d) :
    d.Safe exit initial good := by
  have hs := Stable.of_safe hsafe hg
  intro n m hr
  rw [hs.run_eq h] at hr
  rw [hs.step_eq h hr]
  exact hsafe n m hr

/-- Total correctness on a family of launches: each launch in `domain` is safe
with settled good outcomes and returns to `exit` with a final state in `goal`. -/
def TotalOn (c : Config) (exit : Word) {ι : Type} (domain : ι → Prop) (init : ι → MState)
    (good : MState → Outcome → Prop) (goal : ι → MState → Prop) : Prop :=
  (∀ m o, good m o → o.Settled) ∧
    ∀ i, domain i → c.Safe exit (init i) good ∧ ∃ final, c.Returns exit (init i) final ∧ goal i final

theorem TotalOn.le {ι : Type} {domain : ι → Prop} {init : ι → MState}
    {good : MState → Outcome → Prop} {goal : ι → MState → Prop}
    (ht : c.TotalOn exit domain init good goal) (h : c ≤ d) :
    d.TotalOn exit domain init good goal :=
  ⟨ht.1, fun i hi =>
    let ⟨hsafe, final, hret, hgoal⟩ := ht.2 i hi
    ⟨hsafe.le ht.1 h, final, returns_le h hret, hgoal⟩⟩

end Config

/-! ## Judgments on configurations, and Problems -/

/-- A judgment on configurations that every larger configuration inherits. A
problem stated as `J c` for an upward `J` is solved at every `d ≥ c` by
`Upward.transfer`. -/
def Config.Upward (J : Config → Prop) : Prop := ∀ c d : Config, c ≤ d → J c → J d

theorem Config.Upward.transfer {J : Config → Prop} (hJ : Config.Upward J) {c d : Config}
    (h : c ≤ d) (hc : J c) : J d := hJ c d h hc

theorem Config.Upward.and {J K : Config → Prop} (hJ : Config.Upward J) (hK : Config.Upward K) :
    Config.Upward fun c => J c ∧ K c := fun c d h hc => ⟨hJ c d h hc.1, hK c d h hc.2⟩

theorem Config.Upward.forall {ι : Sort _} {J : ι → Config → Prop} (hJ : ∀ i, Config.Upward (J i)) :
    Config.Upward fun c => ∀ i, J i c := fun c d h hc i => hJ i c d h (hc i)

theorem Config.returns_upward (exit : Word) (initial final : MState) :
    Config.Upward fun c => c.Returns exit initial final := fun _ _ h => Config.returns_le h

theorem Config.reaches_upward (exit : Word) (initial m : MState) :
    Config.Upward fun c => c.Reaches exit initial m := fun _ _ h => Config.reaches_le h

theorem Config.safe_upward (exit : Word) (initial : MState) {good : MState → Outcome → Prop}
    (hg : ∀ m o, good m o → o.Settled) :
    Config.Upward fun c => c.Safe exit initial good := fun _ _ h hs => hs.le hg h

theorem Config.stable_upward (exit : Word) (initial : MState) :
    Config.Upward fun c => c.Stable exit initial := fun _ _ h hs => hs.mono h

theorem Config.totalOn_upward (exit : Word) {ι : Type} (domain : ι → Prop) (init : ι → MState)
    (good : MState → Outcome → Prop) (goal : ι → MState → Prop) :
    Config.Upward fun c => c.TotalOn exit domain init good goal := fun _ _ h ht => ht.le h

/-! ## The integer machine `X86.Ext` at the bottom -/

namespace Config

variable {c : Config} {exit : Word}

/-- In a configuration with LZCNT, BMI1 and POPCNT, an instruction the integer
decoder fetches executes as in `X86.Ext`, whatever the extensions. -/
theorem step_of_base (hF : baseFeatures ⊆ c.features) {m : MState} {i : Ext.Instr} {n : Nat}
    (hf : Ext.fetch m.memory m.state.core.rip.toNat = .decoded i n) :
    c.step exit m = Outcome.ofBase m.state (Ext.step exit m.toBase) := by
  unfold Config.step
  rw [Features.step_of_base hf, baseCheck_of_baseFeatures hF]

/-- The extended state of an integer-machine state. -/
def lift (s : State) (m : X86.MState) : MState := ⟨s.setCore m.core, m.memory⟩

@[simp] theorem lift_toBase (s : State) (m : X86.MState) : (lift s m).toBase = m := rfl

@[simp] theorem lift_state (s : State) (m : X86.MState) : (lift s m).state = s.setCore m.core :=
  rfl

theorem lift_lift (s : State) (m m' : X86.MState) : lift (lift s m).state m' = lift s m' := rfl

private theorem base_decoded_of_retired {m next : X86.MState}
    (h : Ext.step exit m = .retired next ∨ Ext.step exit m = .returned next) :
    ∃ i n, Ext.fetch m.memory m.core.rip.toNat = .decoded i n := by
  unfold Ext.step at h
  split at h
  · simp at h
  · simp at h
  · exact ⟨_, _, by assumption⟩

/-- A retirement of `X86.Ext` is a retirement in every configuration with its features. -/
theorem stepOpt_of_base (hF : baseFeatures ⊆ c.features) (s : State) {m next : X86.MState}
    (h : Ext.stepOpt exit m = some next) : c.stepOpt exit (lift s m) = some (lift s next) := by
  rw [Ext.stepOpt_eq_some_iff] at h
  obtain ⟨i, n, hf⟩ := base_decoded_of_retired (exit := exit) (.inl h)
  rw [stepOpt_eq_some_iff', step_of_base hF (m := lift s m) hf, lift_toBase, h]
  rfl

/-- Runs of `X86.Ext` are runs in every configuration with its features, on any
vector state. -/
theorem run_of_base (hF : baseFeatures ⊆ c.features) (s : State) {n : Nat}
    {m mid : X86.MState} (h : Machine.Execution.run (Ext.stepOpt exit) n m = some mid) :
    c.run exit n (lift s m) = some (lift s mid) := by
  induction n generalizing m with
  | zero => cases h; rfl
  | succ n ih =>
    rw [Machine.Execution.run_succ] at h
    cases hs : Ext.stepOpt exit m with
    | none => rw [hs] at h; cases h
    | some next =>
      rw [hs] at h
      rw [run_succ', stepOpt_of_base hF s hs]
      exact ih h

/-- Returns of `X86.Ext` are returns in every configuration with its features. -/
theorem returns_of_base (hF : baseFeatures ⊆ c.features) (s : State) {m final : X86.MState}
    (h : Ext.Returns exit m final) : c.Returns exit (lift s m) (lift s final) := by
  obtain ⟨n, mid, hrun, hret⟩ := h
  refine ⟨n, lift s mid, run_of_base hF s hrun, ?_⟩
  obtain ⟨i, k, hf⟩ := base_decoded_of_retired (exit := exit) (.inr hret)
  have := step_of_base (c := c) (exit := exit) hF (m := lift s mid) hf
  unfold Config.step at this
  rw [this, lift_toBase, hret]
  rfl

/-! ## `X86.Float` scalar SSE -/

/-- `X86.Float`'s scalar SSE machine as a configuration. -/
def floatConfig (F : FeatureSet) : Config := ⟨F, [floatExt], List.pairwise_singleton _ _⟩

theorem base_le_floatConfig (F : FeatureSet) : base F ≤ floatConfig F := base_le (FeatureSet.subset_refl F)

/-- A scalar SSE step of `X86.Float`'s machine, when settled, is the step of
every configuration above `floatConfig F`. -/
theorem step_floatExt_le {F : FeatureSet} {d : Config} (h : floatConfig F ≤ d) {m : MState}
    {i : Float.Instr} {n : Nat}
    (hfetch : Float.fetch m.memory m.state.core.rip.toNat = .decoded (.sse i) n)
    (hbase : Ext.decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = none)
    (hF : i.feature.toFeature ∈ F)
    (hs : (Outcome.ofFloat m.state (Float.MState.step exit ⟨m.state.toFloat, m.memory⟩)).Settled) :
    d.step exit m = Outcome.ofFloat m.state (Float.MState.step exit ⟨m.state.toFloat, m.memory⟩) := by
  have e : (floatConfig F).step exit m =
      Outcome.ofFloat m.state (Float.MState.step exit ⟨m.state.toFloat, m.memory⟩) :=
    step_floatExt hfetch hbase hF
  rw [← e] at hs ⊢
  exact step_le h hs

end Config

end Silmaril.X86.Features
