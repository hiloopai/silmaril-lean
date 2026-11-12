module

public import Silmaril.Wasm.Game.DivAdequacy.Defs
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic
public import Silmaril.Proofs.Wasm.Game.Env.Basic
public import Silmaril.Games.DivLTS.Thms

/-!
# Divergence-observing strategies of instances: finite plays

The transition systems with silent steps have the same traces as the folded
ones: `I.dlts P s` denotes `I.strategy P s` (`denotes_dlts`; a silent run of
host-free steps followed by a visible move is one folded transition), and
`K.dlts` denotes `K.strategy` (`Env.denotes_dlts`; the silent self-loops on
unanswered questions are invisible). Hence the finite plays of the closed
program `I.closedD P s K` are those of `K.strategy ≫ I.strategy P s`
(`forget_closedD`, through `LTS.Denotes.comp`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace Env

variable {E : Sig.{0}} {K : Silmaril.Wasm.Game.Env E}

/-- Runs of the divergence-observing environment are runs of the plain one (self-loops
dropped). -/
theorem lts_run_of_dlts_run {x y : K.dlts.State} {p : List (Move Sig.empty E)}
    (h : K.dlts.Run x p y) : K.lts.Run x p y := by
  induction h with
  | nil x => exact LTS.Run.nil (L := K.lts) x
  | tau hs _ ih =>
    cases hs
    exact ih
  | vis hs _ ih =>
    cases hs with
    | ask e => exact .vis (.ask e) ih
    | ans hw => exact .vis (.ans hw) ih

/-- Runs of the plain environment are runs of the divergence-observing one. -/
theorem dlts_run_of_lts_run {x y : K.lts.State} {p : List (Move Sig.empty E)}
    (h : K.lts.Run x p y) : K.dlts.Run x p y := by
  induction h with
  | nil x => exact LTS.Run.nil (L := K.dlts) x
  | tau hs _ _ => cases hs
  | vis hs _ ih =>
    cases hs with
    | ask e => exact .vis (.ask e) ih
    | ans hw => exact .vis (.ans hw) ih

/-- The divergence-observing environment denotes the environment's strategy. -/
theorem denotes_dlts (K : Silmaril.Wasm.Game.Env E) : K.dlts.Denotes K.strategy := by
  intro p
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨u, rfl, hu⟩ := run_none (lts_run_of_dlts_run hy)
    exact mem_strategy_iff.2 ⟨u, hu, rfl⟩
  · intro hp
    obtain ⟨u, hu, rfl⟩ := mem_strategy_iff.1 hp
    obtain ⟨y, hy⟩ := run_of_agrees hu
    exact ⟨y, dlts_run_of_lts_run hy⟩

end Env

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile}

open Silmaril.Wasm.Game.ScalarInstance

/-- Host-free runs are silent runs of the transition system with silent steps. -/
theorem dlts_run_of_reach {s₀ : Store Nat} {f : I.F.Op} {s : Store Nat} {t : Thread} :
    ∀ {y : Store Nat × Thread}, Reach P (s, t) y →
      (I.dlts P s₀).Run (.running f s t) [] (.running f y.1 y.2) := by
  intro y h
  induction h with
  | refl => exact .nil _
  | tail _ hst ih =>
    have hstep : (I.dlts P s₀).Run (.running f _ _) [] (.running f _ _) :=
      .tau (DTrans.tau hst) (.nil _)
    exact ih.append hstep

/-- A folded transition is a silent run followed by the visible move. -/
theorem dlts_run_of_trans {s₀ : Store Nat} {q q' : I.HState} {m : Move I.E I.F}
    (h : I.Trans P q m q') : (I.dlts P s₀).Run q [m] q' := by
  cases h with
  | call s f => exact .vis (.call s f) (.nil _)
  | ucall run callout op =>
    exact (dlts_run_of_reach run).append (.vis (DTrans.ucall callout op) (.nil _))
  | uret v => exact .vis (.uret v) (.nil _)
  | oret run final answer =>
    exact (dlts_run_of_reach run).append (.vis (DTrans.oret final answer) (.nil _))

/-- A folded path is a run of the transition system with silent steps. -/
theorem dlts_run_of_path {s₀ : Store Nat} {q q' : I.HState} {p : List (Move I.E I.F)}
    (h : I.Path P q p q') : (I.dlts P s₀).Run q p q' := by
  induction h with
  | nil q => exact LTS.Run.nil (L := I.dlts P s₀) q
  | cons ht _ ih => exact (dlts_run_of_trans ht).append ih

/-- A folded state `q` lags behind the state `y` of the system with silent steps: they are
equal, or `y` is a running state reached from `q` by host-free steps. -/
def Lag (P : Profile) (q y : I.HState) : Prop :=
  q = y ∨ ∃ (f : I.F.Op) (s s' : Store Nat) (t t' : Thread),
    q = .running f s t ∧ y = .running f s' t' ∧ Reach P (s, t) (s', t')

/-- A lagging state that is not running is the state itself. -/
theorem Lag.eq_of_not_running {q y : I.HState} (h : Lag P q y)
    (hy : ∀ f s t, y ≠ .running f s t) : q = y := by
  rcases h with h | ⟨f, s, s', t, t', -, rfl, -⟩
  · exact h
  · exact absurd rfl (hy f s' t')

/-- Lagging behind a running state: the state is running the same question, and reaches the
other one by host-free steps. -/
theorem Lag.running {q : I.HState} {f : I.F.Op} {s' : Store Nat} {t' : Thread}
    (h : Lag P q (.running f s' t')) :
    ∃ s t, q = .running f s t ∧ Reach P (s, t) (s', t') := by
  rcases h with rfl | ⟨f₀, s, s₀, t, t₀, rfl, heq, hr⟩
  · exact ⟨s', t', rfl, .refl⟩
  · cases heq
    exact ⟨s, t, rfl, hr⟩

/-- A visible step of the system with silent steps from a state that `q` lags behind is a
folded transition from `q`. -/
theorem trans_of_lag {q y y' : I.HState} {m : Move I.E I.F} (hl : Lag P q y)
    (hs : I.DTrans P y (some m) y') : I.Trans P q m y' := by
  cases hs with
  | call s f =>
    have hq : q = .idle s := hl.eq_of_not_running fun _ _ _ h => by cases h
    exact hq ▸ .call s f
  | ucall callout op =>
    obtain ⟨s, t, rfl, hr⟩ := hl.running
    exact .ucall hr callout op
  | uret v =>
    have hq : q = .waiting _ _ _ _ := hl.eq_of_not_running fun _ _ _ h => by cases h
    exact hq ▸ .uret v
  | oret final answer =>
    obtain ⟨s, t, rfl, hr⟩ := hl.running
    exact .oret hr final answer

/-- A silent step keeps the lag. -/
theorem Lag.tau {q y y' : I.HState} (hl : Lag P q y) (hs : I.DTrans P y none y') :
    Lag P q y' := by
  cases hs with
  | tau hi =>
    obtain ⟨s, t, rfl, hr⟩ := hl.running
    exact .inr ⟨_, s, _, t, _, rfl, rfl, hr.tail hi⟩

/-- A run of the system with silent steps is a folded path, up to lag. -/
theorem path_of_dlts_run {s₀ : Store Nat} {y z : (I.dlts P s₀).State} {p : List (Move I.E I.F)}
    (h : (I.dlts P s₀).Run y p z) : ∀ q, Lag P q y → ∃ q', I.Path P q p q' ∧ Lag P q' z := by
  induction h with
  | nil x => exact fun q hl => ⟨q, .nil q, hl⟩
  | tau hs _ ih => exact fun q hl => ih q (hl.tau hs)
  | vis hs _ ih =>
    intro q hl
    obtain ⟨q', hq', hl'⟩ := ih _ (.inl rfl)
    exact ⟨q', .cons (trans_of_lag hl hs) hq', hl'⟩

/-- The traces of the system with silent steps are the plays. -/
theorem traces_dlts (P : Profile) (s : Store Nat) : (I.dlts P s).Traces = I.plays P s := by
  ext p
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨q', hq', -⟩ := path_of_dlts_run hy (.idle s) (.inl rfl)
    exact ⟨q', hq'⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, dlts_run_of_path hq⟩

/-- The system with silent steps denotes the strategy of the instance. -/
theorem denotes_dlts (P : Profile) (s : Store Nat) : (I.dlts P s).Denotes (I.strategy P s) := by
  intro p
  rw [traces_dlts, mem_strategy_iff]

/-- The finite plays of the divergence-observing strategy are the strategy. -/
theorem forget_dstrategy (P : Profile) (s : Store Nat) :
    (I.dstrategy P s).forget = I.strategy P s :=
  (denotes_dlts P s).ofLTS_eq

/-- The finite plays of the divergence-observing closed program are those of the closed
program. -/
theorem forget_closedD (P : Profile) (s : Store Nat) (K : Silmaril.Wasm.Game.Env I.E) :
    (I.closedD P s K).forget = I.closedWith P s K :=
  (LTS.Denotes.comp (Env.denotes_dlts K) (denotes_dlts P s)).ofLTS_eq

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
