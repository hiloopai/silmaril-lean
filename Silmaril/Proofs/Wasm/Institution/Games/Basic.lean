module

public import Silmaril.Wasm.Institution.Games.Defs

@[expose] public section

/-!
# Reduction semantics versus game semantics: proofs

Validity in the strategy logics, the trace reading of reduction validity, simulation as a source
of valid refinement sentences (borrowed into the game logic), and a two-move adequacy theorem
for the Wasm reduction `wasmRed`. Summary in `Silmaril.Wasm.Institution.Games.Thms`.
-/

namespace Silmaril.Wasm.Institution.Games

open CategoryTheory ObsSemantics

variable (G : GameIfaces) (E : Silmaril.Games.Sig.{0})

/-- Validity of `p ⊑ q` at `X` is refinement of the restricted strategies. -/
theorem valid_leSen_iff {P : Type} (s : P → Silmaril.Games.Strategy E (G.sig G.top)) (X : G.I)
    (p q : P) :
    (G.stratSem E P s).Valid ((G.stratSem E P s).leSen X p q) ↔
      G.res E (G.toTop X) (s p) ≤ G.res E (G.toTop X) (s q) :=
  (G.stratSem E P s).valid_leSen_iff X p q

/-- At the top interface, validity of `p ⊑ q` is refinement of the denoted strategies. -/
theorem valid_top_iff {P : Type} (s : P → Silmaril.Games.Strategy E (G.sig G.top)) (p q : P) :
    (G.stratSem E P s).Valid ((G.stratSem E P s).leSen G.top p q) ↔ s p ≤ s q := by
  rw [valid_leSen_iff, G.toTop_top, G.res_id, G.res_id]

/-- Refinement at the top interface gives refinement at every interface (hiding). -/
theorem valid_of_top {P : Type} (s : P → Silmaril.Games.Strategy E (G.sig G.top)) {p q : P}
    (h : s p ≤ s q) (X : G.I) :
    (G.stratSem E P s).Valid ((G.stratSem E P s).leSen X p q) :=
  (valid_leSen_iff G E s X p q).2 (Silmaril.Games.Strategy.restrict_mono h _)

variable {RProg : Type}

/-- **Trace reading of reduction validity**: `p ⊑ q` is valid at the top interface iff every
legal trace of `red p` is a play of the strategy of `red q`. -/
theorem valid_red_top_iff_traces (red : RProg → Silmaril.Games.Reduction E (G.sig G.top))
    (p q : RProg) :
    (redSem G E red).Valid ((redSem G E red).leSen G.top p q) ↔
      ∀ t ∈ (red p).toLTS.Traces, Silmaril.Games.Legal t →
        t ∈ Silmaril.Games.Strategy.ofReduction (red q) :=
  (valid_top_iff G E _ p q).trans Silmaril.Games.Strategy.ofLTS_le_iff

/-- **Forward simulation gives valid refinement sentences** of the reduction logic, at every
interface. -/
theorem valid_of_simulation (red : RProg → Silmaril.Games.Reduction E (G.sig G.top)) {p q : RProg}
    (S : (red p).Simulation (red q)) (X : G.I) :
    (redSem G E red).Valid ((redSem G E red).leSen X p q) :=
  valid_of_top G E (fun p => Silmaril.Games.Strategy.ofReduction (red p)) S.ofReduction_le X

/-- **... and, by borrowing along `redToGame`, valid refinement sentences of the game logic**
between the strategies of the two programs. -/
theorem valid_game_of_simulation (red : RProg → Silmaril.Games.Reduction E (G.sig G.top))
    {p q : RProg} (S : (red p).Simulation (red q)) (X : G.I) :
    (gameSem G E).Valid ((redToGame G E red).sen ((redSem G E red).leSen X p q)) :=
  ((redToGame G E red).valid_iff (stratT_surjective G E _ _) _).1
    (valid_of_simulation G E red S X)

/-- The same for transition systems. -/
theorem valid_game_of_ltsSimulation (lts : RProg → Silmaril.Games.LTS E (G.sig G.top))
    {p q : RProg} (S : (lts p).Simulation (lts q)) (X : G.I) :
    (gameSem G E).Valid ((ltsToGame G E lts).sen ((ltsSem G E lts).leSen X p q)) :=
  ((ltsToGame G E lts).valid_iff (stratT_surjective G E _ _) _).1
    (valid_of_top G E (fun p => Silmaril.Games.Strategy.ofLTS (lts p)) S.ofLTS_le X)

/-! ## Two-move plays of reduction strategies -/

section TwoMove

variable {F : Silmaril.Games.Sig.{0}}

theorem run_ans_aux {R : Silmaril.Games.Reduction E F} {q : F.Op} {b : F.Ar q} :
    ∀ {x : R.toLTS.State} {s : List (Silmaril.Games.Move E F)} {y : R.toLTS.State},
      R.toLTS.Run x s y → ∀ (c : R.Conf q) (rest : List (Silmaril.Games.Move E F)),
      x = .run q c → s = .inr (.ans q b) :: rest →
      ∃ c', Relation.ReflTransGen R.step c c' ∧ R.done c' b := by
  intro x s y h
  induction h with
  | nil => intro c rest _ hs; cases hs
  | tau hstep _ ih =>
    intro c rest hx hs
    subst hx
    change R.Step _ _ _ at hstep
    cases hstep with
    | tau h' =>
      obtain ⟨c'', h₁, h₂⟩ := ih _ rest rfl hs
      exact ⟨c'', .head h' h₁, h₂⟩
  | vis hstep _ _ =>
    intro c rest hx hs
    subst hx
    change R.Step _ _ _ at hstep
    simp only [List.cons.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    cases hstep with
    | ret hd => exact ⟨_, .refl, hd⟩

/-- A run from a running configuration whose first visible move is the answer `b` reduces
internally to a configuration answering `b`. -/
theorem run_ans {R : Silmaril.Games.Reduction E F} {q : F.Op} {c : R.Conf q} {b : F.Ar q}
    {rest : List (Silmaril.Games.Move E F)} {y : R.toLTS.State}
    (h : R.toLTS.Run (.run q c) (.inr (.ans q b) :: rest) y) :
    ∃ c', Relation.ReflTransGen R.step c c' ∧ R.done c' b :=
  run_ans_aux E h c rest rfl rfl

/-- The two-move play "ask `q`, answer `b`" does not end with an Opponent move. -/
private theorem ask_ans_ne_concat_O {q : F.Op} {b : F.Ar q} {p₀ : List (Silmaril.Games.Move E F)}
    {o : Silmaril.Games.Move E F} (he : [.inr (.ask q), .inr (.ans q b)] = p₀ ++ [o])
    (ho : Silmaril.Games.Move.IsO o) : False := by
  have hlast : o = .inr (.ans q b) := by simpa using (congrArg List.getLast? he).symm
  have ho' : Silmaril.Games.Move.IsO (.inr (.ans q b) : Silmaril.Games.Move E F) := hlast ▸ ho
  exact ho'

/-- A run from the idle state starting with "ask `q`, answer `b`" reduces the start
configuration of `q` internally to one answering `b`. -/
private theorem run_idle_ask_ans {R : Silmaril.Games.Reduction E F} {q : F.Op} {b : F.Ar q}
    {u s : List (Silmaril.Games.Move E F)} {x y : R.toLTS.State} (hrun : R.toLTS.Run x s y)
    (hx : x = .idle) (hs : s = [.inr (.ask q), .inr (.ans q b)] ++ u) :
    ∃ c', Relation.ReflTransGen R.step (R.start q) c' ∧ R.done c' b := by
  cases hrun with
  | nil => cases hs
  | tau hstep _ =>
    have hstep' : R.Step .idle none _ := hx ▸ hstep
    cases hstep'
  | vis hstep hrun' =>
    have hstep' : R.Step .idle (some _) _ := hx ▸ hstep
    cases hstep' with
    | ask q' =>
      obtain ⟨hq, hs'⟩ := List.cons.inj hs
      cases hq
      exact run_ans E (hs' ▸ hrun')

/-- The forward direction of `mem_ofReduction_ask_ans`. -/
private theorem reduces_of_mem_ask_ans {R : Silmaril.Games.Reduction E F} {q : F.Op} {b : F.Ar q}
    (h : [.inr (.ask q), .inr (.ans q b)] ∈ Silmaril.Games.Strategy.ofReduction R) :
    ∃ c', Relation.ReflTransGen R.step (R.start q) c' ∧ R.done c' b := by
  obtain ⟨-, t, ht, hp⟩ := h
  rcases ht with ht₀ | ⟨⟨y, hrun⟩, -⟩
  · rcases hp with hp | ⟨p₀, o, he, -, ho⟩
    · exact absurd (ht₀ ▸ hp).length_le (by simp)
    · exact (ask_ans_ne_concat_O E he ho).elim
  · rcases hp with ⟨u, hu⟩ | ⟨p₀, o, he, -, ho⟩
    · exact run_idle_ask_ans E hrun rfl hu.symm
    · exact (ask_ans_ne_concat_O E he ho).elim

/-- The backward direction of `mem_ofReduction_ask_ans`. -/
private theorem mem_ask_ans_of_reduces {R : Silmaril.Games.Reduction E F} {q : F.Op} {b : F.Ar q}
    {c' : R.Conf q} (hc' : Relation.ReflTransGen R.step (R.start q) c') (hd : R.done c' b) :
    [.inr (.ask q), .inr (.ans q b)] ∈ Silmaril.Games.Strategy.ofReduction R := by
  have hrun : ∀ c₀, Relation.ReflTransGen R.step c₀ c' →
      R.toLTS.Run (.run q c₀) [.inr (.ans q b)] .idle := by
    intro c₀ h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .vis (Silmaril.Games.Reduction.Step.ret hd) (.nil _)
    | head h₁ _ ih => exact .tau (Silmaril.Games.Reduction.Step.tau h₁) ih
  exact Silmaril.Games.Strategy.mem_ofLTS_of_mem_traces
    ⟨.idle, .vis (Silmaril.Games.Reduction.Step.ask q) (hrun _ hc')⟩
    ⟨.idle, .cons (.ask q) (.cons (.ret q b) (.nil _))⟩

/-- **Two-move plays of a reduction strategy**: the play "ask `q`, answer `b`" belongs to
`ofReduction R` iff the start configuration of `q` reduces internally to one answering `b`. -/
theorem mem_ofReduction_ask_ans {R : Silmaril.Games.Reduction E F} {q : F.Op} {b : F.Ar q} :
    [.inr (.ask q), .inr (.ans q b)] ∈ Silmaril.Games.Strategy.ofReduction R ↔
      ∃ c', Relation.ReflTransGen R.step (R.start q) c' ∧ R.done c' b :=
  ⟨reduces_of_mem_ask_ans E, fun ⟨_, hc', hd⟩ => mem_ask_ans_of_reduces E hc' hd⟩

end TwoMove



end Silmaril.Wasm.Institution.Games
