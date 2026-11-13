module

public import Silmaril.Games.DivLTSComp.Thms
public import Silmaril.Games.Div.Thms

/-!
# Receptive completion of a transition system

`DStrategy.ofLTS_comp` needs transition systems that *denote* their strategies
(`LTS.Denotes`: traces are exactly the plays). The instantiable systems of
`Silmaril.Games.Inst` refuse some legal Opponent moves (an export call before
instantiation, a second instantiation question, anything after a failure), which
`Strategy.ofLTS` adds by receptiveness. Given a map of states to game positions
(`PosMap`), `complete L pos` adds to every state a step to a stuck sink for every
legal Opponent move. Then:

* `denotes_complete`: the completion denotes `Strategy.ofLTS L`;
* `ofLTS_complete`: the completion has the divergence-observing strategy of `L`
  (sinks never move, so no divergence or infinite run is added);
* `silentRunning_complete`: it takes silent steps only in running positions when `L`
  does.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.LinkStartDiv

open Silmaril.Games

universe u

variable {E F : Sig.{u}}

/-- Steps of the receptive completion: the steps of `L`, and from every state a step to a
sink for every legal Opponent move. -/
inductive CStep (L : LTS E F) (pos : L.State → Pos E F) :
    L.State ⊕ Pos E F → Option (Move E F) → L.State ⊕ Pos E F → Prop
  /-- A step of `L`. -/
  | base {x : L.State} {l : Option (Move E F)} {y : L.State} :
      L.step x l y → CStep L pos (.inl x) l (.inl y)
  /-- A legal Opponent move into a sink. -/
  | sink {x : L.State} {o : Move E F} {p : Pos E F} :
      o.IsO → Step (pos x) o p → CStep L pos (.inl x) (some o) (.inr p)

/-- The receptive completion of `L` along `pos`. -/
@[reducible] def complete (L : LTS E F) (pos : L.State → Pos E F) : LTS E F :=
  ⟨L.State ⊕ Pos E F, .inl L.init, CStep L pos⟩

/-- `pos` follows the game: initially idle, visible steps are game steps, silent steps keep
the position. -/
structure PosMap (L : LTS E F) (pos : L.State → Pos E F) : Prop where
  init : pos L.init = .idle
  vis : ∀ {x y : L.State} {o : Move E F}, L.step x (some o) y → Step (pos x) o (pos y)
  tau : ∀ {x y : L.State}, L.step x none y → pos y = pos x

variable {L : LTS E F} {pos : L.State → Pos E F}

/-! ## Runs of the completion -/

/-- A state without steps starts only the empty run. -/
theorem run_stuck {C : LTS E F} {x z : C.State} {w : List (Move E F)}
    (hx : ∀ l y, ¬ C.step x l y) (h : C.Run x w z) : w = [] ∧ z = x := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | tau hs _ => exact (hx _ _ hs).elim
  | vis hs _ => exact (hx _ _ hs).elim

/-- Induction on runs, for a transition system given by a term. -/
theorem run_ind {C : LTS E F} (Pr : C.State → List (Move E F) → C.State → Prop)
    {x z : C.State} {w : List (Move E F)} (h : C.Run x w z) (hnil : ∀ x, Pr x [] x)
    (htau : ∀ {x y z s}, C.step x none y → C.Run y s z → Pr y s z → Pr x s z)
    (hvis : ∀ {x y z o s}, C.step x (some o) y → C.Run y s z → Pr y s z → Pr x (o :: s) z) :
    Pr x w z := by
  induction h with
  | nil => exact hnil _
  | tau hs hr ih => exact htau hs hr ih
  | vis hs hr ih => exact hvis hs hr ih

/-- A sink does not move. -/
theorem run_inr {p : Pos E F} {w : List (Move E F)} {z : (complete L pos).State}
    (h : (complete L pos).Run (.inr p) w z) : w = [] ∧ z = .inr p :=
  run_stuck (fun _ _ hs => by cases hs) h

/-- Runs of `L` are runs of the completion. -/
theorem run_lift {x y : L.State} {w : List (Move E F)} (h : L.Run x w y) :
    (complete L pos).Run (.inl x) w (.inl y) := by
  induction h with
  | nil x => exact .nil _
  | tau hs _ ih => exact .tau (CStep.base hs) ih
  | vis hs _ ih => exact .vis (CStep.base hs) ih

/-- A run of the completion between states of `L` is a run of `L`. -/
theorem run_inl_inl {x y : L.State} {w : List (Move E F)}
    (h : (complete L pos).Run (.inl x) w (.inl y)) : L.Run x w y := by
  refine run_ind (C := complete L pos)
    (fun x' w y' => ∀ a b, x' = .inl a → y' = .inl b → L.Run a w b) h ?_ ?_ ?_ x y rfl rfl
  · rintro x' a b rfl hb
    cases hb
    exact .nil _
  · intro x₁ y₁ z₁ s hs hr ih a b ha hb
    subst ha
    cases hs with
    | base hb' => exact .tau hb' (ih _ b rfl hb)
  · intro x₁ y₁ z₁ o s hs hr ih a b ha hb
    subst ha
    cases hs with
    | base hb' => exact .vis hb' (ih _ b rfl hb)
    | sink _ _ =>
      subst hb
      exact absurd (run_inr hr).2 (by simp)

/-- What a run of the completion into the sink `p` is made of. -/
def SinkRun (L : LTS E F) (pos : L.State → Pos E F) (p : Pos E F) (x : L.State)
    (w : List (Move E F)) : Prop :=
  ∃ w₀ x' o, w = w₀ ++ [o] ∧ L.Run x w₀ x' ∧ o.IsO ∧ Step (pos x') o p

/-- A visible step into a sink ends the run. -/
theorem sinkRun_sink {x : L.State} {o : Move E F} {q p : Pos E F} {s : List (Move E F)}
    (ho : o.IsO) (hst : Step (pos x) o q) (hr : (complete L pos).Run (.inr q) s (.inr p)) :
    SinkRun L pos p x (o :: s) := by
  obtain ⟨hs', hq⟩ := run_inr hr
  have hpq : q = p := Sum.inr.inj hq.symm
  subst hs' hpq
  exact ⟨[], x, o, rfl, .nil _, ho, hst⟩

/-- A step of `L` before a run into a sink. -/
theorem sinkRun_cons {x y : L.State} {l : Option (Move E F)} {p : Pos E F} {s : List (Move E F)}
    (hb : L.step x l y) (ih : SinkRun L pos p y s) : SinkRun L pos p x (l.toList ++ s) := by
  obtain ⟨w₀, x', o, rfl, hr₀, ho, hst⟩ := ih
  cases l with
  | none => exact ⟨w₀, x', o, rfl, .tau hb hr₀, ho, hst⟩
  | some o₁ => exact ⟨o₁ :: w₀, x', o, rfl, .vis hb hr₀, ho, hst⟩

/-- A run of the completion into a sink is a run of `L` followed by a legal Opponent move. -/
theorem run_inl_inr {x : L.State} {p : Pos E F} {w : List (Move E F)}
    (h : (complete L pos).Run (.inl x) w (.inr p)) :
    ∃ w₀ x' o, w = w₀ ++ [o] ∧ L.Run x w₀ x' ∧ o.IsO ∧ Step (pos x') o p := by
  refine run_ind (C := complete L pos)
    (fun x₀ w z => ∀ a, x₀ = .inl a → z = .inr p → SinkRun L pos p a w) h ?_ ?_ ?_ x rfl rfl
  · rintro x' a rfl h
    cases h
  · intro x₁ y₁ z₁ s hs hr ih a ha hz
    subst ha
    cases hs with
    | base hb => exact sinkRun_cons (l := none) hb (ih _ rfl hz)
  · intro x₁ y₁ z₁ o₁ s hs hr ih a ha hz
    subst ha hz
    cases hs with
    | base hb => exact sinkRun_cons (l := some o₁) hb (ih _ rfl rfl)
    | sink ho hst => exact sinkRun_sink ho hst hr

/-! ## The completion denotes the strategy of `L` -/

variable (hm : PosMap L pos)
include hm

theorem path_run {x y : L.State} {w : List (Move E F)} (h : L.Run x w y) :
    Path (pos x) w (pos y) :=
  LTS.path_of_run_pos pos hm.vis hm.tau h

theorem legal_trace {w : List (Move E F)} (h : w ∈ L.Traces) : Legal w := by
  obtain ⟨y, hy⟩ := h
  have hp : Path (pos L.init) w (pos y) := path_run hm hy
  rw [hm.init] at hp
  exact ⟨_, hp⟩

/-- A trace of the completion is a play of `Strategy.ofLTS L`. -/
theorem complete_traces_sub {w : List (Move E F)} (h : w ∈ (complete L pos).Traces) :
    w ∈ Strategy.ofLTS L := by
  obtain ⟨z, hz⟩ := h
  cases z with
  | inl y =>
    have hw : w ∈ L.Traces := ⟨y, run_inl_inl hz⟩
    exact Strategy.mem_ofLTS_of_mem_traces hw (legal_trace hm hw)
  | inr p =>
    obtain ⟨w₀, x', o, rfl, hr₀, ho, hst⟩ := run_inl_inr hz
    have hw₀ : w₀ ∈ L.Traces := ⟨x', hr₀⟩
    have hmem : w₀ ∈ Strategy.ofLTS L := Strategy.mem_ofLTS_of_mem_traces hw₀ (legal_trace hm hw₀)
    have hp : Path (pos L.init) w₀ (pos x') := path_run hm hr₀
    rw [hm.init] at hp
    exact (Strategy.ofLTS L).receptive hmem hp hst ho

/-- A play of `Strategy.ofLTS L` is a trace of the completion. -/
theorem sub_complete_traces {w : List (Move E F)} (h : w ∈ Strategy.ofLTS L) :
    w ∈ (complete L pos).Traces := by
  obtain ⟨hl, s, hs, hp⟩ := h
  have hsT : s ∈ L.Traces := by
    rcases hs with rfl | ⟨hs, -⟩
    · exact ⟨L.init, .nil _⟩
    · exact hs
  rcases hp with hpre | ⟨p₀, o, rfl, hp₀, ho⟩
  · obtain ⟨y, hy⟩ := LTS.traces_of_prefix hsT hpre
    exact ⟨.inl y, run_lift hy⟩
  · obtain ⟨x, hx⟩ := LTS.traces_of_prefix hsT hp₀
    obtain ⟨q, hq⟩ := hl
    obtain ⟨x', hx', hst⟩ := Path.concat_iff.1 hq
    have hpx : Path (pos L.init) p₀ (pos x) := path_run hm hx
    rw [hm.init] at hpx
    have he : x' = pos x := Path.det hx' hpx
    subst he
    exact ⟨.inr q, (run_lift hx).append (.vis (CStep.sink ho hst) (.nil _))⟩

/-- **The completion denotes the strategy of `L`.** -/
theorem denotes_complete : (complete L pos).Denotes (Strategy.ofLTS L) :=
  fun _ => ⟨complete_traces_sub hm, sub_complete_traces hm⟩

/-! ## The completion has the divergence-observing strategy of `L` -/

omit hm in
/-- Divergence in the completion is divergence of `L`. -/
theorem diverges_iff {x : L.State} :
    (complete L pos).Diverges (.inl x) ↔ L.Diverges x := by
  constructor
  · intro h
    refine Silmaril.InfiniteTrace.of_map (R := L.Silent) (S := (complete L pos).Silent)
      Sum.inl (fun _ => True) ?_ trivial h
    intro a b _ hab
    cases hab with
    | base hb => exact ⟨_, hb, trivial, rfl⟩
  · intro h
    exact Silmaril.InfiniteTrace.map (R := L.Silent) (S := (complete L pos).Silent) Sum.inl
      (fun _ _ hab => CStep.base hab) h

omit hm in
theorem divTraces_complete : (complete L pos).DivTraces = L.DivTraces := by
  ext s
  constructor
  · rintro ⟨y, hr, hd⟩
    cases y with
    | inl x => exact ⟨x, run_inl_inl hr, diverges_iff.1 hd⟩
    | inr p =>
      obtain ⟨_, hst, -⟩ := hd.unfold
      cases hst
  · rintro ⟨x, hr, hd⟩
    exact ⟨.inl x, run_lift hr, diverges_iff.2 hd⟩

omit hm in
/-- After a sink, an infinite run of the completion stays put. -/
theorem infRun_sink (r : (complete L pos).InfRun) {n : ℕ} {p : Pos E F}
    (hn : r.st n = .inr p) : ∀ k, r.st (n + k) = .inr p ∧ r.tr (n + k) = r.tr n := by
  intro k
  induction k with
  | zero => exact ⟨hn, rfl⟩
  | succ k ih =>
    obtain ⟨w, hw, hr⟩ := r.step (n + k)
    rw [ih.1] at hr
    obtain ⟨rfl, hz⟩ := run_inr hr
    exact ⟨hz, by rw [← Nat.add_assoc, hw, List.append_nil, ih.2]⟩

omit hm in
/-- An unbounded infinite run of the completion never enters a sink. -/
theorem infRun_inl (r : (complete L pos).InfRun) (hu : r.tr.Unbounded) (n : ℕ) :
    ∃ x, r.st n = .inl x := by
  cases hs : r.st n with
  | inl x => exact ⟨x, rfl⟩
  | inr p =>
    exfalso
    obtain ⟨m, hm', hlen⟩ := Chain.Mono.unbounded_ge r.mono hu ((r.tr n).length + 1) n
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm'
    rw [(infRun_sink r hs k).2] at hlen
    omega

omit hm in
/-- The state of `L` of a state of the completion. -/
def getL : L.State ⊕ Pos E F → L.State := Sum.elim id (fun _ => L.init)

omit hm in
theorem infTraces_complete : (complete L pos).InfTraces = L.InfTraces := by
  ext I
  constructor
  · rintro ⟨r, hu, rfl⟩
    have hst : ∀ n, r.st n = .inl (getL (r.st n)) := fun n => by
      obtain ⟨x, hx⟩ := infRun_inl r hu n
      rw [hx]
      rfl
    have h0 : getL (L := L) (r.st 0) = L.init := by rw [r.st_zero]; rfl
    refine ⟨⟨fun n => getL (r.st n), r.tr, h0, r.tr_zero, fun n => ?_⟩, hu, rfl⟩
    obtain ⟨w, hw, hr⟩ := r.step n
    rw [hst n, hst (n + 1)] at hr
    exact ⟨w, hw, run_inl_inl hr⟩
  · rintro ⟨r, hu, rfl⟩
    have h0 : (Sum.inl (r.st 0) : (complete L pos).State) = .inl L.init := by rw [r.st_zero]
    refine ⟨⟨fun n => .inl (r.st n), r.tr, h0, r.tr_zero, fun n => ?_⟩, hu, rfl⟩
    obtain ⟨w, hw, hr⟩ := r.step n
    exact ⟨w, hw, run_lift hr⟩

/-- **The completion has the divergence-observing strategy of `L`.** -/
theorem ofLTS_complete : DStrategy.ofLTS (complete L pos) = DStrategy.ofLTS L := by
  apply DStrategy.ext
  · exact (denotes_complete hm).ofLTS_eq
  · show {s | s ∈ (complete L pos).DivTraces ∧ _} = {s | s ∈ L.DivTraces ∧ _}
    rw [divTraces_complete]
  · show {I | I ∈ (complete L pos).InfTraces ∧ _} = {I | I ∈ L.InfTraces ∧ _}
    rw [infTraces_complete]

/-- **Silent steps of the completion happen only in running positions** when those of `L`
do. -/
theorem silentRunning_complete (hrun : ∀ {x y : L.State}, L.step x none y → ∃ q, pos x = .run q) :
    (complete L pos).SilentRunning := by
  refine LTS.silentRunning_of_pos (L := complete L pos) (Sum.elim pos id) ?_ ?_ ?_ ?_
  · exact hm.init
  · intro x y o h
    cases h with
    | base hb => exact hm.vis hb
    | sink _ hst => exact hst
  · intro x y h
    cases h with
    | base hb => exact hm.tau hb
  · intro x y h
    cases h with
    | base hb => exact hrun hb

end Silmaril.Proofs.Wasm.Game.LinkStartDiv
