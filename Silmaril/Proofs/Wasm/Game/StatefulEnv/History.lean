module

public import Silmaril.Proofs.Wasm.Game.StatefulEnv.Runs
public import Silmaril.Proofs.Wasm.Game.Env.Basic

/-!
# Stateless and history machines: proofs

* `strategy_ofEnv`, `hostAt_ofEnv`, `sbehavioursOf_ofEnv`: a stateless
  environment `K` is the one-state machine `ofEnv K`: same strategy, and the
  product semantics is Core reduction under `hostOf ts K`.
* `sbehavioursOf_eq_behavioursOf`: more generally, against a machine with at
  most one state the product semantics is Core reduction under the
  (nondeterministic, stateless) host `L.hostAt q`.
* `strategy_ofStrategy`: every environment strategy `τ : Strategy Sig.empty E`
  is the strategy of its history machine, so stateful environments are
  exactly the environment strategies.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SEnv

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core

variable {E : Sig.{0}}

/-! ### Stateless environments -/

theorem agrees_of_agrees_ofEnv (K : Silmaril.Wasm.Game.Env E) :
    ∀ {q : Unit} {u : List (Ev E)}, (Silmaril.Wasm.Game.SEnv.ofEnv K).Agrees q u → K.Agrees u
  | _, [], _ => .nil
  | _, [_], h => by
    rcases h with _ | ⟨_, e⟩
    exact .pending e
  | _, _ :: _ :: _, h => by
    rcases h with _ | _ | ⟨ha, hr⟩
    exact .answered ha (agrees_of_agrees_ofEnv K hr)

theorem agrees_ofEnv_iff (K : Silmaril.Wasm.Game.Env E) {q : Unit} {u : List (Ev E)} :
    (Silmaril.Wasm.Game.SEnv.ofEnv K).Agrees q u ↔ K.Agrees u := by
  constructor
  · exact agrees_of_agrees_ofEnv K
  · intro h
    induction h generalizing q with
    | nil => exact Silmaril.Wasm.Game.SEnv.Agrees.nil (L := Silmaril.Wasm.Game.SEnv.ofEnv K) q
    | pending e => exact Silmaril.Wasm.Game.SEnv.Agrees.pending (L := Silmaril.Wasm.Game.SEnv.ofEnv K) q e
    | answered ha _ ih =>
      exact Silmaril.Wasm.Game.SEnv.Agrees.answered (L := Silmaril.Wasm.Game.SEnv.ofEnv K) (q' := ())
        ha ih

/-- The one-state machine of `K` has the strategy of `K`. -/
theorem strategy_ofEnv (K : Silmaril.Wasm.Game.Env E) :
    (Silmaril.Wasm.Game.SEnv.ofEnv K).strategy () = K.strategy := by
  ext p
  rw [mem_strategy_iff, Env.mem_strategy_iff]
  simp only [agrees_ofEnv_iff]

/-- The host of the one-state machine of `K` is the host induced by `K`. -/
theorem hostAt_ofEnv {ts : List FnType} (K : Silmaril.Wasm.Game.Env (ifaceSig ts)) :
    (Silmaril.Wasm.Game.SEnv.ofEnv K).hostAt () = hostOf ts K := by
  funext h s args out
  apply propext
  constructor
  · rintro ⟨e, he, ⟨w, _, hw, rfl⟩ | ⟨hs, rfl⟩⟩
    · exact ⟨e, he, Or.inl ⟨w, hw, rfl⟩⟩
    · rcases hs with hf | hn
      · exact hf.elim
      · exact ⟨e, he, Or.inr ⟨fun w hw => hn w () hw, rfl⟩⟩
  · rintro ⟨e, he, ⟨w, hw, rfl⟩ | ⟨hn, rfl⟩⟩
    · exact ⟨e, he, Or.inl ⟨w, (), hw, rfl⟩⟩
    · exact ⟨e, he, Or.inr ⟨Or.inr fun w _ hw => hn w hw, rfl⟩⟩

theorem throwsBelow_ofEnv {ts : List FnType} (K : Silmaril.Wasm.Game.Env (ifaceSig ts)) (n : Nat) :
    (Silmaril.Wasm.Game.SEnv.ofEnv K).ThrowsBelow n ↔ ThrowsBelow K n :=
  ⟨fun h e w hw => h () e w () hw, fun h _ e w _ hw => h e w hw⟩

/-! ### Machines with at most one state -/

section OneState

variable {ts : List FnType} {P : Profile} {L : Silmaril.Wasm.Game.SEnv (ifaceSig ts)}

theorem sstep_core_of_subsingleton [Subsingleton L.S] (q : L.S) {x y : Config Nat × L.S}
    (h : SStep P L x y) : Execution.Core.Step P (L.hostAt q) x.1 y.1 := by
  obtain ⟨c, qx⟩ := x
  obtain ⟨c', qy⟩ := y
  obtain rfl : qx = q := Subsingleton.elim _ _
  exact SStep.core_step h

theorem ssteps_core_of_subsingleton [Subsingleton L.S] (q : L.S) {x y : Config Nat × L.S}
    (h : SSteps P L x y) : Steps P (L.hostAt q) x.1 y.1 := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (sstep_core_of_subsingleton q hst)

theorem sstep_of_core_subsingleton [Subsingleton L.S] {q : L.S} {c c' : Config Nat}
    (h : Execution.Core.Step P (L.hostAt q) c c') : SStep P L (c, q) (c', q) := by
  obtain ⟨q', hq'⟩ := core_step_sstep h
  obtain rfl : q' = q := Subsingleton.elim _ _
  exact hq'

theorem ssteps_of_core_subsingleton [Subsingleton L.S] {q : L.S} {c c' : Config Nat}
    (h : Steps P (L.hostAt q) c c') : SSteps P L (c, q) (c', q) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (sstep_of_core_subsingleton hst)

/-- **One host state: the product semantics is Core reduction** under the stateless (possibly
nondeterministic) host `L.hostAt q`. -/
theorem sbehavioursOf_eq_behavioursOf [Subsingleton L.S] (q : L.S) (c : Config Nat) :
    sbehavioursOf P L q c = behavioursOf P (L.hostAt q) c := by
  ext b
  constructor
  · rintro (⟨c', q', r, run, final, rfl⟩ | ⟨rfl, hinf⟩)
    · exact Or.inl ⟨c', r, ssteps_core_of_subsingleton q run, final, rfl⟩
    · exact Or.inr ⟨rfl, InfiniteTrace.map Prod.fst
        (fun _ _ h => sstep_core_of_subsingleton q h) hinf⟩
  · rintro (⟨c', r, run, final, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact Or.inl ⟨c', q, r, ssteps_of_core_subsingleton run, final, rfl⟩
    · exact Or.inr ⟨rfl, InfiniteTrace.map (fun c => (c, q))
        (fun _ _ h => sstep_of_core_subsingleton h) hdiv⟩

/-- One host state: infinite product runs are Core divergence under `L.hostAt q`. -/
theorem sinfinite_iff_diverges [Subsingleton L.S] (q : L.S) (c : Config Nat) :
    InfiniteTrace (SStep P L) (c, q) ↔ Diverges P (L.hostAt q) c :=
  ⟨fun h => InfiniteTrace.map Prod.fst (fun _ _ h => sstep_core_of_subsingleton q h) h,
    fun h => InfiniteTrace.map (fun c => (c, q)) (fun _ _ h => sstep_of_core_subsingleton h) h⟩

/-- For the one-state machine of `K` the product semantics is Core reduction under
`hostOf ts K`. -/
theorem sbehavioursOf_ofEnv (K : Silmaril.Wasm.Game.Env (ifaceSig ts)) (c : Config Nat) :
    sbehavioursOf P (Silmaril.Wasm.Game.SEnv.ofEnv K) () c = behavioursOf P (hostOf ts K) c := by
  have hsub : Subsingleton (Silmaril.Wasm.Game.SEnv.ofEnv K).S := inferInstanceAs (Subsingleton Unit)
  rw [sbehavioursOf_eq_behavioursOf, hostAt_ofEnv]

end OneState

/-! ### History machines -/

section History

variable {τ : Strategy Sig.empty E}

/-- After an idle history, the next upper move of a legal extension is a question, and the
one after it its answer. -/
private theorem path_after_idle {u v : List (Ev E)}
    (hu : Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) .idle)
    (hl : Legal ((u ++ v).map .inr : List (Move Sig.empty E))) :
    ∃ y, Silmaril.Games.Path .idle (v.map .inr : List (Move Sig.empty E)) y := by
  obtain ⟨y, hy⟩ := hl
  have hy' : Silmaril.Games.Path .idle
      ((u.map .inr : List (Move Sig.empty E)) ++ v.map .inr) y := by simpa using hy
  obtain ⟨x, hx, hxy⟩ := Path.append_iff.1 hy'
  obtain rfl : x = .idle := Path.det hx hu
  exact ⟨y, hxy⟩

private theorem path_snoc_pair {u : List (Ev E)} {e : E.Op} {w : E.Ar e}
    (hu : Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) .idle) :
    Silmaril.Games.Path .idle ((u ++ ([.ask e, .ans e w] : List (Ev E))).map .inr :
      List (Move Sig.empty E))
      .idle := by
  have h2 : Silmaril.Games.Path .idle
      (([.ask e, .ans e w] : List (Ev E)).map .inr : List (Move Sig.empty E)) .idle :=
    .cons (.ask e) (.cons (.ret e w) (.nil _))
  simpa using Path.append hu h2

/-- Agreement of one question after an idle history `u` of `τ`. -/
private theorem agrees_ofStrategy_single {u : List (Ev E)} {x : Ev E}
    (hu : (u.map .inr : List (Move Sig.empty E)) ∈ τ)
    (hpu : Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) .idle) :
    (Silmaril.Wasm.Game.SEnv.ofStrategy τ).Agrees u [x] ↔
      ((u ++ [x]).map .inr : List (Move Sig.empty E)) ∈ τ := by
  constructor
  · intro h
    rcases h with _ | ⟨_, e⟩
    have hr : (u.map .inr : List (Move Sig.empty E)) ++ [.inr (.ask e)] ∈ τ :=
      τ.receptive hu hpu (.ask e) trivial
    simpa using hr
  · intro hx
    obtain ⟨z, hz⟩ := path_after_idle hpu (τ.legal hx)
    cases hz with
    | cons hs _ =>
      cases hs
      exact Silmaril.Wasm.Game.SEnv.Agrees.pending (L := Silmaril.Wasm.Game.SEnv.ofStrategy τ) u _

/-- The rest-agreement hypothesis of `agrees_ofStrategy_pair`: agreement of `rest` after
every idle history of `τ` is membership. -/
private def RestAgrees (τ : Strategy Sig.empty E) (rest : List (Ev E)) : Prop :=
  ∀ u' : List (Ev E), (u'.map .inr : List (Move Sig.empty E)) ∈ τ →
    Silmaril.Games.Path .idle (u'.map .inr : List (Move Sig.empty E)) .idle →
    ((Silmaril.Wasm.Game.SEnv.ofStrategy τ).Agrees u' rest ↔
      ((u' ++ rest).map .inr : List (Move Sig.empty E)) ∈ τ)

/-- Agreement of an answered call and more, forwards. -/
private theorem agrees_ofStrategy_pair_mp {u rest : List (Ev E)} {x y : Ev E}
    (hpu : Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) .idle)
    (hih : RestAgrees τ rest)
    (h : (Silmaril.Wasm.Game.SEnv.ofStrategy τ).Agrees u (x :: y :: rest)) :
    ((u ++ x :: y :: rest).map .inr : List (Move Sig.empty E)) ∈ τ := by
  obtain ⟨e, w, rfl, rfl, hmem, hrest⟩ : ∃ e w, x = .ask e ∧ y = .ans e w ∧
      ((u ++ ([.ask e, .ans e w] : List (Ev E))).map .inr : List (Move Sig.empty E)) ∈ τ ∧
      (Silmaril.Wasm.Game.SEnv.ofStrategy τ).Agrees (u ++ [.ask e, .ans e w]) rest := by
    rcases h with _ | _ | ⟨⟨rfl, hmem⟩, hrest⟩
    exact ⟨_, _, rfl, rfl, hmem, hrest⟩
  have hp' : Silmaril.Games.Path .idle ((u ++ ([.ask e, .ans e w] : List (Ev E))).map .inr :
      List (Move Sig.empty E)) .idle := path_snoc_pair hpu
  have hm : ((u ++ ([.ask e, .ans e w] : List (Ev E)) ++ rest).map .inr :
      List (Move Sig.empty E)) ∈ τ := (hih _ hmem hp').1 hrest
  simpa using hm

/-- Agreement of an answered call and more, backwards. -/
private theorem agrees_ofStrategy_pair_mpr {u rest : List (Ev E)} {x y : Ev E}
    (hpu : Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) .idle)
    (hih : RestAgrees τ rest)
    (hx : ((u ++ x :: y :: rest).map .inr : List (Move Sig.empty E)) ∈ τ) :
    (Silmaril.Wasm.Game.SEnv.ofStrategy τ).Agrees u (x :: y :: rest) := by
  obtain ⟨z, hz⟩ := path_after_idle hpu (τ.legal hx)
  obtain ⟨e, w, rfl, rfl⟩ : ∃ e w, x = .ask e ∧ y = .ans e w := by
    rcases hz with _ | ⟨hs, _ | ⟨hs', _⟩⟩
    cases hs
    cases hs'
    exact ⟨_, _, rfl, rfl⟩
  have hpre : ((u ++ ([.ask e, .ans e w] : List (Ev E))).map .inr :
      List (Move Sig.empty E)) ∈ τ := τ.of_prefix hx (by simp)
  have hrest : (Silmaril.Wasm.Game.SEnv.ofStrategy τ).Agrees
      (u ++ ([.ask e, .ans e w] : List (Ev E))) rest :=
    (hih _ hpre (path_snoc_pair hpu)).2 (by simpa using hx)
  exact Silmaril.Wasm.Game.SEnv.Agrees.answered (L := Silmaril.Wasm.Game.SEnv.ofStrategy τ)
    ⟨rfl, hpre⟩ hrest

/-- **Agreement with the history machine** from an idle history `u` of `τ`: the events `v`
agree exactly when `u ++ v` is a play of `τ`. -/
theorem agrees_ofStrategy_iff : ∀ (n : Nat) (v u : List (Ev E)), v.length ≤ n →
    (u.map .inr : List (Move Sig.empty E)) ∈ τ →
    Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) .idle →
    ((Silmaril.Wasm.Game.SEnv.ofStrategy τ).Agrees u v ↔
      ((u ++ v).map .inr : List (Move Sig.empty E)) ∈ τ) := by
  intro n
  induction n with
  | zero =>
    intro v u hn hu _
    obtain rfl : v = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)
    exact ⟨fun _ => by simpa using hu,
      fun _ => Silmaril.Wasm.Game.SEnv.Agrees.nil (L := Silmaril.Wasm.Game.SEnv.ofStrategy τ) u⟩
  | succ n ih =>
    intro v u hn hu hpu
    rcases v with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · exact ⟨fun _ => by simpa using hu,
        fun _ => Silmaril.Wasm.Game.SEnv.Agrees.nil (L := Silmaril.Wasm.Game.SEnv.ofStrategy τ) u⟩
    · exact agrees_ofStrategy_single hu hpu
    · have hlen : rest.length ≤ n := by simp at hn; omega
      have hih : RestAgrees τ rest := fun u' hu' hpu' => ih rest u' hlen hu' hpu'
      exact ⟨agrees_ofStrategy_pair_mp hpu hih, agrees_ofStrategy_pair_mpr hpu hih⟩

/-- Over the empty lower signature a play is its upper events. -/
theorem eq_map_upper : ∀ p : List (Move Sig.empty E), p = (upper p).map .inr
  | [] => rfl
  | .inl a :: _ => (Ev.empty_elim a).elim
  | .inr b :: p => by
    simp only [upper_cons_inr, List.map_cons, List.cons.injEq, true_and]
    exact eq_map_upper p

/-- **Every environment strategy is a stateful environment**: the strategy of the history
machine of `τ` is `τ`. -/
theorem strategy_ofStrategy (τ : Strategy Sig.empty E) :
    (Silmaril.Wasm.Game.SEnv.ofStrategy τ).strategy [] = τ := by
  ext p
  rw [mem_strategy_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h := (agrees_ofStrategy_iff (τ := τ) _ u [] (Nat.le_refl _) τ.nil_mem (.nil _)).1 hu
    simpa using h
  · intro hp
    obtain ⟨u, rfl⟩ : ∃ u : List (Ev E), p = u.map .inr := ⟨upper p, eq_map_upper p⟩
    refine ⟨u, (agrees_ofStrategy_iff (τ := τ) _ u [] (Nat.le_refl _) τ.nil_mem (.nil _)).2
      (by simpa using hp), rfl⟩

end History

end Silmaril.Proofs.Wasm.Game.SEnv
