module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiGames
public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Game.Strategy.Thms

/-!
# Plays with lower calls through compositions, handlers and pairings

`MultiGames` treats rounds without lower moves. With imports, an export question is answered
after calls below: a `CRound` is a question `q`, the answered lower calls `cs` made while
answering it, and the answer `a`, and `cplay l` is the play of the rounds `l` one after
another (`callMoves` are the lower calls). Membership is propagated through the layers:

* a handler on top (`cplay_comp_ofHandler`): `HC h up low`, each upper round answered at once
  or by one call, the lower calls passing through unchanged;
* a handler below (`cplay_ofHandler_comp`): `HB h up low`, each lower call of the strategy on
  top answered by `h` at once or by one call further down (`HRounds h`);
* pairing (`cplay_pair_inr`): rounds of the right component;
* the instance (`cplay_mem_strategy`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference

variable {E F G : Sig.{0}}

/-- A question `q`, answered `a` after the answered lower calls `cs`. -/
structure CRound (E F : Sig.{0}) where
  q : F.Op
  cs : List (Round E)
  a : F.Ar q

/-- The play of the rounds `l`, one after another. -/
def cplay : List (CRound E F) → List (Move E F)
  | [] => []
  | r :: l => .inr (.ask r.q) :: (callMoves r.cs ++ (.inr (.ans r.q r.a) :: cplay l))

theorem cplay_single (r : CRound E F) :
    cplay [r] = .inr (.ask r.q) :: callMoves r.cs ++ [.inr (.ans r.q r.a)] := rfl

theorem path_calls (q : F.Op) :
    ∀ cs : List (Round E), Path (.run q) (callMoves (F := F) cs) (.run q)
  | [] => .nil _
  | ⟨m, n⟩ :: cs => .cons (.call q m) (.cons (.reply q m n) (path_calls q cs))

theorem path_cplay : ∀ l : List (CRound E F), Path .idle (cplay l) .idle
  | [] => .nil _
  | r :: l => .cons (.ask r.q) ((path_calls r.q r.cs).append (.cons (.ret r.q r.a) (path_cplay l)))

theorem legal_cplay (l : List (CRound E F)) : Legal (cplay l) := ⟨_, path_cplay l⟩

/-- The instance plays its runs. -/
theorem cplay_mem_strategy {I : Silmaril.Wasm.Game.ScalarInstance} {P : Silmaril.Wasm.Numerics.Profile}
    {s : Silmaril.Wasm.Execution.Core.Store Nat} {l : List (CRound I.E I.F)} {q : I.HState}
    (h : I.Path P (.idle s) (cplay l) q) : cplay l ∈ I.strategy P s :=
  Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mpr ⟨q, h⟩

/-! ## Zips -/

/-- Lower calls of the lower strategy are visible. -/
theorem zip_calls_left {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∀ cs : List (Round E),
      Zip (callMoves (F := F) cs ++ s) t (callMoves (F := G) cs ++ p)
  | [] => h
  | ⟨_, _⟩ :: cs => .left _ (.left _ (zip_calls_left h cs))

/-! ## A handler on top -/

/-- `HC h up low`: the handler `h` answers each round of `up` at once (no lower calls) or by
one call answered as the round of `low`, whose lower calls pass through. -/
inductive HC (h : Handler F G) : List (CRound E G) → List (CRound E F) → Prop
  | nil : HC h [] []
  | pure {q : G.Op} {a : G.Ar q} {up : List (CRound E G)} {low : List (CRound E F)} :
      h q = .pure a → HC h up low → HC h (⟨q, [], a⟩ :: up) low
  | call {q : G.Op} {q' : F.Op} {k : F.Ar q' → Prog F (G.Ar q)} {a' : F.Ar q'} {a : G.Ar q}
      {cs : List (Round E)} {up : List (CRound E G)} {low : List (CRound E F)} :
      h q = .call q' k → k a' = .pure a → HC h up low →
      HC h (⟨q, cs, a⟩ :: up) (⟨q', cs, a'⟩ :: low)

theorem HC.run {h : Handler F G} {up : List (CRound E G)} {low : List (CRound E F)}
    (H : HC h up low) :
    ∃ t, h.toReduction.toLTS.Run .idle t .idle ∧ Zip (cplay low) t (cplay up) := by
  induction H with
  | nil => exact ⟨[], .nil _, .nil⟩
  | @pure q a _ _ hq _ ih =>
    obtain ⟨t, ht, hz⟩ := ih
    exact ⟨.inr (.ask q) :: .inr (.ans q a) :: t,
      .vis (.ask q) (.vis (.ret (show h q = .pure a from hq)) ht), .right _ (.right _ hz)⟩
  | @call q q' k a' a cs _ _ hq hk _ ih =>
    obtain ⟨t, ht, hz⟩ := ih
    refine ⟨.inr (.ask q) :: .inl (.ask q') :: .inl (.ans q' a') :: .inr (.ans q a) :: t, ?_,
      .right _ (.sync _ (zip_calls_left (.sync _ (.right _ hz)) cs))⟩
    exact .vis (.ask q) (.vis (.call (show h q = .call q' k from hq))
      (.vis (Reduction.Step.resume (R := h.toReduction) q q' k a')
        (.vis (.ret (show k a' = .pure a from hk)) ht)))

/-- **A handler on top**, for rounds with lower calls. -/
theorem cplay_comp_ofHandler {σ : Strategy E F} {h : Handler F G} {up : List (CRound E G)}
    {low : List (CRound E F)} (H : HC h up low) (hσ : cplay low ∈ σ) :
    cplay up ∈ σ.comp (Strategy.ofHandler h) := by
  obtain ⟨t, ht, hz⟩ := H.run
  exact ⟨_, hσ, t, Strategy.mem_ofHandler.mpr ⟨_, ht⟩, hz⟩

/-! ## A handler below -/

/-- The handler's runs serving the lower calls `cs` by the calls `cs'`. -/
theorem HRounds.serve {h : Handler E F} {cs : List (Round F)} {cs' : List (Round E)}
    (H : HRounds h cs cs') :
    ∃ t, h.toReduction.toLTS.Run .idle t .idle ∧
      ∀ {t₁ : List (Move E F)} {s₁ : List (Move F G)} {p₁ : List (Move E G)}, Zip t₁ s₁ p₁ →
        Zip (t ++ t₁) (callMoves cs ++ s₁) (callMoves cs' ++ p₁) := by
  induction H with
  | nil => exact ⟨[], .nil _, fun hz => hz⟩
  | @pure q a _ _ hq _ ih =>
    obtain ⟨t, ht, hz⟩ := ih
    exact ⟨.inr (.ask q) :: .inr (.ans q a) :: t,
      .vis (.ask q) (.vis (.ret (show h q = .pure a from hq)) ht),
      fun h₁ => .sync _ (.sync _ (hz h₁))⟩
  | @call q q' k a' a _ _ hq hk _ ih =>
    obtain ⟨t, ht, hz⟩ := ih
    refine ⟨.inr (.ask q) :: .inl (.ask q') :: .inl (.ans q' a') :: .inr (.ans q a) :: t, ?_,
      fun h₁ => .sync _ (.left _ (.left _ (.sync _ (hz h₁))))⟩
    exact .vis (.ask q) (.vis (.call (show h q = .call q' k from hq))
      (.vis (Reduction.Step.resume (R := h.toReduction) q q' k a')
        (.vis (.ret (show k a' = .pure a from hk)) ht)))

/-- `HB h up low`: the lower calls of each round of `up` are served by `h` (`HRounds h`), the
calls further down being those of the corresponding round of `low`. -/
inductive HB (h : Handler E F) : List (CRound F G) → List (CRound E G) → Prop
  | nil : HB h [] []
  | cons {q : G.Op} {a : G.Ar q} {cs : List (Round F)} {cs' : List (Round E)}
      {up : List (CRound F G)} {low : List (CRound E G)} :
      HRounds h cs cs' → HB h up low → HB h (⟨q, cs, a⟩ :: up) (⟨q, cs', a⟩ :: low)

theorem HB.run {h : Handler E F} {up : List (CRound F G)} {low : List (CRound E G)}
    (H : HB h up low) :
    ∃ t, h.toReduction.toLTS.Run .idle t .idle ∧ Zip t (cplay up) (cplay low) := by
  induction H with
  | nil => exact ⟨[], .nil _, .nil⟩
  | @cons q a _ _ _ _ Hc _ ih =>
    obtain ⟨t₀, ht₀, hz₀⟩ := Hc.serve (G := G)
    obtain ⟨t₁, ht₁, hz₁⟩ := ih
    exact ⟨t₀ ++ t₁, ht₀.append ht₁, .right _ (hz₀ (.right _ hz₁))⟩

/-- **A handler below**, for rounds with lower calls. -/
theorem cplay_ofHandler_comp {τ : Strategy F G} {h : Handler E F} {up : List (CRound F G)}
    {low : List (CRound E G)} (H : HB h up low) (hτ : cplay up ∈ τ) :
    cplay low ∈ (Strategy.ofHandler h).comp τ := by
  obtain ⟨t, ht, hz⟩ := H.run
  exact ⟨t, Strategy.mem_ofHandler.mpr ⟨_, ht⟩, _, hτ, hz⟩

/-! ## Pairing -/

/-- A round of the right component of a pairing. -/
def CRound.inr {F₁ F₂ : Sig.{0}} (r : CRound E F₂) : CRound E (F₁ ⊕ₛ F₂) := ⟨.inr r.q, r.cs, r.a⟩

theorem halves_calls {F₁ F₂ : Sig.{0}} :
    ∀ (cs : List (Round E)) (rest : List (Move E (F₁ ⊕ₛ F₂))),
      Split.halves true (callMoves cs ++ rest) =
        ((Split.halves true rest).1, callMoves cs ++ (Split.halves true rest).2)
  | [], _ => rfl
  | ⟨m, n⟩ :: cs, rest => by
    show Split.halves true (.inl (.ask m) :: .inl (.ans m n) :: (callMoves cs ++ rest)) = _
    simp only [Split.halves, halves_calls cs rest]
    rfl

theorem halves_cplay_inr {F₁ F₂ : Sig.{0}} :
    ∀ (b : Bool) (l : List (CRound E F₂)),
      Split.halves b (cplay (l.map (CRound.inr (F₁ := F₁)))) = ([], cplay l)
  | _, [] => rfl
  | b, ⟨q, cs, a⟩ :: l => by
    show Split.halves b (.inr (.ask (.inr q)) :: (callMoves cs ++
      (.inr (.ans (.inr q) a) :: cplay (l.map (CRound.inr (F₁ := F₁)))))) = _
    simp only [Split.halves, halves_calls, halves_cplay_inr true l]
    rfl

/-- **Rounds of the right component of a pairing**, with lower calls. -/
theorem cplay_pair_inr {F₁ F₂ : Sig.{0}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {l : List (CRound E F₂)} (h : cplay l ∈ σ₂) :
    cplay (l.map (CRound.inr (F₁ := F₁))) ∈ σ₁.pair σ₂ := by
  refine ⟨legal_cplay _, ?_, ?_⟩
  · rw [halves_cplay_inr]
    exact σ₁.nil_mem
  · rw [halves_cplay_inr]
    exact h

end Silmaril.Proofs.Wasm.Component.Reference
