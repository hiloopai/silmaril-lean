module

public import Silmaril.Games.Handler.Defs
public import Silmaril.Games.LTS.Thms

/-!
# Strategies of handlers: proofs

Proofs for `Silmaril.Games.Handler.Thms`.

* The traces of a handler are legal plays (`path_of_run`), and its strategy is
  exactly its set of traces (`mem_ofHandler`): handlers accept every question
  and every answer, so no receptive completion is needed.
* `ofHandler_comp`: the strategy of `h₁.comp h₂` is the composite of the
  strategies. Both inclusions track an invariant `Inv` relating the states of
  the two component handlers with that of the composite handler: the
  composite runs `P.interp h₁` while `h₂` runs `P`, and runs
  `P₁.bind (fun r => (k r).interp h₁)` while `h₁` runs `P₁` on behalf of a call
  of `h₂` waiting with continuation `k`. From the composite side
  (`run_zip`), each visible step of the composite is matched by finitely many
  hidden synchronisations followed by one visible step of a component
  (`adv`); termination of the hidden phase is by induction on the program of
  `h₂`.
-/

public section

namespace Silmaril.Proofs.Games.Handler

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- The game position of a handler state. -/
def pos {h : Handler E F} : Reduction.State h.toReduction → Pos E F
  | .idle => .idle
  | .run q _ => .run q
  | .wait q m _ => .wait q m

theorem path_of_run {h : Handler E F} {x y : h.toReduction.toLTS.State}
    {s : List (Move E F)} (hr : h.toReduction.toLTS.Run x s y) : Path (pos x) s (pos y) := by
  induction hr with
  | nil => exact .nil _
  | tau hs _ _ => cases hs with | tau hc => exact (hc : False).elim
  | vis hs _ ih =>
    cases hs with
    | ask q => exact .cons (.ask q) ih
    | call _ => exact .cons (.call _ _) ih
    | resume => exact .cons (.reply _ _ _) ih
    | ret _ => exact .cons (.ret _ _) ih

/-- A run of a handler extends by any Opponent move that keeps the play legal. -/
private theorem run_concat_of_isO {h : Handler E F} {p₀ : List (Move E F)} {o : Move E F}
    (hy : ∃ y, h.toReduction.toLTS.Run h.toReduction.toLTS.init p₀ y)
    (hl : Legal (p₀ ++ [o])) (ho : o.IsO) :
    ∃ y, h.toReduction.toLTS.Run h.toReduction.toLTS.init (p₀ ++ [o]) y := by
  obtain ⟨y, hy⟩ := hy
  obtain ⟨_, hpath⟩ := hl
  obtain ⟨x, hx, hxo⟩ := Path.concat_iff.1 hpath
  cases (path_of_run hy).det hx
  rcases y with _ | ⟨q, P⟩ | ⟨q, m, k⟩
  · cases hxo with
    | ask q => exact ⟨_, LTS.Run.append hy (.vis (Reduction.Step.ask q) (.nil _))⟩
  · cases hxo <;> exact ho.elim
  · cases hxo with
    | reply _ _ n =>
      exact ⟨_, LTS.Run.append hy (.vis (Reduction.Step.resume _ _ _ n) (.nil _))⟩

theorem mem_ofHandler {h : Handler E F} {p : List (Move E F)} :
    p ∈ Strategy.ofHandler h ↔ ∃ y, h.toReduction.toLTS.Run h.toReduction.toLTS.init p y := by
  constructor
  · intro hp
    have hp' : p ∈ Strategy.generatePlays h.toReduction.toLTS.Traces := hp
    obtain ⟨hl, s, hs, hpre⟩ := hp'
    have hs' : s ∈ h.toReduction.toLTS.Traces := by
      rcases hs with h0 | ⟨hs, -⟩
      · exact h0 ▸ ⟨_, .nil _⟩
      · exact hs
    rcases hpre with hpre | ⟨p₀, o, hpo, hp₀, ho⟩
    · exact LTS.traces_of_prefix hs' hpre
    · have hy : ∃ y, h.toReduction.toLTS.Run h.toReduction.toLTS.init p₀ y :=
        LTS.traces_of_prefix hs' hp₀
      exact hpo ▸ run_concat_of_isO hy (hpo ▸ hl) ho
  · rintro ⟨y, hy⟩
    exact Strategy.subset_generate ⟨y, hy⟩ ⟨_, path_of_run hy⟩

/-! ## The composition invariant -/

variable (h₁ : Handler E F) (h₂ : Handler F G)

/-- How the states of the two component handlers and of the composite handler
correspond. -/
inductive Inv : h₁.toReduction.toLTS.State → h₂.toReduction.toLTS.State →
    (h₁.comp h₂).toReduction.toLTS.State → Prop
  | idle : Inv Reduction.State.idle Reduction.State.idle Reduction.State.idle
  | run (g : G.Op) (P : Prog F (G.Ar g)) :
      Inv Reduction.State.idle (Reduction.State.run g P) (Reduction.State.run g (P.interp h₁))
  | call (g : G.Op) (f : F.Op) (P₁ : Prog E (F.Ar f)) (k : F.Ar f → Prog F (G.Ar g)) :
      Inv (Reduction.State.run f P₁) (Reduction.State.wait g f k)
        (Reduction.State.run g (P₁.bind fun r => (k r).interp h₁))
  | wait (g : G.Op) (f : F.Op) (e : E.Op) (k₁ : E.Ar e → Prog E (F.Ar f))
      (k : F.Ar f → Prog F (G.Ar g)) :
      Inv (Reduction.State.wait f e k₁) (Reduction.State.wait g f k)
        (Reduction.State.wait g e fun n => (k₁ n).bind fun r => (k r).interp h₁)

/-- A handler run reading a move starts with that visible step: handlers have no
silent steps. -/
private theorem vis_of_run_cons {h : Handler E F} {x z : h.toReduction.toLTS.State}
    {o : Move E F} {s : List (Move E F)} (hr : h.toReduction.toLTS.Run x (o :: s) z) :
    ∃ y, h.toReduction.toLTS.step x (some o) y ∧ h.toReduction.toLTS.Run y s z := by
  cases hr with
  | tau hst _ => cases hst with | tau hc => exact (hc : False).elim
  | vis hst hr => exact ⟨_, hst, hr⟩

theorem zip_run {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (hz : Zip s t p) : ∀ {a b c a' b'}, Inv h₁ h₂ a b c →
      h₁.toReduction.toLTS.Run a s a' → h₂.toReduction.toLTS.Run b t b' →
      ∃ c', (h₁.comp h₂).toReduction.toLTS.Run c p c' := by
  induction hz with
  | nil =>
    intro a b c a' b' _ _ _
    exact ⟨c, .nil _⟩
  | @left s t p x _ ih =>
    show ∀ {a b c a' b'}, Inv h₁ h₂ a b c →
      h₁.toReduction.toLTS.Run a (.inl x :: s) a' → h₂.toReduction.toLTS.Run b t b' →
      ∃ c', (h₁.comp h₂).toReduction.toLTS.Run c (.inl x :: p) c'
    intro a b c a' b' hi hs ht
    obtain ⟨y, hst, hs₁⟩ := vis_of_run_cons hs
    cases hst with
    | call hc =>
      cases hi; cases hc
      obtain ⟨c', hc'⟩ := ih (Inv.wait _ _ _ _ _) hs₁ ht
      exact ⟨c', .vis (Reduction.Step.call rfl) hc'⟩
    | resume f e k₁ n =>
      cases hi
      obtain ⟨c', hc'⟩ := ih (Inv.call _ _ _ _) hs₁ ht
      exact ⟨c', .vis (Reduction.Step.resume _ _ _ n) hc'⟩
  | @right s t p y _ ih =>
    show ∀ {a b c a' b'}, Inv h₁ h₂ a b c →
      h₁.toReduction.toLTS.Run a s a' → h₂.toReduction.toLTS.Run b (.inr y :: t) b' →
      ∃ c', (h₁.comp h₂).toReduction.toLTS.Run c (.inr y :: p) c'
    intro a b c a' b' hi hs ht
    obtain ⟨y', hst, ht₁⟩ := vis_of_run_cons ht
    cases hst with
    | ask g =>
      cases hi
      obtain ⟨c', hc'⟩ := ih (Inv.run g (h₂ g)) hs ht₁
      exact ⟨c', .vis (Reduction.Step.ask g) hc'⟩
    | ret hc =>
      cases hi; cases hc
      obtain ⟨c', hc'⟩ := ih (Inv.idle) hs ht₁
      exact ⟨c', .vis (Reduction.Step.ret rfl) hc'⟩
  | @sync s t p z _ ih =>
    show ∀ {a b c a' b'}, Inv h₁ h₂ a b c →
      h₁.toReduction.toLTS.Run a (.inr z :: s) a' → h₂.toReduction.toLTS.Run b (.inl z :: t) b' →
      ∃ c', (h₁.comp h₂).toReduction.toLTS.Run c p c'
    intro a b c a' b' hi hs ht
    obtain ⟨y₁, hst₁, hs₁⟩ := vis_of_run_cons hs
    obtain ⟨y₂, hst₂, ht₁⟩ := vis_of_run_cons ht
    cases hst₁ with
    | ask f =>
      cases hst₂ with
      | call hc => cases hi; cases hc; exact ih (Inv.call _ f (h₁ f) _) hs₁ ht₁
    | ret hc =>
      cases hst₂ with
      | resume _ _ k r => cases hi; cases hc; exact ih (Inv.run _ _) hs₁ ht₁

/-! ## From the composite to the components -/

/-- `s₀` and `t₀` interact to produce `p₀`, in front of any interaction. -/
def ZipPre (s₀ : List (Move E F)) (t₀ : List (Move F G)) (p₀ : List (Move E G)) : Prop :=
  ∀ s t p, Zip s t p → Zip (s₀ ++ s) (t₀ ++ t) (p₀ ++ p)

omit h₁ h₂ in
theorem ZipPre.sync (z : Ev F) {s₀ : List (Move E F)} {t₀ : List (Move F G)}
    {p₀ : List (Move E G)} (h : ZipPre s₀ t₀ p₀) :
    ZipPre (.inr z :: s₀) (.inl z :: t₀) p₀ :=
  fun s t p hz => .sync z (h s t p hz)

/-- After the composite makes the visible move `o` and reaches `c₁`, the
components can follow from `a` and `b`. -/
def Adv (a : h₁.toReduction.toLTS.State) (b : h₂.toReduction.toLTS.State)
    (c₁ : (h₁.comp h₂).toReduction.toLTS.State) (o : Move E G) : Prop :=
  ∃ s₀ t₀ a₁ b₁, h₁.toReduction.toLTS.Run a s₀ a₁ ∧ h₂.toReduction.toLTS.Run b t₀ b₁ ∧
    Inv h₁ h₂ a₁ b₁ c₁ ∧ ZipPre s₀ t₀ [o]

theorem adv_call_aux (g : G.Op) (f : F.Op) (k : F.Ar f → Prog F (G.Ar g))
    (ih : ∀ r {o c₁}, Reduction.Step (h₁.comp h₂).toReduction
      (.run g ((k r).interp h₁)) (some o) c₁ →
        Adv h₁ h₂ Reduction.State.idle (Reduction.State.run g (k r)) c₁ o)
    (P₁ : Prog E (F.Ar f)) {o : Move E G} {c₁ : (h₁.comp h₂).toReduction.toLTS.State}
    (hst : Reduction.Step (h₁.comp h₂).toReduction
      (.run g (P₁.bind fun r => (k r).interp h₁)) (some o) c₁) :
    Adv h₁ h₂ (Reduction.State.run f P₁) (Reduction.State.wait g f k) c₁ o := by
  cases P₁ with
  | pure r =>
    obtain ⟨s₀, t₀, a₁, b₁, hs, ht, hi, hz⟩ := ih r hst
    exact ⟨.inr (.ans f r) :: s₀, .inl (.ans f r) :: t₀, a₁, b₁,
      .vis (Reduction.Step.ret rfl) hs, .vis (Reduction.Step.resume _ _ _ r) ht, hi,
      ZipPre.sync _ hz⟩
  | call e k₁ =>
    cases hst with
    | call hc =>
      cases hc
      exact ⟨[.inl (.ask e)], [], _, _, .vis (Reduction.Step.call rfl) (.nil _), .nil _,
        Inv.wait _ _ _ _ _, fun _ _ _ hz => .left _ hz⟩
    | ret hc => cases hc

theorem adv_run (g : G.Op) (P : Prog F (G.Ar g)) :
    ∀ {o : Move E G} {c₁ : (h₁.comp h₂).toReduction.toLTS.State},
      Reduction.Step (h₁.comp h₂).toReduction (.run g (P.interp h₁)) (some o) c₁ →
      Adv h₁ h₂ Reduction.State.idle (Reduction.State.run g P) c₁ o := by
  induction P with
  | pure r =>
    intro o c₁ hst
    cases hst with
    | call hc => cases hc
    | ret hc =>
      cases hc
      exact ⟨[], [.inr (.ans g r)], Reduction.State.idle, Reduction.State.idle, .nil _,
        .vis (Reduction.Step.ret rfl) (.nil _), .idle, fun _ _ _ hz => .right _ hz⟩
  | call f k ih =>
    intro o c₁ hst
    obtain ⟨s₀, t₀, a₁, b₁, hs, ht, hi, hz⟩ :=
      adv_call_aux h₁ h₂ g f k (fun r _ _ h => ih r h) (h₁ f) hst
    exact ⟨.inr (.ask f) :: s₀, .inl (.ask f) :: t₀, a₁, b₁, .vis (Reduction.Step.ask f) hs,
      .vis (Reduction.Step.call rfl) ht, hi, ZipPre.sync _ hz⟩

theorem adv {a : h₁.toReduction.toLTS.State} {b : h₂.toReduction.toLTS.State}
    {c c₁ : (h₁.comp h₂).toReduction.toLTS.State} {o : Move E G}
    (hi : Inv h₁ h₂ a b c) (hst : Reduction.Step (h₁.comp h₂).toReduction c (some o) c₁) :
    Adv h₁ h₂ a b c₁ o := by
  cases hi with
  | idle =>
    cases hst with
    | ask g =>
      exact ⟨[], [.inr (.ask g)], Reduction.State.idle, _, .nil _,
        .vis (Reduction.Step.ask g) (.nil _), Inv.run g (h₂ g), fun _ _ _ hz => .right _ hz⟩
  | run g P => exact adv_run h₁ h₂ g P hst
  | call g f P₁ k => exact adv_call_aux h₁ h₂ g f k (fun r _ _ h => adv_run h₁ h₂ g (k r) h) P₁ hst
  | wait g f e k₁ k =>
    cases hst with
    | resume _ _ _ n =>
      exact ⟨[.inl (.ans e n)], [], _, _, .vis (Reduction.Step.resume _ _ _ n) (.nil _), .nil _,
        Inv.call _ _ _ _, fun _ _ _ hz => .left _ hz⟩

theorem run_zip {c c' : (h₁.comp h₂).toReduction.toLTS.State} {p : List (Move E G)}
    (hr : (h₁.comp h₂).toReduction.toLTS.Run c p c') :
    ∀ {a b}, Inv h₁ h₂ a b c → ∃ s t a' b', h₁.toReduction.toLTS.Run a s a' ∧
      h₂.toReduction.toLTS.Run b t b' ∧ Zip s t p := by
  induction hr with
  | nil =>
    intro a b _
    exact ⟨[], [], a, b, .nil _, .nil _, .nil⟩
  | tau hst _ _ => cases hst with | tau hc => exact (hc : False).elim
  | vis hst _ ih =>
    intro a b hi
    obtain ⟨s₀, t₀, a₁, b₁, hs₀, ht₀, hi₁, hz₀⟩ := adv h₁ h₂ hi hst
    obtain ⟨s, t, a', b', hs, ht, hz⟩ := ih hi₁
    exact ⟨s₀ ++ s, t₀ ++ t, a', b', LTS.Run.append hs₀ hs, LTS.Run.append ht₀ ht,
      hz₀ s t _ hz⟩

theorem ofHandler_comp :
    Strategy.ofHandler (h₁.comp h₂) = (Strategy.ofHandler h₁).comp (Strategy.ofHandler h₂) := by
  ext p
  rw [Strategy.mem_comp, mem_ofHandler]
  constructor
  · rintro ⟨c', hr⟩
    obtain ⟨s, t, a', b', hs, ht, hz⟩ := run_zip h₁ h₂ hr Inv.idle
    exact ⟨s, mem_ofHandler.2 ⟨a', hs⟩, t, mem_ofHandler.2 ⟨b', ht⟩, hz⟩
  · rintro ⟨s, hs, t, ht, hz⟩
    obtain ⟨a', hs⟩ := mem_ofHandler.1 hs
    obtain ⟨b', ht⟩ := mem_ofHandler.1 ht
    exact zip_run h₁ h₂ hz Inv.idle hs ht

end Silmaril.Proofs.Games.Handler
