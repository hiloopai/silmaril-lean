module

public import Silmaril.Proofs.Wasm.Logic.OpenTotal.Strategy
public import Silmaril.Games.DivComp.Thms

/-!
# Open modules with total correctness: linking

`dlink_refines`: if `M₁` meets `Γm` totally under `Γi`, `M₂` meets `Γe` totally
under `Γm`, and `M₂`'s strategy is productive (`Productive`: it does not chatter
forever with `M₁` within one question), the divergence-observing composite
`(dmodStrat M₁).comp (dmodStrat M₂)` refines `dagStrat (ctxSpec Γi) (ctxSpec Γe)`.
The composite diverges in three ways (`Silmaril.Games.DStrategy.compDiv`), all
excluded after good Opponent behaviour:

* local divergence of either module: by `opp_zip`, the Opponent moves of both
  component plays are good (each hidden move is a Proponent move of the other
  module, good by its assume/guarantee correctness), so `dmodStrat_div` applies;
* infinite hidden chatter: the upper module then has an infinite play
  (`InfInteraction.chatter_inf`) with good Opponent moves and only the finitely
  many upper moves of the visible play (`zip_ucount`), against productivity.

Productivity of every totally correct module is
`Silmaril.Proofs.Wasm.Logic.OpenTotal.Productive.dmodStrat_productive`, which gives
the unconditional `dlink_refines_total`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.OpenTotal

open Silmaril.Games
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Ctx)
open Silmaril.Wasm.Logic.Open (OMod)
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood ctxSpec agStrat comp_refines)

universe u

section Plays

variable {E F G : Sig.{u}} {I : ISpec E} {M : ISpec F} {S : ISpec G}

theorem OppGood.cons {m : Move E F} {p : List (Move E F)} {I : ISpec E} {S : ISpec F}
    (hm : Move.IsO m → MoveGood I S m) (hp : OppGood I S p) : OppGood I S (m :: p) := by
  intro m' hm'
  rcases List.mem_cons.mp hm' with rfl | h
  · exact hm
  · exact hp m' h

theorem OppGood.head {m : Move E F} {p : List (Move E F)} {I : ISpec E} {S : ISpec F}
    (h : OppGood I S (m :: p)) : Move.IsO m → MoveGood I S m := h m (List.mem_cons_self ..)

theorem OppGood.tail {m : Move E F} {p : List (Move E F)} {I : ISpec E} {S : ISpec F}
    (h : OppGood I S (m :: p)) : OppGood I S p := fun m' hm' => h m' (List.mem_cons_of_mem _ hm')

theorem OppGood.of_prefix {p q : List (Move E F)} {I : ISpec E} {S : ISpec F} (hq : p <+: q)
    (h : OppGood I S q) : OppGood I S p := fun m hm => h m (hq.subset hm)

/-- A visible lower move. -/
theorem opp_left {e : Ev E} {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (ih : AG I M s → AG M S t → OppGood I S p → OppGood I M s ∧ OppGood M S t)
    (hs : AG I M (.inl e :: s)) (ht : AG M S t) (hp : OppGood I S (.inl e :: p)) :
    OppGood I M (.inl e :: s) ∧ OppGood M S t := by
  rcases e with m | ⟨m, n⟩
  · obtain ⟨-, hs'⟩ := hs.2 trivial
    obtain ⟨h₁, h₂⟩ := ih hs' ht hp.tail
    exact ⟨OppGood.cons (fun h => h.elim) h₁, h₂⟩
  · have hg : MoveGood I S (.inl (.ans m n)) := hp.head trivial
    obtain ⟨h₁, h₂⟩ := ih (hs.1 trivial hg) ht hp.tail
    exact ⟨OppGood.cons (fun _ => hg) h₁, h₂⟩

/-- A visible upper move. -/
theorem opp_right {e : Ev G} {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (ih : AG I M s → AG M S t → OppGood I S p → OppGood I M s ∧ OppGood M S t)
    (hs : AG I M s) (ht : AG M S (.inr e :: t)) (hp : OppGood I S (.inr e :: p)) :
    OppGood I M s ∧ OppGood M S (.inr e :: t) := by
  rcases e with m | ⟨m, n⟩
  · have hg : MoveGood I S (.inr (.ask m)) := hp.head trivial
    obtain ⟨h₁, h₂⟩ := ih hs (ht.1 trivial hg) hp.tail
    exact ⟨h₁, OppGood.cons (fun _ => hg) h₂⟩
  · obtain ⟨-, ht'⟩ := ht.2 trivial
    obtain ⟨h₁, h₂⟩ := ih hs ht' hp.tail
    exact ⟨h₁, OppGood.cons (fun h => h.elim) h₂⟩

/-- A hidden move: a Proponent move of one side is the other side's Opponent
move, good by assume/guarantee correctness. -/
theorem opp_sync {e : Ev F} {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (ih : AG I M s → AG M S t → OppGood I S p → OppGood I M s ∧ OppGood M S t)
    (hs : AG I M (.inr e :: s)) (ht : AG M S (.inl e :: t)) (hp : OppGood I S p) :
    OppGood I M (.inr e :: s) ∧ OppGood M S (.inl e :: t) := by
  rcases e with m | ⟨m, n⟩
  · obtain ⟨hg, ht'⟩ := ht.2 trivial
    obtain ⟨h₁, h₂⟩ := ih (hs.1 trivial hg) ht' hp
    exact ⟨OppGood.cons (fun _ => hg) h₁, OppGood.cons (fun h => h.elim) h₂⟩
  · obtain ⟨hg, hs'⟩ := hs.2 trivial
    obtain ⟨h₁, h₂⟩ := ih hs' (ht.1 trivial hg) hp
    exact ⟨OppGood.cons (fun h => h.elim) h₁, OppGood.cons (fun _ => hg) h₂⟩

/-- **Good Opponent moves propagate to the components** of an interaction of
assume/guarantee correct plays. -/
theorem opp_zip {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (hz : Zip s t p) : AG I M s → AG M S t → OppGood I S p → OppGood I M s ∧ OppGood M S t := by
  induction hz with
  | nil => exact fun _ _ _ => ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | left a _ ih => exact fun hs ht hp => opp_left ih hs ht hp
  | right c _ ih => exact fun hs ht hp => opp_right ih hs ht hp
  | sync b _ ih => exact fun hs ht hp => opp_sync ih hs ht hp

/-- The upper moves of the upper play are those of the visible play. -/
theorem zip_ucount {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (hz : Zip s t p) : ucount t = ucount p := by
  induction hz with
  | nil => rfl
  | left a _ ih => simpa [ucount, upper, List.filterMap_cons] using ih
  | right c _ ih => simpa [ucount, upper] using ih
  | sync b _ ih => simpa [ucount, upper, List.filterMap_cons] using ih

theorem ucount_mono {t t' : List (Move E F)} (h : t' <+: t) : ucount t' ≤ ucount t := by
  obtain ⟨u, rfl⟩ := h
  simp [ucount, upper]

end Plays

section Link

variable {H : Type} {P : Profile} {M₁ M₂ : OMod H} {bind₁ bind₂ : H → Nat} {Γi Γm Γe : Ctx H}

/-- Chatter of a productive upper strategy with good Opponent moves is impossible. -/
theorem no_chatter {E F G : Sig.{u}} {I : ISpec E} {M : ISpec F} {S : ISpec G}
    {σ : DStrategy E F} {τ : DStrategy F G} (hσ : σ.toStrategy ≤ agStrat I M)
    (hτ : τ.toStrategy ≤ agStrat M S) (hprod : Productive M S τ)
    (i : DStrategy.InfInteraction σ τ) {p : List (Move E G)} (hp : ∀ n, i.p n = p)
    (hg : OppGood I S p) : False := by
  obtain ⟨-, -, -, hinf⟩ := i.chatter_inf hp
  have hgood : ∀ n, OppGood M S (i.t n) := fun n =>
    (opp_zip (i.zip n) (hσ (i.mem_s n)).2 (hτ (i.mem_t n)).2 ((hp n).symm ▸ hg)).2
  obtain ⟨t', ⟨n, hn⟩, hk⟩ := hprod _ hinf (fun t' ⟨n, hn⟩ => (hgood n).of_prefix hn)
    (ucount p + 1)
  have hc : ucount (i.t n) = ucount p := (zip_ucount (i.zip n)).trans (congrArg ucount (hp n))
  have hle : ucount t' ≤ ucount (i.t n) := ucount_mono hn
  omega

/-- **No divergence of the composite after good Opponent behaviour.** -/
theorem dlink_div (h₁ : TModuleSat P M₁ bind₁ Γi Γm) (h₂ : TModuleSat P M₂ bind₂ Γm Γe)
    (hprod : Productive (ctxSpec Γm) (ctxSpec Γe) (dmodStrat P M₂ bind₂))
    {p : List (Move (Strategy.WCall H) (Strategy.WCall H))}
    (hp : p ∈ ((dmodStrat P M₁ bind₁).comp (dmodStrat P M₂ bind₂)).div) :
    ¬ OppGood (ctxSpec Γi) (ctxSpec Γe) p := by
  intro hg
  have hσ := (dmodStrat_sound h₁).1
  have hτ := (dmodStrat_sound h₂).1
  rcases hp with ⟨s, t, hz, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩
  · have hgs := (opp_zip hz (hσ ((dmodStrat P M₁ bind₁).div_mem hs)).2 (hτ ht).2 hg).1
    exact dmodStrat_div h₁ hs hgs
  · have hgt := (opp_zip hz (hσ hs).2 (hτ ((dmodStrat P M₂ bind₂).div_mem ht)).2 hg).2
    exact dmodStrat_div h₂ ht hgt
  · exact no_chatter hσ hτ hprod i hi hg

/-- **Linking totally correct modules**, divergence-aware: if `M₁` meets `Γm`
totally under `Γi`, `M₂` meets `Γe` totally under `Γm` and `M₂` is productive,
their composite refines the divergence-aware assume/guarantee strategy of `Γi`
and `Γe`. -/
theorem dlink_refines (h₁ : TModuleSat P M₁ bind₁ Γi Γm) (h₂ : TModuleSat P M₂ bind₂ Γm Γe)
    (hprod : Productive (ctxSpec Γm) (ctxSpec Γe) (dmodStrat P M₂ bind₂)) :
    (dmodStrat P M₁ bind₁).comp (dmodStrat P M₂ bind₂) ≤ dagStrat (ctxSpec Γi) (ctxSpec Γe) := by
  have hfin : ((dmodStrat P M₁ bind₁).comp (dmodStrat P M₂ bind₂)).toStrategy ≤
      agStrat (ctxSpec Γi) (ctxSpec Γe) := comp_refines (dmodStrat_sound h₁).1 (dmodStrat_sound h₂).1
  refine ⟨hfin, fun p hp => ⟨hfin (DStrategy.div_mem _ hp), DStrategy.div_run _ hp,
    dlink_div h₁ h₂ hprod hp⟩, fun J hJ => ⟨DStrategy.inf_isInf _ hJ, fun s hs =>
      hfin (DStrategy.inf_sub _ hJ hs)⟩⟩

end Link

end Silmaril.Wasm.Logic.OpenTotal
