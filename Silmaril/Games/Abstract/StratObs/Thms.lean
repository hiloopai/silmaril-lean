module

public import Silmaril.Games.Abstract.StratObs.Defs
import Silmaril.Proofs.Games.Abstract.StratObs.Basic

/-!
# From function observations to divergence-observing strategies: theorems

**Reading back the components.** Each component of a triple is read back
from one-round observations of `toDStrat t`:

* finished behaviours from completed rounds (`mem_round`, and `mem_ret`,
  `mem_trap` for the two answers);
* call prefixes `satP t` from plays ending in a call (`mem_pending`); in
  particular every pending call gives such a play (`pending_mem`);
* divergent behaviours from divergent plays (`mem_div`);
* productive streams from infinite plays (`mem_inf`); after any completed
  rounds a stream still gives an infinite play (`streamPlay_mem`).

**Injection up to saturation.** `toDStrat t = toDStrat t' ↔ sat t = sat t'`
(`toDStrat_eq_iff`), so `toDStrat (sat t) = toDStrat t` (`toDStrat_sat`) and
`toDStrat` is injective on saturated triples (`toDStrat_injective`).
Saturation also closes the pending calls under their own prefixes: a pending
call `(c ++ ⟨m, n⟩ :: c', m')` shows the play ending in `ask m` after `c`.

Proofs are in `Silmaril.Proofs.Games.Abstract.StratObs.Basic`.
-/

public section

namespace Silmaril.Games.Abstract.StratObs

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B : Type u} {t t' : ObsTriple E S A B}

/-- The finite plays are the runs of the automaton. -/
theorem mem_toDStrat {s : List (Move E (funSig S A B))} :
    s ∈ (toDStrat t).toStrategy ↔ ∃ y, ARun t.1 (satP t) .idle s y := Iff.rfl

/-! ## Saturation -/

/-- Call prefixes are closed under prefixes. -/
theorem satP_prefix {s : S} {a : A} {c c₁ : List (Call E)} {m m₁ : E.Op}
    (h : (c, m) ∈ satP t s a) (hc : CallPre c₁ m₁ c) : (c₁, m₁) ∈ satP t s a :=
  Silmaril.Proofs.Games.Abstract.StratObs.satP_prefix h hc

/-- Saturation is idempotent. -/
theorem sat_idem : sat (sat t) = sat t := Silmaril.Proofs.Games.Abstract.StratObs.sat_idem

/-- Saturated triples are saturations. -/
theorem saturated_sat : Saturated (sat t) := sat_idem

/-- A triple is saturated when its pending calls are its call prefixes. -/
theorem saturated_iff : Saturated t ↔ satP t = t.2.1 :=
  ⟨fun h => congrArg (fun t => t.2.1) h, fun h => by simp [Saturated, sat, h]⟩

/-! ## Reading back the components -/

/-- **Completed rounds** are finished behaviours. -/
theorem mem_round (q : S × A) (c : List (Call E)) (r : (B × S) ⊕ PUnit) :
    (.inr (.ask q) :: (callMoves c ++ [.inr (.ans q r)]) : List (Move E (funSig S A B))) ∈
      (toDStrat t).toStrategy ↔ (c, ansEnd r) ∈ t.1 q.1 q.2 :=
  Silmaril.Proofs.Games.Abstract.StratObs.mem_round q c r

/-- A completed round answering `.inl (b, s')` is a return. -/
theorem mem_ret (s : S) (a : A) (c : List (Call E)) (b : B) (s' : S) :
    (.inr (.ask (s, a)) :: (callMoves c ++ [.inr (.ans (s, a) (.inl (b, s')))]) :
        List (Move E (funSig S A B))) ∈ (toDStrat t).toStrategy ↔ (c, .ret b s') ∈ t.1 s a :=
  mem_round (s, a) c (.inl (b, s'))

/-- A completed round answering `.inr ()` is a trap. -/
theorem mem_trap (s : S) (a : A) (c : List (Call E)) :
    (.inr (.ask (s, a)) :: (callMoves c ++ [.inr (.ans (s, a) (.inr PUnit.unit))]) :
        List (Move E (funSig S A B))) ∈ (toDStrat t).toStrategy ↔ (c, .trap) ∈ t.1 s a :=
  mem_round (s, a) c (.inr PUnit.unit)

/-- **Plays ending in a call** are the call prefixes. -/
theorem mem_pending (q : S × A) (c : List (Call E)) (m : E.Op) :
    (.inr (.ask q) :: (callMoves c ++ [.inl (.ask m)]) : List (Move E (funSig S A B))) ∈
      (toDStrat t).toStrategy ↔ (c, m) ∈ satP t q.1 q.2 :=
  Silmaril.Proofs.Games.Abstract.StratObs.mem_pending q c m

/-- A pending call gives a play ending in its call. -/
theorem pending_mem {q : S × A} {c : List (Call E)} {m : E.Op} (h : (c, m) ∈ t.2.1 q.1 q.2) :
    (.inr (.ask q) :: (callMoves c ++ [.inl (.ask m)]) : List (Move E (funSig S A B))) ∈
      (toDStrat t).toStrategy :=
  (mem_pending q c m).2 (.inl h)

/-- **Divergent plays** are divergent behaviours. -/
theorem mem_div (q : S × A) (c : List (Call E)) :
    (.inr (.ask q) :: callMoves c : List (Move E (funSig S A B))) ∈ (toDStrat t).div ↔
      (c, .div) ∈ t.1 q.1 q.2 :=
  Silmaril.Proofs.Games.Abstract.StratObs.mem_div q c

/-- A stream play is an infinite trace. -/
theorem isInfPlay_streamPlay (pre : List (Move E (funSig S A B))) (q : S × A)
    (ω : ℕ → Call E) : IsInfPlay (streamPlay pre q ω) :=
  Silmaril.Proofs.Games.Abstract.StratObs.isInfPlay_streamPlay pre q ω

/-- After completed rounds, a productive stream gives an infinite play. -/
theorem streamPlay_mem {pre : List (Move E (funSig S A B))} {q : S × A} {ω : ℕ → Call E}
    (hpre : ARun t.1 (satP t) .idle pre .idle) (hω : ω ∈ t.2.2 q.1 q.2) :
    streamPlay pre q ω ∈ (toDStrat t).inf :=
  Silmaril.Proofs.Games.Abstract.StratObs.streamPlay_mem hpre hω

/-- **Infinite one-round plays** are productive streams. -/
theorem mem_inf (q : S × A) (ω : ℕ → Call E) :
    streamPlay [] q ω ∈ (toDStrat t).inf ↔ ω ∈ t.2.2 q.1 q.2 :=
  Silmaril.Proofs.Games.Abstract.StratObs.mem_inf q ω

/-! ## Injection up to saturation -/

/-- **`toDStrat` identifies exactly the triples with the same saturation.** -/
theorem toDStrat_eq_iff : toDStrat t = toDStrat t' ↔ sat t = sat t' :=
  ⟨Silmaril.Proofs.Games.Abstract.StratObs.sat_eq_of_toDStrat,
    Silmaril.Proofs.Games.Abstract.StratObs.toDStrat_eq_of_sat⟩

/-- Saturation does not change the play object. -/
theorem toDStrat_sat : toDStrat (sat t) = toDStrat t := toDStrat_eq_iff.2 sat_idem

/-- On saturated triples, `toDStrat` is injective. -/
theorem toDStrat_injective (ht : Saturated t) (ht' : Saturated t')
    (h : toDStrat t = toDStrat t') : t = t' :=
  ht.symm.trans ((toDStrat_eq_iff.1 h).trans ht')

end Silmaril.Games.Abstract.StratObs
