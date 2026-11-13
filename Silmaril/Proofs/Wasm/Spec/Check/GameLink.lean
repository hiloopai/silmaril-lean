module

public import Silmaril.Wasm.Spec.Check.Defs
public import Silmaril.Wasm.Logic.GameLink.Thms

@[expose] public section

/-!
# Verification conditions for the simple Wasm specifications: soundness

From a proof in the every-run Hoare logic (`GameSat`) whose interface specifications constrain
only Proponent moves, every trace of the program satisfies them (`gameSat_icall`,
`gameSat_ret`), hence the simple sentences hold (`callPre_of_gameSat`, `neverCall_of_gameSat`,
`assertNeverFalse_of_gameSat`, `retPost_of_gameSat`). Every profile.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Strategy (ISpec AG MoveGood agStrat)
open Silmaril.Wasm.Logic.GameLink (GameSat)

/-- When every Opponent move is allowed, an assume/guarantee correct play has only allowed
Proponent moves. -/
theorem ag_moves_good {E F : Sig.{0}} {I : ISpec E} {S : ISpec F}
    (hO : ∀ m : Move E F, m.IsO → MoveGood I S m) :
    ∀ {p : List (Move E F)}, AG I S p → ∀ m ∈ p, m.IsP → MoveGood I S m
  | [], _, _, hm, _ => absurd hm List.not_mem_nil
  | x :: p, ⟨hOx, hPx⟩, m, hm, hmP => by
    have hp : AG I S p :=
      (Silmaril.Wasm.Logic.Strategy.Move.isO_or_isP x).elim (fun h => hOx h (hO x h))
        (fun h => (hPx h).2)
    rcases List.mem_cons.1 hm with rfl | hm
    · exact (hPx hmP).1
    · exact ag_moves_good hO hp m hm hmP

/-- Opponent moves are allowed when every export question and every import answer is. -/
theorem opp_good {E F : Sig.{0}} {I : ISpec E} {S : ISpec F} (hS : ∀ f, S.pre f)
    (hI : ∀ e v, I.post e v) : ∀ m : Move E F, m.IsO → MoveGood I S m
  | .inl (.ask _), h => absurd h id
  | .inl (.ans e v), _ => hI e v
  | .inr (.ask f), _ => hS f
  | .inr (.ans _ _), h => absurd h id

/-- The move read as an import call event. -/
theorem moveEvent_eq_icall {X : WIface} {m : Move (ifaceSig X.imports) (ifaceSig X.exports)}
    {i : X.Imp} {a : List Val} (h : moveEvent m = Event.icall i a) :
    ∃ e, e.1 = i ∧ e.2.1 = a ∧ m = .inl (.ask e) := by
  rcases m with (e | ⟨e, v⟩) | (f | ⟨f, w⟩)
  · simp only [moveEvent, Sum.map_inl, evOf, Event.icall, Sum.inl.injEq, SideEv.ask.injEq] at h
    exact ⟨e, h.1, h.2, rfl⟩
  · cases h
  · cases h
  · cases h

/-- The move read as an export return event. -/
theorem moveEvent_eq_ret' {X : WIface} {m : Move (ifaceSig X.imports) (ifaceSig X.exports)}
    {j : X.Exp} {b : Behaviour Val} (h : moveEvent m = Event.ret j b) :
    ∃ f w, f.1 = j ∧ Answer.toBehaviour (ft := X.exports.get f.1) w = b ∧ m = .inr (.ans f w) := by
  rcases m with (e | ⟨e, v⟩) | (f | ⟨f, w⟩)
  · cases h
  · cases h
  · cases h
  · simp only [moveEvent, Sum.map_inr, evOf, Event.ret, Sum.inr.injEq, SideEv.ans.injEq] at h
    exact ⟨f, w, h.1, h.2, rfl⟩

variable {P : Profile} {X : WIface} {p : WasmProg X} {Inv : Store Nat → Prop}
  {Ii : ISpec (ifaceSig X.imports)} {Ie : ISpec (ifaceSig X.exports)}

/-- **Import calls of verified programs** (every profile): from a Hoare-logic proof whose
Opponent side is unconstrained, every import call in every trace is allowed. -/
theorem gameSat_icall (hm : GameSat P p.inst Inv Ii Ie) (hs : Inv p.store) (hS : ∀ f, Ie.pre f)
    (hI : ∀ e v, Ii.post e v) {t : List (WEvent X)} (ht : t ∈ (wasmSem P).traces p) {i : X.Imp}
    {a : List Val} (hc : Event.icall i a ∈ t) : ∃ e, e.1 = i ∧ e.2.1 = a ∧ Ii.pre e := by
  obtain ⟨q, hq, rfl⟩ := ht
  have hag : AG Ii Ie q := (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hq).2
  obtain ⟨m, hmq, hme⟩ := List.mem_map.1 hc
  obtain ⟨e, hei, hea, rfl⟩ := moveEvent_eq_icall hme
  have hgood : MoveGood Ii Ie (.inl (.ask e)) := ag_moves_good (opp_good hS hI) hag _ hmq trivial
  exact ⟨e, hei, hea, hgood⟩

/-- **Export returns of verified programs** (every profile). -/
theorem gameSat_ret (hm : GameSat P p.inst Inv Ii Ie) (hs : Inv p.store) (hS : ∀ f, Ie.pre f)
    (hI : ∀ e v, Ii.post e v) {t : List (WEvent X)} (ht : t ∈ (wasmSem P).traces p) {j : X.Exp}
    {b : Behaviour Val} (hc : Event.ret j b ∈ t) :
    ∃ f w, f.1 = j ∧ Answer.toBehaviour (ft := X.exports.get f.1) w = b ∧ Ie.post f w := by
  obtain ⟨q, hq, rfl⟩ := ht
  have hag : AG Ii Ie q := (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hq).2
  obtain ⟨m, hmq, hme⟩ := List.mem_map.1 hc
  obtain ⟨f, w, hfj, hwb, rfl⟩ := moveEvent_eq_ret' hme
  have hgood : MoveGood Ii Ie (.inr (.ans f w)) := ag_moves_good (opp_good hS hI) hag _ hmq trivial
  exact ⟨f, w, hfj, hwb, hgood⟩

/-- **The verification condition for call preconditions is sound** (every profile). -/
theorem callPre_of_gameSat {i : X.Imp} {Pre : List Val → Prop} {Q : Behaviour Val → Prop}
    {j : Option X.Exp}
    (hm : GameSat P p.inst Inv (importGuard X.imports i Pre) (exportGuard X.exports j Q))
    (hs : Inv p.store) :
    Models (callPre FnType (List Val) (Behaviour Val)) (wasmSem P) p ⟨i, Pre⟩ := by
  rw [models_iff]
  intro t ht a hc
  obtain ⟨e, hei, rfl, hpre⟩ := gameSat_icall hm hs (fun _ => trivial) (fun _ _ => trivial) ht hc
  exact hpre hei

/-- **The verification condition for "never called" is sound** (every profile). -/
theorem neverCall_of_gameSat {i : X.Imp} {Q : Behaviour Val → Prop} {j : Option X.Exp}
    (hm : GameSat P p.inst Inv (importGuard X.imports i fun _ => False) (exportGuard X.exports j Q))
    (hs : Inv p.store) : Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) p i := by
  rw [models_iff]
  intro t ht a hc
  obtain ⟨e, hei, rfl, hpre⟩ := gameSat_icall hm hs (fun _ => trivial) (fun _ _ => trivial) ht hc
  exact hpre hei

/-- **The verification condition for "assert never false" is sound** (every profile). -/
theorem assertNeverFalse_of_gameSat {i : X.Imp} {Q : Behaviour Val → Prop} {j : Option X.Exp}
    (hm : GameSat P p.inst Inv (importGuard X.imports i assertOk) (exportGuard X.exports j Q))
    (hs : Inv p.store) : Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) p i := by
  rw [models_iff]
  intro t ht a hc
  obtain ⟨e, hei, rfl, hpre⟩ := gameSat_icall hm hs (fun _ => trivial) (fun _ _ => trivial) ht hc
  exact hpre hei

/-- **The verification condition for return postconditions is sound** (every profile). -/
theorem retPost_of_gameSat {j : X.Exp} {Q : Behaviour Val → Prop} {i : X.Imp}
    {Pre : List Val → Prop}
    (hm : GameSat P p.inst Inv (importGuard X.imports i Pre) (exportGuard X.exports (some j) Q))
    (hs : Inv p.store) :
    Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p ⟨j, Q⟩ := by
  rw [models_iff]
  intro t ht b hc
  obtain ⟨f, w, hfj, rfl, hpost⟩ :=
    gameSat_ret hm hs (fun _ => trivial) (fun _ _ => trivial) ht hc
  exact hpost (congrArg some hfj.symm)

end Silmaril.Wasm.Spec
