module

public import Silmaril.Proofs.Wasm.Game.Shared.Runs

/-!
# The closed program after an answered call

After answering an export question the store-passing instance is idle and holds
nothing; the environment is in the host state left by the call. So the closed
program continues as the closed program against `L` in that state
(`closedSh_after_iff`): host state persists across export calls, and the store
of the next call is whatever its question carries.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile} {L : SEnv I.shE} {q₀ : L.S}

open Silmaril.Wasm.Game.ScalarInstance

/-- Steps of the composite system do not depend on the initial host state. -/
theorem step_reinit {q : L.S} (q' : L.S) {x y : (ShCmp I P L q).State}
    {l : Option (Move Sig.empty I.shF)} (h : (ShCmp I P L q).step x l y) :
    (ShCmp I P L q').step x l y := by
  cases h with
  | tau₁ hk => exact .tau₁ hk
  | tau₂ hi => exact .tau₂ hi
  | left g hk => exact .left g hk
  | right g hi => exact .right g hi
  | sync g hk hi => exact .sync g hk hi

/-- Runs of the composite system do not depend on the initial host state. -/
theorem run_reinit {q : L.S} (q' : L.S) {x y : (ShCmp I P L q).State}
    {p : List (Move Sig.empty I.shF)} (h : (ShCmp I P L q).Run x p y) :
    (ShCmp I P L q').Run x p y := by
  induction h with
  | nil x => exact .nil (L := ShCmp I P L q') x
  | tau hs _ ih => exact .tau (step_reinit q' hs) ih
  | vis hs _ ih => exact .vis (step_reinit q' hs) ih

/-- An idle composite state takes no silent step. -/
theorem idle_no_silent {q : L.S} {x : (ShCmp I P L q₀).State}
    (hs : (ShCmp I P L q₀).step ((q, none), .idle) none x) : False := by
  cases hs with
  | tau₁ hk => cases hk
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ask q e => cases hi

/-- Silent runs from an idle state stay there. -/
theorem idle_run_nil {q : L.S} {x y : (ShCmp I P L q₀).State} {p : List (Move Sig.empty I.shF)}
    (h : (ShCmp I P L q₀).Run x p y) (hp : p = []) (hx : x = ((q, none), .idle)) :
    y = ((q, none), .idle) := by
  cases h with
  | nil => exact hx
  | tau hs _ => exact (idle_no_silent (hx ▸ hs)).elim
  | vis _ _ => cases hp

/-- The answer move from a running state goes to the idle state. -/
theorem ans_target_running (f : I.shF.Op) {s : Store Nat} {t : Thread} {q : L.S}
    {a : I.shF.Ar f} {x' : (ShCmp I P L q₀).State}
    (hs : (ShCmp I P L q₀).step ((q, none), .running f s t) (some (.inr (.ans f a))) x') :
    x' = ((q, none), .idle) := by
  cases hs with
  | right g hi =>
    cases hi with
    | oret => rfl

/-- The answer move from a related state goes to the idle state with the same host state. -/
theorem ans_target (f : I.shF.Op) {cq : Config Nat × L.S} {a : I.shF.Ar f}
    {x x' : (ShCmp I P L q₀).State} (hc : ShRel f cq x)
    (hs : (ShCmp I P L q₀).step x (some (.inr (.ans f a))) x') :
    x' = ((cq.2, none), .idle) := by
  rcases hc with ⟨s, t, hx, -⟩ | ⟨s, t, e, h, args, hx, -, -, -⟩
  · rw [hx] at hs
    exact ans_target_running f hs
  · rw [hx] at hs
    exact (not_ans_waiting (q := (some (shOp s e), cq.2)) f hs).elim

/-- A run of the composite reading an answered export call: a product run to a result, the
composite back at the idle state in the final host state. -/
theorem run_answer_inv {f : I.shF.Op} {q : L.S} {s' : Store Nat}
    {w : Answer (I.exports.get f.1)} {y : (ShCmp I P L q).State}
    (h : (ShCmp I P L q).Run (ShCmp I P L q).init [.inr (.ask f), .inr (.ans f (s', w))] y) :
    ∃ (c' : Config Nat) (q' : L.S) (r : Result),
      ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q') ∧ c'.code = r.toAdmin ∧
        c'.store = s' ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
        y = ((q', none), .idle) := by
  obtain ⟨x₁, x₂, hr₁, hs₁, hr₂⟩ := LTS.Run.cons_inv h
  have hx₁ : x₁ = (ShCmp I P L q).init := init_run_nil hr₁ rfl rfl
  have hx₂ : x₂ = ((q, none), .running f f.2.1 (I.shInit f)) := step_ask_inv (hx₁ ▸ hs₁)
  have hc₂ : ShRel (q₀ := q) f (invoke f.2.1 (I.addr f.1) f.2.2.1, q) x₂ :=
    .inl ⟨f.2.1, I.shInit f, hx₂, rfl⟩
  obtain ⟨x₃, x₄, hr₃, hs₃, hr₄⟩ := LTS.Run.cons_inv hr₂
  obtain ⟨⟨c', q'⟩, hrun, hc₃⟩ := shSteps_of_run_nil f hr₃ rfl _ hc₂
  obtain ⟨r, hfinal, hstore, hans⟩ := final_of_step_ans f hc₃ hs₃
  have hy : y = ((q', none), .idle) := idle_run_nil hr₄ rfl (ans_target f hc₃ hs₃)
  exact ⟨c', q', r, hrun, hfinal, hstore, hans, hy⟩

/-- **The closed program after an answered call** continues as the closed program against the
environment in the host state left by some product run of the call. -/
theorem closedSh_after_iff {f : I.shF.Op} {q : L.S} {s' : Store Nat}
    {w : Answer (I.exports.get f.1)} (p : List (Move Sig.empty I.shF)) :
    [.inr (.ask f), .inr (.ans f (s', w))] ++ p ∈ I.closedSh P L q ↔
      ∃ (c' : Config Nat) (q' : L.S) (r : Result),
        ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q') ∧ c'.code = r.toAdmin ∧
          c'.store = s' ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
          p ∈ I.closedSh P L q' := by
  rw [← cmp_denotes P L q]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨xm, hm, hp⟩ := LTS.Run.of_append hy
    obtain ⟨c', q', r, hrun, hfinal, hstore, hans, rfl⟩ := run_answer_inv hm
    have hp' : (ShCmp I P L q').Run (ShCmp I P L q').init p y := run_reinit (q := q) q' hp
    exact ⟨c', q', r, hrun, hfinal, hstore, hans, (cmp_denotes P L q' p).1 ⟨_, hp'⟩⟩
  · rintro ⟨c', q', r, hrun, hfinal, rfl, hans, hp⟩
    obtain ⟨y, hy⟩ := (cmp_denotes P L q' p).2 hp
    have hy' : (ShCmp I P L q).Run ((q', none), .idle) p y := run_reinit (q := q') q hy
    exact ⟨y, (cmp_run_of_run f hrun hfinal hans).append hy'⟩

end Silmaril.Proofs.Wasm.Game.Shared
