module

public import Silmaril.Wasm.Jco.Bridge.State.Defs
public import Silmaril.Wasm.Jco.Bridge.Thms
public import Silmaril.Games.LTS.Thms
public import Silmaril.Games.Strategy.Thms
public import Silmaril.Proofs.Wasm.Jco.Bridge.Mem

/-!
# Relating the two settings for stateful modules: proofs

Proofs of `Silmaril.Wasm.Jco.Bridge.State.Thms`.

* Memory side: `specCall_state`. Over the instance of a stateful module, a memory-free world
  function under the C convention is `RM.ofFun` of `stateCall`.
* IR side: the state machine has no silent steps (`run_nil`). A run along the play of questions
  `qs` answered by `rs` forces `rs` to be the machine's answers (`run_plays`). The machine's
  answers give a run (`run_answers`), and such plays are legal (`path_plays`). A play of
  questions and answers does not end with an Opponent move (`plays_last`).
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Bridge.State

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Bridge
open Silmaril.Wasm.Jco (PTy PVal Meta inMem)

variable {σ : Type}

/-! ## The memory side -/

theorem ofOption_bind_ofFun {α β : Type} (o : Option α) (h : α → σ → Option (β × σ)) :
    (Silmaril.Wasm.Jco.RM.ofOption o >>= fun a => Silmaril.Wasm.Jco.RM.ofFun (h a)) =
      Silmaril.Wasm.Jco.RM.ofFun fun st => o.bind fun a => h a st := by
  cases o with
  | none => simp only [Silmaril.Wasm.Jco.RM.ofOption_none, Silmaril.Wasm.Jco.RM.fail_bind]; rfl
  | some a => simp only [Silmaril.Wasm.Jco.RM.ofOption_some, Silmaril.Wasm.Jco.RM.pure_bind]; rfl

theorem ofFun_bind_ofOption {α β : Type} (f : σ → Option (α × σ)) (g : α → Option β) :
    (Silmaril.Wasm.Jco.RM.ofFun f >>= fun a => Silmaril.Wasm.Jco.RM.ofOption (g a)) =
      Silmaril.Wasm.Jco.RM.ofFun fun st => (f st).bind fun p => (g p.1).map fun b => (b, p.2) := by
  funext s o
  apply propext
  rw [Silmaril.Wasm.Jco.RM.bind_apply]
  unfold Silmaril.Wasm.Jco.RM.ofFun
  rcases hf : f s with _ | ⟨a, s'⟩
  · simp only [hf, Option.bind_none]
    constructor
    · rintro (⟨_, _, h, -⟩ | ⟨-, h⟩)
      · cases h
      · exact h
    · intro h
      exact .inr ⟨by trivial, h⟩
  · rcases hg : g a with _ | b
    · simp [Silmaril.Wasm.Jco.RM.ofOption, Silmaril.Wasm.Jco.RM.fail, hf, hg]
    · simp [Silmaril.Wasm.Jco.RM.ofOption, Silmaril.Wasm.Jco.RM.pure, hf, hg]

/-- Over the instance of a stateful module, a memory-free world function under the C convention
is `stateCall`. -/
theorem specCall_state (md : Meta) (m : SMod σ) (s : Silmaril.Wasm.Jco.Sig) (hp : s.params.all PTy.memFree = true)
    (hr : inMem s.result = false) (vs : List Val) :
    md.specCall m.inst s (vs.map PVal.val) = Silmaril.Wasm.Jco.RM.ofFun (stateCall m s vs) := by
  have hl : md.specParams m.inst s.params (vs.map PVal.val) =
      Silmaril.Wasm.Jco.RM.ofOption (checkLower (s.params.map PTy.toVal) vs) := by
    rw [← Silmaril.Wasm.Jco.lowerParams_memFree m.inst md (m.inst.call "") s.params _ hp,
      Silmaril.Proofs.Wasm.Jco.Bridge.lowerParams_val m.inst _ s.params vs hp]
  have hc : ∀ xs, m.inst.call s.name xs = Silmaril.Wasm.Jco.RM.ofFun (m.callN s.name xs) :=
    fun _ => rfl
  simp only [Meta.specCall, hr, Bool.false_eq_true, ↓reduceIte, hl, hc,
    Silmaril.Proofs.Wasm.Jco.Bridge.liftResult_val m.inst s.result hr]
  refine (Silmaril.Wasm.Jco.RM.bind_congr fun xs => ofFun_bind_ofOption (σ := σ) _ _).trans ?_
  exact ofOption_bind_ofFun _ _

/-! ## The IR side -/

variable (m : SMod σ)

theorem run_nil {x y : m.lts.State} (h : m.lts.Run x [] y) : y = x := by
  cases h with
  | nil => rfl
  | tau hs => cases hs

theorem run_plays : ∀ (qs : List m.Q) (rs : List (Option Payload)) (s : σ) (y : m.lts.State),
    m.lts.Run (s, none) (m.plays qs rs) y → rs.length = qs.length → rs = (m.answers s qs).1
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | q :: qs, r :: rs, s, y, hrun, hlen => by
    obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv hrun
    have e₁ : x₁ = (s, none) := run_nil m h₁
    subst e₁
    have e₂ : x₂ = (s, some q) := by cases h₂; rfl
    subst e₂
    obtain ⟨y₁, y₂, g₁, g₂, g₃⟩ := LTS.Run.cons_inv h₃
    have e₃ : y₁ = (s, some q) := run_nil m g₁
    subst e₃
    have e₄ : r = (m.ans q s).1 ∧ y₂ = ((m.ans q s).2, none) := by
      cases g₂
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := e₄
    have ih := run_plays qs rs (m.ans q s).2 y g₃ (by simpa using hlen)
    simp only [SMod.answers, ih]

theorem run_answers : ∀ (qs : List m.Q) (s : σ),
    m.lts.Run (s, none) (m.plays qs (m.answers s qs).1) ((m.answers s qs).2, none)
  | [], _ => .nil _
  | q :: qs, s => by
    have h₁ : m.lts.step (s, none) (some (.inr (.ask q))) (s, some q) := SMod.Step.ask s q
    have h₂ : m.lts.step (s, some q) (some (.inr (.ans q (m.ans q s).1)))
        ((m.ans q s).2, none) := SMod.Step.ret s q
    exact .vis h₁ (.vis h₂ (run_answers qs (m.ans q s).2))

theorem path_plays : ∀ (qs : List m.Q) (rs : List (Option Payload)),
    Path .idle (m.plays qs rs) .idle
  | [], _ => .nil _
  | _ :: _, [] => .nil _
  | q :: qs, r :: rs => .cons (.ask q) (.cons (.ret q r) (path_plays qs rs))

theorem getLast_plays : ∀ (qs : List m.Q) (rs : List (Option Payload)),
    (m.plays qs rs).getLast? = none ∨ ∃ q r, (m.plays qs rs).getLast? = some (.inr (.ans q r))
  | [], _ => .inl rfl
  | _ :: _, [] => .inl rfl
  | q :: qs, r :: rs => by
    rcases getLast_plays qs rs with h | ⟨q', r', h⟩
    · have e : m.plays qs rs = [] := List.getLast?_eq_none_iff.1 h
      refine .inr ⟨q, r, ?_⟩
      simp [SMod.plays, e]
    · refine .inr ⟨q', r', ?_⟩
      have hne : m.plays qs rs ≠ [] := fun he => by simp [he] at h
      rw [SMod.plays, List.getLast?_cons_cons, List.getLast?_cons, h]
      cases hp : m.plays qs rs with
      | nil => exact absurd hp hne
      | cons a l => rfl

theorem plays_last (qs : List m.Q) (rs : List (Option Payload)) (p₀ : List m.Mv) (o : m.Mv)
    (h : m.plays qs rs = p₀ ++ [o]) : ¬ o.IsO := by
  have hl : (m.plays qs rs).getLast? = some o := by rw [h]; simp
  rcases getLast_plays m qs rs with h' | ⟨q, r, h'⟩
  · rw [h'] at hl
    cases hl
  · rw [h'] at hl
    cases hl
    simp [Move.IsO]

/-- **The IR strategy of a stateful module contains exactly the plays it answers.** -/
theorem mem_sem_iff (qs : List m.Q) (rs : List (Option Payload)) (hlen : rs.length = qs.length) :
    m.plays qs rs ∈ Strategy.ofLTS m.lts ↔ rs = (m.answers m.init qs).1 := by
  constructor
  · intro hp
    obtain ⟨-, t, ht, hpre⟩ := Strategy.mem_generate.1 hp
    rcases hpre with hpre | ⟨p₀, o, he, -, ho⟩
    · have htr : m.plays qs rs ∈ m.lts.Traces := by
        rcases ht with rfl | ⟨ht, -⟩
        · have e : m.plays qs rs = [] := List.prefix_nil.1 hpre
          rw [e]
          exact ⟨_, .nil _⟩
        · exact LTS.traces_of_prefix ht hpre
      obtain ⟨y, hy⟩ := htr
      exact run_plays m qs rs m.init y hy hlen
    · exact absurd ho (plays_last m qs rs p₀ o he)
  · intro h
    subst h
    exact Strategy.mem_ofLTS_of_mem_traces ⟨_, run_answers m qs m.init⟩ ⟨_, path_plays m qs _⟩

/-! ## The module's answers and its instance -/

theorem callN_export (i : Fin m.exports.length) (xs : List Flat) (s : σ) :
    m.callN (m.exports[i]).1 xs s = m.fn (m.exports[i]).1 xs s := by
  have hm : m.exports.any (·.1 == (m.exports[i]).1) = true :=
    List.any_eq_true.2 ⟨m.exports[i], List.getElem_mem _, by simp⟩
  simp only [SMod.callN, hm, ↓reduceIte]

theorem inst_ok (i : Fin m.exports.length) (xs ys : List Flat) (s s' : σ) :
    m.inst.call (m.exports[i]).1 xs s (.ok ys s') ↔ m.ans (i, .flat xs) s = (some (.flat ys), s') := by
  show Silmaril.Wasm.Jco.RM.ofFun (m.callN (m.exports[i]).1 xs) s (.ok ys s') ↔ _
  unfold Silmaril.Wasm.Jco.RM.ofFun SMod.ans
  rw [callN_export]
  simp only [Fin.getElem_fin]
  rcases m.fn (m.exports[i.1]).1 xs s with _ | ⟨ys', s''⟩ <;> simp [eq_comm]

theorem inst_trap (i : Fin m.exports.length) (xs : List Flat) (s : σ) :
    m.inst.call (m.exports[i]).1 xs s .trap ↔ (m.ans (i, .flat xs) s).1 = none := by
  show Silmaril.Wasm.Jco.RM.ofFun (m.callN (m.exports[i]).1 xs) s .trap ↔ _
  unfold Silmaril.Wasm.Jco.RM.ofFun SMod.ans
  rw [callN_export]
  simp only [Fin.getElem_fin]
  rcases m.fn (m.exports[i.1]).1 xs s with _ | ⟨ys', s''⟩ <;> simp

end Silmaril.Proofs.Wasm.Jco.Bridge.State
