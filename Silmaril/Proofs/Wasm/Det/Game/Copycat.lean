module

public import Silmaril.Wasm.Det.Game.Defs
public import Silmaril.Games.Composition.Thms

/-!
# Copycat is deterministic and strict; a nondeterministic environment

Every Proponent move of copycat forwards the Opponent move just before it (`double_next`), so
copycat is deterministic and strict for any traps. Composing the nondeterministic strategy
`ndBool` (answering `true` or `false`) with copycat gives `ndBool` back (`comp_id`), which is
not deterministic.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Det.Game

universe u

variable {E : Sig.{u}}

/-- The move copycat forwards after an Opponent move. -/
def mirror : Move E E → Move E E
  | .inr (.ask q) => .inl (.ask q)
  | .inl (.ans m n) => .inr (.ans m n)
  | x => x

/-- **A Proponent move of copycat forwards the previous move.** -/
theorem double_next : ∀ {w : List (Ev E)} {p : List (Move E E)} {m : Move E E},
    p ++ [m] <+: Ev.double w → m.IsP → ∃ p₀ o, p = p₀ ++ [o] ∧ m = mirror o
  | [], p, m, h, _ => by
    have := h.length_le
    simp at this
  | x :: w, p, m, h, hm => by
    rw [Ev.double_cons] at h
    match p, x, h with
    | [], .ask q, h => simp [Ev.copy_ask] at h; subst h; exact hm.elim
    | [], .ans q n, h => simp [Ev.copy_ans] at h; subst h; exact hm.elim
    | [y], .ask q, h =>
      simp [Ev.copy_ask] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨[], _, rfl, rfl⟩
    | [y], .ans q n, h =>
      simp [Ev.copy_ans] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨[], _, rfl, rfl⟩
    | y :: z :: p', .ask q, h =>
      simp only [Ev.copy_ask, List.cons_append, List.nil_append, List.cons_prefix_cons] at h
      obtain ⟨rfl, rfl, h⟩ := h
      obtain ⟨p₀, o, rfl, rfl⟩ := double_next h hm
      exact ⟨_ :: _ :: p₀, o, rfl, rfl⟩
    | y :: z :: p', .ans q n, h =>
      simp only [Ev.copy_ans, List.cons_append, List.nil_append, List.cons_prefix_cons] at h
      obtain ⟨rfl, rfl, h⟩ := h
      obtain ⟨p₀, o, rfl, rfl⟩ := double_next h hm
      exact ⟨_ :: _ :: p₀, o, rfl, rfl⟩

/-- **Copycat is deterministic** (for any traps). -/
theorem detMod_id (t : Traps E) : DetMod t (Strategy.id E) := by
  rintro p m₁ m₂ ⟨w₁, -, h₁⟩ ⟨w₂, -, h₂⟩ hm₁ hm₂ -
  obtain ⟨p₁, o₁, rfl, rfl⟩ := double_next h₁ hm₁
  obtain ⟨p₂, o₂, h, rfl⟩ := double_next h₂ hm₂
  obtain ⟨-, rfl⟩ := List.append_inj' h rfl |>.imp id (fun h => by simpa using h)
  exact .inl rfl

/-- **Copycat is strict** (the same traps on both sides). -/
theorem strict_id (t : Traps E) : Strict t t (Strategy.id E) := by
  rintro p m n b ⟨w, hw, h⟩ ht
  have hl := Ev.legal_of_prefix_double hw h
  obtain ⟨y, hy⟩ := hl
  have hy' : Path .idle ((p ++ [.inl (.ans m n)]) ++ [b]) y := by simpa using hy
  obtain ⟨x, hx, hxb⟩ := Path.concat_iff.1 hy'
  obtain ⟨x₀, -, hx₀⟩ := Path.concat_iff.1 hx
  have hb : b.IsP := hx₀.isP_of_isO trivial hxb
  have h' : (p ++ [.inl (.ans m n)]) ++ [b] <+: Ev.double w := by simpa using h
  obtain ⟨p₀, o, he, rfl⟩ := double_next h' hb
  obtain ⟨-, rfl⟩ := List.append_inj' he rfl |>.imp id (fun h => by simpa using h)
  exact ht

/-! ## A nondeterministic environment -/

theorem ndBool_mem (b : Bool) :
    ([.inr (.ask ()), .inr (.ans () b)] : List (Move boolSig boolSig)) ∈ ndBool := by
  refine Strategy.subset_generate ?_
    ⟨_, .cons (Step.ask (E := boolSig) (F := boolSig) ())
      (.cons (Step.ret (E := boolSig) (F := boolSig) () b) (.nil _))⟩
  cases b
  · exact .inr rfl
  · exact .inl rfl

theorem ndBool_not_detMod : ¬ DetMod (noTraps boolSig) ndBool := by
  intro h
  rcases h [.inr (.ask ())] (.inr (.ans () true)) (.inr (.ans () false)) (ndBool_mem true)
    (ndBool_mem false) trivial trivial
    (fun m hm => by simp only [List.mem_singleton] at hm; subst hm; exact id) with h | h | h
  · simp only [Sum.inr.injEq] at h
    injection h with _ h₂
    exact Bool.noConfusion h₂
  · exact h
  · exact h

/-- **Composing a deterministic, strict strategy with a nondeterministic environment is not
deterministic.** -/
theorem comp_nondet :
    DetMod (noTraps boolSig) (Strategy.id boolSig) ∧
      Strict (noTraps boolSig) (noTraps boolSig) (Strategy.id boolSig) ∧
      ¬ DetMod (noTraps boolSig) (ndBool.comp (Strategy.id boolSig)) := by
  refine ⟨detMod_id _, strict_id _, ?_⟩
  rw [Strategy.comp_id]
  exact ndBool_not_detMod

end Silmaril.Proofs.Wasm.Det.Game
