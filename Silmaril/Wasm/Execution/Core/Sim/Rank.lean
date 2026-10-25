module

public import Silmaril.Wasm.Execution.Core.Sim.Segments

@[expose] public section

/-! # Contextual ranks for stuttering code simulations

A rank only needs to decrease under deletion and preserve strict decreases under
sequencing and administrative contexts. It need not count value payloads, local
indices, frame data or source-code metadata. `codeSize` remains a lawful rank.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

/-- The well-founded measure laws needed by the closure simulation. -/
class LawfulCodeRank (rank : List Admin → Nat) : Prop where
  context_lt : ∀ (p q : List Admin) {a b : List Admin}, rank a < rank b →
    rank (p ++ a ++ q) < rank (p ++ b ++ q)
  infix_lt : ∀ (p m q : List Admin), m ≠ [] → rank (p ++ q) < rank (p ++ m ++ q)
  label_body_lt : ∀ (p q : List Admin) (n : Nat) (cont : List Instr) (b : List Admin),
    rank b < rank (p ++ [.label n cont b] ++ q)
  label_lt : ∀ (p q : List Admin) (n : Nat) (cont : List Instr) {b₁ b : List Admin},
    rank b₁ < rank b → rank (p ++ [.label n cont b₁] ++ q) < rank (p ++ [.label n cont b] ++ q)
  handler_body_lt : ∀ (p q : List Admin) (n : Nat) (cs : List Catch) (b : List Admin),
    rank b < rank (p ++ [.handler n cs b] ++ q)
  handler_lt : ∀ (p q : List Admin) (n : Nat) (cs : List Catch) {b₁ b : List Admin},
    rank b₁ < rank b → rank (p ++ [.handler n cs b₁] ++ q) < rank (p ++ [.handler n cs b] ++ q)
  frame_body_lt : ∀ (p q : List Admin) (n : Nat) (fi : Frame) (b : List Admin),
    rank b < rank (p ++ [.frame n fi b] ++ q)
  frame_lt : ∀ (p q : List Admin) (n : Nat) (fi : Frame) {b₁ b : List Admin},
    rank b₁ < rank b → rank (p ++ [.frame n fi b₁] ++ q) < rank (p ++ [.frame n fi b] ++ q)

namespace LawfulCodeRank

variable {rank : List Admin → Nat} [LawfulCodeRank rank]

theorem infix_le (p m q : List Admin) : rank (p ++ q) ≤ rank (p ++ m ++ q) := by
  cases m with
  | nil => simp
  | cons a l => exact (infix_lt p (a :: l) q (by simp)).le

theorem append_right_lt {a b : List Admin} (h : rank a < rank b) (q : List Admin) :
    rank (a ++ q) < rank (b ++ q) := by
  simpa using context_lt (rank := rank) [] q h

theorem drop_vals_lt (a w b : List Val) (rest : List Admin) (hw : w ≠ []) :
    rank (vals (a ++ b) ++ rest) < rank (vals (a ++ w ++ b) ++ rest) := by
  have := infix_lt (rank := rank) (vals a) (vals w) (vals b ++ rest) (by simpa [vals] using hw)
  simpa using this

theorem discard_lt (ws us : List Val) (k r r' : List Admin) (hne : us ≠ [] ∨ r ≠ []) :
    rank (vals ws ++ k ++ r') < rank (vals (ws ++ us) ++ k ++ (r ++ r')) := by
  have e : vals (ws ++ us) ++ k ++ (r ++ r') = vals ws ++ vals us ++ (k ++ r ++ r') := by simp
  rw [e]
  rcases hne with hus | hr
  · calc rank (vals ws ++ k ++ r') ≤ rank (vals ws ++ k ++ r ++ r') := infix_le _ _ _
      _ = rank (vals ws ++ (k ++ r ++ r')) := by simp
      _ < rank (vals ws ++ vals us ++ (k ++ r ++ r')) :=
        infix_lt _ _ _ (by simpa [vals] using hus)
  · calc rank (vals ws ++ k ++ r') < rank (vals ws ++ k ++ r ++ r') := infix_lt _ _ _ hr
      _ = rank (vals ws ++ (k ++ r ++ r')) := by simp
      _ ≤ rank (vals ws ++ vals us ++ (k ++ r ++ r')) := infix_le _ _ _

end LawfulCodeRank

private theorem codeSize_ctx_le (p x q : List Admin) : codeSize x ≤ codeSize (p ++ x ++ q) := by
  have := codeSize_append p x
  have := codeSize_append (p ++ x) q
  have := codeSize_pos p
  have := codeSize_pos q
  omega

private theorem codeSize_ctx_lt (p q : List Admin) {a b : List Admin}
    (h : codeSize a < codeSize b) : codeSize (p ++ a ++ q) < codeSize (p ++ b ++ q) := by
  have := codeSize_append p a
  have := codeSize_append p b
  have := codeSize_append (p ++ a) q
  have := codeSize_append (p ++ b) q
  omega

instance : LawfulCodeRank codeSize where
  context_lt := codeSize_ctx_lt
  infix_lt := codeSize_lt_of_infix
  label_body_lt := by
    intro p q n cont b
    exact lt_of_lt_of_le (by simp [codeSize]; omega) (codeSize_ctx_le p _ q)
  label_lt := by
    intro p q n cont b₁ b h
    apply codeSize_ctx_lt
    simp [codeSize] at h ⊢
    omega
  handler_body_lt := by
    intro p q n cs b
    exact lt_of_lt_of_le (by simp [codeSize]; omega) (codeSize_ctx_le p _ q)
  handler_lt := by
    intro p q n cs b₁ b h
    apply codeSize_ctx_lt
    simp [codeSize] at h ⊢
    omega
  frame_body_lt := by
    intro p q n fi b
    exact lt_of_lt_of_le (by simp [codeSize]; omega) (codeSize_ctx_le p _ q)
  frame_lt := by
    intro p q n fi b₁ b h
    apply codeSize_ctx_lt
    simp [codeSize] at h ⊢
    omega

end Silmaril.Wasm.Execution.Core.Sim
