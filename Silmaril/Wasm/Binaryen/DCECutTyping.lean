module

public import Silmaril.Wasm.Binaryen.SeqTyping

@[expose] public section

/-! # The typing condition for a DCE cut

A semantic bottom block is not stack polymorphic. A retained prefix ending in
an actual bottom instruction is; deleting a suffix additionally has to preserve
the local-initialization claims of the original typing derivation.
-/

namespace Silmaril.Wasm.Binaryen

open Validation

/-- The last lowered instruction is stack polymorphic. This is a syntactic
condition, independent of the desired typing preservation theorem. -/
def EndsInBot (X : List Instr) : Prop :=
  ∃ pre i, X = pre ++ [i] ∧ botInstr i = true

/-- The syntactic code relation for safe DCE. It changes only structured
children and suffixes following a primitive bottom instruction. In particular,
it does not identify arbitrary semantically bottom blocks with their bodies.
This is a code relation, not an assumed observational certificate. -/
inductive DceCut : List Instr → List Instr → Prop where
  | refl (is : List Instr) : DceCut is is
  | trans {a b c} : DceCut a b → DceCut b c → DceCut a c
  | append {a a' b b'} : DceCut a a' → DceCut b b' → DceCut (a ++ b) (a' ++ b')
  | cut {a} (b : List Instr) : EndsInBot a → DceCut (a ++ b) a
  | block {a b} (bt : BlockType) : DceCut a b → DceCut [.block bt a] [.block bt b]
  | loop {a b} (bt : BlockType) : DceCut a b → DceCut [.loop bt a] [.loop bt b]
  | if_ {a a' b b'} (bt : BlockType) : DceCut a a' → DceCut b b' →
      DceCut [.if_ bt a b] [.if_ bt a' b']
  | tryTable {a b} (bt : BlockType) (cs : List Catch) : DceCut a b →
      DceCut [.tryTable bt cs a] [.tryTable bt cs b]

@[simp] theorem endsInBot_singleton (i : Instr) : EndsInBot [i] ↔ botInstr i = true := by
  constructor
  · rintro ⟨pre, j, he, hj⟩
    have hl : pre.length = 0 := by
      have := congrArg List.length he
      simp only [List.length_append, List.length_singleton] at this
      omega
    have hp := List.length_eq_zero_iff.mp hl
    subst pre
    have hij : i = j := by simpa using he
    subst i
    exact hj
  · intro hi
    exact ⟨[], i, rfl, hi⟩

/-- Retyping a prefix ending in a stack-polymorphic instruction. -/
theorem EndsInBot.retype {X : List Instr} (hb : EndsInBot X)
    {C : Context} {ps rs rs' : List CValType} {xs : List Nat}
    (hC : C.Wf) (h : InstrsOk C X ⟨ps, xs, rs⟩)
    (hok : InstrTypeOk C ⟨ps, xs, rs'⟩) : InstrsOk C X ⟨ps, xs, rs'⟩ := by
  obtain ⟨pre, i, rfl, hi⟩ := hb
  have ht : SeqOk C [.op i (liftInstrs pre)] ⟨ps, xs, rs⟩ := by
    simpa [SeqOk, BExpr.lower, lowerList_liftInstrs] using h
  have ht' := infer_bot (by simp [BExpr.isBot, hi]) ht hok hC hi
  simpa [SeqOk, BExpr.lower, lowerList_liftInstrs] using ht'

/-- A dead suffix may be deleted when the retained prefix is stack polymorphic
and the suffix does not initialize locals. The prefix may contain calls and
local writes: neither is restricted by this typing lemma. -/
theorem TyRepl.drop_bot_suffix {X Y : List Instr} (hb : EndsInBot X)
    (hY : ∀ i ∈ Y, initsLocal i = false) : TyRepl (X ++ Y) X := by
  intro C it hC h
  obtain ⟨m, xs₁, xs₂, h₁, h₂, hL⟩ := InstrsOk.split hC h rfl
  have hr := InstrsOk.regular hC h
  have hr₁ := InstrsOk.regular hC h₁
  have hx₂ := InstrsOk.inits_set h₂ hY
  have hX := hb.retype hC h₁ ⟨hr.1, hr.2.1, hr₁.2.2⟩
  refine .sub hX ⟨ResultSub.refl _ _, ResultSub.refl _ _, ?_⟩ hr
  intro x hx hn
  obtain ⟨lt, hlt⟩ := hr.2.2 x hx
  have hs := hL.set (Context.initLocals_set_of_mem hx hlt)
  rw [Context.initLocals_append, Context.initLocals_of_set hx₂] at hs
  rcases Context.initLocals_set hs with hs | hs
  · exact absurd hs hn
  · exact ⟨_, hs⟩

end Silmaril.Wasm.Binaryen
