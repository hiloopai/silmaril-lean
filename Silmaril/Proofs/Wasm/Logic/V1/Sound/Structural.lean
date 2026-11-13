module

public import Silmaril.Wasm.Logic.V1.Judgement.Defs

/-!
# Soundness of the structural proof rules

Figure 10 of Watt et al., plus the empty program. These are the rules whose
soundness is about composing and reshaping executions rather than about any
particular instruction, so each is proved directly against `Valid`.

`valid_frame` and `valid_extension` are the two that constrain the semantic
interpretation, and both forced a change to the source's `Silmaril/Wasm/V1/Logic/Semantics.lean` (here `Silmaril.Wasm.Logic.V1.Judgement.Defs`).

1. Both need the final abstract store to agree with the initial one outside
   `Expr.modified code` — that is the content of the paper's
   `fv(H) ∩ mv(e*) = ∅` side condition, which `Indep` renders semantically.
   Figure 17 constrains the final store only by reification, which says nothing
   about the local and global variables `Indep` is about, so `Valid` carries
   that agreement as a conjunct.

2. `valid_extension` further needs a branch or return result to discard an
   *arbitrary* prefix of the operand stack rather than exactly the triple's
   operand frame: the rule runs its subderivation with the enlarged frame
   `vf ++ S`, so the subderivation measures the label assertion above `vf ++ S`
   while the conclusion measures it above `vf`. The paper has no such problem,
   because its semantics transfers exactly the label's arity at a branch and
   discards the rest of the stack (§5). `Satisfies` therefore quantifies the
   discarded prefix existentially.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

variable {H : Type*} {host : HostSemantics H} {n : Nat} {F : List FuncDef}
variable {L : List Assert} {R : Option Assert} {P Q : Assert}

/-- An index at which `l[i]?` is `some` is in range. -/
private theorem lt_length_of_getElem? {α : Type*} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  by_contra hge
  rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at h
  exact absurd h (by simp)

theorem valid_empty : Valid host n F L R P [] P := by
  intro s f ρ vs vf h hf o pre disj reify run
  obtain rfl := BigStepN.nil_inv run
  exact ⟨h, ρ, disj, reify, fun _ _ => rfl, vs, rfl, pre⟩

/-- The agreement conjunct of `[seq]`: variables `e₁ ++ e₂` does not modify are
modified by neither part. -/
private theorem agree_seq {e₁ e₂ : Silmaril.Wasm.V1.Expr} {ρ ρ₁ ρ₂ : Sto}
    (agree₁ : ∀ x, x ∉ Expr.modified e₁ → ρ₁ x = ρ x)
    (agree₂ : ∀ x, x ∉ Expr.modified e₂ → ρ₂ x = ρ₁ x) :
    ∀ x, x ∉ Expr.modified (e₁ ++ e₂) → ρ₂ x = ρ x := by
  intro x hx
  have hx' : x ∉ Expr.modified e₁ ∧ x ∉ Expr.modified e₂ := by
    simpa only [Expr.modified_append, Set.mem_union, not_or] using hx
  exact (agree₂ x hx'.2).trans (agree₁ x hx'.1)

/-- An abrupt result satisfies any normal postcondition: it only looks at the label
and return assertions. -/
private theorem satisfies_of_abrupt {Q S : Assert} {ρ : Sto} {vf : List Value} {h : AHeap}
    {res : BigResult} (abrupt : res.Abrupt) (sat : Satisfies L R Q ρ vf h res) :
    Satisfies L R S ρ vf h res := by
  cases res with
  | normal ws => exact abrupt.elim
  | br l ws => exact sat
  | ret ws => exact sat
  | trap => exact sat

/-- The `[seq]` rule. -/
theorem valid_seq {e₁ e₂ : Silmaril.Wasm.V1.Expr} {S : Assert} (first : Valid host n F L R P e₁ Q)
    (second : Valid host n F L R Q e₂ S) : Valid host n F L R P (e₁ ++ e₂) S := by
  intro s f ρ vs vf h hf o pre disj reify run
  have run' : BigStepN host n s f (vf ++ vs) (expression e₁ ++ expression e₂) o := by
    simpa only [expression, List.map_append] using run
  rcases run'.append_inv with ⟨s₂, f₂, ws, run₁, run₂⟩ | ⟨run₁, abrupt⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, ws', hws, hq⟩ :=
      first s f ρ vs vf h hf _ pre disj reify run₁
    obtain ⟨h₂, ρ₂, disj₂, reify₂, agree₂, sat₂⟩ :=
      second s₂ f₂ ρ₁ ws' vf h₁ hf o hq disj₁ reify₁ (hws ▸ run₂)
    exact ⟨h₂, ρ₂, disj₂, reify₂, agree_seq agree₁ agree₂, sat₂⟩
  · obtain ⟨h₁, ρ₁, disj₁, reify₁, agree₁, sat₁⟩ :=
      first s f ρ vs vf h hf _ pre disj reify run₁
    exact ⟨h₁, ρ₁, disj₁, reify₁,
      fun x hx => agree₁ x fun hm => hx (Expr.subset_modified_append_left e₁ e₂ hm),
      satisfies_of_abrupt abrupt sat₁⟩

/-- The `[consequence]` rule. The paper's `n' ≤ n` stack-length side conditions
on the label and return assertions are unnecessary here: `Valid` has no analogue
of Figure 17's `reifies_lab` and `reifies_ret`, since `BigStepN` carries no
label or return index, so the subderivation can be instantiated at the very same
execution whatever the label assertions' stack lengths are, and `Assert.Entails`
is pointwise. -/
theorem valid_consequence {L' : List Assert} {R' : Option Assert} {P' Q' : Assert} {e : Silmaril.Wasm.V1.Expr}
    (inner : Valid host n F L' R' P' e Q')
    (pre : Assert.Entails P P') (post : Assert.Entails Q' Q)
    (labelLen : L.length = L'.length)
    (labels : ∀ (i : Nat) (P₁ P₁' : Assert), L[i]? = some P₁ → L'[i]? = some P₁' →
      Assert.Entails P₁' P₁)
    (return_ : ∀ R₁' : Assert, R' = some R₁' → ∃ R₁, R = some R₁ ∧ Assert.Entails R₁' R₁) :
    Valid host n F L R P e Q := by
  intro s f ρ vs vf h hf o hp disj reify run
  obtain ⟨os, of, ores⟩ := o
  obtain ⟨h', ρ', disj', reify', agree, sat⟩ :=
    inner s f ρ vs vf h hf _ (pre ρ vs h hp) disj reify run
  refine ⟨h', ρ', disj', reify', agree, ?_⟩
  cases ores with
  | normal ws =>
    obtain ⟨ws', hws, hq⟩ := sat
    exact ⟨ws', hws, post ρ' ws' h' hq⟩
  | br l ws =>
    obtain ⟨P₁', pre', ws', hl', hws, hp'⟩ := sat
    have hlt : l.toNat < L.length := labelLen ▸ lt_length_of_getElem? hl'
    refine ⟨L[l.toNat], pre', ws', List.getElem?_eq_getElem hlt, hws, ?_⟩
    exact labels l.toNat _ P₁' (List.getElem?_eq_getElem hlt) hl' ρ' ws' h' hp'
  | ret ws =>
    obtain ⟨R₁', pre', ws', hR', hws, hr⟩ := sat
    obtain ⟨R₁, hR, ent⟩ := return_ R₁' hR'
    exact ⟨R₁, pre', ws', hR, hws, ent ρ' ws' h' hr⟩
  | trap => exact sat.elim

/-- The `[frame]` rule: the heap frame is distributed through the label and
return assertions as well, which is what makes it sound in the presence of
branches. -/
theorem valid_frame {e : Silmaril.Wasm.V1.Expr} (Hf : HAssert) (inner : Valid host n F L R P e Q)
    (indep : HAssert.Indep (Expr.modified e) Hf) :
    Valid host n F (L.map (fun P' => P'.frame Hf)) (R.map (fun R' => R'.frame Hf))
      (P.frame Hf) e (Q.frame Hf) := by
  intro s f ρ vs vf h hf o hp disj reify run
  obtain ⟨os, of, ores⟩ := o
  obtain ⟨h₁, h₂, d₁₂, rfl, hP, hHf⟩ := hp
  have d₂f : AHeap.Disj h₂ hf := AHeap.disj_union_right disj
  have d₁f : AHeap.Disj h₁ hf := AHeap.disj_union_left disj
  have dmix : AHeap.Disj h₁ (h₂ ∪ hf) := (AHeap.disj_union d₁₂.symm d₁f.symm).symm
  rw [AHeap.union_assoc] at reify
  obtain ⟨h₁', ρ', d', reify', agree, sat⟩ :=
    inner s f ρ vs vf h₁ (h₂ ∪ hf) _ hP dmix reify run
  have d₁'₂ : AHeap.Disj h₁' h₂ := (AHeap.disj_union_left d'.symm).symm
  have d₁'f : AHeap.Disj h₁' hf := (AHeap.disj_union_right d'.symm).symm
  rw [← AHeap.union_assoc] at reify'
  have hHf' : Hf ρ' h₂ := (indep ρ ρ' h₂ fun x hx => (agree x hx).symm).mp hHf
  refine ⟨h₁' ∪ h₂, ρ', AHeap.disj_union d₁'f d₂f, reify', agree, ?_⟩
  cases ores with
  | normal ws =>
    obtain ⟨ws', hws, hq⟩ := sat
    exact ⟨ws', hws, h₁', h₂, d₁'₂, rfl, hq, hHf'⟩
  | br l ws =>
    obtain ⟨P₁, pre', ws', hl, hws, hp₁⟩ := sat
    refine ⟨P₁.frame Hf, pre', ws', ?_, hws, h₁', h₂, d₁'₂, rfl, hp₁, hHf'⟩
    rw [List.getElem?_map, hl, Option.map_some]
  | ret ws =>
    obtain ⟨R₁, pre', ws', hR, hws, hr⟩ := sat
    exact ⟨R₁.frame Hf, pre', ws', by rw [hR, Option.map_some], hws, h₁', h₂, d₁'₂, rfl, hr,
      hHf'⟩
  | trap => exact sat.elim

/-- The `[exists]` rule: the existential is eliminated from the label and return
assertions too, without which it is unsound. -/
theorem valid_exists {α : Type} {L : List (α → Assert)} {R : Option (α → Assert)}
    {P Q : α → Assert} {e : Silmaril.Wasm.V1.Expr}
    (inner : ∀ a, Valid host n F (L.map (fun g => g a)) (R.map (fun g => g a)) (P a) e (Q a)) :
    Valid host n F (L.map Assert.ex) (R.map Assert.ex) (Assert.ex P) e (Assert.ex Q) := by
  intro s f ρ vs vf h hf o hp disj reify run
  obtain ⟨os, of, ores⟩ := o
  obtain ⟨a, hp⟩ := hp
  obtain ⟨h', ρ', d', reify', agree, sat⟩ := inner a s f ρ vs vf h hf _ hp disj reify run
  refine ⟨h', ρ', d', reify', agree, ?_⟩
  cases ores with
  | normal ws =>
    obtain ⟨ws', hws, hq⟩ := sat
    exact ⟨ws', hws, a, hq⟩
  | br l ws =>
    obtain ⟨P₁, pre', ws', hl, hws, hp₁⟩ := sat
    rw [List.getElem?_map] at hl
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hl
    exact ⟨Assert.ex g, pre', ws', by rw [List.getElem?_map, hg, Option.map_some], hws, a, hp₁⟩
  | ret ws =>
    obtain ⟨R₁, pre', ws', hR, hws, hr⟩ := sat
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hR
    exact ⟨Assert.ex g, pre', ws', by rw [hg, Option.map_some], hws, a, hr⟩
  | trap => exact sat.elim

/-- The `[extension]` rule: the analogue of `[frame]` for the operand stack.
Unlike `[frame]` it does not touch the label or return assertions, because the
interpretation already strips the operand frame from every result. -/
theorem valid_extension {e : Silmaril.Wasm.V1.Expr} (S : List (Term Value)) (inner : Valid host n F L R P e Q)
    (indep : ∀ τ ∈ S, Term.Indep (Expr.modified e) τ) :
    Valid host n F L R (Assert.extend S P) e (Assert.extend S Q) := by
  intro s f ρ vs vf h hf o hp disj reify run
  obtain ⟨os, of, ores⟩ := o
  obtain ⟨vs', rfl, hP⟩ := hp
  rw [← List.append_assoc] at run
  obtain ⟨h', ρ', d', reify', agree, sat⟩ :=
    inner s f ρ vs' (vf ++ S.map (fun τ => τ ρ)) h hf _ hP disj reify run
  have hagree : ∀ x, x ∉ Expr.modified e → ρ x = ρ' x := fun x hx => (agree x hx).symm
  have hS : S.map (fun τ => τ ρ') = S.map (fun τ => τ ρ) :=
    List.map_congr_left fun τ hτ => (indep τ hτ ρ ρ' hagree).symm
  refine ⟨h', ρ', d', reify', agree, ?_⟩
  cases ores with
  | normal ws =>
    obtain ⟨ws', hws, hq⟩ := sat
    refine ⟨S.map (fun τ => τ ρ) ++ ws', by rw [hws, List.append_assoc], ws', ?_, hq⟩
    rw [hS]
  | br l ws => exact sat
  | ret ws => exact sat
  | trap => exact sat.elim

/-- The `[context]` rule: a triple only promises to branch to targets in `L`, so
`L` may be enlarged. -/
theorem valid_context {Lf : List Assert} {e : Silmaril.Wasm.V1.Expr} (inner : Valid host n F L R P e Q) :
    Valid host n F (L ++ Lf) R P e Q := by
  intro s f ρ vs vf h hf o hp disj reify run
  obtain ⟨os, of, ores⟩ := o
  obtain ⟨h', ρ', d', reify', agree, sat⟩ := inner s f ρ vs vf h hf _ hp disj reify run
  refine ⟨h', ρ', d', reify', agree, ?_⟩
  cases ores with
  | normal ws => exact sat
  | br l ws =>
    obtain ⟨P₁, pre', ws', hl, hws, hp₁⟩ := sat
    exact ⟨P₁, pre', ws',
      by rw [List.getElem?_append_left (lt_length_of_getElem? hl), hl], hws, hp₁⟩
  | ret ws => exact sat
  | trap => exact sat.elim

/-- A triple with no return assertion never returns, so one may be supplied. -/
theorem valid_contextRet {e : Silmaril.Wasm.V1.Expr} (inner : Valid host n F L none P e Q) :
    Valid host n F L R P e Q := by
  intro s f ρ vs vf h hf o hp disj reify run
  obtain ⟨os, of, ores⟩ := o
  obtain ⟨h', ρ', d', reify', agree, sat⟩ := inner s f ρ vs vf h hf _ hp disj reify run
  refine ⟨h', ρ', d', reify', agree, ?_⟩
  cases ores with
  | normal ws => exact sat
  | br l ws => exact sat
  | ret ws =>
    obtain ⟨_, _, _, hR, -, -⟩ := sat
    exact absurd hR (by simp)
  | trap => exact sat.elim

end Silmaril.Wasm.Logic.V1
