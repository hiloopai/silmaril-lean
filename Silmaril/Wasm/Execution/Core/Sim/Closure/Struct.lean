module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic

@[expose] public section

/-! # Closure proof: structured-instruction heads

`struct_case`: a redex step at a plain instruction related by `InstrRel`
(`block`, `loop`, `if`, `try_table` with `InstrsRel`-related bodies, or the
identity). Plan: the identity is `transport_lift`; for a structured instruction
invert the step (`block`/`loop`/`if-true`/`if-false`/`try_table` and their
arity-mismatch traps) and take the same rule on the right, relating the new
`LABEL`/`HANDLER` bodies with `AdminRel.label`/`.handler` and `AdminsRel.src`. -/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type}

variable {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

variable {rank : List Admin → Nat}

namespace Closure

/-- A structured instruction: `block`, `loop`, `if` or `try_table`. -/
def IsStructInstr : Instr → Prop
  | .block _ _ | .loop _ _ | .if_ _ _ _ | .tryTable _ _ _ => True
  | _ => False

theorem IsStructInstr.val?_eq {i : Instr} (hi : IsStructInstr i) : (Admin.plain i).val? = none := by
  cases i <;> first | rfl | exact (hi : False).elim

theorem IsStructInstr.not_isCallRef {i : Instr} (hi : IsStructInstr i) :
    ¬ (Admin.plain i).IsCallRef := by
  cases i <;> first | exact (hi : False).elim | exact id

theorem IsStructInstr.not_isReturnCallRef {i : Instr} (hi : IsStructInstr i) :
    ¬ (Admin.plain i).IsReturnCallRef := by
  cases i <;> first | exact (hi : False).elim | exact id

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **Structured redexes.** A step of `val* i` with `i` structured is the
`block`/`loop`/`if`/`try_table` rule (under `ctxt-instrs`). It neither reads nor
changes the store, and the same rule applies to any `InstrRel`-related `i'` on any
store, with `AdminsRel`-related results. -/
theorem struct_match_aux {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (i i' : Instr), c.code = vals us ++ [.plain i] → IsStructInstr i →
      InstrRel BI i i' →
      c'.store = c.store ∧ ∃ r', AdminsRel BI B c'.code r' ∧
        ∀ t : Store H, Step P host ⟨t, c.frame, vals us ++ [.plain i']⟩ ⟨t, c'.frame, r'⟩ := by
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us i i' hc hi hii'
    dsimp only at hc ⊢
    obtain ⟨u₁, b, is₁, hb, rfl⟩ := exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ u₁) ++ b :: (is₁ ++ rest) = vals us ++ Admin.plain i :: [] := by
      rw [← hc]; simp
    obtain ⟨h1, rfl, h3⟩ := vals_append_cons_inj hb hi.val?_eq hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨hs', r', hr, hstep⟩ := ih u₁ i i' rfl hi hii'
    subst h1
    refine ⟨hs', vals vs₀ ++ r' ++ [], ((AdminsRel.refl _).append hr).append .nil, fun t => ?_⟩
    have := Step.ctxtInstrs (vs := vs₀) (rest := []) (hstep t) hne
    simpa using this
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro us i i' hc hi hii'
    dsimp only at hc ⊢
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc
    cases hi'
    cases hii' with
    | refl => exact ⟨rfl, _, AdminsRel.refl _, fun t => .block hbt hm⟩
    | block _ hb =>
      exact ⟨rfl, _, .cons (.label _ .nil ((AdminsRel.refl _).append (.src hb))) .nil,
        fun t => .block hbt hm⟩
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro us i i' hc hi hii'
    dsimp only at hc ⊢
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc
    cases hi'
    cases hii' with
    | refl => exact ⟨rfl, _, AdminsRel.refl _, fun t => .loop hbt hm⟩
    | loop _ hb =>
      exact ⟨rfl, _, .cons (.label _ (.cons (.loop _ hb) .nil)
        ((AdminsRel.refl _).append (.src hb))) .nil, fun t => .loop hbt hm⟩
  | @ifTrue s f c bt b₁ b₂ hc0 =>
    intro us i i' hc hi hii'
    have hc' : vals [Val.i32 c] ++ Admin.plain (.if_ bt b₁ b₂) :: [] =
        vals us ++ Admin.plain i :: [] := hc
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc'
    cases hi'
    cases hii' with
    | refl => exact ⟨rfl, _, AdminsRel.refl _, fun t => .ifTrue hc0⟩
    | if_ _ h₁ h₂ => exact ⟨rfl, _, .cons (.plain (.block _ h₁)) .nil, fun t => .ifTrue hc0⟩
  | @ifFalse s f bt b₁ b₂ =>
    intro us i i' hc hi hii'
    have hc' : vals [Val.i32 0] ++ Admin.plain (.if_ bt b₁ b₂) :: [] =
        vals us ++ Admin.plain i :: [] := hc
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc'
    cases hi'
    cases hii' with
    | refl => exact ⟨rfl, _, AdminsRel.refl _, fun t => .ifFalse⟩
    | if_ _ h₁ h₂ => exact ⟨rfl, _, .cons (.plain (.block _ h₂)) .nil, fun t => .ifFalse⟩
  | @tryTable s f bt cs body vs t₁ t₂ hbt hm =>
    intro us i i' hc hi hii'
    dsimp only at hc ⊢
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc
    cases hi'
    cases hii' with
    | refl => exact ⟨rfl, _, AdminsRel.refl _, fun t => .tryTable hbt hm⟩
    | tryTable _ _ hb =>
      exact ⟨rfl, _, .cons (.handler _ _ (.cons (.label _ .nil
        ((AdminsRel.refl _).append (.src hb))) .nil)) .nil, fun t => .tryTable hbt hm⟩
  | @trapInstrs s f vs₀ rest hne =>
    intro us i i' hc hi hii'
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.plain i :: [] := by
      rw [← hc]; simp
    exact absurd (vals_append_cons_inj val?_trap hi.val?_eq hc').2.1 (by simp)
  | @throwRefInstrs s f vs₀ a rest hne =>
    intro us i i' hc hi hii'
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.plain i :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    have := (vals_append_cons_inj val?_throwRef hi.val?_eq hc').2.1
    cases this
    exact (hi : False).elim
  | _ =>
    intro us i i' hc hi hii'
    have hnc := hi.not_isCallRef
    have hnr := hi.not_isReturnCallRef
    first
      | (((have := congrArg List.getLast? hc
           simp [constI32, Val.i32, Val.toAdmin] at this) <;> (try subst this) <;>
          first | exact (hi : False).elim | simp_all [IsStructInstr]) <;> done)
      | (rename_i hf; cases hf <;>
          (have := congrArg List.getLast? hc; simp [constI32, Val.i32, Val.toAdmin] at this) <;>
          (try subst this) <;>
          first | exact (hi : False).elim | simp_all [IsStructInstr] <;> done)

/-- A step at a structured head related by `InstrRel`: the same rule on the right. -/
theorem struct_lift {s t s' : Store H} {f f' : Frame} {ws us : List Val} {i i' : Instr}
    {is' L L' : List Admin} (hst : StoreRel F s t) (hii' : InstrRel BI i i')
    (hi : IsStructInstr i) (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s', f', is'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', vals ws ++ is' ++ L⟩
      ⟨t, f, vals (ws ++ us) ++ [.plain i'] ++ L'⟩
      (rank (vals (ws ++ us) ++ .plain i :: L)) := by
  obtain ⟨hs', r', hr, hstep⟩ := struct_match_aux (B := WithCuts B) h us i i' rfl hi hii'
  dsimp only at hs' hr hstep
  subst hs'
  refine ⟨⟨t, f', vals ws ++ r' ++ L'⟩, Or.inl (.single ?_), hst, rfl,
    ((AdminsRel.refl _).append hr).append hL⟩
  have := Step.append_right (Step.vals_left (hstep t) ws) L'
  rwa [show vals ws ++ (vals us ++ [.plain i']) ++ L' = vals (ws ++ us) ++ [.plain i'] ++ L' by
    simp] at this

/-- A redex step at a plain instruction related by `InstrRel`: the identity is
`transport_lift`; a structured instruction (`block`, `loop`, `if`, `try_table`) with
related bodies takes the same step on the right, the new `LABEL`/`HANDLER` bodies
related through `AdminsRel.src`. The head is not a `CALL_REF` (`hcall`): a call
head is `call_case`, and without `hcall` the statement is false
(`Closure.struct_case_without_hcall_false`, separate simulation-closure counterexamples (not included in this package)). -/
-- FLAG(statement-change): added `hcall`; the statement without it is refuted by
-- `struct_case_without_hcall_false` (a Wasm callee on the left, a host callee on the right).
theorem struct_case {s t s' : Store H} {f f' : Frame} {ws us : List Val} {i i' : Instr}
    {is' L L' : List Admin} (hst : StoreRel F s t) (hii' : InstrRel BI i i')
    (hcall : ¬ (Admin.plain i).IsCallRef) (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s', f', is'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', vals ws ++ is' ++ L⟩
      ⟨t, f, vals (ws ++ us) ++ [.plain i'] ++ L'⟩
      (rank (vals (ws ++ us) ++ .plain i :: L)) := by
  cases hii' with
  | refl => exact transport_lift hst (by simp [Admin.IsCtx]) hcall hL h _
  | block bt hb => exact struct_lift hst (.block bt hb) trivial hL h
  | loop bt hb => exact struct_lift hst (.loop bt hb) trivial hL h
  | if_ bt h₁ h₂ => exact struct_lift hst (.if_ bt h₁ h₂) trivial hL h
  | tryTable bt cs hb => exact struct_lift hst (.tryTable bt cs hb) trivial hL h

end Closure

end Silmaril.Wasm.Execution.Core.Sim
