module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Resumption

/-! # Finite adequacy of the instruction-resumable machine

The machine rules remain independent of big-step evaluation. This module proves
that finite completed single-thread runs coincide with the existing semantics.
The continuation interpretation is used only in the proof, never as a premise
of a machine transition. The equivalence does not assume deterministic or total
primitive instructions.
-/

@[expose] public section
universe u v w
namespace Silmaril.Isotope.LambdaSSA.Resumption
open Semantics
variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem term_eval_run {env : Env α} {term : Tm Φ} {s t : σ} {value : Value α}
    (eval : Semantics.Tm.Eval instr env term s value t) (k : TermCont α Φ) :
    Run instr (.term env term k) s (.value value k) t := by
  induction eval generalizing k with
  | var => exact .single (.admin .var)
  | unit => exact .single (.admin .unit)
  | op _ primitive ih =>
      exact .head (.admin .op) ((ih _).trans (.head (.admin .request) (.single (.instruction primitive))))
  | let₁ _ _ left right =>
      exact .head (.admin .let₁) ((left _).trans (.head (.admin .bind₁) (right k)))
  | pair _ _ left right =>
      exact .head (.admin .pair) ((left _).trans (.head (.admin .pairLeft)
        ((right _).trans (.single (.admin .pairRight)))))
  | let₂ _ _ left right =>
      exact .head (.admin .let₂) ((left _).trans (.head (.admin .bind₂) (right k)))
  | inl _ ih => exact .head (.admin .inl) ((ih _).trans (.single (.admin .injectLeft)))
  | inr _ ih => exact .head (.admin .inr) ((ih _).trans (.single (.admin .injectRight)))
  | case_inl _ _ left right =>
      exact .head (.admin .case) ((left _).trans (.head (.admin .caseLeft) (right k)))
  | case_inr _ _ left right =>
      exact .head (.admin .case) ((left _).trans (.head (.admin .caseRight) (right k)))

theorem region_eval_run {env : Env α} {region : Region Φ} {s t : σ} {label : Nat} {value : Value α}
    (eval : Semantics.Region.Eval instr env region s label value t) (h : RegionCont α Φ) :
    Run instr (.region env region h) s (.branch label value h) t := by
  induction eval using Semantics.Region.Eval.rec
      (motive_2 := fun env n blocks first initial s label value t _ =>
        ∀ h : RegionCont α Φ, Run instr (.branch first initial (.cfg env n blocks h)) s
          (.branch label value h) t) generalizing h with
  | br arg => exact .head (.admin .regionBr) ((term_eval_run arg _).trans (.single (.admin .branch)))
  | let₁ arg _ ih =>
      exact .head (.admin .regionLet₁) ((term_eval_run arg _).trans (.head (.admin .regionBind₁) (ih h)))
  | let₂ arg _ ih =>
      exact .head (.admin .regionLet₂) ((term_eval_run arg _).trans (.head (.admin .regionBind₂) (ih h)))
  | case_inl arg _ ih =>
      exact .head (.admin .regionCase) ((term_eval_run arg _).trans (.head (.admin .regionLeft) (ih h)))
  | case_inr arg _ ih =>
      exact .head (.admin .regionCase) ((term_eval_run arg _).trans (.head (.admin .regionRight) (ih h)))
  | cfg _ _ entry follow => exact .head (.admin .cfg) ((entry _).trans (follow h))
  | exit outside => exact .single (.admin (.exit outside))
  | step inside _ _ body follow =>
      rename_i h
      exact .head (.admin (.follow inside)) ((body _).trans (follow h))

/-- The two distinct kinds of completed control. -/
inductive Result (α : Type u) where
  | term (value : Value α)
  | region (label : Nat) (value : Value α)

def Result.control (result : Result α) : Control α Φ :=
  match result with
  | .term value => doneTerm value
  | .region label value => doneRegion label value

/-- Proof-only interpretation of the surrounding CFG scopes. -/
inductive RegionCont.Eval (instr : Φ → Value α → σ → Value α → σ → Prop) :
    RegionCont α Φ → Nat → Value α → σ → Result α → σ → Prop where
  | halt {label value state} : Eval instr .halt label value state (.region label value) state
  | cfg {env n blocks next label value state out result middle final done} :
      Semantics.Region.Follow instr env blocks label value state out result middle →
      Eval instr next out result middle done final →
      Eval instr (.cfg env n blocks next) label value state done final

/-- Proof-only interpretation of pending expression/region frames. -/
inductive TermCont.Eval (instr : Φ → Value α → σ → Value α → σ → Prop) :
    TermCont α Φ → Value α → σ → Result α → σ → Prop where
  | halt {value state} : Eval instr .halt value state (.term value) state
  | op {f next argument value state middle done final} :
      instr f argument state value middle → Eval instr next value middle done final →
      Eval instr (.op f next) argument state done final
  | let₁ {env body next argument value state middle done final} :
      Semantics.Tm.Eval instr (extend env argument) body state value middle →
      Eval instr next value middle done final → Eval instr (.let₁ env body next) argument state done final
  | pairLeft {env right next left value state middle done final} :
      Semantics.Tm.Eval instr env right state value middle →
      Eval instr next (.pair left value) middle done final →
      Eval instr (.pairLeft env right next) left state done final
  | pairRight {next left right state done final} :
      Eval instr next (.pair left right) state done final → Eval instr (.pairRight left next) right state done final
  | let₂ {env body next a b value state middle done final} :
      Semantics.Tm.Eval instr (extend (extend env a) b) body state value middle →
      Eval instr next value middle done final → Eval instr (.let₂ env body next) (.pair a b) state done final
  | inl {next value state done final} :
      Eval instr next (.inl value) state done final → Eval instr (.inl next) value state done final
  | inr {next value state done final} :
      Eval instr next (.inr value) state done final → Eval instr (.inr next) value state done final
  | caseLeft {env left right next argument value state middle done final} :
      Semantics.Tm.Eval instr (extend env argument) left state value middle →
      Eval instr next value middle done final → Eval instr (.case env left right next) (.inl argument) state done final
  | caseRight {env left right next argument value state middle done final} :
      Semantics.Tm.Eval instr (extend env argument) right state value middle →
      Eval instr next value middle done final → Eval instr (.case env left right next) (.inr argument) state done final
  | br {label next value state done final} :
      RegionCont.Eval instr next label value state done final → Eval instr (.br label next) value state done final
  | regionLet₁ {env body next argument label value state middle done final} :
      Semantics.Region.Eval instr (extend env argument) body state label value middle →
      RegionCont.Eval instr next label value middle done final →
      Eval instr (.regionLet₁ env body next) argument state done final
  | regionLet₂ {env body next a b label value state middle done final} :
      Semantics.Region.Eval instr (extend (extend env a) b) body state label value middle →
      RegionCont.Eval instr next label value middle done final →
      Eval instr (.regionLet₂ env body next) (.pair a b) state done final
  | regionLeft {env left right next argument label value state middle done final} :
      Semantics.Region.Eval instr (extend env argument) left state label value middle →
      RegionCont.Eval instr next label value middle done final →
      Eval instr (.regionCase env left right next) (.inl argument) state done final
  | regionRight {env left right next argument label value state middle done final} :
      Semantics.Region.Eval instr (extend env argument) right state label value middle →
      RegionCont.Eval instr next label value middle done final →
      Eval instr (.regionCase env left right next) (.inr argument) state done final

/-- Interpretation used to prove soundness backwards across a machine run. -/
def Control.Evaluates (instr : Φ → Value α → σ → Value α → σ → Prop)
    (control : Control α Φ) (state : σ) (done : Result α) (final : σ) : Prop :=
  match control with
  | .term env expression next => ∃ value middle, Semantics.Tm.Eval instr env expression state value middle ∧
      TermCont.Eval instr next value middle done final
  | .value v next => TermCont.Eval instr next v state done final
  | .region env body next => ∃ label value middle,
      Semantics.Region.Eval instr env body state label value middle ∧
      RegionCont.Eval instr next label value middle done final
  | .branch label v next => RegionCont.Eval instr next label v state done final
  | .request instruction argument next => ∃ value middle, instr instruction argument state value middle ∧
      TermCont.Eval instr next value middle done final

theorem Admin.evaluates_backward {before after : Control α Φ} (step : Admin before after)
    {state final : σ} {done : Result α} (eval : after.Evaluates instr state done final) :
    before.Evaluates instr state done final := by
  cases step with
  | var => exact ⟨_, _, .var, eval⟩
  | unit => exact ⟨_, _, .unit, eval⟩
  | op =>
      obtain ⟨arg, middle, argEval, rest⟩ := eval
      cases rest with
      | op primitive tail => exact ⟨_, _, .op argEval primitive, tail⟩
  | let₁ =>
      obtain ⟨arg, middle, argEval, rest⟩ := eval
      cases rest with
      | let₁ body tail => exact ⟨_, _, .let₁ argEval body, tail⟩
  | pair =>
      obtain ⟨arg, middle, argEval, rest⟩ := eval
      cases rest with
      | pairLeft right tail => exact ⟨_, _, .pair argEval right, tail⟩
  | let₂ =>
      obtain ⟨arg, middle, argEval, rest⟩ := eval
      cases rest with
      | let₂ body tail => exact ⟨_, _, .let₂ argEval body, tail⟩
  | inl =>
      obtain ⟨arg, middle, argEval, rest⟩ := eval
      cases rest with
      | inl tail => exact ⟨_, _, .inl argEval, tail⟩
  | inr =>
      obtain ⟨arg, middle, argEval, rest⟩ := eval
      cases rest with
      | inr tail => exact ⟨_, _, .inr argEval, tail⟩
  | case =>
      obtain ⟨arg, middle, argEval, rest⟩ := eval
      cases rest with
      | caseLeft body tail => exact ⟨_, _, .case_inl argEval body, tail⟩
      | caseRight body tail => exact ⟨_, _, .case_inr argEval body, tail⟩
  | abort =>
      obtain ⟨_, _, _, rest⟩ := eval
      cases rest
  | request =>
      obtain ⟨_, _, primitive, tail⟩ := eval
      exact .op primitive tail
  | bind₁ =>
      obtain ⟨_, _, body, tail⟩ := eval
      exact .let₁ body tail
  | pairLeft =>
      obtain ⟨_, _, right, rest⟩ := eval
      cases rest with
      | pairRight tail => exact .pairLeft right tail
  | pairRight => exact .pairRight eval
  | bind₂ =>
      obtain ⟨_, _, body, tail⟩ := eval
      exact .let₂ body tail
  | injectLeft => exact .inl eval
  | injectRight => exact .inr eval
  | caseLeft =>
      obtain ⟨_, _, body, tail⟩ := eval
      exact .caseLeft body tail
  | caseRight =>
      obtain ⟨_, _, body, tail⟩ := eval
      exact .caseRight body tail
  | regionBr =>
      obtain ⟨_, _, arg, rest⟩ := eval
      cases rest with
      | br tail => exact ⟨_, _, _, .br arg, tail⟩
  | regionLet₁ =>
      obtain ⟨_, _, arg, rest⟩ := eval
      cases rest with
      | regionLet₁ body tail => exact ⟨_, _, _, .let₁ arg body, tail⟩
  | regionLet₂ =>
      obtain ⟨_, _, arg, rest⟩ := eval
      cases rest with
      | regionLet₂ body tail => exact ⟨_, _, _, .let₂ arg body, tail⟩
  | regionCase =>
      obtain ⟨_, _, arg, rest⟩ := eval
      cases rest with
      | regionLeft body tail => exact ⟨_, _, _, .case_inl arg body, tail⟩
      | regionRight body tail => exact ⟨_, _, _, .case_inr arg body, tail⟩
  | cfg =>
      obtain ⟨_, _, _, entry, rest⟩ := eval
      cases rest with
      | cfg follow tail => exact ⟨_, _, _, .cfg entry follow, tail⟩
  | branch => exact .br eval
  | regionBind₁ =>
      obtain ⟨_, _, _, body, tail⟩ := eval
      exact .regionLet₁ body tail
  | regionBind₂ =>
      obtain ⟨_, _, _, body, tail⟩ := eval
      exact .regionLet₂ body tail
  | regionLeft =>
      obtain ⟨_, _, _, body, tail⟩ := eval
      exact .regionLeft body tail
  | regionRight =>
      obtain ⟨_, _, _, body, tail⟩ := eval
      exact .regionRight body tail
  | follow inside =>
      obtain ⟨_, _, _, body, rest⟩ := eval
      cases rest with
      | cfg follow tail => exact .cfg (.step inside body follow) tail
  | exit outside => exact .cfg (.exit outside) eval

theorem Step.evaluates_backward {before after : Control α Φ} {state middle final : σ} {done : Result α}
    (step : Step instr before state after middle) (eval : after.Evaluates instr middle done final) :
    before.Evaluates instr state done final := by
  cases step with
  | admin step => exact step.evaluates_backward eval
  | instruction primitive => exact ⟨_, _, primitive, eval⟩

theorem Run.evaluates_backward {before after : Control α Φ} {state middle final : σ} {done : Result α}
    (run : Run instr before state after middle) (eval : after.Evaluates instr middle done final) :
    before.Evaluates instr state done final := by
  induction run with
  | refl => exact eval
  | head step _ ih => exact step.evaluates_backward (ih eval)

theorem Result.evaluates (done : Result α) (state : σ) :
    (done.control (Φ := Φ)).Evaluates instr state done state := by
  cases done with
  | term value => exact .halt
  | region label value => exact .halt

/-- Exact finite expression adequacy, without determinism or totality premises. -/
theorem term_adequacy {env : Env α} {term : Tm Φ} {s t : σ} {value : Value α} :
    Run instr (startTerm env term) s (doneTerm value) t ↔ Semantics.Tm.Eval instr env term s value t := by
  constructor
  · intro run
    obtain ⟨_, _, eval, rest⟩ := run.evaluates_backward ((Result.term value).evaluates (instr := instr) t)
    cases rest
    exact eval
  · intro eval
    exact term_eval_run eval .halt

/-- Exact finite region adequacy, including nested CFG label handling. -/
theorem region_adequacy {env : Env α} {region : Region Φ} {s t : σ} {label : Nat} {value : Value α} :
    Run instr (startRegion env region) s (doneRegion label value) t ↔
      Semantics.Region.Eval instr env region s label value t := by
  constructor
  · intro run
    obtain ⟨_, _, _, eval, rest⟩ := run.evaluates_backward ((Result.region label value).evaluates (instr := instr) t)
    cases rest
    exact eval
  · intro eval
    exact region_eval_run eval .halt

end Silmaril.Isotope.LambdaSSA.Resumption
