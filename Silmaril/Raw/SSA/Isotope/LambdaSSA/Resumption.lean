module

public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Instruction-resumable lambda-SSA

The control stack records left-to-right expression evaluation and captured CFG
environments. Administrative steps never access machine state. An instruction
request resumes with exactly one supplied primitive transition; no rule invokes
whole-expression or whole-region evaluation. A scheduler may therefore suspend
one control at a request and run another control against shared state.

`Run` describes a finite single-thread execution. It imposes no termination,
instruction-totality, scheduling or progress assumption. Malformed raw values
and `abort` can get stuck, as in the existing operational semantics.
-/

@[expose] public section
universe u v w
namespace Silmaril.Isotope.LambdaSSA.Resumption
open Semantics

/-- Captured CFG scopes, innermost first. -/
inductive RegionCont (α : Type u) (Φ : Type v) where
  | halt
  | cfg (env : Env α) (n : Nat) (blocks : Fin n → Region Φ) (next : RegionCont α Φ)

/-- Expression continuations, including the boundary back into a region. -/
inductive TermCont (α : Type u) (Φ : Type v) where
  | halt
  | op (instruction : Φ) (next : TermCont α Φ)
  | let₁ (env : Env α) (body : Tm Φ) (next : TermCont α Φ)
  | pairLeft (env : Env α) (right : Tm Φ) (next : TermCont α Φ)
  | pairRight (left : Value α) (next : TermCont α Φ)
  | let₂ (env : Env α) (body : Tm Φ) (next : TermCont α Φ)
  | inl (next : TermCont α Φ)
  | inr (next : TermCont α Φ)
  | case (env : Env α) (left right : Tm Φ) (next : TermCont α Φ)
  | abort
  | br (label : Nat) (next : RegionCont α Φ)
  | regionLet₁ (env : Env α) (body : Region Φ) (next : RegionCont α Φ)
  | regionLet₂ (env : Env α) (body : Region Φ) (next : RegionCont α Φ)
  | regionCase (env : Env α) (left right : Region Φ) (next : RegionCont α Φ)

/-- Control is independent of the external machine state. In particular,
instruction requests retain their input and exact continuation. -/
inductive Control (α : Type u) (Φ : Type v) where
  | term (env : Env α) (term : Tm Φ) (next : TermCont α Φ)
  | value (value : Value α) (next : TermCont α Φ)
  | region (env : Env α) (region : Region Φ) (next : RegionCont α Φ)
  | branch (label : Nat) (value : Value α) (next : RegionCont α Φ)
  | request (instruction : Φ) (argument : Value α) (next : TermCont α Φ)

variable {α : Type u} {Φ : Type v} {σ : Type w}

def startTerm (env : Env α) (term : Tm Φ) : Control α Φ := .term env term .halt
def doneTerm (value : Value α) : Control α Φ := .value value .halt
def startRegion (env : Env α) (region : Region Φ) : Control α Φ := .region env region .halt
def doneRegion (label : Nat) (value : Value α) : Control α Φ := .branch label value .halt

/-- Only syntax, environments and continuations change in an administrative
step. The `abort` frame deliberately has no returning transition. -/
inductive Admin : Control α Φ → Control α Φ → Prop where
  | var {env i k} : Admin (.term env (.var i) k) (.value (env i) k)
  | op {env f a k} : Admin (.term env (.op f a) k) (.term env a (.op f k))
  | let₁ {env a b k} : Admin (.term env (.let₁ a b) k) (.term env a (.let₁ env b k))
  | pair {env a b k} : Admin (.term env (.pair a b) k) (.term env a (.pairLeft env b k))
  | unit {env k} : Admin (.term env .unit k) (.value .unit k)
  | let₂ {env a b k} : Admin (.term env (.let₂ a b) k) (.term env a (.let₂ env b k))
  | inl {env a k} : Admin (.term env (.inl a) k) (.term env a (.inl k))
  | inr {env a k} : Admin (.term env (.inr a) k) (.term env a (.inr k))
  | case {env a l r k} : Admin (.term env (.case a l r) k) (.term env a (.case env l r k))
  | abort {env a k} : Admin (.term env (.abort a) k) (.term env a .abort)
  | request {f value k} : Admin (.value value (.op f k)) (.request f value k)
  | bind₁ {env b value k} : Admin (.value value (.let₁ env b k)) (.term (extend env value) b k)
  | pairLeft {env b value k} : Admin (.value value (.pairLeft env b k)) (.term env b (.pairRight value k))
  | pairRight {a b k} : Admin (.value b (.pairRight a k)) (.value (.pair a b) k)
  | bind₂ {env body a b k} : Admin (.value (.pair a b) (.let₂ env body k))
      (.term (extend (extend env a) b) body k)
  | injectLeft {value k} : Admin (.value value (.inl k)) (.value (.inl value) k)
  | injectRight {value k} : Admin (.value value (.inr k)) (.value (.inr value) k)
  | caseLeft {env l r value k} : Admin (.value (.inl value) (.case env l r k)) (.term (extend env value) l k)
  | caseRight {env l r value k} : Admin (.value (.inr value) (.case env l r k)) (.term (extend env value) r k)
  | regionBr {env label arg h} : Admin (.region env (.br label arg) h) (.term env arg (.br label h))
  | regionLet₁ {env a body h} : Admin (.region env (.let₁ a body) h) (.term env a (.regionLet₁ env body h))
  | regionLet₂ {env a body h} : Admin (.region env (.let₂ a body) h) (.term env a (.regionLet₂ env body h))
  | regionCase {env a l r h} : Admin (.region env (.case a l r) h) (.term env a (.regionCase env l r h))
  | cfg {env entry n blocks h} : Admin (.region env (.cfg entry n blocks) h) (.region env entry (.cfg env n blocks h))
  | branch {label value h} : Admin (.value value (.br label h)) (.branch label value h)
  | regionBind₁ {env body value h} : Admin (.value value (.regionLet₁ env body h)) (.region (extend env value) body h)
  | regionBind₂ {env body a b h} : Admin (.value (.pair a b) (.regionLet₂ env body h))
      (.region (extend (extend env a) b) body h)
  | regionLeft {env l r value h} : Admin (.value (.inl value) (.regionCase env l r h)) (.region (extend env value) l h)
  | regionRight {env l r value h} : Admin (.value (.inr value) (.regionCase env l r h)) (.region (extend env value) r h)
  | follow {env n blocks h label value} (inside : label < n) :
      Admin (.branch label value (.cfg env n blocks h))
        (.region (extend env value) (blocks ⟨label, inside⟩) (.cfg env n blocks h))
  | exit {env n blocks h label value} (outside : n ≤ label) :
      Admin (.branch label value (.cfg env n blocks h)) (.branch (label - n) value h)

/-- One administrative step, or exactly one primitive effect. -/
inductive Step (instr : Φ → Value α → σ → Value α → σ → Prop) :
    Control α Φ → σ → Control α Φ → σ → Prop where
  | admin {before after : Control α Φ} {state : σ} :
      Admin before after → Step instr before state after state
  | instruction {f argument result k before after} :
      instr f argument before result after →
      Step instr (.request f argument k) before (.value result k) after

/-- Finite execution with all intermediate instruction effects retained. -/
inductive Run (instr : Φ → Value α → σ → Value α → σ → Prop) :
    Control α Φ → σ → Control α Φ → σ → Prop where
  | refl {control state} : Run instr control state control state
  | head {a b c s t z} : Step instr a s b t → Run instr b t c z → Run instr a s c z

variable {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem Run.single {a b : Control α Φ} {s t : σ} (step : Step instr a s b t) : Run instr a s b t :=
  .head step .refl

theorem Run.trans {a b c : Control α Φ} {s t z : σ}
    (first : Run instr a s b t) (second : Run instr b t c z) : Run instr a s c z := by
  induction first with
  | refl => exact second
  | head step _ ih => exact .head step (ih second)

theorem Admin.deterministic {a b c : Control α Φ} (first : Admin a b) (second : Admin a c) : b = c := by
  cases first <;> cases second <;> first | rfl | omega

theorem Step.deterministic (det : InstrDeterministic instr)
    {a b c : Control α Φ} {s t z : σ} (first : Step instr a s b t) (second : Step instr a s c z) :
    b = c ∧ t = z := by
  cases first with
  | admin first =>
      cases second with
      | admin second => exact ⟨first.deterministic second, rfl⟩
      | instruction _ => cases first
  | instruction first =>
      cases second with
      | admin second => cases second
      | instruction second =>
          obtain ⟨rfl, rfl⟩ := det _ _ _ _ _ _ _ first second
          exact ⟨rfl, rfl⟩

theorem Step.from_request {f argument k after s t}
    (step : Step instr (.request f argument k) s after t) :
    ∃ result, after = .value result k ∧ instr f argument s result t := by
  cases step with
  | admin impossible => cases impossible
  | instruction primitive => exact ⟨_, rfl, primitive⟩

theorem Step.not_doneTerm {value after s t} : ¬ Step instr (doneTerm value) s after t := by
  intro step
  cases step with
  | admin impossible => cases impossible

theorem Step.not_doneRegion {label value after s t} : ¬ Step instr (doneRegion label value) s after t := by
  intro step
  cases step with
  | admin impossible => cases impossible

end Silmaril.Isotope.LambdaSSA.Resumption
