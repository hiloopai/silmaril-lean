module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Resumption

/-! # Runtime typing of resumable SSA control

Atoms are typed by an arbitrary relation. Products, sums and unit retain their
runtime constructors over the canonical `Silmaril.Ty` algebra. The continuation
judgments check every captured environment and every CFG block. Preservation
requires only that an actual primitive transition preserves its declared type;
it neither assumes primitive totality nor restricts effects.
-/

@[expose] public section
universe u v w x
namespace Silmaril.Isotope.LambdaSSA.Resumption
open Semantics
variable {α : Type u} {Φ : Type v} {σ : Type w} {κ : Type x}

namespace Typing

/-- Structural runtime typing, parameterized only by atomic typing. -/
inductive ValueTyped (atomType : α → κ → Prop) : Value α → Ty κ → Prop where
  | atom {a A} : atomType a A → ValueTyped atomType (.atom a) (.base A)
  | unit : ValueTyped atomType .unit .unit
  | pair {a b A B} : ValueTyped atomType a A → ValueTyped atomType b B →
      ValueTyped atomType (.pair a b) (.product A B)
  | inl {a A B} : ValueTyped atomType a A → ValueTyped atomType (.inl a) (.coprod A B)
  | inr {b A B} : ValueTyped atomType b B → ValueTyped atomType (.inr b) (.coprod A B)

variable {atomType : α → κ → Prop}

def EnvTyped (atomType : α → κ → Prop) (Γ : VCtx (Ty κ)) (env : Env α) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → ValueTyped atomType (env i) A

theorem EnvTyped.extend {Γ : VCtx (Ty κ)} {env : Env α} {value : Value α} {A : Ty κ}
    (typed : EnvTyped atomType Γ env) (bound : ValueTyped atomType value A) :
    EnvTyped atomType (A :: Γ) (Semantics.extend env value) := by
  intro i B atIndex
  cases i with
  | zero =>
      have same : A = B := by simpa [At] using atIndex
      subst B
      exact bound
  | succ i => exact typed (by simpa [At] using atIndex)

/-- The type of a final expression value or external region transfer. -/
inductive Answer (κ : Type x) where
  | term (type : Ty κ)
  | region (labels : LCtx (Ty κ))

variable [HasTy Φ (Ty κ)]

inductive RegionContTyped (atomType : α → κ → Prop) :
    RegionCont α Φ → LCtx (Ty κ) → Answer κ → Prop where
  | halt {L} : RegionContTyped atomType .halt L (.region L)
  | cfg {Γ env n blocks next L answer} (R : Fin n → Ty κ) :
      EnvTyped atomType Γ env →
      (∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) →
      RegionContTyped atomType next L answer →
      RegionContTyped atomType (.cfg env n blocks next) (List.ofFn R ++ L) answer

inductive TermContTyped (atomType : α → κ → Prop) :
    TermCont α Φ → Ty κ → Answer κ → Prop where
  | halt {A} : TermContTyped atomType .halt A (.term A)
  | op {f next answer} : TermContTyped atomType next (instrTrg f) answer →
      TermContTyped atomType (.op f next) (instrSrc f) answer
  | let₁ {Γ env body next A B answer} : EnvTyped atomType Γ env →
      Tm.HasType (A :: Γ) body B → TermContTyped atomType next B answer →
      TermContTyped atomType (.let₁ env body next) A answer
  | pairLeft {Γ env right next A B answer} : EnvTyped atomType Γ env →
      Tm.HasType Γ right B → TermContTyped atomType next (.product A B) answer →
      TermContTyped atomType (.pairLeft env right next) A answer
  | pairRight {left next A B answer} : ValueTyped atomType left A →
      TermContTyped atomType next (.product A B) answer →
      TermContTyped atomType (.pairRight left next) B answer
  | let₂ {Γ env body next A B C answer} : EnvTyped atomType Γ env →
      Tm.HasType (B :: A :: Γ) body C → TermContTyped atomType next C answer →
      TermContTyped atomType (.let₂ env body next) (.product A B) answer
  | inl {next A B answer} : TermContTyped atomType next (.coprod A B) answer →
      TermContTyped atomType (.inl next) A answer
  | inr {next A B answer} : TermContTyped atomType next (.coprod A B) answer →
      TermContTyped atomType (.inr next) B answer
  | case {Γ env left right next A B C answer} : EnvTyped atomType Γ env →
      Tm.HasType (A :: Γ) left C → Tm.HasType (B :: Γ) right C → TermContTyped atomType next C answer →
      TermContTyped atomType (.case env left right next) (.coprod A B) answer
  | abort {answer} : TermContTyped atomType .abort .empty answer
  | br {label next L A answer} : At L label A → RegionContTyped atomType next L answer →
      TermContTyped atomType (.br label next) A answer
  | regionLet₁ {Γ env body next A L answer} : EnvTyped atomType Γ env →
      Region.HasType (A :: Γ) body L → RegionContTyped atomType next L answer →
      TermContTyped atomType (.regionLet₁ env body next) A answer
  | regionLet₂ {Γ env body next A B L answer} : EnvTyped atomType Γ env →
      Region.HasType (B :: A :: Γ) body L → RegionContTyped atomType next L answer →
      TermContTyped atomType (.regionLet₂ env body next) (.product A B) answer
  | regionCase {Γ env left right next A B L answer} : EnvTyped atomType Γ env →
      Region.HasType (A :: Γ) left L → Region.HasType (B :: Γ) right L → RegionContTyped atomType next L answer →
      TermContTyped atomType (.regionCase env left right next) (.coprod A B) answer

inductive ControlTyped (atomType : α → κ → Prop) : Control α Φ → Answer κ → Prop where
  | term {Γ env expression next A answer} : EnvTyped atomType Γ env →
      Tm.HasType Γ expression A → TermContTyped atomType next A answer →
      ControlTyped atomType (.term env expression next) answer
  | value {value next A answer} : ValueTyped atomType value A → TermContTyped atomType next A answer →
      ControlTyped atomType (.value value next) answer
  | region {Γ env body next L answer} : EnvTyped atomType Γ env →
      Region.HasType Γ body L → RegionContTyped atomType next L answer →
      ControlTyped atomType (.region env body next) answer
  | branch {label value next L A answer} : At L label A → ValueTyped atomType value A →
      RegionContTyped atomType next L answer → ControlTyped atomType (.branch label value next) answer
  | request {f argument next answer} : ValueTyped atomType argument (instrSrc f) →
      TermContTyped atomType next (instrTrg f) answer → ControlTyped atomType (.request f argument next) answer

theorem startTerm_typed {Γ : VCtx (Ty κ)} {env : Env α} {term : Tm Φ} {A : Ty κ}
    (environment : EnvTyped atomType Γ env) (termType : Tm.HasType Γ term A) :
    ControlTyped atomType (startTerm env term) (.term A) := .term environment termType .halt

theorem startRegion_typed {Γ : VCtx (Ty κ)} {env : Env α} {region : Region Φ} {L : LCtx (Ty κ)}
    (environment : EnvTyped atomType Γ env) (regionType : Region.HasType Γ region L) :
    ControlTyped atomType (startRegion env region) (.region L) := .region environment regionType .halt

theorem Admin.typed {before after : Control α Φ} {answer : Answer κ}
    (step : Resumption.Admin before after) (typed : ControlTyped atomType before answer) :
    ControlTyped atomType after answer := by
  cases step with
  | var =>
      cases typed with
      | term environment expression next =>
          cases expression with
          | var atIndex => exact .value (environment atIndex) next
  | op =>
      cases typed with
      | term environment expression next =>
          cases expression with
          | op arg => exact .term environment arg (.op next)
  | let₁ =>
      cases typed with
      | term environment expression next =>
          cases expression with
          | let₁ arg body => exact .term environment arg (.let₁ environment body next)
  | pair =>
      cases typed with
      | term environment expression next =>
          cases expression with
          | pair left right => exact .term environment left (.pairLeft environment right next)
  | unit =>
      cases typed with
      | term _ expression next => cases expression; exact .value .unit next
  | let₂ =>
      cases typed with
      | term environment expression next =>
          cases expression with
          | let₂ arg body => exact .term environment arg (.let₂ environment body next)
  | inl =>
      cases typed with
      | term environment expression next => cases expression with
          | inl arg => exact .term environment arg (.inl next)
  | inr =>
      cases typed with
      | term environment expression next => cases expression with
          | inr arg => exact .term environment arg (.inr next)
  | case =>
      cases typed with
      | term environment expression next => cases expression with
          | case arg left right => exact .term environment arg (.case environment left right next)
  | abort =>
      cases typed with
      | term environment expression _ => cases expression with
          | abort arg => exact .term environment arg .abort
  | request =>
      cases typed with
      | value value next => cases next with
          | op next => exact .request value next
  | bind₁ =>
      cases typed with
      | value value next => cases next with
          | let₁ environment body tail => exact .term (environment.extend value) body tail
  | pairLeft =>
      cases typed with
      | value value next => cases next with
          | pairLeft environment right tail => exact .term environment right (.pairRight value tail)
  | pairRight =>
      cases typed with
      | value value next => cases next with
          | pairRight left tail => exact .value (.pair left value) tail
  | bind₂ =>
      cases typed with
      | value value next => cases next with
          | let₂ environment body tail => cases value with
              | pair left right => exact .term ((environment.extend left).extend right) body tail
  | injectLeft =>
      cases typed with
      | value value next => cases next with
          | inl tail => exact .value (.inl value) tail
  | injectRight =>
      cases typed with
      | value value next => cases next with
          | inr tail => exact .value (.inr value) tail
  | caseLeft =>
      cases typed with
      | value value next => cases next with
          | case environment left _ tail => cases value with
              | inl value => exact .term (environment.extend value) left tail
  | caseRight =>
      cases typed with
      | value value next => cases next with
          | case environment _ right tail => cases value with
              | inr value => exact .term (environment.extend value) right tail
  | regionBr =>
      cases typed with
      | region environment expression next => cases expression with
          | br label arg => exact .term environment arg (.br label next)
  | regionLet₁ =>
      cases typed with
      | region environment expression next => cases expression with
          | let₁ arg body => exact .term environment arg (.regionLet₁ environment body next)
  | regionLet₂ =>
      cases typed with
      | region environment expression next => cases expression with
          | let₂ arg body => exact .term environment arg (.regionLet₂ environment body next)
  | regionCase =>
      cases typed with
      | region environment expression next => cases expression with
          | case arg left right => exact .term environment arg (.regionCase environment left right next)
  | cfg =>
      cases typed with
      | region environment expression next => cases expression with
          | cfg R entry blocks => exact .region environment entry (.cfg R environment blocks next)
  | branch =>
      cases typed with
      | value value next => cases next with
          | br label tail => exact .branch label value tail
  | regionBind₁ =>
      cases typed with
      | value value next => cases next with
          | regionLet₁ environment body tail => exact .region (environment.extend value) body tail
  | regionBind₂ =>
      cases typed with
      | value value next => cases next with
          | regionLet₂ environment body tail => cases value with
              | pair left right => exact .region ((environment.extend left).extend right) body tail
  | regionLeft =>
      cases typed with
      | value value next => cases next with
          | regionCase environment left _ tail => cases value with
              | inl value => exact .region (environment.extend value) left tail
  | regionRight =>
      cases typed with
      | value value next => cases next with
          | regionCase environment _ right tail => cases value with
              | inr value => exact .region (environment.extend value) right tail
  | @follow env n blocks h label value inside =>
      cases typed with
      | branch atLabel valueType next => cases next with
          | cfg R environment blocks tail =>
              have typedValue : ValueTyped atomType value (R ⟨label, inside⟩) := by
                have same := atLabel
                simp [At, List.getElem?_append, inside] at same
                exact same.symm ▸ valueType
              exact .region (environment.extend typedValue)
                (blocks ⟨label, inside⟩) (.cfg R environment blocks tail)
  | exit outside =>
      cases typed with
      | branch atLabel valueType next => cases next with
          | cfg R _ _ tail =>
              exact .branch (by simpa [At, List.getElem?_append, Nat.not_lt.mpr outside] using atLabel) valueType tail

/-- No instruction is assumed to succeed; this checks the outputs of the
primitive transitions that actually occur. -/
def InstrTyped (atomType : α → κ → Prop)
    (instr : Φ → Value α → σ → Value α → σ → Prop) : Prop :=
  ∀ ⦃f input before output after⦄, ValueTyped atomType input (instrSrc f) →
    instr f input before output after → ValueTyped atomType output (instrTrg f)

theorem Step.typed {instr : Φ → Value α → σ → Value α → σ → Prop}
    (primitiveTyped : InstrTyped atomType instr) {before after : Control α Φ} {s t : σ} {answer : Answer κ}
    (step : Resumption.Step instr before s after t) (typed : ControlTyped atomType before answer) :
    ControlTyped atomType after answer := by
  cases step with
  | admin step => exact Admin.typed step typed
  | instruction primitive =>
      cases typed with
      | request argument next => exact .value (primitiveTyped argument primitive) next

theorem Run.typed {instr : Φ → Value α → σ → Value α → σ → Prop}
    (primitiveTyped : InstrTyped atomType instr) {before after : Control α Φ} {s t : σ} {answer : Answer κ}
    (run : Resumption.Run instr before s after t) (typed : ControlTyped atomType before answer) :
    ControlTyped atomType after answer := by
  induction run with
  | refl => exact typed
  | head step _ ih => exact ih (Step.typed primitiveTyped step typed)

theorem doneTerm_typed {value : Value α} {A : Ty κ}
    (typed : ControlTyped (Φ := Φ) atomType (doneTerm value) (.term A)) : ValueTyped atomType value A := by
  cases typed with
  | value value next => cases next; exact value

theorem doneRegion_typed {label : Nat} {value : Value α} {L : LCtx (Ty κ)}
    (typed : ControlTyped (Φ := Φ) atomType (doneRegion label value) (.region L)) :
    ∃ A, At L label A ∧ ValueTyped atomType value A := by
  cases typed with
  | branch atLabel value next => cases next; exact ⟨_, atLabel, value⟩

end Typing
end Silmaril.Isotope.LambdaSSA.Resumption
