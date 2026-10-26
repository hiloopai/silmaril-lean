module

public import Silmaril.Courses.Cambridge.L2.Reduction

/-! # Cambridge L2 typing, §§4.3 and 4.6

The environment pairs the L1 location assumptions with variable assumptions.
Free variables use a finite map, while bound variables use a list matching the
de Bruijn syntax. Pushing onto the list represents the notes' `Γ,x:T` without
depending on the spelling of `x`. The rules are collected on pp. 66–67.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

structure TypeEnv where
  locs : L1.TypeEnv
  free : Finmap (fun _ : Var => Ty)
  bound : List Ty

def TypeEnv.empty : TypeEnv := ⟨∅, ∅, []⟩

def TypeEnv.push (Γ : TypeEnv) (type : Ty) : TypeEnv :=
  { Γ with bound := type :: Γ.bound }

inductive HasType : TypeEnv → Expr → Ty → Prop where
  | int {Γ : TypeEnv} (n : Int) : HasType Γ (.int n) .int
  | bool {Γ : TypeEnv} (b : Bool) : HasType Γ (.bool b) .bool
  | add {Γ : TypeEnv} {left right : Expr}
      (hl : HasType Γ left .int) (hr : HasType Γ right .int) :
      HasType Γ (.binary left .add right) .int
  | ge {Γ : TypeEnv} {left right : Expr}
      (hl : HasType Γ left .int) (hr : HasType Γ right .int) :
      HasType Γ (.binary left .ge right) .bool
  | cond {Γ : TypeEnv} {test yes no : Expr} {T : Ty}
      (hc : HasType Γ test .bool) (hy : HasType Γ yes T) (hn : HasType Γ no T) :
      HasType Γ (.cond test yes no) T
  | assign {Γ : TypeEnv} {loc : Loc} {e : Expr}
      (present : loc ∈ Γ.locs) (he : HasType Γ e .int) :
      HasType Γ (.assign loc e) .unit
  | deref {Γ : TypeEnv} {loc : Loc}
      (present : loc ∈ Γ.locs) : HasType Γ (.deref loc) .int
  | skip {Γ : TypeEnv} : HasType Γ .skip .unit
  | seq {Γ : TypeEnv} {left right : Expr} {T : Ty}
      (hl : HasType Γ left .unit) (hr : HasType Γ right T) :
      HasType Γ (.seq left right) T
  | loop {Γ : TypeEnv} {test body : Expr}
      (ht : HasType Γ test .bool) (hb : HasType Γ body .unit) :
      HasType Γ (.loop test body) .unit
  | bvar {Γ : TypeEnv} {index : Nat} {T : Ty}
      (lookup : Γ.bound[index]? = some T) :
      HasType Γ (.bvar index) T
  | fvar {Γ : TypeEnv} {name : Var} {T : Ty}
      (lookup : Finmap.lookup name Γ.free = some T) :
      HasType Γ (.fvar name) T
  | lam {Γ : TypeEnv} {domain codomain : Ty} {body : Expr}
      (typing : HasType (Γ.push domain) body codomain) :
      HasType Γ (.lam domain body) (.arr domain codomain)
  | app {Γ : TypeEnv} {function argument : Expr} {domain codomain : Ty}
      (hf : HasType Γ function (.arr domain codomain))
      (ha : HasType Γ argument domain) :
      HasType Γ (.app function argument) codomain
  | letE {Γ : TypeEnv} {type result : Ty} {value body : Expr}
      (hv : HasType Γ value type)
      (hb : HasType (Γ.push type) body result) :
      HasType Γ (.letE type value body) result
  | letRecFun {Γ : TypeEnv} {domain codomain result : Ty} {functionBody body : Expr}
      (hf : HasType ((Γ.push (.arr domain codomain)).push domain)
        functionBody codomain)
      (hb : HasType (Γ.push (.arr domain codomain)) body result) :
      HasType Γ (.letRecFun domain codomain functionBody body) result

/-- Syntax-directed inference for the complete L2 grammar. -/
def infer (Γ : TypeEnv) : Expr → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .binary left .add right =>
      if infer Γ left = some .int ∧ infer Γ right = some .int then some .int else none
  | .binary left .ge right =>
      if infer Γ left = some .int ∧ infer Γ right = some .int then some .bool else none
  | .cond test yes no =>
      match infer Γ test, infer Γ yes, infer Γ no with
      | some .bool, some yesType, some noType =>
          if yesType = noType then some yesType else none
      | _, _, _ => none
  | .assign loc e =>
      if loc ∈ Γ.locs ∧ infer Γ e = some .int then some .unit else none
  | .deref loc => if loc ∈ Γ.locs then some .int else none
  | .skip => some .unit
  | .seq left right =>
      if infer Γ left = some .unit then infer Γ right else none
  | .loop test body =>
      if infer Γ test = some .bool ∧ infer Γ body = some .unit then some .unit else none
  | .bvar index => Γ.bound[index]?
  | .fvar name => Finmap.lookup name Γ.free
  | .lam domain body => (infer (Γ.push domain) body).map (.arr domain)
  | .app function argument =>
      match infer Γ function, infer Γ argument with
      | some (.arr domain codomain), some argumentType =>
          if domain = argumentType then some codomain else none
      | _, _ => none
  | .letE type value body =>
      if infer Γ value = some type then infer (Γ.push type) body else none
  | .letRecFun domain codomain functionBody body =>
      if infer ((Γ.push (.arr domain codomain)).push domain) functionBody =
          some codomain then
        infer (Γ.push (.arr domain codomain)) body
      else none

theorem infer_complete {Γ : TypeEnv} {e : Expr} {T : Ty}
    (typing : HasType Γ e T) : infer Γ e = some T := by
  induction typing <;> simp_all [infer]

theorem infer_sound {Γ : TypeEnv} : ∀ e T, infer Γ e = some T → HasType Γ e T := by
  intro e
  induction e generalizing Γ with
  | int n =>
      intro T h
      cases h
      exact .int n
  | bool b =>
      intro T h
      cases h
      exact .bool b
  | binary left op right ihLeft ihRight =>
      intro T h
      cases op with
      | add =>
          simp only [infer] at h
          split_ifs at h with valid
          · cases h
            exact .add (ihLeft .int valid.1) (ihRight .int valid.2)
      | ge =>
          simp only [infer] at h
          split_ifs at h with valid
          · cases h
            exact .ge (ihLeft .int valid.1) (ihRight .int valid.2)
  | cond test yes no ihTest ihYes ihNo =>
      intro T h
      simp only [infer] at h
      split at h <;> try cases h
      split_ifs at h with same
      · cases h
        exact .cond (ihTest .bool (by assumption))
          (ihYes _ (by assumption)) (ihNo _ (by simpa [same] using ‹_›))
  | assign loc e ih =>
      intro T h
      simp only [infer] at h
      split_ifs at h with valid
      · cases h
        exact .assign valid.1 (ih .int valid.2)
  | deref loc =>
      intro T h
      simp only [infer] at h
      split_ifs at h with present
      · cases h
        exact .deref present
  | skip =>
      intro T h
      cases h
      exact .skip
  | seq left right ihLeft ihRight =>
      intro T h
      simp only [infer] at h
      split_ifs at h with leftType
      · exact .seq (ihLeft .unit leftType) (ihRight T h)
  | loop test body ihTest ihBody =>
      intro T h
      simp only [infer] at h
      split_ifs at h with valid
      · cases h
        exact .loop (ihTest .bool valid.1) (ihBody .unit valid.2)
  | bvar index =>
      intro T h
      exact .bvar h
  | fvar name =>
      intro T h
      exact .fvar h
  | lam domain body ih =>
      intro T h
      simp only [infer] at h
      cases result : infer (Γ.push domain) body with
      | none => simp [result] at h
      | some codomain =>
          simp [result] at h
          cases h
          exact .lam (ih codomain result)
  | app function argument ihFunction ihArgument =>
      intro T h
      simp only [infer] at h
      split at h <;> try cases h
      split_ifs at h with same
      · cases h
        exact .app (ihFunction _ (by assumption))
          (ihArgument _ (by simpa [same] using ‹_›))
  | letE type value body ihValue ihBody =>
      intro T h
      simp only [infer] at h
      split_ifs at h with valid
      · exact .letE (ihValue type valid) (ihBody T h)
  | letRecFun domain codomain functionBody body ihFunction ihBody =>
      intro T h
      simp only [infer] at h
      split_ifs at h with valid
      · exact .letRecFun (ihFunction codomain valid) (ihBody T h)

theorem infer_iff_hasType {Γ : TypeEnv} {e : Expr} {T : Ty} :
    infer Γ e = some T ↔ HasType Γ e T :=
  ⟨infer_sound e T, infer_complete⟩

theorem typeable_iff_infer_isSome {Γ : TypeEnv} {e : Expr} :
    (∃ T, HasType Γ e T) ↔ (infer Γ e).isSome = true := by
  constructor
  · rintro ⟨T, typing⟩
    simp [infer_complete typing]
  · intro present
    cases result : infer Γ e with
    | none => simp [result] at present
    | some T => exact ⟨T, infer_sound e T result⟩

theorem HasType.unique {Γ : TypeEnv} {e : Expr} {T U : Ty}
    (first : HasType Γ e T) (second : HasType Γ e U) : T = U := by
  have firstResult := infer_complete first
  have secondResult := infer_complete second
  simpa [firstResult] using secondResult

instance (Γ : TypeEnv) (e : Expr) (T : Ty) : Decidable (HasType Γ e T) :=
  decidable_of_iff (infer Γ e = some T) infer_iff_hasType

end Silmaril.Courses.Cambridge.L2
