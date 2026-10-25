module

public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
public import Silmaril.Wasm.SingleThreaded.Determinism.FamDetVector
public import Silmaril.Wasm.SingleThreaded.Determinism.FamDetTable
public import Silmaril.Wasm.SingleThreaded.Determinism.FamDetMemory
public import Silmaril.Wasm.SingleThreaded.Determinism.FamDetAggregate
public import Mathlib.Logic.Relation

@[expose] public section

/-! # Determinism of head steps

Two head steps at the same first non-value, whose value arguments are suffixes of
one another, consume the same arguments and have joinable results (equal, except
under a context rule, where the inner steps are joined by induction).
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

/-- Host-free reduction in the deterministic profile. -/
abbrev DStep (o : GrowKind → Nat → Nat → Nat → Bool) : Config H → Config H → Prop :=
  Step (Profile.deterministic o) noHost

/-- Joinability in at most one step on each side. -/
def Join {α : Type _} (R : α → α → Prop) (x y : α) : Prop :=
  ∃ z, Relation.ReflGen R x z ∧ Relation.ReflGen R y z

theorem Join.rfl' {α : Type _} {R : α → α → Prop} {x : α} : Join R x x :=
  ⟨x, .refl, .refl⟩

theorem Join.symm {α : Type _} {R : α → α → Prop} {x y : α} (h : Join R x y) : Join R y x :=
  let ⟨z, h₁, h₂⟩ := h; ⟨z, h₂, h₁⟩

theorem Join.map {α : Type _} {R : α → α → Prop} (F : α → α) (hF : ∀ a b, R a b → R (F a) (F b))
    {x y : α} (h : Join R x y) : Join R (F x) (F y) := by
  obtain ⟨z, h₁, h₂⟩ := h
  refine ⟨F z, ?_, ?_⟩
  · cases h₁ with
    | refl => exact .refl
    | single h => exact .single (hF _ _ h)
  · cases h₂ with
    | refl => exact .refl
    | single h => exact .single (hF _ _ h)

section lift
variable {P : Profile}

theorem lift_instrs (vs : List Val) (rest : List Admin) :
    ∀ a b : Config H, Step P noHost a b →
      Step P noHost ⟨a.store, a.frame, vals vs ++ a.code ++ rest⟩
        ⟨b.store, b.frame, vals vs ++ b.code ++ rest⟩ := by
  rintro ⟨s, f, is⟩ ⟨s', f', is'⟩ h
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact .ctxtInstrs h hne
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa using h

theorem lift_label (n : Nat) (cont : List Instr) :
    ∀ a b : Config H, Step P noHost a b →
      Step P noHost ⟨a.store, a.frame, [.label n cont a.code]⟩
        ⟨b.store, b.frame, [.label n cont b.code]⟩ := by
  rintro ⟨s, f, is⟩ ⟨s', f', is'⟩ h
  exact .ctxtLabel h

theorem lift_handler (n : Nat) (cs : List Catch) :
    ∀ a b : Config H, Step P noHost a b →
      Step P noHost ⟨a.store, a.frame, [.handler n cs a.code]⟩
        ⟨b.store, b.frame, [.handler n cs b.code]⟩ := by
  rintro ⟨s, f, is⟩ ⟨s', f', is'⟩ h
  exact .ctxtHandler h

theorem lift_frame (n : Nat) (f : Frame) :
    ∀ a b : Config H, Step P noHost a b →
      Step P noHost ⟨a.store, f, [.frame n a.frame a.code]⟩
        ⟨b.store, f, [.frame n b.frame b.code]⟩ := by
  rintro ⟨s, fi, is⟩ ⟨s', fi', is'⟩ h
  exact .ctxtFrame h

end lift

/-! ## Families -/

def FamRel (P : Profile) (k : Fam) (s : Store H) (f : Frame) (l : List Admin) (c : Config H) :
    Prop :=
  match k with
  | .parametric => ∃ is', ParametricStep l is' ∧ c = ⟨s, f, is'⟩
  | .numeric => ∃ is', NumericStep P l is' ∧ c = ⟨s, f, is'⟩
  | .vector => ∃ is', VectorStep P l is' ∧ c = ⟨s, f, is'⟩
  | .variable => VariableStep ⟨s, f, l⟩ c
  | .table => TableStep P ⟨s, f, l⟩ c
  | .memory => MemoryStep P ⟨s, f, l⟩ c
  | .reference => RefStep ⟨s, f, l⟩ c
  | .aggregate => AggregateStep ⟨s, f, l⟩ c
  | .control => False

theorem IsCallRef.famOf {c : Admin} (h : c.IsCallRef) : famOf c = .control := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsCallRef] at h
  · cases i <;> simp at h; rfl
  · rfl

theorem Head.fam_inv {P : Profile} {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c : Config H} (h : Head P s f args e c) (hc : famOf e ≠ .control) :
    FamRel P (famOf e) s f (vals args ++ [e]) c := by
  cases h with
  | parametric h => rw [(famOf_of_shape (ParametricStep.shape h)).2]; exact ⟨_, h, rfl⟩
  | numeric h => rw [(famOf_of_shape (NumericStep.shape h)).2]; exact ⟨_, h, rfl⟩
  | vector h => rw [(famOf_of_shape (VectorStep.shape h)).2]; exact ⟨_, h, rfl⟩
  | «variable» h => rw [(famOf_of_shape (VariableStep.shape h)).2]; exact h
  | table h => rw [(famOf_of_shape (TableStep.shape h)).2]; exact h
  | memory h => rw [(famOf_of_shape (MemoryStep.shape h)).2]; exact h
  | reference h => rw [(famOf_of_shape (RefStep.shape h)).2]; exact h
  | aggregate h => rw [(famOf_of_shape (AggregateStep.shape h)).2]; exact h
  | callRefNull hc' => exact absurd (IsCallRef.famOf hc') hc
  | callRefFunc _ hc' => exact absurd (IsCallRef.famOf hc') hc
  | _ => exact absurd rfl hc

theorem Head.det_fam {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {args₁ args₂ p : List Val} {e : Admin} {c₁ c₂ : Config H} (hc : famOf e ≠ .control)
    (h₁ : Head (Profile.deterministic o) s f args₁ e c₁)
    (h₂ : Head (Profile.deterministic o) s f args₂ e c₂) (hp : args₁ = p ++ args₂) :
    p = [] ∧ c₁ = c₂ := by
  have f₁ := h₁.fam_inv hc
  have f₂ := h₂.fam_inv hc
  have hl : vals args₁ ++ [e] = vals p ++ (vals args₂ ++ [e]) := by subst hp; simp
  revert f₁ f₂ hc
  generalize famOf e = k
  intro hc f₁ f₂
  cases k with
  | parametric =>
    obtain ⟨is₁, r₁, rfl⟩ := f₁; obtain ⟨is₂, r₂, rfl⟩ := f₂
    obtain ⟨hp', rfl⟩ := ParametricStep.det r₁ r₂ hl; exact ⟨hp', rfl⟩
  | numeric =>
    obtain ⟨is₁, r₁, rfl⟩ := f₁; obtain ⟨is₂, r₂, rfl⟩ := f₂
    obtain ⟨hp', rfl⟩ := NumericStep.det r₁ r₂ hl; exact ⟨hp', rfl⟩
  | vector =>
    obtain ⟨is₁, r₁, rfl⟩ := f₁; obtain ⟨is₂, r₂, rfl⟩ := f₂
    obtain ⟨hp', rfl⟩ := VectorStep.det r₁ r₂ hl; exact ⟨hp', rfl⟩
  | «variable» => exact VariableStep.det f₁ f₂ hl
  | table => exact TableStep.det f₁ f₂ hl
  | memory => exact MemoryStep.det f₁ f₂ hl
  | reference => exact RefStep.det f₁ f₂ hl
  | aggregate => exact AggregateStep.det f₁ f₂ hl
  | control => exact absurd rfl hc

/-! ## Control rules -/

open Lean Meta Elab Tactic in
/-- For every hypothesis `h : a = b` between lists of instructions, add
`hfnv : fnv a = fnv b`. -/
elab "fnv_all" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    let listAdmin ← mkAppM ``List #[mkConst ``Silmaril.Wasm.Execution.Core.Admin]
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let t ← instantiateMVars ldecl.type
      match t.eq? with
      | some (ty, _, _) =>
        if (← isDefEq ty listAdmin) then
          let pf ← mkCongrArg (mkConst ``Silmaril.Wasm.SingleThreaded.Det.fnv) ldecl.toExpr
          let (_, g') ← g.note `hfnv pf
          g := g'
      | none => pure ()
    replaceMainGoal [g]

theorem IsReturnCallRef.val_none {c : Admin} (h : c.IsReturnCallRef) : c.val? = none := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsReturnCallRef] at h
  · cases i <;> simp at h; rfl
  · rfl

theorem IsReturnCallRef.blocked {c : Admin} (h : c.IsReturnCallRef) : Blocked c :=
  .inr (.inr h)

@[simp] theorem fnv_br_cons (l : LabelIdx) (r : List Admin) :
    fnv (.plain (.br l) :: r) = ([], .plain (.br l) :: r) := fnv_cons_of_none rfl r
@[simp] theorem fnv_return_cons (r : List Admin) :
    fnv (.plain .return_ :: r) = ([], .plain .return_ :: r) := fnv_cons_of_none rfl r
@[simp] theorem fnv_throwRef_cons (r : List Admin) :
    fnv (.plain .throwRef :: r) = ([], .plain .throwRef :: r) := fnv_cons_of_none rfl r

set_option hygiene false in
/-- Close two control head rules at the same instruction. -/
macro "hd_close" : tactic => `(tactic| first
  | (exfalso; assumption)
  | (subst_vars; exact ⟨by simpa using hp, Join.rfl'⟩)
  | (subst_vars; exfalso; exact not_step_vals ‹_›)
  | (subst_vars; exfalso; exact not_step_trap ‹_›)
  | (subst_vars; exfalso; exact not_step_throwing ‹_›)
  | (subst_vars; exfalso
     refine not_step_blocked ‹_› (W := _) (e := .plain (.br _)) (rest := _) (by simp) ?_
     exact .inl ⟨_, rfl⟩)
  | (subst_vars; exfalso
     refine not_step_blocked ‹_› (W := _) (e := .plain .return_) (rest := _) (by simp) ?_
     exact .inr (.inl rfl))
  | (subst_vars; exfalso
     refine not_step_blocked ‹_› (W := _) (rest := _)
       (by simp [fnv_cons_of_none (IsReturnCallRef.val_none ‹_›)]) ?_
     exact IsReturnCallRef.blocked ‹_›)
  | (subst_vars; fnv_all
     simp [fnv_cons_of_none (IsReturnCallRef.val_none ‹_›)] at *
     done)
  | (subst_vars; fnv_all
     simp at *
     done))

set_option hygiene false in
/-- A family rule at a control instruction is impossible. -/
macro "fam_excl" : tactic => `(tactic| (exfalso; first
  | exact hc (famOf_of_shape (ParametricStep.shape ‹_›)).2 (by decide)
  | exact hc (famOf_of_shape (NumericStep.shape ‹_›)).2 (by decide)
  | exact hc (famOf_of_shape (VectorStep.shape ‹_›)).2 (by decide)
  | exact hc (famOf_of_shape (VariableStep.shape ‹_›)).2 (by decide)
  | exact hc (famOf_of_shape (TableStep.shape ‹_›)).2 (by decide)
  | exact hc (famOf_of_shape (MemoryStep.shape ‹_›)).2 (by decide)
  | exact hc (famOf_of_shape (RefStep.shape ‹_›)).2 (by decide)
  | exact hc (famOf_of_shape (AggregateStep.shape ‹_›)).2 (by decide)))

end Silmaril.Wasm.SingleThreaded.Det
