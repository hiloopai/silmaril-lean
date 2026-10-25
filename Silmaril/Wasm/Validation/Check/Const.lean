module

public import Silmaril.Wasm.Validation.Const

@[expose] public section

/-! # Computable checker for constant expressions

`InstrConst.check`, `ExprConst.check` (both with iff lemmas and `Decidable`
instances), and `constOk`, parametric over a sound (resp. complete) expression
type checker `exprOk`.
-/

namespace Silmaril.Wasm.Validation

/-- Boolean check for `InstrConst C i`. -/
def InstrConst.check (C : Context) : Instr → Bool
  | .intConst _ _ | .floatConst _ _ | .vecConst _ | .refNull _ | .refI31
  | .refFunc _ | .structNew _ | .structNewDefault _ | .arrayNew _
  | .arrayNewDefault _ | .arrayNewFixed _ _ | .anyConvertExtern
  | .externConvertAny => true
  | .globalGet x =>
    match C.globals[x.toNat]? with
    | some g => g.mutability == .const
    | none => false
  | .intBinOp _ op => op == .add || op == .sub || op == .mul
  | _ => false

theorem InstrConst.check_iff {C : Context} {i : Instr} :
    InstrConst.check C i = true ↔ InstrConst C i := by
  constructor
  · intro h
    cases i <;> simp only [InstrConst.check, Bool.false_eq_true] at h
    case globalGet x =>
      revert h
      cases hg : C.globals[x.toNat]? with
      | none => simp
      | some g =>
        obtain ⟨m, t⟩ := g
        intro h
        simp only [beq_iff_eq] at h
        subst h
        exact .globalGet hg
    case intBinOp t op =>
      exact .binop (by simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using h)
    all_goals constructor
  · intro h
    cases h with
    | globalGet hg => simp [InstrConst.check, hg]
    | binop hop => rcases hop with rfl | rfl | rfl <;> rfl
    | _ => rfl

instance (C : Context) (i : Instr) : Decidable (InstrConst C i) :=
  decidable_of_iff _ InstrConst.check_iff

/-- Boolean check for `ExprConst C e`. -/
def ExprConst.check (C : Context) (e : Expr) : Bool := e.all (InstrConst.check C)

theorem ExprConst.check_iff {C : Context} {e : Expr} :
    ExprConst.check C e = true ↔ ExprConst C e := by
  simp [ExprConst.check, ExprConst, List.all_eq_true, InstrConst.check_iff]

instance (C : Context) (e : Expr) : Decidable (ExprConst C e) :=
  decidable_of_iff _ ExprConst.check_iff

theorem InstrConst.check_complete {C : Context} {i : Instr} (h : InstrConst C i) :
    InstrConst.check C i = true := InstrConst.check_iff.2 h

theorem ExprConst.check_complete {C : Context} {e : Expr} (h : ExprConst C e) :
    ExprConst.check C e = true := ExprConst.check_iff.2 h

/-- `C ⊢ e : t CONST`, relative to an expression checker `exprOk`. -/
def constOk (exprOk : Context → Expr → List CValType → Bool)
    (C : Context) (e : Expr) (t : CValType) : Bool :=
  exprOk C e [t] && ExprConst.check C e

theorem constOk_sound {exprOk : Context → Expr → List CValType → Bool}
    (hexpr : ∀ C e ts, exprOk C e ts = true → ExprOk C e ts)
    {C : Context} {e : Expr} {t : CValType} :
    constOk exprOk C e t = true → ExprOkConst C e t := by
  intro h
  simp only [constOk, Bool.and_eq_true] at h
  exact ⟨hexpr _ _ _ h.1, ExprConst.check_iff.1 h.2⟩

theorem constOk_complete {exprOk : Context → Expr → List CValType → Bool}
    (hexpr : ∀ C e ts, ExprOk C e ts → exprOk C e ts = true)
    {C : Context} {e : Expr} {t : CValType} :
    ExprOkConst C e t → constOk exprOk C e t = true := by
  intro h
  simp only [constOk, Bool.and_eq_true]
  exact ⟨hexpr _ _ _ h.typed, ExprConst.check_complete h.const⟩

theorem constOk_iff {exprOk : Context → Expr → List CValType → Bool}
    (hexpr : ∀ C e ts, exprOk C e ts = true ↔ ExprOk C e ts)
    {C : Context} {e : Expr} {t : CValType} :
    constOk exprOk C e t = true ↔ ExprOkConst C e t :=
  ⟨constOk_sound (fun _ _ _ => (hexpr _ _ _).1),
   constOk_complete (fun _ _ _ => (hexpr _ _ _).2)⟩

/-! ## Examples -/

example : ExprConst {} [.intConst .i32 1, .intConst .i32 2, .intBinOp .i32 .add] := by
  decide

example : ¬ ExprConst {} [.localGet ⟨0⟩] := by decide

example : ¬ InstrConst {} (.intBinOp .i32 (.div .signed)) := by decide

example : InstrConst { globals := [⟨.const, Ty.i32⟩] } (.globalGet ⟨0⟩) := by decide

example : ¬ InstrConst { globals := [⟨.var, Ty.i32⟩] } (.globalGet ⟨0⟩) := by decide

end Silmaril.Wasm.Validation
