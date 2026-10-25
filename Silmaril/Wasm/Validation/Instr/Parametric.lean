module

public import Silmaril.Wasm.Validation.TypeOk

@[expose] public section

/-! # Typing family: parametric instructions (§2.3 "Parametric instructions")

Spec rules (all present): `Instr_ok/nop`, `Instr_ok/unreachable`, `Instr_ok/drop`,
`Instr_ok/select-expl`, `Instr_ok/select-impl`.

`select (some ts)` is only well-formed with exactly one annotation (`SELECT t`),
which is why the explicit rule matches `some [t]`.
-/

namespace Silmaril.Wasm.Validation

inductive ParametricInstrOk (C : Context) : Instr → InstrType → Prop where
  /-- `Instr_ok/nop`. -/
  | nop : ParametricInstrOk C .nop (.plain [] [])
  /-- `Instr_ok/unreachable`. -/
  | unreachable {t₁ t₂ : List CValType} (h : InstrTypeOk C (.plain t₁ t₂)) :
      ParametricInstrOk C .unreachable (.plain t₁ t₂)
  /-- `Instr_ok/drop`. -/
  | drop {t : CValType} (h : TyOk C.toTypeCtx t) : ParametricInstrOk C .drop (.plain [t] [])
  /-- `Instr_ok/select-expl`. -/
  | selectExpl {t : ValType} (h : TyOk C.toTypeCtx (C.closeVal t)) :
      ParametricInstrOk C (.select (some [t]))
        (.plain [C.closeVal t, C.closeVal t, .i32] [C.closeVal t])
  /-- `Instr_ok/select-impl`: only numeric and vector operands. -/
  | selectImpl {t t' : CValType} (h : TyOk C.toTypeCtx t) (hs : Sub C.toTypeCtx t t')
      (hnv : t'.IsNumOrVec) :
      ParametricInstrOk C (.select none) (.plain [t, t, .i32] [t])

end Silmaril.Wasm.Validation
