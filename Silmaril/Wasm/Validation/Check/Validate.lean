module

public import Silmaril.Wasm.Validation.Check.AtomicA
public import Silmaril.Wasm.Validation.Check.AtomicB
public import Silmaril.Wasm.Validation.Check.Const
public import Silmaril.Wasm.Validation.Check.Func
public import Silmaril.Wasm.Validation.Check.Instrs
public import Silmaril.Wasm.Validation.Check.Module
public import Silmaril.Wasm.Validation.Check.ModuleDefs
public import Silmaril.Wasm.Validation.Check.TyOk
public import Silmaril.Wasm.Validation.Check.Types

@[expose] public section

/-! # The concrete module validator

Assembles `checkModule?` from the merged part checkers and proves it sound:
`validate? m = some mt → ModuleOk m mt`.
-/

namespace Silmaril.Wasm.Validation

/-- The type-validity oracle: `TyOk.check`. -/
def tyOkC : TyOkOracle := fun Δ {_} t => TyOk.check Δ t

theorem tyOkC_sound : TyOkSound tyOkC := fun _ _ _ h => TyOk.check_sound h

/-- The atomic-instruction oracle: families A, then families B. -/
def atomC : AtomOracle := fun C S i =>
  atomicA? (@tyOkC C.toTypeCtx) C S i <|> atomicB? (@tyOkC C.toTypeCtx) C S i

theorem atomC_sound : AtomSound atomC := by
  intro C stk i n xs out h
  have hty : ∀ {k} {t : Ty k}, @tyOkC C.toTypeCtx k t = true → TyOk C.toTypeCtx t :=
    fun h => TyOk.check_sound h
  unfold atomC at h
  cases ha : atomicA? (@tyOkC C.toTypeCtx) C stk i with
  | some r =>
    rw [ha] at h
    cases h
    exact atomicA?_sound hty ha
  | none =>
    rw [ha] at h
    exact atomicB?_sound hty h

/-- The expression checker. -/
def exprC : Context → Expr → List CValType → Bool := checkExpr? atomC tyOkC

theorem exprC_sound : ∀ C e ts, exprC C e ts = true → ExprOk C e ts :=
  fun _ _ _ h => checkExpr?_sound atomC_sound tyOkC_sound h

/-- The constant-expression checker. -/
def constC : Context → Expr → CValType → Bool := constOk exprC

theorem constC_sound : ∀ C e t, constC C e t = true → ExprOkConst C e t :=
  fun _ _ _ h => constOk_sound exprC_sound h

theorem tyOkC_sound' : ∀ Δ {k} (t : Ty k), tyOkC Δ t = true → TyOk Δ t :=
  fun Δ _ t h => tyOkC_sound Δ _ t h

/-- The default part checkers. -/
def defaultCheckers : ModuleCheckers where
  types? := typesCheck? RecTypeOkAt.check
  import? := importCheck? tyOkC
  tag? := tagCheck? tyOkC
  globals? := globalsCheck? tyOkC constC
  mem := memCheck
  table? := tableDefCheck? tyOkC constC
  func := funcCheck tyOkC exprC
  data := dataCheck constC
  elem? := elemCheck? tyOkC constC
  start := startCheck
  export? := exportCheck?

theorem defaultCheckers_sound : defaultCheckers.Sound where
  types h := typesCheck?_sound (fun _ _ _ h => RecTypeOkAt.check_sound h) h
  import_ h := importCheck?_sound tyOkC_sound' h
  tag h := tagCheck?_sound tyOkC_sound' h
  globals h := globalsCheck?_sound tyOkC_sound' constC_sound h
  mem h := memCheck_sound h
  table h := tableDefCheck?_sound tyOkC_sound' constC_sound h
  func h := funcCheck_sound tyOkC_sound' exprC_sound h
  data h := dataCheck_sound constC_sound h
  elem h := elemCheck?_sound tyOkC_sound' constC_sound h
  start h := startCheck_sound h
  export_ h := exportCheck?_sound h

/-- The concrete module validator. -/
def validate? (m : Module) : Option CModuleType := checkModule? defaultCheckers m

theorem validate?_sound {m : Module} {mt : CModuleType} (h : validate? m = some mt) :
    ModuleOk m mt :=
  checkModule?_sound defaultCheckers_sound h

theorem validate_sound {m : Module} (h : (validate? m).isSome) : ModuleValid m :=
  checkModuleValid_sound defaultCheckers_sound h

/-! ## Examples -/

section Examples

/-- The empty module. -/
example : (validate? {}).isSome = true := by decide +kernel

/-- `(func (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)`. -/
def exAdd : Module where
  types := [⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add]⟩]

example : (validate? exAdd).isSome = true := by decide +kernel

/-- A global and an export. -/
def exGlobal : Module where
  globals := [⟨⟨.const, .i32⟩, [.intConst .i32 42]⟩]
  exports := [⟨"g", .global ⟨0⟩⟩]

example : (validate? exGlobal).isSome = true := by decide +kernel

/-- Ill-typed: the body leaves an `i64` where an `i32` result is declared. -/
def exBad : Module where
  types := [⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i64 0]⟩]

example : validate? exBad = none := by decide +kernel

end Examples

end Silmaril.Wasm.Validation
