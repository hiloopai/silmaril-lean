module

public import Silmaril.Wasm.Interp.Diverge.Defs
public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Abstract.HostEval.Defs

/-!
# Coinductive divergence of the open native semantics: definitions

`Silmaril.Wasm.Interp.DivStep` unfolds divergence of the recursive native semantics, reading
terminating parts with `Eval`. `DivStepO C` is the same unfolding for the open semantics
`EvalO C`: terminating parts are read by `EvalO C`, and a call that returns is answered by the
oracle `C` (`callRet`, any callee, as in `EvalO.callOk`), while divergence inside a Wasm callee
is read by `Y` (`callee`). At the closure `C = closedCall` it is `DivStep`
(`Silmaril.Wasm.Abstract.DivO.Thms`).

* `EvalDivO C := gfp (X ↦ DivStepO C X X)`;
* `LocalDivO C := gfp (X ↦ DivStepO C X ⊥)`: divergence within the function, every call it
  makes answered by `C`.

For calls (`y` a callee, arguments and store, as in `ReachO`/`PendO`):

* `CallDivO C y`: the body of the Wasm function `y` diverges (`EvalDivO C`);
* `LocalCallDivO C y`: it diverges within its own function (`LocalDivO C`);
* `BodyReachO C x y`: the body of `x` reaches the call `y` (one `PendO` descent).

These are the Core-side decomposition targets of H2 divergence with
`C = hostCall host`. The logged, host-independent packaging is separate.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (Problem)

variable {H : Type}

/-- One unfolding of divergence of `EvalO C`: `X` for the code itself, `Y` for callee bodies. -/
inductive DivStepO (C : CallRel H) (X Y : Problem H) : Problem H where
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr} :
      X s f stk args → DivStepO C X Y s f stk (.op i args :: es)
  | callee {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType}
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      Y s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) →
      DivStepO C X Y s f stk (.op (.call x) args :: es)
  | callRet {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {fl : Flow}
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl))
      (hvs : fl.retVals = some vs) :
      X s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es →
      DivStepO C X Y s f stk (.op (.call x) args :: es)
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      X s₂ f₂ stk₂ es → DivStepO C X Y s f stk (.op i args :: es)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStepO C X Y s f stk (.block bt body :: es)
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      X s₁ f₁ (vs.take nr ++ stk.drop np) es → DivStepO C X Y s f stk (.block bt body :: es)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} (har : arity f bt = some (np, nr)) :
      X s f (stk.take np) body → DivStepO C X Y s f stk (.loop bt body :: es)
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, .normal vs)) :
      X s₁ f₁ (vs.take nr ++ stk.drop np) es → DivStepO C X Y s f stk (.loop bt body :: es)
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, .brk 0 vs)) :
      X s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) →
      DivStepO C X Y s f stk (.loop bt body :: es)
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr} :
      X s f stk c → DivStepO C X Y s f stk (.if_ bt c t el :: es)
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat}
      (hc : EvalO C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      X s₁ f₁ (stk₁.take np) (if b then t else el) → DivStepO C X Y s f stk (.if_ bt c t el :: es)
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      (hc : EvalO C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalO C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      X s₂ f₂ (vs.take nr ++ stk₁.drop np) es → DivStepO C X Y s f stk (.if_ bt c t el :: es)

theorem DivStepO.mono {C : CallRel H} {X X' Y Y' : Problem H} (hX : X ≤ X') (hY : Y ≤ Y') {s : Store H}
    {f : Frame} {stk : List Val} {es : List BExpr} (h : DivStepO C X Y s f stk es) :
    DivStepO C X' Y' s f stk es := by
  cases h with
  | args h => exact .args (hX _ _ _ _ h)
  | callee hargs hfi hcode hty h => exact .callee hargs hfi hcode hty (hY _ _ _ _ h)
  | callRet hargs hfi hty hcall hvs h =>
    exact .callRet hargs hfi hty hcall hvs (hX _ _ _ _ h)
  | opK hi hargs hflat h => exact .opK hi hargs hflat (hX _ _ _ _ h)
  | block har h => exact .block har (hX _ _ _ _ h)
  | blockK har hbody hvs h => exact .blockK har hbody hvs (hX _ _ _ _ h)
  | loop har h => exact .loop har (hX _ _ _ _ h)
  | loopK har hbody h => exact .loopK har hbody (hX _ _ _ _ h)
  | loopBack har hbody h => exact .loopBack har hbody (hX _ _ _ _ h)
  | cond h => exact .cond (hX _ _ _ _ h)
  | arm hc hb har h => exact .arm hc hb har (hX _ _ _ _ h)
  | ifK hc hb har harm hvs h => exact .ifK hc hb har harm hvs (hX _ _ _ _ h)

/-- Unfolding of the open semantics' divergence. -/
def divOpO (C : CallRel H) : Problem H →o Problem H where
  toFun X := DivStepO C X X
  monotone' _ _ h _ _ _ _ := DivStepO.mono h h

/-- Unfolding of divergence within the function, every call answered by `C`. -/
def localDivOpO (C : CallRel H) : Problem H →o Problem H where
  toFun X := DivStepO C X ⊥
  monotone' _ _ h _ _ _ _ := DivStepO.mono h le_rfl

/-- **Coinductive divergence of the open native semantics.** -/
def EvalDivO (C : CallRel H) : Problem H := (divOpO C).gfp

/-- **Divergence within a function**, every call answered by `C`. -/
def LocalDivO (C : CallRel H) : Problem H := (localDivOpO C).gfp

/-- The body of the Wasm function called by `y` diverges. -/
def CallDivO (C : CallRel H) (y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), y.2.2.funcs[y.1]? = some fi ∧ fi.code = .wasm fn ∧
    EvalDivO C y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (liftInstrs fn.body)

/-- The body of the Wasm function called by `y` diverges within its own function. -/
def LocalCallDivO (C : CallRel H) (y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), y.2.2.funcs[y.1]? = some fi ∧ fi.code = .wasm fn ∧
    LocalDivO C y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (liftInstrs fn.body)

/-- The body of the Wasm function called by `x` reaches the call `y`. -/
def BodyReachO (C : CallRel H) (x y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func), x.2.2.funcs[x.1]? = some fi ∧ fi.code = .wasm fn ∧
    ReachO C x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) y

end Silmaril.Wasm.Abstract
