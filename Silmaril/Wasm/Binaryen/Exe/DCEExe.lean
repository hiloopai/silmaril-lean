module

public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.Binaryen.Lower

@[expose] public section

/-! # The executable checked DCE

`Pass/DCE.lean` and `Pass/DCECheck.lean` carry the simulation tooling in their import
closure, which the executable does not need. This file holds a copy of the run
function of `dceChecked` over the light syntax and typing modules only. It is proved
equal to the original (`Exe.Dce.dceChecked_eq`, `Exe/PipelineSound.lean`), as
`Exe/InlineExe.lean` is for the inliner.
-/

namespace Silmaril.Wasm.Binaryen.Exe.Dce

open Silmaril.Wasm Silmaril.Wasm.Binaryen

mutual
/-- Copy of `Binaryen.dceE`. -/
def dceE : BExpr → List BExpr
  | .op i args =>
      let a := dceL args
      if BExpr.listBot a then a else [.op i a]
  | .block bt b => [.block bt (dceL b)]
  | .loop bt b => [.loop bt (dceL b)]
  | .if_ bt c t e =>
      let c' := dceL c
      if BExpr.listBot c' then c' else [.if_ bt c' (dceL t) (dceL e)]
  | .tryTable bt cs b => [.tryTable bt cs (dceL b)]
/-- Copy of `Binaryen.dceL`. -/
def dceL : List BExpr → List BExpr
  | [] => []
  | e :: es =>
      let e' := dceE e
      if BExpr.listBot e' then e' else e' ++ dceL es
end

/-- Copy of `Binaryen.endsInBotB`. -/
def endsInBotB (X : List Instr) : Bool :=
  match X.getLast? with
  | some i => botInstr i
  | none => false

mutual
/-- Copy of `Binaryen.dceSafeWEB`. -/
def dceSafeWEB : BExpr → Bool
  | .op _ args => dceSafeWB args &&
      (!BExpr.listBot (dceL args) || endsInBotB (BExpr.lowerList (dceL args)))
  | .block _ b => dceSafeWB b
  | .loop _ b => dceSafeWB b
  | .tryTable _ _ b => dceSafeWB b
  | .if_ _ c t e => dceSafeWB c &&
      (if BExpr.listBot (dceL c) then endsInBotB (BExpr.lowerList (dceL c))
       else dceSafeWB t && dceSafeWB e)
/-- Copy of `Binaryen.dceSafeWB`. -/
def dceSafeWB : List BExpr → Bool
  | [] => true
  | e :: es => dceSafeWEB e &&
      (if BExpr.listBot (dceE e) then es.isEmpty || endsInBotB (BExpr.lowerList (dceE e))
       else dceSafeWB es)
end

/-- Copy of `Binaryen.dceBodyChecked`. -/
def dceBodyChecked (b : List BExpr) : List BExpr := if dceSafeWB b then dceL b else b

/-- Copy of `Binaryen.dceChecked` (`BModule.mapBodies dceBodyChecked`). -/
def dceChecked (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := dceBodyChecked f.body } }

end Silmaril.Wasm.Binaryen.Exe.Dce
