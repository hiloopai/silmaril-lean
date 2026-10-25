module

public import Silmaril.Wasm.Binaryen.Pass.VacuumLite
public import Silmaril.Wasm.Numerics.Integer

@[expose] public section

/-! # Anchored integer constant addition

The first proved subset folds integer addition of two constant leaves.
Only original constant nodes are matched. A fold is applied only when the
transformed tail of its sequence has VacuumLite's anchor. Integer overflow wraps.
-/

namespace Silmaril.Wasm.Binaryen.PrecomputeLite

open Numerics

def constOf? (t : IntType) : BExpr → Option (BitVec t.width)
  | .op (.intConst t' b) [] => if h : t' = t then some (h ▸ b) else none
  | _ => none

def foldNode : BExpr → Option BExpr
  | .op (.intBinOp t .add) [a, b] => do
      let x ← constOf? t a
      let y ← constOf? t b
      some (.op (.intConst t (x+y)) [])
  | _ => none

mutual
def precE : BExpr → BExpr
  | .op i args => .op i (precL args)
  | .block bt b => .block bt (precL b)
  | .loop bt b => .loop bt (precL b)
  | .if_ bt c t e => .if_ bt (precL c) (precL t) (precL e)
  | .tryTable bt cs b => .tryTable bt cs (precL b)
def precL : List BExpr → List BExpr
  | [] => []
  | e :: es =>
      let es' := precL es
      let e' := precE e
      let e'' := if VacuumLite.headL es' == some true
        then (foldNode e).getD e' else e'
      e'' :: es'
end

def precomputeLite (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := precL f.body } }
end Silmaril.Wasm.Binaryen.PrecomputeLite
