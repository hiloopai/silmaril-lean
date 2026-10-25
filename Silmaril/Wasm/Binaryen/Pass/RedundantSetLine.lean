module

public import Silmaril.Wasm.Binaryen.Pass.ConstBranch

@[expose] public section

/-! Redundant local stores whose value is read from that same local.
The set becomes a drop, retaining the read even for an unset local; a tee becomes
its read. Both folded trees and adjacent flat instructions are handled.
-/

namespace Silmaril.Wasm.Binaryen.RedundantSetLine

mutual
def foldE : BExpr → BExpr
  | .op (.localSet x) [.op (.localGet y) []] =>
    if x == y then .op .drop [.op (.localGet y) []]
    else .op (.localSet x) [.op (.localGet y) []]
  | .op (.localTee x) [.op (.localGet y) []] =>
    if x == y then .op (.localGet y) []
    else .op (.localTee x) [.op (.localGet y) []]
  | .op i es => .op i (foldL es)
  | .block bt b => .block bt (foldL b)
  | .loop bt b => .loop bt (foldL b)
  | .if_ bt c t e => .if_ bt (foldL c) (foldL t) (foldL e)
  | .tryTable bt cs b => .tryTable bt cs (foldL b)
def foldL : List BExpr → List BExpr
  | [] => []
  | .op (.localGet x) [] :: .op (.localSet y) [] :: es =>
    if x == y then .op (.localGet x) [] :: .op .drop [] :: foldL es
    else .op (.localGet x) [] :: foldL (.op (.localSet y) [] :: es)
  | .op (.localGet x) [] :: .op (.localTee y) [] :: es =>
    if x == y then .op (.localGet x) [] :: foldL es
    else .op (.localGet x) [] :: foldL (.op (.localTee y) [] :: es)
  | e :: es => foldE e :: foldL es
end


def rseLine (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := foldL f.body } }

/-- Retain exportless modules, whose changed bytes may have no engine evidence. -/
def rseLineChecked (m : BModule) : BModule :=
  if ConstBranch.exportsFunc m && Exe.validOk (rseLine m) then rseLine m else m

end Silmaril.Wasm.Binaryen.RedundantSetLine
