module

public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.Equiv

@[expose] public section

/-! A single traversal counts direct calls to all function indices at once. The
array is bounded by the module's function count; invalid indices are ignored. -/

namespace Silmaril.Wasm.Binaryen.Exe.Inl

mutual
/-- Add the direct calls in a tree to a uniquely threaded count array. -/
def addCallsE : BExpr → Array Nat → Array Nat
  | .op i args, counts =>
    let counts := match i with
      | .call f => counts.modify f.toNat (· + 1)
      | _ => counts
    addCallsL args counts
  | .block _ b, counts | .loop _ b, counts | .tryTable _ _ b, counts =>
    addCallsL b counts
  | .if_ _ c t e, counts => addCallsL e (addCallsL t (addCallsL c counts))
/-- Add the direct calls in a sequence to a count array. -/
def addCallsL : List BExpr → Array Nat → Array Nat
  | [], counts => counts
  | e :: es, counts => addCallsL es (addCallsE e counts)
end

/-- One count per imported or defined function, computed in one traversal. -/
def moduleCallCounts (m : BModule) : Array Nat :=
  m.funcs.foldl (fun counts fn => addCallsL fn.body counts)
    (Array.replicate (m.numImportedFuncs + m.funcs.length) 0)

end Silmaril.Wasm.Binaryen.Exe.Inl
