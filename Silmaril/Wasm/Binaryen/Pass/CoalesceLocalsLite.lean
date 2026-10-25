module

public import Silmaril.Wasm.Binaryen.Pass.VacuumLite

@[expose] public section

/-! # CoalesceLocals-lite: a local store overwritten by the next store is dropped

The part of Binaryen's `CoalesceLocals` (`src/passes/CoalesceLocals.cpp`, dead stores
found by liveness) that needs no liveness: a `local.set x v` whose next sibling in the
same sequence stores a constant into the same local is dead, so its value is dropped:

```
local.set x v; local.set x (const c)   ~>   drop v; local.set x (const c)
```

applied everywhere, bottom-up (`v` is rewritten too); the overwriting store is kept as
it is and is not itself a candidate. The value `v` is still evaluated (it may trap or
have effects); `Vacuum` removes the `drop` of a constant in the next round. The drop
is one byte shorter than the set (for the first 128 locals).

Nothing runs between the two stores, which is what makes the code simulation of
`Binaryen/CoalesceLocalsLiteSim.lean` frame-equal: when the rewritten side stores the
constant, the original side runs both stores and reaches the same frame. The full
liveness pass is open work outside this restricted pass.

This file contains executable definitions only.
-/

namespace Silmaril.Wasm.Binaryen.CoalesceLocalsLite

open VacuumLite (constInstr)

/-- `e` stores a constant into local `x`: `local.set x (const c)`. -/
def overwrites (x : LocalIdx) : BExpr → Bool
  | .op (.localSet y) [.op k []] => x == y && constInstr k
  | _ => false

mutual
/-- Rewrite every dead store of a tree. -/
def dsE : BExpr → BExpr
  | .op i args => .op i (dsL args)
  | .block bt b => .block bt (dsL b)
  | .loop bt b => .loop bt (dsL b)
  | .if_ bt c t e => .if_ bt (dsL c) (dsL t) (dsL e)
  | .tryTable bt cs b => .tryTable bt cs (dsL b)
/-- Rewrite every dead store of a sequence: `local.set x v` followed by an overwrite
becomes `drop v`, and the overwrite is kept unchanged. -/
def dsL : List BExpr → List BExpr
  | [] => []
  | [e] => [dsE e]
  | e :: e₂ :: es =>
    match e with
    | .op (.localSet x) [v] =>
      if overwrites x e₂ then .op .drop [dsE v] :: e₂ :: dsL es
      else .op (.localSet x) [dsE v] :: dsL (e₂ :: es)
    | e => dsE e :: dsL (e₂ :: es)
end

/-- The pass on a module. -/
def deadSetLite (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := dsL f.body } }

end Silmaril.Wasm.Binaryen.CoalesceLocalsLite
