module

public import Silmaril.Wasm.Binaryen.Lower
public import Silmaril.Wasm.Binaryen.Profile

@[expose] public section

/-! # SimplifyLocals-lite: a dropped `local.tee` becomes a `local.set`

The part of Binaryen's `SimplifyLocals` (`src/passes/SimplifyLocals.cpp`, version_133,
`visitDrop`) that turns a `local.tee` whose value is dropped into a `local.set`:

```
drop (local.tee x v)   ~>   local.set x v
```

applied top-down (the operand `v` is rewritten too) in functions whose declared locals
are scalar or SIMD values. Functions with reference locals keep their original bodies:
the external engines do not yet provide evidence for every changed GC module without
exports. The raw traversal also handles references and remains proved in
`SimplifyLocalsLiteSim.lean`. The set is one byte shorter than the tee and the drop.

This file contains executable definitions only.
-/

namespace Silmaril.Wasm.Binaryen.SimplifyLocalsLite

mutual
/-- Rewrite every `drop (local.tee x v)` of a tree into `local.set x v`. -/
def tdE : BExpr → BExpr
  | .op i args =>
    match i, args with
    | .drop, [.op (.localTee x) [v]] => .op (.localSet x) [tdE v]
    | i, args => .op i (tdL args)
  | .block bt b => .block bt (tdL b)
  | .loop bt b => .loop bt (tdL b)
  | .if_ bt c t e => .if_ bt (tdL c) (tdL t) (tdL e)
  | .tryTable bt cs b => .tryTable bt cs (tdL b)
/-- `tdE` on every tree of a sequence. -/
def tdL : List BExpr → List BExpr
  | [] => []
  | e :: es => tdE e :: tdL es
end

/-- The pass on a module, preserving bodies with locals outside the scalar/SIMD
fragment. This is a per-function choice, so scalar work in mixed modules still runs. -/
def teeDrop (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f =>
      { f with body := if f.locals.all profileLocalType then tdL f.body else f.body } }

end Silmaril.Wasm.Binaryen.SimplifyLocalsLite
