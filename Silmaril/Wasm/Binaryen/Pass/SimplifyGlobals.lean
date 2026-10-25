module

public import Silmaril.Wasm.Binaryen.Lower

@[expose] public section

/-! # SimplifyGlobals: propagate immutable integer globals

Only defined, immutable globals with a single integer-constant initializer are
eligible. Imported globals and computed initializers are left alone. The global
declarations and indices are preserved; a subsequent RUME can remove globals
whose last use has disappeared.

This file contains executable definitions only. The module-level semantic proof
is a separate obligation in `SimplifyGlobalsSound.lean`.
-/

namespace Silmaril.Wasm.Binaryen

namespace SimplifyGlobals

/-- A literal initializer of an immutable global whose declared type is the literal's
type (validation implies the match; checking it keeps the typing argument local). -/
def constant? (g : Global) : Option Instr :=
  match g.type.mutability, g.init with
  | .const, [i@(.intConst t _)] => if g.type.value = .num (.int t) then some i else none
  | _, _ => none

/-- Resolve an absolute global index, accounting for imported globals. -/
def lookup (m : BModule) (x : GlobalIdx) : Option Instr :=
  if x.toNat < m.numImportedGlobals then none
  else m.base.globals[x.toNat - m.numImportedGlobals]?.bind constant?

/-- Rewrite just the operator; operands are retained even for a stacky `global.get`. -/
def instr (m : BModule) (i : Instr) : Instr :=
  match i with
  | .globalGet x => (lookup m x).getD i
  | _ => i

mutual
/-- Propagate literals recursively through folded operands and structured bodies. -/
def expr (m : BModule) : BExpr → BExpr
  | .op i args => .op (instr m i) (exprs m args)
  | .block bt b => .block bt (exprs m b)
  | .loop bt b => .loop bt (exprs m b)
  | .if_ bt c t e => .if_ bt (exprs m c) (exprs m t) (exprs m e)
  | .tryTable bt cs b => .tryTable bt cs (exprs m b)
/-- Propagate literals through a list of folded expressions. -/
def exprs (m : BModule) : List BExpr → List BExpr
  | [] => []
  | e :: es => expr m e :: exprs m es
end

end SimplifyGlobals

/-- Simplify immutable global reads in function bodies, leaving declarations intact. -/
def simplifyGlobals (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := SimplifyGlobals.exprs m f.body } }

end Silmaril.Wasm.Binaryen
