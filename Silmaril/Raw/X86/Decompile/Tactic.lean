module

public import Silmaril.X86.Decompile.Cfg
public meta import Lean.Elab.Tactic.Basic

/-!
# The `split_functions`, `recover_cfg` and `decode_region` tactics

`split_functions` closes a goal that states the result of `Decompile.check` on
concrete data — `check r p fuel = .ok acc`, or any equation between closed
terms built from `check` — by reduction in the kernel. `recover_cfg` does the
same for `Decompile.checkCfg`, including a goal whose proposal is
`CfgPropose.ofFunction` applied to concrete data, so that the proposer and the
checker are both run by the kernel.

Compiled evaluation (the token the layout check forbids) is not used and must not be: a decompilation accepted by the
compiler rather than the kernel is a test, not a proof. The tactic tries `rfl`
first, which reduces `check` directly, and falls back to `decide`, which also
reduces the `DecidableEq` instance. `maxRecDepth` is raised because the
elaborator's default limit is reached by lists of a few hundred bytes long
before the kernel is troubled.

## How far it scales

The 64-byte, 20-instruction `MD5_memset` fixture is closed by the kernel in
`Decompile.Examples`, for both rungs: its partition, and the four-block
control-flow graph of its loop. The 3253-byte, 794-instruction `.text` of the
ingested `clang -O0` `sha256.o` is not: `Ext.decode` reduction over that many
bytes is too slow in the kernel, so that example is checked by `#guard`, which
runs compiled code at build time. A `#guard` is a test and adds no axioms, but
it is not a proof, and `Decompile.Examples` says which is which for each
example, in the style of `Crypto.X86.Objects.Sha256ClangO0Facts`.

`recover_cfg` reduces `CfgPropose.ofFunction` as well as `checkCfg`, which is
why that proposer avoids `List.mergeSort`: well-founded recursion does not
reduce in the kernel.

## `decode_region`

`decode_region` closes a goal about `Region.decode?` on concrete bytes — the
rung below the other two, since a partition cannot be checked against a region
that does not decode. On failure it does what a bare `decide` cannot: it finds
the `Region.decode?` application in the goal, reduces the *error* branch
`Region.decode`, and reports which of the two things went wrong — the address at
which no instruction of the model decodes, or exhausted fuel. Those are the only
two ways `Region.decode` fails (`Decompile.DecodeError`), and they call for
opposite repairs: a bad address usually means the region's base or extent is
wrong, or that the bytes are data rather than code; exhausted fuel just means
the `fuel` argument is too small.
-/

@[expose] public section

namespace Silmaril.X86.Decompile

/-- Close a goal about `check` on concrete data by kernel reduction. -/
scoped syntax "split_functions" : tactic

macro_rules
  | `(tactic| split_functions) =>
    `(tactic| set_option maxRecDepth 100000 in (first | rfl | decide))

/-- Close a goal about `checkCfg`, or about a proposal `CfgPropose.ofFunction`
builds, on concrete data by kernel reduction. -/
scoped syntax "recover_cfg" : tactic

macro_rules
  | `(tactic| recover_cfg) =>
    `(tactic| set_option maxRecDepth 100000 in (first | rfl | decide))

/-! ## `decode_region` -/

open Lean Elab Tactic Meta

/-- The region and fuel of the first `Region.decode?` or `Region.decode`
application in an expression. -/
private meta partial def findRegionDecode : Expr → Option (Expr × Expr)
  | .mdata _ b => findRegionDecode b
  | .lam _ _ b _ => findRegionDecode b
  | .forallE _ d b _ => findRegionDecode d <|> findRegionDecode b
  | .letE _ _ v b _ => findRegionDecode v <|> findRegionDecode b
  | e@(.app _ _) =>
    match e.getAppFnArgs with
    | (``Region.decode?, #[r, fuel]) => some (r, fuel)
    | (``Region.decode, #[r, fuel]) => some (r, fuel)
    | _ => e.getAppArgs.findSome? findRegionDecode
  | _ => none

/-- Close the goal by kernel reduction, or report why the region did not
decode. -/
meta def decodeRegionCore : TacticM Unit := do
  let ty ← (← getMainGoal).getType
  try
    withOptions (fun o => o.set `maxRecDepth (100000 : Nat)) do
      evalTactic (← `(tactic| first | rfl | decide))
  catch err =>
    let some (r, fuel) := findRegionDecode ty |
      throwError "decode_region: the goal mentions no `Region.decode?` on concrete data"
    let reduced ← withOptions (fun o => o.set `maxRecDepth (100000 : Nat))
      (reduce (← mkAppM ``Region.decode #[r, fuel]))
    match reduced.getAppFnArgs with
    | (``Except.error, #[_, _, e]) =>
      match (← reduce e).getAppFnArgs with
      | (``DecodeError.undecodable, #[addr]) =>
        throwError "decode_region: no instruction of the model decodes at address{indentExpr addr}"
      | (``DecodeError.outOfFuel, _) =>
        throwError "decode_region: the fuel ran out before the region's bytes did"
      | _ => throwError "decode_region: the region did not decode:{indentExpr e}"
    | _ => throw err

/-- Close a goal about `Region.decode?` on concrete bytes by kernel reduction,
reporting the address that failed to decode, or exhausted fuel, when it does
not. -/
scoped syntax "decode_region" : tactic

elab_rules : tactic
  | `(tactic| decode_region) => decodeRegionCore

end Silmaril.X86.Decompile
