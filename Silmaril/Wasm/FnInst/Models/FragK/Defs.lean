module

public import Silmaril.Wasm.FnInst.Models.Frag.Defs

/-!
# The fragment with a choice of semantics (models (b))

A second semantics of the fragment's syntax (`Frag.syn`): `semT` is `Frag.sem` except that
`add` **traps on unsigned overflow** (a checked-arithmetic engine, standing for a semantics that
differs from Wasm's wrapping `i32.add`). `sems : Bool → FnSem syn` is the family
(`true`: Wasm's wrapping semantics, `false`: the checked one); `kInst sems` is the institution of
bodies plus a choice of semantics.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models.FragK

open Silmaril.Wasm.FnInst.Models.Frag

/-- Checked addition: traps when the unsigned sum does not fit. -/
def addT (x y : Val) : St → Set Res :=
  if x.toNat + y.toNat < 2 ^ 32 then ret (x + y) else fun s => {(none, s)}

/-- Evaluation with checked addition. -/
def evalT {n : ℕ} (env : Fin n → Den) (args : List Val) : Frag.Expr n → St → Set Res
  | .const c => ret c
  | .param k => ret (args.getD k 0)
  | .add a b => bind (evalT env args a) fun x => bind (evalT env args b) fun y => addT x y
  | .ext8 a => bind (evalT env args a) fun x => ret ((x.truncate 8).signExtend 32)
  | .gget => fun s => {(some s, s)}
  | .gset a => bind (evalT env args a) fun x _ => {(some x, x)}
  | .call f a => bind (evalT env args a) fun x => env f [x]
  | .seq a b => bind (evalT env args a) fun _ => evalT env args b
  | .trap => fun s => {(none, s)}

theorem evalT_rename {n m : ℕ} (ρ : Fin n → Fin m) (env : Fin m → Den) (args : List Val)
    (e : Frag.Expr n) : evalT env args (e.rename ρ) = evalT (env ∘ ρ) args e := by
  induction e <;> simp_all [Expr.rename, evalT]

/-- The checked semantics. -/
abbrev semT : FnSem syn where
  Den := Den
  eval env b := fun args => evalT env args b
  eval_rename ρ env b := funext fun args => evalT_rename ρ env args b

/-- The family: `true` is Wasm's wrapping semantics, `false` the checked one. -/
def sems : Bool → FnSem syn
  | true => sem
  | false => semT

end Silmaril.Wasm.FnInst.Models.FragK
