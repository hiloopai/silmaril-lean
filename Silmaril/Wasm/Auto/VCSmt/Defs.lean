module

public import Silmaril.Wasm.Auto.VCGen.Defs

/-!
# SMT-LIB queries for the conditions of the reflective VC generator

`smtQuery φ` prints one verification condition of `Silmaril.Wasm.Auto.VCGen` (`Fm`) as an SMT-LIB
script over bit-vectors (`QF_UFBV`) whose `check-sat` is `unsat` exactly when the condition is
valid for every value of its variables and every interpretation of its specification
functions. The printer follows `Tm.den`/`Fm.den` construct by construct:

* `i32`/`i64` values are `(_ BitVec 32)`/`(_ BitVec 64)`; variable `var .i32 i` is `v<i>`,
  `var .i64 i` is `w<i>` (the names `vcgen_vars` gives in Lean);
* comparisons and `eqz` used as values are `(ite … #x00000001 #x00000000)`, never a free atom
  (the encoding gap behind the spurious counterexamples, `docs/projects/wasm-binaryen-tooling.md`);
* shifts take the count modulo the width (`bvurem`), as Wasm does; `wrap` is `extract`, the
  extensions are `sign_extend`/`zero_extend`; signed comparisons are `bvslt`/`bvsle`;
* specification functions `fn k` are uninterpreted functions `f32_<k>`/`f64_<k>`
  (`g32_<k>`/`g64_<k>` for binary ones), so a model of a query that uses them may be spurious;
  `smtUsesFns` says whether one does.

The printer is not verified: it is an oracle for finding counterexamples quickly and for
`tools/wasm-vc reflect`; the conditions themselves are proved in Lean.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.VCGen

open Silmaril.Wasm

def smtWidth : IntType → Nat
  | .i32 => 32
  | .i64 => 64

def smtSort (t : IntType) : String := s!"(_ BitVec {smtWidth t})"

def smtLit (t : IntType) (n : Nat) : String := s!"(_ bv{n % 2 ^ smtWidth t} {smtWidth t})"

def smtVar : IntType → Nat → String
  | .i32, i => s!"v{i}"
  | .i64, i => s!"w{i}"

def smtRelOp : IntRelOp → String × Bool
  | .eq => ("=", false)
  | .ne => ("distinct", false)
  | .lt .unsigned => ("bvult", false)
  | .gt .unsigned => ("bvult", true)
  | .le .unsigned => ("bvule", false)
  | .ge .unsigned => ("bvule", true)
  | .lt .signed => ("bvslt", false)
  | .gt .signed => ("bvslt", true)
  | .le .signed => ("bvsle", false)
  | .ge .signed => ("bvsle", true)

/-- A comparison as an SMT-LIB Boolean. -/
def smtRel (op : IntRelOp) (a b : String) : String :=
  let (o, swap) := smtRelOp op
  if swap then s!"({o} {b} {a})" else s!"({o} {a} {b})"

/-- An `i32` truth value. -/
def smtBool32 (c : String) : String := s!"(ite {c} (_ bv1 32) (_ bv0 32))"

/-- A term (an SMT-LIB bit-vector expression). -/
def Tm.smt : {t : IntType} → Tm t → String
  | _, .var t i => smtVar t i
  | _, .loc t j => s!"loc{smtWidth t}_{j}"
  | _, .lit t n => smtLit t n
  | t, .un op a =>
    let x := a.smt
    match op with
    | .extend sz => s!"((_ sign_extend {smtWidth t - sz.width}) ((_ extract {sz.width - 1} 0) {x}))"
    | .clz => s!"(clz{smtWidth t} {x})"
    | .ctz => s!"(ctz{smtWidth t} {x})"
    | .popcnt => s!"(popcnt{smtWidth t} {x})"
  | t, .bin op a b =>
    let x := a.smt
    let y := b.smt
    let k := s!"(bvurem {y} {smtLit t (smtWidth t)})"
    match op with
    | .add => s!"(bvadd {x} {y})"
    | .sub => s!"(bvsub {x} {y})"
    | .mul => s!"(bvmul {x} {y})"
    | .div .unsigned => s!"(bvudiv {x} {y})"
    | .div .signed => s!"(bvsdiv {x} {y})"
    | .rem .unsigned => s!"(bvurem {x} {y})"
    | .rem .signed => s!"(bvsrem {x} {y})"
    | .and => s!"(bvand {x} {y})"
    | .or => s!"(bvor {x} {y})"
    | .xor => s!"(bvxor {x} {y})"
    | .shl => s!"(bvshl {x} {k})"
    | .shr .unsigned => s!"(bvlshr {x} {k})"
    | .shr .signed => s!"(bvashr {x} {k})"
    | .rotl => s!"(bvor (bvshl {x} {k}) (bvlshr {x} (bvsub {smtLit t (smtWidth t)} {k})))"
    | .rotr => s!"(bvor (bvlshr {x} {k}) (bvshl {x} (bvsub {smtLit t (smtWidth t)} {k})))"
  | _, .rel op a b => smtBool32 (smtRel op a.smt b.smt)
  | _, .eqz (t := t) a => smtBool32 s!"(= {a.smt} {smtLit t 0})"
  | _, .ite c a b => s!"(ite (distinct {c.smt} (_ bv0 32)) {a.smt} {b.smt})"
  | _, .wrap a => s!"((_ extract 31 0) {a.smt})"
  | _, .ext .signed a => s!"((_ sign_extend 32) {a.smt})"
  | _, .ext .unsigned a => s!"((_ zero_extend 32) {a.smt})"
  | t, .fn k a => s!"(f{smtWidth t}_{k} {a.smt})"
  | t, .fn2 k a b => s!"(g{smtWidth t}_{k} {a.smt} {b.smt})"

/-- A formula (an SMT-LIB Boolean). -/
def Fm.smt : Fm → String
  | .tt => "true"
  | .ff => "false"
  | .rel op a b => smtRel op a.smt b.smt
  | .nz a => s!"(distinct {a.smt} (_ bv0 32))"
  | .not p => s!"(not {p.smt})"
  | .and p q => s!"(and {p.smt} {q.smt})"
  | .or p q => s!"(or {p.smt} {q.smt})"
  | .imp p q => s!"(=> {p.smt} {q.smt})"

/-- The variables and function symbols of a term: `(kind, type, index)`, kind `0` a variable,
`1` a unary, `2` a binary function, `3` a counting operator. -/
def Tm.syms : {t : IntType} → Tm t → List (Nat × IntType × Nat)
  | _, .var t i => [(0, t, i)]
  | _, .loc _ _ => []
  | _, .lit _ _ => []
  | t, .un op a => (match op with
      | .clz => [(3, t, 0)] | .ctz => [(3, t, 1)] | .popcnt => [(3, t, 2)] | _ => []) ++ a.syms
  | _, .bin _ a b => a.syms ++ b.syms
  | _, .rel _ a b => a.syms ++ b.syms
  | _, .eqz a => a.syms
  | _, .ite c a b => c.syms ++ a.syms ++ b.syms
  | _, .wrap a => a.syms
  | _, .ext _ a => a.syms
  | t, .fn k a => (1, t, k) :: a.syms
  | t, .fn2 k a b => (2, t, k) :: a.syms ++ b.syms

def Fm.syms : Fm → List (Nat × IntType × Nat)
  | .tt => []
  | .ff => []
  | .rel _ a b => a.syms ++ b.syms
  | .nz a => a.syms
  | .not p => p.syms
  | .and p q => p.syms ++ q.syms
  | .or p q => p.syms ++ q.syms
  | .imp p q => p.syms ++ q.syms

def smtCount : Nat → String
  | 0 => "clz"
  | 1 => "ctz"
  | _ => "popcnt"

def smtDecl : Nat × IntType × Nat → String
  | (0, t, i) => s!"(declare-const {smtVar t i} {smtSort t})"
  | (1, t, k) => s!"(declare-fun f{smtWidth t}_{k} ({smtSort t}) {smtSort t})"
  | (2, t, k) => s!"(declare-fun g{smtWidth t}_{k} ({smtSort t} {smtSort t}) {smtSort t})"
  | (_, t, k) => s!"(declare-fun {smtCount k}{smtWidth t} ({smtSort t}) {smtSort t})"

/-- Whether a condition uses uninterpreted symbols (specification functions or counting
operators), so that a model may be spurious. -/
def smtUsesFns (φ : Fm) : Bool := φ.syms.any (·.1 != 0)

/-- The SMT-LIB script of one condition: `unsat` iff it is valid. -/
def smtQuery (φ : Fm) : String :=
  let ds := φ.syms.eraseDups.map smtDecl
  String.intercalate "\n" (["(set-logic QF_UFBV)"] ++ ds ++
    [s!"(assert (not {φ.smt}))", "(check-sat)", "(get-model)"])

/-- All conditions, separated by `;; vc <k> <uses-fns>` lines (for `tools/wasm-vc reflect`). -/
def smtScript (l : List Fm) : String :=
  String.intercalate "\n" ((l.zipIdx).map fun (φ, k) =>
    s!";; vc {k} {if smtUsesFns φ then "uf" else "bv"}\n{smtQuery φ}")

end Silmaril.Wasm.Auto.VCGen
