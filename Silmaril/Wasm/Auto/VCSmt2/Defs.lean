module

public import Silmaril.Wasm.Auto.VCGen2.Defs
public import Silmaril.Wasm.Auto.VCSmt.Defs

/-!
# SMT-LIB queries for the conditions of the VC generator with SSA names and memory

`smtQuery φ` prints one verification condition of `Silmaril.Wasm.Auto.VCGen2` (`Fm`) as an
SMT-LIB script (`QF_AUFBV`) whose `check-sat` is `unsat` when the condition is valid. It extends
the first printer (`Silmaril.Wasm.Auto.VCGen.smtScript`, whose helpers it reuses: comparisons and
`eqz` used as values are `ite` terms, shifts are taken modulo the width, `wrap` is `extract`)
with memory:

* memory variable `ρ.mem k` is the pair of an array `M<k>` from 64-bit addresses to bytes and a
  64-bit size `Z<k>` (the placeholder `MR.cur` is `Mcur`/`Zcur`);
* a load `load t n sx m a off` is the little-endian concatenation of the `n` bytes at
  `a + off` (`a` zero-extended to 64 bits, so the address does not wrap), extended to the type's
  width by `sx`, and `0` when `a + off + n` exceeds the size (as `Memory.load … |>.getD 0`);
* `inb m a n` is `a + n ≤ Z`; `st k m n a off v` says `Z<k> = Z_m` and `M<k>` is `M_m` with the
  `n` low bytes of `v` written at `a + off` when they fit, `M_m` otherwise (as `stW`);
* user predicates `pr k m as` and memory functions `mfn k m a b` are uninterpreted
  (`pr<k>_<arity>`, `mf<k>`), applied to the memory's array and size;
* `meq m₁ m₂` is equality of the arrays and of the sizes.

**Faithfulness.** A Lean environment gives an SMT model by padding every memory with zero bytes
beyond its size; loads and bounds read only below the size and stores keep the padding, so every
condition has the same truth value in both. Hence `unsat` means the condition holds in every
environment (up to the correctness of this unverified printer and of z3). The converse can fail:
a model may put other bytes beyond a size, which only uninterpreted symbols and `meq` can
observe. `smtUsesFns` flags such queries (specification functions, counting operators, user
predicates, memory functions, memory equality): their models may be spurious.

The printer is not verified: it is an oracle (for `tools/wasm-vc reflect`, `generator = 2`);
the conditions are proved in Lean.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.VCGen2

open Silmaril.Wasm
open Silmaril.Wasm.Auto.VCGen (smtWidth smtSort smtLit smtVar smtRel smtBool32 smtCount)

/-- The SMT names of a memory: its array and its size. -/
def MR.smt : MR → String × String
  | .v k => (s!"M{k}", s!"Z{k}")
  | .cur => ("Mcur", "Zcur")

/-- A 64-bit SMT-LIB literal. -/
def smtLit64 (n : Nat) : String := s!"(_ bv{n % 2 ^ 64} 64)"

/-- The address `a + off` of an `i32` term `a`, without wrapping (64 bits). -/
def smtAddr (a : String) (off : Nat) : String := s!"(bvadd ((_ zero_extend 32) {a}) {smtLit64 off})"

/-- The byte at address `x + i` of the array `M`. -/
def smtByte (M x : String) (i : Nat) : String := s!"(select {M} (bvadd {x} {smtLit64 i}))"

/-- The little-endian concatenation of the `n` bytes at `x` (`n ≥ 1`). -/
def smtBytes (M x : String) (n : Nat) : String :=
  match n with
  | 0 => "(_ bv0 8)"
  | 1 => smtByte M x 0
  | n + 1 => s!"(concat {smtByte M x n} {smtBytes M x n})"

/-- A load of `n` bytes at `x` of the memory `(M, Z)`, extended to `w` bits by `sx`, `0` out of
bounds. -/
def smtLoad (w n : Nat) (sx : Signedness) (M Z x : String) : String :=
  let v := smtBytes M x n
  let e := if w ≤ 8 * n then v else
    match sx with
    | .unsigned => s!"((_ zero_extend {w - 8 * n}) {v})"
    | .signed => s!"((_ sign_extend {w - 8 * n}) {v})"
  s!"(ite (bvule (bvadd {x} {smtLit64 n}) {Z}) {e} (_ bv0 {w}))"

/-- The array `M` with the `n` low bytes of the `w`-bit value `v` written at `x`. -/
def smtStoreBytes (M x v : String) : Nat → String
  | 0 => M
  | i + 1 => s!"(store {smtStoreBytes M x v i} (bvadd {x} {smtLit64 i}) ((_ extract {8 * i + 7} {8 * i}) {v}))"

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
  | t, .load _ n sx m a off =>
    smtLoad (smtWidth t) n sx (m.smt).1 (m.smt).2 (smtAddr a.smt off)
  | _, .mfn k m a b => s!"(mf{k} {(m.smt).1} {(m.smt).2} {a.smt} {b.smt})"

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
  | .inb m a n => s!"(bvule {smtAddr a.smt n} {(m.smt).2})"
  | .pr k m as =>
    s!"(pr{k}_{as.length} {(m.smt).1} {(m.smt).2}{String.join (as.map fun a => " " ++ a.smt)})"
  | .meq m₁ m₂ => s!"(and (= {(m₁.smt).1} {(m₂.smt).1}) (= {(m₁.smt).2} {(m₂.smt).2}))"
  | .st k m n a off v =>
    let x := smtAddr a.smt off
    let (M, Z) := m.smt
    s!"(and (= Z{k} {Z}) (= M{k} (ite (bvule (bvadd {x} {smtLit64 n}) {Z}) {smtStoreBytes M x v.smt n} {M})))"

/-- The declarations of a memory. -/
def MR.decls (m : MR) : List String :=
  let (M, Z) := m.smt
  [s!"(declare-const {M} (Array (_ BitVec 64) (_ BitVec 8)))", s!"(declare-const {Z} (_ BitVec 64))"]

/-- Combine two declaration lists. -/
def cmb (a b : List String × Bool) : List String × Bool := (a.1 ++ b.1, a.2 || b.2)

/-- The declarations a term needs, and whether it uses uninterpreted symbols. -/
def Tm.decls : {t : IntType} → Tm t → List String × Bool
  | _, .var t i => ([s!"(declare-const {smtVar t i} {smtSort t})"], false)
  | _, .loc t j => ([s!"(declare-const loc{smtWidth t}_{j} {smtSort t})"], false)
  | _, .lit _ _ => ([], false)
  | t, .un op a =>
    let d := a.decls
    let c : List String × Bool := match op with
      | .clz => ([s!"(declare-fun {smtCount 0}{smtWidth t} ({smtSort t}) {smtSort t})"], true)
      | .ctz => ([s!"(declare-fun {smtCount 1}{smtWidth t} ({smtSort t}) {smtSort t})"], true)
      | .popcnt => ([s!"(declare-fun {smtCount 2}{smtWidth t} ({smtSort t}) {smtSort t})"], true)
      | _ => ([], false)
    (c.1 ++ d.1, c.2 || d.2)
  | _, .bin _ a b => cmb a.decls b.decls
  | _, .rel _ a b => cmb a.decls b.decls
  | _, .eqz a => a.decls
  | _, .ite c a b => cmb c.decls (cmb a.decls b.decls)
  | _, .wrap a => a.decls
  | _, .ext _ a => a.decls
  | t, .fn k a =>
    cmb ([s!"(declare-fun f{smtWidth t}_{k} ({smtSort t}) {smtSort t})"], true) a.decls
  | t, .fn2 k a b =>
    cmb ([s!"(declare-fun g{smtWidth t}_{k} ({smtSort t} {smtSort t}) {smtSort t})"], true)
      (cmb a.decls b.decls)
  | _, .load _ _ _ m a _ => cmb (m.decls, false) a.decls
  | _, .mfn k m a b =>
    cmb ([s!"(declare-fun mf{k} ((Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))"] ++ m.decls, true)
      (cmb a.decls b.decls)

/-- The declarations a formula needs, and whether it uses uninterpreted symbols or memory
equality. -/
def Fm.decls : Fm → List String × Bool
  | .tt => ([], false)
  | .ff => ([], false)
  | .rel _ a b => cmb a.decls b.decls
  | .nz a => a.decls
  | .not p => p.decls
  | .and p q => cmb p.decls q.decls
  | .or p q => cmb p.decls q.decls
  | .imp p q => cmb p.decls q.decls
  | .inb m a _ => cmb (m.decls, false) a.decls
  | .pr k m as =>
    let args := String.join (as.map fun _ => " (_ BitVec 32)")
    cmb ([s!"(declare-fun pr{k}_{as.length} ((Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64){args}) Bool)"] ++ m.decls, true)
      (as.foldr (fun a acc => cmb a.decls acc) ([], false))
  | .meq m₁ m₂ => (m₁.decls ++ m₂.decls, true)
  | .st k m _ a _ v => cmb ((MR.v k).decls ++ m.decls, false) (cmb a.decls v.decls)

/-- Whether a condition uses uninterpreted symbols or memory equality, so that a model may be
spurious. -/
def smtUsesFns (φ : Fm) : Bool := φ.decls.2

/-- The declarations first (constants before functions, as SMT-LIB needs no order). -/
def smtDecls (φ : Fm) : List String := φ.decls.1.eraseDups

/-- The SMT-LIB script of one condition: `unsat` means it is valid. -/
def smtQuery (φ : Fm) : String :=
  String.intercalate "\n" (["(set-logic QF_AUFBV)"] ++ smtDecls φ ++
    [s!"(assert (not {φ.smt}))", "(check-sat)", "(get-model)"])

/-- All conditions, separated by `;; vc <k> <uf|bv>` lines (for `tools/wasm-vc reflect`). -/
def smtScript (l : List Fm) : String :=
  String.intercalate "\n" ((l.zipIdx).map fun (φ, k) =>
    s!";; vc {k} {if smtUsesFns φ then "uf" else "bv"}\n{smtQuery φ}")

end Silmaril.Wasm.Auto.VCGen2
