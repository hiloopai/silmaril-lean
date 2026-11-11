module

public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Logic.Hoare.Defs

/-!
# A reflective verification-condition generator for Core 3.0 functions

`genFunc S fn fuel` computes, **as data**, the list of verification conditions (VCs) of the
function `fn` (silmaril-lean `Func`, Core 3.0) against the annotated specification `S`: a
precondition and a postcondition over the parameters and results, and one invariant per loop.
A VC is a formula `Fm` over symbolic bit-vector terms `Tm`; its meaning `Fm.den` is an ordinary
proposition about `BitVec 32`/`BitVec 64` values (`+`, `*`, shifts, `toNat`, `toInt`, `if`), so
the conditions are discharged by `omega`, `bv_omega`, `simp` and `decide` without stepping the
semantics inside a tactic. `Silmaril.Wasm.Auto.VCGen.Thms.genFunc_sound` (one theorem, proved
once) turns `AllValid F (genFunc S fn fuel)` into an every-run function specification
(`Silmaril.Wasm.Logic.Hoare.FSpecValid`: partial correctness and safety at every profile and for
every host relation).

The generator is a symbolic executor:

* the state `SSt` holds symbolic locals, a symbolic operand stack (top first) and the path
  condition (newest first);
* integer constants, `local.get`/`set`/`tee`, `drop`, `nop`, integer unary, binary, test and
  comparison operators, `i32.wrap_i64` and `i64.extend_i32_{s,u}` push terms (division and
  remainder add their trap-freedom side conditions);
* `select` pushes an `ite` term (no path split);
* `block`, `if` (with a block type of no parameters entered with an otherwise empty stack),
  `br`, `br_if` and `return` follow the labels; a branch continues with the code after its
  block, so code after a join point is visited once per incoming path;
* `loop` (no parameters, otherwise empty stack): the `k`-th loop in pre-order uses invariant
  `S.inv[k]` over the parameters (`var t i`) and the locals (`loc t j`); the generator asks for
  it on entry and on every branch back, and verifies the body once from fresh locals
  (`var t (p + j)`) assuming it.

Anything else gives an unprovable condition (`pc → False`): the generator is sound, not
complete. Memory, globals and calls are not supported yet. The loop invariants are numbered by
`nloops` and the recursion is bounded by `fuel` (the generator gives `False` when it runs out),
so everything reduces by kernel evaluation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.VCGen

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC (Ctl ctl)

/-! ## Symbolic terms and formulas -/

/-- Symbolic integer terms of type `t`. `var t i` is a variable of the environment (parameters
`i < p`, then fresh loop variables); `loc t j` is a placeholder for the `j`-th local (in an
invariant) or result (in a postcondition), replaced by `Tm.subst`. -/
inductive Tm : IntType → Type where
  | var (t : IntType) (i : Nat) : Tm t
  | loc (t : IntType) (j : Nat) : Tm t
  | lit (t : IntType) (n : Nat) : Tm t
  | un {t : IntType} (op : IntUnOp) (a : Tm t) : Tm t
  | bin {t : IntType} (op : IntBinOp) (a b : Tm t) : Tm t
  /-- A comparison as an `i32` (`1` or `0`). -/
  | rel {t : IntType} (op : IntRelOp) (a b : Tm t) : Tm .i32
  | eqz {t : IntType} (a : Tm t) : Tm .i32
  /-- `select`: `a` if `c ≠ 0`, else `b`. -/
  | ite {t : IntType} (c : Tm .i32) (a b : Tm t) : Tm t
  | wrap (a : Tm .i64) : Tm .i32
  | ext (sx : Signedness) (a : Tm .i32) : Tm .i64
  /-- A specification function (`Fns.app1`), e.g. a reference implementation. -/
  | fn {t : IntType} (k : Nat) (a : Tm t) : Tm t
  /-- A binary specification function (`Fns.app2`). -/
  | fn2 {t : IntType} (k : Nat) (a b : Tm t) : Tm t

/-- Verification-condition formulas. -/
inductive Fm where
  | tt
  | ff
  | rel {t : IntType} (op : IntRelOp) (a b : Tm t)
  | nz (a : Tm .i32)
  | not (p : Fm)
  | and (p q : Fm)
  | or (p q : Fm)
  | imp (p q : Fm)

/-- An environment: values of the `i32` and of the `i64` variables. -/
structure Env where
  e32 : Nat → BitVec 32
  e64 : Nat → BitVec 64

/-- The value of variable `i` of type `t`. -/
def Env.get (ρ : Env) : (t : IntType) → Nat → BitVec t.width
  | .i32, i => ρ.e32 i
  | .i64, i => ρ.e64 i

/-- The specification functions a specification may use, numbered, per type. -/
structure Fns where
  f32 : Nat → BitVec 32 → BitVec 32 := fun _ x => x
  f64 : Nat → BitVec 64 → BitVec 64 := fun _ x => x
  g32 : Nat → BitVec 32 → BitVec 32 → BitVec 32 := fun _ x _ => x
  g64 : Nat → BitVec 64 → BitVec 64 → BitVec 64 := fun _ x _ => x

/-- Unary specification function `k` at type `t`. -/
def Fns.app1 (F : Fns) : (t : IntType) → Nat → BitVec t.width → BitVec t.width
  | .i32 => F.f32
  | .i64 => F.f64

/-- Binary specification function `k` at type `t`. -/
def Fns.app2 (F : Fns) : (t : IntType) → Nat → BitVec t.width → BitVec t.width → BitVec t.width
  | .i32 => F.g32
  | .i64 => F.g64

/-! The meaning of terms is stated at the concrete widths `32` and `64` (the `…W` functions,
selected by the `…T` functions), so that the unfolded conditions mention `BitVec 32` and
`BitVec 64` only, never `BitVec IntType.i32.width`. -/

/-- Integer binary operators as total functions (`intBinOp` where it does not trap). -/
def binW (n : Nat) : IntBinOp → BitVec n → BitVec n → BitVec n
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div .unsigned, x, y => x / y
  | .div .signed, x, y => x.sdiv y
  | .rem .unsigned, x, y => x % y
  | .rem .signed, x, y => x.srem y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => x <<< (y.toNat % n)
  | .shr .unsigned, x, y => x >>> (y.toNat % n)
  | .shr .signed, x, y => x.sshiftRight (y.toNat % n)
  | .rotl, x, y => x.rotateLeft y.toNat
  | .rotr, x, y => x.rotateRight y.toNat

/-- Integer comparisons as propositions (unsigned on `toNat`, signed on `toInt`). -/
def relW (n : Nat) : IntRelOp → BitVec n → BitVec n → Prop
  | .eq, x, y => x = y
  | .ne, x, y => x ≠ y
  | .lt .unsigned, x, y => x.toNat < y.toNat
  | .gt .unsigned, x, y => y.toNat < x.toNat
  | .le .unsigned, x, y => x.toNat ≤ y.toNat
  | .ge .unsigned, x, y => y.toNat ≤ x.toNat
  | .lt .signed, x, y => x.toInt < y.toInt
  | .gt .signed, x, y => y.toInt < x.toInt
  | .le .signed, x, y => x.toInt ≤ y.toInt
  | .ge .signed, x, y => y.toInt ≤ x.toInt

/-- Integer comparisons as Booleans (no `decide`, so no instance carries a term). -/
def relB (n : Nat) : IntRelOp → BitVec n → BitVec n → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lt .unsigned, x, y => x.ult y
  | .gt .unsigned, x, y => y.ult x
  | .le .unsigned, x, y => x.ule y
  | .ge .unsigned, x, y => y.ule x
  | .lt .signed, x, y => x.slt y
  | .gt .signed, x, y => y.slt x
  | .le .signed, x, y => x.sle y
  | .ge .signed, x, y => y.sle x

/-- Integer unary operators: sign extension at the concrete width, the others as `intUnOp`. -/
def unW (n : Nat) : IntUnOp → BitVec n → BitVec n
  | .extend sz, x => (x.setWidth sz.width).signExtend n
  | .clz, x => x.clz
  | .ctz, x => x.ctz
  | .popcnt, x => x.cpop

def litT : (t : IntType) → Nat → BitVec t.width
  | .i32, n => BitVec.ofNat 32 n
  | .i64, n => BitVec.ofNat 64 n

def unT : (t : IntType) → IntUnOp → BitVec t.width → BitVec t.width
  | .i32 => unW 32
  | .i64 => unW 64

def binT : (t : IntType) → IntBinOp → BitVec t.width → BitVec t.width → BitVec t.width
  | .i32 => binW 32
  | .i64 => binW 64

def relP : (t : IntType) → IntRelOp → BitVec t.width → BitVec t.width → Prop
  | .i32 => relW 32
  | .i64 => relW 64

/-- A comparison as an `i32` (`1` or `0`). -/
def relV : (t : IntType) → IntRelOp → BitVec t.width → BitVec t.width → BitVec 32
  | .i32, op, x, y => bool32 (relB 32 op x y)
  | .i64, op, x, y => bool32 (relB 64 op x y)

/-- `eqz` as an `i32`. -/
def eqzV : (t : IntType) → BitVec t.width → BitVec 32
  | .i32, x => bool32 ((x : BitVec 32) == 0)
  | .i64, x => bool32 ((x : BitVec 64) == 0)

/-- An `i32` used as a condition. -/
def nz32 (x : BitVec 32) : Bool := x != 0

/-- `select` at the concrete width. -/
def iteT : (t : IntType) → Bool → BitVec t.width → BitVec t.width → BitVec t.width
  | .i32, c, a, b => @cond (BitVec 32) c a b
  | .i64, c, a, b => @cond (BitVec 64) c a b

/-- `i32.wrap_i64`. -/
def wrapW (x : BitVec 64) : BitVec 32 := x.setWidth 32

/-- `i64.extend_i32_s`. -/
def extSW (x : BitVec 32) : BitVec 64 := x.signExtend 64

/-- `i64.extend_i32_u`. -/
def extUW (x : BitVec 32) : BitVec 64 := x.setWidth 64

/-- The meaning of a term: `ρ` for variables, `ξ` for placeholders. -/
def Tm.den (F : Fns) (ρ ξ : Env) : {t : IntType} → Tm t → BitVec t.width
  | t, .var _ i => ρ.get t i
  | t, .loc _ j => ξ.get t j
  | t, .lit _ n => litT t n
  | t, .un op a => unT t op (a.den F ρ ξ)
  | t, .bin op a b => binT t op (a.den F ρ ξ) (b.den F ρ ξ)
  | _, .rel (t := t) op a b => relV t op (a.den F ρ ξ) (b.den F ρ ξ)
  | _, .eqz (t := t) a => eqzV t (a.den F ρ ξ)
  | t, .ite c a b => iteT t (nz32 (c.den F ρ ξ)) (a.den F ρ ξ) (b.den F ρ ξ)
  | _, .wrap a => wrapW (a.den F ρ ξ)
  | _, .ext .signed a => extSW (a.den F ρ ξ)
  | _, .ext .unsigned a => extUW (a.den F ρ ξ)
  | t, .fn k a => F.app1 t k (a.den F ρ ξ)
  | t, .fn2 k a b => F.app2 t k (a.den F ρ ξ) (b.den F ρ ξ)

/-- The meaning of a formula. -/
def Fm.den (F : Fns) (ρ ξ : Env) : Fm → Prop
  | .tt => True
  | .ff => False
  | .rel (t := t) op a b => relP t op (a.den F ρ ξ) (b.den F ρ ξ)
  | .nz a => nz32 (a.den F ρ ξ) = true
  | .not p => ¬ p.den F ρ ξ
  | .and p q => p.den F ρ ξ ∧ q.den F ρ ξ
  | .or p q => p.den F ρ ξ ∨ q.den F ρ ξ
  | .imp p q => p.den F ρ ξ → q.den F ρ ξ

/-- A closed condition: true in every environment. -/
def Valid (F : Fns) (φ : Fm) : Prop := ∀ ρ : Env, φ.den F ρ ρ

/-- Every condition of a list is valid. -/
def AllValid (F : Fns) : List Fm → Prop
  | [] => True
  | φ :: r => Valid F φ ∧ AllValid F r

/-- Conjunction of a list (no trailing `True`). -/
def Fm.conj : List Fm → Fm
  | [] => .tt
  | [p] => p
  | p :: ps => .and p (Fm.conj ps)

/-! ## Symbolic values -/

/-- A symbolic value of either integer type. -/
inductive SV where
  | i32 (a : Tm .i32)
  | i64 (a : Tm .i64)

def SV.ty : SV → IntType
  | .i32 _ => .i32
  | .i64 _ => .i64

def SV.of : (t : IntType) → Tm t → SV
  | .i32, a => .i32 a
  | .i64, a => .i64 a

def SV.as : (t : IntType) → SV → Option (Tm t)
  | .i32, .i32 a => some a
  | .i64, .i64 a => some a
  | _, _ => none

def SV.den (F : Fns) (ρ ξ : Env) : SV → Val
  | .i32 a => .num ⟨.int .i32, a.den F ρ ξ⟩
  | .i64 a => .num ⟨.int .i64, a.den F ρ ξ⟩

/-! ## Substitution and scope -/

/-- Replace each placeholder `loc t j` by the `j`-th value of `ls` (`0` if missing or of
another type). -/
def Tm.subst (ls : List SV) : {t : IntType} → Tm t → Tm t
  | _, .var t i => .var t i
  | _, .loc t j => match ls[j]? with
    | some v => (v.as t).getD (.lit t 0)
    | none => .lit t 0
  | _, .lit t n => .lit t n
  | _, .un op a => .un op (a.subst ls)
  | _, .bin op a b => .bin op (a.subst ls) (b.subst ls)
  | _, .rel op a b => .rel op (a.subst ls) (b.subst ls)
  | _, .eqz a => .eqz (a.subst ls)
  | _, .ite c a b => .ite (c.subst ls) (a.subst ls) (b.subst ls)
  | _, .wrap a => .wrap (a.subst ls)
  | _, .ext sx a => .ext sx (a.subst ls)
  | _, .fn k a => .fn k (a.subst ls)
  | _, .fn2 k a b => .fn2 k (a.subst ls) (b.subst ls)

def Fm.subst (ls : List SV) : Fm → Fm
  | .tt => .tt
  | .ff => .ff
  | .rel op a b => .rel op (a.subst ls) (b.subst ls)
  | .nz a => .nz (a.subst ls)
  | .not p => .not (p.subst ls)
  | .and p q => .and (p.subst ls) (q.subst ls)
  | .or p q => .or (p.subst ls) (q.subst ls)
  | .imp p q => .imp (p.subst ls) (q.subst ls)

/-- Every variable `var t i` of the term is parameter `i`, of type `t`. -/
def Tm.scoped (p : List IntType) : {t : IntType} → Tm t → Bool
  | _, .var t i => decide (p[i]? = some t)
  | _, .loc _ _ => true
  | _, .lit _ _ => true
  | _, .un _ a => a.scoped p
  | _, .bin _ a b => a.scoped p && b.scoped p
  | _, .rel _ a b => a.scoped p && b.scoped p
  | _, .eqz a => a.scoped p
  | _, .ite c a b => c.scoped p && a.scoped p && b.scoped p
  | _, .wrap a => a.scoped p
  | _, .ext _ a => a.scoped p
  | _, .fn _ a => a.scoped p
  | _, .fn2 _ a b => a.scoped p && b.scoped p

def Fm.scoped (p : List IntType) : Fm → Bool
  | .tt => true
  | .ff => true
  | .rel _ a b => a.scoped p && b.scoped p
  | .nz a => a.scoped p
  | .not q => q.scoped p
  | .and q r => q.scoped p && r.scoped p
  | .or q r => q.scoped p && r.scoped p
  | .imp q r => q.scoped p && r.scoped p

/-! ## The symbolic executor -/

/-- A symbolic state: locals, the operand stack (top first) and the path condition. -/
structure SSt where
  locals : List SV
  stack : List SV
  pc : List Fm

/-- A label: a block (its arity and the continuation after it) or the loop with invariant
number `j`. -/
inductive Lbl where
  | blk (n : Nat) (k : SSt → List Fm)
  | lp (j : Nat)

/-- An annotated specification. Formulas use `var t i` for parameter `i`; the postcondition
uses `loc t j` for result `j` (bottom first) and invariant `k` uses `loc t j` for local `j`. -/
structure FnSpec where
  params : List IntType
  results : List IntType
  pre : Fm := .tt
  post : Fm
  inv : List Fm := []

/-- The condition `φ` under the path condition of `σ`. -/
def vc (σ : SSt) (φ : Fm) : Fm := .imp (Fm.conj σ.pc) φ

/-- An unprovable condition (unsupported code, ill-typed stack, out of fuel). -/
def bad (σ : SSt) : List Fm := [vc σ .ff]

/-- The path condition `c ≠ 0`, with comparisons and `eqz` unfolded. -/
def condF : Tm .i32 → Fm
  | .rel op a b => .rel op a b
  | .eqz (t := t) a => .rel .eq a (.lit t 0)
  | c => .nz c

/-- The path condition `c = 0`. -/
def ncondF : Tm .i32 → Fm
  | .rel op a b => .not (.rel op a b)
  | .eqz (t := t) a => .rel .ne a (.lit t 0)
  | c => .not (.nz c)

/-- Pop a value of type `t` (the stack is top first). -/
def pop1 (t : IntType) : List SV → Option (Tm t × List SV)
  | v :: r => (v.as t).map fun a => (a, r)
  | [] => none

/-- The side conditions of a binary operator: no division by zero, no signed overflow. -/
def safeF (t : IntType) (op : IntBinOp) (a b : Tm t) : List Fm :=
  match op with
  | .div .unsigned => [.rel .ne b (.lit t 0)]
  | .rem _ => [.rel .ne b (.lit t 0)]
  | .div .signed => [.rel .ne b (.lit t 0),
      .not (.and (.rel .eq a (.lit t (2 ^ (t.width - 1)))) (.rel .eq b (.lit t (2 ^ t.width - 1))))]
  | _ => []

/-- `select` on two values of the same type. -/
def selV (c : Tm .i32) : SV → SV → Option SV
  | .i32 a, .i32 b => some (.i32 (.ite c a b))
  | .i64 a, .i64 b => some (.i64 (.ite c a b))
  | _, _ => none

/-- One straight-line instruction: the new state and the side conditions. -/
def step1 (i : Instr) (σ : SSt) : Option (SSt × List Fm) :=
  match i with
  | .nop => some (σ, [])
  | .drop => match σ.stack with
    | _ :: st => some ({ σ with stack := st }, [])
    | [] => none
  | .intConst t c => some ({ σ with stack := SV.of t (.lit t c.toNat) :: σ.stack }, [])
  | .localGet x => σ.locals[x.toNat]?.map fun v => ({ σ with stack := v :: σ.stack }, [])
  | .localSet x => match σ.stack, σ.locals[x.toNat]? with
    | v :: st, some w =>
      if v.ty = w.ty then some ({ σ with stack := st, locals := σ.locals.set x.toNat v }, [])
      else none
    | _, _ => none
  | .localTee x => match σ.stack, σ.locals[x.toNat]? with
    | v :: _, some w =>
      if v.ty = w.ty then some ({ σ with locals := σ.locals.set x.toNat v }, []) else none
    | _, _ => none
  | .intUnOp t op => (pop1 t σ.stack).map fun (a, st) =>
      ({ σ with stack := SV.of t (.un op a) :: st }, [])
  | .intBinOp t op => match pop1 t σ.stack with
    | some (b, st) => (pop1 t st).map fun (a, st') =>
        ({ σ with stack := SV.of t (.bin op a b) :: st' }, safeF t op a b)
    | none => none
  | .intTestOp t _ => (pop1 t σ.stack).map fun (a, st) =>
      ({ σ with stack := .i32 (.eqz a) :: st }, [])
  | .intRelOp t op => match pop1 t σ.stack with
    | some (b, st) => (pop1 t st).map fun (a, st') =>
        ({ σ with stack := .i32 (.rel op a b) :: st' }, [])
    | none => none
  | .convert .wrap => (pop1 .i64 σ.stack).map fun (a, st) =>
      ({ σ with stack := .i32 (.wrap a) :: st }, [])
  | .convert (.extend sx) => (pop1 .i32 σ.stack).map fun (a, st) =>
      ({ σ with stack := .i64 (.ext sx a) :: st }, [])
  | _ => none

/-- The number of results of a block type without parameters. -/
def arity : BlockType → Option Nat
  | .empty => some 0
  | .value _ => some 1
  | .typeIdx _ => none

/-- The number of loops of an instruction list, in pre-order (bounded by `fuel`). -/
def nloops : Nat → List Instr → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, i :: r =>
    (match ctl i with
      | .block _ b => nloops n b
      | .loop _ b => nloops n b + 1
      | .if_ _ b₁ b₂ => nloops n b₁ + nloops n b₂
      | _ => 0) + nloops n r

/-- Invariant `k` at the locals `ls`. -/
def invAt (S : FnSpec) (k : Nat) (ls : List SV) : Fm := (S.inv.getD k .tt).subst ls

/-- Fresh locals of types `lt`, variables from `p` on. -/
def havocLocals (p : Nat) (lt : List IntType) : List SV :=
  lt.mapIdx fun j t => SV.of t (.var t (p + j))

/-- The state at the head of loop `k`: fresh locals satisfying the invariant. -/
def havoc (S : FnSpec) (lt : List IntType) (k : Nat) : SSt :=
  { locals := havocLocals S.params.length lt, stack := [],
    pc := [invAt S k (havocLocals S.params.length lt)] }

/-- `return` (or the end of the body): the top `n` values satisfy the postcondition. -/
def retVC (S : FnSpec) (σ : SSt) : List Fm :=
  if S.results.length ≤ σ.stack.length then
    [vc σ (S.post.subst (σ.stack.take S.results.length).reverse)]
  else bad σ

/-- The end of the body: exactly the results are on the stack. -/
def endVC (S : FnSpec) (σ : SSt) : List Fm :=
  if σ.stack.length = S.results.length then retVC S σ else bad σ

/-- A branch to label `l`. -/
def brTo (S : FnSpec) (L : List Lbl) (l : Nat) (σ : SSt) : List Fm :=
  match L[l]? with
  | some (.blk n K) => if n ≤ σ.stack.length then K { σ with stack := σ.stack.take n } else bad σ
  | some (.lp j) => [vc σ (invAt S j σ.locals)]
  | none => bad σ

/-- **The generator.** `gen S lt fuel L kont k is σ`: the conditions for running `is` from the
symbolic state `σ` with the labels `L` (innermost first) and the continuation `kont` after `is`;
the loops of `is` use the invariants `k`, `k + 1`, … in pre-order; `lt` are the types of the
locals. -/
def gen (S : FnSpec) (lt : List IntType) :
    Nat → List Lbl → (SSt → List Fm) → Nat → List Instr → SSt → List Fm
  | 0, _, _, _, _, σ => bad σ
  | _ + 1, _, kont, _, [], σ => kont σ
  | fuel + 1, L, kont, k, i :: r, σ =>
    match ctl i with
    | .block bt b =>
      match arity bt, σ.stack with
      | some n, [] =>
        gen S lt fuel (.blk n (gen S lt fuel L kont (k + nloops fuel b) r) :: L)
          (gen S lt fuel L kont (k + nloops fuel b) r) k b σ
      | _, _ => bad σ
    | .loop bt b =>
      match arity bt, σ.stack with
      | some _, [] =>
        vc σ (invAt S k σ.locals) ::
          gen S lt fuel (.lp k :: L) (gen S lt fuel L kont (k + 1 + nloops fuel b) r) (k + 1) b
            (havoc S lt k)
      | _, _ => bad σ
    | .if_ bt b₁ b₂ =>
      match arity bt, σ.stack with
      | some n, [.i32 c] =>
        gen S lt fuel (.blk n (gen S lt fuel L kont (k + nloops fuel b₁ + nloops fuel b₂) r) :: L)
            (gen S lt fuel L kont (k + nloops fuel b₁ + nloops fuel b₂) r) k b₁
            { σ with stack := [], pc := condF c :: σ.pc } ++
          gen S lt fuel
            (.blk n (gen S lt fuel L kont (k + nloops fuel b₁ + nloops fuel b₂) r) :: L)
            (gen S lt fuel L kont (k + nloops fuel b₁ + nloops fuel b₂) r) (k + nloops fuel b₁) b₂
            { σ with stack := [], pc := ncondF c :: σ.pc }
      | _, _ => bad σ
    | .br l => brTo S L l.toNat σ
    | .brIf l =>
      match σ.stack with
      | .i32 c :: st =>
        brTo S L l.toNat { σ with stack := st, pc := condF c :: σ.pc } ++
          gen S lt fuel L kont k r { σ with stack := st, pc := ncondF c :: σ.pc }
      | _ => bad σ
    | .select =>
      match σ.stack with
      | .i32 c :: v₂ :: v₁ :: st =>
        match selV c v₁ v₂ with
        | some v => gen S lt fuel L kont k r { σ with stack := v :: st }
        | none => bad σ
      | _ => bad σ
    | .ret => retVC S σ
    | .brTable .. | .call _ | .cvt _ | .trap | .plain =>
      match step1 i σ with
      | some (σ', side) => side.map (vc σ) ++ gen S lt fuel L kont k r σ'
      | none => bad σ

/-- The integer type of a declared local. -/
def intTy? : ValType → Option IntType
  | .num (.int t) => some t
  | _ => none

/-- The integer types of declared locals. -/
def intTys? (ts : List ValType) : Option (List IntType) := ts.mapM intTy?

/-- The initial state: parameters `var t i`, declared locals `0`, the precondition. -/
def initSt (S : FnSpec) (lts : List IntType) : SSt :=
  { locals := S.params.mapIdx (fun i t => SV.of t (.var t i)) ++
      lts.map (fun t => SV.of t (.lit t 0)),
    stack := [], pc := [S.pre] }

/-- The annotations only mention parameters (as variables). -/
def FnSpec.wellScoped (S : FnSpec) : Bool :=
  S.post.scoped S.params && S.inv.all (Fm.scoped S.params)

/-- **The verification conditions of a function.** -/
def genFunc (S : FnSpec) (fn : Func) (fuel : Nat) : List Fm :=
  match intTys? fn.locals with
  | some lts =>
    if S.wellScoped then
      gen S (S.params ++ lts) fuel [] (endVC S) 0 fn.body (initSt S lts)
    else [.ff]
  | none => [.ff]

/-! ## The function specification -/

/-- The arguments of the parameter environment `ρ`. -/
def argsOf (S : FnSpec) (ρ : Env) : List Val :=
  S.params.mapIdx fun i t => .num ⟨.int t, ρ.get t i⟩

/-- The placeholder environment of a list of values: `loc t j` is the `j`-th value. -/
def valEnv (vs : List Val) : Env where
  e32 j := match vs[j]? with
    | some (.num ⟨.int .i32, x⟩) => x
    | _ => 0
  e64 j := match vs[j]? with
    | some (.num ⟨.int .i64, x⟩) => x
    | _ => 0

/-- **The every-run specification** `genFunc_sound` proves for the function at address `a`
(instance `fi`): called with arguments `argsOf S ρ` satisfying the precondition, it returns
(no trap, no exception) results `res` satisfying the postcondition (with `loc t j` the `j`-th
result) and leaves the store unchanged. -/
def fspec {H : Type} (F : Fns) (S : FnSpec) (a : Nat) (fi : FuncInst H) :
    Silmaril.Wasm.Logic.Hoare.FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ ρ, args = argsOf S ρ ∧ S.pre.den F ρ ρ
  post s args s' o := s' = s ∧ ∃ res, o = .normal res ∧ res.length = S.results.length ∧
    ∀ ρ, args = argsOf S ρ → S.post.den F ρ (valEnv res)

/-! ## Notions of the soundness proof

The denotation of symbolic states (`locEnv`, `dens`, `locs`, `Agree`, `ovr`) and the relation
and postconditions of the soundness induction (`Rel`, `Kc`, `InvC`, `postOf`, `IH`). -/

section Sound
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP)

variable {H : Type}

/-- The placeholder environment of a list of symbolic values. -/
def locEnv (F : Fns) (ρ ξ : Env) (ls : List SV) : Env where
  e32 j := match ls[j]? with
    | some (.i32 a) => a.den F ρ ξ
    | _ => 0
  e64 j := match ls[j]? with
    | some (.i64 a) => a.den F ρ ξ
    | _ => 0

/-- Two environments agree on the parameters `ps` (at their types). -/
def Agree (ps : List IntType) (ρ ρ' : Env) : Prop :=
  ∀ i t, ps[i]? = some t → ρ.get t i = ρ'.get t i

/-- The values a symbolic stack denotes. -/
abbrev dens (F : Fns) (ρ : Env) (l : List SV) : List Val := l.map (SV.den F ρ ρ)

/-- The locals a symbolic state denotes. -/
abbrev locs (F : Fns) (ρ : Env) (l : List SV) : List (Option Val) :=
  l.map fun v => some (v.den F ρ ρ)

/-- `ρ` with the fresh variables `p + j` set to the values of the locals `ls`. -/
def ovr (F : Fns) (p : Nat) (ρ : Env) (ls : List SV) : Env where
  e32 i := if p ≤ i then
      (match ls[i - p]? with
        | some (.i32 a) => a.den F ρ ρ
        | _ => ρ.e32 i)
    else ρ.e32 i
  e64 i := if p ≤ i then
      (match ls[i - p]? with
        | some (.i64 a) => a.den F ρ ρ
        | _ => ρ.e64 i)
    else ρ.e64 i

section Defs

variable (F : Fns) (S : FnSpec) (lt : List IntType) (ρ₀ : Env) (s₀ : Store H) (m : ModuleInst)

/-- The concrete configurations a symbolic state denotes in `ρ`. -/
def Rel (ρ : Env) (σ : SSt) (s : Store H) (f : Frame) (rs : List Val) : Prop :=
  s = s₀ ∧ f.module = m ∧ f.locals = locs F ρ σ.locals ∧ rs = dens F ρ σ.stack ∧
    σ.locals.map SV.ty = lt ∧ Agree S.params ρ ρ₀ ∧ ∀ φ ∈ σ.pc, φ.den F ρ ρ

/-- A continuation whose conditions hold at a denoted state (`vs` bottom first). -/
def Kc (K : SSt → List Fm) (s : Store H) (f : Frame) (vs : List Val) : Prop :=
  ∃ ρ σ, Rel F S lt ρ₀ s₀ m ρ σ s f vs.reverse ∧ AllValid F (K σ)

/-- The concrete invariant of loop `j`: the configurations its head state denotes. -/
def InvC (j : Nat) (s : Store H) (f : Frame) (a : List Val) : Prop :=
  a = [] ∧ ∃ ρ, Rel F S lt ρ₀ s₀ m ρ (havoc S lt j) s f []

/-- The postcondition of code run under the labels `L` with the continuation `kont`. -/
def postOf (L : List Lbl) (kont : SSt → List Fm) : Post H := fun s f o =>
  match o with
  | .normal vs => Kc F S lt ρ₀ s₀ m kont s f vs
  | .br l vs =>
    match L[l]? with
    | some (.blk n K) => n ≤ vs.length ∧ Kc F S lt ρ₀ s₀ m K s f (vs.drop (vs.length - n))
    | some (.lp j) => InvC F S lt ρ₀ s₀ m j s f []
    | none => False
  | .ret vs => Kc F S lt ρ₀ s₀ m (retVC S) s f vs
  | _ => False

/-- The induction hypothesis: soundness of `gen` at `fuel`. -/
def IH (P : Profile) (host : HostSemantics H) (fuel : Nat) : Prop :=
  ∀ L kont k is σ ρ s f rs, Rel F S lt ρ₀ s₀ m ρ σ s f rs →
    AllValid F (gen S lt fuel L kont k is σ) →
    HWP P host s f (vals rs.reverse ++ expression is) (postOf F S lt ρ₀ s₀ m L kont)

end Defs

end Sound

end Silmaril.Wasm.Auto.VCGen
