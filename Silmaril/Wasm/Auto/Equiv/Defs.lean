module

public import Silmaril.Wasm.Logic.Core.Defs
public import Silmaril.Wasm.Logic.Instr.Defs
public import Silmaril.Wasm.Logic.Total.Defs
public import Silmaril.Wasm.Logic.Memory.Defs

/-!
# Automatic equivalence of straight-line Wasm segments: definitions

A **reflective** equivalence checker for loop-free `i32`/`i64` code segments of Wasm
Core 3.0. Everything here is executable data and functions, so the check runs in the
kernel (`decide`) or compiled (`#eval`, the `wasm-equiv` benchmark executable); the
soundness theorems are in `Silmaril.Wasm.Auto.Equiv.Thms`.

* `Term`: bitvector terms over symbolic inputs (`var n`), constants, and the
  integer unary, binary and comparison operators of Wasm. `ev ρ t e` evaluates a
  term at type `t` in an environment `ρ` of bitvectors.
* `norm t e`: a normaliser. Sums, differences, products by constants and shifts
  left by constants become a canonical linear combination over `ℤ/2^w` of atoms
  (`Lin`, sorted and merged); bitwise operators are folded, simplified by their
  identities and ordered; comparisons are folded, oriented (`gt`/`ge` become
  `lt`/`le`) and equalities become `d = 0` for the canonical difference `d`.
  Atoms are normalised recursively. `norm` is proved to preserve `ev`
  (`Silmaril.Wasm.Auto.Equiv.Thms.ev_norm`); it is not claimed to be complete.
* `sexec`: symbolic execution of a segment from a symbolic state (`SState`: the
  locals and the top of the operand stack as typed terms). It accepts `nop`,
  `drop`, integer constants, `local.get`/`set`/`tee`, and the integer unary,
  binary, test and comparison operators; division and remainder only when the
  normalised divisor is a constant that cannot trap. Anything else gives `none`
  (the checker answers "unknown").
* `check lt st a b`: both segments run symbolically from the same typed initial
  state (locals typed `lt`, stack top typed `st`) and every slot of the two final
  states has equal type and equal normal form. `residuals` lists the slots whose
  normal forms differ, as bitvector equations (`Goal.Holds`) left to the caller.
* `SegEquiv lt st a b`: the semantic notion the checker decides: in every context
  (any store, any frame whose locals hold values of types `lt`, any values below
  the typed stack top, any code after the segment, any postcondition, both readings
  of the every-run logic, every profile and host relation), the weakest
  preconditions of `a` and `b` agree.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Wp Corr)

/-! ## Terms -/

/-- Bitvector terms. A term has no type of its own: it is evaluated at a type `t`
(`ev ρ t`); the arguments of a comparison are evaluated at the comparison's type. -/
inductive Term where
  /-- The symbolic input number `n`. -/
  | var (n : Nat)
  /-- A constant, read modulo `2^w`. -/
  | const (c : Nat)
  /-- An integer unary operator. -/
  | un (op : IntUnOp) (a : Term)
  /-- An integer binary operator. -/
  | bin (op : IntBinOp) (a b : Term)
  /-- A comparison at type `t`, giving `0` or `1`. -/
  | rel (t : IntType) (op : IntRelOp) (a b : Term)
  deriving DecidableEq, Repr, Inhabited

/-- An environment: the value of every symbolic input at every type. -/
abbrev Env := (t : IntType) → Nat → BitVec t.width

/-- A binary operator as a total function: a trap gives `0`. Symbolic execution only
admits trapping operators where they cannot trap. -/
def binV (t : IntType) (op : IntBinOp) (x y : BitVec t.width) : BitVec t.width :=
  match intBinOp t op x y with
  | .ok z => z
  | .error _ => 0

/-- The value of a term at type `t`. -/
def ev (ρ : Env) : (t : IntType) → Term → BitVec t.width
  | t, .var n => ρ t n
  | t, .const c => BitVec.ofNat t.width c
  | t, .un op a => intUnOp t op (ev ρ t a)
  | t, .bin op a b => binV t op (ev ρ t a) (ev ρ t b)
  | t, .rel t' op a b => (intRelOp t' op (ev ρ t' a) (ev ρ t' b)).setWidth t.width

/-! ## A total order on terms (for canonical forms) -/

def unOpCode : IntUnOp → Nat
  | .clz => 0 | .ctz => 1 | .popcnt => 2
  | .extend .i8 => 3 | .extend .i16 => 4 | .extend .i32 => 5 | .extend .i64 => 6

def sgnCode : Signedness → Nat
  | .signed => 0 | .unsigned => 1

def binOpCode : IntBinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div s => 3 + sgnCode s | .rem s => 5 + sgnCode s
  | .and => 7 | .or => 8 | .xor => 9 | .shl => 10 | .shr s => 11 + sgnCode s
  | .rotl => 13 | .rotr => 14

def relOpCode : IntRelOp → Nat
  | .eq => 0 | .ne => 1 | .lt s => 2 + sgnCode s | .gt s => 4 + sgnCode s
  | .le s => 6 + sgnCode s | .ge s => 8 + sgnCode s

def tyCode : IntType → Nat
  | .i32 => 0 | .i64 => 1

/-- A prefix code of a term. -/
def Term.enc : Term → List Nat
  | .var n => [0, n]
  | .const c => [1, c]
  | .un op a => [2, unOpCode op] ++ a.enc
  | .bin op a b => [3, binOpCode op] ++ a.enc ++ b.enc
  | .rel t op a b => [4, tyCode t, relOpCode op] ++ a.enc ++ b.enc

/-- Lexicographic order on codes. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x < y || (x == y && lexLe xs ys)

/-- The order on terms used to sort atoms and the arguments of commutative operators. -/
def Term.le (a b : Term) : Bool := lexLe a.enc b.enc

/-! ## Linear combinations -/

/-- A linear combination `k + Σ cᵢ·aᵢ` over `ℤ/2^w` with atoms `aᵢ`. -/
abbrev Lin := Nat × List (Nat × Term)

namespace Lin

def add (p q : Lin) : Lin := (p.1 + q.1, p.2 ++ q.2)

def scale (c : Nat) (p : Lin) : Lin := (c * p.1, p.2.map fun m => (c * m.1, m.2))

/-- Insert a monomial into a list sorted by atom. -/
def ins (m : Nat × Term) : List (Nat × Term) → List (Nat × Term)
  | [] => [m]
  | n :: ns => if m.2.le n.2 then m :: n :: ns else n :: ins m ns

/-- Insertion sort by atom (structural, so that the kernel evaluates it). -/
def isort : List (Nat × Term) → List (Nat × Term)
  | [] => []
  | m :: ms => ins m (isort ms)

/-- Merge neighbouring monomials with the same atom. -/
def mergeAdj : List (Nat × Term) → List (Nat × Term)
  | [] => []
  | m :: ms =>
    match mergeAdj ms with
    | n :: rest => if m.2 = n.2 then (m.1 + n.1, m.2) :: rest else m :: n :: rest
    | [] => [m]

/-- Reduce coefficients modulo `M` and drop zero monomials. -/
def reduce (M : Nat) : List (Nat × Term) → List (Nat × Term)
  | [] => []
  | m :: ms => if m.1 % M = 0 then reduce M ms else (m.1 % M, m.2) :: reduce M ms

/-- The canonical form of a linear combination at type `t`. -/
def canon (t : IntType) (p : Lin) : Lin :=
  (p.1 % 2 ^ t.width, reduce (2 ^ t.width) (mergeAdj (isort p.2)))

/-- The value of a list of monomials. -/
def evMs (ρ : Env) (t : IntType) : List (Nat × Term) → BitVec t.width
  | [] => 0
  | m :: ms => BitVec.ofNat t.width m.1 * ev ρ t m.2 + evMs ρ t ms

/-- The value of a linear combination. -/
def ev (ρ : Env) (t : IntType) (p : Lin) : BitVec t.width :=
  BitVec.ofNat t.width p.1 + evMs ρ t p.2

end Lin

/-- Read a term as a linear combination (sums and products by a constant on the left). -/
def linOf : Term → Lin
  | .bin .add a b => Lin.add (linOf a) (linOf b)
  | .bin .mul (.const c) a => Lin.scale c (linOf a)
  | .const c => (c, [])
  | e => (0, [(1, e)])

/-- A monomial as a term. -/
def mono (c : Nat) (a : Term) : Term :=
  if c = 1 then a else .bin .mul (.const c) a

/-- A sum of monomials as a term. -/
def sumMs : List (Nat × Term) → Term
  | [] => .const 0
  | [m] => mono m.1 m.2
  | m :: ms => .bin .add (mono m.1 m.2) (sumMs ms)

/-- A linear combination as a term. -/
def rebuild (p : Lin) : Term :=
  match p.2 with
  | [] => .const p.1
  | ms => if p.1 = 0 then sumMs ms else .bin .add (sumMs ms) (.const p.1)

/-- The canonical term of a linear combination at type `t`. -/
def linNorm (t : IntType) (p : Lin) : Term := rebuild (Lin.canon t p)

/-! ## The normaliser -/

/-- `2^w - 1`, the constant `-1` at type `t`. -/
def mOne (t : IntType) : Nat := 2 ^ t.width - 1

/-- Order the arguments of a commutative operator. -/
def ord2 (op : IntBinOp) (a b : Term) : Term :=
  if a.le b then .bin op a b else .bin op b a

/-- Bitwise operators on normal forms. -/
def normBitwise (t : IntType) (op : IntBinOp) (a b : Term) : Term :=
  match a, b with
  | .const x, .const y => .const (binV t op (BitVec.ofNat _ x) (BitVec.ofNat _ y)).toNat
  | _, _ =>
    if a = b then
      (match op with
       | .xor => .const 0
       | _ => a)
    else
      match op, a, b with
      | .and, .const 0, _ | .and, _, .const 0 => .const 0
      | .or, .const 0, e | .or, e, .const 0 | .xor, .const 0, e | .xor, e, .const 0 => e
      | .and, .const c, e | .and, e, .const c => if c = mOne t then e else ord2 .and a b
      | .or, .const c, _ | .or, _, .const c => if c = mOne t then .const c else ord2 .or a b
      | op, _, _ => ord2 op a b

/-- Operators that are the identity when the right operand is `0` modulo the width. -/
def idAtZero : IntBinOp → Bool
  | .shr _ | .rotl | .rotr => true
  | _ => false

/-- The other binary operators on normal forms: constant folding, and shifts and
rotations by a multiple of the width. -/
def normOther (t : IntType) (op : IntBinOp) (a b : Term) : Term :=
  match a, b with
  | .const x, .const y => .const (binV t op (BitVec.ofNat _ x) (BitVec.ofNat _ y)).toNat
  | _, .const k => if idAtZero op = true ∧ k % t.width = 0 then a else .bin op a b
  | _, _ => .bin op a b

/-- Binary operators on normal forms. -/
def normBin (t : IntType) (op : IntBinOp) (a b : Term) : Term :=
  match op with
  | .add => linNorm t (Lin.add (linOf a) (linOf b))
  | .sub => linNorm t (Lin.add (linOf a) (Lin.scale (mOne t) (linOf b)))
  | .mul =>
    match a, b with
    | .const c, _ => linNorm t (Lin.scale c (linOf b))
    | _, .const c => linNorm t (Lin.scale c (linOf a))
    | _, _ => ord2 .mul a b
  | .shl =>
    match b with
    | .const k => linNorm t (Lin.scale (2 ^ (k % t.width)) (linOf a))
    | _ => .bin .shl a b
  | .and | .or | .xor => normBitwise t op a b
  | op => normOther t op a b

/-- The canonical difference `a - b` at type `t`, up to sign (for `eq`/`ne`). -/
def diffNorm (t : IntType) (a b : Term) : Lin :=
  Lin.canon t (Lin.add (linOf a) (Lin.scale (mOne t) (linOf b)))

/-- `eq`/`ne` on normal forms: compare the canonical difference with `0`, choosing the
smaller of `d` and `-d`. -/
def normEqNe (t t' : IntType) (op : IntRelOp) (a b : Term) : Term :=
  let d := diffNorm t' a b
  match d.2 with
  | [] => .const ((intRelOp t' op (BitVec.ofNat _ d.1) 0).setWidth t.width).toNat
  | _ =>
    let d₁ := rebuild d
    let d₂ := rebuild (Lin.canon t' (Lin.scale (mOne t') d))
    if d₁.le d₂ then .rel t' op d₁ (.const 0) else .rel t' op d₂ (.const 0)

/-- The negation of a comparison, oriented like `normRel` (`gt`/`ge` become `le`/`lt`). -/
def negRel : Term → Option Term
  | .rel t .eq a b => some (.rel t .ne a b)
  | .rel t .ne a b => some (.rel t .eq a b)
  | .rel t (.lt s) a b => some (.rel t (.le s) b a)
  | .rel t (.le s) a b => some (.rel t (.lt s) b a)
  | .rel t (.gt s) a b => some (.rel t (.le s) a b)
  | .rel t (.ge s) a b => some (.rel t (.lt s) a b)
  | _ => none

/-- Is the term a comparison (a boolean)? -/
def isRel : Term → Bool
  | .rel .. => true
  | _ => false

/-- A boolean compared with `0`: `eqz` of a comparison is its negation, `ne 0` of a
comparison is the comparison (the `EqzPair` rule of Binaryen). -/
def boolEqZero (op : IntRelOp) (a b : Term) : Option Term :=
  match op, a, b with
  | .eq, r, .const 0 | .eq, .const 0, r => negRel r
  | .ne, r, .const 0 | .ne, .const 0, r => if isRel r then some r else none
  | _, _, _ => none

/-- Comparisons on normal forms; the arguments have type `t'`, the result type `t`. -/
def normRel (t t' : IntType) (op : IntRelOp) (a b : Term) : Term :=
  match a, b with
  | .const x, .const y =>
    .const ((intRelOp t' op (BitVec.ofNat _ x) (BitVec.ofNat _ y)).setWidth t.width).toNat
  | _, _ =>
    match boolEqZero op a b with
    | some r => r
    | none =>
      match op with
      | .eq => normEqNe t t' .eq a b
      | .ne => normEqNe t t' .ne a b
      | .gt s => .rel t' (.lt s) b a
      | .ge s => .rel t' (.le s) b a
      | op => .rel t' op a b

/-- The normaliser. -/
def norm : IntType → Term → Term
  | _, .var n => .var n
  | t, .const c => .const (c % 2 ^ t.width)
  | t, .un op a =>
    match norm t a with
    | .const c => .const (intUnOp t op (BitVec.ofNat _ c)).toNat
    | a' => .un op a'
  | t, .bin op a b => normBin t op (norm t a) (norm t b)
  | t, .rel t' op a b => normRel t t' op (norm t' a) (norm t' b)

/-! ## Symbolic execution -/

/-- A symbolic state: the locals and the operand stack (top first) as typed terms. -/
structure SState where
  locals : List (IntType × Term)
  stack : List (IntType × Term)
  deriving DecidableEq, Repr

/-- Division and remainder only by constants that cannot trap; every other binary
operator always. -/
def safeBin (t : IntType) (op : IntBinOp) (b : Term) : Bool :=
  match op, norm t b with
  | .div .unsigned, .const c | .rem .unsigned, .const c | .rem .signed, .const c =>
    c % 2 ^ t.width ≠ 0
  | .div .signed, .const c => c % 2 ^ t.width ≠ 0 && c % 2 ^ t.width ≠ mOne t
  | .div _, _ | .rem _, _ => false
  | _, _ => true

/-- One instruction, symbolically. -/
def sstep (S : SState) : Instr → Option SState
  | .nop => some S
  | .drop =>
    match S.stack with
    | _ :: st => some { S with stack := st }
    | [] => none
  | .intConst t c => some { S with stack := (t, .const c.toNat) :: S.stack }
  | .localGet x => S.locals[x.toNat]?.map fun p => { S with stack := p :: S.stack }
  | .localSet x =>
    match S.stack with
    | p :: st =>
      if x.toNat < S.locals.length then some ⟨S.locals.set x.toNat p, st⟩ else none
    | [] => none
  | .localTee x =>
    match S.stack with
    | p :: st =>
      if x.toNat < S.locals.length then some ⟨S.locals.set x.toNat p, p :: st⟩ else none
    | [] => none
  | .intUnOp t op =>
    match S.stack with
    | (t₁, a) :: st => if t₁ = t then some { S with stack := (t, .un op a) :: st } else none
    | [] => none
  | .intBinOp t op =>
    match S.stack with
    | (t₂, b) :: (t₁, a) :: st =>
      if t₁ = t ∧ t₂ = t ∧ safeBin t op b = true then
        some { S with stack := (t, .bin op a b) :: st }
      else none
    | _ => none
  | .intTestOp t _ =>
    match S.stack with
    | (t₁, a) :: st =>
      if t₁ = t then some { S with stack := (.i32, .rel t .eq a (.const 0)) :: st } else none
    | [] => none
  | .intRelOp t op =>
    match S.stack with
    | (t₂, b) :: (t₁, a) :: st =>
      if t₁ = t ∧ t₂ = t then some { S with stack := (.i32, .rel t op a b) :: st } else none
    | _ => none
  | _ => none

/-- A segment, symbolically. -/
def sexec (S : SState) : List Instr → Option SState
  | [] => some S
  | i :: is =>
    match sstep S i with
    | some S' => sexec S' is
    | none => none

/-- The initial symbolic state: local `i` is input `i`, stack slot `j` (top first) is
input `lt.length + j`. -/
def initState (lt st : List IntType) : SState :=
  ⟨lt.mapIdx fun i t => (t, .var i), st.mapIdx fun j t => (t, .var (lt.length + j))⟩

/-! ## The checker -/

/-- Two slots are equal: same type, same normal form. -/
def slotEq (p q : IntType × Term) : Bool :=
  decide (p.1 = q.1) && decide (norm p.1 p.2 = norm q.1 q.2)

/-- Two slot lists are equal slot by slot. -/
def slotsEq : List (IntType × Term) → List (IntType × Term) → Bool
  | [], [] => true
  | p :: ps, q :: qs => slotEq p q && slotsEq ps qs
  | _, _ => false

/-- Two symbolic states are equal. -/
def stateEq (A B : SState) : Bool := slotsEq A.locals B.locals && slotsEq A.stack B.stack

/-- **The equivalence check.** -/
def check (lt st : List IntType) (a b : List Instr) : Bool :=
  match sexec (initState lt st) a, sexec (initState lt st) b with
  | some A, some B => stateEq A B
  | _, _ => false

/-- A residual goal: two terms of type `t` with the same value in every environment. -/
abbrev Goal := IntType × Term × Term

/-- The proposition a residual goal stands for. -/
def Goal.Holds (g : Goal) : Prop := ∀ ρ : Env, ev ρ g.1 g.2.1 = ev ρ g.1 g.2.2

/-- The residual goals of two slot lists of the same shape and types; `none` when the
shapes or types differ. -/
def slotsGoals : List (IntType × Term) → List (IntType × Term) → Option (List Goal)
  | [], [] => some []
  | p :: ps, q :: qs =>
    if p.1 = q.1 then
      (slotsGoals ps qs).map fun gs =>
        if norm p.1 p.2 = norm q.1 q.2 then gs else (p.1, norm p.1 p.2, norm q.1 q.2) :: gs
    else none
  | _, _ => none

/-- The residual goals of two symbolic states. -/
def stateGoals (A B : SState) : Option (List Goal) :=
  match slotsGoals A.locals B.locals, slotsGoals A.stack B.stack with
  | some g₁, some g₂ => some (g₁ ++ g₂)
  | _, _ => none

/-- The residual goals of two segments (`none`: unsupported code or different shapes). -/
def residuals (lt st : List IntType) (a b : List Instr) : Option (List Goal) :=
  match sexec (initState lt st) a, sexec (initState lt st) b with
  | some A, some B => stateGoals A B
  | _, _ => none

/-! ## Concrete states and the semantic notion -/

/-- The value of a typed slot. -/
def den (ρ : Env) (p : IntType × Term) : Val := .num ⟨.int p.1, ev ρ p.1 p.2⟩

/-- The frame of a symbolic state: `f` with the locals of `S`. -/
def frameAt (f : Frame) (ρ : Env) (S : SState) : Frame :=
  { f with locals := S.locals.map fun p => some (den ρ p) }

/-- The operand stack of a symbolic state, top first. -/
def stackAt (ρ : Env) (S : SState) : List Val := S.stack.map (den ρ)

/-- The code of a configuration: values `us` (bottom first), the stack of `S`, the
segment, and the rest. -/
def codeAt (ρ : Env) (S : SState) (us : List Val) (a : List Instr) (rest : List Admin) :
    List Admin :=
  vals (us ++ (stackAt ρ S).reverse) ++ expression a ++ rest

/-- **Segment equivalence** at input types `lt` (locals) and `st` (stack top, top
first): in every context, the every-run weakest preconditions of `a` and `b` agree,
in both readings (`HWP` and `TWP`), for every profile, host relation and
postcondition. -/
def SegEquiv (lt st : List IntType) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (ρ : Env) (us : List Val) (rest : List Admin) (Q : Silmaril.Wasm.Logic.Core.Post H),
    Wp m P host s (frameAt f ρ (initState lt st)) (codeAt ρ (initState lt st) us a rest) Q ↔
      Wp m P host s (frameAt f ρ (initState lt st)) (codeAt ρ (initState lt st) us b rest) Q

/-- Postconditions that do not look at the locals of the final frame (only at its
module), such as the function postconditions `funcPost` and `bodyPost` of the call
rules: after a function body the locals are dead. -/
def LocalsBlind {H : Type} (Q : Silmaril.Wasm.Logic.Core.Post H) : Prop :=
  ∀ s (F F' : Frame) o, F.module = F'.module → (Q s F o ↔ Q s F' o)

/-- **Equivalence of results**: like `SegEquiv`, but for a segment that ends the code
(a function body or the tail of one) and postconditions blind to the locals, so the
two segments may leave different values in scratch locals. -/
def OutEquiv (lt st : List IntType) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (ρ : Env) (us : List Val) (Q : Silmaril.Wasm.Logic.Core.Post H), LocalsBlind Q →
    (Wp m P host s (frameAt f ρ (initState lt st)) (codeAt ρ (initState lt st) us a []) Q ↔
      Wp m P host s (frameAt f ρ (initState lt st)) (codeAt ρ (initState lt st) us b []) Q)

/-- The result check: equal final stacks, locals ignored. -/
def checkOut (lt st : List IntType) (a b : List Instr) : Bool :=
  match sexec (initState lt st) a, sexec (initState lt st) b with
  | some A, some B => slotsEq A.stack B.stack
  | _, _ => false

/-- The residual goals of the result check. -/
def residualsOut (lt st : List IntType) (a b : List Instr) : Option (List Goal) :=
  match sexec (initState lt st) a, sexec (initState lt st) b with
  | some A, some B => slotsGoals A.stack B.stack
  | _, _ => none

/-! ## Typed concrete states -/

/-- `vs` are values of the integer types `ts`, position by position. -/
def TypedVals (ts : List IntType) (vs : List Val) : Prop :=
  ∃ h : vs.length = ts.length, ∀ (i : Nat) (hi : i < ts.length),
    ∃ x : BitVec (ts[i]'hi).width, vs[i]'(h ▸ hi) = .num ⟨.int (ts[i]'hi), x⟩

/-- The bits of an integer value of type `t` (`0` for any other value). -/
def asBV : (t : IntType) → Val → BitVec t.width
  | .i32, .num ⟨.int .i32, x⟩ => x
  | .i64, .num ⟨.int .i64, x⟩ => x
  | _, _ => 0

/-- The environment of a list of concrete inputs (locals, then the stack top). -/
def envOfVals (vs : List Val) : Env := fun t n => asBV t (vs.getD n (Val.i32 0))

/-! ## Counterexamples -/

/-- Two symbolic states differ in an environment. -/
def differ (ρ : Env) (A B : SState) : Bool :=
  decide (A.locals.map (den ρ) ≠ B.locals.map (den ρ)) || decide (stackAt ρ A ≠ stackAt ρ B)

/-- A finite environment: the listed values (as natural numbers), then `0`. -/
def envOf (xs : List Nat) : Env := fun t n => BitVec.ofNat t.width (xs.getD n 0)

/-- Is `ρ` a counterexample to the equivalence of `a` and `b`? -/
def cexAt (lt st : List IntType) (a b : List Instr) (ρ : Env) : Bool :=
  match sexec (initState lt st) a, sexec (initState lt st) b with
  | some A, some B => differ ρ A B
  | _, _ => false

/-- Small test values for differential testing. -/
def probeVals : List Nat :=
  [0, 1, 2, 3, 7, 10, 255, 256, 65535, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 63, 2 ^ 64 - 1,
    0x12345678, 0x9abcdef0]

/-- Candidate environments: every input set to one probe value, and some mixed ones. -/
def probeEnvs (n : Nat) : List (List Nat) :=
  probeVals.map (fun v => List.replicate n v) ++
    (List.range 8).map fun k =>
      (List.range n).map fun i => probeVals.getD ((i * 7 + k * 3) % probeVals.length) 0

/-- Search the probe environments for a counterexample (differential testing). -/
def findCex (lt st : List IntType) (a b : List Instr) : Option (List Nat) :=
  (probeEnvs (lt.length + st.length)).find? fun xs => cexAt lt st a b (envOf xs)

/-- The final stacks differ in an environment (locals ignored). -/
def differOut (ρ : Env) (A B : SState) : Bool := decide (stackAt ρ A ≠ stackAt ρ B)

/-- Is `ρ` a counterexample to the equivalence of results of `a` and `b`? -/
def cexAtOut (lt st : List IntType) (a b : List Instr) (ρ : Env) : Bool :=
  match sexec (initState lt st) a, sexec (initState lt st) b with
  | some A, some B => differOut ρ A B
  | _, _ => false

/-- Differential testing for the equivalence of results. -/
def findCexOut (lt st : List IntType) (a b : List Instr) : Option (List Nat) :=
  (probeEnvs (lt.length + st.length)).find? fun xs => cexAtOut lt st a b (envOf xs)

/-! ## Verdicts -/

/-- The checker's answer. -/
inductive Verdict where
  /-- Equal normal forms: equivalence holds (`segEquiv_of_check`, `outEquiv_of_checkOut`). -/
  | proved
  /-- A concrete counterexample (input values): `not_segEquiv_of_cex`, `not_outEquiv_of_cex`. -/
  | refuted (xs : List Nat)
  /-- Same shape; these bitvector goals remain (`segEquiv_of_residuals`,
  `outEquiv_of_residualsOut`). -/
  | residual (gs : List Goal)
  /-- Unsupported code or different shapes. -/
  | unknown
  deriving Repr

/-- Decide what can be decided: normal forms, then differential testing, then residuals. -/
def decideSeg (lt st : List IntType) (a b : List Instr) : Verdict :=
  if check lt st a b then .proved
  else match findCex lt st a b with
    | some xs => .refuted xs
    | none =>
      match residuals lt st a b with
      | some gs => .residual gs
      | none => .unknown

/-- `decideSeg` for the equivalence of results (function bodies). -/
def decideOut (lt st : List IntType) (a b : List Instr) : Verdict :=
  if checkOut lt st a b then .proved
  else match findCexOut lt st a b with
    | some xs => .refuted xs
    | none =>
      match residualsOut lt st a b with
      | some gs => .residual gs
      | none => .unknown

/-! ## Code in context: labels and structured control flow

`Silmaril.Wasm.Auto.Equiv` decides equivalence of straight-line segments at the top level of a
function body (`SegEquiv`: any values below, any code after). This module states equivalence of
code that sits **inside** labels and of code with structured control flow, in the every-run
logic (`Silmaril.Wasm.Logic.Hoare`: `HWP`, partial correctness, and `TWP`, total correctness):

* `seqPostM`, `labelPostM`: the postconditions of `HWP.seq`/`TWP.seq` and `HWP.label`/
  `TWP.label` for either reading;
* `NoFuncTop us`: the value right below a label is not a function reference. A body that starts
  with `return_call_ref` and no operand of its own would otherwise take that reference from
  outside the label (invalid code, but a configuration of the semantics), and the label
  inversion rule would fail;
* `LCtx`: label contexts, `vals us ++ [LABEL_k{cont} E] ++ rest` nested, with `LCtx.plug` and the
  postcondition transformer `LCtx.post`;
* `CEquiv lt st a b`: `a` and `b` have the same weakest precondition in both readings, for every
  profile, host relation, store and postcondition, in every frame whose locals are integer
  values of the types `lt`, with integer values of the types `st` on top of the stack, any
  values below them (not ending in a function reference) and any code after them;
* `PEquiv lt st a b`: the same for partial correctness (`HWP`) only, which is what the loop
  congruence gives;
* `Keeps lt st c lt' st'`: running `c` from such a typed state, every normal exit is a typed
  state of the types `lt'`, `st'` over the same values below (a typing fact about `c` alone,
  used to compose equivalences sequentially);
* `KeepsBr0 lt a`: every branch to the label right around `a` (a loop body) leaves the locals
  typed `lt` (used by the loop congruence).

A Silmaril addition.
-/

section
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type}

/-- The postcondition of a label body in either reading. -/
def labelPostM : Corr → Profile → HostSemantics H → Nat → List Instr → List Val → Post H → Post H
  | .part => labelPost
  | .total => labelPostT

/-- The postcondition of the first part of a sequence in either reading. -/
def seqPostM : Corr → Profile → HostSemantics H → List Admin → Post H → Post H
  | .part => seqPost
  | .total => seqPostT

/-- The value right below a label is not a function reference. -/
def NoFuncTop (us : List Val) : Prop := ∀ a, us.getLast? ≠ some (.ref (.func a))

/-- Label contexts. -/
inductive LCtx where
  /-- The hole. -/
  | hole
  /-- `vals us ++ [LABEL_k{cont} E] ++ rest`. -/
  | label (us : List Val) (k : Nat) (cont : List Instr) (E : LCtx) (rest : List Admin)

/-- Plug code into a label context. -/
def LCtx.plug : LCtx → List Admin → List Admin
  | .hole, x => x
  | .label us k cont E rest, x => vals us ++ [.label k cont (E.plug x)] ++ rest

/-- What code in the hole must establish for the context to establish `Q`. -/
def LCtx.post (m : Corr) (P : Profile) (host : HostSemantics H) : LCtx → Post H → Post H
  | .hole, Q => Q
  | .label us k cont E rest, Q => E.post m P host (labelPostM m P host k cont us (seqPostM m P host rest Q))

/-- Every label of the context has no function reference right below it. -/
def LCtx.Ok : LCtx → Prop
  | .hole => True
  | .label us _ _ E _ => NoFuncTop us ∧ E.Ok

/-- The code of a typed configuration: the values `us` below, the stack top `rs` (top first),
the code `a` and the rest. -/
def cfgCode (us rs : List Val) (a : List Instr) (rest : List Admin) : List Admin :=
  vals (us ++ rs.reverse) ++ expression a ++ rest

/-- A frame whose locals are integer values of the types `lt`. -/
def TypedFrame (lt : List IntType) (f : Frame) : Prop :=
  ∃ ls, f.locals = ls.map some ∧ TypedVals lt ls

/-- **Equivalence in typed contexts**, both readings of the every-run logic. -/
def CEquiv (lt st : List IntType) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (rs us : List Val) (rest : List Admin) (Q : Post H),
    TypedFrame lt f → TypedVals st rs → NoFuncTop us →
    (Wp m P host s f (cfgCode us rs a rest) Q ↔ Wp m P host s f (cfgCode us rs b rest) Q)

/-- **Equivalence in typed contexts**, partial correctness only. -/
def PEquiv (lt st : List IntType) (a b : List Instr) : Prop :=
  ∀ (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (rs us : List Val) (rest : List Admin) (Q : Post H),
    TypedFrame lt f → TypedVals st rs → NoFuncTop us →
    (HWP P host s f (cfgCode us rs a rest) Q ↔ HWP P host s f (cfgCode us rs b rest) Q)

/-- The postcondition `Q`, and every normal exit is a typed state over the values `us`. -/
def TypedExit (lt' st' : List IntType) (us : List Val) (Q : Post H) : Post H := fun s F o =>
  Q s F o ∧ ∀ vs, o = .normal vs → TypedFrame lt' F ∧ ∃ rs', TypedVals st' rs' ∧ vs = us ++ rs'.reverse

/-- **Typing of normal exits**: from a typed state, `c` falls through only to typed states. -/
def Keeps (lt st : List IntType) (c : List Instr) (lt' st' : List IntType) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (rs us : List Val) (Q : Post H),
    TypedFrame lt f → TypedVals st rs →
    Wp m P host s f (cfgCode us rs c []) Q → Wp m P host s f (cfgCode us rs c []) (TypedExit lt' st' us Q)

/-- The postcondition `Q`, and every branch to the innermost label leaves locals typed `lt`. -/
def TypedBr0 (lt : List IntType) (Q : Post H) : Post H := fun s F o =>
  Q s F o ∧ ∀ vs, o = .br 0 vs → TypedFrame lt F

/-- **Typing at loop back-edges**: from a typed state with an empty stack, every branch of `a`
to the label around it leaves locals typed `lt`. -/
def KeepsBr0 (lt : List IntType) (a : List Instr) : Prop :=
  ∀ (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame) (Q : Post H),
    TypedFrame lt f → HWP P host s f (expression a) Q → HWP P host s f (expression a) (TypedBr0 lt Q)

/-- A loop body `c ++ [br_if l]` whose straight-line part `c` runs symbolically from locals typed
`lt` and an empty stack, keeps the local types and leaves an `i32` on top (decidable;
`KeepsBr0.of_check`). -/
def brIfBodyOk (lt : List IntType) (c : List Instr) : Bool :=
  match Silmaril.Wasm.Auto.Equiv.sexec (Silmaril.Wasm.Auto.Equiv.initState lt []) c with
  | some S => decide (S.locals.map Prod.fst = lt) && decide ((S.stack.map Prod.fst).head? = some .i32)
  | none => false

/-- `block`/`loop`/`if` types without parameters. -/
def NoParams (bt : BlockType) : Prop := ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂)

end

/-! ## The extended language: memory, globals, `select`, conversions and traps

An extension of the straight-line checker of `Silmaril.Wasm.Auto.Equiv`. Executable data
and functions; the soundness theorems are in `Silmaril.Wasm.Auto.Equiv.Thms`.

* `XT`: terms over symbolic inputs with the integer operators of `Equiv.Term`, plus
  `wrap` (`i32.wrap_i64`), `ext` (`i64.extend_i32_s/u`), `sel` (`select`), and **memory as an
  array term**: `minit` (the initial memory), `mstore m t p a arg v` (memory `m` after a store
  of `v` at `a`), and `load m t p a arg` (a load from the memory term `m`). `evX ρ B0 t e` and
  `evM ρ B0 m` evaluate them in an environment `ρ` with initial memory bytes `B0`.
* `Guard`: a condition under which an instruction does not trap: an in-bounds access
  (`inb`) or a binary operator that succeeds (`binOk`: division by zero, signed overflow).
* `XState`: locals, stack, the **globals** `0 … k-1` (typed, current values), the memory term,
  and the guards met so far, each with the state at that point (where the code traps if the
  guard fails).
* `xstep`, `xsexec`: symbolic execution. Supported: everything of `Equiv.sstep`, `select`
  (numeric), `i32.wrap_i64`, `i64.extend_i32_s/u`, division and remainder by any divisor (a
  `binOk` guard unless the divisor is a safe constant), `global.get`/`global.set` of the typed
  globals, and integer loads and stores (full and packed) on memory `0` (an `inb` guard).
* `canon`: a simplifier (pure integer subterms by `Equiv.norm`, `select` with a constant or
  equal branches, `wrap` of `ext`, constant conversions), proved to preserve values.
* `checkX`: equivalence: equal guards (in order, with equal trap states), equal final states;
  `refinesX`: the left side may trap more: every guard of the right side is a guard of the left
  side, equal final states.
* `SegEquivX`, `SegRefinesX`: the semantic notions, for both readings of the every-run logic,
  in every typed context (`XCtx`: locals, stack top and globals of the given integer types,
  distinct global addresses, memory `0` present when `mem`).

A Silmaril addition.
-/

section
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Wp Corr)

/-! ### Terms -/

/-- Extended terms; `minit` and `mstore` are memory terms, the others value terms. -/
inductive XT where
  | var (n : Nat)
  | const (c : Nat)
  | un (op : IntUnOp) (a : XT)
  | bin (op : IntBinOp) (a b : XT)
  | rel (t : IntType) (op : IntRelOp) (a b : XT)
  /-- `i32.wrap_i64` of an `i64` term. -/
  | wrap (a : XT)
  /-- `i64.extend_i32_s/u` of an `i32` term. -/
  | ext (sx : Signedness) (a : XT)
  /-- `select`: `a` if the `i32` term `c` is not zero, else `b`. -/
  | sel (c a b : XT)
  /-- A load of type `t` (packed when `p ≠ none`) from the memory term `m` at `a`. -/
  | load (m : XT) (t : IntType) (p : Option (PackSize × Signedness)) (a : XT) (arg : MemArg)
  /-- The initial memory. -/
  | minit
  /-- The memory term `m` after a store of the value `v` of type `t` at `a`. -/
  | mstore (m : XT) (t : IntType) (p : Option PackSize) (a : XT) (arg : MemArg) (v : XT)
  deriving DecidableEq, Repr, Inhabited

/-- The bytes accessed by a load or store of type `t`, packed as `p`. -/
def accBytes (t : IntType) : Option PackSize → Nat
  | none => t.width / 8
  | some sz => sz.width / 8

/-- A load from bytes `B` at the address `i` (`0` out of bounds; symbolic execution guards it). -/
def loadV (B : ByteArray) (t : IntType) (p : Option (PackSize × Signedness)) (i : BitVec 32)
    (arg : MemArg) : BitVec t.width :=
  match p with
  | none =>
    match Memory.load B (effAddr i.toNat arg) (t.width / 8) with
    | some c => c.setWidth t.width
    | none => 0
  | some (sz, sx) =>
    match Memory.load B (effAddr i.toNat arg) (sz.width / 8) with
    | some c =>
      match sx with
      | .signed => c.signExtend t.width
      | .unsigned => c.setWidth t.width
    | none => 0

/-- A store into bytes `B` (unchanged out of bounds; symbolic execution guards it). -/
def storeM (B : ByteArray) (t : IntType) (p : Option PackSize) (i : BitVec 32) (arg : MemArg)
    (c : BitVec t.width) : ByteArray :=
  match p with
  | none => (Memory.store B (effAddr i.toNat arg) (count := t.width / 8) (c.setWidth _)).getD B
  | some sz => (Memory.store B (effAddr i.toNat arg) (count := sz.width / 8) (c.setWidth _)).getD B

mutual

/-- The value of a value term at type `t`. -/
def evX (ρ : Env) (B0 : ByteArray) : (t : IntType) → XT → BitVec t.width
  | t, .var n => ρ t n
  | t, .const c => BitVec.ofNat t.width c
  | t, .un op a => intUnOp t op (evX ρ B0 t a)
  | t, .bin op a b => binV t op (evX ρ B0 t a) (evX ρ B0 t b)
  | t, .rel t' op a b => (intRelOp t' op (evX ρ B0 t' a) (evX ρ B0 t' b)).setWidth t.width
  | t, .wrap a => (evX ρ B0 .i64 a).setWidth t.width
  | t, .ext sx a =>
    match sx with
    | .signed => (evX ρ B0 .i32 a).signExtend t.width
    | .unsigned => (evX ρ B0 .i32 a).setWidth t.width
  | t, .sel c a b => if evX ρ B0 .i32 c ≠ 0 then evX ρ B0 t a else evX ρ B0 t b
  | t, .load m t' p a arg => (loadV (evM ρ B0 m) t' p (evX ρ B0 .i32 a) arg).setWidth t.width
  | _, .minit => 0
  | _, .mstore .. => 0

/-- The bytes of a memory term. -/
def evM (ρ : Env) (B0 : ByteArray) : XT → ByteArray
  | .minit => B0
  | .mstore m t p a arg v => storeM (evM ρ B0 m) t p (evX ρ B0 .i32 a) arg (evX ρ B0 t v)
  | .var _ | .const _ | .un .. | .bin .. | .rel .. | .wrap _ | .ext .. | .sel .. | .load .. => B0

end

/-! ### Embedding `Equiv.Term` and the simplifier -/

/-- `Equiv.Term` as an extended term. -/
def ofTerm : Term → XT
  | .var n => .var n
  | .const c => .const c
  | .un op a => .un op (ofTerm a)
  | .bin op a b => .bin op (ofTerm a) (ofTerm b)
  | .rel t op a b => .rel t op (ofTerm a) (ofTerm b)

/-- A pure integer term (no extended constructor) as an `Equiv.Term`. -/
def toTerm? : XT → Option Term
  | .var n => some (.var n)
  | .const c => some (.const c)
  | .un op a => (toTerm? a).map (.un op)
  | .bin op a b => do return .bin op (← toTerm? a) (← toTerm? b)
  | .rel t op a b => do return .rel t op (← toTerm? a) (← toTerm? b)
  | _ => none

/-- `select` on simplified operands. -/
def mkSel (c a b : XT) : XT :=
  match c with
  | .const k => if k % 2 ^ 32 = 0 then b else a
  | _ => if a = b then a else .sel c a b

/-- `i32.wrap_i64` on a simplified operand. -/
def mkWrap (a : XT) : XT :=
  match a with
  | .const c => .const (c % 2 ^ 32)
  | .ext _ b => b
  | _ => .wrap a

/-- `i64.extend_i32_s/u` on a simplified operand. -/
def mkExt (sx : Signedness) (a : XT) : XT :=
  match a with
  | .const c =>
    match sx with
    | .signed => .const ((BitVec.ofNat 32 c).signExtend 64).toNat
    | .unsigned => .const (c % 2 ^ 32)
  | _ => .ext sx a

/-- Normalise a pure integer term by `Equiv.norm`; leave others. -/
def pureNorm (t : IntType) (e : XT) : XT :=
  match toTerm? e with
  | some e' => ofTerm (Silmaril.Wasm.Auto.Equiv.norm t e')
  | none => e

/-- A prefix code of an extended term (for ordering the arguments of commutative operators). -/
def XT.enc : XT → List Nat
  | .var n => [0, n]
  | .const c => [1, c]
  | .un op a => [2, Silmaril.Wasm.Auto.Equiv.unOpCode op] ++ a.enc
  | .bin op a b => [3, Silmaril.Wasm.Auto.Equiv.binOpCode op] ++ a.enc ++ b.enc
  | .rel t op a b => [4, Silmaril.Wasm.Auto.Equiv.tyCode t, Silmaril.Wasm.Auto.Equiv.relOpCode op] ++ a.enc ++ b.enc
  | .wrap a => [5] ++ a.enc
  | .ext sx a => [6, Silmaril.Wasm.Auto.Equiv.sgnCode sx] ++ a.enc
  | .sel c a b => [7] ++ c.enc ++ a.enc ++ b.enc
  | .load m t _ a arg => [8, Silmaril.Wasm.Auto.Equiv.tyCode t, arg.offset.val] ++ m.enc ++ a.enc
  | .minit => [9]
  | .mstore m t _ a arg v => [10, Silmaril.Wasm.Auto.Equiv.tyCode t, arg.offset.val] ++ m.enc ++ a.enc ++ v.enc

/-- The order on extended terms. -/
def XT.le (a b : XT) : Bool := Silmaril.Wasm.Auto.Equiv.lexLe a.enc b.enc

/-- Commutative binary operators. -/
def commOp : IntBinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- A binary operator with ordered arguments when it commutes. -/
def mkBin (op : IntBinOp) (a b : XT) : XT :=
  if commOp op && !(a.le b) then .bin op b a else .bin op a b

/-- A comparison oriented like `Equiv.normRel` (`gt`/`ge` become `lt`/`le`). -/
def mkRel (t : IntType) (op : IntRelOp) (a b : XT) : XT :=
  match op with
  | .gt s => .rel t (.lt s) b a
  | .ge s => .rel t (.le s) b a
  | op => .rel t op a b

mutual

/-- **The simplifier** of value terms at type `t`. -/
def canon : IntType → XT → XT
  | t, .un op a => pureNorm t (.un op (canon t a))
  | t, .bin op a b => pureNorm t (mkBin op (canon t a) (canon t b))
  | t, .rel t' op a b => pureNorm t (mkRel t' op (canon t' a) (canon t' b))
  | t, .wrap a => if t = .i32 then mkWrap (canon .i64 a) else .wrap (canon .i64 a)
  | t, .ext sx a => if t = .i64 then mkExt sx (canon .i32 a) else .ext sx (canon .i32 a)
  | t, .sel c a b => mkSel (canon .i32 c) (canon t a) (canon t b)
  | _, .load m t' p a arg => .load (canonM m) t' p (canon .i32 a) arg
  | t, e => pureNorm t e

/-- The simplifier of memory terms. -/
def canonM : XT → XT
  | .mstore m t p a arg v => .mstore (canonM m) t p (canon .i32 a) arg (canon t v)
  | e => e

end

/-! ### Guards and symbolic states -/

/-- A condition under which an instruction does not trap. -/
inductive Guard where
  /-- The access of `n` bytes at `a` (offset `arg`) is in bounds. -/
  | inb (a : XT) (arg : MemArg) (n : Nat)
  /-- The binary operator succeeds on `a` and `b`. -/
  | binOk (t : IntType) (op : IntBinOp) (a b : XT)
  deriving DecidableEq, Repr

/-- The guard holds (memory size: that of the initial memory, which stores keep). -/
def Guard.holds (ρ : Env) (B0 : ByteArray) : Guard → Bool
  | .inb a arg n => decide (effAddr (evX ρ B0 .i32 a).toNat arg + n ≤ B0.size)
  | .binOk t op a b =>
    match intBinOp t op (evX ρ B0 t a) (evX ρ B0 t b) with
    | .ok _ => true
    | .error _ => false

/-- The simplified guard. -/
def Guard.canon : Guard → Guard
  | .inb a arg n => .inb (Silmaril.Wasm.Auto.Equiv.canon .i32 a) arg n
  | .binOk t op a b => .binOk t op (Silmaril.Wasm.Auto.Equiv.canon t a) (Silmaril.Wasm.Auto.Equiv.canon t b)

/-- A symbolic state. -/
structure XState where
  /-- The locals. -/
  locals : List (IntType × XT)
  /-- The operand stack, top first. -/
  stack : List (IntType × XT)
  /-- The globals `0 … k-1`. -/
  globs : List (IntType × XT)
  /-- The memory term (memory `0`). -/
  mem : XT
  /-- The guards met so far, in order, with the state at each (where a failing guard traps). -/
  guards : List (Guard × XState)
  deriving Inhabited

/-- Division and remainder by a constant that cannot trap need no guard. -/
def safeBinX (t : IntType) (op : IntBinOp) (b : XT) : Bool :=
  match toTerm? b with
  | some b' => Silmaril.Wasm.Auto.Equiv.safeBin t op b'
  | none => match op with
    | .div _ | .rem _ => false
    | _ => true

/-- Add a guard, recording the current state. -/
def XState.guard (S : XState) (g : Guard) : XState :=
  { S with guards := S.guards ++ [(g, { S with guards := [] })] }

/-- One instruction, symbolically; `mem`: memory `0` may be used. -/
def xstep (mem : Bool) (S : XState) : Instr → Option XState
  | .nop => some S
  | .drop =>
    match S.stack with
    | _ :: st => some { S with stack := st }
    | [] => none
  | .intConst t c => some { S with stack := (t, .const c.toNat) :: S.stack }
  | .localGet x => S.locals[x.toNat]?.map fun p => { S with stack := p :: S.stack }
  | .localSet x =>
    match S.stack with
    | p :: st =>
      if x.toNat < S.locals.length then some { S with locals := S.locals.set x.toNat p, stack := st }
      else none
    | [] => none
  | .localTee x =>
    match S.stack with
    | p :: st =>
      if x.toNat < S.locals.length then some { S with locals := S.locals.set x.toNat p, stack := p :: st }
      else none
    | [] => none
  | .globalGet x => S.globs[x.toNat]?.map fun p => { S with stack := p :: S.stack }
  | .globalSet x =>
    match S.stack, S.globs[x.toNat]? with
    | (t, v) :: st, some (t', _) =>
      if t = t' then some { S with globs := S.globs.set x.toNat (t, v), stack := st } else none
    | _, _ => none
  | .intUnOp t op =>
    match S.stack with
    | (t₁, a) :: st => if t₁ = t then some { S with stack := (t, .un op a) :: st } else none
    | [] => none
  | .intBinOp t op =>
    match S.stack with
    | (t₂, b) :: (t₁, a) :: st =>
      if t₁ = t ∧ t₂ = t then
        let S' := if safeBinX t op b then S else S.guard (.binOk t op a b)
        some { S' with stack := (t, .bin op a b) :: st }
      else none
    | _ => none
  | .intTestOp t _ =>
    match S.stack with
    | (t₁, a) :: st =>
      if t₁ = t then some { S with stack := (.i32, .rel t .eq a (.const 0)) :: st } else none
    | [] => none
  | .intRelOp t op =>
    match S.stack with
    | (t₂, b) :: (t₁, a) :: st =>
      if t₁ = t ∧ t₂ = t then some { S with stack := (.i32, .rel t op a b) :: st } else none
    | _ => none
  | .select ts =>
    match S.stack with
    | (tc, c) :: (t₂, b) :: (t₁, a) :: st =>
      if tc = .i32 ∧ t₁ = t₂ ∧ (ts = none ∨ ts = some [.num (.int t₁)]) then
        some { S with stack := (t₁, .sel c a b) :: st }
      else none
    | _ => none
  | .convert .wrap =>
    match S.stack with
    | (.i64, a) :: st => some { S with stack := (.i32, .wrap a) :: st }
    | _ => none
  | .convert (.extend sx) =>
    match S.stack with
    | (.i32, a) :: st => some { S with stack := (.i64, .ext sx a) :: st }
    | _ => none
  | .intLoad t p x arg =>
    match S.stack with
    | (.i32, a) :: st =>
      if mem ∧ x.toNat = 0 ∧ (∀ q ∈ p, q.1.width ≤ t.width) then
        let S' := S.guard (.inb a arg (accBytes t (p.map Prod.fst)))
        some { S' with stack := (t, .load S.mem t p a arg) :: st }
      else none
    | _ => none
  | .intStore t p x arg =>
    match S.stack with
    | (t₁, v) :: (.i32, a) :: st =>
      if mem ∧ x.toNat = 0 ∧ t₁ = t ∧ (∀ q ∈ p, q.width ≤ t.width) then
        let S' := S.guard (.inb a arg (accBytes t p))
        some { S' with stack := st, mem := .mstore S.mem t p a arg v }
      else none
    | _ => none
  | _ => none

/-- A segment, symbolically. -/
def xsexec (mem : Bool) (S : XState) : List Instr → Option XState
  | [] => some S
  | i :: is =>
    match xstep mem S i with
    | some S' => xsexec mem S' is
    | none => none

/-- The initial state: local `i` is input `i`, stack slot `j` input `lt.length + j`, global `k`
input `lt.length + st.length + k`; the initial memory; no guards. -/
def initX (lt st gt : List IntType) : XState where
  locals := lt.mapIdx fun i t => (t, .var i)
  stack := st.mapIdx fun j t => (t, .var (lt.length + j))
  globs := gt.mapIdx fun k t => (t, .var (lt.length + st.length + k))
  mem := .minit
  guards := []

/-! ### The checks -/

/-- Simplified slots. -/
def canonSlots (l : List (IntType × XT)) : List (IntType × XT) := l.map fun p => (p.1, canon p.1 p.2)

/-- The observable part of a state, simplified: locals, globals, memory (and the stack). -/
def XState.key (S : XState) : List (IntType × XT) × List (IntType × XT) × XT :=
  (canonSlots S.locals, canonSlots S.globs, canonM S.mem)

/-- The guards, simplified, with the simplified trap states. -/
def guardKeys (S : XState) : List (Guard × (List (IntType × XT) × List (IntType × XT) × XT)) :=
  S.guards.map fun g => (g.1.canon, g.2.key)

/-- **The equivalence check.** -/
def checkX (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Bool :=
  match xsexec mem (initX lt st gt) a, xsexec mem (initX lt st gt) b with
  | some A, some B =>
    decide (guardKeys A = guardKeys B) && decide (A.key = B.key) &&
      decide (canonSlots A.stack = canonSlots B.stack)
  | _, _ => false

/-- The observable part of a state at the end of a function body: globals and memory. -/
def XState.outKey (S : XState) : List (IntType × XT) × XT := (canonSlots S.globs, canonM S.mem)

/-- **The result check** (the end of a function body: scratch locals ignored). -/
def checkOutX (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Bool :=
  match xsexec mem (initX lt st gt) a, xsexec mem (initX lt st gt) b with
  | some A, some B =>
    decide ((A.guards.map fun g => (g.1.canon, g.2.outKey)) = (B.guards.map fun g => (g.1.canon, g.2.outKey))) &&
      decide (A.outKey = B.outKey) && decide (canonSlots A.stack = canonSlots B.stack)
  | _, _ => false

/-- **The refinement check**: `b` refines `a` (it may trap less): every guard of `b` is a guard
of `a`, and the final states agree. -/
def refinesX (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Bool :=
  match xsexec mem (initX lt st gt) a, xsexec mem (initX lt st gt) b with
  | some A, some B =>
    (B.guards.all fun g => (A.guards.map fun h => h.1.canon).contains g.1.canon) &&
      decide (A.key = B.key) && decide (canonSlots A.stack = canonSlots B.stack)
  | _, _ => false

/-! ### Concrete states -/

/-- The value of a typed slot. -/
def denX (ρ : Env) (B0 : ByteArray) (p : IntType × XT) : Val := .num ⟨.int p.1, evX ρ B0 p.1 p.2⟩

/-- Set the globals at the addresses `ga` to the values `vs`. -/
def setGlobals {H : Type} : Store H → List Nat → List Val → Store H
  | s, a :: as, v :: vs => setGlobals (s.setGlobal a v) as vs
  | s, _, _ => s

/-- A typed context: the concrete store and frame, the global addresses `ga` and the address
and instance of memory `0`, matching the initial symbolic state of types `lt`, `st`, `gt` in
the environment `ρ`, with initial memory bytes `mi.bytes`. -/
structure XCtx (H : Type) where
  s : Store H
  f : Frame
  ρ : Env
  ga : List Nat
  ma : Nat
  mi : MemInst

/-- The frame of a symbolic state. -/
def XCtx.frameOf {H : Type} (c : XCtx H) (S : XState) : Frame :=
  { c.f with locals := S.locals.map fun p => some (denX c.ρ c.mi.bytes p) }

/-- The store of a symbolic state. -/
def XCtx.storeOf {H : Type} (c : XCtx H) (mem : Bool) (S : XState) : Store H :=
  let s₁ := setGlobals c.s c.ga (S.globs.map (denX c.ρ c.mi.bytes))
  if mem then s₁.setMem c.ma { c.mi with bytes := evM c.ρ c.mi.bytes S.mem } else s₁

/-- The stack of a symbolic state, top first. -/
def XCtx.stackOf {H : Type} (c : XCtx H) (S : XState) : List Val :=
  S.stack.map (denX c.ρ c.mi.bytes)

/-- The context matches the initial symbolic state. -/
def XCtx.Ok {H : Type} (lt st gt : List IntType) (mem : Bool) (c : XCtx H) : Prop :=
  c.storeOf mem (initX lt st gt) = c.s ∧ c.frameOf (initX lt st gt) = c.f ∧
    c.ga.length = gt.length ∧ c.ga.Nodup ∧
    (∀ (k : Nat) (hk : k < c.ga.length), c.f.module.globals[k]? = some c.ga[k] ∧ c.ga[k] < c.s.globals.length) ∧
    (mem = true → c.s.mem? c.f ⟨0⟩ = some (c.ma, c.mi))

/-- The configuration code of a context: values `us`, the initial stack, `a`, `rest`. -/
def XCtx.code {H : Type} (c : XCtx H) (lt st gt : List IntType) (us : List Val) (a : List Instr)
    (rest : List Admin) : List Admin :=
  vals (us ++ (c.stackOf (initX lt st gt)).reverse) ++ expression a ++ rest

/-- **Segment equivalence with memory and globals.** -/
def SegEquivX (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (c : XCtx H) (us : List Val)
    (rest : List Admin) (Q : Silmaril.Wasm.Logic.Core.Post H), c.Ok lt st gt mem →
    (Wp m P host c.s c.f (c.code lt st gt us a rest) Q ↔ Wp m P host c.s c.f (c.code lt st gt us b rest) Q)

/-- Postconditions that do not look at the locals of the frame. -/
def LocalsBlindX {H : Type} (Q : Silmaril.Wasm.Logic.Core.Post H) : Prop :=
  ∀ s (F F' : Frame) o, F.module = F'.module → (Q s F o ↔ Q s F' o)

/-- **Equivalence of results** (segments that end a function body; postconditions blind to the
locals). -/
def OutEquivX (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (c : XCtx H) (us : List Val)
    (Q : Silmaril.Wasm.Logic.Core.Post H), c.Ok lt st gt mem → LocalsBlindX Q →
    (Wp m P host c.s c.f (c.code lt st gt us a []) Q ↔ Wp m P host c.s c.f (c.code lt st gt us b []) Q)

/-- The postcondition `Q`, or a trap. -/
def TrapOr {H : Type} (Q : Silmaril.Wasm.Logic.Core.Post H) : Silmaril.Wasm.Logic.Core.Post H :=
  fun s f o => o = .trap ∨ Q s f o

/-- **Refinement**: `b` refines `a`: whatever `b` guarantees, `a` guarantees too, or traps. -/
def SegRefinesX (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (c : XCtx H) (us : List Val)
    (rest : List Admin) (Q : Silmaril.Wasm.Logic.Core.Post H), c.Ok lt st gt mem →
    Wp m P host c.s c.f (c.code lt st gt us b rest) Q →
      Wp m P host c.s c.f (c.code lt st gt us a rest) (TrapOr Q)

end

/-! ## Notions of the soundness statements -/

section
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

/-- The host relation with no host calls. -/
def noHost : HostSemantics Unit := fun _ _ _ _ => False

/-- The postcondition "fell through with these values, in a frame of this module". -/
def resultPost (mi : ModuleInst) (vs : List Val) : Silmaril.Wasm.Logic.Core.Post Unit :=
  fun _ F' o => F'.module = mi ∧ o = .normal vs

/-- The postcondition "fell through with exactly this frame and these values". -/
def exactPost (F : Frame) (vs : List Val) : Silmaril.Wasm.Logic.Core.Post Unit :=
  fun _ F' o => F' = F ∧ o = .normal vs

variable {H : Type}

/-- What `XCtx.Ok` gives about the context, kept by every symbolic step. -/
def XCtx.Good (mem : Bool) (c : XCtx H) : Prop :=
  c.ga.Nodup ∧
    (∀ (k : Nat) (hk : k < c.ga.length), c.f.module.globals[k]? = some c.ga[k] ∧ c.ga[k] < c.s.globals.length) ∧
    (mem = true → c.s.mem? c.f ⟨0⟩ = some (c.ma, c.mi))

/-- What one symbolic step from `S` to `S'` leaves to prove: the configuration of `S'`, or, if
the step added a guard, the trap postcondition at `S` when the guard fails. -/
def XStepOut (m : Corr) (P : Profile) (host : HostSemantics H) (c : XCtx H) (mem : Bool)
    (S S' : XState) (us : List Val) (rest : List Admin) (Q : Post H) : Prop :=
  match S'.guards.drop S.guards.length with
  | (g, _) :: _ =>
    if g.holds c.ρ c.mi.bytes = true then
      Wp m P host (c.storeOf mem S') (c.frameOf S') (vals (us ++ (c.stackOf S').reverse) ++ rest) Q
    else Q (c.storeOf mem S) (c.frameOf S) .trap
  | [] => Wp m P host (c.storeOf mem S') (c.frameOf S') (vals (us ++ (c.stackOf S').reverse) ++ rest) Q

/-- The configuration code of a state. -/
abbrev cfg (c : XCtx H) (S : XState) (us : List Val) (rest : List Admin) : List Admin :=
  vals (us ++ (c.stackOf S).reverse) ++ rest

/-- The state of the first failing guard. -/
def firstFail (ρ : Env) (B0 : ByteArray) : List (Guard × XState) → Option XState
  | [] => none
  | (g, T) :: G => if g.holds ρ B0 = true then firstFail ρ B0 G else some T

/-- What a symbolic run leaves: a trap at the first failing guard, or the final configuration. -/
def XOut (m : Corr) (P : Profile) (host : HostSemantics H) (c : XCtx H) (mem : Bool) (S : XState)
    (us : List Val) (rest : List Admin) (Q : Post H) : Prop :=
  match firstFail c.ρ c.mi.bytes S.guards with
  | some T => Q (c.storeOf mem T) (c.frameOf T) .trap
  | none => Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ rest) Q

/-- A memory instance (unused when `mem = false`). -/
def noMem : MemInst := ⟨⟨.i32, ⟨0, by decide⟩, none⟩, ByteArray.empty⟩

end

end Silmaril.Wasm.Auto.Equiv
