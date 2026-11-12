module

public import Silmaril.Wasm.Auto.VCGen.Defs
public import Silmaril.Wasm.Logic.Instr.Defs
public import Silmaril.Wasm.Logic.Total.Defs

/-!
# A reflective VC generator with SSA names, linear memory and loop variants

`genFunc S fn fuel` computes, **as data**, the verification conditions of the Core 3.0
function `fn` against the annotated specification `S` (precondition, postcondition, one
invariant per loop, whether the function uses memory `0`, callee specifications, and, for total
correctness, one variant per loop). `Silmaril.Wasm.Auto.VCGen2.Thms.genFunc_sound` (proved once)
turns `AllValid F (genFunc S fn fuel)` into the every-run function specification
`fspec F S a fi` (partial correctness, every profile, every host relation), and
`genFunc_tsound` into the same specification for **total correctness** when `S.total` (every run
terminates).

With `S.total`, every branch back to loop `j` also asks that the variant `S.var[j]` (an `i32` term
over the parameters and the locals, read unsigned, no memory) at the current locals be below its
value at the locals the iteration started with (`varVC`); with the defaults (`total := false`,
no variants) no variant condition is emitted. The generator extends the straight-line generator
of `Silmaril.Wasm.Auto.VCGen` with:

* **fresh variables** (SSA names): the state carries a counter `next`; `local.set`/`local.tee` of
  a value that is not a variable or a literal binds it to the fresh variable `var t next` with
  the path condition `var t next = value`. The soundness proof keeps the **freshness invariant**
  `SSt.fresh` (every variable of the state is below `next`), so extending the environment at
  `next` does not change the meaning of the state (`EqBelow`);
* **linear memory** (memory `0` only, `FnSpec.mem`): memory variables `ρ.mem k` (`k = 0` is the
  memory at entry); a load is the term `load t n sx (.v k) a off` (an uninterpreted read of `n`
  bytes, `ldT`) with the bounds condition `inb (.v k) a (off + n)`; a store binds a fresh memory
  variable `k'` with the path condition `st k' (.v k) n a off v` (`ρ.mem k' = stT …`) and the
  same bounds condition;
* **user predicates and memory functions** in annotations: `pr k m [a₁, …]` is
  `F.pr k (memory m) [a₁, …]`, an arbitrary Lean predicate (so a loop invariant can be any
  statement about memory and `i32` values), `mfn k m a b` an `i32`-valued function of memory;
* **calls** `call x` to functions with specifications in `S.calls` (same `Fns`, same module):
  the arguments are bound to fresh variables and must satisfy the callee's precondition (a VC);
  the results are fresh variables and the callee's postcondition is assumed (with a fresh memory
  variable if the callee uses memory); `genFunc_sound` assumes the callees' `FSpecValid`;
* loops are verified from a state with fresh variables for the locals the body writes (the
  other locals keep their values, so invariants need not restate them) and a fresh memory
  variable when the body stores or calls, the loop invariant **and the precondition** in the
  path condition.

Placeholders: `loc t j` is local `j` (in an invariant) or result `j` (in the postcondition);
`MR.cur` is the current memory (in an invariant) or the final memory (in the postcondition).
Memory `MR.v 0` in an annotation is the memory at entry.

Anything else gives an unprovable condition: the generator is sound, not complete. Globals,
`memory.size`/`grow`, bulk memory, indirect calls and recursion are not supported.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.VCGen2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC (Ctl ctl)
open Silmaril.Wasm.Auto.VCGen (binW relW relB unW litT unT binT relP relV eqzV nz32 iteT wrapW
  extSW extUW arity intTy? intTys?)

/-! ## Environments and specification functions -/

/-- An environment: the values of the `i32`, `i64` and memory variables. -/
structure Env where
  e32 : Nat → BitVec 32
  e64 : Nat → BitVec 64
  mem : Nat → ByteArray

/-- The value of variable `i` of type `t`. -/
def Env.get (ρ : Env) : (t : IntType) → Nat → BitVec t.width
  | .i32, i => ρ.e32 i
  | .i64, i => ρ.e64 i

/-- Specification functions: those of `Silmaril.Wasm.Auto.VCGen`, `i32`-valued functions of a memory and two `i32`
values, and predicates on a memory and a list of `i32` values. -/
structure Fns extends Silmaril.Wasm.Auto.VCGen.Fns where
  mf : Nat → ByteArray → BitVec 32 → BitVec 32 → BitVec 32 := fun _ _ x _ => x
  pr : Nat → ByteArray → List (BitVec 32) → Prop := fun _ _ _ => True

/-- Unary specification function `k` at type `t`. -/
def Fns.app1 (F : Fns) : (t : IntType) → Nat → BitVec t.width → BitVec t.width
  | .i32 => F.f32
  | .i64 => F.f64

/-- Binary specification function `k` at type `t`. -/
def Fns.app2 (F : Fns) : (t : IntType) → Nat → BitVec t.width → BitVec t.width → BitVec t.width
  | .i32 => F.g32
  | .i64 => F.g64

/-- A memory reference: memory variable `k`, or the placeholder `cur` (the current memory in an
invariant, the final memory in a postcondition). -/
inductive MR where
  | v (k : Nat)
  | cur

/-- The memory a reference denotes (`cur` is `ξ.mem 0`). -/
def MR.den (ρ ξ : Env) : MR → ByteArray
  | .v k => ρ.mem k
  | .cur => ξ.mem 0

/-! ## Memory reads and writes -/

/-- The `n` bytes at `a`, little-endian (`0` out of bounds). -/
def rd (B : ByteArray) (a n : Nat) : BitVec (8 * n) := (Memory.load B a n).getD 0

/-- A load of `n` bytes at `a`, zero- or sign-extended to `w` bits. -/
def ldW (w n : Nat) (sx : Signedness) (B : ByteArray) (a : Nat) : BitVec w :=
  match sx with
  | .unsigned => (rd B a n).setWidth w
  | .signed => (rd B a n).signExtend w

/-- A load at type `t`. -/
def ldT : (t : IntType) → Nat → Signedness → ByteArray → Nat → BitVec t.width
  | .i32 => ldW 32
  | .i64 => ldW 64

/-- A store of the low `n` bytes of `x` at `a` (`B` out of bounds). -/
def stW (w n : Nat) (B : ByteArray) (a : Nat) (x : BitVec w) : ByteArray :=
  (Memory.store B a (count := n) (x.setWidth (8 * n))).getD B

/-- A store at type `t`. -/
def stT : (t : IntType) → Nat → ByteArray → Nat → BitVec t.width → ByteArray
  | .i32 => stW 32
  | .i64 => stW 64

/-! ## Terms and formulas -/

/-- Symbolic integer terms of type `t` (`Silmaril.Wasm.Auto.VCGen.Tm` with memory). -/
inductive Tm : IntType → Type where
  | var (t : IntType) (i : Nat) : Tm t
  | loc (t : IntType) (j : Nat) : Tm t
  | lit (t : IntType) (n : Nat) : Tm t
  | un {t : IntType} (op : IntUnOp) (a : Tm t) : Tm t
  | bin {t : IntType} (op : IntBinOp) (a b : Tm t) : Tm t
  | rel {t : IntType} (op : IntRelOp) (a b : Tm t) : Tm .i32
  | eqz {t : IntType} (a : Tm t) : Tm .i32
  | ite {t : IntType} (c : Tm .i32) (a b : Tm t) : Tm t
  | wrap (a : Tm .i64) : Tm .i32
  | ext (sx : Signedness) (a : Tm .i32) : Tm .i64
  | fn {t : IntType} (k : Nat) (a : Tm t) : Tm t
  | fn2 {t : IntType} (k : Nat) (a b : Tm t) : Tm t
  /-- A load of `n` bytes from memory `m` at address `a + off`, extended by `sx`. -/
  | load (t : IntType) (n : Nat) (sx : Signedness) (m : MR) (a : Tm .i32) (off : Nat) : Tm t
  /-- A memory specification function `F.mf k`. -/
  | mfn (k : Nat) (m : MR) (a b : Tm .i32) : Tm .i32

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
  /-- `a + n` is within memory `m`: `a.toNat + n ≤ size`. -/
  | inb (m : MR) (a : Tm .i32) (n : Nat)
  /-- The user predicate `F.pr k` on memory `m` and the values `as`. -/
  | pr (k : Nat) (m : MR) (as : List (Tm .i32))
  /-- Two memories are equal. -/
  | meq (m₁ m₂ : MR)
  /-- Memory variable `k` is memory `m` after a store of `n` bytes of `v` at `a + off`. -/
  | st {t : IntType} (k : Nat) (m : MR) (n : Nat) (a : Tm .i32) (off : Nat) (v : Tm t)

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
  | t, .load _ n sx m a off => ldT t n sx (m.den ρ ξ) ((a.den F ρ ξ).toNat + off)
  | _, .mfn k m a b => F.mf k (m.den ρ ξ) (a.den F ρ ξ) (b.den F ρ ξ)

/-- The meanings of a list of `i32` terms. -/
def Tm.dens32 (F : Fns) (ρ ξ : Env) : List (Tm .i32) → List (BitVec 32)
  | [] => []
  | a :: as => a.den F ρ ξ :: Tm.dens32 F ρ ξ as

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
  | .inb m a n => (a.den F ρ ξ).toNat + n ≤ (m.den ρ ξ).size
  | .pr k m as => F.pr k (m.den ρ ξ) (Tm.dens32 F ρ ξ as)
  | .meq m₁ m₂ => m₁.den ρ ξ = m₂.den ρ ξ
  | .st (t := t) k m n a off v =>
    ρ.mem k = stT t n (m.den ρ ξ) ((a.den F ρ ξ).toNat + off) (v.den F ρ ξ)

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

/-! ## Substitution, scope and freshness -/

/-- Replace the placeholder `cur` by memory variable `cm`. -/
def MR.subst (cm : Nat) : MR → MR
  | .v k => .v k
  | .cur => .v cm

/-- Replace each placeholder `loc t j` by the `j`-th value of `ls` (`0` if missing or of another
type) and `cur` by memory variable `cm`. -/
def Tm.subst (ls : List SV) (cm : Nat) : {t : IntType} → Tm t → Tm t
  | _, .var t i => .var t i
  | _, .loc t j => match ls[j]? with
    | some v => (v.as t).getD (.lit t 0)
    | none => .lit t 0
  | _, .lit t n => .lit t n
  | _, .un op a => .un op (a.subst ls cm)
  | _, .bin op a b => .bin op (a.subst ls cm) (b.subst ls cm)
  | _, .rel op a b => .rel op (a.subst ls cm) (b.subst ls cm)
  | _, .eqz a => .eqz (a.subst ls cm)
  | _, .ite c a b => .ite (c.subst ls cm) (a.subst ls cm) (b.subst ls cm)
  | _, .wrap a => .wrap (a.subst ls cm)
  | _, .ext sx a => .ext sx (a.subst ls cm)
  | _, .fn k a => .fn k (a.subst ls cm)
  | _, .fn2 k a b => .fn2 k (a.subst ls cm) (b.subst ls cm)
  | _, .load t n sx m a off => .load t n sx (m.subst cm) (a.subst ls cm) off
  | _, .mfn k m a b => .mfn k (m.subst cm) (a.subst ls cm) (b.subst ls cm)

def Fm.subst (ls : List SV) (cm : Nat) : Fm → Fm
  | .tt => .tt
  | .ff => .ff
  | .rel op a b => .rel op (a.subst ls cm) (b.subst ls cm)
  | .nz a => .nz (a.subst ls cm)
  | .not p => .not (p.subst ls cm)
  | .and p q => .and (p.subst ls cm) (q.subst ls cm)
  | .or p q => .or (p.subst ls cm) (q.subst ls cm)
  | .imp p q => .imp (p.subst ls cm) (q.subst ls cm)
  | .inb m a n => .inb (m.subst cm) (a.subst ls cm) n
  | .pr k m as => .pr k (m.subst cm) (as.map (Tm.subst ls cm))
  | .meq m₁ m₂ => .meq (m₁.subst cm) (m₂.subst cm)
  | .st k m n a off v => .st k (m.subst cm) n (a.subst ls cm) off (v.subst ls cm)

/-- Rename a callee's memory at entry to memory variable `m`. -/
def MR.ren (m : Nat) : MR → MR
  | .v _ => .v m
  | .cur => .cur

/-- Rename a callee's annotation to a call site: parameter `i` becomes variable `n + i`, the
memory at entry memory variable `m`. -/
def Tm.ren (n m : Nat) : {t : IntType} → Tm t → Tm t
  | _, .var t i => .var t (n + i)
  | _, .loc t j => .loc t j
  | _, .lit t k => .lit t k
  | _, .un op a => .un op (a.ren n m)
  | _, .bin op a b => .bin op (a.ren n m) (b.ren n m)
  | _, .rel op a b => .rel op (a.ren n m) (b.ren n m)
  | _, .eqz a => .eqz (a.ren n m)
  | _, .ite c a b => .ite (c.ren n m) (a.ren n m) (b.ren n m)
  | _, .wrap a => .wrap (a.ren n m)
  | _, .ext sx a => .ext sx (a.ren n m)
  | _, .fn k a => .fn k (a.ren n m)
  | _, .fn2 k a b => .fn2 k (a.ren n m) (b.ren n m)
  | _, .load t k sx r a off => .load t k sx (r.ren m) (a.ren n m) off
  | _, .mfn k r a b => .mfn k (r.ren m) (a.ren n m) (b.ren n m)

def Fm.ren (n m : Nat) : Fm → Fm
  | .tt => .tt
  | .ff => .ff
  | .rel op a b => .rel op (a.ren n m) (b.ren n m)
  | .nz a => .nz (a.ren n m)
  | .not p => .not (p.ren n m)
  | .and p q => .and (p.ren n m) (q.ren n m)
  | .or p q => .or (p.ren n m) (q.ren n m)
  | .imp p q => .imp (p.ren n m) (q.ren n m)
  | .inb r a k => .inb (r.ren m) (a.ren n m) k
  | .pr k r as => .pr k (r.ren m) (as.map (Tm.ren n m))
  | .meq r₁ r₂ => .meq (r₁.ren m) (r₂.ren m)
  | .st _ _ _ _ _ _ => .ff

/-- An annotation's memory: the memory at entry (`v 0`) or the placeholder. -/
def MR.scoped : MR → Bool
  | .v k => k == 0
  | .cur => true

/-- Every variable `var t i` of the term is parameter `i`, of type `t`, and every memory is the
memory at entry or the placeholder. -/
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
  | _, .load _ _ _ m a _ => m.scoped && a.scoped p
  | _, .mfn _ m a b => m.scoped && a.scoped p && b.scoped p

def Fm.scoped (p : List IntType) : Fm → Bool
  | .tt => true
  | .ff => true
  | .rel _ a b => a.scoped p && b.scoped p
  | .nz a => a.scoped p
  | .not q => q.scoped p
  | .and q r => q.scoped p && r.scoped p
  | .or q r => q.scoped p && r.scoped p
  | .imp q r => q.scoped p && r.scoped p
  | .inb m a _ => m.scoped && a.scoped p
  | .pr _ m as => m.scoped && as.all (Tm.scoped p)
  | .meq m₁ m₂ => m₁.scoped && m₂.scoped
  | .st _ _ _ _ _ _ => false

/-- Every variable and placeholder index is below `n` (the freshness invariant). -/
def MR.vlt (n : Nat) : MR → Bool
  | .v k => decide (k < n)
  | .cur => decide (0 < n)

def Tm.vlt (n : Nat) : {t : IntType} → Tm t → Bool
  | _, .var _ i => decide (i < n)
  | _, .loc _ j => decide (j < n)
  | _, .lit _ _ => true
  | _, .un _ a => a.vlt n
  | _, .bin _ a b => a.vlt n && b.vlt n
  | _, .rel _ a b => a.vlt n && b.vlt n
  | _, .eqz a => a.vlt n
  | _, .ite c a b => c.vlt n && a.vlt n && b.vlt n
  | _, .wrap a => a.vlt n
  | _, .ext _ a => a.vlt n
  | _, .fn _ a => a.vlt n
  | _, .fn2 _ a b => a.vlt n && b.vlt n
  | _, .load _ _ _ m a _ => m.vlt n && a.vlt n
  | _, .mfn _ m a b => m.vlt n && a.vlt n && b.vlt n

def Fm.vlt (n : Nat) : Fm → Bool
  | .tt => true
  | .ff => true
  | .rel _ a b => a.vlt n && b.vlt n
  | .nz a => a.vlt n
  | .not q => q.vlt n
  | .and q r => q.vlt n && r.vlt n
  | .or q r => q.vlt n && r.vlt n
  | .imp q r => q.vlt n && r.vlt n
  | .inb m a _ => m.vlt n && a.vlt n
  | .pr _ m as => m.vlt n && as.all (Tm.vlt n)
  | .meq m₁ m₂ => m₁.vlt n && m₂.vlt n
  | .st k m _ a _ v => decide (k < n) && m.vlt n && a.vlt n && v.vlt n

def SV.vlt (n : Nat) : SV → Bool
  | .i32 a => a.vlt n
  | .i64 a => a.vlt n

/-- A term that does not read memory (a variant). -/
def Tm.memFree : {t : IntType} → Tm t → Bool
  | _, .var _ _ => true
  | _, .loc _ _ => true
  | _, .lit _ _ => true
  | _, .un _ a => a.memFree
  | _, .bin _ a b => a.memFree && b.memFree
  | _, .rel _ a b => a.memFree && b.memFree
  | _, .eqz a => a.memFree
  | _, .ite c a b => c.memFree && a.memFree && b.memFree
  | _, .wrap a => a.memFree
  | _, .ext _ a => a.memFree
  | _, .fn _ a => a.memFree
  | _, .fn2 _ a b => a.memFree && b.memFree
  | _, .load .. => false
  | _, .mfn .. => false

/-- A variable or a literal: not worth a fresh name. -/
def Tm.atomic {t : IntType} : Tm t → Bool
  | .var _ _ => true
  | .lit _ _ => true
  | _ => false

def SV.atomic : SV → Bool
  | .i32 a => a.atomic
  | .i64 a => a.atomic

/-! ## The symbolic executor -/

/-- A symbolic state: locals, the operand stack (top first), the path condition (newest
first), the next fresh variable and the current memory variable. -/
structure SSt where
  locals : List SV
  stack : List SV
  pc : List Fm
  nv : Nat
  mem : Nat

/-- The freshness invariant: every variable of the state is below `next`. -/
def SSt.fresh (σ : SSt) : Bool :=
  σ.locals.all (SV.vlt σ.nv) && σ.stack.all (SV.vlt σ.nv) &&
    σ.pc.all (Fm.vlt σ.nv) && decide (σ.mem < σ.nv)

/-- A label: a block (its arity and the continuation after it) or loop `j` whose head state has
the locals `hl` (fresh variables from `b` on for the locals the loop writes), memory variable
`hm`. -/
inductive Lbl where
  | blk (n : Nat) (k : SSt → List Fm)
  | lp (j b hm : Nat) (hl : List SV)

/-- An annotated specification. Formulas use `var t i` for parameter `i` and `MR.v 0` for the
memory at entry; the postcondition uses `loc t j` for result `j` and `MR.cur` for the final
memory, invariant `k` uses `loc t j` for local `j` and `MR.cur` for the current memory. -/
structure FnSpec where
  params : List IntType
  results : List IntType
  pre : Fm := .tt
  post : Fm
  inv : List Fm := []
  /-- The function uses memory `0`. -/
  mem : Bool := false
  /-- Callees: `(x, S', code)` for `call x` to a function of the same module running `code` and
  meeting `S'` (whose own `inv` and `calls` are not used here). -/
  calls : List (Nat × FnSpec × Func) := []
  /-- One variant per loop, in pre-order (over parameters `var t i` and locals `loc .i32 j`, no
  memory): an unsigned `i32` value that every branch back to the loop decreases. Used when
  `total`. -/
  var : List (Tm .i32) := []
  /-- Generate the variant conditions (total correctness, `genFunc_tsound`). -/
  total : Bool := false

/-- The precondition as used in states (placeholders replaced by `0` and the memory at entry). -/
def FnSpec.preF (S : FnSpec) : Fm := S.pre.subst [] 0

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

/-- The definition `var t n = a` of a fresh variable. -/
def defF (n : Nat) : SV → Fm
  | .i32 a => .rel .eq (.var .i32 n) a
  | .i64 a => .rel .eq (.var .i64 n) a

/-- Name a value: an atomic value stays, any other is bound to the fresh variable `σ.nv`. -/
def bindV (σ : SSt) (v : SV) : SV × SSt :=
  if v.atomic then (v, σ)
  else (SV.of v.ty (.var v.ty σ.nv),
    { σ with pc := defF σ.nv v :: σ.pc, nv := σ.nv + 1 })

/-- The byte count and extension of a load. -/
def ldSz (t : IntType) : Option (PackSize × Signedness) → Nat × Signedness
  | none => (t.width / 8, .unsigned)
  | some (sz, sx) => (sz.width / 8, sx)

/-- The byte count of a store. -/
def stSz (t : IntType) : Option PackSize → Nat
  | none => t.width / 8
  | some sz => sz.width / 8

/-- One straight-line instruction: the new state and the side conditions (in the old state).
`mem` says whether memory `0` may be used. -/
def step1 (mem : Bool) (i : Instr) (σ : SSt) : Option (SSt × List Fm) :=
  match i with
  | .nop => some (σ, [])
  | .drop => match σ.stack with
    | _ :: st => some ({ σ with stack := st }, [])
    | [] => none
  | .intConst t c => some ({ σ with stack := SV.of t (.lit t c.toNat) :: σ.stack }, [])
  | .localGet x => σ.locals[x.toNat]?.map fun v => ({ σ with stack := v :: σ.stack }, [])
  | .localSet x => match σ.stack, σ.locals[x.toNat]? with
    | v :: st, some w =>
      if v.ty = w.ty then
        let b := bindV { σ with stack := st } v
        some ({ b.2 with locals := σ.locals.set x.toNat b.1 }, [])
      else none
    | _, _ => none
  | .localTee x => match σ.stack, σ.locals[x.toNat]? with
    | v :: st, some w =>
      if v.ty = w.ty then
        let b := bindV { σ with stack := st } v
        some ({ b.2 with locals := σ.locals.set x.toNat b.1, stack := b.1 :: st }, [])
      else none
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
  | .intLoad t pk x arg =>
    if mem && x.toNat == 0 then
      (pop1 .i32 σ.stack).map fun (a, st) =>
        ({ σ with stack := SV.of t (.load t (ldSz t pk).1 (ldSz t pk).2 (.v σ.mem) a
            arg.offset.val) :: st },
          [.inb (.v σ.mem) a (arg.offset.val + (ldSz t pk).1)])
    else none
  | .intStore t pk x arg =>
    if mem && x.toNat == 0 then
      match pop1 t σ.stack with
      | some (v, st) => (pop1 .i32 st).map fun (a, st') =>
          ({ σ with
              stack := st'
              mem := σ.nv
              nv := σ.nv + 1
              pc := .st σ.nv (.v σ.mem) (stSz t pk) a arg.offset.val v :: σ.pc },
            [.inb (.v σ.mem) a (arg.offset.val + stSz t pk)])
      | none => none
    else none
  | _ => none

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

/-- Whether an instruction list may write memory (a store or a call; bounded by `fuel`). -/
def writes : Nat → List Instr → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, i :: r =>
    (match i with
      | .block _ b => writes n b
      | .loop _ b => writes n b
      | .if_ _ b₁ b₂ => writes n b₁ || writes n b₂
      | .intStore .. => true
      | .call _ => true
      | _ => false) || writes n r

/-- Whether an instruction list may write local `j` (bounded by `fuel`). -/
def wrLocal (j : Nat) : Nat → List Instr → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, i :: r =>
    (match i with
      | .block _ b => wrLocal j n b
      | .loop _ b => wrLocal j n b
      | .if_ _ b₁ b₂ => wrLocal j n b₁ || wrLocal j n b₂
      | .localSet x => x.toNat == j
      | .localTee x => x.toNat == j
      | _ => false) || wrLocal j n r

/-- Is the value the variable `n`? -/
def SV.isVarAt (n : Nat) : SV → Bool
  | .i32 (.var _ i) => i == n
  | .i64 (.var _ i) => i == n
  | _ => false

/-- The equation of two values of the same type (`ff` otherwise). -/
def eqSV : SV → SV → Fm
  | .i32 a, .i32 b => .rel .eq a b
  | .i64 a, .i64 b => .rel .eq a b
  | _, _ => .ff

/-- The locals at the head of a loop: a fresh variable `b + j` for each local `j` the loop may
write (`w j`), the current value for the others. -/
def headLocals (b : Nat) (ls : List SV) (w : Nat → Bool) : List SV :=
  ls.mapIdx fun j v => if w j then SV.of v.ty (.var v.ty (b + j)) else v

/-- The kept locals of a loop head must equal the current ones: one equation per local that is
not the head's fresh variable. -/
def keepEqs (b : Nat) : Nat → List SV → List SV → List Fm
  | j, h :: hs, v :: vs => (if h.isVarAt (b + j) then [] else [eqSV v h]) ++ keepEqs b (j + 1) hs vs
  | _, _, _ => []

/-- A well-formed loop head: the types of the locals, and every local is its fresh variable or
below `b`. -/
def headOK (b : Nat) (lt : List IntType) (hl : List SV) : Bool :=
  decide (hl.map SV.ty = lt) && (hl.mapIdx fun j v => v.isVarAt (b + j) || v.vlt b).all id

/-- Invariant `k` at the locals `ls` and memory variable `cm`. -/
def invAt (S : FnSpec) (k : Nat) (ls : List SV) (cm : Nat) : Fm := (S.inv.getD k .tt).subst ls cm

/-- The state at the head of loop `k`: the head locals `hl`, memory variable `hm`, the invariant
and the precondition. -/
def havoc (S : FnSpec) (lt : List IntType) (k b hm : Nat) (hl : List SV) : SSt :=
  { locals := hl, stack := [],
    pc := [invAt S k hl hm, S.preF],
    nv := max (b + lt.length + 1) (hm + 1), mem := hm }

/-- The condition for entering or re-entering loop `j` (head variables from `b`, memory
variable `hm`, head locals `hl`) from `σ`: the invariant at the current locals and memory, and the
kept locals unchanged. The head must be well formed and its memory variable fresh or the current
one. -/
def lpVC (S : FnSpec) (lt : List IntType) (j b hm : Nat) (hl : List SV) (σ : SSt) : List Fm :=
  if (hm = b + lt.length ∨ hm = σ.mem) ∧ S.params.length < b ∧ headOK b lt hl = true then
    [vc σ (Fm.conj (invAt S j σ.locals σ.mem :: keepEqs b 0 hl σ.locals))]
  else bad σ

/-- Variant `k` at the locals `ls` (no memory). -/
def varAt (S : FnSpec) (k : Nat) (ls : List SV) : Tm .i32 := (S.var.getD k (.lit .i32 0)).subst ls 0

/-- A usable variant: memory-free and mentioning only parameters among the variables. -/
def varOK (S : FnSpec) (k : Nat) : Bool :=
  (S.var.getD k (.lit .i32 0)).memFree && (S.var.getD k (.lit .i32 0)).scoped S.params

/-- The variant condition of a branch back to loop `j` (head locals `hl`), for total
correctness: the variant at the current locals is below its value at the head. Nothing for
partial correctness. -/
def varVC (S : FnSpec) (j : Nat) (hl : List SV) (σ : SSt) : List Fm :=
  if S.total then
    if varOK S j then [vc σ (.rel (.lt .unsigned) (varAt S j σ.locals) (varAt S j hl))] else bad σ
  else []

/-- `return` (or the end of the body): the top `n` values and the current memory satisfy the
postcondition. -/
def retVC (S : FnSpec) (σ : SSt) : List Fm :=
  if S.results.length ≤ σ.stack.length ∧
      (σ.stack.take S.results.length).reverse.map SV.ty = S.results then
    [vc σ (S.post.subst (σ.stack.take S.results.length).reverse σ.mem)]
  else bad σ

/-- The end of the body: exactly the results are on the stack. -/
def endVC (S : FnSpec) (σ : SSt) : List Fm :=
  if σ.stack.length = S.results.length then retVC S σ else bad σ

/-- A branch to label `l`. A branch back to a loop asks for its invariant (and, for total
correctness, a smaller variant); the loop's memory variable must be fresh or the current one. -/
def brTo (S : FnSpec) (lt : List IntType) (L : List Lbl) (l : Nat) (σ : SSt) : List Fm :=
  match L[l]? with
  | some (.blk n K) => if n ≤ σ.stack.length then K { σ with stack := σ.stack.take n } else bad σ
  | some (.lp j b hm hl) => lpVC S lt j b hm hl σ ++ varVC S j hl σ
  | none => bad σ

/-- Pop the arguments of types `ts` (the last on top): bottom first, and the rest of the
stack. -/
def popArgs (ts : List IntType) (st : List SV) : Option (List SV × List SV) :=
  if ts.length ≤ st.length ∧ (st.take ts.length).reverse.map SV.ty = ts then
    some ((st.take ts.length).reverse, st.drop ts.length)
  else none

/-- Variables `n + j` of types `ts`. -/
def varsFrom (n : Nat) (ts : List IntType) : List SV :=
  ts.mapIdx fun j t => SV.of t (.var t (n + j))

/-- The definitions `var (n + i) = args[i]` of the arguments of a call. -/
def argDefs (n : Nat) (args : List SV) : List Fm :=
  args.mapIdx fun i v => defF (n + i) v

/-- `call x` to a callee `S'` of `S.calls` (which has no callees itself, and uses memory only if
the caller does). With `n = σ.nv`, `p` parameters and `r` results:
the arguments are bound to the fresh variables `n …`, the results are the fresh variables
`n + p …`; `n + p + r` is the callee's memory at entry if it does not use memory (unconstrained),
and `n + p + r + 1` its final memory (the caller's new memory if it uses memory). The result is
the state where the callee's precondition is asked, that condition, and the state after the
call, with the callee's postcondition in the path condition. -/
def callStep (S : FnSpec) (x : Nat) (σ : SSt) : Option (SSt × Fm × SSt) :=
  match S.calls.find? (fun c => c.1 == x) with
  | some (_, C, _) =>
    if (C.mem && !S.mem) || !C.calls.isEmpty then none else
    match popArgs C.params σ.stack with
    | some (args, st) =>
      let n := σ.nv
      let p := C.params.length
      let r := C.results.length
      let m₀ := if C.mem then σ.mem else n + p + r
      let res := varsFrom (n + p) C.results
      let σ₁ : SSt := { σ with stack := st, pc := argDefs n args ++ σ.pc, nv := n + p + r + 2 }
      some (σ₁, C.preF.ren n m₀,
        { σ₁ with
          stack := res.reverse ++ st
          mem := if C.mem then n + p + r + 1 else σ.mem
          pc := (C.post.ren n m₀).subst res (n + p + r + 1) :: σ₁.pc })
    | none => none
  | none => none

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
        let hm := if writes fuel b then σ.nv + lt.length else σ.mem
        let hl := headLocals σ.nv σ.locals fun j => wrLocal j fuel b
        lpVC S lt k σ.nv hm hl σ ++
          gen S lt fuel (.lp k σ.nv hm hl :: L) (gen S lt fuel L kont (k + 1 + nloops fuel b) r)
            (k + 1) b (havoc S lt k σ.nv hm hl)
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
    | .br l => brTo S lt L l.toNat σ
    | .brIf l =>
      match σ.stack with
      | .i32 c :: st =>
        brTo S lt L l.toNat { σ with stack := st, pc := condF c :: σ.pc } ++
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
      match i with
      | .call x =>
        match callStep S x.toNat σ with
        | some (σ₁, pre, σ₂) => vc σ₁ pre :: gen S lt fuel L kont k r σ₂
        | none => bad σ
      | _ =>
        match step1 S.mem i σ with
        | some (σ', side) => side.map (vc σ) ++ gen S lt fuel L kont k r σ'
        | none => bad σ

/-- The initial state: parameters `var t i`, declared locals `0`, the precondition; fresh
variables from `p + 1` on (memory variable `0` is the memory at entry). -/
def initSt (S : FnSpec) (lts : List IntType) : SSt :=
  { locals := S.params.mapIdx (fun i t => SV.of t (.var t i)) ++
      lts.map (fun t => SV.of t (.lit t 0)),
    stack := [], pc := [S.preF], nv := S.params.length + 1, mem := 0 }

/-- The annotations only mention parameters and the memory at entry. -/
def FnSpec.wellScoped (S : FnSpec) : Bool :=
  S.pre.scoped S.params && S.post.scoped S.params && S.inv.all (Fm.scoped S.params) &&
    S.calls.all fun c => c.2.1.pre.scoped c.2.1.params && c.2.1.post.scoped c.2.1.params

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

/-- The placeholder environment of a list of values and a memory: `loc t j` is the `j`-th value,
`cur` is `B`. -/
def valEnv (vs : List Val) (B : ByteArray) : Env where
  e32 j := match vs[j]? with
    | some (.num ⟨.int .i32, x⟩) => x
    | _ => 0
  e64 j := match vs[j]? with
    | some (.num ⟨.int .i64, x⟩) => x
    | _ => 0
  mem _ := B

/-- The store `s` with the bytes of memory `0` of `m` replaced by `B`. -/
def setM {H : Type} (s : Store H) (m : ModuleInst) (B : ByteArray) : Store H :=
  match m.mems[0]? with
  | some ma => match s.mems[ma]? with
    | some mi => s.setMem ma { mi with bytes := B }
    | none => s
  | none => s

/-- The store after a call: `s` with final memory `B` (unchanged if the function does not use
memory). -/
def upd {H : Type} (S : FnSpec) (s : Store H) (m : ModuleInst) (B : ByteArray) : Store H :=
  if S.mem then setM s m B else s

/-- The memory at entry: memory `0` of `m` holds `B` (if the function uses memory; otherwise `B`
is empty). -/
def MemOk {H : Type} (S : FnSpec) (s : Store H) (m : ModuleInst) (B : ByteArray) : Prop :=
  if S.mem then ∃ ma mi, m.mems[0]? = some ma ∧ s.mems[ma]? = some mi ∧ mi.bytes = B
  else B = ByteArray.empty

/-- The integer type of a value. -/
def valTy : Val → Option IntType
  | .num ⟨.int t, _⟩ => some t
  | _ => none

/-- The callees of `S` are in the store `s`: for each `(x, S', code)`, function `x` of `fi`'s
module is an instance of the same module running `code`, with as many parameters and results
as `S'`. -/
def Callees {H : Type} (S : FnSpec) (fi : FuncInst H) (s : Store H) : Prop :=
  ∀ c ∈ S.calls, ∃ a' fi' ps rs, fi.module.funcs[c.1]? = some a' ∧ s.funcs[a']? = some fi' ∧
    fi'.code = .wasm c.2.2 ∧ fi'.module = fi.module ∧
    Silmaril.Wasm.Validation.Expand fi'.type (.func ps rs) ∧ c.2.1.params.length = ps.length ∧
    c.2.1.results.length = rs.length

/-- **The every-run specification** `genFunc_sound` proves for the function at address `a`
(instance `fi`): called with arguments `argsOf S ρ` and memory `ρ.mem 0` satisfying the
precondition, it returns (no trap, no exception) results `res` and a final memory `B'` satisfying
the postcondition (with `loc t j` the `j`-th result and `cur` the final memory); the store
changes only in the bytes of memory `0`. -/
def fspec {H : Type} (F : Fns) (S : FnSpec) (a : Nat) (fi : FuncInst H) :
    Silmaril.Wasm.Logic.Hoare.FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ Callees S fi s ∧
    ∃ ρ, args = argsOf S ρ ∧ MemOk S s fi.module (ρ.mem 0) ∧ S.preF.den F ρ ρ
  post s args s' o := ∃ B', s' = upd S s fi.module B' ∧ ∃ res, o = .normal res ∧
    res.length = S.results.length ∧ res.map valTy = S.results.map some ∧
    ∀ ρ, args = argsOf S ρ → MemOk S s fi.module (ρ.mem 0) → S.post.den F ρ (valEnv res B')

/-! ## Definitions of the soundness proof

The environments, relations and induction hypotheses that the soundness proof
(`Silmaril.Proofs.Wasm.Auto.VCGen2`) and the statements of `Silmaril.Wasm.Auto.VCGen2.Thms` mention. -/

section Soundness

open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Logic.Hoare (FSpecValid Wp Corr TFSpecAt)
open Silmaril.Wasm.Validation (Expand Ty)

variable {H : Type}

/-! ### Environments and scope -/

/-- The placeholder environment of a list of symbolic values and a memory variable. -/
def locEnv (F : Fns) (ρ ξ : Env) (ls : List SV) (cm : Nat) : Env where
  e32 j := match ls[j]? with
    | some (.i32 a) => a.den F ρ ξ
    | _ => 0
  e64 j := match ls[j]? with
    | some (.i64 a) => a.den F ρ ξ
    | _ => 0
  mem _ := ρ.mem cm

/-- Two environments agree on the parameters `ps` (at their types) and on the memory at
entry. -/
def Agree (ps : List IntType) (ρ ρ' : Env) : Prop :=
  (∀ i t, ps[i]? = some t → ρ.get t i = ρ'.get t i) ∧ ρ.mem 0 = ρ'.mem 0

/-- Two environments agree on every variable below `n`. -/
def EqBelow (n : Nat) (ρ ρ' : Env) : Prop :=
  ∀ i < n, ρ.e32 i = ρ'.e32 i ∧ ρ.e64 i = ρ'.e64 i ∧ ρ.mem i = ρ'.mem i

/-- The values a symbolic stack denotes. -/
abbrev dens (F : Fns) (ρ : Env) (l : List SV) : List Val := l.map (SV.den F ρ ρ)

/-- The locals a symbolic state denotes. -/
abbrev locs (F : Fns) (ρ : Env) (l : List SV) : List (Option Val) :=
  l.map fun v => some (v.den F ρ ρ)

/-- `ρ` with variable `n` of type `t` set to `x`. -/
def Env.setV (ρ : Env) : (t : IntType) → Nat → BitVec t.width → Env
  | .i32, n, x => { ρ with e32 := fun i => if i = n then x else ρ.e32 i }
  | .i64, n, x => { ρ with e64 := fun i => if i = n then x else ρ.e64 i }

/-- `ρ` with memory variable `n` set to `B`. -/
def Env.setM (ρ : Env) (n : Nat) (B : ByteArray) : Env :=
  { ρ with mem := fun i => if i = n then B else ρ.mem i }

/-- The callee's environment at a call site: parameter `i` is variable `n + i`, the memory at
entry is memory variable `m`. -/
def renEnv (ρ : Env) (n m : Nat) : Env where
  e32 i := ρ.e32 (n + i)
  e64 i := ρ.e64 (n + i)
  mem _ := ρ.mem m

/-- `ρ` with the variables `n + j` set to the integer values `vs[j]`. -/
def Env.put (ρ : Env) (n : Nat) (vs : List Val) : Env where
  e32 i := if n ≤ i then
      (match vs[i - n]? with
        | some (.num ⟨.int .i32, x⟩) => x
        | _ => ρ.e32 i)
    else ρ.e32 i
  e64 i := if n ≤ i then
      (match vs[i - n]? with
        | some (.num ⟨.int .i64, x⟩) => x
        | _ => ρ.e64 i)
    else ρ.e64 i
  mem := ρ.mem

/-! ### The relation -/

section Rel

variable (F : Fns) (S : FnSpec) (lt : List IntType) (ρ₀ : Env) (s₀ : Store H) (m : ModuleInst)

/-- The concrete configurations a symbolic state denotes in `ρ`. -/
structure Rel (ρ : Env) (σ : SSt) (s : Store H) (f : Frame) (rs : List Val) : Prop where
  store : s = upd S s₀ m (ρ.mem σ.mem)
  memOk : MemOk S s₀ m (ρ.mem 0)
  modl : f.module = m
  locals : f.locals = locs F ρ σ.locals
  stack : rs = dens F ρ σ.stack
  types : σ.locals.map SV.ty = lt
  agree : Agree S.params ρ ρ₀
  pc : ∀ φ ∈ σ.pc, φ.den F ρ ρ
  fresh : σ.fresh = true
  pnv : S.params.length < σ.nv
  pre : S.preF.den F ρ₀ ρ₀

end Rel

/-- The continuation of an instruction: from any configuration related to the next state in an
environment that agrees with `ρ` below `n` (the environment before the instruction and its next
fresh variable), in either reading `c` of the logic. -/
abbrev Cont (c : Corr) (F : Fns) (S : FnSpec) (lt : List IntType) (ρ₀ : Env) (s₀ : Store H)
    (m : ModuleInst) (P : Profile) (host : HostSemantics H) (ρ : Env) (n : Nat) (σ' : SSt)
    (rest : List Admin) (Q : Post H) : Prop :=
  ∀ ρ' s' f', Rel F S lt ρ₀ s₀ m ρ' σ' s' f' (dens F ρ' σ'.stack) → EqBelow n ρ ρ' →
    Wp c P host s' f' (vals (dens F ρ' σ'.stack).reverse ++ rest) Q

/-- `ρ` with variable `n` set to the value of `v`. -/
def Env.setSV (F : Fns) (ρ : Env) (n : Nat) : SV → Env
  | .i32 a => ρ.setV .i32 n (a.den F ρ ρ)
  | .i64 a => ρ.setV .i64 n (a.den F ρ ρ)

/-! ### Calls -/

/-- A function specification holdsin reading `c`: every-run partial correctness
(`FSpecValid`) or total correctness (`TFSpecAt`). -/
def SpecOK (c : Corr) (P : Profile) (host : HostSemantics H) (a : Nat)
    (S : Silmaril.Wasm.Logic.Hoare.FSpec H) : Prop :=
  match c with
  | .part => FSpecValid P host a S
  | .total => TFSpecAt P host a S

/-- The callees of `S` meet their specifications (in reading `c`) and are in the entry store
`s₀`. -/
def CallsOK (c : Corr) (P : Profile) (host : HostSemantics H) (F : Fns) (S : FnSpec)
    (s₀ : Store H) (m : ModuleInst) : Prop :=
  ∀ e ∈ S.calls, ∃ a' fi', m.funcs[e.1]? = some a' ∧ s₀.funcs[a']? = some fi' ∧
    fi'.module = m ∧ SpecOK c P host a' (fspec F e.2.1 a' fi')

/-- The environment at the call: the arguments at `σ.nv`, the callee's memory at entry (when it
does not use memory) empty. -/
def callEnv₁ (F : Fns) (ρ : Env) (n p r : Nat) (args : List SV) : Env :=
  (ρ.put n (dens F ρ args)).setM (n + p + r) ByteArray.empty

/-- The environment after the call: the results at `n + p`, the callee's final memory at
`n + p + r + 1`. -/
def callEnv₂ (ρ₁ : Env) (n p r : Nat) (res : List Val) (B' : ByteArray) : Env :=
  (ρ₁.put (n + p) res).setM (n + p + r + 1) B'

/-- The callee's memory variable at entry at a call from `σ`. -/
def callM₀ (σ : SSt) (C : FnSpec) : Nat :=
  if C.mem then σ.mem else σ.nv + C.params.length + C.results.length

/-- The state after a call (`callStep`'s third component). -/
def callSt₂ (σ : SSt) (C : FnSpec) (args st : List SV) : SSt :=
  { locals := σ.locals
    stack := (varsFrom (σ.nv + C.params.length) C.results).reverse ++ st
    pc := (C.post.ren σ.nv (callM₀ σ C)).subst (varsFrom (σ.nv + C.params.length) C.results)
        (σ.nv + C.params.length + C.results.length + 1) :: (argDefs σ.nv args ++ σ.pc)
    nv := σ.nv + C.params.length + C.results.length + 2
    mem := if C.mem then σ.nv + C.params.length + C.results.length + 1 else σ.mem }

/-- The environment after a call from `σ` in `ρ`. -/
def callEnv (F : Fns) (ρ : Env) (σ : SSt) (C : FnSpec) (args : List SV) (res : List Val)
    (B' : ByteArray) : Env :=
  callEnv₂ (callEnv₁ F ρ σ.nv C.params.length C.results.length args) σ.nv C.params.length
    C.results.length res B'

/-- The callees' specifications hold (for every instance running their code), in reading `c`:
the hypothesis of `genFunc_sound` and `genFunc_tsound` (vacuous without callees). -/
def CalleesValid (c : Corr) (P : Profile) (host : HostSemantics H) (F : Fns) (S : FnSpec) :
    Prop :=
  ∀ e ∈ S.calls, ∀ a' (fi' : FuncInst H) (ps' rs' : Ty (.list .val)), fi'.code = .wasm e.2.2 →
    Expand fi'.type (.func ps' rs') → e.2.1.params.length = ps'.length →
    e.2.1.results.length = rs'.length → SpecOK c P host a' (fspec F e.2.1 a' fi')

/-! ### Labels, continuations and loops -/

section Loops

variable (F : Fns) (S : FnSpec) (lt : List IntType) (ρ₀ : Env) (s₀ : Store H) (m : ModuleInst)

/-- A continuation whose conditions hold at a related state (`vs` bottom first), in an
environment that agrees with `ρ` below `N`. -/
def Kc (ρ : Env) (N : Nat) (K : SSt → List Fm) (s : Store H) (f : Frame) (vs : List Val) : Prop :=
  ∃ ρ' σ, Rel F S lt ρ₀ s₀ m ρ' σ s f vs.reverse ∧ EqBelow N ρ ρ' ∧ N ≤ σ.nv ∧ AllValid F (K σ)

/-- The concrete invariant of loop `j` with head variables from `b` and memory variable `hm`, in
an environment that agrees with `ρ` below `b`. -/
def InvC (ρ : Env) (j b hm : Nat) (hl : List SV) (s : Store H) (f : Frame) (a : List Val) : Prop :=
  a = [] ∧ ∃ ρ', Rel F S lt ρ₀ s₀ m ρ' (havoc S lt j b hm hl) s f [] ∧ EqBelow b ρ ρ'

/-- **The concrete variant** of loop `j`: variant `j` read at the frame's locals (parameters from
the entry environment `ρ₀`). -/
def Vc (j : Nat) (f : Frame) : Nat :=
  ((S.var.getD j (.lit .i32 0)).den F ρ₀ (valEnv (f.locals.filterMap id) ByteArray.empty)).toNat

/-- The postcondition of code run under the labels `L` with the continuation `kont`, started in
the environment `ρ` with next fresh variable `N`, in reading `c`. A branch back to a loop
re-establishes its invariant and, for total correctness, decreases its variant below its value
at the head locals in `ρ`. -/
def postOf (c : Corr) (ρ : Env) (N : Nat) (L : List Lbl) (kont : SSt → List Fm) : Post H :=
  fun s f o =>
  match o with
  | .normal vs => Kc F S lt ρ₀ s₀ m ρ N kont s f vs
  | .br l vs =>
    match L[l]? with
    | some (.blk n K) => n ≤ vs.length ∧ Kc F S lt ρ₀ s₀ m ρ N K s f (vs.drop (vs.length - n))
    | some (.lp j b hm hl) => InvC F S lt ρ₀ s₀ m ρ j b hm hl s f [] ∧
        (c = .total → varOK S j = true ∧ Vc F S ρ₀ j f < ((varAt S j hl).den F ρ ρ).toNat)
    | none => False
  | .ret vs => Kc F S lt ρ₀ s₀ m ρ N (retVC S) s f vs
  | _ => False

/-- The loop labels of `L` have their head variables below `N`. -/
def LblsOK (L : List Lbl) (N : Nat) : Prop :=
  ∀ (l j b hm : Nat) (hl : List SV), L[l]? = some (Lbl.lp j b hm hl) → S.params.length < b ∧ b ≤ N ∧
    ∀ v ∈ hl, v.vlt N = true

/-- The induction hypothesis: soundness of `gen` at `fuel`, in reading `c`. -/
def IH (c : Corr) (P : Profile) (host : HostSemantics H) (fuel : Nat) : Prop :=
  ∀ L kont k is σ ρ s f rs, Rel F S lt ρ₀ s₀ m ρ σ s f rs → LblsOK S L σ.nv →
    AllValid F (gen S lt fuel L kont k is σ) →
    Wp c P host s f (vals rs.reverse ++ expression is) (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont)

end Loops

/-- `ρ` with the head variables `b + j` set to the values of the locals `ls` and memory variable
`b + |ls|` set to memory variable `cm`. -/
def ovr (F : Fns) (b : Nat) (ρ : Env) (ls : List SV) (cm : Nat) : Env where
  e32 i := if b ≤ i then
      (match ls[i - b]? with
        | some (.i32 a) => a.den F ρ ρ
        | _ => ρ.e32 i)
    else ρ.e32 i
  e64 i := if b ≤ i then
      (match ls[i - b]? with
        | some (.i64 a) => a.den F ρ ρ
        | _ => ρ.e64 i)
    else ρ.e64 i
  mem i := if i = b + ls.length then ρ.mem cm else ρ.mem i

section Body

variable {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}

/-- The loop body from any head configuration, by the induction hypothesis. -/
abbrev BodyOK (c : Corr) (P : Profile) (host : HostSemantics H) (L : List Lbl)
    (kont : SSt → List Fm) (k hm b₀ : Nat) (hl : List SV) (b r : List Instr) (fuel : Nat) : Prop :=
  ∀ s' f' ρ', Rel F S lt ρ₀ s₀ m ρ' (havoc S lt k b₀ hm hl) s' f' [] →
    Wp c P host s' f' (expression b) (postOf F S lt ρ₀ s₀ m c ρ' (havoc S lt k b₀ hm hl).nv
      (.lp k b₀ hm hl :: L) (gen S lt fuel L kont (k + 1 + nloops fuel b) r))

end Body

end Soundness

end Silmaril.Wasm.Auto.VCGen2
