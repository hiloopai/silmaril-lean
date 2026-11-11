module

public import Silmaril.Wasm.Auto.EGraph.Defs
public import Silmaril.Wasm.Auto.XExec.Defs
public import Silmaril.Wasm.Auto.Equiv.Defs
public import Silmaril.Wasm.Logic.Instr.Defs

/-! # E-graph certificates for straight-line segments with locals

The pass-1 checker (`Silmaril.Wasm.Auto.EGraph`) relates terms: straight-line integer code
without `local.set`/`local.tee` whose stack discipline is a tree. Real optimizer input and
output keep intermediate values in locals, drop values and overwrite locals. This module
lifts such code to an **effect summary** and checks two summaries with certificates:

* `Sym`: a symbolic state: the operand stack (top first) and the current value of each local,
  as terms over the *initial* frame, and the **guards**: terms computed and then discarded
  (dropped, or overwritten in a local). A discarded term is not observable, but its trap is
  (`div_u` by zero traps even when the quotient is dropped), so it is kept;
* `lstep`, `lsteps`, `lift`: symbolic execution of `nop`, `drop`, integer constants,
  `local.get`/`local.set`/`local.tee` and the integer unary, test, binary and comparison
  operators;
* `den f S`: what a symbolic state denotes in a frame: `none` when some term of the state
  (guard, local or stack slot) is `none` (a trap or a type error), else the frame with the
  locals set and the stack values;
* `XStep`, `checkEqX`: the basic certificate steps (library rules, constant folding, the
  computed rewrites `Term.comp?`) plus a second family of computed rewrites `comp2?`
  (odd masks of booleans, shifts of shifts, unsigned comparisons with `0` and `1`, `x <s 0` as a shift, `eqz` of a
  signed remainder by a power of two as a mask, signed division by a power of two);
* `Cover`, `coversOk`: why the terms of one side cannot trap when those of the other side do
  not (a typed term without division, or a chain to a subterm of a term of the other side);
* `checkSeg` (`SegEquiv`: same stack, same locals, same traps) and `checkBody` (`BodyEquiv`:
  same stack, same store and module, same traps; the locals may differ, as after a function
  body).

Soundness is in `Silmaril.Wasm.Auto.ESeg.Thms`. Everything here is structurally recursive, so
`decide +kernel` evaluates a check.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph

/-! ## Computed rewrites, second family -/

/-- Shifts of shifts by constants, when the counts add up below the width:
`(a << m) << n = a << (m + n)`, and the same for `shr_u` and `shr_s`. -/
def shiftShift? : Term → Option Term
  | .bin t op (.bin t' op' a (.const t₁ m)) (.const t₂ n) =>
    if t = t' ∧ t = t₁ ∧ t = t₂ ∧ op = op' ∧ m < t.width ∧ n < t.width ∧ m + n < t.width ∧
        (op = .shl ∨ op = .shr .unsigned ∨ op = .shr .signed) then
      some (.bin t op a (.const t (m + n)))
    else none
  | _ => none

/-- Unsigned comparisons with `0` and `1` as tests: `a <u 1` and `a ≤u 0` are `eqz a`;
`a >u 0` and `a ≥u 1` are `a ≠ 0`. -/
def cmpZero? : Term → Option Term
  | .rel t (.lt .unsigned) a (.const t' 1) => if t = t' then some (.test t a) else none
  | .rel t (.le .unsigned) a (.const t' 0) => if t = t' then some (.test t a) else none
  | .rel t (.gt .unsigned) a (.const t' 0) =>
    if t = t' then some (.rel t .ne a (.const t 0)) else none
  | .rel t (.ge .unsigned) a (.const t' 1) =>
    if t = t' then some (.rel t .ne a (.const t 0)) else none
  | _ => none

/-- The sign test: `a <s 0` is `a >>u 31` (at `i32`). -/
def signTest? : Term → Option Term
  | .rel .i32 (.lt .signed) a (.const .i32 0) =>
    some (.bin .i32 (.shr .unsigned) a (.const .i32 31))
  | _ => none

/-- Divisibility by a power of two: `eqz (a %s 2^k)` is `eqz (a & (2^k - 1))`, for
`2^k < 2^(w-1)` (Binaryen's `OptimizeInstructions`). -/
def sremEqz? : Term → Option Term
  | .test t (.bin t' (.rem .signed) a (.const t'' n)) =>
    if t = t' ∧ t = t'' then
      (pow2Exp? (t.width - 1) n).map fun _ => .test t (.bin t .and a (.const t (n - 1)))
    else none
  | _ => none

/-- The bias form of signed division by `2^k`, `0 < k < w - 1`:
`a /s 2^k = (a + ((a >>s (w-1)) >>u (w-k))) >>s k` (what C compilers emit). -/
def sdivForm (t : IntType) (a : Term) (k : Nat) : Term :=
  .bin t (.shr .signed)
    (.bin t .add a
      (.bin t (.shr .unsigned) (.bin t (.shr .signed) a (.const t (t.width - 1)))
        (.const t (t.width - k))))
    (.const t k)

/-- Signed division by a power of two as shifts (`sdivForm`). -/
def sdivPow2? : Term → Option Term
  | .bin t (.div .signed) a (.const t' n) =>
    if t = t' then
      (pow2Exp? (t.width - 1) n).bind fun k => if 0 < k then some (sdivForm t a k) else none
    else none
  | _ => none

/-- The term is a test or a comparison: its value is `0` or `1`. -/
def isBool : Term → Bool
  | .test _ _ | .rel _ _ _ _ => true
  | _ => false

/-- A mask with the low bit set keeps a boolean: `c & b = b & c = b` for `b` a test or a
comparison and `c` odd (Binaryen's `OptimizeInstructions` drops such masks). -/
def boolMask? : Term → Option Term
  | .bin .i32 .and (.const .i32 c) b => if c % 2 = 1 ∧ isBool b = true then some b else none
  | .bin .i32 .and b (.const .i32 c) => if c % 2 = 1 ∧ isBool b = true then some b else none
  | _ => none

/-- The second family of computed rewrites, valid for every operand (trapping or not). -/
def comp2? (e : Term) : Option Term :=
  match boolMask? e with
  | some b => some b
  | none =>
  match shiftShift? e with
  | some b => some b
  | none =>
    match cmpZero? e with
    | some b => some b
    | none =>
      match signTest? e with
      | some b => some b
      | none =>
        match sremEqz? e with
        | some b => some b
        | none => sdivPow2? e

/-! ## Certificate steps -/

/-- A step of an equational certificate: the basic steps (`Step`) and the second family
of computed rewrites, forwards (`comp2`) and backwards (`uncomp2`). -/
inductive XStep where
  | rw (rule : Nat) (fwd : Bool) (path : List Nat) (σ₀ : List (Nat × Term))
  | fold (path : List Nat)
  | unfold (path : List Nat) (b : Term)
  | comp (path : List Nat)
  | uncomp (path : List Nat) (b : Term)
  | comp2 (path : List Nat)
  | uncomp2 (path : List Nat) (b : Term)
  deriving DecidableEq, Repr

/-- A pass-1 step, used only as an equation. -/
def baseEq (Γ : List IntType) (rules : List Rule) (e : Term) (s : Step) : Option Term :=
  match applyStep Γ rules e s with
  | some (e', true) => some e'
  | _ => none

/-- Apply an equational step. -/
def applyX (Γ : List IntType) (rules : List Rule) (e : Term) : XStep → Option Term
  | .rw i fwd p σ₀ => baseEq Γ rules e (.rw i fwd p σ₀)
  | .fold p => baseEq Γ rules e (.fold p)
  | .unfold p b => baseEq Γ rules e (.unfold p b)
  | .comp p => baseEq Γ rules e (.comp p)
  | .uncomp p b => baseEq Γ rules e (.uncomp p b)
  | .comp2 p => (e.get? p).bind fun a => (comp2? a).bind fun b => e.set? p b
  | .uncomp2 p b => (e.get? p).bind fun a => if comp2? b = some a then e.set? p b else none

/-- Replay a chain of equational steps. -/
def runX (Γ : List IntType) (rules : List Rule) : Term → List XStep → Option Term
  | e, [] => some e
  | e, s :: ss =>
    match applyX Γ rules e s with
    | some e' => runX Γ rules e' ss
    | none => none

/-- The steps take `e₁` to `e₂`. -/
def checkEqX (Γ : List IntType) (rules : List Rule) (e₁ e₂ : Term) (ss : List XStep) : Bool :=
  match runX Γ rules e₁ ss with
  | some e => e == e₂
  | none => false

/-- One chain per position. -/
def checkEqXL (Γ : List IntType) (rules : List Rule) :
    List Term → List Term → List (List XStep) → Bool
  | [], [], [] => true
  | e₁ :: es₁, e₂ :: es₂, c :: cs => checkEqX Γ rules e₁ e₂ c && checkEqXL Γ rules es₁ es₂ cs
  | _, _, _ => false

/-! ## Effect summaries -/

/-- A symbolic state of straight-line code: the operand stack (top first), the current term
of each local, and the guards (terms computed and discarded, whose traps are kept). All terms
are over the initial frame. -/
structure Sym where
  stack : List Term
  locs : List Term
  guards : List Term
  deriving DecidableEq, Repr

/-- The initial state of a frame with `n` locals: the empty stack, local `i` holds its own
initial value. -/
def Sym.init (n : Nat) : Sym := ⟨[], (List.range n).map Term.lget, []⟩

/-- All terms of a state: guards, locals, stack. -/
def Sym.terms (S : Sym) : List Term := S.guards ++ S.locs ++ S.stack

/-- One instruction, symbolically. A set local keeps the overwritten term as a guard; a
dropped value becomes a guard. -/
def lstep (S : Sym) : Instr → Option Sym
  | .nop => some S
  | .drop =>
    match S.stack with
    | e :: st => some ⟨st, S.locs, e :: S.guards⟩
    | [] => none
  | .intConst t c => some ⟨.const t c.toNat :: S.stack, S.locs, S.guards⟩
  | .localGet x => (S.locs[x.toNat]?).map fun e => ⟨e :: S.stack, S.locs, S.guards⟩
  | .localSet x =>
    match S.stack, S.locs[x.toNat]? with
    | e :: st, some old => some ⟨st, S.locs.set x.toNat e, old :: S.guards⟩
    | _, _ => none
  | .localTee x =>
    match S.stack, S.locs[x.toNat]? with
    | e :: st, some old => some ⟨e :: st, S.locs.set x.toNat e, old :: S.guards⟩
    | _, _ => none
  | .intUnOp t op =>
    match S.stack with
    | a :: st => some ⟨.un t op a :: st, S.locs, S.guards⟩
    | [] => none
  | .intTestOp t _ =>
    match S.stack with
    | a :: st => some ⟨.test t a :: st, S.locs, S.guards⟩
    | [] => none
  | .intBinOp t op =>
    match S.stack with
    | b :: a :: st => some ⟨.bin t op a b :: st, S.locs, S.guards⟩
    | _ => none
  | .intRelOp t op =>
    match S.stack with
    | b :: a :: st => some ⟨.rel t op a b :: st, S.locs, S.guards⟩
    | _ => none
  | _ => none

/-- A sequence of instructions, symbolically. -/
def lsteps (S : Sym) : List Instr → Option Sym
  | [] => some S
  | i :: is =>
    match lstep S i with
    | some S' => lsteps S' is
    | none => none

/-- Lift a segment run in a frame with `n` locals and any stack below. -/
def lift (n : Nat) (is : List Instr) : Option Sym := lsteps (Sym.init n) is

/-- The frame `f` with its first locals replaced by `ls`. -/
def setLocs (f : Frame) (ls : List Val) : Frame :=
  { f with locals := ls.map some ++ f.locals.drop ls.length }

/-- What a symbolic state denotes in the frame `f` it starts from: `none` if a guard, a
local or a stack slot is `none`; else the frame with the locals and the stack values. -/
def den (f : Frame) (S : Sym) : Option (Frame × List Val) :=
  (evalL f S.guards).bind fun _ => (evalL f S.locs).bind fun ls =>
    (evalL f S.stack).map fun vs => (setLocs f ls, vs)

/-! ## Covers: trapping on one side implies trapping on the other -/

/-- Why a term does not trap when the other side's terms do not: it is typed and has no
division (`total`); a chain makes it equal to the subterm at `path` of the `j`-th term of the
other side (`sub`); or its head operator cannot trap on typed operands and its operands are
covered (`split1` for unary operators and `eqz`, `split2` for binary operators and comparisons;
a division or remainder by a constant that cannot trap counts as such a head); or a chain takes
it to a term with the same value that is covered (`chain`, e.g. constant folding first). -/
inductive Cover where
  | total
  | sub (j : Nat) (path : List Nat) (steps : List XStep)
  | split1 (c : Cover)
  | split2 (c₁ c₂ : Cover)
  | chain (steps : List XStep) (c : Cover)
  deriving DecidableEq, Repr

/-- A binary operator whose right operand is `b` cannot trap on integers of type `t`: not a
division or remainder, or one by a constant that is not `0` (and, for `div_s`, not `-1`). -/
def safeBinOp (t : IntType) (op : IntBinOp) (b : Term) : Bool :=
  match op, b with
  | .div .unsigned, .const t' n | .rem .unsigned, .const t' n | .rem .signed, .const t' n =>
    t == t' && n % 2 ^ t.width != 0
  | .div .signed, .const t' n =>
    t == t' && n % 2 ^ t.width != 0 && n % 2 ^ t.width != 2 ^ t.width - 1
  | .div _, _ | .rem _, _ => false
  | _, _ => true

/-- Check one cover. -/
def coverOk (Γ : List IntType) (rules : List Rule) (other : List Term) : Term → Cover → Bool
  | e, .total => e.noTrap && (e.typeOf Γ).isSome
  | e, .sub j p ss =>
    match other[j]? with
    | some r =>
      match r.get? p with
      | some r' => checkEqX Γ rules e r' ss
      | none => false
    | none => false
  | .un t op a, .split1 c => ((Term.un t op a).typeOf Γ).isSome && coverOk Γ rules other a c
  | .test t a, .split1 c => ((Term.test t a).typeOf Γ).isSome && coverOk Γ rules other a c
  | .bin t op a b, .split2 c₁ c₂ =>
    safeBinOp t op b && ((Term.bin t op a b).typeOf Γ).isSome && coverOk Γ rules other a c₁ &&
      coverOk Γ rules other b c₂
  | .rel t op a b, .split2 c₁ c₂ =>
    ((Term.rel t op a b).typeOf Γ).isSome && coverOk Γ rules other a c₁ &&
      coverOk Γ rules other b c₂
  | e, .chain ss c =>
    match runX Γ rules e ss with
    | some e' => coverOk Γ rules other e' c
    | none => false
  | _, _ => false

/-- One cover per term. -/
def coversOk (Γ : List IntType) (rules : List Rule) (other : List Term) :
    List Term → List Cover → Bool
  | [], [] => true
  | e :: es, c :: cs => coverOk Γ rules other e c && coversOk Γ rules other es cs
  | _, _ => false

/-! ## Certificates and checkers -/

/-- A certificate for two segments: chains for the stack slots and for the locals (the
latter only for `checkSeg`), and covers for the terms of each side. -/
structure SegCert where
  stack : List (List XStep)
  locs : List (List XStep) := []
  covA : List Cover
  covB : List Cover
  deriving Repr

/-- The locals can be read by index (`Term.lget i` reads local `i`). -/
def localsOk (Γ : List IntType) : Bool := decide (Γ.length < 2 ^ 32)

/-- **The segment checker**: equal stacks, equal locals, the same traps. -/
def checkSeg (Γ : List IntType) (rules : List Rule) (a b : List Instr) (c : SegCert) : Bool :=
  localsOk Γ &&
    match lift Γ.length a, lift Γ.length b with
    | some A, some B =>
      checkEqXL Γ rules A.stack B.stack c.stack && checkEqXL Γ rules A.locs B.locs c.locs &&
        coversOk Γ rules B.terms A.terms c.covA && coversOk Γ rules A.terms B.terms c.covB
    | _, _ => false

/-- **The body checker**: equal stacks, the same traps; the locals may differ. -/
def checkBody (Γ : List IntType) (rules : List Rule) (a b : List Instr) (c : SegCert) : Bool :=
  localsOk Γ &&
    match lift Γ.length a, lift Γ.length b with
    | some A, some B =>
      checkEqXL Γ rules A.stack B.stack c.stack &&
        coversOk Γ rules B.terms A.terms c.covA && coversOk Γ rules A.terms B.terms c.covB
    | _, _ => false

/-! ## Body equivalence -/

/-- Results that agree up to the locals of the frame: both fail, or both run to the same
store and stack in frames of the same module. -/
def OutEq {H : Type} : Option (Store H × Frame × List Val) → Option (Store H × Frame × List Val) →
    Prop
  | none, none => True
  | some (s₁, f₁, r₁), some (s₂, f₂, r₂) => s₁ = s₂ ∧ f₁.module = f₂.module ∧ r₁ = r₂
  | _, _ => False

/-- Two function bodies (or tails of bodies) are **equivalent up to their locals** on frames
typed by `Γ`: from every store, frame and operand stack, `exec` fails on both or runs both to
the same store and stack, in frames of the same module. After a function body the locals are
dead, so this is the equivalence an optimizer has to keep. -/
def BodyEquiv (Γ : List IntType) (a b : List Instr) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (rs : List Val), FrameOk Γ f →
    OutEq (exec s f rs a) (exec s f rs b)

/-! ## Typed, trap-free summaries (for the every-run logic) -/

/-- Every term of the state is typed and has no division: the code neither traps nor gets
stuck in a frame typed by `Γ`. -/
def pureOk (Γ : List IntType) (S : Sym) : Bool :=
  S.terms.all fun e => e.noTrap && (e.typeOf Γ).isSome

/-- The segment lifts to a typed, trap-free summary. -/
def checkPure (Γ : List IntType) (a : List Instr) : Bool :=
  localsOk Γ &&
    match lift Γ.length a with
    | some A => pureOk Γ A
    | none => false

/-! ## Effect summaries with `select`, and bodies whose frames differ

Two extensions of the effect summaries of `Silmaril.Wasm.Auto.ESeg`:

* **`select`** (`lstepSel`, `liftSel`): an `i32` `select` of typed operands `a`, `b` and condition
  `c` is the term `selTerm a b c = b ^ ((a ^ b) & (0 - (c ≠ 0)))`, which the e-graph treats like
  any other term. The statements are about `Silmaril.Wasm.Auto.XExec.execS` (`exec` with
  `select`): `SegEquivSel`, `BodyEquivSel`. A `select` of `i64` operands is not lifted (terms have
  no `i32` to `i64` conversion).
* **Function entry** (`Sym.entry`, `liftEntrySel`, `checkFunc`, `FuncEquiv`): a function body
  starts in a frame whose parameters are the arguments and whose declared locals are zero.
  Lifting from that state makes every term a term over the parameters alone, so two bodies with
  the **same parameters but different declared locals** (renumbered, merged, reordered, retyped
  by an optimizer) are compared directly: `FuncEquiv Γ da db a b` says that `a` run in an entry
  frame with parameters `Γ` and declared locals `da`, and `b` in one with the same arguments
  and declared locals `db`, fail together or end with the same store and stack. This is the
  statement a renaming lemma would give for whole bodies, for any change of the declared locals.

Soundness is in `Silmaril.Wasm.Auto.ESeg.Thms`.
-/

section
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg Silmaril.Wasm.Auto.XExec

/-! ### `select` as a term -/

/-- `select a b c` on `i32` operands as a term: `b ^ ((a ^ b) & (0 - (c ≠ 0)))` (the mask is
all ones when `c ≠ 0`, zero otherwise). -/
def selTerm (a b c : Term) : Term :=
  .bin .i32 .xor b
    (.bin .i32 .and (.bin .i32 .xor a b)
      (.bin .i32 .sub (.const .i32 0) (.rel .i32 .ne c (.const .i32 0))))

/-- One instruction, symbolically, with `select` on `i32` operands typed by `Γ`. -/
def lstepSel (Γ : List IntType) (S : Sym) : Instr → Option Sym
  | .select _ =>
    match S.stack with
    | c :: b :: a :: st =>
      if a.typeOf Γ = some .i32 ∧ b.typeOf Γ = some .i32 ∧ c.typeOf Γ = some .i32 then
        some ⟨selTerm a b c :: st, S.locs, S.guards⟩
      else none
    | _ => none
  | i => lstep S i

/-- A sequence of instructions, symbolically, with `select`. -/
def lstepsSel (Γ : List IntType) (S : Sym) : List Instr → Option Sym
  | [] => some S
  | i :: is =>
    match lstepSel Γ S i with
    | some S' => lstepsSel Γ S' is
    | none => none

/-- Lift a segment run in a frame typed by `Γ`. -/
def liftSel (Γ : List IntType) (is : List Instr) : Option Sym := lstepsSel Γ (Sym.init Γ.length) is

/-- The state at function entry: parameters `0 … n-1` hold their own values, the declared
locals of types `ds` are zero. -/
def Sym.entry (n : Nat) (ds : List IntType) : Sym :=
  ⟨[], (List.range n).map Term.lget ++ ds.map fun t => .const t 0, []⟩

/-- Lift a function body with parameters `Γ` and declared locals `ds`. -/
def liftEntrySel (Γ ds : List IntType) (is : List Instr) : Option Sym :=
  lstepsSel (Γ ++ ds) (Sym.entry Γ.length ds) is

/-- Every local a term reads is below `n`. -/
def readsBelow (n : Nat) : Term → Bool
  | .const _ _ => true
  | .lget i => decide (i < n)
  | .un _ _ a | .test _ a => readsBelow n a
  | .bin _ _ a b | .rel _ _ a b => readsBelow n a && readsBelow n b

/-! ### Checkers -/

/-- **The segment checker with `select`**: equal stacks, equal locals, the same traps. -/
def checkSegSel (Γ : List IntType) (rules : List Rule) (a b : List Instr) (c : SegCert) : Bool :=
  localsOk Γ &&
    match liftSel Γ a, liftSel Γ b with
    | some A, some B =>
      checkEqXL Γ rules A.stack B.stack c.stack && checkEqXL Γ rules A.locs B.locs c.locs &&
        coversOk Γ rules B.terms A.terms c.covA && coversOk Γ rules A.terms B.terms c.covB
    | _, _ => false

/-- **The body checker with `select`**: equal stacks, the same traps. -/
def checkBodySel (Γ : List IntType) (rules : List Rule) (a b : List Instr) (c : SegCert) : Bool :=
  localsOk Γ &&
    match liftSel Γ a, liftSel Γ b with
    | some A, some B =>
      checkEqXL Γ rules A.stack B.stack c.stack &&
        coversOk Γ rules B.terms A.terms c.covA && coversOk Γ rules A.terms B.terms c.covB
    | _, _ => false

/-- **The function checker**: parameters `Γ`, declared locals `da` and `db`; both bodies are
lifted from function entry, so their terms read parameters only; equal stacks, the same
traps. -/
def checkFunc (Γ da db : List IntType) (rules : List Rule) (a b : List Instr) (c : SegCert) :
    Bool :=
  localsOk (Γ ++ da) && localsOk (Γ ++ db) &&
    match liftEntrySel Γ da a, liftEntrySel Γ db b with
    | some A, some B =>
      (A.terms ++ B.terms).all (readsBelow Γ.length) &&
        checkEqXL Γ rules A.stack B.stack c.stack &&
        coversOk Γ rules B.terms A.terms c.covA && coversOk Γ rules A.terms B.terms c.covB
    | _, _ => false

/-! ### Statements -/

/-- Segments with `select`, equivalent on frames typed by `Γ`: `execS` gives the same result
(store, frame, stack, failure) from every store, typed frame and stack. -/
def SegEquivSel (Γ : List IntType) (a b : List Instr) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (rs : List Val), FrameOk Γ f →
    execS s f rs a = execS s f rs b

/-- Bodies with `select`, equivalent up to their locals on frames typed by `Γ`. -/
def BodyEquivSel (Γ : List IntType) (a b : List Instr) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (rs : List Val), FrameOk Γ f →
    OutEq (execS s f rs a) (execS s f rs b)

/-- A frame at function entry: parameters of types `Γ`, then declared locals of types `ds`,
all zero. -/
def EntryFrame (Γ ds : List IntType) (f : Frame) : Prop :=
  FrameOk (Γ ++ ds) f ∧
    ∀ j t, ds[j]? = some t → localVal? f (lidx (Γ.length + j)) = some (intVal t 0)

/-- Two frames hold the same parameters `0 … n-1`. -/
def SameParams (n : Nat) (f g : Frame) : Prop :=
  ∀ i, i < n → localVal? f (lidx i) = localVal? g (lidx i)

/-- **Function bodies with different declared locals.** Run from function entry with the same
arguments (parameters of types `Γ`), `a` with declared locals `da` and `b` with `db`, in frames
of the same module, the bodies fail together or end with the same store and stack. -/
def FuncEquiv (Γ da db : List IntType) (a b : List Instr) : Prop :=
  ∀ {H : Type} (s : Store H) (fa fb : Frame) (rs : List Val), EntryFrame Γ da fa →
    EntryFrame Γ db fb → SameParams Γ.length fa fb → fa.module = fb.module →
      OutEq (execS s fa rs a) (execS s fb rs b)

/-! ### Typed code for the every-run bridges -/

/-- The code has no integer division or remainder (it cannot trap). -/
def noDiv : List Instr → Bool
  | [] => true
  | .intBinOp _ (.div _) :: _ | .intBinOp _ (.rem _) :: _ => false
  | _ :: is => noDiv is

/-- The code is typed by `XExec.tsteps` from the empty stack, with locals of types `Γ` (which
can be read by index). -/
def typedBody (Γ : List IntType) (a : List Instr) : Bool :=
  localsOk Γ && (tsteps Γ [] a).isSome

end

/-! ## Function bodies with different locals in the every-run logic

`FuncOutEquiv Γ da db a b`: from function entry (parameters of types `Γ`, declared locals `da`
for `a` and `db` for `b`, all zero), with the same arguments and in frames of the same module,
the every-run weakest preconditions (`Wp`, both readings, every profile and host relation) of
the two bodies agree for every postcondition blind to the locals (`Equiv.LocalsBlind`, such as
the function postconditions of the call rules), traps included. The theorems are in
`Silmaril.Wasm.Auto.ESeg.Thms`.
-/

section
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Wp Corr)
open Silmaril.Wasm.Auto.ESeg

/-- **Function bodies with different declared locals, every run.** -/
def FuncOutEquiv (Γ da db : List IntType) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (fa fb : Frame)
    (Q : Silmaril.Wasm.Logic.Core.Post H), EntryFrame Γ da fa → EntryFrame Γ db fb →
    SameParams Γ.length fa fb → fa.module = fb.module → Silmaril.Wasm.Auto.Equiv.LocalsBlind Q →
    (Wp m P host s fa (expression a) Q ↔ Wp m P host s fb (expression b) Q)

end

end Silmaril.Wasm.Auto.ESeg
