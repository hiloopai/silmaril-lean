module

public import Silmaril.Wasm.Auto.Bridge.Defs
public import Silmaril.Wasm.Auto.EquivUnroll.Defs
public import Silmaril.Wasm.Auto.Front.Defs

@[expose] public section

/-!
# Function summaries, round 2 of the summaries track: unrolled loops, a guard-aware check

The third summariser of the front end (`docs/projects/wasm-binaryen-tooling.md`, section "Round 2 (wa2),
summaries"). It extends the extended summaries of `Silmaril.Wasm.Auto.Bridge` in two ways:

* **Loops.** Bodies are run by track equiv's unrolling executor
  `Silmaril.Wasm.Auto.EquivUnroll.xsexecU` instead of `Equiv.xsexec`: a `do … while` loop
  (`loop` whose body ends in `br_if 0`, entered with an empty operand stack) whose condition the
  simplifier decides at every iteration is unrolled. `fuel` bounds the instructions and
  iterations; past it, or on a condition that is not a constant, there is no summary.
* **The check.** `sumCheckU` compares two summaries more precisely than `Bridge.sumCheckX`:
  * a **dead guard** (a division or remainder by a divisor that simplifies to `0`) means the
    function always traps; two summaries that both always trap are equal;
  * guards are compared by a **key** that forgets what cannot make them fail (the dividend of an
    unsigned division and of either remainder);
  * results and guards are simplified by `canon2`: `canon` followed twice by `simp2`, a second
    simplifier with rules `canon` lacks (a comparison of a term with itself, `x <u 0`, shifts
    of `0`, remainders by a boolean, absorption in `and`/`or`, cancellation in `xor`, unsigned
    division by a power of two as a shift, chains of `add` and of `mul` flattened and sorted),
    each proved to preserve values.

The result of a summarised export is `Bridge.fnOutX` as before. The theorems
(`Silmaril.Wasm.Auto2.Summ.Thms`) are `behaviours_of_fnSumU` (every accepted invocation of a
summarised export returns or traps as `fnOutX` says, at every profile) and
`modEquiv_of_fnCheckU`, `modEquiv_of_checkAmongU`, `checkEquivU_proved`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Auto2.Summ

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto.Bridge (scalarInt? intTy?)
open Silmaril.Wasm.Game (ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance?)

/-! ## A second simplifier -/

/-- A comparison (its value is `0` or `1` at every type). -/
def isRel : XT → Bool
  | .rel .. => true
  | _ => false

/-- The constant `0` at type `t`. -/
def zeroC (t : IntType) : XT → Bool
  | .const c => c % 2 ^ t.width == 0
  | _ => false

/-- The exponent `k` of a constant `2 ^ k` at type `t`, `0 < k < width`. -/
def pow2? (t : IntType) : XT → Option Nat
  | .const c =>
    let v := c % 2 ^ t.width
    let k := Nat.log2 v
    if 0 < k ∧ k < t.width ∧ 2 ^ k = v then some k else none
  | _ => none

/-- `a op b` is `b` when `b` is `c op d` with `a` among `c`, `d` (absorption, for idempotent
associative commutative `op`). -/
def absorb (op : IntBinOp) (a b : XT) : Option XT :=
  match b with
  | .bin op' c d => if op' = op ∧ (a = c ∨ a = d) then some b else none
  | _ => none

/-- `a xor b` is `d` (`c`) when `b` is `c xor d` and `a` is `c` (`d`). -/
def cancelX (a b : XT) : Option XT :=
  match b with
  | .bin .xor c d => if a = c then some d else if a = d then some c else none
  | _ => none

/-- The operands of a chain of `op` (`a op (b op c)` and `(a op b) op c` alike). -/
def leaves (op : IntBinOp) : XT → List XT
  | .bin op' a b => if op' = op then leaves op a ++ leaves op b else [.bin op' a b]
  | e => [e]

/-- Insert into a list ordered by `XT.le`. -/
def insLe (x : XT) : List XT → List XT
  | [] => [x]
  | y :: ys => if x.le y then x :: y :: ys else y :: insLe x ys

/-- Insertion sort by `XT.le`. -/
def sortLe : List XT → List XT
  | [] => []
  | x :: xs => insLe x (sortLe xs)

/-- A right-nested chain of `op` (`[]` is not used). -/
def chain (op : IntBinOp) : List XT → XT
  | [] => .const 0
  | [x] => x
  | x :: xs => .bin op x (chain op xs)

/-- `a op b` for an associative commutative `op` (`add`, `mul`): the operands of both chains,
sorted, as one right-nested chain. -/
def mkAC (op : IntBinOp) (a b : XT) : XT := chain op (sortLe (leaves op a ++ leaves op b))

/-- A binary operator on simplified operands. -/
def mkBin2 (t : IntType) (op : IntBinOp) (a b : XT) : XT :=
  match op with
  | .rem _ => if isRel b then .const 0 else .bin op a b
  | .shl => if zeroC t a then .const 0 else .bin op a b
  | .shr _ => if zeroC t a then .const 0 else .bin op a b
  | .and => if a = b then a else (absorb .and a b).getD ((absorb .and b a).getD (.bin op a b))
  | .or => if a = b then a else (absorb .or a b).getD ((absorb .or b a).getD (.bin op a b))
  | .xor => if a = b then .const 0 else (cancelX a b).getD ((cancelX b a).getD (.bin op a b))
  | .div .unsigned =>
    match pow2? t b with
    | some k => .bin (.shr .unsigned) a (.const k)
    | none => .bin op a b
  | .add => mkAC .add a b
  | .mul => mkAC .mul a b
  | _ => .bin op a b

/-- The value of a comparison of a value with itself. -/
def reflRel : IntRelOp → Nat
  | .eq | .le _ | .ge _ => 1
  | .ne | .lt _ | .gt _ => 0

/-- A comparison on simplified operands. -/
def mkRel2 (t : IntType) (op : IntRelOp) (a b : XT) : XT :=
  if a = b then .const (reflRel op)
  else
    match op with
    | .lt .unsigned => if zeroC t b then .const 0 else .rel t op a b
    | _ => .rel t op a b

/-- **The second simplifier** of value terms at type `t` (memory terms and loads are kept). -/
def simp2 : IntType → XT → XT
  | t, .un op a => .un op (simp2 t a)
  | t, .bin op a b => mkBin2 t op (simp2 t a) (simp2 t b)
  | _, .rel t' op a b => mkRel2 t' op (simp2 t' a) (simp2 t' b)
  | _, .wrap a => .wrap (simp2 .i64 a)
  | _, .ext sx a => .ext sx (simp2 .i32 a)
  | t, .sel c a b => .sel (simp2 .i32 c) (simp2 t a) (simp2 t b)
  | _, e => e

/-- One round: the second simplifier, then `canon`. -/
def simpRound (t : IntType) (e : XT) : XT := canon t (simp2 t e)

/-- **The combined simplifier**: `canon`, then two rounds. -/
def canon2 (t : IntType) (e : XT) : XT := simpRound t (simpRound t (canon t e))

/-- Simplified slots. -/
def slots2 (l : List (IntType × XT)) : List (IntType × XT) := l.map fun p => (p.1, canon2 p.1 p.2)

/-! ## Guards -/

/-- Operators that fail exactly on a zero divisor. -/
def nzOp : IntBinOp → Bool
  | .div .unsigned | .rem _ => true
  | _ => false

/-- Division and remainder. -/
def isDivRem : IntBinOp → Bool
  | .div _ | .rem _ => true
  | _ => false

/-- **The key of a guard**: simplified, and without the dividend when only the divisor matters. -/
def gkey : Guard → Guard
  | .inb a arg n => .inb (canon2 .i32 a) arg n
  | .binOk t op a b =>
    if nzOp op then .binOk t (.rem .unsigned) (.const 0) (canon2 t b)
    else .binOk t op (canon2 t a) (canon2 t b)

/-- **A dead guard**: a division or remainder by a divisor that simplifies to `0` (it never
holds). -/
def gdead : Guard → Bool
  | .binOk t op _ b => isDivRem op && zeroC t (canon2 t b)
  | .inb .. => false

/-- The keys of guards. -/
def keys (G : List (Guard × XState)) : List Guard := G.map fun g => gkey g.1

/-- Some guard is dead. -/
def anyDead (G : List (Guard × XState)) : Bool := G.any fun g => gdead g.1

/-! ## Summaries with unrolled loops -/

/-- The default fuel of the unrolling executor (instructions and iterations). -/
def defFuel : Nat := 4096

/-- The summary of a function instance with scalar type `ft` in the store `s`, loops unrolled. -/
def sumOfU (fuel : Nat) {H : Type} (s : Store H) (ft : FnType) (fi : FuncInst H) :
    Option FnSumX :=
  match fi.code with
  | .wasm code =>
    match ft.params.mapM scalarInt?, ft.results.mapM scalarInt?, code.locals.mapM intTy? with
    | some ps, some rs, some ls =>
      let g := globsUsed s fi.module
      let mo := memOf s fi.module
      match Silmaril.Wasm.Auto.EquivUnroll.xsexecU mo.isSome fuel (fnInitX ps ls g.2.2) code.body with
      | some A =>
        if A.stack.map (·.1) = rs.reverse then some ⟨ps, rs, g.2.1, bytesOf mo, A⟩ else none
      | none => none
    | _, _, _ => none
  | .host _ => none

/-- The summary of function export `j` of a computed instance. -/
def fnSumUI (fuel : Nat) (I : ScalarInstance) (j : Nat) : Option FnSumX :=
  match I.exports[j]?, I.store.funcs[I.addrs.getD j 0]? with
  | some ft, some fi => sumOfU fuel I.store ft fi
  | _, _ => none

/-- **The summary of function export `j` of `m`'s computed instance**, loops unrolled. -/
def fnSumU? (fuel : Nat) (m : Module) (j : Nat) : Option FnSumX :=
  match instance? m with
  | some (_, I) => fnSumUI fuel I j
  | none => none

/-! ## The check -/

/-- **The check of two summaries**: the same parameter types and global values, and either both
always trap (a dead guard on each side), or the same guard keys (as sets), the same initial
memory when either result may depend on it, and equal simplified results. -/
def sumCheckU : Option FnSumX → Option FnSumX → Bool
  | some A, some B =>
    A.params == B.params && decide (A.gvals = B.gvals) &&
      ((anyDead A.final.guards && anyDead B.final.guards) ||
        ((!(usesMem A.final || usesMem B.final) || decide (A.bytes = B.bytes)) &&
          (keys A.final.guards).all (keys B.final.guards).contains &&
          (keys B.final.guards).all (keys A.final.guards).contains &&
          decide (slots2 A.final.stack = slots2 B.final.stack)))
  | _, _ => false

/-- The check at export `j` of two modules. -/
def fnCheckU (fuel : Nat) (m₁ m₂ : Module) (j : Nat) : Bool :=
  sumCheckU (fnSumU? fuel m₁ j) (fnSumU? fuel m₂ j)

/-- **The check on the exports `js`**, each module instantiated once (entry `i` for export
`js[i]`). -/
def checkAmongU (fuel : Nat) (m₁ m₂ : Module) (js : List Nat) : List Bool :=
  match instance? m₁, instance? m₂ with
  | some (_, I₁), some (_, I₂) => js.map fun j => sumCheckU (fnSumUI fuel I₁ j) (fnSumUI fuel I₂ j)
  | _, _ => []

/-! ## The front end -/

/-- Turn a report without a verdict into a proof (stage `equivu`) when `ok` holds. -/
def upgradeU (r : Silmaril.Wasm.Auto.Front.Report) (ok : Bool) : Silmaril.Wasm.Auto.Front.Report :=
  if r.verdict == .unknown && ok then ⟨.proved, .stage "equivu"⟩ else r

/-- **The front end for equivalence**: round 3's (`Front.checkEquiv`), then this check. -/
def checkEquivU (R : Silmaril.Wasm.Auto.Front.Rel) (m₁ m₂ : Module) (j : Nat) (nRand : Nat)
    (identical : Bool) : Silmaril.Wasm.Auto.Front.Report :=
  upgradeU (Silmaril.Wasm.Auto.Front.checkEquiv R m₁ m₂ j nRand identical) (fnCheckU defFuel m₁ m₂ j)

/-- **The front end for a refinement**: round 3's, then this check (which proves equivalence). -/
def checkRefinesU (R : Silmaril.Wasm.Auto.Front.Rel) (impl spec : Module) (j : Nat) (nRand : Nat)
    (identical : Bool) : Silmaril.Wasm.Auto.Front.Report :=
  upgradeU (Silmaril.Wasm.Auto.Front.checkRefines R impl spec j nRand identical)
    (fnCheckU defFuel impl spec j)

/-- The proving stages alone (no differential testing). -/
def proveStageU (m₁ m₂ : Module) (j : Nat) : Silmaril.Wasm.Auto.Front.Report :=
  upgradeU (Silmaril.Wasm.Auto.Front.proveStage m₁ m₂ j) (fnCheckU defFuel m₁ m₂ j)

end Silmaril.Wasm.Auto2.Summ
