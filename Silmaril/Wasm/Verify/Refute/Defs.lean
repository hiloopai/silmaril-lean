module

public import Silmaril.Wasm.Spec.Verdict.Defs
public import Silmaril.Wasm.Game.Instance.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun

@[expose] public section

/-!
# Counterexamples to import-call properties

A computable search for **concrete counterexamples** to "import `i` is never called" and "the
assertion `i` is never called with `i32 0`", on an instantiated store:

* `candVal k t`, `candArgs k ps`: the candidate argument `k` (`0` or `1`) of every scalar
  parameter type: the number with bits `k`, the vector with bits `k`, the `i31` reference `k`.
  They are typed by construction (`candArgs_typed`).
* `calloutOf? s a args`: run silmaril-lean's verified interpreter (`runInvoke?`, deterministic
  profile `profile refOracle`, fuel `refFuel`, no host) on `$invoke(a, args)`; if the run stops
  at a host-call redex (`decompose?`), its host function and arguments.
* `refuteStore s addrs imp i bad`: the first export `j` (in export order) and candidate `k` whose
  run stops at a call of host function `i` with arguments `args'` such that `bad args'` holds and
  `args'` are typed by the import type `imp`. The result `Cex` records the export index, the
  export arguments and the import arguments.

The counterexample is a play `[call j args, icall i args']` of the instance's strategy: a host-free
Core run of the export call reaches the callout before any other import call, so the environment
plays no part (every environment admits it). Soundness: `Silmaril.Wasm.Verify.Refute.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Game

/-- The grow oracle of the refuter: `memory.grow` and `table.grow` always fail. -/
def refOracle : GrowOracle := fun _ _ _ _ => false

/-- The fuel of the refuter (interpreter steps per run). -/
def refFuel : Nat := 100000

/-- The candidate value `k` of a scalar type. -/
def candVal (k : Nat) : ScalarType → Val
  | .num t => .num ⟨t, BitVec.ofNat _ k⟩
  | .v128 => .vec (BitVec.ofNat _ k)
  | .i31 _ => .ref (.i31 (BitVec.ofNat _ k))

/-- The candidate arguments `k` of a list of parameter types. -/
def candArgs (k : Nat) (ps : List ScalarType) : List Val := ps.map (candVal k)

/-- The scalar function type of the function at address `a`. -/
def funcType? (s : Store Nat) (a : Nat) : Option FnType :=
  s.funcs[a]?.bind fun fi => FnType.ofDefType? fi.type

/-- Run the export call `$invoke(a, args)` with the verified interpreter; if it stops at a
host-call redex, the host function and its arguments. -/
def calloutOf? (s : Store Nat) (a : Nat) (args : List Val) : Option (Nat × List Val) :=
  match Silmaril.Wasm.SingleThreaded.Exec.runInvoke? refOracle refFuel s a args with
  | some (c, _, _) =>
    match decompose? c.store c.code with
    | some (_, _, h, args') => some (h, args')
    | none => none
  | none => none

/-- A counterexample: export `exp` (an index into the function exports) called with `args`
calls the import with `callArgs`. -/
structure Cex where
  /-- The export index. -/
  exp : Nat
  /-- The arguments of the export call. -/
  args : List Val
  /-- The arguments of the import call. -/
  callArgs : List Val
  deriving DecidableEq, Repr

/-- Try the export at index `j` with candidate `k`. -/
def tryExport (s : Store Nat) (addrs : List Nat) (imp : FnType) (i : Nat)
    (bad : List Val → Bool) (jk : Nat × Nat) : Option Cex :=
  (addrs[jk.1]?).bind fun a => (funcType? s a).bind fun ft =>
    (calloutOf? s a (candArgs jk.2 ft.params)).bind fun r =>
      if r.1 == i && bad r.2 && Silmaril.Wasm.Spec.typedB imp.params r.2 then
        some ⟨jk.1, candArgs jk.2 ft.params, r.2⟩
      else none

/-- The export/candidate pairs tried by the refuter. -/
def tries (n : Nat) : List (Nat × Nat) := (List.range n).flatMap fun j => [(j, 0), (j, 1)]

/-- **The refuter** on an instantiated store with export addresses `addrs`: a counterexample
whose import call (of host function `i`, of type `imp`) has arguments satisfying `bad`. -/
def refuteStore (s : Store Nat) (addrs : List Nat) (imp : FnType) (i : Nat)
    (bad : List Val → Bool) : Option Cex :=
  (tries addrs.length).findSome? (tryExport s addrs imp i bad)

/-- Any call is bad (for "never called"). -/
def anyCall (_ : List Val) : Bool := true

/-- A call whose first argument is `i32 0` (for assertions). -/
def falseCall (args : List Val) : Bool := args.head? == some (Val.i32 0)

end Silmaril.Wasm.Verify
