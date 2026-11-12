module

public import Silmaril.Wasm.Verify.Check.Defs
public import Silmaril.Wasm.Verify.Split.Defs

@[expose] public section

/-!
# Per-export reachability: "import `i` is never called while export `e` is active"

`checkFrom m i e : Report` decides, conservatively, the specification sentence
`neverCallFrom (i, e)` of `Silmaril.Wasm.Spec` (`NeverCallFrom.holds`: no import call of `i`
while the call of export `e` is pending) for a start-free Core 3.0 module `m`, directly,
not only through `neverCall i`.

## The analysis

On the store `s` of the instance (`instantiateOnce?` into `importStore`, as for `check`):

1. `A`: the functions reachable from every root (`closure s fs (rootsOf s addrs)`, as `check`);
   every function that can ever run.
2. `V` (`escapes`): the **escaping** functions, whose references may appear as values: the
   function references held by the store (`storeFuncs`) and the `ref.func` targets of the
   bodies of the functions of `A` (`rfSuccs`). Exports are not escaping by themselves: the
   reference of an export call is consumed by its `call_ref` (a transient reference).
3. `Ce`: the functions **callable** while export `e` is active: the closure of `e`'s function
   and of `V` (indirect calls may call any escaping function) under direct calls,
   `return_call` and `ref.func` (`succs`).

**Certificate check** (`fromB`; soundness depends only on it): `A` and `Ce` are closed
(`closedB`) and name with `ref.func` only functions of `V` (`rfClosedB`); `A` contains every
export and `V`; `V` contains the references of the store; `Ce` contains `e`'s function and
`V`; `Ce` avoids import `i` (`avoidsB`). Then `checkFrom` is `proved`, with reason
`unreachableFrom Ce V`. The soundness argument (`Silmaril.Wasm.Verify.From.Thms`) splits the
reachability invariant into the escaping set `V` (values, store, locals) and the callable sets
(`Silmaril.Wasm.Verify.Split`): `Cs j = Ce` for `j = e`, `A` for the other exports.

Otherwise the refuter tries the export `e` alone (`refuteFrom`, candidate arguments `0` and
`1`): a host-free run of the call of `e` reaching a callout of `i` is a play
`[call e args, icall i args']`, so the sentence fails (`refuted`). Else `unknown`, with a call
path from `e`'s function or an escaping function to the import (`reaches`).

Modules with a start function give `unknown` (`startFunction`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The `ref.func` targets of the body of the function at address `a`. -/
def rfSuccs (s : Store Nat) (fs : List Nat) (a : Nat) : List Nat :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm code => (exprRefFuncs code.body).filterMap fun x => fs[x]?
    | .host _ => []
  | none => []

/-- The list without repetitions, in order of first occurrence. -/
def dedupNats (l : List Nat) : List Nat :=
  l.foldl (fun acc b => if acc.contains b then acc else acc ++ [b]) []

/-- The escaping functions: references of the store and `ref.func` targets of the functions
of `A`. -/
def escapes (s : Store Nat) (fs A : List Nat) : List Nat :=
  dedupNats (storeFuncs s ++ A.flatMap (rfSuccs s fs))

/-- Every function of `G` names with `ref.func` only functions of `V`. -/
def rfClosedB (s : Store Nat) (fs V G : List Nat) : Bool :=
  G.all fun a => (rfSuccs s fs a).all V.contains

/-- The certificate check of the per-export analysis. -/
def fromB (s : Store Nat) (fs addrs : List Nat) (i a : Nat) (A V Ce : List Nat) : Bool :=
  closedB s fs A && rfClosedB s fs V A && rootsB A addrs && rootsB A V &&
    rootsB V (storeFuncs s) && closedB s fs Ce && rfClosedB s fs V Ce && rootsB Ce (a :: V) &&
    avoidsB s Ce i

/-- The refuter for export `e` alone: a run of a call of export `e` (candidates `0`, `1`)
stopping at a bad call of host function `i`. -/
def refuteFrom (s : Store Nat) (addrs : List Nat) (imp : FnType) (i : Nat) (bad : List Val → Bool)
    (e : Nat) : Option Cex :=
  [(e, 0), (e, 1)].findSome? (tryExport s addrs imp i bad)

/-- The decision for "never calls import `i` while export `e` is active" on an instantiated
store without a start function. -/
def decideFrom (s : Store Nat) (fs addrs : List Nat) (i e : Nat) (imp : Option FnType) :
    Report :=
  let a := addrs.getD e 0
  let A := closure s fs (rootsOf s addrs)
  let V := escapes s fs A
  let Ce := closure s fs (a :: V)
  if fromB s fs addrs i a A V Ce then ⟨.proved, .unreachableFrom Ce V⟩
  else
    match imp.bind fun ft => refuteFrom s addrs ft i anyCall e with
    | some x => ⟨.refuted, .counterexample x⟩
    | none =>
      match (paths s fs (a :: V)).find? (fun (b, _) => isHost s i b) with
      | some (_, p) => ⟨.unknown, .reaches p.reverse⟩
      | none => ⟨.unknown, .notClosed⟩

/-- **The per-export verifier**: "import `i` is never called while export `e` (an index into
the function exports) is active". -/
def checkFrom (m : Module) (i e : Nat) : Report :=
  match validate? m with
  | none => ⟨.unknown, .invalidModule⟩
  | some mt =>
    if !(mt.imports.all isFuncImport) then ⟨.unknown, .nonFunctionImport⟩
    else if mt.imports.length ≤ i then ⟨.unknown, .importOutOfRange⟩
    else if m.start.isSome then ⟨.unknown, .startFunction ((checkSpec m mt i).verdict != .proved)⟩
    else
      match instantiateOnce? (importStore (CExternType.funcs mt.imports)) m
          ((List.range mt.imports.length).map ExternAddr.func) with
      | none => ⟨.unknown, .instantiationFailed⟩
      | some (s, f, none) =>
        if (exportFuncAddrs f.module).length ≤ e then ⟨.unknown, .exportOutOfRange⟩
        else decideFrom s f.module.funcs (exportFuncAddrs f.module) i e (importType? mt i)
      | some (_, _, some _) => ⟨.unknown, .startFunction true⟩

end Silmaril.Wasm.Verify
