module

public import Silmaril.Wasm.Binaryen.Exe.InlineExe
public import Silmaril.Wasm.Binaryen.FastChecks

@[expose] public section

/-! # Memoized callee checks for the executable inliner

`inlineStep` evaluates `calleeOkWith` at every direct call it meets while searching
for a site, and each evaluation computes the callee's effects, size and depth (and
lowers its body to measure it). A module with many calls to a few large functions
(an interpreter's helpers) pays for the same callee again and again on every step.

`inlineStepFast` builds, once per step, one lazily evaluated answer per function
index (`okTable`, an `Array (Thunk Bool)`), so each callee is checked at most once
per step, and checks it without lowering it or building its effect lists
(`calleeOkFast`). It is proved equal to `inlineStep` (`inlineStep_eq_fast`), and both
`inlineStep` and `inlineSmall` are replaced in compiled code (`@[csimp]`), so outputs
are unchanged and every theorem about `Inl.inlineSmall` still applies.
-/

namespace Silmaril.Wasm.Binaryen.Exe.Inl

open Silmaril.Wasm Silmaril.Wasm.Binaryen

/-- `calleeOkWith` on a raw function index. -/
def calleeOkN (once : Nat → Bool) (budget : Nat) (m : BModule) (n : Nat) : Bool :=
  match m.defFunc? n with
  | none => false
  | some fn =>
      let e := effectsList fn.body
      (decide (bodySize fn.body ≤ budget) || (budget != 0 && once n)) &&
        !e.any && (!e.branchesOut || decide (depthL fn.body < 2 ^ 32)) && !e.calls

theorem calleeOkWith_eq_N (once : Nat → Bool) (budget : Nat) (m : BModule) (f : FuncIdx) :
    calleeOkWith once budget m f = calleeOkN once budget m f.toNat := rfl

/-! ## The callee check without lowering or effect lists

The check reads the lowered size of the body and three flags of its effects. The size
is counted on the trees (a structured node lowers to one instruction), and the flags
are or-ed over the operators, without building the effect lists (`flagsL`,
`Binaryen/FastChecks.lean`). The effects are only
read when the size test passes. -/

mutual
/-- Length of the lowering of a tree. -/
def sizeE : BExpr → Nat
  | .op _ args => sizeL args + 1
  | .block .. | .loop .. | .tryTable .. => 1
  | .if_ _ c _ _ => sizeL c + 1
/-- Length of the lowering of a sequence. -/
def sizeL : List BExpr → Nat
  | [] => 0
  | e :: es => sizeE e + sizeL es
end

mutual
theorem sizeE_eq : ∀ e : BExpr, sizeE e = e.lower.length
  | .op _ args => by simp [sizeE, BExpr.lower, sizeL_eq args, bodySize]
  | .block .. | .loop .. | .tryTable .. => by simp [sizeE, BExpr.lower]
  | .if_ _ c _ _ => by simp [sizeE, BExpr.lower, sizeL_eq c, bodySize]
theorem sizeL_eq : ∀ es : List BExpr, sizeL es = bodySize es
  | [] => rfl
  | e :: es => by
      simp only [sizeL, bodySize, BExpr.lowerList_cons, List.length_append, sizeE_eq e]
      rw [sizeL_eq es, bodySize]
end

/-- `calleeOkN`, reading the size and the flags directly. -/
def calleeOkFast (once : Nat → Bool) (budget : Nat) (m : BModule) (n : Nat) : Bool :=
  match m.defFunc? n with
  | none => false
  | some fn =>
      if decide (sizeL fn.body ≤ budget) || (budget != 0 && once n) then
        let (a, b, c) := flagsL fn.body
        !a && (!b || decide (depthL fn.body < 2 ^ 32)) && !c
      else false

theorem calleeOkFast_eq (once : Nat → Bool) (budget : Nat) (m : BModule) (n : Nat) :
    calleeOkFast once budget m n = calleeOkN once budget m n := by
  unfold calleeOkFast calleeOkN
  split
  · rfl
  · rw [sizeL_eq, flagsL_eq]
    cases (decide (bodySize _ ≤ budget) || (budget != 0 && once n)) <;> simp [flagsOf]

/-- One lazily evaluated callee check per imported or defined function. -/
def okTable (once : Nat → Bool) (budget : Nat) (m : BModule) : Array (Thunk Bool) :=
  Array.ofFn (n := m.numImportedFuncs + m.funcs.length) fun i =>
    Thunk.mk fun _ => calleeOkFast once budget m i

/-- The callee check read from a table, recomputed for indices outside it. -/
def okCached (tbl : Array (Thunk Bool)) (once : Nat → Bool) (budget : Nat) (m : BModule)
    (f : FuncIdx) : Bool :=
  if h : f.toNat < tbl.size then tbl[f.toNat].get else calleeOkFast once budget m f.toNat

theorem okCached_okTable (once : Nat → Bool) (budget : Nat) (m : BModule) :
    okCached (okTable once budget m) once budget m = calleeOkWith once budget m := by
  funext f
  simp only [okCached, okTable, Array.size_ofFn, Array.getElem_ofFn, Thunk.get, calleeOkWith_eq_N,
    calleeOkFast_eq]
  split <;> rfl

/-- `inlineStep` with one memoized callee table per step. The table is bound before
the search predicate is built, so compiled code shares it across queries. -/
def inlineStepFast (budget : Nat) (m : BModule) : Option BModule :=
  let counts := if budget = 0 then #[] else moduleCallCounts m
  let once := calledOnceWith counts m
  let tbl := okTable once budget m
  match findSite (okCached tbl once budget m) m with
  | some (g, K, args, f) => inlineSite m g K args f
  | none => none

/-- `inlineSmall` through `inlineStepFast`. -/
def inlineSmallFast (budget : Nat) : Nat → BModule → BModule
  | 0, m => m
  | fuel + 1, m =>
    match inlineStepFast budget m with
    | some m' => inlineSmallFast budget fuel m'
    | none => m

/-- Compiled code runs the memoized step. -/
@[csimp] theorem inlineStep_eq_fast : @inlineStep = @inlineStepFast := by
  funext budget m
  simp only [inlineStep, inlineStepFast, okCached_okTable]
  rfl

/-- Compiled code runs the memoized loop. -/
@[csimp] theorem inlineSmall_eq_fast : @inlineSmall = @inlineSmallFast := by
  funext budget fuel
  induction fuel with
  | zero => funext m; rfl
  | succ fuel ih =>
    funext m
    simp only [inlineSmall, inlineSmallFast, ← inlineStep_eq_fast, ih]
    rfl

end Silmaril.Wasm.Binaryen.Exe.Inl
