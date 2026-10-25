module

public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Binaryen.Exe.InlineCallCounts

@[expose] public section

/-! # The executable inliner (milestone P2 of `binaryen-lean`)

`Binaryen/Inline.lean` and `Binaryen/InlineDefs.lean` cannot be imported by the
executable: their import closure contains `NTyping.lean`'s
`Counterexample.overflowFunc`, a closed term holding `List.replicate (2 ^ 32 + 1) .i32`,
which the compiled program evaluates when it initialises its imports (it runs out of
memory before `main`). This file therefore carries verbatim copies of the layer-D
inlining definitions (`shiftIdx`, `labelIdx`, `shiftLocalInstr`, `shiftLocalsE/L`,
`retToBrE/L`, `zeroInstr`, `siteCode`, `inlineSite`) in the namespace `Exe.Inl`;
`Exe/PipelineSound.lean` proves each copy equal to the original
(`Inl.inlineSite_eq`), so the theorems about `Binaryen.inlineSite` apply.

On top of that, `inlineSmall budget fuel`:

* `findSite` looks for a direct call `op (call f) args` in a body, returned as a
  one-hole context `K` with `K.plug [op (call f) args] = body` (`findSite_spec`); the
  first function, then the first call in evaluation order;
* the callee must pass `calleeOk`: a defined function whose body has at most
  `budget` lowered instructions or that is called exactly once (`calledOnce`; only
  for `budget ≠ 0`), and whose effects have `any = false` (inside the
  profile, hence structured and free of tail calls), either `branchesOut = false` (no
  `return`, so `retToBrL` has nothing to rewrite) or a nesting depth below `2 ^ 32`
  (`retToBrL` turns each `return` into the exact branch out of the inlined block), and
  `calls = false` (a leaf: non-recursive by construction; iterating inlines
  bottom-up, as a mid-level function becomes a leaf once its callees are inlined);
* the site is replaced by `inlineSite` (which re-zeroes the callee's locals, so it
  fails on non-defaultable locals), at most `fuel` times. The loop stops at the first
  site whose `inlineSite` fails. Callees left without references are deleted later
  by RUME.
-/

namespace Silmaril.Wasm.Binaryen.Exe.Inl

open Silmaril.Wasm Silmaril.Wasm.Binaryen Validation

/-! ## Copies of `Binaryen/InlineDefs.lean` and `Binaryen.inlineSite` -/

/-- Copy of `Binaryen.shiftIdx`. -/
def shiftIdx {k : IndexKind} (base : Nat) (x : Idx k) : Idx k :=
  (Idx.ofNat? (x.toNat + base)).getD x

/-- Copy of `Binaryen.labelIdx`. -/
def labelIdx (d : Nat) : LabelIdx := (Idx.ofNat? d).getD ⟨⟨0, by decide⟩⟩

/-- Copy of `Binaryen.shiftLocalInstr`. -/
def shiftLocalInstr (base : Nat) : Instr → Instr
  | .localGet x => .localGet (shiftIdx base x)
  | .localSet x => .localSet (shiftIdx base x)
  | .localTee x => .localTee (shiftIdx base x)
  | i => i

mutual
/-- Copy of `Binaryen.shiftLocalsE`. -/
def shiftLocalsE (base : Nat) : BExpr → BExpr
  | .op i args => .op (shiftLocalInstr base i) (shiftLocalsL base args)
  | .block bt b => .block bt (shiftLocalsL base b)
  | .loop bt b => .loop bt (shiftLocalsL base b)
  | .if_ bt c t e => .if_ bt (shiftLocalsL base c) (shiftLocalsL base t) (shiftLocalsL base e)
  | .tryTable bt cs b => .tryTable bt cs (shiftLocalsL base b)
/-- Copy of `Binaryen.shiftLocalsL`. -/
def shiftLocalsL (base : Nat) : List BExpr → List BExpr
  | [] => []
  | e :: es => shiftLocalsE base e :: shiftLocalsL base es
end

mutual
/-- Copy of `Binaryen.retToBrE`. -/
def retToBrE (d : Nat) : BExpr → BExpr
  | .op .return_ args => .op (.br (labelIdx d)) (retToBrL d args)
  | .op i args => .op i (retToBrL d args)
  | .block bt b => .block bt (retToBrL (d + 1) b)
  | .loop bt b => .loop bt (retToBrL (d + 1) b)
  | .if_ bt c t e => .if_ bt (retToBrL d c) (retToBrL (d + 1) t) (retToBrL (d + 1) e)
  | .tryTable bt cs b => .tryTable bt cs (retToBrL (d + 1) b)
/-- Copy of `Binaryen.retToBrL`. -/
def retToBrL (d : Nat) : List BExpr → List BExpr
  | [] => []
  | e :: es => retToBrE d e :: retToBrL d es
end

/-- Copy of `Binaryen.zeroInstr`. -/
def zeroInstr : ValType → Option Instr
  | .num (.int t) => some (.intConst t 0)
  | .num (.float t) => some (.floatConst t 0)
  | .vec _ => some (.vecConst 0)
  | .ref _ => none

/-- Copy of `Binaryen.siteCode`. -/
def siteCode (ty : TypeIdx) (base np : Nat) (ls : List ValType) (args body : List BExpr) :
    Option (List BExpr) := do
  let sets ← (List.range np).reverse.mapM fun j => do
    let x : LocalIdx ← Idx.ofNat? (base + j)
    pure (BExpr.op (.localSet x) [])
  let zeros ← (List.range ls.length).mapM fun j => do
    let t ← ls[j]?
    let z ← zeroInstr t
    let x : LocalIdx ← Idx.ofNat? (base + np + j)
    pure (BExpr.op (.localSet x) [.op z []])
  let body' := retToBrL 0 (shiftLocalsL base body)
  pure (args ++ [BExpr.block (.typeIdx ty) (sets ++ zeros ++ body')])

/-- Copy of `Binaryen.inlineSite`: inline the call `call f args` found at context `K`
of defined function `g`. -/
def inlineSite (m : BModule) (g : Nat) (K : BCtx) (args : List BExpr) (f : FuncIdx) :
    Option BModule := do
  let caller ← m.funcs[g]?
  let callee ← m.defFunc? f.toNat
  let cft ← m.funcType? caller.type
  let ft ← m.funcType? callee.type
  let base := cft.params.length + caller.locals.length
  let site ← siteCode callee.type base ft.params.length callee.locals args callee.body
  pure (m.setFunc g { caller with locals := caller.locals ++ ft.params ++ callee.locals,
                                  body := K.plug site })

/-! ## Finding a call site -/

/-- A found site: the hole context, the call's folded operands and the callee. -/
abbrev Site := BCtx × List BExpr × FuncIdx

/-- The callee of a direct call. -/
def callee? : Instr → Option FuncIdx
  | .call f => some f
  | _ => none

mutual
/-- The first call `op (call f) args` with `p f` in a tree, as a context of `[e]`. -/
def siteE (p : FuncIdx → Bool) : BExpr → Option Site
  | .op i args =>
      match callee? i with
      | some f =>
          if p f then some (.hole, args, f) else
            (siteL p args).map fun (K, a, g) => (.op i [] K [], a, g)
      | none => (siteL p args).map fun (K, a, g) => (.op i [] K [], a, g)
  | .block bt b => (siteL p b).map fun (K, a, g) => (.block bt [] K [], a, g)
  | .loop bt b => (siteL p b).map fun (K, a, g) => (.loop bt [] K [], a, g)
  | .if_ bt c t e =>
      match siteL p c with
      | some (K, a, g) => some (.ifCond bt [] K [] t e, a, g)
      | none =>
        match siteL p t with
        | some (K, a, g) => some (.ifThen bt c [] K [] e, a, g)
        | none => (siteL p e).map fun (K, a, g) => (.ifElse bt c t [] K [], a, g)
  | .tryTable .. => none
/-- The first call site in a list. -/
def siteL (p : FuncIdx → Bool) : List BExpr → Option Site
  | [] => none
  | e :: es =>
      match siteE p e with
      | some (K, a, g) => some (.seq [] K es, a, g)
      | none => (siteL p es).map fun (K, a, g) => (.seq [e] K [], a, g)
end

/-- The first defined function (relative index `g`, counting from `g₀`) with a site. -/
def findIn (p : FuncIdx → Bool) : Nat → List BFunc → Option (Nat × Site)
  | _, [] => none
  | g, fn :: fs =>
      match siteL p fn.body with
      | some s => some (g, s)
      | none => findIn p (g + 1) fs

/-- The first call site in a module. -/
def findSite (p : FuncIdx → Bool) (m : BModule) : Option (Nat × Site) := findIn p 0 m.funcs

/-! ## The inlining loop -/

/-- Size of a body in lowered instructions (top level; Binaryen's `Measurer` counts
tree nodes). -/
def bodySize (es : List BExpr) : Nat := (BExpr.lowerList es).length

mutual
/-- Number of direct calls to function `f` in a tree. -/
def callsToE (f : Nat) : BExpr → Nat
  | .op i args => (if callee? i |>.any (·.toNat == f) then 1 else 0) + callsToL f args
  | .block _ b => callsToL f b
  | .loop _ b => callsToL f b
  | .if_ _ c t e => callsToL f c + callsToL f t + callsToL f e
  | .tryTable _ _ b => callsToL f b
/-- Number of direct calls to function `f` in a list. -/
def callsToL (f : Nat) : List BExpr → Nat
  | [] => 0
  | e :: es => callsToE f e + callsToL f es
end

/-- Function `f` is referenced exactly once: by one direct call, and neither exported nor
the start function (inside the profile there are no tables, element segments or
`ref.func`). Inlining it then leaves the original unreferenced, and RUME deletes it, so the
module does not grow by a copy of its body. -/
def calledOnce (m : BModule) (f : Nat) : Bool :=
  !(m.base.exports.any fun e => match e.index with | .func g => g.toNat == f | _ => false) &&
    !(m.base.start.any (·.toNat == f)) &&
    (m.funcs.foldl (fun n fn => n + callsToL f fn.body) 0) == 1

/-- The same call-once test using a module-wide count table. Out-of-range indices
fall back to the original test, preserving its behavior even on malformed IR. -/
def calledOnceWith (counts : Array Nat) (m : BModule) (f : Nat) : Bool :=
    !(m.base.exports.any fun e => match e.index with | .func g => g.toNat == f | _ => false) &&
      !(m.base.start.any (·.toNat == f)) &&
      (if f < counts.size then counts[f]! else
        m.funcs.foldl (fun n fn => n + callsToL f fn.body) 0) == 1

mutual
/-- Copy of `Binaryen.BExpr.depth`: the nesting depth `retToBrE` counts. -/
def depthE : BExpr → Nat
  | .op _ args => depthL args
  | .block _ b => depthL b + 1
  | .loop _ b => depthL b + 1
  | .if_ _ c t e => max (depthL c) (max (depthL t) (depthL e) + 1)
  | .tryTable _ _ b => depthL b + 1
/-- Copy of `Binaryen.BExpr.depthList`. -/
def depthL : List BExpr → Nat
  | [] => 0
  | e :: es => max (depthE e) (depthL es)
end

/-- The callee check of `inlineSmall`: a leaf that is small, or (when inlining at all,
`budget ≠ 0`) called exactly once, as in Binaryen's `Inlining`, which inlines a function
with a single caller whatever its size. A `return` in the callee becomes a branch out of
the inlined block, exact while the nesting depth stays below `2 ^ 32`. -/
def calleeOk (budget : Nat) (m : BModule) (f : FuncIdx) : Bool :=
  match m.defFunc? f.toNat with
  | none => false
  | some fn =>
      let e := effectsList fn.body
      (decide (bodySize fn.body ≤ budget) || (budget != 0 && calledOnce m f.toNat)) &&
        !e.any && (!e.branchesOut || decide (depthL fn.body < 2 ^ 32)) && !e.calls

/-- Callee eligibility with a shared call-once predicate. -/
def calleeOkWith (once : Nat → Bool) (budget : Nat) (m : BModule) (f : FuncIdx) : Bool :=
  match m.defFunc? f.toNat with
  | none => false
  | some fn =>
      let e := effectsList fn.body
      (decide (bodySize fn.body ≤ budget) || (budget != 0 && once f.toNat)) &&
        !e.any && (!e.branchesOut || decide (depthL fn.body < 2 ^ 32)) && !e.calls

/-- One inlining step: the first acceptable site, inlined. -/
def inlineStep (budget : Nat) (m : BModule) : Option BModule :=
  let counts := if budget = 0 then #[] else moduleCallCounts m
  match findSite (calleeOkWith (calledOnceWith counts m) budget m) m with
  | some (g, K, args, f) => inlineSite m g K args f
  | none => none

/-- **Inlining with a size heuristic**: at most `fuel` steps of `inlineStep`. -/
def inlineSmall (budget : Nat) : Nat → BModule → BModule
  | 0, m => m
  | fuel + 1, m =>
    match inlineStep budget m with
    | some m' => inlineSmall budget fuel m'
    | none => m

end Silmaril.Wasm.Binaryen.Exe.Inl
