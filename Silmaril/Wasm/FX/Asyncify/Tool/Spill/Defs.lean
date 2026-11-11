module

public import Silmaril.Wasm.FX.Asyncify.Tool.Elide.Defs

/-!
# Operands live across calls: spilling to locals before the asyncify pass

The statement form of `Silmaril.Wasm.FX.Asyncify.Tool.Frag` needs an empty operand stack at every
call: arguments come from `local.get`s, results go to `local.set`s. Code that keeps operands on
the stack across a call (`local.get 0; local.get 1; call $f; i32.add`) is first brought into
that form by **spilling**, a source-to-source pass on the frame machine:

* a function in **segmented form** (`FnSeg`) is pure code `c₀`, then call sites, each followed by
  pure code (`flatCalls`); a call site (`Site`) records the callee, the stack depth `d` at the call
  (arguments included), the arguments `n` and the results `m`; `chainOk` checks the depths;
* the spilled function has `T = maxD + maxM` more locals (`B = nloc` is the first): at a site,
  `spillPre` stores the `d` operands in temporaries `B, …, B + d - 1` (`local.set`, deepest
  first) and reloads the `n` arguments; after the call, `spillPost` stores the `m` results at
  `B + maxD, …`, reloads the `d - n` live operands, then the results.

The spilled code is in statement form (argument and result temporaries are locals), so the
asyncify pass applies to it. `segmentEnv` reads a machine program in segmented form;
`asyncifyS` (and `asyncifyBytesS` on bytes) is the tool on the wider fragment: segment, spill,
recognise the statement form (`progOf`), elide checks, transform. Theorems in
`Silmaril.Wasm.FX.Asyncify.Tool.Spill.Thms` (`spill_beh`: the spilled program has the source's
behaviours).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- A call site: the callee, the stack depth `d` at the call (arguments included), the arguments
`n` and the results `m`. -/
structure Site where
  f : FuncIdx
  d : Nat
  n : Nat
  m : Nat
  deriving Repr

/-- A function in segmented form: pure code, then call sites each followed by pure code. -/
structure FnSeg where
  nparams : Nat
  nlocals : Nat
  nres : Nat
  c0 : List Instr
  calls : List (Site × List Instr)
  deriving Repr

/-- The flat code of call sites and the code after them. -/
def flatCalls : List (Site × List Instr) → List Instr
  | [] => []
  | (s, c) :: r => .call s.f :: (c ++ flatCalls r)

/-- The flat body. -/
def FnSeg.body (g : FnSeg) : List Instr := g.c0 ++ flatCalls g.calls

/-- The number of locals (parameters included); the first temporary. -/
def FnSeg.nloc (g : FnSeg) : Nat := g.nparams + g.nlocals

/-- The most operands at a call site. -/
def FnSeg.maxD (g : FnSeg) : Nat := (g.calls.map fun x => x.1.d).foldr max 0

/-- The most results of a call site. -/
def FnSeg.maxM (g : FnSeg) : Nat := (g.calls.map fun x => x.1.m).foldr max 0

/-- The number of temporaries. -/
def FnSeg.ntmp (g : FnSeg) : Nat := g.maxD + g.maxM

/-- Temporaries `B + a, …, B + a + k - 1`. -/
def tv (B a k : Nat) : List LocalIdx := (List.range k).map fun j => lidx (B + a + j)

/-- Before a call: store the `d` operands, reload the `n` arguments. -/
def spillPre (B : Nat) (s : Site) : List Instr :=
  setsCode (tv B 0 s.d) ++ getsCode (tv B (s.d - s.n) s.n)

/-- After a call: store the `m` results at `B + D`, reload the live operands, then the results. -/
def spillPost (B D : Nat) (s : Site) : List Instr :=
  setsCode (tv B D s.m) ++ getsCode (tv B 0 (s.d - s.n)) ++ getsCode (tv B D s.m)

/-- The spilled code of call sites and the code after them. -/
def spCalls (B D : Nat) : List (Site × List Instr) → List Instr
  | [] => []
  | (s, c) :: r => spillPre B s ++ .call s.f :: (spillPost B D s ++ c ++ spCalls B D r)

/-- The spilled body. -/
def FnSeg.spBody (g : FnSeg) : List Instr := g.c0 ++ spCalls g.nloc g.maxD g.calls

/-- The machine function. -/
def FnSeg.toDef (g : FnSeg) : FnDef := ⟨g.nparams, g.nlocals, g.nres, g.body⟩

/-- The spilled machine function. -/
def FnSeg.spDef (g : FnSeg) : FnDef := ⟨g.nparams, g.nlocals + g.ntmp, g.nres, g.spBody⟩

/-- Arity and result count of function index `f` of a machine program. -/
def Env.sig (E : Env) (f : Nat) : Option (Nat × Nat) :=
  if h : f < E.imps.length then some E.imps[f]
  else (E.fns[f - E.imps.length]?).map fun fn => (fn.nparams, fn.nres)

/-- The depths of segmented code: `d` operands at the start of `q`, then the call sites `r`. -/
def chainOk (sig : Nat → Option (Nat × Nat)) (B nres : Nat) :
    Nat → List Instr → List (Site × List Instr) → Bool
  | d, q, [] => q.all (pureIns B) && depthAfter q d == some nres
  | d, q, (s, c) :: r =>
    q.all (pureIns B) && depthAfter q d == some s.d && sig s.f.value.val == some (s.n, s.m) &&
      decide (s.n ≤ s.d) && chainOk sig B nres (s.d - s.n + s.m) c r

/-- The checks of a segmented function (the bound keeps temporaries' indices below `2 ^ 32`). -/
def FnSeg.ok (sig : Nat → Option (Nat × Nat)) (g : FnSeg) : Bool :=
  chainOk sig g.nloc g.nres 0 g.c0 g.calls && decide (g.nloc + g.ntmp < 2 ^ 32)

/-- The machine program of segmented functions. -/
def segEnv (imps : List (Nat × Nat)) (gs : List FnSeg) : Env := ⟨imps, gs.map FnSeg.toDef⟩

/-- The spilled machine program. -/
def spEnv (imps : List (Nat × Nat)) (gs : List FnSeg) : Env := ⟨imps, gs.map FnSeg.spDef⟩

/-! ## Reading the segmented form -/

/-- Split code at its first `call`: the code before it, then the callee and the rest. -/
def splitCall : List Instr → List Instr × Option (FuncIdx × List Instr)
  | [] => ([], none)
  | .call f :: r => ([], some (f, r))
  | i :: r =>
    match splitCall r with
    | (q, x) => (i :: q, x)

/-- The call sites of code after a call to `f` with `d` operands before it (`fuel`: the length). -/
def sitesOf (sig : Nat → Option (Nat × Nat)) : Nat → Nat → FuncIdx → List Instr →
    Option (List (Site × List Instr))
  | 0, _, _, _ => none
  | fuel + 1, d, f, r => do
    let (n, m) ← sig f.value.val
    let (c, x) := splitCall r
    let s : Site := ⟨f, d, n, m⟩
    match x with
    | none => pure [(s, c)]
    | some (f', r') =>
      let d' ← depthAfter c (d - n + m)
      let rest ← sitesOf sig fuel d' f' r'
      pure ((s, c) :: rest)

/-- The segmented form of a machine function. -/
def segFn (sig : Nat → Option (Nat × Nat)) (fn : FnDef) : Option FnSeg := do
  let (c0, x) := splitCall fn.body
  match x with
  | none => pure ⟨fn.nparams, fn.nlocals, fn.nres, c0, []⟩
  | some (f, r) =>
    let d ← depthAfter c0 0
    let calls ← sitesOf sig (fn.body.length + 1) d f r
    pure ⟨fn.nparams, fn.nlocals, fn.nres, c0, calls⟩

/-- The segmented form of a machine program, checked: it flattens to the program and its depths
are consistent. -/
def segmentEnv (E : Env) : Option (List FnSeg) := do
  let gs ← E.fns.mapM (segFn E.sig)
  if fnDefsEqb (gs.map FnSeg.toDef) E.fns && gs.all (FnSeg.ok E.sig) then some gs else none

/-! ## The tool on the wider fragment -/

/-- Asyncify a module whose functions are in segmented form: segment, spill, recognise the
statement form of the spilled program, elide checks, transform. -/
def asyncifyS (m : Module) (pages : Nat := 1) : Except String Module :=
  match envOf m with
  | none => .error "not in the fragment: only i32 function imports and i32 functions, no globals, memories, tables, tags, segments or start"
  | some E =>
    match segmentEnv E with
    | none => .error "not in the fragment: function bodies must be pure i32 code and calls, with consistent stack depths"
    | some gs =>
      let P := progOf (spEnv E.imps gs)
      if envEqb P.env (spEnv E.imps gs) && P.wf then
        if m.exports.any (fun e => e.name == stateExport || e.name == memoryExport) then
          .error "the module already exports asyncify_state or asyncify_memory"
        else if P.elide.sb + 4 * P.elide.frameWords ≤ 65536 * pages ∧ pages < 65536 then
          .ok (asyncifyModule m P.elide pages)
        else .error "the memory cannot hold the request area and one frame"
      else .error "internal: the spilled program is not in statement form"

/-- The tool: statement form if the module is in it (no spilling), else the segmented form. -/
def asyncifyW (m : Module) (pages : Nat := 1) : Except String Module :=
  match asyncifyE m pages with
  | .ok m' => .ok m'
  | .error _ => asyncifyS m pages

/-- Decode, asyncify (statement form or segmented form, checks elided), encode. -/
def asyncifyBytesW (b : ByteArray) (pages : Nat := 1) : Except String ByteArray :=
  match Binary.Core.decode? b with
  | none => .error "the input does not decode as a Core module"
  | some m =>
    match asyncifyW m pages with
    | .error e => .error e
    | .ok m' =>
      match Binaryen.Exe.encodeModule? m' with
      | .ok bs => .ok ⟨bs.toArray⟩
      | .error e => .error s!"encoding failed: {e}"

end Silmaril.Wasm.FX.Asyncify.Tool
