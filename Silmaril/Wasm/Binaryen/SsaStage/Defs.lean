module

public import Silmaril.Wasm.SSA.CoreCert.Defs

@[expose] public section

/-! # The SSA optimiser as an opt-in `wasm-opt` stage: run functions

Wraps the Wasm lambda-SSA optimiser of `Silmaril.Wasm.SSA` (owned by that topic; only its
`Defs`/`Thms` headers are used here). Each defined function is optimised independently
against the *input* module with the **export-certified** entry point
`SSA.optimizeFuncExport`: the arity-guarded optimiser, the run-time checks `coreReady` on source
and result, the local certificate `SSA.runCert` of the source (the function is a store-free
leaf; the module is closed and valid; the module with every other function replaced by
`unreachable` validates, and its allocated store passes the executable arity and native-profile
checks and allocates the function like the module does), and source and result strict leaf
functions (`SSA.strictFunc`: no block type is a type index). The combined module is kept only
when `ssaAccept` holds: it is closed and valid, and every rewritten function passes
`SSA.runCert` in it; else the input is returned unchanged.

**Certificate class: exact export equivalence at every numerical profile** (closed host;
`StageCert.anyProfile`, `Silmaril.Wasm.Binaryen.SsaStage.Thms`): validity of the output and
`ExportEquiv (· = ·) P closedHost` of output and input (`SSA.replace_exportEquiv`, through the
caller-side simulation `SSA.behaviours_srel`), together with the per-function guarantees of
`SsaSpec`. Only the rewritten functions themselves need to be integer-only strict leaf code;
modules with imports are returned unchanged (`runCert` needs a closed module).
-/

namespace Silmaril.Wasm.Binaryen.SsaStage

open Silmaril.Wasm.Binaryen

/-- Candidate replacements, each Core-certified against the input module. -/
def ssaFuncs (m : BModule) : List BFunc :=
  m.funcs.mapIdx fun g f => (Silmaril.Wasm.SSA.optimizeFuncExport m g).getD f

/-- The source type of defined function `g`, if any. -/
def srcType? (m : BModule) (g : Nat) : Option Silmaril.Wasm.FuncType :=
  m.funcs[g]? >>= fun bf => m.funcType? bf.type

/-- The check of the combined module: closed and valid, and every rewritten function passes the
local certificate `runCert` in it at its source type. -/
def ssaAccept (m m' : BModule) : Bool :=
  Silmaril.Wasm.SSA.closedValid m' && (List.range m.funcs.length).all fun g =>
    !(Silmaril.Wasm.SSA.optimizeFuncExport m g).isSome ||
      match srcType? m g, m'.funcs[g]? with
      | some ft, some bf' => Silmaril.Wasm.SSA.runCert m' g ft bf'
      | _, _ => false

/-- **The SSA stage**: all accepted replacements, kept when the combined module passes
`ssaAccept`. Modules with imports are returned at once (no function could be certified). -/
def ssaRun (m : BModule) : BModule :=
  if !Silmaril.Wasm.SSA.closedValid m then m else
  let m' : BModule := { m with funcs := ssaFuncs m }
  if ssaAccept m m' then m' else m

/-- Per-function report: `(index, rewritten with a Core certificate?)`. -/
def ssaReport (m : BModule) : List (Nat × Bool) :=
  (List.range m.funcs.length).map fun g =>
    (g, (Silmaril.Wasm.SSA.optimizeFuncExport m g).isSome)

/-- Is defined function `g` in the fragment at all (recognised by `ofBFunc?`)? -/
def inFragment (m : BModule) (g : Nat) : Bool :=
  match m.funcs[g]? with
  | none => false
  | some bf => match m.funcType? bf.type with
    | none => false
    | some ft => (Silmaril.Wasm.SSA.ofBFunc? ft bf).isSome

/-- Would the validator-guarded optimiser (`optimizeFuncChecked`) rewrite function `g`? (For
`--stats`: functions rewritten before the Core certificate was required.) -/
def fragRewritable (m : BModule) (g : Nat) : Bool :=
  (Silmaril.Wasm.SSA.optimizeFuncChecked m g).isSome

end Silmaril.Wasm.Binaryen.SsaStage
