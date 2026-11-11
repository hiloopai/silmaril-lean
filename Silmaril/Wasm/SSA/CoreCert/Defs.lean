module

public import Silmaril.Wasm.SSA.Native.Defs
public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

/-!
# The lambda-SSA optimiser certified against Core 3.0: definitions

`Silmaril.Wasm.SSA.Native` relates the arity-guarded optimiser `optimizeFuncNative?` to
silmaril's native Binaryen interpreter (`native_adequate`), and `Silmaril.Wasm.Interp` relates that
interpreter to Core 3.0 (`native_adequacy`) on stores whose functions pass the arity check
`chk` and are of the native profile. This topic joins the two at the function level:

* `coreFunc bf`: the Core function of a Binaryen function (its folded body lowered);
* `setCode s a fn`: the store `s` with the code of the function at address `a` replaced
  by `fn` (type and module instance kept);
* `coreReady ft bf`: the run-time conditions under which the body of `bf`, of function type
  `ft`, is handed to the native-adequacy theorem: it is folded (`BExpr.structuredList`, so that
  the interpreter's evaluation of the lowered code is that of the trees), its lowering is of
  the native profile (`Interp.instrsNative`) and it passes the arity check against the empty
  store and instance (`Interp.chk`; such a check passes against every store and instance,
  `Interp.chk_of_free`). This is the run-time bridge from `FragFunc.native` to `chk`;
* `optimizeFuncCore? ft bf`: `optimizeFuncNative?` guarded by `coreReady` on the source and
  the result; `optimizeFuncCoreCertified m g` adds silmaril's module validator as
  `optimizeFuncCertified` does;
* `optimizeFuncCoreChecked m g`: the run-time certificate for a closed module (validated, no
  imports): `optimizeFuncCore?` on function `g`, both the module and the module with the
  replacement validate, and the stores that silmaril's executable instantiation `prepare?`
  allocates for them pass the executable arity and native-profile checks
  (`Interp.storeChkB`, `Interp.nativeFuncsB`) and hold function `g` at the source type
  (`typeAt`).

Results in `Silmaril.Wasm.SSA.CoreCert.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core

/-- The Core function of a Binaryen function. -/
abbrev coreFunc (bf : BFunc) : Func := Declaration.Func.mapBody BExpr.lowerList bf

/-- Replace the code of the function at address `a` (its type and module instance are kept). -/
def setCode {H : Type} (s : Store H) (a : Nat) (fn : Func) : Store H :=
  { s with funcs := s.funcs.modify a fun fi => { fi with code := .wasm fn } }

/-- The run-time conditions for handing a body to Core: folded, native profile, and passing the
arity check against the empty store and instance. -/
def coreReady (ft : FuncType) (bf : BFunc) : Bool :=
  BExpr.structuredList bf.body && Interp.instrsNative (BExpr.lowerList bf.body) &&
    Interp.endsAt (Interp.chk ([] : List (FuncInst Empty)) {}
      (ft.params.length + bf.locals.length) ft.results.length [ft.results.length] (some 0)
      (liftInstrs (BExpr.lowerList bf.body))) ft.results.length

/-- **The Core-certified optimiser** of one function of type `ft`. -/
def optimizeFuncCore? (ft : FuncType) (bf : BFunc) : Option BFunc := do
  let bf' ← optimizeFuncNative? ft bf
  if coreReady ft bf && coreReady ft bf' then some bf' else none

/-- `optimizeFuncCore?` on function `g` of a module, kept only if the module with the
replacement validates. -/
def optimizeFuncCoreCertified (m : BModule) (g : Nat) : Option BFunc := do
  let bf ← m.funcs[g]?
  let ft ← m.funcType? bf.type
  let bf' ← optimizeFuncCore? ft bf
  if validates (m.setFunc g bf') then some bf' else none

/-- The function at address `a` of a store has the function type `ft`. -/
def typeAt {H : Type} (s : Store H) (a : Nat) (ft : FuncType) : Bool :=
  match s.funcs[a]? with
  | some fi => Validation.DefType.funcType? fi.type ==
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal)
  | none => false

/-- The module validates and has no imports. -/
def closedValid (m : BModule) : Bool :=
  ((Validation.validate? m.lower).map fun mt => mt.imports.isEmpty) == some true

/-- The allocated store of a closed module (silmaril's executable instantiation `prepare?`
into the empty store), if any. -/
def allocStore? (m : BModule) : Option (Store Empty) :=
  (prepare? evalConst? ({} : Store Empty) m.lower []).map fun p => p.1.store

/-- The executable hypotheses of native adequacy on a store, and the type of address `a`. -/
def storeReady {H : Type} (s : Store H) (a : Nat) (ft : FuncType) : Bool :=
  Interp.storeChkB s.funcs && Interp.nativeFuncsB s.funcs && typeAt s a ft

/-- **The run-time certificate** of replacing function `g` of a closed module by its
Core-certified optimisation. -/
def optimizeFuncCoreChecked (m : BModule) (g : Nat) : Option BFunc := do
  let bf ← m.funcs[g]?
  let ft ← m.funcType? bf.type
  let bf' ← optimizeFuncCore? ft bf
  let s ← allocStore? m
  let s' ← allocStore? (m.setFunc g bf')
  if closedValid m && closedValid (m.setFunc g bf') && storeReady s g ft && storeReady s' g ft then
    some bf'
  else none

/-! ## Store-free code -/

mutual
/-- **Store-free, call-free instructions**: integer operators, locals, `select`, `drop`,
`nop`, `unreachable`, structured control, branches, `return` and constants. Core steps of such code read
and write neither the store nor any other function. -/
def pureInstr : Instr → Bool
  | .block _ body | .loop _ body => pureInstrs body
  | .if_ _ b₁ b₂ => pureInstrs b₁ && pureInstrs b₂
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .return_
  | .localGet _ | .localSet _ | .localTee _ | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _
  | .intTestOp _ _ | .intRelOp _ _ | .floatConst _ _ | .vecConst _ => true
  | _ => false

/-- `pureInstr` on a sequence. -/
def pureInstrs : List Instr → Bool
  | [] => true
  | i :: is => pureInstr i && pureInstrs is
end

/-- Integer local types. -/
def intLocals (ts : List ValType) : Bool :=
  ts.all fun t => match t with | .num (.int _) => true | _ => false

/-- **A store-free leaf function**: Wasm code, store-free and call-free, with integer locals. -/
def leafFunc (fn : Func) : Bool := pureInstrs fn.body && intLocals fn.locals

/-- A block type read without the module instance (not a type index). -/
def inlineBT : BlockType → Bool
  | .typeIdx _ => false
  | _ => true

mutual
/-- **Strict leaf instructions**: `pureInstr` with block types that are not type indices, so
that their Core steps read neither the store nor the module instance of the frame. -/
def strictInstr : Instr → Bool
  | .block bt body | .loop bt body => inlineBT bt && strictInstrs body
  | .if_ bt b₁ b₂ => inlineBT bt && strictInstrs b₁ && strictInstrs b₂
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .return_
  | .localGet _ | .localSet _ | .localTee _ | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _
  | .intTestOp _ _ | .intRelOp _ _ | .floatConst _ _ | .vecConst _ => true
  | _ => false

/-- `strictInstr` on a sequence. -/
def strictInstrs : List Instr → Bool
  | [] => true
  | i :: is => strictInstr i && strictInstrs is
end

/-- **A strict leaf function**: strict leaf code with integer locals. Its in-flight frames
evolve independently of the store, of the host, of the enclosing frame and of the module
instance (`Silmaril.Proofs.Wasm.SSA.CoreCert.Strict`). -/
def strictFunc (fn : Func) : Bool := strictInstrs fn.body && intLocals fn.locals

/-! ## Local certificates: only the optimised function needs to be native -/

/-- The module with every defined function except `g` replaced by `unreachable` (types and
locals kept). -/
def stubModule (m : BModule) (g : Nat) : BModule :=
  { m with funcs := m.funcs.mapIdx fun i bf =>
      if i = g then bf else { bf with body := [.op .unreachable []] } }

/-- Two stores hold function instances with the same type and module instance at `g`. -/
def sameFuncAt {H H' : Type} (s : Store H) (u : Store H') (g : Nat) : Bool :=
  match s.funcs[g]?, u.funcs[g]? with
  | some fi, some fj => fi.type == fj.type && fi.module == fj.module
  | _, _ => false

/-- **The local run-time certificate** of function `g` (Binaryen function `bf` of type `ft`)
of a closed module `m`: `bf` is a store-free leaf passing `coreReady`, and in the closed valid
module `stubModule m g`, whose allocated store passes the executable checks at `g`, function
`g` is allocated with the same type and module instance as in `m`. Then the Core behaviours of
`g` in `m`'s allocated store are its fragment outcomes (`runCert_spec`); no other function
of `m` needs to be native or arity-checked. -/
def runCert (m : BModule) (g : Nat) (ft : FuncType) (bf : BFunc) : Bool :=
  leafFunc (coreFunc bf) && coreReady ft bf && closedValid m && closedValid (stubModule m g) &&
    match allocStore? m, allocStore? (stubModule m g) with
    | some s, some u => storeReady u g ft && sameFuncAt s u g
    | _, _ => false

/-- **The locally certified optimiser** of function `g` of a closed module: `optimizeFuncCore?`,
kept when the source passes `runCert`. (The module holding the result is checked by `runCert`
too, by the caller.) -/
def optimizeFuncLocal (m : BModule) (g : Nat) : Option BFunc := do
  let bf ← m.funcs[g]?
  let ft ← m.funcType? bf.type
  let bf' ← optimizeFuncCore? ft bf
  if runCert m g ft bf then some bf' else none

/-- **The export-certified optimiser** of function `g` of a closed module: `optimizeFuncLocal`,
kept when the source and the result are strict leaf functions (`strictFunc`). A module whose
functions are the originals or such results, each passing `runCert` in that module too, is
export-equivalent to the source (`Silmaril.Wasm.SSA.replace_exportEquiv`), at every profile. -/
def optimizeFuncExport (m : BModule) (g : Nat) : Option BFunc := do
  let bf ← m.funcs[g]?
  let bf' ← optimizeFuncLocal m g
  if strictFunc (coreFunc bf) && strictFunc (coreFunc bf') then some bf' else none

/-- The Core 3.0 behaviour of a call outcome of the fragment (`none`: no outcome, divergence). -/
def outBeh : Option FOut → Behaviour Val
  | some (.ret none) => .returns []
  | some (.ret (some w)) => .returns [w.toVal]
  | some .trap => .traps
  | none => .diverges

/-- The closed module with one function `bf` of type `ft` (type index `0`), exported as `f`. -/
def soloModule (ft : FuncType) (bf : BFunc) : BModule where
  base := { types := [⟨[⟨true, [], .func ft⟩]⟩], exports := [⟨"f", .func ⟨0⟩⟩] }
  funcs := [bf]

/-- The integer function type of a fragment signature. -/
def sigType (ps : List IntType) (r : Option IntType) : FuncType :=
  ⟨ps.map fun t => .num (.int t), resultTypes r⟩

/-- **A lambda-SSA function compiled to a Core 3.0 store**: out of SSA, lowered to a Binaryen
function, placed alone in a closed module, validated and allocated by `prepare?`; kept only
when the run-time checks (`FragFunc.native`, `coreReady`, `closedValid`, `storeReady`) pass.
The function is at address `0`. -/
def compileCore? (f : SFunc) : Option (Store Empty) := do
  let g ← decompileFunc f
  let bf ← toBFunc? ⟨0⟩ g
  let ft := sigType g.params g.result
  if g.native && coreReady ft bf && closedValid (soloModule ft bf) then
    let s ← allocStore? (soloModule ft bf)
    if storeReady s 0 ft then some s else none
  else none

end Silmaril.Wasm.SSA
