module

public import Silmaril.Wasm.SSA.CoreCert.Defs
public import Silmaril.Wasm.SSA.CoreCert.Leaf.Defs
public import Silmaril.Wasm.SSA.Pipeline.Thms
public import Silmaril.Wasm.SSA.Native.Thms
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Execution.Core.Sim.Closure
public import Silmaril.Wasm.Execution.Core.Sim.TypedProgress
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.Binaryen.Uniform
public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Binaryen.CodeSimTyped
public import Silmaril.Wasm.SingleThreaded.Soundness
import Silmaril.Proofs.Wasm.SSA.CoreCert.Module
import Silmaril.Proofs.Wasm.SSA.CoreCert.LocalCert
import Silmaril.Proofs.Wasm.SSA.CoreCert.ExportCert

/-!
# The lambda-SSA optimiser certified against Core 3.0: theorems

Proofs in `Silmaril.Proofs.Wasm.SSA.CoreCert.*`, imported privately; the predicates and
relations the statements use (`SRel`, `ModRel`, `LeafConf`, …) are in
`Silmaril.Wasm.SSA.CoreCert.Leaf.Defs`.

**Function level.** `invoke_replace`: let `s` and `s'` be stores, typed (`StoreOk`), of
native-profile functions passing the arity check (`Binaryen.NativeFuncsOk`,
`Interp.StoreChk`), holding at the same address `a`, with the same integer function type `ft`,
the Core code of `bf` and of `bf'`, where `optimizeFuncCore? ft bf = some bf'`. Then every typed
invocation of `a` has the same Core 3.0 behaviours (closed host) in `s` and in `s'`, at
**every** profile, divergence included: both sets are the native interpreter's
(`Interp.native_adequacy`), which are determined by the observable results of `invokeRun`,
and these are the images of the fragment outcomes of the two functions
(`native_adequate`, `native_outcome`), equal by `optimizeFuncNative?_spec`.
`invoke_setCode` is the case `s' = setCode s a (coreFunc bf')`: the replaced store is native and
arity-checked by `coreReady` (`Interp.storeChk_modify`), only its typing is assumed.

**The Core semantics of a fragment function.** `behaviours_eq_run`: on such a store, the Core
3.0 behaviours of a typed invocation of a function whose code is that of a recognised,
arity-checked, folded fragment function `f` are `f`'s outcomes (`outBeh`), and divergence
exactly when it has none, at every profile.

**Module level, by a run-time certificate.** `optimizeFuncCoreChecked m g` returns the
Core-certified optimisation `bf'` of function `g` of a closed module `m` only after checking
that `m` and `m.setFunc g bf'` validate without imports and that the stores silmaril's
executable instantiation allocates for them pass the executable arity and native-profile
checks and type function `g` at its source type. `coreChecked_spec`: then invocations of
function `g` (address `g`, the module has no imports) have the same Core 3.0 behaviours in the
two allocated stores, every profile, divergence included; `allocStore_instantiate`: these
stores are those of Core 3.0 instantiations (`Instantiate`) of the two modules. Typing and the
function's code in the allocated stores are proved (`Instantiate.ok`, silmaril's
`alloc_funcs`), not checked.

**Lambda-SSA functions in Core.** `compileCore? f` compiles a lambda-SSA function `f`
(out of SSA, lowered, alone in a closed module, allocated by `prepare?`, run-time checked) to a
Core 3.0 store holding it at address `0`. `compileCore_spec`: the Core 3.0 behaviours of a
typed invocation there are exactly `f`'s SSA outcomes, and divergence exactly when it has none,
at every profile. This is the sound edge of the lambda-SSA object of
`Silmaril.Wasm.Category.WasmProg`.

`exCoreCert_checked`: the certificate succeeds, by kernel evaluation, on a module whose
function the optimiser actually rewrites (`testArith`, three body trees after optimisation).

**Only the optimised function needs to be native** (`Silmaril.Proofs.Wasm.SSA.CoreCert.{Local,
LocalCert}`). `behaviours_local`: the Core 3.0 behaviours (any profile, any host) of an
invocation, on integer arguments, of a store-free leaf function (`leafFunc`: integer
operators, locals, control, no globals, no calls, integer locals) are the same in every store
holding the same function instance at that address (a step-by-step simulation over the rules of
`Step`). `runCert_spec`: the local run-time certificate `runCert m g ft bf` (`g` a leaf,
`stubModule m g`, with every other function replaced by `unreachable`, validates and its
allocated store passes the executable checks and allocates `g` like `m`) gives the Core
behaviours of `g` in `m`'s allocated store as its fragment outcomes, whatever the other
functions of `m` are. `optimizeFuncLocal_replace`: the certificate of a replacement between `m`
and any module `m''` holding it.

**Callers, and export equivalence** (`Silmaril.Proofs.Wasm.SSA.CoreCert.{Strict,Ctx,Match,Caller,
Export,ExportCert}`). A frame running *strict* leaf code (`strictFunc`: `leafFunc` with block
types that are not type indices) evolves independently of the store, host, enclosing frame and
module instance, so its Core behaviours are those of a canonical configuration (`LBeh`).
`SRel P s t`: the stores are equal except that some functions are replaced by equivalent strict
leaf functions (`LeafPair`: same type and instance, no reference parameters, and the same `LBeh`
of the callee frames on arguments of the parameter types). `behaviours_srel`: in typed `SRel`
stores, every typed invocation of **any** function (callers of the replaced ones included) has
the same Core 3.0 behaviours, closed host, every profile, divergence included. The proof is a
simulation over every Core step under the closed host (`step_match`): a call of a replaced
function is typed, so its arguments have the parameter types (`args_typed`, from
`Sim.ContextTyped`); the source callee frame then runs while the target waits, and when it
returns (or diverges, `InfiniteTrace.context_decompose`) the target callee frame runs to the same
result (or diverges). `exportEquiv_modRel`: Core modules whose functions are equal or
`LeafFun`-equivalent are `ExportEquiv (· = ·)` under the closed host (imports allowed, host calls
unchanged). `replace_exportEquiv`: a module whose functions are the originals or results of the
export-certified optimiser `optimizeFuncExport` (each passing `runCert` in that module) is
export-equivalent to the source, every profile.

**Not covered.** The certificate needs the module to be closed for `runCert` (the equivalence of
a rewritten function is established on the stub module's allocated store) and the rewritten
functions to be strict leaves; the export theorems are under the closed host (host functions
never return), as for the other `wasm-opt` stages.
-/

public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H H' : Type}

/-- **Replacing a function by its Core-certified optimisation preserves the Core 3.0
behaviours of every typed invocation of it**, at every profile, divergence included. -/
theorem invoke_replace {s : Store H} {s' : Store H'} {a : Nat} {fi : FuncInst H}
    {fi' : FuncInst H'} {ft : FuncType} {bf bf' : BFunc} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs) (hs' : StoreOk s')
    (hF' : NativeFuncsOk s'.funcs) (hS' : Silmaril.Wasm.Interp.StoreChk s'.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hfi' : s'.funcs[a]? = some fi') (hcode' : fi'.code = .wasm (coreFunc bf'))
    (hty' : Validation.DefType.funcType? fi'.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (ho : optimizeFuncCore? ft bf = some bf') {vs : List Val} (hok : InvokeOk s a vs)
    (P : Numerics.Profile) :
    behaviours P closedHost s a vs = behaviours P closedHost s' a vs :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.invoke_replace hs hF hS hs' hF' hS' hfi hcode hty hfi' hcode'
    hty' ho hok P

/-- **`invoke_replace` for `setCode`**: only the typing of the replaced store is assumed. -/
theorem invoke_setCode {s : Store H} {a : Nat} {fi : FuncInst H} {ft : FuncType}
    {bf bf' : BFunc} (hs : StoreOk s) (hs' : StoreOk (setCode s a (coreFunc bf')))
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (ho : optimizeFuncCore? ft bf = some bf') {vs : List Val} (hok : InvokeOk s a vs)
    (P : Numerics.Profile) :
    behaviours P closedHost s a vs = behaviours P closedHost (setCode s a (coreFunc bf')) a vs :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.invoke_setCode hs hs' hF hS hfi hcode hty ho hok P

/-- **The Core 3.0 behaviours of a native fragment function**: its outcomes, and divergence
exactly when it has none, at every profile. -/
theorem behaviours_eq_run {s : Store H} {a : Nat} {fi : FuncInst H} {ft : FuncType} {bf : BFunc}
    {f : FragFunc} (hs : StoreOk s) (hF : NativeFuncsOk s.funcs)
    (hS : Silmaril.Wasm.Interp.StoreChk s.funcs) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hf : ofBFunc? ft bf = some f) (hn : f.native = true)
    (hst : BExpr.structuredList bf.body = true) {vs : List Val} (hok : InvokeOk s a vs)
    (P : Numerics.Profile) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
      behaviours P closedHost s a vs =
        {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.behaviours_eq_run hs hF hS hfi hcode hty hf hn hst hok P

/-- **The run-time certificate is sound**: invocations of the optimised function have the same
Core 3.0 behaviours in the allocated stores of the module and of the module with the
replacement, at every profile, divergence included. -/
theorem coreChecked_spec {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCoreChecked m g = some bf') :
    ∃ s s' : Store Empty, allocStore? m = some s ∧ allocStore? (m.setFunc g bf') = some s' ∧
      ∀ (P : Numerics.Profile) (vs : List Val), InvokeOk s g vs →
        behaviours P closedHost s g vs = behaviours P closedHost s' g vs :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.coreChecked_spec h

/-- **The certificate against any module holding the replacement** (several functions may be
replaced at once): if `m'` is closed and valid, holds `bf'` as function `g`, and its allocated
store passes the executable checks at `g` with `g`'s source type, then invocations of `g` have
the same Core 3.0 behaviours in the allocated stores of `m` and `m'`, every profile. -/
theorem coreChecked_replace {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCoreChecked m g = some bf') {m' : BModule} {s' : Store Empty}
    (hv' : closedValid m' = true) (hs' : allocStore? m' = some s')
    (hcode' : m'.funcs[g]? = some bf')
    (hr' : ∀ bf ft, m.funcs[g]? = some bf → m.funcType? bf.type = some ft →
      storeReady s' g ft = true) :
    ∃ s : Store Empty, allocStore? m = some s ∧ ∀ (P : Numerics.Profile) (vs : List Val),
      InvokeOk s g vs → behaviours P closedHost s g vs = behaviours P closedHost s' g vs :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.coreChecked_replace h hv' hs' hcode' hr'

/-- The certificate's replacement is fragment-equivalent to the source. -/
theorem coreChecked_frag {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCoreChecked m g = some bf') :
    ∃ bf ft f f', m.funcs[g]? = some bf ∧ m.funcType? bf.type = some ft ∧
      ofBFunc? ft bf = some f ∧ ofBFunc? ft bf' = some f' ∧
      ∀ args o, f.Run args o ↔ f'.Run args o := by
  obtain ⟨bf, ft, -, -, hbf, hft, ho, -⟩ :=
    Silmaril.Proofs.Wasm.SSA.CoreCert.optimizeFuncCoreChecked_inv h
  obtain ⟨hon, -, -⟩ := Silmaril.Proofs.Wasm.SSA.CoreCert.optimizeFuncCore?_inv ho
  obtain ⟨f, f', hf, -, hf', -, -, -, hrun⟩ := optimizeFuncNative?_spec hon
  exact ⟨bf, ft, f, f', hbf, hft, hf, hf', hrun⟩

/-- A closed valid module is valid. -/
theorem ok_of_closedValid {m : BModule} (h : closedValid m = true) : m.Ok := by
  apply validates_ok
  have h' : ((Validation.validate? m.lower).map fun mt => mt.imports.isEmpty) = some true :=
    beq_iff_eq.mp h
  unfold validates
  rcases hv : Validation.validate? m.lower with _ | mt
  · rw [hv] at h'
    cases h'
  · rfl

/-- The certificate validates both modules, without imports. -/
theorem coreChecked_valid {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCoreChecked m g = some bf') :
    closedValid m = true ∧ closedValid (m.setFunc g bf') = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hv, hv', -, -⟩ :=
    Silmaril.Proofs.Wasm.SSA.CoreCert.optimizeFuncCoreChecked_inv h
  exact ⟨hv, hv'⟩

/-- **The allocated store of a closed validated module is that of a Core 3.0 instantiation.** -/
theorem allocStore_instantiate {m : BModule} {s : Store Empty} (hs : allocStore? m = some s)
    (hv : closedValid m = true) :
    ∃ c : Config Empty, c.store = s ∧ ∀ (P : Numerics.Profile) (host : HostSemantics Empty),
      Instantiate P host ({} : Store Empty) m.lower [] c :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.allocStore?_instantiate hs hv

/-- **A lambda-SSA function compiled to Core has its SSA outcomes as Core 3.0 behaviours**, and
diverges exactly when it has none, at every profile. -/
theorem compileCore_spec {f : SFunc} {s : Store Empty} (h : compileCore? f = some s)
    (P : Numerics.Profile) {vs : List Val} (hok : InvokeOk s 0 vs) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
      behaviours P closedHost s 0 vs =
        {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.compileCore?_spec h P hok

/-- Fragment values are determined by their Core values. -/
theorem WVal.toVal_injective : Function.Injective WVal.toVal := by
  intro a b h
  have e : ∀ w : WVal, WVal.ofVal? w.toVal = some w := fun w => by cases w <;> rfl
  have h' : some a = some b := (e a).symm.trans ((congrArg WVal.ofVal? h).trans (e b))
  exact Option.some.inj h'

theorem WVal.map_toVal_inj {as bs : List WVal} (h : as.map WVal.toVal = bs.map WVal.toVal) :
    as = bs :=
  (List.map_injective_iff.mpr WVal.toVal_injective) h

/-- Integer arguments of the parameter types are a typed invocation of the compiled function. -/
theorem compileCore_invokeOk {f : SFunc} {s : Store Empty} (h : compileCore? f = some s)
    {args : List WVal} (hargs : args.map WVal.type = f.params) :
    InvokeOk s 0 (args.map WVal.toVal) :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.compileCore?_invokeOk h hargs

/-- `compileCore?` succeeds on the SSA form of `testArith` and on its optimisation (kernel
evaluation). -/
theorem compileCore_testArith :
    (compileCore? (compileFunc testArith)).isSome = true ∧
      (compileCore? (optimizeSSA (compileFunc testArith))).isSome = true := by
  constructor <;> decide +kernel

/-- **Invocations of a store-free leaf function are local**: the same behaviours in every store
holding the same function instance at the address, at every profile and host. -/
theorem behaviours_local {s t : Store H} {a : Nat} {fi : FuncInst H} {fn : Func}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) (hleaf : leafFunc fn = true)
    (ht : t.funcs[a]? = s.funcs[a]?) (P : Numerics.Profile) (host : HostSemantics H)
    (args : List WVal) :
    behaviours P host s a (args.map WVal.toVal) = behaviours P host t a (args.map WVal.toVal) :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.behaviours_local ⟨fi, fn, hfi, hcode, hleaf⟩ ht
    (Silmaril.Proofs.Wasm.SSA.CoreCert.valP_toVal a args)

/-- **The local certificate**: the Core 3.0 behaviours of function `g` of a closed module are
its fragment outcomes, and divergence exactly when it has none, at every profile, whatever the
other functions of the module are. -/
theorem runCert_spec {m : BModule} {g : Nat} {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (hbf : m.funcs[g]? = some bf) (hf : ofBFunc? ft bf = some f) (hn : f.native = true)
    (hc : runCert m g ft bf = true) :
    ∃ s : Store Empty, allocStore? m = some s ∧
      (∀ args : List WVal, args.map WVal.type = f.params → InvokeOk s g (args.map WVal.toVal)) ∧
      ∀ (P : Numerics.Profile) (vs : List Val), InvokeOk s g vs →
        ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
          behaviours P closedHost s g vs =
            {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.runCert_spec hbf hf hn hc

/-- **The local certificate of a replacement**: invocations of `g` have the same Core 3.0
behaviours in the allocated stores of `m` and of any module `m''` holding the replacement and
passing `runCert` at `g`, every profile, divergence included. -/
theorem optimizeFuncLocal_replace {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncLocal m g = some bf') {m'' : BModule} (hbf'' : m''.funcs[g]? = some bf')
    (hr : ∀ bf ft, m.funcs[g]? = some bf → m.funcType? bf.type = some ft →
      runCert m'' g ft bf' = true) :
    ∃ s s'' : Store Empty, allocStore? m = some s ∧ allocStore? m'' = some s'' ∧
      ∀ (P : Numerics.Profile) (vs : List Val), InvokeOk s g vs →
        behaviours P closedHost s g vs = behaviours P closedHost s'' g vs :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.optimizeFuncLocal_replace h hbf'' hr

/-- The local certificate's replacement is fragment-equivalent to the source. -/
theorem optimizeFuncLocal_frag {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncLocal m g = some bf') :
    ∃ bf ft f f', m.funcs[g]? = some bf ∧ m.funcType? bf.type = some ft ∧
      ofBFunc? ft bf = some f ∧ ofBFunc? ft bf' = some f' ∧
      ∀ args o, f.Run args o ↔ f'.Run args o := by
  obtain ⟨bf, ft, hbf, hft, ho, -⟩ := Silmaril.Proofs.Wasm.SSA.CoreCert.optimizeFuncLocal_inv h
  obtain ⟨hon, -, -⟩ := Silmaril.Proofs.Wasm.SSA.CoreCert.optimizeFuncCore?_inv ho
  obtain ⟨f, f', hf, -, hf', -, -, -, hrun⟩ := optimizeFuncNative?_spec hon
  exact ⟨bf, ft, f, f', hbf, hft, hf, hf', hrun⟩

/-- A closed module with one function, `testArith` (`f(x) = (x + 0) * 1 + (2 + 3)` with a
local), exported as `f`. -/
def exCoreCert : BModule where
  base := { types := [⟨[⟨true, [], .func ⟨[.num (.int .i32)], [.num (.int .i32)]⟩⟩]⟩],
            exports := [⟨"f", .func ⟨0⟩⟩] }
  funcs := [(toBFunc? ⟨0⟩ testArith).getD ⟨⟨0⟩, [], []⟩]

/-- **Non-vacuity**: the certificate succeeds on `exCoreCert` (kernel evaluation), and the
optimised body has three trees. -/
theorem exCoreCert_checked :
    ((optimizeFuncCoreChecked exCoreCert 0).map fun bf => bf.body.length) = some 3 := by
  decide +kernel

/-! ## Callers and export equivalence -/

/-- **Callers of equivalent strict leaf functions**: in typed stores that are equal except for
functions replaced by equivalent strict leaf functions (`SRel`), every typed invocation of any
function has the same Core 3.0 behaviours (closed host), divergence included. -/
theorem behaviours_srel {s t : Store H} {P : Numerics.Profile}
    (hst : CoreCert.SRel P s t) (hs : StoreOk s) (ht : StoreOk t)
    {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) :
    behaviours P closedHost s a vs = behaviours P closedHost t a vs :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.behaviours_srel hst hs ht hok

/-- **Modules with equal or equivalent strict leaf functions are export equivalent** (closed
host), with or without imports. -/
theorem exportEquiv_modRel {m m' : Module} {P : Numerics.Profile}
    (hrel : CoreCert.ModRel P m m') (hm : ∃ mt, Validation.ModuleOk m mt)
    (hm' : ∃ mt, Validation.ModuleOk m' mt) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m m' :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.exportEquiv_modRel hrel hm hm'

/-- **The export certificate of the SSA optimiser**: a valid module whose functions are the
originals or results of `optimizeFuncExport` (each passing `runCert` in it) is export-equivalent
to the source, at every profile, under the closed host. -/
theorem replace_exportEquiv {m m' : BModule} (hbase : m'.base = m.base)
    (hlen : m'.funcs.length = m.funcs.length) (hm : m.Ok) (hm' : m'.Ok)
    (hfun : ∀ g bf', m'.funcs[g]? = some bf' → m.funcs[g]? = some bf' ∨
      (optimizeFuncExport m g = some bf' ∧ ∀ bf ft, m.funcs[g]? = some bf →
        m.funcType? bf.type = some ft → runCert m' g ft bf' = true))
    (P : Numerics.Profile) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m'.lower m.lower :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.replace_exportEquiv hbase hlen hm hm' hfun P

/-- The export-certified optimiser is the local one, restricted. -/
theorem optimizeFuncExport_local {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncExport m g = some bf') : optimizeFuncLocal m g = some bf' := by
  obtain ⟨_, -, h', -, -⟩ := Silmaril.Proofs.Wasm.SSA.CoreCert.optimizeFuncExport_inv h
  exact h'

/-- **Non-vacuity**: the export-certified optimiser rewrites `exCoreCert` (kernel
evaluation). -/
theorem exCoreCert_export :
    ((optimizeFuncExport exCoreCert 0).map fun bf => bf.body.length) = some 3 := by
  decide +kernel

end Silmaril.Wasm.SSA

/-! ## Runs of store-free leaf code -/

namespace Silmaril.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **A step of store-free leaf code** (frames of leaf values, the function at `a` a store-free
leaf) keeps the store and is a step from the same code and frame in any store holding the same
function at `a`, to leaf code. -/
theorem step_swap {a : Nat} {c c' : Config H} (h : Step P host c c') (hp : PAdmins a c.code)
    (hfr : FrameP a c.frame) (hL : LeafAt c.store a) {t : Store H}
    (ht : t.funcs[a]? = c.store.funcs[a]?) : Swap P host a t c c' :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.step_swap h hp hfr hL ht

/-- `step_swap` with the leaf invariant `LeafConf`. -/
theorem step_swap' {a : Nat} {c c' : Config H} (h : Step P host c c') (hc : LeafConf a c)
    {t : Store H} (ht : t.funcs[a]? = c.store.funcs[a]?) :
    c'.store = c.store ∧ Step P host (swapStore t c) (swapStore t c') ∧ LeafConf a c' :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.step_swap' h hc ht

/-- **Runs of leaf code are runs in any store holding the same function at `a`.** -/
theorem steps_swap {a : Nat} {c c' : Config H} (h : Steps P host c c') (hc : LeafConf a c)
    {t : Store H} (ht : t.funcs[a]? = c.store.funcs[a]?) :
    c'.store = c.store ∧ Steps P host (swapStore t c) (swapStore t c') ∧ LeafConf a c' :=
  Silmaril.Proofs.Wasm.SSA.CoreCert.steps_swap h hc ht

end Silmaril.Wasm.SSA.CoreCert
