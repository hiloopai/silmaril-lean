module

public import Silmaril.Wasm.LimeCompile.Handle.Defs
public import Silmaril.Wasm.LimeCompile.Direct.Defs
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# The 3.0 → Lime compiler: `funcref`/`externref` rewritten to `i32` handles

The first compiler of this development whose output does **not** keep the export API. Every
`funcref`/`externref` (`Handle.handleRef`, either nullability) in a function type, a local, a
global, a block type or a `select` annotation becomes `i32`: a **handle**, an index into a
table `σ : List Val` of references kept by the embedder (the *emulated table*). Handle `0` is
the null reference.

Code level:

* `hv t`: `i32` for a handle reference type, `t` otherwise; `hFT`, `hSub`, `hRec`, `hBT`: the
  same on function types, sub types, recursion groups and block types;
* `hI`/`hL`: the instruction rewrite. Type annotations are rewritten; `ref.null func` /
  `ref.null extern` become `i32.const 0` (the null handle) and `ref.is_null` becomes
  `i32.eqz`; every other instruction is kept (so an instruction that *creates* or *consumes*
  a reference in another way, e.g. `ref.func`, `table.get`, `call_ref`, stays and is rejected
  by the Lime1 read-back);
* `hModule M`: rewrite types, locals, globals (types and initializers) and function bodies.
  Imports, tables, element segments, data, exports and the start function are kept;
* `importsHandleFree M`: no import mentions a handle type (imports are not translated: both
  modules are instantiated against the same store and imports);
* **`compile0 M`**: `Direct.compile (hModule M)` when the imports are handle-free;
* **`compile`** `= Preserve.limePres compile0`: the Lime-preserving variant (Lime-only input
  is returned unchanged, part (3)).

Behaviour level. `Handle.HandleCorrectOn` quantifies over **every** handle table `σ` and lets
a handle stand for **any** reference. Both are too strong (refuted in `HandleTr.Thms`): a
handle `k` with `σ[k]` ill-typed at the parameter (a function reference at an `externref`
parameter, an address outside the store) is accepted by the `i32`-typed target and rejected by
the source; and a translated `ref.null` returns handle `0`, which denotes null only if `σ[0]` is
null. The restatement:

* `HandleTable σ`: `σ[0]` is null and no other handle is null;
* `HandleOk t v`: `v` is a value of handle type `t` in **every** store: null (at a nullable
  type), or an external host reference `extern (host a)` at an `externref` type. A non-null
  function reference is store-dependent and **not** covered (open);
* `ArgRelT`, `ArgsRelT`, `CallRelT`, `ScriptRelT`: `Handle.ArgRel` etc. with `HandleOk` at
  handle parameters;
* `RefinesUpToT`, `CoRefinesUpToT`, **`EquivUpToT`**: `Handle.RefinesUpTo` etc. with the
  typed script relation (behaviours still related by `Handle.BehRel σ`);
* **`HandleCorrectOnT S c`**: on inputs in `S`, every output has the translated export API
  (`Handle.handleApi`) and is `EquivUpToT σ` its input, for every handle table, profile and
  code-parametric host.

Fragment proved (`HandleTr.Thms`): **`FwdFrag`** ("forwarders": no imports and no tables,
memories, globals, tags, segments or start; the types are 2.0 function types; every function
has no locals and its body is a list of `local.get`s; the source is valid and so is the
compiled module's Core image). Such modules create no references and pass handles through.

Open: `Task.handleCorrect` (frozen), `HandleCorrectOnT` for every valid import-free source
that `compile` accepts. Not stated as a `Task`: dynamic handle allocation (sources that create
references, e.g. `ref.func` or references returned by imports, are rejected by `compile`; a
correct translation needs an embedder-side allocation interface and a table that grows during
a session, which the fixed-`σ` relations here cannot express).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (moduleObs SessionRel Call)
open Silmaril.Wasm.LimeCompile.Preserve (ApiTy Compiler)
open Silmaril.Wasm.LimeCompile.Handle (handleRef handleApi BehRel paramsOf)

/-! ## Code level -/

/-- A handle reference type becomes `i32`; other value types are kept. -/
def hv (t : ValType) : ValType := if handleRef t then .i32 else t

/-- The rewrite of a function type. -/
def hFT (ft : FuncType) : FuncType := ⟨ft.params.map hv, ft.results.map hv⟩

/-- The rewrite of a composite type (only function types change). -/
def hComp : CompositeType → CompositeType
  | .func ft => .func (hFT ft)
  | c => c

/-- The rewrite of a sub type. -/
def hSub (st : SubType) : SubType := { st with body := hComp st.body }

/-- The rewrite of a recursion group. -/
def hRec (rt : RecType) : RecType := ⟨rt.types.map hSub⟩

/-- The rewrite of a block type. -/
def hBT : BlockType → BlockType
  | .value t => .value (hv t)
  | bt => bt

/-- The heap types whose null is a handle. -/
def handleHeap : HeapType → Bool
  | .abstract .func | .abstract .extern => true
  | _ => false

set_option linter.unusedTactic false in
mutual
/-- **The instruction rewrite.** -/
def hI : Instr → Instr
  | .refNull ht => if handleHeap ht then .intConst .i32 0 else .refNull ht
  | .refIsNull => .intTestOp .i32 .eqz
  | .select (some ts) => .select (some (ts.map hv))
  | .block bt b => .block (hBT bt) (hL b)
  | .loop bt b => .loop (hBT bt) (hL b)
  | .if_ bt b₁ b₂ => .if_ (hBT bt) (hL b₁) (hL b₂)
  | .tryTable bt cs b => .tryTable (hBT bt) cs (hL b)
  | i => i
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The rewrite of an instruction sequence. -/
def hL : List Instr → List Instr
  | [] => []
  | i :: is => hI i :: hL is
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

/-- The rewrite of a function: locals and body (the type index is kept). -/
def hFunc (f : Func) : Func := ⟨f.type, f.locals.map hv, hL f.body⟩

/-- The rewrite of a global: value type and initializer. -/
def hGlobal (g : Global) : Global :=
  ⟨{ g.type with value := hv g.type.value }, hL g.init⟩

/-- **The handle rewrite of a module.** -/
def hModule (M : Module) : Module :=
  { M with
    types := M.types.map hRec
    globals := M.globals.map hGlobal
    funcs := M.funcs.map hFunc }

/-- An import mentions no handle type (a function import's type is unchanged by `hSub`). -/
def importHandleFree (M : Module) (i : Import) : Bool :=
  match i.type with
  | .func x => match Preserve.Module.typeAt M x with
    | some st => decide (hSub st = st)
    | none => true
  | .global gt => !handleRef gt.value
  | _ => true

/-- No import mentions a handle type. -/
def importsHandleFree (M : Module) : Bool := M.imports.all (importHandleFree M)

/-- **The handle compiler**: rewrite handles to `i32`, then the direct compiler. -/
def compile0 (M : Module) : Option Lime1.Module :=
  if importsHandleFree M then Direct.compile (hModule M) else none

/-- **The Lime-preserving handle compiler.** -/
def compile : Compiler := Preserve.limePres compile0

/-! ## Behaviour level (restated) -/

/-- **A handle table**: handle `0` is null, and no other handle is null. -/
def HandleTable (σ : List Val) : Prop :=
  σ[0]? = some (.ref .null) ∧ ∀ k v, σ[k]? = some v → k ≠ 0 → v ≠ .ref .null

/-- `t` is an `externref` type (either nullability). -/
def externRef : ValType → Bool
  | .ref ⟨_, .abstract .extern⟩ => true
  | _ => false

/-- `t` is a nullable reference type. -/
def nullableRef : ValType → Bool
  | .ref ⟨n, _⟩ => n
  | _ => false

/-- **A store-independent value of handle type `t`**: null at a nullable type, or an external
host reference at an `externref` type. -/
def HandleOk (t : ValType) (v : Val) : Prop :=
  (nullableRef t = true ∧ v = .ref .null) ∨
    (externRef t = true ∧ ∃ a, v = .ref (.extern (.host a)))

/-- A target argument `w` for a source argument `v` at parameter type `t` (typed handles). -/
def ArgRelT (σ : List Val) (t : ValType) (w v : Val) : Prop :=
  (handleRef t = false ∧ w = v) ∨
    (handleRef t = true ∧ ∃ k : BitVec 32, w = Val.i32 k ∧ σ[k.toNat]? = some v ∧ HandleOk t v)

/-- Target and source argument lists at parameter types `ps`. -/
def ArgsRelT (σ : List Val) (ps : List ValType) (ws vs : List Val) : Prop :=
  if vs.length = ps.length then List.Forall₂ (fun w tv => ArgRelT σ tv.1 w tv.2) ws (ps.zip vs)
  else ws = vs

/-- A target invocation request for a source one, against the source API `A`. -/
def CallRelT (σ : List Val) (A : List (String × Option ApiTy)) (c' c : Call) : Prop :=
  c'.1 = c.1 ∧
    match paramsOf A c.1 with
    | some ps => ArgsRelT σ ps c'.2 c.2
    | none => c'.2 = c.2

/-- A target script for a source script. -/
def ScriptRelT (σ : List Val) (A : List (String × Option ApiTy)) : List Call → List Call → Prop :=
  List.Forall₂ (CallRelT σ A)

variable {H : Type}

/-- **Export refinement up to typed handles** (target `m'` implements source `m`). -/
structure RefinesUpToT (σ : List Val) (P : Profile) (host : HostSemantics H) (m' m : Module) :
    Prop where
  instantiates : ∀ (s : Store H) xas c, StoreOk s → Instantiate P host s m xas c →
    ∃ c', Instantiate P host s m' xas c'
  obs : ∀ (s : Store H) xas script' script, StoreOk s →
    ScriptRelT σ (Preserve.Module.exportApi m) script' script →
    ∀ bs ∈ moduleObs P host s xas m' script',
      ∃ bs' ∈ moduleObs P host s xas m script, SessionRel (BehRel σ) bs bs'

/-- The converse. -/
structure CoRefinesUpToT (σ : List Val) (P : Profile) (host : HostSemantics H) (m' m : Module) :
    Prop where
  instantiates : ∀ (s : Store H) xas c', StoreOk s → Instantiate P host s m' xas c' →
    ∃ c, Instantiate P host s m xas c
  obs : ∀ (s : Store H) xas script' script, StoreOk s →
    ScriptRelT σ (Preserve.Module.exportApi m) script' script →
    ∀ bs' ∈ moduleObs P host s xas m script,
      ∃ bs ∈ moduleObs P host s xas m' script', SessionRel (fun b' b => BehRel σ b b') bs' bs

/-- **Export equivalence up to typed handles.** -/
def EquivUpToT (σ : List Val) (P : Profile) (host : HostSemantics H) (m' m : Module) : Prop :=
  RefinesUpToT σ P host m' m ∧ CoRefinesUpToT σ P host m' m

/-- **Correctness up to the API translation, restated**: handle tables only, typed handles. -/
def HandleCorrectOnT (S : Module → Prop) (c : Compiler) : Prop :=
  ∀ M l, S M → c M = some l →
    handleApi (Preserve.Module.exportApi M) = some (Preserve.Module.exportApi l.toCore) ∧
      ∀ (H : Type) (σ : List Val) (P : Profile) (host : HostSemantics H),
        HandleTable σ → Sim.HostParametric host → EquivUpToT σ P host l.toCore M

/-! ## The proved fragment -/

/-- A function that forwards some of its parameters: no locals, a body of `local.get`s. -/
def fwdFunc (f : Func) : Bool :=
  f.locals.isEmpty && f.body.all fun i => match i with
    | .localGet _ => true
    | _ => false

/-- The module has only types, functions and exports. -/
def onlyFuncs (M : Module) : Bool :=
  M.imports.isEmpty && M.tags.isEmpty && M.globals.isEmpty && M.memories.isEmpty &&
    M.tables.isEmpty && M.data.isEmpty && M.elems.isEmpty && M.start.isNone

/-- **The forwarder fragment**: valid modules of forwarding functions only, whose types are
2.0 function types (number, vector, `funcref`, `externref`), and whose compiled image is valid
too. -/
def FwdFrag (M : Module) : Prop :=
  onlyFuncs M = true ∧ (∀ f ∈ M.funcs, fwdFunc f = true) ∧
    (∃ ts : List V2.FuncType, M.types = ts.map V2.FuncType.toCoreRec) ∧ (∃ mt, ModuleOk M mt) ∧
    ∀ l, compile M = some l → ∃ mt, ModuleOk l.toCore mt

/-! ## Open targets (frozen) -/

/-- **Open target (frozen)**: the handle compiler is correct up to typed handles on every
valid source without imports that it accepts. (With imports a host can inspect the store,
whose function types and globals differ between source and target; `HostParametric` only
constrains hosts on stores that differ in function code, so imports are excluded.) -/
def Task.handleCorrect : Prop :=
  HandleCorrectOnT (fun M => (∃ mt, ModuleOk M mt) ∧ M.imports = []) compile

end Silmaril.Wasm.LimeCompile.HandleTr
