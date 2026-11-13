module

public import Silmaril.Wasm.LimeCompile.Preserve.Defs
public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Execution.Core.Sim.Store

/-!
# The 3.0 → Lime compiler: `funcref`/`externref` exports as `i32` handles

`Preserve.api_iff` shows that an export API can be kept exactly by a Lime1 module iff all its
resolved types are Lime types. An export whose function type (or global type) mentions
`funcref` or `externref` therefore has to be *translated*. The translation here passes such
references as `i32` **handles** into an embedder-side handle table.

API level:

* `handleRef t`: `t` is `funcref`/`externref` (`(ref null? func)`, `(ref null? extern)`);
* `handleVal t`: a Lime value type is kept, a handle reference becomes `i32`, anything else
  (`v128`, other references) has no translation;
* `handleTy`: final parent-free function types and global types are translated pointwise;
  other export types are kept when they are Lime types and rejected otherwise;
* **`handleApi A`**: translate every resolved type of an export API (`none`: some export cannot
  be translated).

Behaviour level ("correct up to the API translation"):

* a **handle table** `σ : List Val` is fixed for the whole run: handle `k` denotes `σ[k]`.
  (Handles allocated during a session, e.g. for a reference *returned* by the source, are not
  modelled: the result relation only says that a returned handle denotes the returned
  reference in `σ`.)
* `ArgRel σ t w v`: the target argument `w` stands for the source argument `v` at parameter
  type `t`: equal at non-handle types, a handle `i32 k` with `σ[k] = v` at handle types;
* `CallRel σ A`, `ScriptRel σ A`: target and source invocation requests, by export name; the
  arguments are related by `ArgRel` at the parameter types of `A` (the *source* API) when the
  argument count matches, and are equal otherwise;
* `ResRel σ`, `BehRel σ`: target and source behaviours: equal, or both returning, with each
  value equal or a handle for the source's reference;
* **`RefinesUpTo σ P host m' m`**, `EquivUpTo`: silmaril-lean's `ExportRefines`/`ExportEquiv`
  (instantiation, then every session of export invocations sharing the store) with the source
  script translated by `ScriptRel` and behaviours related by `BehRel`;
* **`HandleCorrectOn S c`**: on inputs in `S`, every output of `c` has the translated export API
  of its input and is `EquivUpTo` it, for every handle table, profile and code-parametric host.

Imports are not translated: both modules are instantiated against the same store and imports.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Handle

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (moduleObs SessionRel Call)
open Silmaril.Wasm.LimeCompile.Preserve (ApiTy limeVal Compiler)

/-! ## API level -/

/-- `funcref` or `externref`, either nullability: passed as an `i32` handle. -/
def handleRef : ValType → Bool
  | .ref ⟨_, .abstract .func⟩ => true
  | .ref ⟨_, .abstract .extern⟩ => true
  | _ => false

/-- The value type of the translated API: Lime types kept, handle references as `i32`. -/
def handleVal (t : ValType) : Option ValType :=
  if limeVal t then some t else if handleRef t then some .i32 else none

/-- Translate a resolved export type. -/
def handleTy : ApiTy → Option ApiTy
  | .func ⟨true, [], .func ft⟩ =>
    match ft.params.mapM handleVal, ft.results.mapM handleVal with
    | some ps, some rs => some (.func ⟨true, [], .func ⟨ps, rs⟩⟩)
    | _, _ => none
  | .global t => (handleVal t.value).map fun v => .global { t with value := v }
  | t => if t.lime then some t else none

/-- Translate one export-API entry (an unresolved index is kept). -/
def handleEntry : String × Option ApiTy → Option (String × Option ApiTy)
  | (n, none) => some (n, none)
  | (n, some t) => (handleTy t).map fun t' => (n, some t')

/-- **The handle translation of an export API.** -/
def handleApi (A : List (String × Option ApiTy)) : Option (List (String × Option ApiTy)) :=
  A.mapM handleEntry

/-! ## Behaviour level -/

/-- The parameter types of the function export named `x` in an export API. -/
def paramsOf (A : List (String × Option ApiTy)) (x : String) : Option (List ValType) :=
  match A.find? (fun p => p.1 == x) with
  | some (_, some (.func ⟨_, _, .func ft⟩)) => some ft.params
  | _ => none

/-- A target argument `w` for a source argument `v` at parameter type `t`. -/
def ArgRel (σ : List Val) (t : ValType) (w v : Val) : Prop :=
  (handleRef t = false ∧ w = v) ∨
    (handleRef t = true ∧ ∃ (k : BitVec 32) (r : Ref), v = .ref r ∧ w = Val.i32 k ∧
      σ[k.toNat]? = some v)

/-- Target and source argument lists at parameter types `ps`. -/
def ArgsRel (σ : List Val) (ps : List ValType) (ws vs : List Val) : Prop :=
  if vs.length = ps.length then List.Forall₂ (fun w tv => ArgRel σ tv.1 w tv.2) ws (ps.zip vs)
  else ws = vs

/-- A target invocation request for a source one, against the source API `A`. -/
def CallRel (σ : List Val) (A : List (String × Option ApiTy)) (c' c : Call) : Prop :=
  c'.1 = c.1 ∧
    match paramsOf A c.1 with
    | some ps => ArgsRel σ ps c'.2 c.2
    | none => c'.2 = c.2

/-- A target script for a source script. -/
def ScriptRel (σ : List Val) (A : List (String × Option ApiTy)) : List Call → List Call → Prop :=
  List.Forall₂ (CallRel σ A)

/-- A target result value for a source one: equal, or a handle denoting the source reference. -/
def ResRel (σ : List Val) (w v : Val) : Prop :=
  w = v ∨ ∃ (k : BitVec 32) (r : Ref), v = .ref r ∧ w = Val.i32 k ∧ σ[k.toNat]? = some v

/-- A target behaviour for a source one. -/
def BehRel (σ : List Val) (b b' : Behaviour Val) : Prop :=
  b = b' ∨ ∃ ws vs, b = .returns ws ∧ b' = .returns vs ∧ List.Forall₂ (ResRel σ) ws vs

variable {H : Type}

/-- **Export refinement up to the handle translation** (target `m'` implements source `m`). -/
structure RefinesUpTo (σ : List Val) (P : Profile) (host : HostSemantics H) (m' m : Module) :
    Prop where
  instantiates : ∀ (s : Store H) xas c, StoreOk s → Instantiate P host s m xas c →
    ∃ c', Instantiate P host s m' xas c'
  obs : ∀ (s : Store H) xas script' script, StoreOk s →
    ScriptRel σ (Preserve.Module.exportApi m) script' script →
    ∀ bs ∈ moduleObs P host s xas m' script',
      ∃ bs' ∈ moduleObs P host s xas m script, SessionRel (BehRel σ) bs bs'

/-- The converse: every source observation is matched by a target one. -/
structure CoRefinesUpTo (σ : List Val) (P : Profile) (host : HostSemantics H) (m' m : Module) :
    Prop where
  instantiates : ∀ (s : Store H) xas c', StoreOk s → Instantiate P host s m' xas c' →
    ∃ c, Instantiate P host s m xas c
  obs : ∀ (s : Store H) xas script' script, StoreOk s →
    ScriptRel σ (Preserve.Module.exportApi m) script' script →
    ∀ bs' ∈ moduleObs P host s xas m script,
      ∃ bs ∈ moduleObs P host s xas m' script', SessionRel (fun b' b => BehRel σ b b') bs' bs

/-- **Export equivalence up to the handle translation.** -/
def EquivUpTo (σ : List Val) (P : Profile) (host : HostSemantics H) (m' m : Module) : Prop :=
  RefinesUpTo σ P host m' m ∧ CoRefinesUpTo σ P host m' m

/-- **Correctness up to the API translation**, on inputs in `S`. -/
def HandleCorrectOn (S : Module → Prop) (c : Compiler) : Prop :=
  ∀ M l, S M → c M = some l →
    handleApi (Preserve.Module.exportApi M) = some (Preserve.Module.exportApi l.toCore) ∧
      ∀ (H : Type) (σ : List Val) (P : Profile) (host : HostSemantics H),
        Sim.HostParametric host → EquivUpTo σ P host l.toCore M

end Silmaril.Wasm.LimeCompile.Handle
