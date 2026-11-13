module

public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Structural.Defs
public import Silmaril.Wasm.Lime1.ToCore.Modules
public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Validation.Subtyping.Decide
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Relation

/-!
# Core 3.0 engines: static types, typed laws, and the Lime1 refinement hypothesis

A `Core3Engine` is a lawful `CoreEngine` that runs full WebAssembly Core 3.0 modules
(`Silmaril.Wasm.Module`) with the static semantics of Core 3.0 validation (`Validation/*`) and
satisfies the typed laws `Core3Engine.TypedLaws` (progress and preservation of core
activations at the canon boundary). These are the obligations that the concrete Core 3.0
semantics of the repository (`Execution/Core/*`, the single-threaded machine
`SingleThreaded/*` and its interpreter) discharges: `Core3.core3Engine o`
(`Engine/Core3/Instance.lean`) is a `Core3Engine` over the executable interpreter, with its
typed laws `Core3.core3Typed o` in `Engine/Core3/Typed.lean`. Its instantiation deviates from the
spec's `$instantiate` in allocating every global once (`$evalglobals`, then the direct
instantiation of the global-free residue, `Execution.Core.instantiateOnce?`); the engine with the
transcription's double-allocating instantiation (`Execution.Core.instantiateDirect?`) is
`core3SpecEngine o` (`Engine/Core3/Spec.lean`), which agrees with it on global-free modules and
up to a renaming of global addresses in general (`Engine/Core3/GlobalRen.lean`). This file only
states the obligations; generic theorems about Core 3.0 take an arbitrary `Core3Engine` (and,
where needed, a refinement hypothesis) as a parameter. `RefinesLime1` below is the old forward
statement, which cannot hold for the deterministic `core3Engine`; the restated `RefinesLime1'`
(Engine/Core3/Refines/Defs.lean) is proved for it (`Core3.Refines.refinesLime1`).
Nothing here is an axiom.

The structural, syntax-level helpers (`Core3.importTypes`, `Core3.exportTypes?`,
`Core3.StructurallyValid`, `Core3.exportFlatType?`, `Core3.ImportsMatch`, ...) are in
`Engine/Core3/Structural.lean`. The component validator's Core 3.0 profile works over the same
closed extern types as this interface (`Validation.Core3Extern`, `Validation/Defs.lean`).

## The structure `Core3Engine`

A `Core3Engine` packages an engine `E : CoreEngine` with

* `modules : E.Module ≃ Silmaril.Wasm.Module`.
* `funcTypes : E.FuncType ≃ DefType`: function types are closed defined types
  (`Validation/DefTypes.lean`).
* `externTypes : E.ExternType ≃ {τ : CExternType // ExternTypeOk {} τ}`: extern types are
  closed extern types (the spec's `$clos_externtype`) valid in the empty context. Closed types
  carry no module-relative type indices, so the type `externType?` of an exporter's value and
  an importer's `importTypes` entry are directly comparable; validity in `{}` makes extern
  subtyping a preorder (`ExternSub.trans` needs a valid middle type).
* `externSub_iff`: import matching is extern subtyping in the empty context, `ExternSub {}`
  (the spec's `Externtype_sub`, as checked at instantiation). It is decidable
  (`Core3Engine.decExternSub`, from `ExternSub.decideEmpty`).
* `ofFlatType_eq`, `flatType?_eq`: a canon host function with flat signature `ft` gets the
  defined type `V1.FuncType.toDefType ft` (a singleton final recursive group); the partial
  inverse is `SingleThreaded.flatType?` (`Core3Engine.flatType?_funcType`). A defined type has a
  flat signature only if it is such a group: a function whose type is declared in a larger
  recursive group has none, even when it expands to a numeric signature.
* `valid_iff`: validity is Core 3.0 module validation `ModuleValid` (`Validation/Modules.lean`,
  decided by the validator `validate?`).
* `importTypes_eq`, `exportTypes_eq`: for a module accepted by the validator,
  `validate? m = some mt`, the import and export types are `mt.imports` and `mt.exports`,
  paired positionally with the names of `m.imports` and `m.exports`. Nothing is claimed for
  modules the validator rejects.
* `lawful : E.Lawful` (Engine/Laws.lean).
* `typed : Core3Engine.TypedLaws E`.

## The typed laws `Core3Engine.TypedLaws`

The untyped laws `Lawful` give no progress, and `CoreEngine.ResumeLawful` does not hold for
Core 3.0: resuming a callout with values of the host function's result types may reach
another callout immediately (in `ref.func $h2; call $h1; call_ref $t`, with `$h1` and `$h2`
host functions whose results are empty, resuming `$h1` with `[]` leaves
`ref (func h2) :: call_ref ...`, where `SingleThreaded.decompose?` at once finds the callout
of `$h2`), and nothing types a resumption with ill-typed values. `TypedLaws` states
progress and preservation over abstract typing predicates:

* predicates: `StoreOk s` (a well-typed store), `Ext s s'` (typed store extension, reflexive
  on `StoreOk` stores and transitive), `ThreadOk s t rs` (the activation `t` is typed in `s`
  with flat result types `rs`) and `HostTyped s h ft` (the host code `h` is consistent with the
  flat type `ft` in `s`; in `Core3.core3Typed` (`Core3.HostTypedE`): every host function of `s`
  with code `h` has type `ofFlatType ft`, which is vacuous while there is none);
* closure laws: the empty store is `StoreOk` and consistent with every host typing
  (`empty_ok`, `empty_hostTyped`); `allocHost`, `memWrite?` and `prepare?` (of a valid module
  whose imports match, `Core3.ImportsMatch`) preserve `StoreOk` and extend the store
  (`allocHost_ok`, `memWrite_ok`, `prepare_ok`); host typing persists through memory writes,
  instantiation and internal steps, and through `allocHost s ft h` for every code other than
  `h` and for `h` at `ft` (`allocHost_hostTyped`); invoking a function with a flat signature on
  arguments of its parameter types gives a typed activation (`invoke_ok`), and so does the start
  function returned by `prepare?` (at `[] -> []`); typing survives store extension
  (`threadOk_ext`) and internal steps (`internal_ok`, subject reduction);
* obligations on typed activations in `StoreOk` stores: a `running` activation can step
  (`running_progress`); it is never `stuck` (`not_stuck`); returned values have the result
  types (`returned_typed`); callout arguments have the parameter types of the host code's type
  (`callout_typed`); resuming a callout, at any extended `StoreOk` store, with values of the
  host code's result types or with a trap gives a typed activation (`resume_ok`).

The predicates are not vacuous: starting from the empty store, the closure laws establish them
along every engine operation, provided each host code is only ever allocated at one flat type
(`TypedLaws.allocHost_invoke_ok`, `TypedLaws.steps_ok`, `TypedLaws.steps_not_stuck`). The
concrete instance `Core3.core3Typed` takes `StoreOk` to be `Core3.StoreOkE`
(`Execution.Core.StoreOk` together with "every host function has a flat type"), `Ext` to be
`Execution.Core.Extend`, `ThreadOk` to be `Core3.ThreadOkE` (`SingleThreaded.ThreadOk` at
numeric result types) and `HostTyped` to be `Core3.HostTypedE`; its sources are the Core
soundness facts
`SingleThreaded.status_ne_stuck`, `SingleThreaded.Internal.preserves`,
`SingleThreaded.resume_typed`, `SingleThreaded.resume_progress`, `SingleThreaded.status_flat`,
`SingleThreaded.status_throw`, `Execution.Core.invoke_ok` and, for instantiation,
`Core3.prepareE?_typed` (over `Execution.Core.instantiateOnce?`: `$evalglobals`, then
`Execution.Core.instantiateDirect?` of the global-free residue).

Exceptions: a Core 3.0 exception escaping the outermost activation of a canon call must be
reported as `.returned .trap` (REF `call_and_trap_on_throw`, design/mvp/canonical-abi/
definitions.py line 2161 at component-model a25fc0b). `Status` has no exception constructor,
so this is not an abstract law; its formal content is `not_stuck` with `running_progress`: a
typed activation never reports an escaped exception as `stuck`, nor as `running` without a
step. For the concrete semantics it is `SingleThreaded.status_throw`.

Further remarks, not stated formally:

* memory64: `memAddrType?` may return `.i64` (in `Core3.core3`, the memory's own address
  type), so the canonical ABI selects its 64-bit pointer variants on i64 memories; no example
  exercises this for `Core3.core3` (kernel-checked Core 3.0 examples have no linear memory).
* Multiple memories and tables: each is a separate `MemAddr`/`TableAddr`, selected by the canon
  options; nothing in the interface changes.
* Values: `FlatValue` is the canon boundary type; references, exceptions and `v128` stay inside
  the engine.

## The old refinement hypothesis `RefinesLime1`

`RefinesLime1` is the OLD, forward statement of the Lime1 refinement. It cannot hold for the
deterministic `core3Engine o` (see below), and it is superseded by the restated `RefinesLime1'`
(Engine/Core3/Refines/Defs.lean: backward stuttering refinement with progress), which is proved
for `core3Engine o` as `Core3.Refines.refinesLime1` (Engine/Core3/Refines/Instance.lean).

`RefinesLime1 C L ofLime1` says that on images `m.toCore` of Lime1 modules
(`Silmaril.Wasm.Lime1.Module.toCore`, Lime1/ToCore/Modules.lean) the Core 3.0 engine `C`
behaves like the Lime1-like engine `L` on `ofLime1 m` (for the Lime1 engine of `Engine/Lime1.lean`,
`ofLime1 := id`). It is the existence of a `Lime1Simulation`: relations on stores, threads,
addresses, external values and instances such that

* import checking agrees: import names coincide and a related value matches an `L` import
  type iff it matches the `C` one (`importMatch`, derived `importsMatch_iff`); so the
  instantiator's `ExternSub`/`externType?` check succeeds in both engines or in neither;
* empty stores, host allocation, instantiation (`prepare?`, for `L`-valid modules and imports
  that match in `L`), exports, invocation (with arguments typed by the flat signature) and
  resumption preserve the relations;
* related configurations that are not `stuck` in `L` have EQUAL statuses (so the same
  callouts with the same arguments, and the same returned values or traps); where `L` is stuck
  (ill-typed code or values) `C` is unconstrained;
* related memories have equal address types, sizes and contents, writes preserve the relation,
  and related tables hold related function references;
* every `L` internal step is matched by zero or more `C` internal steps, and every `C`
  internal step by zero or more `L` steps (a stuttering bisimulation; divergence preservation
  is NOT part of the hypothesis). Consequently observable-trace agreement transfers only for
  FINITE runs and finite prefixes: an infinite silent run of one engine may be matched by a
  finite run of the other. Downstream statements should be phrased over finite traces.

Static module types are not part of the hypothesis: the `C` side is tied to the validator
`validate?` by `Core3Engine.importTypes_eq`/`exportTypes_eq`, and relating Lime1 module types
to those of `m.toCore` is a statement for the validation layer.

It is not proved for any concrete engine and is never assumed as an axiom: the old theorems
that need it take it (or a `Lime1Simulation`) as a hypothesis. `step_forward` asks `C` to match
every internal step of `L`. Lime1 is nondeterministic (it may return any NaN payload of the Wasm
3.0 NaN-propagation result sets and may fail any `memory.grow`, Lime1/Execution/Step.lean),
while `core3Engine o` is deterministic (canonical NaNs, grow failure decided by `o`), so a Lime1
step that picks another payload, or a grow failure that `o` does not pick, has no Core 3.0
counterpart and `core3Engine o` cannot satisfy it. The derived lemmas below (`steps_forward`,
`steps_backward`, `returned_forward`, `callout_forward`,
`RefinesLime1.allocHost_returned`, `importsMatch_iff`) are proved.

Example of use in a profile theorem (schematic; the component-level names are from later
items):

```
theorem lime1_profile_transfer (C : Core3Engine) (hR : RefinesLime1 C lime1 id) ... :
    ... := by
  obtain ⟨R⟩ := hR
  -- relate the instantiated stores with `R.prepare`, then transport each core activation
  -- of the Lime1 run with `R.returned_forward` / `R.callout_forward`
  ...
```
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

/-! ## Typed laws -/

/-- The typed laws of a Core 3.0 engine: abstract typing predicates on stores, activations and
host code, closed under every engine operation the component runtime performs, with progress
and typed results, callouts and resumption for typed activations. See the module docstring. -/
structure Core3Engine.TypedLaws (E : CoreEngine) where
  /-- Well-typed stores. -/
  StoreOk : {H : Type} → E.Store H → Prop
  /-- Typed store extension. -/
  Ext : {H : Type} → E.Store H → E.Store H → Prop
  /-- `ThreadOk s t rs`: the activation `t` is typed in `s` with flat result types `rs`. -/
  ThreadOk : {H : Type} → E.Store H → E.Thread H → List NumType → Prop
  /-- `HostTyped s h ft`: the host code `h` is consistent with the flat type `ft` in `s`
  (in `Core3.core3Typed`: every host function of `s` with code `h` has type `ofFlatType ft`). -/
  HostTyped : {H : Type} → E.Store H → H → V1.FuncType → Prop
  /-- Typed store extension is reflexive on well-typed stores. -/
  ext_refl : ∀ {H : Type} {s : E.Store H}, StoreOk s → Ext s s
  ext_trans : ∀ {H : Type} {s₁ s₂ s₃ : E.Store H}, Ext s₁ s₂ → Ext s₂ s₃ → Ext s₁ s₃
  /-- The empty store is well typed. -/
  empty_ok : ∀ H, StoreOk (E.empty H)
  /-- The empty store has no host function, so it is consistent with every host typing. -/
  empty_hostTyped : ∀ {H : Type} (h : H) (ft : V1.FuncType), HostTyped (E.empty H) h ft
  /-- Host allocation preserves typing and extends the store. -/
  allocHost_ok : ∀ {H : Type} {s s' : E.Store H} {ft h a}, StoreOk s →
    E.allocHost s ft h = (s', a) → StoreOk s' ∧ Ext s s'
  /-- Host allocation keeps every host typing except that of the allocated code at another
  type. -/
  allocHost_hostTyped : ∀ {H : Type} {s s' : E.Store H} {ft h a} {h' : H} {ft' : V1.FuncType},
    E.allocHost s ft h = (s', a) → HostTyped s h' ft' → (h' = h → ft' = ft) →
      HostTyped s' h' ft'
  /-- Memory writes preserve typing, extend the store and keep every host typing. -/
  memWrite_ok : ∀ {H : Type} {s s' : E.Store H} {m st bs}, StoreOk s →
    E.memWrite? s m st bs = some s' →
      StoreOk s' ∧ Ext s s' ∧ ∀ h ft, HostTyped s h ft → HostTyped s' h ft
  /-- Instantiation of a valid module with matching imports preserves typing; the returned
  start function (type `[] -> []`) gives a typed activation. -/
  prepare_ok : ∀ {H : Type} {s s' : E.Store H} {m imps i st}, StoreOk s → E.Valid m →
    Core3.ImportsMatch E s imps m → E.prepare? s m imps = some (s', i, st) →
      StoreOk s' ∧ Ext s s' ∧ (∀ h ft, HostTyped s h ft → HostTyped s' h ft) ∧
        ∀ a, st = some a → ThreadOk s' (E.invoke a []) []
  /-- Invoking a function with a flat signature on arguments of its parameter types. -/
  invoke_ok : ∀ {H : Type} {s : E.Store H} {a ft} {args : List FlatValue}, StoreOk s →
    (E.funcType? s a).bind E.flatType? = some ft → args.map (·.type) = ft.params →
      ThreadOk s (E.invoke a args) ft.results
  /-- Typing of an activation survives store extension (parked activations stay typed while
  other activations and instantiations run). -/
  threadOk_ext : ∀ {H : Type} {s s' : E.Store H} {t rs}, StoreOk s → ThreadOk s t rs →
    Ext s s' → StoreOk s' → ThreadOk s' t rs
  /-- Subject reduction: internal steps of typed activations preserve typing, extend the store
  and keep every host typing. -/
  internal_ok : ∀ {H : Type} {s s' : E.Store H} {t t' rs}, StoreOk s → ThreadOk s t rs →
    E.Internal (s, t) (s', t') →
      StoreOk s' ∧ ThreadOk s' t' rs ∧ Ext s s' ∧ ∀ h ft, HostTyped s h ft → HostTyped s' h ft
  /-- Progress: a typed `running` activation can step. -/
  running_progress : ∀ {H : Type} {s : E.Store H} {t rs}, StoreOk s → ThreadOk s t rs →
    E.status s t = .running → ∃ c', E.Internal (s, t) c'
  /-- Typed activations are never `stuck` (in particular an escaped exception is not). -/
  not_stuck : ∀ {H : Type} {s : E.Store H} {t rs}, StoreOk s → ThreadOk s t rs →
    E.status s t ≠ .stuck
  /-- Returned values have the activation's result types. -/
  returned_typed : ∀ {H : Type} {s : E.Store H} {t rs} {vs : List FlatValue}, StoreOk s →
    ThreadOk s t rs → E.status s t = .returned (.values vs) → vs.map (·.type) = rs
  /-- Callout arguments have the parameter types of the host code's flat type. -/
  callout_typed : ∀ {H : Type} {s : E.Store H} {t rs h ft} {args : List FlatValue},
    StoreOk s → ThreadOk s t rs → HostTyped s h ft → E.status s t = .callout h args →
      args.map (·.type) = ft.params
  /-- Resuming a callout at an extended `StoreOk` store, with a trap or with values of the
  result types of a flat type of the host code, gives a typed activation. -/
  resume_ok : ∀ {H : Type} {s s' : E.Store H} {t rs h} {args : List FlatValue}
    {r : CallResult}, StoreOk s → ThreadOk s t rs → E.status s t = .callout h args →
      Ext s s' → StoreOk s' →
      (r = .trap ∨ ∃ (ft : V1.FuncType) (vs : List FlatValue), HostTyped s h ft ∧
        r = .values vs ∧ vs.map (·.type) = ft.results) →
        ThreadOk s' (E.resume s' t r) rs

namespace Core3Engine.TypedLaws

variable {E : CoreEngine} (T : Core3Engine.TypedLaws E)

end Core3Engine.TypedLaws

/-! ## The engine -/

/-- A Core 3.0 engine: a lawful `CoreEngine` whose modules are Core 3.0 modules, whose function
and extern types are closed Core 3.0 types (up to the given equivalences), with Core 3.0 module
validation, import matching and validator-computed import/export types, satisfying the typed
laws. See the module docstring. -/
structure Core3Engine where
  /-- The underlying engine. -/
  E : CoreEngine
  modules : E.Module ≃ Wasm.Module
  /-- Function types are closed defined types. -/
  funcTypes : E.FuncType ≃ Wasm.Validation.DefType
  /-- Extern types are closed extern types valid in the empty context. -/
  externTypes : E.ExternType ≃
    {τ : Wasm.Validation.CExternType // Wasm.Validation.ExternTypeOk {} τ}
  /-- Canon host functions get the defined types of their flat signatures. -/
  ofFlatType_eq : ∀ ft, funcTypes (E.ofFlatType ft) = ft.toDefType
  flatType?_eq : ∀ t, E.flatType? t = SingleThreaded.flatType? (funcTypes t)
  /-- Import matching is extern subtyping in the empty context. -/
  externSub_iff : ∀ a b,
    E.ExternSub a b ↔ Wasm.Validation.ExternSub {} (externTypes a).1 (externTypes b).1
  /-- Validity is Core 3.0 module validation. -/
  valid_iff : ∀ m, E.Valid m ↔ Wasm.Validation.ModuleValid (modules m)
  /-- Import types of a validated module are the validator's, named by the module's imports. -/
  importTypes_eq : ∀ m mt, Wasm.Validation.validate? (modules m) = some mt →
    (E.importTypes m).map (fun p => (p.1, p.2.1, (externTypes p.2.2).1)) =
      ((modules m).imports.zip mt.imports).map fun p => (p.1.moduleName, p.1.name, p.2)
  /-- Export types of a validated module are the validator's, named by the module's exports. -/
  exportTypes_eq : ∀ m mt, Wasm.Validation.validate? (modules m) = some mt →
    (E.exportTypes m).map (fun p => (p.1, (externTypes p.2).1)) =
      ((modules m).exports.zip mt.exports).map fun p => (p.1.name, p.2)
  lawful : E.Lawful
  typed : Core3Engine.TypedLaws E

namespace Core3Engine

variable (C : Core3Engine)

instance : C.E.Lawful := C.lawful

/-- A Core 3.0 module as a module of the engine. -/
def ofCore (m : Wasm.Module) : C.E.Module := C.modules.symm m

@[simp] theorem modules_ofCore (m : Wasm.Module) : C.modules (C.ofCore m) = m :=
  C.modules.apply_symm_apply m

/-- Import matching of a Core 3.0 engine is decidable (`externSub_iff`,
`ExternSub.decideEmpty`). -/
def decExternSub (a b : C.E.ExternType) : Decidable (C.E.ExternSub a b) :=
  haveI := Wasm.Validation.ExternSub.decideEmpty (C.externTypes a).1 (C.externTypes b).1
    (C.externTypes a).2 (C.externTypes b).2
  decidable_of_iff _ (C.externSub_iff a b).symm

end Core3Engine

/-! ## The refinement hypothesis -/

/-- A stuttering simulation between a Lime1-like engine `L` (on modules `ofLime1 m`) and a
Core 3.0 engine `C` (on modules `m.toCore`). See the module docstring.

The behavioural fields are restricted to well-typed uses, so that a Core 3.0 engine that
treats ill-typed inputs differently from `L` (e.g. traps where Lime1 is `stuck`) can still
satisfy it: `prepare` assumes the imports match in `L` (`Core3.ImportsMatch`), `invoke`
assumes arguments typed by the function's flat signature, and `status` only constrains
configurations that are not `stuck` in `L`. `resume` is not restricted (the callout status
does not carry the host function's type); a `C` engine may only deviate on ill-typed results
where `L` becomes `stuck`. -/
structure Lime1Simulation (C : Core3Engine) (L : CoreEngine)
    (ofLime1 : Silmaril.Wasm.Lime1.Module → L.Module) where
  StoreRel : {H : Type} → L.Store H → C.E.Store H → Prop
  ThreadRel : {H : Type} → L.Thread H → C.E.Thread H → Prop
  FuncRel : L.FuncAddr → C.E.FuncAddr → Prop
  MemRel : L.MemAddr → C.E.MemAddr → Prop
  TableRel : L.TableAddr → C.E.TableAddr → Prop
  GlobalRel : L.GlobalAddr → C.E.GlobalAddr → Prop
  ExternRel : L.ExternVal → C.E.ExternVal → Prop
  InstRel : L.Inst → C.E.Inst → Prop
  /-- Valid Lime1 modules have valid Core 3.0 images. -/
  valid : ∀ m, L.Valid (ofLime1 m) → C.E.Valid (C.ofCore m.toCore)
  empty : ∀ H, StoreRel (L.empty H) (C.E.empty H)
  /-- Import checking agrees: the import lists have the same names, and a related value in
  related stores matches the `L` import type iff it matches the `C` one (with each engine's
  own `externType?`/`ExternSub`, so no common type frame is needed). -/
  importMatch : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} m,
    StoreRel sL sC → L.Valid (ofLime1 m) →
      List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ ∀ v v', ExternRel v v' →
          ((∃ τ, L.externType? sL v = some τ ∧ L.ExternSub τ p.2.2) ↔
            (∃ τ, C.E.externType? sC v' = some τ ∧ C.E.ExternSub τ q.2.2)))
        (L.importTypes (ofLime1 m)) (C.E.importTypes (C.ofCore m.toCore))
  /-- Instantiation of a valid module with related, well-typed imports: both fail or both
  succeed with related stores, instances and start functions. -/
  prepare : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {m impsL impsC},
    StoreRel sL sC → L.Valid (ofLime1 m) → List.Forall₂ ExternRel impsL impsC →
      Core3.ImportsMatch L sL impsL (ofLime1 m) →
      Option.Rel (fun a b => StoreRel a.1 b.1 ∧ InstRel a.2.1 b.2.1 ∧
          Option.Rel FuncRel a.2.2 b.2.2)
        (L.prepare? sL (ofLime1 m) impsL) (C.E.prepare? sC (C.ofCore m.toCore) impsC)
  exports : ∀ {i i'}, InstRel i i' →
    List.Forall₂ (fun a b => a.1 = b.1 ∧ ExternRel a.2 b.2) (L.exports i) (C.E.exports i')
  asFunc : ∀ {v v'}, ExternRel v v' → Option.Rel FuncRel (L.asFunc? v) (C.E.asFunc? v')
  asMemory : ∀ {v v'}, ExternRel v v' → Option.Rel MemRel (L.asMemory? v) (C.E.asMemory? v')
  asTable : ∀ {v v'}, ExternRel v v' → Option.Rel TableRel (L.asTable? v) (C.E.asTable? v')
  asGlobal : ∀ {v v'}, ExternRel v v' →
    Option.Rel GlobalRel (L.asGlobal? v) (C.E.asGlobal? v')
  ofFunc : ∀ {a a'}, FuncRel a a' → ExternRel (L.ofFunc a) (C.E.ofFunc a')
  allocHost : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} (ft : V1.FuncType) (h : H),
    StoreRel sL sC →
      StoreRel (L.allocHost sL ft h).1 (C.E.allocHost sC ft h).1 ∧
        FuncRel (L.allocHost sL ft h).2 (C.E.allocHost sC ft h).2
  /-- Related functions have the same flat signature. -/
  flatType : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {a a'},
    StoreRel sL sC → FuncRel a a' →
      (L.funcType? sL a).bind L.flatType? = (C.E.funcType? sC a').bind C.E.flatType?
  memAddrType : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {m m'},
    StoreRel sL sC → MemRel m m' → L.memAddrType? sL m = C.E.memAddrType? sC m'
  memSize : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {m m'},
    StoreRel sL sC → MemRel m m' → L.memSize? sL m = C.E.memSize? sC m'
  memRead : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {m m'} (st len : Nat),
    StoreRel sL sC → MemRel m m' → L.memRead? sL m st len = C.E.memRead? sC m' st len
  memWrite : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {m m'} (st : Nat) (bs : ByteArray),
    StoreRel sL sC → MemRel m m' →
      Option.Rel StoreRel (L.memWrite? sL m st bs) (C.E.memWrite? sC m' st bs)
  tableAddrType : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {t t'},
    StoreRel sL sC → TableRel t t' → L.tableAddrType? sL t = C.E.tableAddrType? sC t'
  tableFunc : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {t t'} (i : Nat),
    StoreRel sL sC → TableRel t t' →
      Option.Rel (Option.Rel FuncRel) (L.tableFunc? sL t i) (C.E.tableFunc? sC t' i)
  /-- Invocations of related functions with arguments typed by their flat signature are
  related. -/
  invoke : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {a a'} {ft : V1.FuncType}
    (args : List FlatValue), StoreRel sL sC → FuncRel a a' →
      (L.funcType? sL a).bind L.flatType? = some ft → args.map (·.type) = ft.params →
      ThreadRel (L.invoke (H := H) a args) (C.E.invoke a' args)
  /-- Related configurations that are not `stuck` in `L` have equal statuses. -/
  status : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {t t'},
    StoreRel sL sC → ThreadRel t t' → L.status sL t ≠ .stuck →
      L.status sL t = C.E.status sC t'
  resume : ∀ {H : Type} {sL : L.Store H} {sC : C.E.Store H} {t t'} (r : CallResult),
    StoreRel sL sC → ThreadRel t t' → ThreadRel (L.resume sL t r) (C.E.resume sC t' r)
  /-- Forward simulation: one `L` step is matched by zero or more `C` steps. -/
  step_forward : ∀ {H : Type} {sL sL₁ : L.Store H} {sC : C.E.Store H} {t t₁ t'},
    StoreRel sL sC → ThreadRel t t' → L.Internal (sL, t) (sL₁, t₁) →
      ∃ sC₁ t₁', C.E.Steps (sC, t') (sC₁, t₁') ∧ StoreRel sL₁ sC₁ ∧ ThreadRel t₁ t₁'
  /-- Backward simulation: one `C` step is matched by zero or more `L` steps. -/
  step_backward : ∀ {H : Type} {sL : L.Store H} {sC sC₁ : C.E.Store H} {t t' t₁'},
    StoreRel sL sC → ThreadRel t t' → C.E.Internal (sC, t') (sC₁, t₁') →
      ∃ sL₁ t₁, L.Steps (sL, t) (sL₁, t₁) ∧ StoreRel sL₁ sC₁ ∧ ThreadRel t₁ t₁'

/-- The old, forward refinement hypothesis: the Core 3.0 engine `C` refines the Lime1-like
engine `L` along `Silmaril.Wasm.Lime1.Module.toCore`. NOT proved and NOT an axiom: theorems that
need it take it as a hypothesis. It cannot hold for the deterministic `core3Engine o`
(`step_forward` would have to match Lime1's NaN and `memory.grow` choices); the restated
`RefinesLime1'` (Engine/Core3/Refines/Defs.lean) is the one proved for it,
`Core3.Refines.refinesLime1`. -/
def RefinesLime1 (C : Core3Engine) (L : CoreEngine)
    (ofLime1 : Silmaril.Wasm.Lime1.Module → L.Module) : Prop :=
  Nonempty (Lime1Simulation C L ofLime1)

namespace Lime1Simulation

variable {C : Core3Engine} {L : CoreEngine} {ofLime1 : Silmaril.Wasm.Lime1.Module → L.Module}
  (R : Lime1Simulation C L ofLime1)

end Lime1Simulation

end Silmaril.Wasm.Component.Engine
