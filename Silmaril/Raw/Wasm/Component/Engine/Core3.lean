module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Defs

public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Structural
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

namespace Core3Engine.TypedLaws

variable {E : CoreEngine} (T : Core3Engine.TypedLaws E)

/-- Runs of internal steps from a typed activation stay typed, extend the store and keep every
host typing. -/
theorem steps_ok {H : Type} {s s' : E.Store H} {t t' : E.Thread H} {rs : List NumType}
    (hs : T.StoreOk s) (ht : T.ThreadOk s t rs) (h : E.Steps (s, t) (s', t')) :
    T.StoreOk s' ∧ T.ThreadOk s' t' rs ∧ T.Ext s s' ∧
      ∀ hc ft, T.HostTyped s hc ft → T.HostTyped s' hc ft := by
  suffices ∀ c : E.Config H, E.Steps (s, t) c → T.StoreOk c.1 ∧ T.ThreadOk c.1 c.2 rs ∧
      T.Ext s c.1 ∧ ∀ hc ft, T.HostTyped s hc ft → T.HostTyped c.1 hc ft from this _ h
  intro c hc
  induction hc with
  | refl => exact ⟨hs, ht, T.ext_refl hs, fun _ _ e => e⟩
  | @tail b c _ step ih =>
    obtain ⟨hs₁, ht₁, he₁, hh₁⟩ := ih
    obtain ⟨hs₂, ht₂, he₂, hh₂⟩ := T.internal_ok (s := b.1) (t := b.2) (s' := c.1) (t' := c.2)
      hs₁ ht₁ step
    exact ⟨hs₂, ht₂, T.ext_trans he₁ he₂, fun hc ft e => hh₂ hc ft (hh₁ hc ft e)⟩

/-- No configuration reachable from a typed activation is `stuck`. -/
theorem steps_not_stuck {H : Type} {s s' : E.Store H} {t t' : E.Thread H} {rs : List NumType}
    (hs : T.StoreOk s) (ht : T.ThreadOk s t rs) (h : E.Steps (s, t) (s', t')) :
    E.status s' t' ≠ .stuck :=
  let ⟨hs', ht', _⟩ := T.steps_ok hs ht h
  T.not_stuck hs' ht'

/-- The typing predicates are satisfiable: a host function allocated in the empty store,
invoked with arguments of its flat parameter types, is a typed activation in a `StoreOk`
store, and its host code is typed by its flat type. -/
theorem allocHost_invoke_ok [L : E.Lawful] {H : Type} (ft : V1.FuncType) (h : H)
    {args : List FlatValue} (hargs : args.map (·.type) = ft.params) :
    T.StoreOk (E.allocHost (E.empty H) ft h).1 ∧
      T.ThreadOk (E.allocHost (E.empty H) ft h).1
        (E.invoke (E.allocHost (E.empty H) ft h).2 args) ft.results ∧
      T.HostTyped (E.allocHost (E.empty H) ft h).1 h ft := by
  have e := (Prod.mk.eta (p := E.allocHost (E.empty H) ft h)).symm
  obtain ⟨hs, -⟩ := T.allocHost_ok (T.empty_ok H) e
  refine ⟨hs, T.invoke_ok hs ?_ hargs,
    T.allocHost_hostTyped e (T.empty_hostTyped h ft) fun _ => rfl⟩
  rw [L.allocHost_funcType e]
  exact L.flatType?_ofFlatType ft

end Core3Engine.TypedLaws

/-! ## The engine -/

namespace Core3Engine

variable (C : Core3Engine)

/-- The engine's flat-type view: a function type has flat signature `ft` exactly when it is the
defined type of `ft`. -/
theorem flatType?_funcType (t : C.E.FuncType) (ft : V1.FuncType) :
    C.E.flatType? t = some ft ↔ C.funcTypes t = ft.toDefType := by
  rw [C.flatType?_eq]
  constructor
  · intro h
    exact (SingleThreaded.flatType?_sound h).symm
  · intro h
    rw [h]
    exact SingleThreaded.flatType?_ofFlatType ft

end Core3Engine

/-! ## The refinement hypothesis -/

namespace Lime1Simulation

variable {C : Core3Engine} {L : CoreEngine} {ofLime1 : Silmaril.Wasm.Lime1.Module → L.Module}
  (R : Lime1Simulation C L ofLime1)

/-- Import matching of related value lists agrees in the two engines (the instantiator's
import check succeeds in `L` iff it succeeds in `C`). -/
theorem importsMatch_iff {H : Type} {sL : L.Store H} {sC : C.E.Store H} {m}
    {impsL : List L.ExternVal} {impsC : List C.E.ExternVal} (hs : R.StoreRel sL sC)
    (hv : L.Valid (ofLime1 m)) (hi : List.Forall₂ R.ExternRel impsL impsC) :
    Core3.ImportsMatch L sL impsL (ofLime1 m) ↔
      Core3.ImportsMatch C.E sC impsC (C.ofCore m.toCore) := by
  unfold Core3.ImportsMatch
  have ht := R.importMatch m hs hv
  generalize L.importTypes (ofLime1 m) = tsL at ht ⊢
  generalize C.E.importTypes (C.ofCore m.toCore) = tsC at ht ⊢
  induction hi generalizing tsL tsC with
  | nil =>
    cases ht with
    | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
    | cons _ _ => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | cons hx _ ih =>
    cases ht with
    | nil => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | cons hp hrest =>
      constructor
      · intro h
        cases h with
        | cons h₁ h₂ => exact .cons ((hp.2.2 _ _ hx).1 h₁) ((ih _ _ hrest).1 h₂)
      · intro h
        cases h with
        | cons h₁ h₂ => exact .cons ((hp.2.2 _ _ hx).2 h₁) ((ih _ _ hrest).2 h₂)

/-- Finite `L` runs are matched by finite `C` runs ending in related configurations. -/
theorem steps_forward {H : Type} {sL sL₁ : L.Store H} {sC : C.E.Store H} {t t₁ t'}
    (hs : R.StoreRel sL sC) (ht : R.ThreadRel t t') (h : L.Steps (sL, t) (sL₁, t₁)) :
    ∃ sC₁ t₁', C.E.Steps (sC, t') (sC₁, t₁') ∧ R.StoreRel sL₁ sC₁ ∧ R.ThreadRel t₁ t₁' := by
  suffices ∀ c : L.Config H, L.Steps c (sL₁, t₁) → ∀ sC t', R.StoreRel c.1 sC →
      R.ThreadRel c.2 t' →
      ∃ sC₁ t₁', C.E.Steps (sC, t') (sC₁, t₁') ∧ R.StoreRel sL₁ sC₁ ∧ R.ThreadRel t₁ t₁' from
    this _ h sC t' hs ht
  intro c hc
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun sC t' hs ht => ⟨sC, t', Relation.ReflTransGen.refl, hs, ht⟩
  | head step _ ih =>
    intro sC t' hs ht
    obtain ⟨sC₂, t₂', hC, hs₂, ht₂⟩ := R.step_forward hs ht step
    obtain ⟨sC₁, t₁', hC', hs₁, ht₁⟩ := ih sC₂ t₂' hs₂ ht₂
    exact ⟨sC₁, t₁', hC.trans hC', hs₁, ht₁⟩

/-- Finite `C` runs are matched by finite `L` runs ending in related configurations. -/
theorem steps_backward {H : Type} {sL : L.Store H} {sC sC₁ : C.E.Store H} {t t' t₁'}
    (hs : R.StoreRel sL sC) (ht : R.ThreadRel t t') (h : C.E.Steps (sC, t') (sC₁, t₁')) :
    ∃ sL₁ t₁, L.Steps (sL, t) (sL₁, t₁) ∧ R.StoreRel sL₁ sC₁ ∧ R.ThreadRel t₁ t₁' := by
  suffices ∀ c : C.E.Config H, C.E.Steps c (sC₁, t₁') → ∀ sL t, R.StoreRel sL c.1 →
      R.ThreadRel t c.2 →
      ∃ sL₁ t₁, L.Steps (sL, t) (sL₁, t₁) ∧ R.StoreRel sL₁ sC₁ ∧ R.ThreadRel t₁ t₁' from
    this _ h sL t hs ht
  intro c hc
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun sL t hs ht => ⟨sL, t, Relation.ReflTransGen.refl, hs, ht⟩
  | head step _ ih =>
    intro sL t hs ht
    obtain ⟨sL₂, t₂, hL, hs₂, ht₂⟩ := R.step_backward hs ht step
    obtain ⟨sL₁, t₁, hL', hs₁, ht₁⟩ := ih sL₂ t₂ hs₂ ht₂
    exact ⟨sL₁, t₁, hL.trans hL', hs₁, ht₁⟩

/-- An `L` activation that returns `r` (values or trap) is matched by a `C` activation that
returns the same `r`, with related final stores (hence equal memory contents). -/
theorem returned_forward {H : Type} {sL sL₁ : L.Store H} {sC : C.E.Store H} {a a'}
    {ft : V1.FuncType} {args : List FlatValue} {t₁ r} (hs : R.StoreRel sL sC)
    (ha : R.FuncRel a a') (hft : (L.funcType? sL a).bind L.flatType? = some ft)
    (hargs : args.map (·.type) = ft.params)
    (h : L.Steps (sL, L.invoke a args) (sL₁, t₁)) (hr : L.status sL₁ t₁ = .returned r) :
    ∃ sC₁ t₁', C.E.Steps (sC, C.E.invoke a' args) (sC₁, t₁') ∧
      C.E.status sC₁ t₁' = .returned r ∧ R.StoreRel sL₁ sC₁ := by
  obtain ⟨sC₁, t₁', hC, hs₁, ht₁⟩ := R.steps_forward hs (R.invoke args hs ha hft hargs) h
  exact ⟨sC₁, t₁', hC, (R.status hs₁ ht₁ (by simp [hr])) ▸ hr, hs₁⟩

/-- An `L` activation that parks on a callout is matched by a `C` activation parked on the same
callout with the same arguments. -/
theorem callout_forward {H : Type} {sL sL₁ : L.Store H} {sC : C.E.Store H} {t t₁ t'}
    {h : H} {args : List FlatValue} (hs : R.StoreRel sL sC) (ht : R.ThreadRel t t')
    (hL : L.Steps (sL, t) (sL₁, t₁)) (hc : L.status sL₁ t₁ = .callout h args) :
    ∃ sC₁ t₁', C.E.Steps (sC, t') (sC₁, t₁') ∧ C.E.status sC₁ t₁' = .callout h args ∧
      R.StoreRel sL₁ sC₁ ∧ R.ThreadRel t₁ t₁' := by
  obtain ⟨sC₁, t₁', hC, hs₁, ht₁⟩ := R.steps_forward hs ht hL
  exact ⟨sC₁, t₁', hC, (R.status hs₁ ht₁ (by simp [hc])) ▸ hc, hs₁, ht₁⟩

end Lime1Simulation

/-- `RefinesLime1` transports the observable result of activations: if the `L` activation of a
host function allocated in the empty store returns `r`, so does the corresponding `C`
activation. A minimal instance of how a profile theorem consumes the hypothesis. -/
theorem RefinesLime1.allocHost_returned {C : Core3Engine} {L : CoreEngine} [L.Lawful]
    {ofLime1 : Silmaril.Wasm.Lime1.Module → L.Module} (hR : RefinesLime1 C L ofLime1)
    {H : Type} (ft : V1.FuncType) (h : H) {args : List FlatValue} {sL₁ : L.Store H} {t₁ r}
    (hargs : args.map (·.type) = ft.params)
    (hL : L.Steps ((L.allocHost (L.empty H) ft h).1,
      L.invoke (L.allocHost (L.empty H) ft h).2 args) (sL₁, t₁))
    (hr : L.status sL₁ t₁ = .returned r) :
    ∃ sC₁ t₁', C.E.Steps ((C.E.allocHost (C.E.empty H) ft h).1,
        C.E.invoke (C.E.allocHost (C.E.empty H) ft h).2 args) (sC₁, t₁') ∧
      C.E.status sC₁ t₁' = .returned r := by
  obtain ⟨R⟩ := hR
  obtain ⟨hs, ha⟩ := R.allocHost ft h (R.empty H)
  have hft := CoreEngine.allocHost_flatType_of_extends (E := L)
    (Prod.mk.eta (p := L.allocHost (L.empty H) ft h)).symm (CoreEngine.Extends.refl _)
  obtain ⟨sC₁, t₁', hC, hst, _⟩ := R.returned_forward hs ha hft hargs hL hr
  exact ⟨sC₁, t₁', hC, hst⟩

end Silmaril.Wasm.Component.Engine
