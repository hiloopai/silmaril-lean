module

public import Silmaril.Wasm.Component.Reference.Instantiate.Root.Defs

-- Kernel computation uses the body of the upstream derived instance.
import all Batteries.Data.Except

public import Silmaril.Raw.Wasm.Component.Instantiate.Defs

/-!
# Root (host) instantiation

The host instantiates a root component with an argument map for its imports (Explainer.md,
"Instance Definitions"): `instantiateRoot recurse c args`
allocates the root component instance and runs `instantiateComponent` on the closure `⟨c, []⟩`
(a root component has no enclosing frames), returning the root instance and its exports. It is
a program of the specification carrier `Canon.P E σ`, run by the component machine; nested
instantiation goes through `recurse` (`Instantiate/Defs.lean`): the specification tie is
`instantiateRootCall` (`recurse := callRecurse`, a late-bound `Call.instantiate` resolved by
the dispatcher, so arbitrary nesting depth is bounded only by the machine's fuel); the fuel tie
`instantiateRootFuel` serves store-only tests without a machine.

The relaxations of wasmtime's root instantiation are NOT applied: every import must be
supplied. `instantiateRoot` checks `argsComplete` FIRST, before allocating the root instance
or running any definition (core instantiation, start function, resource allocation), and traps
`hostTrap "missing import"` otherwise, as wasmtime rejects a missing import at link /
instantiate-pre time before any core instantiation.

The supplied arguments are type-checked against the import descriptors (`importTypeCheck`:
functions, types and instances of them by type, core modules and components by sort; a
mismatch traps `hostTrap "import type mismatch: ..."`) also BEFORE any side effect, like
wasmtime, which type-checks every import (`crates/wasmtime/src/runtime/component/matching.rs`)
at link / instantiate-pre time before any core instantiation: `precheckImports` walks the
definitions of the root without running them,
building only the index spaces that import descriptors can read (types, instances and core
types, `typeRelevant`), and checks each `import` it reaches. The walk stops (without an error)
at the first definition whose type-relevant entry is only known by running it: a resource
type definition, an `alias export` of a type or instance out of an instance produced by
`instance (instantiate ...)` (which the walk records as an empty placeholder instance), an
outer alias past the root, a type whose resolution fails, or a 🪙 `start`/`value` definition.
Imports after that point are checked in definition order only, by the `import` row of
`instantiateDef` (which re-checks every import, for root and nested instantiation alike), so a
mismatch there traps after the side effects of the preceding definitions (start functions,
nested instantiations), unlike wasmtime. The walk reproduces the frame of `instantiateDef` on
the type-relevant index spaces only for valid components (validation restricts outer aliases
in type declarators to types, so resolving a type never reads the skipped index spaces).
`instantiateRoot_prechecked`: a root instantiation that returns (under a store handler) passed
the pre-check on its initial store. Core modules and components supplied as arguments are
checked by sort only (`expected module found instance` in `matching.rs`; their module and
component types are not computed), and a 🪙 value or an unallocated function supplied where a
typed entity is expected is rejected (`untypedImportMsg`), so the check is weaker than
wasmtime's `matching.rs`. wasmtime's `Linker` check against the validated component type
(module types compared, root component imports rejected, the arguments projected onto the
import types) is `linkCheck` / `instantiateLinkedTop` (`Instantiate/Link.lean`).

Deviation from wasmtime: a missing or ill-typed root argument is modelled as a trap (the
`hostTrap`s above), and the machine's trap rule locks the store down, so no later embedder
action is possible on that store. wasmtime instead reports a link error before any side effect
(`Linker::instantiate` / `instantiate_pre` return `Err`) and leaves the store usable for other
instantiations and calls. The host Embedding-API
assertion that the store is not locked down is a side condition of the machine rule that
starts a root instantiation, not part of this program (deviation D-f).

Theorems: `instantiateRoot_inv` / `instantiateRootFuel_inv` / `instantiateRootCall_inv` (the
store updates of root instantiation only append to arenas, `ArenasExtend`; for
`instantiateRootFuel` this covers the nested bodies, which run inline; for
`instantiateRootCall` it covers the root body's own `modify`s only, since nested bodies run as
separately dispatched programs: their dispatcher arm is covered by
`Canon.instantiateCallProg_inv`, and the composition across the machine is not proved here),
`instantiateRoot_prechecked` (see
above), `instantiateRoot_inst_fresh` (under a store handler, the returned
instance id was not allocated in the initial store; that it is allocated afterwards is proved
only for `allocInst` itself, `allocInst_fresh`, since later operations such as `call` are
unconstrained by a store handler), and kernel-checked runs of
small components on the Mock engine with a store-only interpreter (`Tests`), including the
import check with an inferred resource binder (`importCheck_resource_ok`/`_bad`,
`rtImporter_run_ok`/`_bad`), the rejection of untypable arguments (`precheck_value_for_func`,
`precheck_unallocated_func`, `precheck_unallocated_func_for_instance`,
`precheck_value_export_for_func`, `precheck_unallocated_func_run`) and the reach of the
pre-check (`precheck_after_instantiate`, `precheck_stops_at_resource`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Instantiate

open Engine Canon _root_.Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-! ## Import type pre-check -/

theorem instantiateRoot_inv {s₀ : CStore E} {recurse : Recurse E σ}
    (hrec : ∀ c a, P.Inv (ArenasExtend s₀) (recurse c a)) (c : Syntax.Component E.Module)
    (args : Exports E) : P.Inv (ArenasExtend s₀) (instantiateRoot recurse c args) :=
  P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind P.Inv.getStore fun _ =>
    P.Inv.bind (checkImport_inv _) fun _ => P.Inv.bind allocInst_inv fun inst =>
    P.Inv.bind (instantiateComponent_inv hrec _ args inst) fun _ => P.Inv.pure _

theorem instantiateRootFuel_inv {s₀ : CStore E} (fuel : Nat) (c : Syntax.Component E.Module)
    (args : Exports E) :
    P.Inv (ArenasExtend s₀) (instantiateRootFuel fuel c args : P E σ (InstId × Exports E)) :=
  instantiateRoot_inv (fun c a => instantiateFuel_inv fuel c a) c args

/-- The root body's store updates only append to arenas. Nested instantiations are late-bound
calls, unconstrained by `P.Inv`; their bodies are covered by `Canon.instantiateCallProg_inv`
(the dispatcher arm), not by this lemma. -/
theorem instantiateRootCall_inv {s₀ : CStore E} (c : Syntax.Component E.Module)
    (args : Exports E) :
    P.Inv (ArenasExtend s₀) (instantiateRootCall c args : P E σ (InstId × Exports E)) :=
  instantiateRoot_inv (fun c a => callRecurse_inv c a) c args

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- `allocInst` returns an instance id that was not allocated before and is allocated
afterwards with the initial instance state. -/
theorem allocInst_fresh {H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop}
    (hH : StoreHandler H) {s s' : CStore E} {i : InstId}
    (h : Prog.Eval (S := Eff E σ) H allocInst s i s') :
    s.inst? i = none ∧ s'.inst? i = some {} := by
  simp only [allocInst, allocObj, getStore, modifyStore, perform, Prog.lift,
    bind, Prog.bind, pure] at h
  obtain ⟨g, s₁, hg, h1⟩ := Prog.Eval.op_inv h
  obtain ⟨rfl, rfl⟩ := hH.1 _ _ _ hg
  obtain ⟨u, s₂, hm, h2⟩ := Prog.Eval.op_inv h1
  have hs₂ := hH.2 _ _ _ _ hm
  obtain ⟨rfl, rfl⟩ := Prog.Eval.pure_inv h2
  subst hs₂
  exact ⟨ArenaField.get?_fresh _ _, ArenaField.get?_alloc_self _ _ _⟩

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- Under a store handler, `getStore` returns the store and leaves it unchanged. -/
theorem getStore_eval {H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop}
    (hH : StoreHandler H) {s s' r : CStore E}
    (h : Prog.Eval (S := Eff E σ) H getStore s r s') : r = s ∧ s' = s := by
  simp only [getStore, perform, Prog.lift] at h
  obtain ⟨g, s₁, hg, h1⟩ := Prog.Eval.op_inv h
  obtain ⟨rfl, rfl⟩ := hH.1 _ _ _ hg
  exact Prog.Eval.pure_inv h1

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- A `checkImport` that returns saw a successful check and left the store unchanged. -/
theorem checkImport_eval {H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop}
    {x : Except String Unit} {s s' : CStore E} {u : Unit}
    (h : Prog.Eval (S := Eff E σ) H (checkImport x) s u s') : x = .ok () ∧ s' = s := by
  cases x with
  | ok v => exact ⟨rfl, (Prog.Eval.pure_inv h).2⟩
  | error e =>
    obtain ⟨e, _, _, _⟩ := Prog.Eval.op_inv h
    exact nomatch e

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- A `trapIf` that returns saw a false condition and left the store unchanged. -/
theorem trapIf_eval {H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop}
    {b : Bool} {r : TrapReason} {s s' : CStore E} {u : Unit}
    (h : Prog.Eval (S := Eff E σ) H (trapIf b r) s u s') : b = false ∧ s' = s := by
  cases b <;> simp only [trapIf, Bool.false_eq_true, ite_true, ite_false] at h
  · exact ⟨rfl, (Prog.Eval.pure_inv h).2⟩
  · obtain ⟨e, _, _, _⟩ := Prog.Eval.op_inv h
    exact nomatch e

/-- The prefix of `instantiateRoot` before the root instance is allocated: a returning run
passed both checks on its initial store `s` and then runs `allocInst` from `s`. -/
theorem instantiateRoot_eval_prefix
    {H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop} (hH : StoreHandler H)
    {recurse : Recurse E σ} {c : Syntax.Component E.Module}
    {args : Exports E} {s s' : CStore E} {r : InstId × Exports E}
    (h : Prog.Eval (S := Eff E σ) H (instantiateRoot recurse c args) s r s') :
    argsComplete c args = true ∧ precheckImports s args Frame.empty c = .ok () ∧
      ∃ s₁, Prog.Eval (S := Eff E σ) H allocInst s r.1 s₁ := by
  obtain ⟨_, s₀, h0, h1⟩ := Prog.Eval.bind_inv h
  obtain ⟨hc, rfl⟩ := trapIf_eval h0
  obtain ⟨g, s₁, hg, h2⟩ := Prog.Eval.bind_inv h1
  obtain ⟨rfl, rfl⟩ := getStore_eval hH hg
  obtain ⟨_, s₂, hk, h3⟩ := Prog.Eval.bind_inv h2
  obtain ⟨hk, rfl⟩ := checkImport_eval hk
  obtain ⟨inst, s₃, h4, h5⟩ := Prog.Eval.bind_inv h3
  obtain ⟨es, s₄, _, h6⟩ := Prog.Eval.bind_inv h5
  obtain ⟨rfl, rfl⟩ := Prog.Eval.pure_inv h6
  exact ⟨by simpa using hc, hk, s₃, h4⟩

/-- The import pre-check precedes every side effect: a root instantiation that returns (under
a store handler) passed `precheckImports` on its initial store. -/
theorem instantiateRoot_prechecked {H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop}
    (hH : StoreHandler H) {recurse : Recurse E σ} {c : Syntax.Component E.Module}
    {args : Exports E} {s s' : CStore E} {r : InstId × Exports E}
    (h : Prog.Eval (S := Eff E σ) H (instantiateRoot recurse c args) s r s') :
    precheckImports s args Frame.empty c = .ok () :=
  (instantiateRoot_eval_prefix hH h).2.1

/-- The root instance is fresh: under a store handler, the instance id returned by
`instantiateRoot` was not allocated in the initial store (that it is allocated right after
`allocInst` is `allocInst_fresh`; later operations are not constrained by `StoreHandler`). -/
theorem instantiateRoot_inst_fresh {H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop}
    (hH : StoreHandler H) {recurse : Recurse E σ} {c : Syntax.Component E.Module}
    {args : Exports E} {s s' : CStore E} {r : InstId × Exports E}
    (h : Prog.Eval (S := Eff E σ) H (instantiateRoot recurse c args) s r s') :
    s.inst? r.1 = none := by
  obtain ⟨_, _, s₁, h1⟩ := instantiateRoot_eval_prefix hH h
  exact (allocInst_fresh hH h1).1

/-! ## Tests (Mock engine, store-only interpreter) -/

namespace Tests

open Engine.Mock

theorem twoResources_run :
    summary (runRoot twoResources []) = some (⟨0⟩, ["r"], some ⟨1⟩, 2) := by
  decide +kernel

/-- The second resource type is defined by the root instance with representation `i64`. -/
theorem twoResources_rt :
    ((runRoot twoResources []).map fun p => p.2.resourceTypes) =
      some [{ impl := some ⟨0⟩, rep := .i32 }, { impl := some ⟨0⟩, rep := .i64 }] := by
  decide +kernel

/-- An import re-exported: the argument passes through unchanged. -/
theorem reexport_run :
    summary (runRoot [.import_ { name := "t" } (.type .subResource),
        .export_ { name := "u" } ⟨.type, 0⟩ none] [("t", .type (.resource ⟨7⟩))]) =
      some (⟨0⟩, ["u"], some ⟨7⟩, 0) := by
  decide +kernel

/-- A missing import traps (the store-only interpreter aborts). -/
theorem missing_import_run :
    (runRoot [.import_ { name := "t" } (.type .subResource)] []).isNone = true := by
  decide +kernel

theorem nestedTwice_rt :
    ((runRoot nestedTwice []).map fun p => (p.2.resourceTypes, p.2.insts.length)) =
      some ([{ impl := some ⟨1⟩, rep := .i32 }, { impl := some ⟨2⟩, rep := .i32 }], 3) := by
  decide +kernel

theorem nestedTwice_exports :
    ((runRoot nestedTwice []).map fun p => p.1.2.map fun
        | (n, .type (.resource r)) => (n, some r)
        | (n, _) => (n, none)) =
      some [("a", some ⟨0⟩), ("b", some ⟨1⟩)] := by
  decide +kernel

/-! ### Import type checks with resource binders -/

/-- The binder `t` is inferred from the argument (`7`) and `u = 7` matches it. -/
theorem importCheck_resource_ok :
    checkClass (precheckImports CStore.empty (rtArg 7 7) Frame.empty (rtImporter [])) =
      some true := by decide +kernel

/-- `u = 8` differs from the inferred `t = 7`. -/
theorem importCheck_resource_bad :
    checkClass (precheckImports CStore.empty (rtArg 7 8) Frame.empty (rtImporter [])) =
      some false := by decide +kernel

/-- The same checks through root instantiation: accepted, and rejected before any
allocation. -/
theorem rtImporter_run_ok : (runRoot (rtImporter []) (rtArg 7 7)).isSome = true := by
  decide +kernel

theorem rtImporter_run_bad : (runRoot (rtImporter []) (rtArg 7 8)).isNone = true := by
  decide +kernel

/-- The pre-check walks past a nested instantiation (an empty placeholder instance), so an
import after it is still checked before any side effect. -/
theorem precheck_after_instantiate :
    checkClass (precheckImports CStore.empty (rtArg 7 8) Frame.empty
      (rtImporter [.component [], .instance_ (.instantiate 0 [])])) = some false := by
  decide +kernel

/-- The pre-check stops at a resource type definition (its identity is only known by running
it): an import after it is not pre-checked (`ok`), and is checked in definition order by the
`import` row instead (the run still traps). -/
theorem precheck_stops_at_resource :
    checkClass (precheckImports CStore.empty (rtArg 7 8) Frame.empty
      (rtImporter [.type (.resource .i32 none)] 1)) = some true ∧
    (runRoot (rtImporter [.type (.resource .i32 none)] 1) (rtArg 7 8)).isNone = true ∧
    (runRoot (rtImporter [.type (.resource .i32 none)] 1) (rtArg 7 7)).isSome = true := by
  decide +kernel

/-- A 🪙 value supplied for a function import has no run-time type and is rejected (wasmparser's
sort mismatch). -/
theorem precheck_value_for_func :
    precheckImports CStore.empty [("f", .value (.bool true))] Frame.empty funcImporter =
      .error "type mismatch for import `f`\nexpected func, found value" := by decide +kernel

/-- An unallocated function id supplied for a function import is rejected (the wording of
wasmtime's `TypeChecker::definition`). -/
theorem precheck_unallocated_func :
    precheckImports CStore.empty [("f", .func ⟨5⟩)] Frame.empty funcImporter =
      .error "type mismatch for import `f`\nfunction implementation is missing" := by
  decide +kernel

/-- An unallocated function id supplied for an instance import: wasmparser's sort mismatch. -/
theorem precheck_unallocated_func_for_instance :
    precheckImports (E := mock) CStore.empty [("i", .func ⟨5⟩)] Frame.empty
      [Syntax.instanceT [], Syntax.importInstance "i" 0] =
      .error "type mismatch for import `i`\nexpected instance, found func" := by decide +kernel

/-- Inside a supplied instance an untypable export is dropped (`itemEntities`), so a 🪙 value
exported under the name of an expected function is reported missing. -/
theorem precheck_value_export_for_func :
    precheckImports (E := mock) CStore.empty [("i", .instance [("x", .value (.bool true))])]
      Frame.empty
      [Syntax.instanceT [.type (Syntax.fnTy [] none), .export_ { name := "x" } (.func 0)],
        Syntax.importInstance "i" 0] =
      .error "type mismatch for import `i`\nmissing expected export `x`" := by decide +kernel

/-- The rejection precedes every side effect: the run allocates nothing. -/
theorem precheck_unallocated_func_run :
    (runRoot funcImporter [("f", .func ⟨5⟩)]).isNone = true := by decide +kernel

end Tests

end Silmaril.Wasm.Component.Instantiate
