module

public import Silmaril.Wasm.Component.Reference.Instantiate.Defs

public import Silmaril.Raw.Wasm.Component.Instantiate.Runtime
public import Silmaril.Raw.Wasm.Component.Canon.Effects
public import Silmaril.Raw.Wasm.Component.Syntax.Builder
public import Silmaril.Raw.Wasm.Component.Types.Subtype.Check

/-!
# Instantiation as a specification program

Component instantiation (Explainer.md, "Instance Definitions") as a program of the specification
carrier `Canon.P E σ` (`Canon/Effects.lean`), run by the component machine like every other
REF function. There is no upstream function for the whole: the Python reference
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
only has `Store.lift` (L539-543) and `Store.lower` (L545-548), which are the `canon lift` and
`canon lower` rows below. The per-definition table follows the Explainer's definition forms, and
the order of side effects is definition order, as in wasmtime's inliner
(`crates/environ/src/component/translate/inline.rs` at wasmtime `a7b4f29`, whose
`GlobalInitializer` list, `crates/environ/src/component/info.rs`, keeps instantiations and
resource definitions in definition order).

Per definition (`instantiateDef`):
* `core module m`: push `m`. `core type t`: push the core type slot (static).
* `component c`: push the closure `⟨c, f :: outer⟩`.
* `import n d`: push `args[n]` into `sort(d)`; a missing argument traps
  `hostTrap "missing import"`.
* `core instance (instantiate m args)`: `coreImportsFor?`, `E.prepare?` on the core store
  (failure traps `coreTrap`), then the start function as a synchronous task of `inst`
  (`runStart`), then push the export map.
* `core instance (exports ...)` and `instance (exports ...)`: push the synthetic bag.
* `instance (instantiate c args)`: evaluate the arguments, `recurse` (a fresh instance), push
  the child's exports.
* `alias export` / `alias core export` / `alias outer`: push the aliased entry.
* `type (resource rep dtor)`: allocate a fresh `RtId` with `impl = inst`
  (`allocResourceType`), push it. Other `type`s: resolve (`resolveDefValType?`,
  `resolveFuncType?`) and push (static).
* `canon lift`: `Store.lift`, allocate `CFuncInst.lifted core ft opts inst`, push its `FuncId`.
* `canon lower`: `Store.lower`, `E.allocHost` of `CanonHost.lowered callee ft opts inst`, push
  the address. `canon <builtin>`: `E.allocHost` of `CanonHost.builtin b inst`, push it.
* `export n si`: record `(n, E[si])` and push it again.

**Start functions** (Concurrency.md "Interaction with the start function"): a core start function
returned by `E.prepare?` is registered as a lifted `CFuncInst`
with the implicit type `func()` and empty (default) options in instance `inst`, and called with
`call (.funcInst f caller)` where `caller` is a fresh `Caller.sub .start` record. It therefore
runs as a *synchronous task* of `inst` through `canon_lift`'s synchronous loop (REF L2140-2144,
handled by `canon_lift`, not here): while the task is not resolved, a ready thread of `inst` is
resumed, and the start function traps only if it blocks while *no* thread of `inst` is ready
(`trap_if(not candidates)`; test/async/dont-block-start.wast). It may block while another
thread of `inst` is ready (test/async/during-sync-call-may-block-if-other-ready-threads.wast),
e.g. a thread spawned by the start function of an earlier core instance of `inst`.

**Nested instantiation.** `instance (instantiate c args)` instantiates the closure `c`, which
comes from the frame, not from a syntactic subterm of the current definition list, so the
recursion is not structural. The programs here take the nested instantiation as a parameter
`recurse : Recurse E σ` (instantiate a closure with arguments in a *fresh* component instance
and return its exports). Two ties are provided:
* the specification tie `callRecurse c args := callItems (.instantiate c args)`: a late-bound
  call, which the dispatcher (`Canon.dispatch`) resolves to `instantiateClosure callRecurse c
  args`, so nesting depth is bounded only by the machine's fuel. Core instantiation goes
  through `coreImportsFor?`, so this needs the instance `[∀ a b, Decidable (E.ExternSub a b)]`
  (an instance argument of `Canon.dispatch`; `lime1`, `v1` and `mock` have one, and for a
  `Core3Engine` it is `Core3Engine.decExternSub`, from `externSub_iff` and
  `ExternSub.decideEmpty`);
* `instantiateFuel n`, by recursion on fuel, for store-only tests without a machine
  (exhaustion traps `TrapReason.exhausted`, not a REF trap).

**Import type checking** (Explainer.md, "Instance Definitions" and "Type Checking"): the `import
n d` row checks the supplied value against the descriptor `d` resolved in the current frame
(`importTypeCheck`, wasmparser's `open_instance_type(args, component, Import)` over
`Types.Entity.sub?`), for root and nested instantiation alike; a mismatch traps
`hostTrap "import type mismatch: ..."` (for nested instantiation of a valid component this is
unreachable: validation performs the same check statically; for root instantiation
`instantiateRoot` also runs the check before any side effect as far as it can, see
`Instantiate/Root.lean`). Functions, types and instances of them are checked by type; core
modules and components by sort only (their module and component types are not compared);
🪙 values are not typed at run time (`itemEntity?`, `pruneEntity`), so a 🪙 value or an
unallocated function supplied where a typed entity is expected is rejected
(`untypedImportMsg`). Soundness: `importTypeCheck_sound`, `importTypeCheck_typable`,
`importTypeCheck_sound_typed`. The type check of wasmtime's `Linker` against a validated
component type, including core module types, is `linkCheck` (`Instantiate/Link.lean`).

Design notes:
* `instantiateDef` takes the scope state `Scope E` (the frame *and* the exports recorded so
  far), the enclosing frames `outer` and the argument map `args`, besides `inst`; it returns the
  new `Scope E`. It takes no `Limits` (nothing here depends on them).
* Core type definitions push one slot per member of a recursion group (`coreTypeSlots`), like
  the validation context (`Validation.Ctx.pushCoreRec`), and one per core module type.
* Instance and component *type* definitions are resolved into semantic types over `RtId`
  (`staticType?`, `resolveDefType?` of `Instantiate/Runtime.lean`): binders are reserved
  identities (`binderVar`), instance types in import/export position are freshened and hoisted
  (`freshenInstance`). Declarators outside the supported fragment (`alias export` inside a type,
  🪙 value descriptors) fall back to the empty placeholder types. Core module *type* definitions
  remain the placeholder `.module_ ⟨[], []⟩` (the engine interface has no translation of Core
  3.0 extern types into `E.ExternType`); only the sort of a core module argument is checked
  (`pruneEntity`).
* 🪙 `start` and `value` definitions are NOT modelled: they trap `internal` (no profile enables
  🪙 values, so this is unreachable for components validated under any profile).
* Every resolution failure other than a missing import (unknown index, sort mismatch, a core
  import that does not match, a type index of the wrong kind) is an `internal` trap: validation
  rules it out.

Provided theorems (the generativity requirement):
* `ArenasExtend s₀ s`: every arena of `s₀` is a prefix of the same arena of `s` (hence
  `ArenasExtend.length_le`: arena lengths are monotone); reflexive and transitive.
* `instantiateDef_inv`, `instantiateComponent_inv`, `instantiateClosure_inv`,
  `instantiateFuel_inv`: `P.Inv (ArenasExtend s₀)` for every `s₀`, i.e. every store update the
  instantiation programs issue only appends to arenas (for `recurse`, under the hypothesis that
  it does so too; the `call`-based tie satisfies it trivially since `P.Inv` only constrains
  `modify`).
* `resource_fresh`: under any handler that implements `get`/`modify` as reading/updating the
  store (`StoreHandler`), `allocResourceType` returns an `RtId` that was not allocated before and
  is allocated afterwards with `impl = some inst`; `instantiateDef_resource` shows that the
  `type (resource rep dtor)` row is exactly `allocResourceType` followed by a push.

NOT claimed: instantiation typing, completeness of the import check, agreement with wasmtime's
inliner or with wasmtime's `Linker` (`linkCheck`), termination of
nested instantiation, or anything about the machine's treatment of `call`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Instantiate

open Engine Canon _root_.Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type}

/-! ## Named store updates -/

/-! ## Helpers -/

section Core

variable [∀ a b, Decidable (E.ExternSub a b)]

/-! ### Import type checking -/

theorem xsubCheck_sound {a b : E.ExternType} (h : xsubCheck a b = .ok ()) :
    E.ExternSub a b := by
  unfold xsubCheck at h
  split at h
  · assumption
  · cases h

/-- **Soundness of the import check**: when both sides are typable and the check succeeds,
the supplied item's type is a subtype (`Types.Entity.Sub` over `E.ExternSub`) of the pruned
expected type with its binders `bs` instantiated by some renaming `φ`, which is the identity on
every resource identity outside `bs` (concrete resources of the expected type are kept). -/
theorem importTypeCheck_sound {s : CStore E} {f : Frame E} {n : String}
    {d : Syntax.ExternDesc} {v : ItemVal E} {exp exp' act : EntityT E} {bs : List RtId}
    {k : Nat} (hd : descEntity? f 0 d = some (exp, bs, k)) (hv : itemEntity? s v = some act)
    (hp : pruneEntity exp = some exp') (h : importTypeCheck s f n d v = .ok ()) :
    ∃ φ : RtId → RtId, (∀ r, r ∉ bs → φ r = r) ∧
      Types.Entity.Sub E.ExternSub act (exp'.map φ) := by
  unfold importTypeCheck at h
  rw [hd, hv] at h
  simp only [hp] at h
  split at h
  · rename_i m hm
    have hl := Types.openInstanceType?_sound
      (fun a b hab => Types.Entity.sub?_sound (fun _ _ hx => xsubCheck_sound hx) hab) hm
    obtain ⟨a, ha, hs⟩ := (Types.Entity.ListSub.iff.mp hl) n (exp'.map (m.apply bs))
      (by simp [Types.Entity.mapList])
    simp only [List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at ha
    subst ha
    exact ⟨m.apply bs, fun _ hr => Types.Remapping.apply_of_not_mem m hr, hs⟩
  · cases h

/-- **The import check types the supplied item**: when the descriptor resolves to an entity
that `pruneEntity` keeps and the check succeeds, the supplied item has a run-time type (it is
not a 🪙 value and not an unallocated function). -/
theorem importTypeCheck_typable {s : CStore E} {f : Frame E} {n : String}
    {d : Syntax.ExternDesc} {v : ItemVal E} {exp exp' : EntityT E} {bs : List RtId} {k : Nat}
    (hd : descEntity? f 0 d = some (exp, bs, k)) (hp : pruneEntity exp = some exp')
    (h : importTypeCheck s f n d v = .ok ()) : ∃ act, itemEntity? s v = some act := by
  cases hv : itemEntity? s v with
  | some act => exact ⟨act, rfl⟩
  | none =>
    unfold importTypeCheck at h
    rw [hd, hv] at h
    simp only [hp, reduceCtorEq] at h

/-- `importTypeCheck_sound` without the typability hypothesis (`importTypeCheck_typable`). -/
theorem importTypeCheck_sound_typed {s : CStore E} {f : Frame E} {n : String}
    {d : Syntax.ExternDesc} {v : ItemVal E} {exp exp' : EntityT E} {bs : List RtId} {k : Nat}
    (hd : descEntity? f 0 d = some (exp, bs, k)) (hp : pruneEntity exp = some exp')
    (h : importTypeCheck s f n d v = .ok ()) :
    ∃ act, itemEntity? s v = some act ∧ ∃ φ : RtId → RtId, (∀ r, r ∉ bs → φ r = r) ∧
      Types.Entity.Sub E.ExternSub act (exp'.map φ) := by
  obtain ⟨act, hv⟩ := importTypeCheck_typable hd hp h
  exact ⟨act, hv, importTypeCheck_sound hd hv hp h⟩

end Core

/-! ## Generativity: instantiation only appends to arenas -/

namespace ArenasExtend

theorem refl (s : CStore E) : ArenasExtend s s := by
  simp [ArenasExtend]

theorem trans {s₁ s₂ s₃ : CStore E} (h₁ : ArenasExtend s₁ s₂)
    (h₂ : ArenasExtend s₂ s₃) :
    ArenasExtend s₁ s₃ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := h₂
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8, a9.trans b9, a10.trans b10, a11.trans b11⟩

/-- Arena lengths are monotone. -/
theorem length_le {s₀ s : CStore E} (h : ArenasExtend s₀ s) :
    s₀.insts.length ≤ s.insts.length ∧
    s₀.resourceTypes.length ≤ s.resourceTypes.length ∧
    s₀.funcs.length ≤ s.funcs.length ∧ s₀.tasks.length ≤ s.tasks.length ∧
    s₀.threads.length ≤ s.threads.length ∧ s₀.subtasks.length ≤ s.subtasks.length ∧
    s₀.resHandles.length ≤ s.resHandles.length ∧ s₀.ends.length ≤ s.ends.length ∧
    s₀.wsets.length ≤ s.wsets.length ∧ s₀.errCtxs.length ≤ s.errCtxs.length ∧
    s₀.callers.length ≤ s.callers.length := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  exact ⟨a1.length_le, a2.length_le, a3.length_le, a4.length_le, a5.length_le, a6.length_le,
    a7.length_le, a8.length_le, a9.length_le, a10.length_le, a11.length_le⟩

/-- An object allocated before stays allocated with the same value. -/
theorem resourceType?_eq {s₀ s : CStore E} (h : ArenasExtend s₀ s) {r : RtId}
    {rt : ResourceType E} (hr : s₀.resourceType? r = some rt) : s.resourceType? r = some rt := by
  obtain ⟨_, a2, _⟩ := h
  obtain ⟨l, hl⟩ := a2
  simp only [CStore.resourceType?, ArenaField.get?, ArenaField.resourceTypes,
    Arena.get?_eq_getElem?] at hr ⊢
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 hr
  rw [← hl, List.getElem?_append_left hlt]
  exact hr

variable {s₀ : CStore E}

theorem setCoreSt {s : CStore E} (c : E.Store (CanonHost E)) (h : ArenasExtend s₀ s) :
    ArenasExtend s₀ (Instantiate.setCoreSt c s) := h

theorem allocHostSt {s : CStore E} (ty : V1.FuncType) (hc : CanonHost E)
    (h : ArenasExtend s₀ s) : ArenasExtend s₀ (Instantiate.allocHostSt ty hc s) := h

theorem alloc_insts {s : CStore E} (x : InstState) (h : ArenasExtend s₀ s) :
    ArenasExtend s₀ (ArenaOps.allocSt ArenaField.insts x s) := by
  obtain ⟨a1, rest⟩ := h
  exact ⟨a1.trans (List.prefix_append _ _), rest⟩

theorem alloc_resourceTypes {s : CStore E} (x : ResourceType E) (h : ArenasExtend s₀ s) :
    ArenasExtend s₀ (ArenaOps.allocSt ArenaField.resourceTypes x s) := by
  obtain ⟨a1, a2, rest⟩ := h
  exact ⟨a1, a2.trans (List.prefix_append _ _), rest⟩

theorem alloc_funcs {s : CStore E} (x : CFuncInst E) (h : ArenasExtend s₀ s) :
    ArenasExtend s₀ (ArenaOps.allocSt ArenaField.funcs x s) := by
  obtain ⟨a1, a2, a3, rest⟩ := h
  exact ⟨a1, a2, a3.trans (List.prefix_append _ _), rest⟩

theorem alloc_callers {s : CStore E} (x : Caller E) (h : ArenasExtend s₀ s) :
    ArenasExtend s₀ (ArenaOps.allocSt ArenaField.callers x s) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11.trans (List.prefix_append _ _)⟩

end ArenasExtend

section Inv

variable {s₀ : CStore E}

local notation "I" => ArenasExtend s₀

theorem need_inv {α : Type} (w : String) (o : Option α) : P.Inv I (need w o : P E σ α) :=
  P.Inv.orTrap _ _

theorem pushEntry_inv (f : Frame E) (s : Syntax.Sort_) (e : Entry E) :
    P.Inv I (pushEntry f s e : P E σ (Frame E)) := need_inv _ _

theorem allocInst_inv : P.Inv I (allocInst : P E σ InstId) :=
  P.Inv.allocObj _ _ fun _ => ArenasExtend.alloc_insts _

theorem allocResourceType_inv (inst : InstId) (rep : AddrType) (dtor : Option E.FuncAddr) :
    P.Inv I (allocResourceType inst rep dtor : P E σ RtId) :=
  P.Inv.allocObj _ _ fun _ => ArenasExtend.alloc_resourceTypes _

theorem resolveDtor_inv (f : Frame E) (dtor : Option Nat) :
    P.Inv I (resolveDtor f dtor : P E σ (Option E.FuncAddr)) := by
  cases dtor
  · exact P.Inv.pure _
  · exact P.Inv.map (need_inv _ _)

theorem allocFunc_inv (fi : CFuncInst E) : P.Inv I (allocFunc fi : P E σ FuncId) :=
  P.Inv.allocObj _ _ fun _ => ArenasExtend.alloc_funcs _

theorem allocCoreHost_inv (h : CanonHost E) : P.Inv I (allocCoreHost h : P E σ E.FuncAddr) :=
  P.Inv.bind P.Inv.getStore fun _ =>
    P.Inv.bind (P.Inv.modifyStore fun _ => ArenasExtend.allocHostSt _ _) fun _ => P.Inv.pure _

theorem runStart_inv (inst : InstId) (sf : E.FuncAddr) :
    P.Inv I (runStart inst sf : P E σ Unit) :=
  P.Inv.bind (allocFunc_inv _) fun _ =>
    P.Inv.bind (P.Inv.allocObj _ _ fun _ => ArenasExtend.alloc_callers _) fun _ =>
      P.Inv.bind (P.Inv.callCancel _) fun _ => P.Inv.pure _

theorem callRecurse_inv (c : Closure E) (args : Exports E) :
    P.Inv I (callRecurse c args : P E σ (Exports E)) := P.Inv.callItems _

theorem checkImport_inv (r : Except String Unit) : P.Inv I (checkImport r : P E σ Unit) := by
  cases r with
  | ok u => exact P.Inv.pure _
  | error e => exact P.Inv.trap _

variable [∀ a b, Decidable (E.ExternSub a b)]

theorem instantiateCore_inv (inst : InstId) (f : Frame E) (m : Nat)
    (args : List (String × Nat)) : P.Inv I (instantiateCore inst f m args : P E σ _) := by
  refine P.Inv.bind (need_inv _ _) fun md => P.Inv.bind P.Inv.getStore fun s =>
    P.Inv.bind (need_inv _ _) fun imports => ?_
  rcases E.prepare? s.core md imports with _ | ⟨core', ci, start⟩
  · exact P.Inv.trap _
  · refine P.Inv.bind (P.Inv.modifyStore fun _ => ArenasExtend.setCoreSt _) fun _ => ?_
    rcases start with _ | sf
    · exact P.Inv.bind (P.Inv.pure _) fun _ => P.Inv.pure _
    · exact P.Inv.bind (runStart_inv _ _) fun _ => P.Inv.pure _

/-- Generativity, per definition: every store update of `instantiateDef` only appends to
arenas (given that nested instantiation does). -/
theorem instantiateDef_inv {recurse : Recurse E σ} (hrec : ∀ c a, P.Inv I (recurse c a))
    (inst : InstId) (outer : List (Frame E)) (args : Exports E) (sc : Scope E)
    (d : Syntax.Definition E.Module) :
    P.Inv I (instantiateDef recurse inst outer args sc d) := by
  have hp : ∀ (f : Frame E) (s : Syntax.Sort_) (e : Entry E) (k : Frame E → Scope E),
      P.Inv I (pushEntry f s e >>= fun f' => (pure (k f') : P E σ (Scope E))) :=
    fun _ _ _ _ => P.Inv.bind (pushEntry_inv _ _ _) fun _ => P.Inv.pure _
  cases d with
  | coreModule m => exact hp ..
  | coreType t => exact P.Inv.pure _
  | component defs => exact hp ..
  | import_ n d =>
    exact P.Inv.bind (P.Inv.orTrap _ _) fun _ => P.Inv.bind P.Inv.getStore fun _ =>
      P.Inv.bind (checkImport_inv _) fun _ => hp ..
  | coreInstance e =>
    cases e with
    | instantiate m cargs => exact P.Inv.bind (instantiateCore_inv ..) fun _ => hp ..
    | exports items => exact P.Inv.bind (need_inv _ _) fun _ => hp ..
  | instance_ e =>
    cases e with
    | instantiate c iargs =>
      exact P.Inv.bind (need_inv _ _) fun cl => P.Inv.bind (need_inv _ _) fun vs =>
        P.Inv.bind (hrec cl vs) fun _ => hp ..
    | exports items => exact P.Inv.bind (need_inv _ _) fun _ => hp ..
  | «alias» a =>
    cases a with
    | export_ i name s =>
      exact P.Inv.bind (need_inv _ _) fun _ => P.Inv.bind (need_inv _ _) fun _ => hp ..
    | coreExport i name s =>
      exact P.Inv.bind (need_inv _ _) fun _ => P.Inv.bind (need_inv _ _) fun _ =>
        P.Inv.bind (need_inv _ _) fun _ => hp ..
    | outer ct idx s =>
      exact P.Inv.bind (need_inv _ _) fun _ => P.Inv.bind (need_inv _ _) fun _ => hp ..
  | type t =>
    cases t with
    | resource rep dtor =>
      exact P.Inv.bind (resolveDtor_inv _ _) fun _ =>
        P.Inv.bind (allocResourceType_inv ..) fun _ => hp ..
    | _ => exact P.Inv.bind (need_inv _ _) fun _ => hp ..
  | canon c =>
    cases c with
    | lift cf opts ft =>
      exact P.Inv.bind (need_inv _ _) fun _ => P.Inv.bind (allocFunc_inv _) fun _ => hp ..
    | lower g opts =>
      exact P.Inv.bind (need_inv _ _) fun _ => P.Inv.bind (P.Inv.getObj _ _) fun _ =>
        P.Inv.bind (allocCoreHost_inv _) fun _ => hp ..
    | builtin b =>
      exact P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind (need_inv _ _) fun _ =>
        P.Inv.bind (allocCoreHost_inv _) fun _ => hp ..
  | start _ _ _ => exact P.Inv.internal _
  | value _ _ => exact P.Inv.internal _
  | export_ n si _ =>
    exact P.Inv.bind (need_inv _ _) fun _ => P.Inv.bind (need_inv _ _) fun _ => hp ..

theorem instantiateComponent_inv {recurse : Recurse E σ} (hrec : ∀ c a, P.Inv I (recurse c a))
    (c : Closure E) (args : Exports E) (inst : InstId) :
    P.Inv I (instantiateComponent recurse c args inst) :=
  P.Inv.bind (P.Inv.listFoldlM fun sc d _ => instantiateDef_inv hrec inst c.outer args sc d)
    fun _ => P.Inv.pure _

theorem instantiateClosure_inv {recurse : Recurse E σ} (hrec : ∀ c a, P.Inv I (recurse c a))
    (c : Closure E) (args : Exports E) : P.Inv I (instantiateClosure recurse c args) :=
  P.Inv.bind allocInst_inv fun inst => instantiateComponent_inv hrec c args inst

theorem instantiateFuel_inv (n : Nat) (c : Closure E) (args : Exports E) :
    P.Inv I (instantiateFuel n c args : P E σ (Exports E)) := by
  induction n generalizing c args with
  | zero => exact P.Inv.trap _
  | succ n ih => exact instantiateClosure_inv (fun c a => ih c a) c args

end Inv

/-! ## Freshness of resource types -/

/-- Generativity of resource types: `allocResourceType` returns an `RtId` that was not
allocated before and is allocated afterwards, with the defining instance `inst`. -/
theorem resource_fresh {H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop}
    (hH : StoreHandler H) {inst : InstId} {rep : AddrType} {dtor : Option E.FuncAddr}
    {s s' : CStore E} {r : RtId}
    (h : Prog.Eval (S := Eff E σ) H (allocResourceType inst rep dtor) s r s') :
    s.resourceType? r = none ∧ s'.resourceType? r = some { impl := some inst, rep, dtor } := by
  simp only [allocResourceType, allocObj, getStore, modifyStore, perform, Prog.lift,
    bind, Prog.bind, pure] at h
  obtain ⟨g, s₁, hg, h1⟩ := Prog.Eval.op_inv h
  obtain ⟨rfl, rfl⟩ := hH.1 _ _ _ hg
  obtain ⟨u, s₂, hm, h2⟩ := Prog.Eval.op_inv h1
  have hs₂ := hH.2 _ _ _ _ hm
  obtain ⟨rfl, rfl⟩ := Prog.Eval.pure_inv h2
  subst hs₂
  exact ⟨ArenaField.get?_fresh _ _, ArenaField.get?_alloc_self _ _ _⟩

/-- The `type (resource rep dtor)` row is `allocResourceType` followed by a push. -/
theorem instantiateDef_resource [∀ a b, Decidable (E.ExternSub a b)] (recurse : Recurse E σ)
    (inst : InstId) (outer : List (Frame E)) (args : Exports E) (sc : Scope E)
    (rep : AddrType) (dtor : Option Nat) :
    instantiateDef recurse inst outer args sc (.type (.resource rep dtor)) = (do
      let d ← resolveDtor sc.frame dtor
      let r ← allocResourceType inst rep d
      let f ← pushEntry sc.frame .type (.item (.type (.resource r)))
      pure { sc with frame := f }) := rfl

end Silmaril.Wasm.Component.Instantiate
