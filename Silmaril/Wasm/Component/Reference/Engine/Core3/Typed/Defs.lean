module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Extends.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Status.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
import Silmaril.Wasm.Component.Reference.Engine.Core3.Agreement.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Prepare.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Store.Defs

/-!
# The typed laws of the concrete Core 3.0 engine

`core3Typed o : Core3Engine.TypedLaws (core3 o)` instantiates the abstract typing predicates of
`Core3Engine.TypedLaws` (Engine/Core3.lean) with Core 3.0 typing (`Execution/Core/Typing/*`):

* `StoreOkE s`: the store is well typed (`StoreOk`, the spec's `Store_ok`) and every host
  function of `s` has a flat type (`HostFlat`; canon host functions are allocated by
  `allocHost` at `ofFlatType ft`);
* `Ext s s'`: typed store extension `Extend s s'` (the spec's `Extend_store`);
* `ThreadOkE s t rs`: the thread's configuration is typed with the numeric result types `rs`
  (`SingleThreaded.ThreadOk s t (rs.map Silmaril.Wasm.Validation.Ty.num)`, i.e. `Config_ok`);
* `HostTypedE s h ft`: every host function of `s` with code `h` has type `ofFlatType ft` (vacuous
  while there is none).

Each law is a separate theorem in the namespace `Core3.Typed`, named after the field it
discharges. The laws about internal steps, status and resumption go through the agreement with
the single-threaded machine (Engine/Core3/Agreement.lean: `core3_internal_sound`, `statusE_eq`)
and its soundness theorems (`SingleThreaded.status_ne_stuck`, `SingleThreaded.Internal.preserves`,
`SingleThreaded.resume_typed`); internal steps never change the function instances
(`SingleThreaded.Internal.funcs_prefix`), so host typing persists. Flat results and callout
arguments, trap resumption (Engine/Core3/Typed/Status.lean), host allocation, memory writes,
threads in extended stores (Engine/Core3/Typed/Store.lean) and instantiation
(Engine/Core3/Typed/Prepare.lean) are proved from Core 3.0 progress and preservation
(`Config.progress`, `Step.preservation`, `Instantiate.ok`, `invoke_ok`). `running_progress` holds
without typing (`statusE_running_step`). `prepare_ok` does not use its validity and
import-matching hypotheses: `prepareE?` checks both itself (`validate?`, `externAddrsOk?`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-! ## The typing predicates -/

/-- Every host function of the store has a flat type. -/
def HostFlat (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ h : H, fi.code = .host h → ∃ ft, fi.type = SingleThreaded.ofFlatType ft

/-- Well-typed stores of the concrete engine: `Store_ok`, and every host function is flat. -/
def StoreOkE (s : Store H) : Prop := StoreOk s ∧ HostFlat s

/-- Every host function of `s` with code `h` has type `ofFlatType ft`. -/
def HostTypedE (s : Store H) (h : H) (ft : V1.FuncType) : Prop :=
  ∀ fi ∈ s.funcs, fi.code = .host h → fi.type = SingleThreaded.ofFlatType ft

/-- A typed thread with numeric result types `rs`. -/
def ThreadOkE (s : Store H) (t : SingleThreaded.Thread) (rs : List NumType) : Prop :=
  SingleThreaded.ThreadOk s t (rs.map Silmaril.Wasm.Validation.Ty.num)

/-! ## Progress of running threads (no typing needed) -/

theorem statusC_running_isSome {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread}
    (h : SingleThreaded.statusC (SingleThreaded.Exec.stepI o) s t = .running) :
    (SingleThreaded.Exec.stepI o (t.config s)).isSome = true := by
  have h1 : ¬ (SingleThreaded.splitVals (t.config s).code).2.isEmpty = true := fun e => by
    simp [SingleThreaded.statusC, e] at h
  have h2 : ¬ SingleThreaded.isTrap? (t.config s).code = true := fun e => by
    simp [SingleThreaded.statusC, h1, e] at h
  have h3 : ¬ SingleThreaded.isThrowing? (t.config s).code = true := fun e => by
    simp [SingleThreaded.statusC, h1, h2, e] at h
  rw [statusC_of_live h1 h2 h3] at h
  split at h
  · cases h
  · by_contra hs
    simp [hs] at h

/-- A `running` thread of the concrete engine has an internal step. -/
theorem statusE_running_step {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} (h : statusE o s t = .running) :
    ∃ c', SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some c' := by
  rw [statusE_eq_flatStatus, flatStatus_running_iff] at h
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (statusC_running_isSome h)
  refine ⟨(c'.store, .active c'.frame c'.code), ?_⟩
  show Option.map _ (SingleThreaded.Exec.stepI o (t.config s)) = _
  rw [hc]
  rfl

/-! ## Host typing and the store's functions -/

theorem HostFlat.of_funcs_eq {s s' : Store H} (he : s'.funcs = s.funcs) (h : HostFlat s) :
    HostFlat s' := by
  intro fi hfi
  rw [he] at hfi
  exact h fi hfi

theorem HostTypedE.of_funcs_eq {s s' : Store H} {hc : H} {ft : V1.FuncType}
    (he : s'.funcs = s.funcs) (h : HostTypedE s hc ft) : HostTypedE s' hc ft := by
  intro fi hfi
  rw [he] at hfi
  exact h fi hfi

/-- Appending Wasm functions keeps every host function flat. -/
theorem HostFlat.of_append_wasm {s s' : Store H} {new : List (FuncInst H)}
    (he : s'.funcs = s.funcs ++ new) (hw : ∀ fi ∈ new, ∃ code, fi.code = .wasm code)
    (h : HostFlat s) : HostFlat s' := by
  intro fi hfi hc hcode
  rw [he] at hfi
  rcases List.mem_append.mp hfi with hfi | hfi
  · exact h fi hfi hc hcode
  · obtain ⟨code, hcode'⟩ := hw fi hfi
    rw [hcode] at hcode'
    cases hcode'

/-- Appending Wasm functions keeps every host typing. -/
theorem HostTypedE.of_append_wasm {s s' : Store H} {new : List (FuncInst H)} {hc : H}
    {ft : V1.FuncType} (he : s'.funcs = s.funcs ++ new)
    (hw : ∀ fi ∈ new, ∃ code, fi.code = .wasm code) (h : HostTypedE s hc ft) :
    HostTypedE s' hc ft := by
  intro fi hfi hcode
  rw [he] at hfi
  rcases List.mem_append.mp hfi with hfi | hfi
  · exact h fi hfi hcode
  · obtain ⟨code, hcode'⟩ := hw fi hfi
    rw [hcode] at hcode'
    cases hcode'

/-! ## The laws, one per field of `Core3Engine.TypedLaws` -/

namespace Typed

theorem ext_refl {s : Store H} (hs : StoreOkE s) : Extend s s := Extend.refl hs.1

theorem empty_ok (H : Type) : StoreOkE ({} : Store H) := by
  refine ⟨?_, fun _ h => by cases h⟩
  constructor <;> intro x hx <;> cases hx

theorem empty_hostTyped (h : H) (ft : V1.FuncType) : HostTypedE ({} : Store H) h ft := by
  intro fi hfi
  cases hfi

theorem allocHost_ok {s s' : Store H} {ft : V1.FuncType} {h : H} {a : Nat} (hs : StoreOkE s)
    (e : SingleThreaded.allocHost s ft h = (s', a)) : StoreOkE s' ∧ Extend s s' := by
  obtain ⟨h₁, h₂, h₃⟩ := allocHost_storeOk hs.1 e
  refine ⟨⟨h₁, fun fi hfi hc hcode => ?_⟩, h₂⟩
  rw [h₃] at hfi
  rcases List.mem_append.mp hfi with hfi | hfi
  · exact hs.2 fi hfi hc hcode
  · rw [List.mem_singleton] at hfi
    subst hfi
    exact ⟨ft, rfl⟩

theorem allocHost_hostTyped {s s' : Store H} {ft : V1.FuncType} {h : H} {a : Nat} {h' : H}
    {ft' : V1.FuncType} (e : SingleThreaded.allocHost s ft h = (s', a))
    (hh : HostTypedE s h' ft') (heq : h' = h → ft' = ft) : HostTypedE s' h' ft' := by
  intro fi hfi hcode
  rw [allocHost_funcs e] at hfi
  rcases List.mem_append.mp hfi with hfi | hfi
  · exact hh fi hfi hcode
  · rw [List.mem_singleton] at hfi
    subst hfi
    have e' : h = h' := FuncCode.host.inj hcode
    subst e'
    rw [heq rfl]

theorem memWrite_ok {s s' : Store H} {m st : Nat} {bs : ByteArray} (hs : StoreOkE s)
    (h : SingleThreaded.memWrite? s m st bs = some s') :
    StoreOkE s' ∧ Extend s s' ∧ ∀ hc ft, HostTypedE s hc ft → HostTypedE s' hc ft := by
  obtain ⟨h₁, h₂, h₃⟩ := memWrite?_storeOk hs.1 h
  exact ⟨⟨h₁, HostFlat.of_funcs_eq h₃ hs.2⟩, h₂, fun _ _ hh => HostTypedE.of_funcs_eq h₃ hh⟩

/-- Instantiation of a valid module with matching imports preserves typing, and the start
function (of type `[] -> []`) gives a typed activation. -/
theorem prepare_ok {o : SingleThreaded.GrowOracle} {s s' : Store H} {m : Module}
    {imps : List ExternAddr} {i : ModuleInst} {st : Option Nat} (hs : StoreOkE s)
    (hv : ModuleValid m) (hm : ImportsMatch (core3 o) (H := H) s imps m)
    (h : prepareE? s m imps = some (s', i, st)) :
    StoreOkE s' ∧ Extend s s' ∧ (∀ hc ft, HostTypedE s hc ft → HostTypedE s' hc ft) ∧
      ∀ a, st = some a → ThreadOkE s' (SingleThreaded.Thread.invokeFlat a []) [] := by
  -- `prepareE?` itself checks validity (`validate?`) and the import types (`externAddrsOk?`), so
  -- `hv` and `hm` are implied by `h`.
  have _ := hv
  have _ := hm
  obtain ⟨h₁, h₂, ⟨new, hnew, hw⟩, h₄⟩ := prepareE?_typed hs.1 h
  exact ⟨⟨h₁, HostFlat.of_append_wasm hnew hw hs.2⟩, h₂,
    fun _ _ hh => HostTypedE.of_append_wasm hnew hw hh, h₄⟩

theorem invoke_ok {s : Store H} {a : Nat} {ft : V1.FuncType} {args : List FlatValue}
    (hs : StoreOkE s) (hft : (funcTypeE? s a).bind SingleThreaded.flatType? = some ft)
    (hargs : args.map (·.type) = ft.params) :
    ThreadOkE s (SingleThreaded.Thread.invokeFlat a args) ft.results := by
  unfold funcTypeE? at hft
  cases hfi : s.funcs[a]? with
  | none => simp [hfi] at hft
  | some fi =>
    show ThreadOkE s (SingleThreaded.Thread.invokeFlat a args) ft.results
    simp only [hfi, Option.map_some, Option.bind_some] at hft
    have hty : fi.type = SingleThreaded.ofFlatType ft := (SingleThreaded.flatType?_sound hft).symm
    have hexp : Expand fi.type
        (.func (Silmaril.Wasm.Validation.Ty.ofList (ft.params.map Silmaril.Wasm.Validation.Ty.num)) (Silmaril.Wasm.Validation.Ty.ofList (ft.results.map Silmaril.Wasm.Validation.Ty.num))) := by
      rw [hty]
      exact expand_ofFlatType ft
    have hargsOk : List.Forall₂ (ValOk s) (args.map SingleThreaded.ofFlat)
        (Silmaril.Wasm.Validation.Ty.ofList (ft.params.map Silmaril.Wasm.Validation.Ty.num)).toList := by
      rw [Silmaril.Wasm.Validation.Ty.toList_ofList, ← hargs]
      exact SingleThreaded.forall₂_ofFlat args
    obtain ⟨fi', ps', rs', hf', hexp', hok⟩ :=
      Silmaril.Wasm.Execution.Core.invoke_ok hs.1 ⟨fi, _, _, hfi, hexp, hargsOk⟩
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hf')
    obtain ⟨-, hrs⟩ : _ ∧ Silmaril.Wasm.Validation.Ty.ofList (ft.results.map Silmaril.Wasm.Validation.Ty.num) = rs' :=
      Silmaril.Wasm.Validation.Ty.func.inj (Expand.func_eq hexp hexp')
    have hok' : ConfigOk (invoke s a (args.map SingleThreaded.ofFlat)) (ft.results.map Silmaril.Wasm.Validation.Ty.num) := by
      simpa only [← hrs, Silmaril.Wasm.Validation.Ty.toList_ofList] using hok
    exact hok'

theorem threadOk_ext {s s' : Store H} {t : SingleThreaded.Thread} {rs : List NumType}
    (hs : StoreOkE s) (ht : ThreadOkE s t rs) (he : Extend s s') (hs' : StoreOkE s') :
    ThreadOkE s' t rs :=
  threadOk_extend hs.1 he hs'.1 ht

theorem internal_ok {o : SingleThreaded.GrowOracle} {s s' : Store H}
    {t t' : SingleThreaded.Thread} {rs : List NumType} (hs : StoreOkE s) (ht : ThreadOkE s t rs)
    (h : SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some (s', t')) :
    StoreOkE s' ∧ ThreadOkE s' t' rs ∧ Extend s s' ∧
      ∀ hc ft, HostTypedE s hc ft → HostTypedE s' hc ft := by
  have hi := core3_internal_sound ht h
  obtain ⟨h₁, h₂, h₃⟩ := SingleThreaded.Internal.preserves hs.1 ht hi
  have hf := SingleThreaded.Internal.funcs_prefix hi
  exact ⟨⟨h₁, HostFlat.of_funcs_eq hf hs.2⟩, h₂, h₃, fun _ _ hh => HostTypedE.of_funcs_eq hf hh⟩

theorem running_progress {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {rs : List NumType} (_hs : StoreOkE s) (_ht : ThreadOkE s t rs)
    (h : statusE o s t = .running) :
    ∃ c', SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some c' :=
  statusE_running_step h

/-- The callout of a typed thread has flat arguments, so its flat status is not `stuck`. -/
theorem callout_flat_ne_stuck {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {rs : List NumType} {hc : H} {args : List Val}
    (hs : StoreOkE s) (ht : ThreadOkE s t rs) (hst : SingleThreaded.status o s t = .callout hc args) :
    flatStatus (.callout hc args) ≠ .stuck := by
  obtain ⟨fi, hfi, hcode, ps, rs', hexp, hargs⟩ := callout_args_typed hs.1 ht hst
  obtain ⟨ft, hty⟩ := hs.2 fi hfi hc hcode
  have hexpF : Expand (SingleThreaded.ofFlatType ft) (.func ps rs') := hty ▸ hexp
  obtain ⟨hps, -⟩ : Silmaril.Wasm.Validation.Ty.ofList (ft.params.map Silmaril.Wasm.Validation.Ty.num) = ps ∧ _ :=
    Silmaril.Wasm.Validation.Ty.func.inj (Expand.func_eq (expand_ofFlatType ft) hexpF)
  have hargsF : List.Forall₂ (ValOk s) args (ft.params.map Silmaril.Wasm.Validation.Ty.num) := by
    simpa only [← hps, Silmaril.Wasm.Validation.Ty.toList_ofList] using hargs
  obtain ⟨fargs, hm, -⟩ := mapM_toFlat?_of_forall₂ hargsF
  simp only [flatStatus, hm]
  intro e
  cases e

/-- Typed threads are never `stuck`; in particular an exception escaping the thread is
`returned .trap`, and results and callout arguments are flat. -/
theorem not_stuck {o : SingleThreaded.GrowOracle} {s : Store H} {t : SingleThreaded.Thread}
    {rs : List NumType} (hs : StoreOkE s) (ht : ThreadOkE s t rs) : statusE o s t ≠ .stuck := by
  rw [statusE_eq ht]
  have hne := SingleThreaded.status_ne_stuck (o := o) hs.1 ht
  cases hst : SingleThreaded.status o s t with
  | running => intro e; cases e
  | returned r =>
    cases r with
    | values vs =>
      obtain ⟨fvs, hm, -⟩ := returned_values_flat hs.1 ht hst
      simp only [flatStatus, hm]
      intro e
      cases e
    | trap => intro e; cases e
  | callout hc args => exact callout_flat_ne_stuck hs ht hst
  | stuck => exact absurd hst hne

theorem returned_typed {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {rs : List NumType} {vs : List FlatValue} (hs : StoreOkE s)
    (ht : ThreadOkE s t rs) (h : statusE o s t = .returned (.values vs)) :
    vs.map (·.type) = rs := by
  rw [statusE_eq ht] at h
  obtain ⟨vs', hst, hm⟩ := flatStatus_eq_returned_values h
  obtain ⟨fvs, hm', hty⟩ := returned_values_flat hs.1 ht hst
  rw [hm] at hm'
  cases hm'
  exact hty

theorem callout_typed {o : SingleThreaded.GrowOracle} {s : Store H} {t : SingleThreaded.Thread}
    {rs : List NumType} {hc : H} {ft : V1.FuncType} {args : List FlatValue} (hs : StoreOkE s)
    (ht : ThreadOkE s t rs) (hh : HostTypedE s hc ft) (h : statusE o s t = .callout hc args) :
    args.map (·.type) = ft.params := by
  rw [statusE_eq ht] at h
  obtain ⟨args', hst, hm⟩ := flatStatus_eq_callout' h
  obtain ⟨fi, hfi, hcode, ps, rs', hexp, hargs⟩ := callout_args_typed hs.1 ht hst
  rw [hh fi hfi hcode] at hexp
  have e := Expand.func_eq hexp (expand_ofFlatType ft)
  simp only [Silmaril.Wasm.Validation.Ty.func.injEq] at e
  obtain ⟨rfl, -⟩ := e
  rw [Silmaril.Wasm.Validation.Ty.toList_ofList] at hargs
  obtain ⟨fargs, hm', hty⟩ := mapM_toFlat?_of_forall₂ hargs
  rw [hm] at hm'
  cases hm'
  exact hty

/-- Resuming a callout at an extended well-typed store, with a trap or with values of the result
types of a flat type of the host code, gives a typed thread. -/
theorem resume_ok {o : SingleThreaded.GrowOracle} {s s' : Store H} {t : SingleThreaded.Thread}
    {rs : List NumType} {hc : H} {args : List FlatValue} {r : CallResult} (hs : StoreOkE s)
    (ht : ThreadOkE s t rs) (h : statusE o s t = .callout hc args) (he : Extend s s')
    (hs' : StoreOkE s')
    (hr : r = .trap ∨ ∃ (ft : V1.FuncType) (vs : List FlatValue), HostTypedE s hc ft ∧
      r = .values vs ∧ vs.map (·.type) = ft.results) :
    ThreadOkE s' (SingleThreaded.resume s' t (toCR r)) rs := by
  rw [statusE_eq ht] at h
  obtain ⟨args', hst, -⟩ := flatStatus_eq_callout' h
  rcases hr with rfl | ⟨ft, vs, hh, rfl, hvs⟩
  · exact resume_trap_extend hs.1 ht hst he hs'.1
  · refine SingleThreaded.resume_typed hs.1 ht hst hs'.1 he fun E a args'' hd => ?_
    obtain ⟨fi, -, -, -, hf, hcode, -, -, -, -⟩ := SingleThreaded.decompose?_sound hd
    refine ⟨fi, Silmaril.Wasm.Validation.Ty.ofList (ft.params.map Silmaril.Wasm.Validation.Ty.num), Silmaril.Wasm.Validation.Ty.ofList (ft.results.map Silmaril.Wasm.Validation.Ty.num), hf, ?_, ?_⟩
    · rw [hh fi (List.mem_of_getElem? hf) hcode]
      exact expand_ofFlatType ft
    · rw [Silmaril.Wasm.Validation.Ty.toList_ofList, ← hvs]
      exact SingleThreaded.forall₂_ofFlat vs

end Typed

end Silmaril.Wasm.Component.Engine.Core3

namespace Silmaril.Wasm.Component.Engine

open Silmaril.Wasm.Execution.Core Core3

/-- The typed laws of the concrete Core 3.0 engine. -/
def core3Typed (o : SingleThreaded.GrowOracle) : Core3Engine.TypedLaws (core3 o) where
  StoreOk := StoreOkE
  Ext := Extend
  ThreadOk := ThreadOkE
  HostTyped := HostTypedE
  ext_refl := Typed.ext_refl
  ext_trans := Extend.trans
  empty_ok := Typed.empty_ok
  empty_hostTyped := Typed.empty_hostTyped
  allocHost_ok := Typed.allocHost_ok
  allocHost_hostTyped := Typed.allocHost_hostTyped
  memWrite_ok := Typed.memWrite_ok
  prepare_ok := Typed.prepare_ok
  invoke_ok := Typed.invoke_ok
  threadOk_ext := Typed.threadOk_ext
  internal_ok := Typed.internal_ok
  running_progress := Typed.running_progress
  not_stuck := Typed.not_stuck
  returned_typed := Typed.returned_typed
  callout_typed := Typed.callout_typed
  resume_ok := Typed.resume_ok

end Silmaril.Wasm.Component.Engine
