module

public import Silmaril.Project.WasmComponents.Ref.Defs
public import Silmaril.Project.Shapes.Component.Thms
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# The Wasm components pilot: the reference denotation (theorems)

* `hevW_strip_wevOf`: on the WASI view of a reference event, `hevW` is the provider
  classifier `compProviderEv` (exports named injectively);
* `accepts_provGuar_strip`, `accepts_provGuar_wevOf`: `provGuar` ignores the call arguments of
  answers, and accepts the WASI view of a trace iff `compProviderSpec` accepts the trace;
* `step_provGuar_isO`: an Opponent move (an export call or an import answer) is never rejected;
* **`wasiSat_traceModel`**: if every trace of `T` is accepted by `compProviderSpec new drop`,
  then `traceModel W fnI fnE T` satisfies `provGuar fnE new drop` under **every** WASI theory;
* `onExp_provGuar`, **`wasiEveryHost_traceModel`**: hence over every host of every theory;
* **`wasiSat_refDen`**, **`wasiEveryHost_refDen`**: the same for `refDen` of a binary component
  whose reference reading `toRef? c` is a correct provider (`Models` of `compProviderSpec` over
  `refMultiSem`).
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Ref

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Resource (HEv handleProto handleStep Protocol compProviderEv compProviderSpec
  protoLogic)
open Silmaril.Project.Shapes.Component (WasiSat WasiEveryHost)

variable {X : CIface} {fnI : X.Imp → FnName} {fnE : X.Exp → FnName} {new drop : X.Exp}

/-! ## The classifier on WASI events -/

/-- `hevW` does not read the arguments that answers repeat. -/
theorem hevW_strip (e : WEv) : hevW fnE new drop (strip e) = hevW fnE new drop e := by
  cases e <;> rfl

/-- On one value of a call, `hevW` is the provider classifier. -/
theorem hevW_call (hinj : Function.Injective fnE) (j : X.Exp) (v : RVal) :
    hevW fnE new drop (.call (fnE j) [wval v]) = compProviderEv new drop (.inr (.ask j [v])) := by
  cases v <;> try (rename_i k _; cases k)
  all_goals simp only [hevW, callEv, wval, hval, compProviderEv, hinj.eq_iff]

/-- On one result of a return, `hevW` is the provider classifier. -/
theorem hevW_ret (hinj : Function.Injective fnE) (j : X.Exp) (v : RVal) :
    hevW fnE new drop (.ret (fnE j) [] (some [wval v])) =
      compProviderEv new drop (.inr (.ans j (.returns (some [v])))) := by
  cases v <;> try (rename_i k _; cases k)
  all_goals simp only [hevW, retEv, wval, hval, compProviderEv, hinj.eq_iff]

/-- **On the WASI view of a reference event, `hevW` is `compProviderEv`.** -/
theorem hevW_strip_wevOf (hinj : Function.Injective fnE) (c : CEvent X) :
    hevW fnE new drop (strip (wevOf fnI fnE c)) = compProviderEv new drop c := by
  rcases c with (⟨i, a⟩ | ⟨i, o⟩) | (⟨j, a⟩ | ⟨j, o⟩)
  · rfl
  · rfl
  · rcases a with _ | ⟨v, _ | ⟨w, a⟩⟩
    · rfl
    · exact hevW_call hinj j v
    · cases v <;> rfl
  · rcases o with (_ | _ | ⟨v, _ | ⟨w, vs⟩⟩) | _ | _ | _
    all_goals first | rfl | exact hevW_ret hinj j v | (cases v <;> rfl)

/-- `provGuar` does not read the arguments that answers repeat. -/
theorem accepts_provGuar_strip (l : List WEv) :
    (provGuar fnE new drop).Accepts (l.map strip) ↔ (provGuar fnE new drop).Accepts l := by
  unfold provGuar
  rw [Protocol.accepts_comap, Protocol.accepts_comap, List.map_map]
  have h : hevW fnE new drop ∘ strip = hevW fnE new drop := funext hevW_strip
  rw [h]

/-- **The WASI view of a trace is accepted iff the trace is.** -/
theorem accepts_provGuar_wevOf (hinj : Function.Injective fnE) (t : List (CEvent X)) :
    (provGuar fnE new drop).Accepts (t.map (wevOf fnI fnE)) ↔
      (compProviderSpec new drop).Accepts t := by
  rw [← accepts_provGuar_strip]
  unfold provGuar compProviderSpec
  rw [Protocol.accepts_comap, Protocol.accepts_comap, List.map_map, List.map_map]
  have h : (hevW fnE new drop ∘ strip) ∘ wevOf fnI fnE = compProviderEv new drop :=
    funext (hevW_strip_wevOf hinj)
  rw [h]

/-! ## Opponent moves -/

/-- The provider handle protocol never rejects a use, a free or a skip. -/
theorem handleStep_provider_isSome (q : Option (List ℕ)) (e : HEv ℕ) (he : ∀ r, e ≠ .alloc r) :
    (handleStep .provider q e).isSome := by
  rcases q with _ | L
  · rfl
  · rcases e with r | r | r | _
    · exact absurd rfl (he r)
    · by_cases hr : r ∈ L <;> simp [handleStep, hr, Silmaril.Wasm.Resource.fault]
    · by_cases hr : r ∈ L <;> simp [handleStep, hr, Silmaril.Wasm.Resource.fault]
    · rfl

/-- A call event is never an allocation. -/
theorem hevW_call_ne_alloc (f : FnName) (a : List Silmaril.Wasm.Component.Val) (r : ℕ) :
    hevW fnE new drop (.call f a) ≠ .alloc r := by
  show callEv fnE drop f a ≠ .alloc r
  unfold callEv
  repeat' split
  all_goals nofun

/-- **An Opponent move is never rejected by `provGuar`**: it is an export call or an import
answer. -/
theorem step_provGuar_isO {I E : Set FnName} {o : Move (nsig I) (nsig E)} (ho : Move.IsO o)
    (q : Option (List ℕ)) : ((provGuar fnE new drop).step q (wev o)).isSome := by
  rcases o with (m | ⟨m, n⟩) | (m | ⟨m, n⟩)
  · exact absurd ho id
  · exact handleStep_provider_isSome q _ fun _ => nofun
  · exact handleStep_provider_isSome q _ (hevW_call_ne_alloc _ _)
  · exact absurd ho id

/-- One Opponent move more is accepted. -/
theorem accepts_provGuar_concat {I E : Set FnName} {p : List (Move (nsig I) (nsig E))}
    {o : Move (nsig I) (nsig E)} (ho : Move.IsO o) (hp : (provGuar fnE new drop).Accepts (wtrace p)) :
    (provGuar fnE new drop).Accepts (wtrace (p ++ [o])) := by
  obtain ⟨q, hq⟩ := (Protocol.accepts_iff_exists _ _).1 hp
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 (step_provGuar_isO (fnE := fnE) (new := new)
    (drop := drop) ho q)
  have he : wtrace (p ++ [o]) = wtrace p ++ [wev o] := List.map_append
  rw [he]
  exact (Protocol.accepts_concat_iff _ _ _).2 ⟨q, hq, q', hq'⟩

/-! ## The generated model -/

/-- The generating plays of `traceModel` are accepted. -/
theorem accepts_of_gen (hinj : Function.Injective fnE) {T : Set (List (CEvent X))}
    (hT : ∀ t ∈ T, (compProviderSpec new drop).Accepts t) {I E : Set FnName}
    {u : List (Move (nsig I) (nsig E))}
    (hu : ∃ t ∈ T, (wtrace u).map strip = t.map (wevOf fnI fnE)) :
    (provGuar fnE new drop).Accepts (wtrace u) := by
  obtain ⟨t, ht, he⟩ := hu
  have h₁ : (provGuar fnE new drop).Accepts (t.map (wevOf fnI fnE)) :=
    (accepts_provGuar_wevOf hinj t).2 (hT t ht)
  rw [← he] at h₁
  exact (accepts_provGuar_strip _).1 h₁

/-- **A correct provider's traces give a model of `provGuar` under every WASI theory.** -/
theorem wasiSat_traceModel {W : World} {S : Type} (hinj : Function.Injective fnE)
    {T : Set (List (CEvent X))} (hT : ∀ t ∈ T, (compProviderSpec new drop).Accepts t)
    (Th : Protocol S WEv) :
    WasiSat (traceModel W fnI fnE T) Th (provGuar fnE new drop) := by
  rintro s ⟨-, u, hu, hp⟩ -
  have hU : (provGuar fnE new drop).Accepts (wtrace u) := by
    rcases hu with rfl | ⟨hu, -⟩
    · exact Protocol.accepts_nil _
    · exact accepts_of_gen hinj hT hu
  rcases hp with hp | ⟨p₀, o, rfl, hp₀, ho⟩
  · exact hU.of_prefix (hp.map wev)
  · exact accepts_provGuar_concat ho (hU.of_prefix (hp₀.map wev))

/-- `provGuar` skips the import events anyway. -/
theorem onExp_provGuar : onExp (provGuar fnE new drop) = provGuar fnE new drop := by
  unfold onExp provGuar Protocol.comap
  congr 1
  funext q e
  rcases e with _ | _ | _ | _
  · rcases q <;> rfl
  · rcases q <;> rfl
  · rfl
  · rfl

/-- **Over every host**: linked over any host of any theory, the export events of a correct
provider's model satisfy `provGuar`. -/
theorem wasiEveryHost_traceModel {W : World} {S : Type} (hinj : Function.Injective fnE)
    {T : Set (List (CEvent X))} (hT : ∀ t ∈ T, (compProviderSpec new drop).Accepts t)
    (Th : Protocol S WEv) :
    WasiEveryHost (traceModel W fnI fnE T) Th (provGuar fnE new drop) := by
  apply WasiSat.everyHost
  rw [onExp_provGuar]
  exact wasiSat_traceModel hinj hT Th

/-! ## Binary components -/

variable {σ : Type} {P : Silmaril.Wasm.Numerics.Profile} {prof : Silmaril.Wasm.Component.ProfileKind}
  {h : Silmaril.Wasm.Component.Reference.Host (Silmaril.Wasm.Component.Reference.core3P P) σ} {σ0 : σ}
  {args : Silmaril.Wasm.Component.Instantiate.Exports (Silmaril.Wasm.Component.Reference.core3P P)}
  {names : X.Exp → String} {W : World}

/-- The reference denotation of a component in the fragment. -/
theorem refDen_of_toRef {c : Silmaril.Wasm.Component.Binary.Ast}
    {rc : Silmaril.Wasm.Component.Reference.Core3Component} (hc : toRef? c = some rc) :
    refDen P prof h σ0 X args names W fnI fnE c =
      traceModel W fnI fnE (refMultiTraces prof h σ0
        (⟨rc, args, names⟩ : RefProg (Silmaril.Wasm.Component.Reference.core3P P) X)) := by
  unfold refDen
  rw [hc]

/-- **A binary component whose reference reading is a correct provider satisfies `provGuar`
under every WASI theory.** -/
theorem wasiSat_refDen {S : Type} (hinj : Function.Injective fnE) {c : Silmaril.Wasm.Component.Binary.Ast}
    {rc : Silmaril.Wasm.Component.Reference.Core3Component} (hc : toRef? c = some rc)
    (hm : Models (protoLogic CFn (List RVal) Outcome (Option (List ℕ))) (refMultiSem prof h σ0)
      (⟨rc, args, names⟩ : RefProg (Silmaril.Wasm.Component.Reference.core3P P) X)
      (compProviderSpec new drop))
    (Th : Protocol S WEv) :
    WasiSat (refDen P prof h σ0 X args names W fnI fnE c) Th (provGuar fnE new drop) := by
  rw [refDen_of_toRef hc]
  exact wasiSat_traceModel hinj ((Silmaril.Wasm.Resource.models_protoLogic_iff _ _ _).1 hm) Th

/-- **… and over every host of every theory.** -/
theorem wasiEveryHost_refDen {S : Type} (hinj : Function.Injective fnE)
    {c : Silmaril.Wasm.Component.Binary.Ast} {rc : Silmaril.Wasm.Component.Reference.Core3Component}
    (hc : toRef? c = some rc)
    (hm : Models (protoLogic CFn (List RVal) Outcome (Option (List ℕ))) (refMultiSem prof h σ0)
      (⟨rc, args, names⟩ : RefProg (Silmaril.Wasm.Component.Reference.core3P P) X)
      (compProviderSpec new drop))
    (Th : Protocol S WEv) :
    WasiEveryHost (refDen P prof h σ0 X args names W fnI fnE c) Th (provGuar fnE new drop) := by
  rw [refDen_of_toRef hc]
  exact wasiEveryHost_traceModel hinj ((Silmaril.Wasm.Resource.models_protoLogic_iff _ _ _).1 hm) Th

end Silmaril.Project.WasmComponents.Ref

end
