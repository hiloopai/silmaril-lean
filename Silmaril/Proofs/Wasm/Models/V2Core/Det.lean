module

public import Silmaril.Proofs.Wasm.Models.V2Core.Behaviours
public import Silmaril.Proofs.Wasm.Models.V2Core.CallInv
public import Silmaril.Wasm.Binaryen.DetLift
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitLoops

/-!
# Equality of 2.0 and Core 3.0 behaviours at the deterministic profile

* `core_not_step_unalloc`, `core_behaviours_unalloc`: Core's entry configuration at an
  unallocated address does not step, so its behaviours are empty (`call_ref` reads the
  function instance; the host case needs `hostArity?`, which is also `none` there);
* `liftHost_closed`: the Core host induced by the closed 2.0 host is the closed Core host;
* `core_behaviours_sub_singleton`: at `Profile.deterministic g`, if the closed-host Core run
  of a configuration has a behaviour `b`, then `b` is its only behaviour under **every** host.
  This is `Silmaril.Wasm.Binaryen.DetLift` (unique normal forms of the host-free diamond, and a
  host call never reached);
* **`behaviours_det_eq`**: at `Profile.deterministic g`, when the closed-host 2.0 run of the
  call has a behaviour, the 2.0 behaviours read in Core values are exactly the Core
  behaviours of the image, under any host that preserves well-formedness and keeps functions.

The hypothesis is needed. `DetFalse` refutes the statement without it: a host call can tell
apart 2.0 arguments that have the same Core image.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Step Steps Diverges behavioursOf)
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ## Core at an unallocated address -/

theorem core_head_callRefType_unalloc {P : Profile} {X : CStore H}
    {f : Silmaril.Wasm.Execution.Core.Frame} {ws pre args : List CVal} {a : Nat}
    {t : Silmaril.Wasm.Validation.DefType} {c₀ : Silmaril.Wasm.Execution.Core.Config H}
    (ha : X.funcs.length ≤ a) (hws : ws ++ [.ref (.func a)] = pre ++ args)
    (hh : Head P X f args (.callRefType t) c₀) : False := by
  have hlast : (pre ++ args).getLast? = some (.ref (.func a)) := by rw [← hws]; simp
  cases hh with
  | parametric h => exact absurd (famOf_of_shape (ParametricStep.shape h)).2 (by simp [famOf])
  | numeric h => exact absurd (famOf_of_shape (NumericStep.shape h)).2 (by simp [famOf])
  | vector h => exact absurd (famOf_of_shape (VectorStep.shape h)).2 (by simp [famOf])
  | «variable» h => exact absurd (famOf_of_shape (VariableStep.shape h)).2 (by simp [famOf])
  | table h => exact absurd (famOf_of_shape (TableStep.shape h)).2 (by simp [famOf])
  | memory h => exact absurd (famOf_of_shape (MemoryStep.shape h)).2 (by simp [famOf])
  | reference h => exact absurd (famOf_of_shape (RefStep.shape h)).2 (by simp [famOf])
  | aggregate h => exact absurd (famOf_of_shape (AggregateStep.shape h)).2 (by simp [famOf])
  | callRefNull _ => simp at hlast
  | callRefFunc hargs _ hf =>
    subst hargs
    simp only [← List.append_assoc, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_singleton, Option.some.injEq,
      Silmaril.Wasm.Execution.Core.Val.ref.injEq,
      Silmaril.Wasm.Execution.Core.Ref.func.injEq] at hlast
    subst hlast
    simp [List.getElem?_eq_none ha] at hf

/-- **Core's entry code at an unallocated address does not step.** -/
theorem core_not_step_unalloc {P : Profile} {host : CHost H} {X : CStore H}
    {f : Silmaril.Wasm.Execution.Core.Frame} {vs : List CVal} {a : Nat}
    {t : Silmaril.Wasm.Validation.DefType} {c' : Silmaril.Wasm.Execution.Core.Config H}
    (ha : X.funcs.length ≤ a) :
    ¬ Step P host ⟨X, f, Silmaril.Wasm.Execution.Core.vals vs ++
      [.ref (.func a), .callRefType t]⟩ c' := by
  intro h
  have hcode : Silmaril.Wasm.Execution.Core.vals vs ++ [.ref (.func a), .callRefType t] =
      Silmaril.Wasm.Execution.Core.vals (vs ++ [.ref (.func a)]) ++ .callRefType t :: [] := by
    simp [Silmaril.Wasm.Execution.Core.vals, Silmaril.Wasm.Execution.Core.Val.toAdmin]
  rcases Step.split_host h with h | ⟨E, a', hh, args, hd, -⟩
  · rw [hcode] at h
    obtain ⟨pre, args, c₀, hws, hhead, -⟩ :=
      Silmaril.Wasm.Execution.Core.Step.head_inv (rest := []) h rfl (by simp) (by simp)
    exact core_head_callRefType_unalloc ha hws hhead
  · simp only at hd
    rw [hcode, decompose?_of_split (splitVals_vals_cons (d := .callRefType t) rfl [])] at hd
    simp [decompHead, topRedex, hostArity?, List.getElem?_eq_none ha,
      Silmaril.Wasm.Execution.Core.Admin.isCallRef] at hd

theorem core_steps_of_stuck {P : Profile} {host : CHost H}
    {c c' : Silmaril.Wasm.Execution.Core.Config H}
    (hn : ∀ c'', ¬ Step P host c c'') (h : Steps P host c c') : c' = c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hs _ _ => exact absurd hs (hn _)

theorem core_invoke_not_result {X : CStore H} {a : Nat} {vs : List CVal}
    (r : Silmaril.Wasm.Execution.Core.Result) :
    (Silmaril.Wasm.Execution.Core.invoke X a vs).code ≠ r.toAdmin := by
  intro h
  have hl := congrArg List.getLast? h
  cases r with
  | values ws =>
    rcases List.eq_nil_or_concat ws with rfl | ⟨ws', w, rfl⟩
    · simp [Silmaril.Wasm.Execution.Core.invoke, Silmaril.Wasm.Execution.Core.Result.toAdmin,
        Silmaril.Wasm.Execution.Core.vals] at h
    · rcases w with ⟨⟨_ | _⟩, _⟩ | _ | _ <;>
        simp [Silmaril.Wasm.Execution.Core.invoke, Silmaril.Wasm.Execution.Core.Result.toAdmin,
          Silmaril.Wasm.Execution.Core.vals, Silmaril.Wasm.Execution.Core.Val.toAdmin] at hl
  | throw _ =>
    simp [Silmaril.Wasm.Execution.Core.invoke, Silmaril.Wasm.Execution.Core.Result.toAdmin] at hl
  | trap =>
    simp [Silmaril.Wasm.Execution.Core.invoke, Silmaril.Wasm.Execution.Core.Result.toAdmin] at hl

/-- **Core behaviours of invoking an unallocated address are empty**, at every profile and
host. -/
theorem core_behaviours_unalloc (P : Profile) (host : CHost H) (X : CStore H) {a : Nat}
    (ha : X.funcs.length ≤ a) (vs : List CVal) :
    Silmaril.Wasm.Execution.Core.behaviours P host X a vs = ∅ := by
  have hn : ∀ c'', ¬ Step P host (Silmaril.Wasm.Execution.Core.invoke X a vs) c'' :=
    fun _ => core_not_step_unalloc ha
  ext b
  simp only [Silmaril.Wasm.Execution.Core.behaviours_eq, behavioursOf, Set.mem_union,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨c', r, hrun, hcode, -⟩
    obtain rfl := core_steps_of_stuck hn hrun
    exact core_invoke_not_result r hcode
  · rintro ⟨-, hdiv⟩
    obtain ⟨c', hs, -⟩ := Silmaril.InfiniteTrace.unfold hdiv
    exact hn _ hs

/-! ## The deterministic profile -/

/-- The Core host induced by the closed 2.0 host is the closed Core host. -/
theorem liftHost_closed :
    liftHost (closedV (H := H)) = Silmaril.Wasm.Binaryen.closedHost := by
  funext h S args out
  simp [liftHost, closedV, Silmaril.Wasm.Binaryen.closedHost]

/-- **A closed-host behaviour is the only behaviour** at the deterministic profile. -/
theorem core_behaviours_sub_singleton {g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool}
    {c : Silmaril.Wasm.Execution.Core.Config H} {b : Behaviour CVal}
    (hb : b ∈ behavioursOf (Profile.deterministic g) Silmaril.Wasm.Binaryen.closedHost c)
    (host : CHost H) : behavioursOf (Profile.deterministic g) host c ⊆ {b} := by
  rintro b' hb'
  rcases hb with ⟨t, r, ht, htc, rfl⟩ | ⟨rfl, hd⟩
  · rcases hb' with ⟨y, r', hy, hyc, rfl⟩ | ⟨rfl, hd'⟩
    · obtain rfl := Silmaril.Wasm.Binaryen.DetLift.term_eq ht ⟨r, htc⟩ hy ⟨r', hyc⟩
      obtain rfl := Silmaril.Wasm.Binaryen.DetLift.result_eq htc hyc
      rfl
    · exact (Silmaril.Wasm.Binaryen.DetLift.term_not_div ht ⟨r, htc⟩ hd').elim
  · rcases hb' with ⟨y, r', hy, hyc, rfl⟩ | ⟨rfl, -⟩
    · exact (Silmaril.Wasm.Binaryen.DetLift.div_not_term hd hy ⟨r', hyc⟩).elim
    · rfl

theorem closedV_preserves : Silmaril.Wasm.V2.Execution.HostPreserves (closedV (H := H)) :=
  fun _ _ _ _ _ h => h.elim

theorem closedV_keeps : HostKeepsV (closedV (H := H)) := fun _ _ _ _ _ h => h.elim

/-- **2.0 and Core behaviours are equal at the deterministic profile** when the closed-host 2.0
run of the call has a behaviour. -/
theorem behaviours_det_eq (g : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {s : VStore H} {src : VHost H} {X : CStore H}
    (hwf : Silmaril.Wasm.V2.Execution.StoreWF s)
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X)
    (hp : Silmaril.Wasm.V2.Execution.HostPreserves src) (hk : HostKeepsV src) {a : Nat}
    (ha : a < s.funcs.length) (vs : List VVal)
    (htot : (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) closedV s a
      vs).Nonempty) :
    Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behaviours (Profile.deterministic g) src s a vs) =
      Silmaril.Wasm.Execution.Core.behaviours (Profile.deterministic g) (liftHost src) X a
        (vs.map Silmaril.Wasm.V2.Execution.Val.toCore) := by
  obtain ⟨b, hb⟩ := htot
  have hbC : Behaviour.map Silmaril.Wasm.V2.Execution.Val.toCore b ∈
      behavioursOf (Profile.deterministic g) Silmaril.Wasm.Binaryen.closedHost
        (Silmaril.Wasm.Execution.Core.invoke X a
          (vs.map Silmaril.Wasm.V2.Execution.Val.toCore)) := by
    have hsub := behaviours_sub (Profile.deterministic g) hwf hX closedV_preserves
      closedV_keeps ha vs
    rw [liftHost_closed] at hsub
    exact hsub ⟨b, hb, rfl⟩
  refine Set.Subset.antisymm (behaviours_sub _ hwf hX hp hk ha vs) ?_
  intro b' hb'
  obtain rfl := core_behaviours_sub_singleton hbC (liftHost src) hb'
  exact ⟨b, behaviours_of_closed hb, rfl⟩

end Silmaril.Proofs.Wasm.Models.V2Core
