module

public import Silmaril.Wasm.Component.Param.Defs
public import Silmaril.Wasm.Component.Semantics.Thms
import all Silmaril.Wasm.Component.Semantics.Thms
public import Silmaril.Games.LTS.Thms
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Restrictions of an engine: proofs

* `restrict_lawful`, `restrict_resumeLawful`: the laws of an engine pass to its restrictions.
* `steps_restrict`, `steps_of_restrict`, `diverges_of_restrict`: restricted runs are runs of the
  engine; from a configuration in the runtime invariant, runs of the engine are restricted runs
  when the invariant is closed under internal steps.
* `engineStrategy_restrict_le`: the game semantics of a restricted instance refines the
  engine's; `engineStrategy_restrict_eq`: they are equal for an instance that respects the
  restriction (`Respects`).
* `engineSem_restrict_le`: the same for the core semantics of the IR.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps Lawful ResumeLawful Extends)

variable {E : Engine} {r : Restriction E}

/-! ## Laws -/

theorem extends_restrict {H : Type} {s s' : E.Store H} (h : E.Extends s s') :
    (restrict E r).Extends s s' :=
  ⟨h.funcType, h.memAddrType, h.memSize, h.tableAddrType, h.callout⟩

theorem extends_of_restrict {H : Type} {s s' : E.Store H} (h : (restrict E r).Extends s s') :
    E.Extends s s' :=
  ⟨h.funcType, h.memAddrType, h.memSize, h.tableAddrType, h.callout⟩

/-- The laws of an engine pass to its restrictions. -/
theorem restrict_lawful [L : E.Lawful] : (restrict E r).Lawful where
  flatType?_ofFlatType := L.flatType?_ofFlatType
  returned_no_step h hi := L.returned_no_step h hi.1
  callout_no_step h hi := L.callout_no_step h hi.1
  stuck_no_step h hi := L.stuck_no_step h hi.1
  externSub_refl := L.externSub_refl
  externSub_trans := L.externSub_trans
  asFunc?_ofFunc := L.asFunc?_ofFunc
  internal_extends h := extends_restrict (L.internal_extends h.1)
  prepare_extends h := extends_restrict (L.prepare_extends h)
  allocHost_extends h := extends_restrict (L.allocHost_extends h)
  allocHost_fresh := L.allocHost_fresh
  allocHost_frame := L.allocHost_frame
  allocHost_funcType := L.allocHost_funcType
  allocHost_callout := L.allocHost_callout
  memWrite_extends h := extends_restrict (L.memWrite_extends h)
  memWrite_memSize := L.memWrite_memSize
  memWrite_memAddrType := L.memWrite_memAddrType
  memWrite_read := L.memWrite_read
  memWrite_read_other := L.memWrite_read_other
  memRead_isSome_iff := L.memRead_isSome_iff
  memRead_size := L.memRead_size
  memWrite_isSome_iff := L.memWrite_isSome_iff
  memAddrType_isSome_iff := L.memAddrType_isSome_iff

/-- Resumption progress passes to restrictions. -/
theorem restrict_resumeLawful [R : E.ResumeLawful] : (restrict E r).ResumeLawful where
  resume_unparked h hx := R.resume_unparked h (extends_of_restrict hx)

/-! ## Runs -/

theorem steps_of_restrict {H : Type} {c c' : E.Config H} (h : Steps (restrict E r) c c') :
    Steps E c c' := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih step.1

/-- From a configuration of the invariant, a run of the engine is a restricted run, and ends in
the invariant. -/
theorem steps_restrict (hc : r.Closed) {H : Type} {c c' : E.Config H} (h0 : r.Rt c)
    (h : Steps E c c') : Steps (restrict E r) c c' ∧ r.Rt c' := by
  induction h with
  | refl => exact ⟨.refl, h0⟩
  | tail _ step ih => exact ⟨.tail ih.1 ⟨step, hc ih.2 step⟩, hc ih.2 step⟩

theorem diverges_of_restrict {H : Type} {c : E.Config H}
    (h : Silmaril.Wasm.Component.Engine.CoreEngine.Diverges (restrict E r) c) :
    Silmaril.Wasm.Component.Engine.CoreEngine.Diverges E c :=
  Silmaril.InfiniteTrace.map id (fun _ _ h => h.1) h

/-! ## Game semantics -/

theorem eTrans_unres {addrs : List E.FuncAddr} {imps exps : CoreIface}
    {x y : EState (restrict E r) imps.length exps.length} {m}
    (h : ETrans (restrict E r) addrs imps exps x m y) :
    ETrans E addrs imps exps x.unres m y.unres := by
  cases h with
  | call h => exact .call h
  | refuse h => exact .refuse h
  | refused => exact .refused
  | ucall run callout hh => exact .ucall (steps_of_restrict run) callout hh
  | uret v => exact .uret v
  | oret run final => exact .oret (steps_of_restrict run) final
  | otrap run final => exact .otrap (steps_of_restrict run) final

/-- **The game semantics of a restricted instance refines the engine's.** -/
theorem engineStrategy_restrict_le (I : EInstance E) (imps exps : CoreIface) :
    engineStrategy (restrict E r) I.res imps exps ≤ engineStrategy E I imps exps := by
  refine LTS.Simulation.ofLTS_le
    { R := fun x y => y = EState.unres x, init := rfl, step := ?_ }
  rintro x x' y l rfl ⟨m, rfl, hm⟩
  exact ⟨_, LTS.Run.of_step ⟨m, rfl, eTrans_unres hm⟩, rfl⟩

/-- **An instance respects a restriction** along a store invariant `Sto`: the initial store is
in `Sto`, invocations of exports from `Sto` stores and resumptions of parked threads of the
runtime invariant are in it, and the stores of the runtime invariant are in `Sto`. -/
structure Respects (r : Restriction E) (I : EInstance E) (Sto : E.Store Nat → Prop) : Prop where
  closed : r.Closed
  init : Sto I.store
  invoke : ∀ s, Sto s → ∀ a ∈ I.addrs, ∀ xs, r.Rt (s, E.invoke a xs)
  store : ∀ s t, r.Rt (s, t) → Sto s
  resume : ∀ (s : E.Store Nat) (t : E.Thread Nat) (h : Nat) args res, r.Rt (s, t) →
    E.status s t = .callout h args →
    r.Rt (s, E.resume s t res)

/-- The invariant of the hidden states of an instance that respects a restriction. -/
def EInv (r : Restriction E) (Sto : E.Store Nat → Prop) {n k : Nat} : EState E n k → Prop
  | .idle s => Sto s
  | .running _ s t => r.Rt (s, t)
  | .waiting _ s t _ => r.Rt (s, t) ∧ ∃ h args, E.status s t = .callout h args
  | .refusing _ s => Sto s

theorem callee?_mem {addrs : List E.FuncAddr} {exps : CoreIface} {q} {a : E.FuncAddr}
    {xs : List Flat} (h : callee? addrs exps q = some (a, xs)) : a ∈ addrs := by
  unfold callee? at h
  split at h
  · split at h
    · obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact List.mem_of_getElem? hb
    · cases h
  · cases h

theorem eTrans_res {I : EInstance E} {Sto : E.Store Nat → Prop} (hR : Respects r I Sto)
    {imps exps : CoreIface} {x y : EState E imps.length exps.length} {m}
    (hx : EInv r Sto x) (h : ETrans E I.addrs imps exps x m y) :
    ETrans (restrict E r) I.addrs imps exps x.res m y.res ∧ EInv r Sto y := by
  cases h with
  | call h => exact ⟨.call h, hR.invoke _ hx _ (callee?_mem h) _⟩
  | refuse h => exact ⟨.refuse h, hx⟩
  | refused => exact ⟨.refused, hx⟩
  | ucall run callout hh =>
    obtain ⟨run', hy⟩ := steps_restrict hR.closed hx run
    exact ⟨.ucall run' callout hh, hy, _, _, callout⟩
  | uret v =>
    obtain ⟨hx, h, args, hc⟩ := hx
    exact ⟨.uret v, hR.resume _ _ _ _ _ hx hc⟩
  | oret run final =>
    obtain ⟨run', hy⟩ := steps_restrict hR.closed hx run
    exact ⟨.oret run' final, hR.store _ _ hy⟩
  | otrap run final =>
    obtain ⟨run', hy⟩ := steps_restrict hR.closed hx run
    exact ⟨.otrap run' final, hR.store _ _ hy⟩

/-- **The game semantics of an instance that respects a restriction is that of the restricted
instance.** -/
theorem engineStrategy_restrict_eq {I : EInstance E} {Sto : E.Store Nat → Prop}
    (hR : Respects r I Sto) (imps exps : CoreIface) :
    engineStrategy (restrict E r) I.res imps exps = engineStrategy E I imps exps := by
  refine le_antisymm (engineStrategy_restrict_le I imps exps) (LTS.Simulation.ofLTS_le
    { R := fun x y => y = EState.res x ∧ EInv r Sto x, init := ⟨rfl, hR.init⟩, step := ?_ })
  rintro x x' y l ⟨rfl, hx⟩ ⟨m, rfl, hm⟩
  obtain ⟨hm', hx'⟩ := eTrans_res hR hx hm
  exact ⟨_, LTS.Run.of_step ⟨m, rfl, hm'⟩, rfl, hx'⟩

/-! ## The core semantics of the IR -/

theorem allocHosts_restrict (s : E.Store Nat) (i : Nat) (imps : CoreIface) :
    allocHosts (restrict E r) s i imps = allocHosts E s i imps := by
  induction imps generalizing s i with
  | nil => rfl
  | cons x is ih => simp only [allocHosts, ih]

theorem instOf_restrict (m : E.Module) (imps exps : CoreIface) :
    instOf (restrict E r) m imps exps = (instOf E m imps exps).map EInstance.res := by
  unfold instOf
  simp only [allocHosts_restrict]
  split
  · simp_all only [Option.map_map, Function.comp_def, EInstance.res]
    rfl
  · simp_all

/-- **The core semantics of a restriction refines the engine's.** -/
theorem engineSem_restrict_le (M : Type) [CoreModule M] (emb : M → E.Module) :
    (engineSem (restrict E r) M emb).Le (engineSem E M emb) := fun (m : M) => by
  simp only [engineSem, instOf_restrict]
  cases instOf E (emb m) (CoreModule.imports m) (CoreModule.exports m) with
  | none => exact le_rfl
  | some I => exact engineStrategy_restrict_le I _ _

end Silmaril.Proofs.Wasm.Component.Param
