module

public import Silmaril.Wasm.Resource.Check.Defs
public import Silmaril.Proofs.Wasm.Resource.Handle.Basic
public import Silmaril.Wasm.Verify.Check.Thms

/-!
# Checking handle protocols on modules: soundness

`client_refuted`: a `firstCall?` counterexample for `use` or `free` refutes the client sentence at
every specification profile (`refute_play` gives the play; the client protocol rejects its second
event). `clientSpec_check`: the verifier's `proved` verdicts for "never calls `use`" and "never
calls `free`" give the client sentence, every profile.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify
open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- A first event `use h` or `free h` is rejected by the client protocol. -/
theorem client_first_rejected {X : WIface} {ia iu if_ k : X.Imp} (hk : k = iu ∨ k = if_)
    (j : X.Exp) (a : List Val) (h : Val) :
    (clientSpec ia iu if_).acceptsB [Event.call j a, Event.icall k [h]] = false := by
  rcases hk with rfl | rfl
  · simp [clientSpec, Protocol.acceptsB, Protocol.comap, handleProto, clientEv, HEv.useOf,
      handleStep, fault, Protocol.run]
  · by_cases hku : k = iu
    · subst hku
      simp [clientSpec, Protocol.acceptsB, Protocol.comap, handleProto, clientEv, HEv.useOf,
        handleStep, fault, Protocol.run]
    · simp [clientSpec, Protocol.acceptsB, Protocol.comap, handleProto, clientEv, HEv.freeOf,
        handleStep, fault, Protocol.run, hku]

/-- **Refutation of the client sentence on an instance**, every profile admitting the
deterministic steps of the refuter. -/
theorem client_refuted_inst {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {ia iu if_ k : (ifaceOf I).Imp} (hk : k = iu ∨ k = if_)
    {imp : FnType} (himp : ((CExternType.funcs mt.imports)[k.val]?).bind FnType.ofDefType? = some imp)
    {x : Cex} (hx : refuteStore I.store I.addrs imp k.val oneArg = some x) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (WasmProg.ofInstance I) (clientSpec ia iu if_) := by
  obtain ⟨j, a, e, -, he1, he2, hbad, hplay⟩ := refute_play hI himp hx hP
  have hlen : x.callArgs.length = 1 := by simpa [oneArg] using hbad
  obtain ⟨h, hh⟩ := List.length_eq_one_iff.1 hlen
  have hek : e.1 = k := Fin.ext he1
  refine not_models_of_play (WasmProg.ofInstance I) _ hplay ?_
  change (clientSpec ia iu if_).acceptsB [Event.call j a.1, Event.icall e.1 e.2.1] = false
  rw [he2, hh, hek]
  exact client_first_rejected hk j a.1 h

/-- **Refutation of the client sentence on a module** (every specification profile): the
first-call refuter finds an export call whose first import call is `use` or `free`. -/
theorem client_refuted {m : Module} (hm : (instance? m).isSome = true)
    {ia iu if_ k : (ifaceOf (instOf m)).Imp} (hk : k = iu ∨ k = if_)
    (h : (firstCall? m k.val).isSome = true) (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val)))
      (wasmSem (Profile.spec nd {})) (progOf m) (clientSpec ia iu if_) := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨imp, himp, hr⟩ := Option.bind_eq_some_iff.1 hx
  have himp' : ((CExternType.funcs mt.imports)[k.val]?).bind FnType.ofDefType? = some imp := by
    have := himp
    simp only [importType?, hI.valid, Option.bind_some] at this
    exact this
  exact client_refuted_inst hI hk himp' hr fun _ _ hs => Step.deterministic_refines_spec nd hs

/-- **Clients that never use or free, by the verifier** (every profile). -/
theorem clientSpec_check {m : Module} (hm : (instance? m).isSome = true)
    {ia iu if_ : (ifaceOf (instOf m)).Imp}
    (hu : (check m (.neverCall iu.val)).verdict = .proved)
    (hf : (check m (.neverCall if_.val)).verdict = .proved) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf m) (clientSpec ia iu if_) :=
  clientSpec_of_neverCall _ ia iu if_ (check_neverCall hm hu P) (check_neverCall hm hf P)

end Silmaril.Wasm.Resource
