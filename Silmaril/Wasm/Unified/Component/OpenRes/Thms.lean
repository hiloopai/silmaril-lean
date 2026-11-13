module

public import Silmaril.Wasm.Unified.Component.Open.Thms
public import Silmaril.Wasm.Unified.Component.Res.Defs

/-!
# Resource sentences of open core modules

In `cinst` a core module never calls its imports, so it satisfies every client resource
sentence vacuously. In the open institution `cinstO` its import calls are moves of its strategy
and the resource sentences see them.

* `play_open_call`: if an open model may run export `j` of `m` on `p` as a program whose first
  step calls import `i < |imports|` with `a`, the two-move play "call export `j` with `p`; call
  import `i` with `a`" is a play of the module (`modU`: the narrowing handler, the module's
  reduction, the widening handler, composed by explicit interleavings).
* **`not_osat_open_drop`**: an open module that may begin an export call by dropping a handle
  (a call of `d.drop` with `[h]`) violates the client sentence of `d`: nothing was allocated, so
  `free h` is a use-after-free or a free of a never-allocated handle. `not_osat_toyDrop`: the
  instance at the toy's resource type (`toyDecl`, import `2`).

Not done: a positive client sentence of an open module that allocates and then uses a handle
(it needs a protocol invariant across the three composed layers of `modU`).
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open Silmaril.Wasm.Component Silmaril.Wasm.Unified Silmaril.Wasm.Resource
open Silmaril.Games (Strategy Prog Reduction Zip Legal Path)

variable {S : FSig}

/-- **A first import call of an open module is a play of the module.** -/
theorem play_open_call (M : OModel S) (m : UMod S) (j : Nat) (hj : j < m.exports.length)
    (p : Payload) (i : Nat) (hi : i < m.imports.length) (a : Payload)
    (k : Option Payload → Prog sigU (Option Payload)) (hP : .call (i, a) k ∈ M.obs (m.code j, p)) :
    [.inr (.ask (j, p)), .inl (.ask (i, a))] ∈ denO M (.core m) := by
  have h3 : [.inr (.ask (j, p)), .inl (.ask ((⟨j, hj⟩ : Fin m.exports.length), p))] ∈
      Strategy.ofHandler (widenH (CoreModule.exports m).length) := by
    rw [Strategy.mem_ofHandler]
    refine ⟨_, .vis (.ask _) (.vis (.call (k := fun r => Prog.pure r) ?_) (.nil _))⟩
    show widenH m.exports.length (j, p) = _
    simp only [widenH, hj, ↓reduceDIte]
  have hstep : (coreRedO M m).step (q := ((⟨j, hj⟩ : Fin m.exports.length), p)) .start
      (.run (.call (i, a) k)) := hP
  have hcall : callO m.imports.length (.run (.call (i, a) k)) ⟨i, hi⟩ a (fun r => .run (k r)) :=
    ⟨k, rfl, rfl⟩
  have hlegal : Legal [(.inr (.ask ((⟨j, hj⟩ : Fin m.exports.length), p)) :
      Silmaril.Games.Move (CoreIface.sig m.imports) (CoreIface.sig m.exports)),
      .inl (.ask ((⟨i, hi⟩ : Fin m.imports.length), a))] :=
    ⟨_, .cons (.ask _) (.cons (.call _ _) (.nil _))⟩
  have h2 : [.inr (.ask ((⟨j, hj⟩ : Fin m.exports.length), p)),
      .inl (.ask ((⟨i, hi⟩ : Fin m.imports.length), a))] ∈ (coreSemO M).sem m :=
    Strategy.mem_ofLTS_of_mem_traces
      ⟨_, .vis (.ask _) (.tau (Reduction.Step.tau hstep) (.vis (.call hcall) (.nil _)))⟩ hlegal
  have h1 : [.inr (.ask ((⟨i, hi⟩ : Fin m.imports.length), a)), .inl (.ask (i, a))] ∈
      Strategy.ofHandler (narrowH (CoreModule.imports m).length) := by
    rw [Strategy.mem_ofHandler]
    have hn : narrowH (CoreModule.imports m).length (⟨i, hi⟩, a) =
        Prog.call (i, a) (fun r => Prog.pure r) := rfl
    exact ⟨_, .vis (.ask _) (.vis (.call hn) (.nil _))⟩
  have ht : [.inr (.ask (j, p)), .inl (.ask ((⟨i, hi⟩ : Fin m.imports.length), a))] ∈
      ((coreSemO M).sem m).comp (Strategy.ofHandler (widenH (CoreModule.exports m).length)) :=
    ⟨_, h2, _, h3, .right _ (.sync _ (.left _ .nil))⟩
  exact ⟨_, h1, _, ht, .right _ (.sync _ (.left _ .nil))⟩

/-- **An open module that may drop a handle first violates the client sentence.** -/
theorem not_osat_open_drop (M : OModel S) {K : CMSig} (m : UMod S) (d : ResDecl)
    (hd : CMFeature.resource d ∈ K) (j : Nat) (hj : j < m.exports.length) (p : Payload)
    (h : Flat) (hdi : d.drop < m.imports.length) (k : Option Payload → Prog sigU (Option Payload))
    (hP : .call (d.drop, .flat [h]) k ∈ M.obs (m.code j, p)) :
    ¬ CSatO (T := (S, K)) M (.res ⟨.core m, CProg.uses_core K m⟩ d hd .client) := fun hs =>
  absurd (hs _ (play_open_call M m j hj p d.drop hdi _ k hP))
    (by simp [Protocol.Accepts, Protocol.run, handleProto, handleStep, resEv, fault])

/-- The instance at the toy's resource type: a module importing the toy's interface whose
export may begin by calling `drop` (import `2`). -/
theorem not_osat_toyDrop (M : OModel S) (m : UMod S) (j : Nat) (hj : j < m.exports.length)
    (p : Payload) (h : Flat) (hdi : 2 < m.imports.length)
    (k : Option Payload → Prog sigU (Option Payload))
    (hP : .call (2, .flat [h]) k ∈ M.obs (m.code j, p)) :
    ¬ CSatO (T := (S, toySig)) M
      (.res ⟨.core m, CProg.uses_core toySig m⟩ toyDecl (Or.inr ⟨toyDecl, rfl, rfl⟩) .client) :=
  not_osat_open_drop M m toyDecl _ j hj p h hdi k hP

end Silmaril.Wasm.Unified.Component
