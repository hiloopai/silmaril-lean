module

public import Silmaril.Wasm.Game.LinkStart.Defs
public import Silmaril.Games.Inst.Thms
public import Silmaril.Proofs.Wasm.Game.LinkStart.Order

/-!
# Links with start functions: proofs

* The instantiation outcomes of the strategy of a closed instance with its start
  phase are the Core outcomes of the start function under the empty host
  (`closed_instReady_iff`, `closed_instFails_iff`, `closed_instDiverges_iff`):
  without imports the instantiation run is host-free (`reach_of_steps`).
* For a link with start functions (`StartSetup.linkInst`), every profile: a
  provider start function that may trap or throw makes the link fail alike,
  one that may diverge makes it diverge, the link is ready when both start
  functions may return without import calls, and the link is ready **only if**
  the provider's start function may return (`link_instReady_imp`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStart

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {I : ScalarInstance} {P : Profile} {s : Store Nat} {start : Option Nat}

/-- Host-free runs of the start thread are empty-host Core runs to their configurations. -/
theorem reach_iff_steps {d : Config Nat} :
    (∃ c, Relation.ReflTransGen (InternalP P) (s, startThread start) c ∧ d = c.2.config c.1) ↔
      Steps P (Det.noHost : HostSemantics Nat) (startConfig s start) d := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact Silmaril.Proofs.Wasm.Game.Reach.steps hc
  · intro h
    obtain ⟨s', t', hr, hd⟩ := Silmaril.Proofs.Wasm.Game.reach_of_steps h
    exact ⟨(s', t'), hr, hd.symm⟩

/-- Instantiation of an instance succeeds silently exactly when its start phase may return
under the empty host. -/
theorem instReady_iff :
    (I.instStrategy P s start).InstReady ↔
      ∃ s', StartsTo P (Det.noHost : HostSemantics Nat) s start s' := by
  rw [ScalarInstance.instStrategy, DStrategy.ofInst_instReady_iff]
  constructor
  · rintro ⟨c, st, hc, hres, rfl⟩
    exact ⟨_, _, reach_iff_steps.1 ⟨c, hc, rfl⟩, hres, Thread.config_store _ _⟩
  · rintro ⟨_, c', hc', hcode, rfl⟩
    obtain ⟨c, hc, rfl⟩ := reach_iff_steps.2 hc'
    exact ⟨c, c.1, hc, hcode, rfl⟩

/-- Instantiation of an instance fails silently with `b` exactly when its start phase may
trap or throw `b` under the empty host. -/
theorem instFails_iff {b : Behaviour Val} :
    (I.instStrategy P s start).InstFails b ↔
      ∃ (c' : Config Nat) (r : Result),
        Steps P (Det.noHost : HostSemantics Nat) (startConfig s start) c' ∧
        c'.code = r.toAdmin ∧ (r = .trap ∨ ∃ x, r = .throw x) ∧ b = r.toBehaviour := by
  rw [ScalarInstance.instStrategy, DStrategy.ofInst_instFails_iff]
  constructor
  · rintro ⟨c, hc, ⟨hres, rfl⟩ | ⟨x, hres, rfl⟩⟩
    · exact ⟨_, _, reach_iff_steps.1 ⟨c, hc, rfl⟩, hres, .inl rfl, rfl⟩
    · exact ⟨_, _, reach_iff_steps.1 ⟨c, hc, rfl⟩, hres, .inr ⟨x, rfl⟩, rfl⟩
  · rintro ⟨c', r, hc', hcode, hr, rfl⟩
    obtain ⟨c, hc, rfl⟩ := reach_iff_steps.2 hc'
    rcases hr with rfl | ⟨x, rfl⟩
    · exact ⟨c, hc, .inl ⟨hcode, rfl⟩⟩
    · exact ⟨c, hc, .inr ⟨x, hcode, rfl⟩⟩

/-- Instantiation of an instance diverges silently exactly when its start phase may diverge
under the empty host. -/
theorem instDiverges_iff :
    (I.instStrategy P s start).InstDiverges ↔
      Diverges P (Det.noHost : HostSemantics Nat) (startConfig s start) := by
  rw [ScalarInstance.instStrategy, DStrategy.ofInst_instDiverges_iff]
  constructor
  · exact InfiniteTrace.map (fun x : Store Nat × Thread => x.2.config x.1)
      fun _ _ h => InternalP.toStep P _ h
  · refine InfiniteTrace.of_map (R := InternalP P) (S := Step P (Det.noHost : HostSemantics Nat))
      (a := (s, startThread start)) (fun x : Store Nat × Thread => x.2.config x.1) (fun _ => True)
      ?_ trivial
    rintro ⟨s₁, t₁⟩ b - hb
    rcases (Silmaril.Proofs.Wasm.Game.stepP_iff P _ s₁ t₁ b).1 hb with
      ⟨s', f', code', rfl, hi⟩ | ⟨-, -, -, -, -, ⟨-, -, ⟨⟩, -⟩ | ⟨⟨⟩, -⟩⟩
    exact ⟨(s', .active f' code'), hi, trivial, rfl⟩

namespace StartSetup

variable (S : StartSetup)

/-- **A failing provider start function makes the link fail alike.** -/
theorem linkInst_instFails {b : Behaviour Val}
    (h : ∃ (c' : Config Nat) (r : Result),
      Steps P (Det.noHost : HostSemantics Nat) (startConfig S.sp S.provStart) c' ∧
      c'.code = r.toAdmin ∧ (r = .trap ∨ ∃ x, r = .throw x) ∧ b = r.toBehaviour) :
    (S.linkInst P).InstFails b :=
  DStrategy.link_instFails (instFails_iff.2 h)

/-- **A diverging provider start function makes the link diverge.** -/
theorem linkInst_instDiverges
    (h : Diverges P (Det.noHost : HostSemantics Nat) (startConfig S.sp S.provStart)) :
    (S.linkInst P).InstDiverges :=
  DStrategy.link_instDiverges (instDiverges_iff.2 h)

/-- **The link is ready when the provider's start function, then the consumer's, may return**
(the consumer's start function making no import call). -/
theorem linkInst_instReady {sp' sc' : Store Nat}
    (hp : StartsTo P (Det.noHost : HostSemantics Nat) S.sp S.provStart sp')
    (hc : StartsTo P (Det.noHost : HostSemantics Nat) S.scs S.consStart sc') :
    (S.linkInst P).InstReady := by
  obtain ⟨c', hc', hcode, -⟩ := hc
  obtain ⟨c, hrun, rfl⟩ := reach_iff_steps.2 hc'
  exact DStrategy.link_instReady (instReady_iff.2 ⟨sp', hp⟩) hrun ⟨hcode, rfl⟩

/-- **The link is ready only if the provider's start function may return**: the provider is
instantiated, and its start function run, before the consumer. -/
theorem linkInst_instReady_imp (h : (S.linkInst P).InstReady) :
    ∃ sp', StartsTo P (Det.noHost : HostSemantics Nat) S.sp S.provStart sp' :=
  instReady_iff.1 (link_instReady_imp h)

end StartSetup

end Silmaril.Proofs.Wasm.Game.LinkStart
