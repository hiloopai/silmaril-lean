module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegSpec
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegValid
public import Silmaril.Proofs.Wasm.Game.Linking.Split.Typed
public import Silmaril.Proofs.Wasm.Game.Start.Main

/-!
# The outcome of a trapping segment initialisation

A trapped configuration (`TRAP` under a callout context) only bubbles the trap, under **any**
host (it has no host-call redex): every run stays trapped in the same store and frame
(`steps_doomed_host`), the only result it reaches is `trap` (`result_doomed`), it reaches it
(`fill_trap_reach`) and it cannot diverge (`not_diverges_doomed`, the code shrinks).

`spec_trap_outcome`: when the direct segment initialisation traps, the closed program whose
instantiation phase is the spec's `$instantiate` configuration fails with `traps`, and only
so: it is never ready, never diverges during instantiation, and fails exactly with `traps`
(every profile, every environment).

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm.Game Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation Silmaril.Proofs.Wasm.Game.Choice

variable {P : Profile} {host : HostSemantics Nat}

/-- A host step of a trapped configuration is a host-free step. -/
theorem step_doomed_host {E : Ctx} {s : Store Nat} {f : Frame} {d : Config Nat}
    (h : Step P host ⟨s, f, E.fill [.trap]⟩ d) : Step P noHost ⟨s, f, E.fill [.trap]⟩ d := by
  rcases Step.split_host h with h' | ⟨E', a, hh, args, hd, -⟩
  · exact h'
  · have hn : decompose? s (E.fill [.trap]) = none := Ctx.decompose?_fill_trap s E
    rw [hd] at hn
    cases hn

theorem doomed_eq {s : Store Nat} {f : Frame} {d : Config Nat} (h : Doomed s f d) :
    ∃ E' : Ctx, d = ⟨s, f, E'.fill [.trap]⟩ := by
  obtain ⟨hs, hf, E', hc⟩ := h
  refine ⟨E', ?_⟩
  obtain ⟨st, fr, co⟩ := d
  have hs' : st = s := hs
  have hf' : fr = f := hf
  have hc' : co = E'.fill [.trap] := hc
  rw [hs', hf', hc']

/-- Runs of a trapped configuration, under any host, stay trapped. -/
theorem steps_doomed_host {E : Ctx} {s : Store Nat} {f : Frame} {d : Config Nat}
    (h : Steps P host ⟨s, f, E.fill [.trap]⟩ d) : Doomed s f d := by
  induction h with
  | refl => exact ⟨rfl, rfl, E, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨E', hb⟩ := doomed_eq ih
    rw [hb] at hstep
    exact step_doomed (step_doomed_host hstep)

/-- The only result a trapped configuration reaches is `trap`. -/
theorem result_doomed {E : Ctx} {s : Store Nat} {f : Frame} {d : Config Nat} {r : Result}
    (h : Steps P host ⟨s, f, E.fill [.trap]⟩ d) (hr : d.code = r.toAdmin) : r = .trap := by
  obtain ⟨-, -, E', hc⟩ := steps_doomed_host h
  exact fill_trap_toAdmin (hc.symm.trans hr)

/-- A trapped configuration reaches the bare trap, under any host. -/
theorem reach_trap_host (E : Ctx) (s : Store Nat) (f : Frame) :
    Steps P host ⟨s, f, E.fill [.trap]⟩ ⟨s, f, [.trap]⟩ :=
  Reach.steps (Silmaril.Proofs.Wasm.Game.Linking.Split.fill_trap_reach P s E f)

/-- A trapped configuration does not diverge, under any host. -/
theorem not_diverges_doomed (E : Ctx) (s : Store Nat) (f : Frame) :
    ¬ Diverges P host ⟨s, f, E.fill [.trap]⟩ := by
  rintro ⟨tr, h0, hstep⟩
  have key : ∀ n, ∃ E' : Ctx, tr n = ⟨s, f, E'.fill [.trap]⟩ ∧
      sizeOf (E'.fill [.trap]) + n ≤ sizeOf (E.fill [.trap]) := by
    intro n
    induction n with
    | zero => exact ⟨E, h0, by omega⟩
    | succ n ih =>
      obtain ⟨E', hn, hle⟩ := ih
      have hs : Step P noHost ⟨s, f, E'.fill [.trap]⟩ (tr (n + 1)) :=
        step_doomed_host (hn ▸ hstep n)
      obtain ⟨E'', he⟩ := doomed_eq (step_doomed hs)
      have hlt : sizeOf (E''.fill [.trap]) < sizeOf (E'.fill [.trap]) := by
        have h' := trapped_step_lt hs
        rw [he] at h'
        exact h'
      exact ⟨E'', he, by omega⟩
  obtain ⟨E', -, hle⟩ := key (sizeOf (E.fill [.trap]) + 1)
  omega

/-- The instantiation outcome of a closed program whose instantiation thread is trapped:
never ready, never diverging, failing exactly with `traps`. -/
theorem closedInstT_trapped (I : ScalarInstance) (P : Profile) (K : Env I.E) (s : Store Nat)
    (f : Frame) (E : Ctx) :
    ¬ (I.closedInstT P s (.active f (E.fill [.trap])) K).InstReady ∧
    ¬ (I.closedInstT P s (.active f (E.fill [.trap])) K).InstDiverges ∧
    ∀ b, (I.closedInstT P s (.active f (E.fill [.trap])) K).InstFails b ↔ b = .traps := by
  refine ⟨fun hr => ?_, fun hd => ?_, fun b => ?_⟩
  · obtain ⟨c', hs, hc⟩ := (Silmaril.Proofs.Wasm.Game.Start.instReady_closedInstT_iff
      (I := I) (P := P) (s := s) (K := K) (t₀ := .active f (E.fill [.trap]))).1 hr
    cases result_doomed hs hc
  · have hdiv := (Silmaril.Proofs.Wasm.Game.Start.div_inst_iff (I := I) (P := P) (s₀ := s)
      (t₀ := .active f (E.fill [.trap])) (K := K)).1 hd
    exact not_diverges_doomed E s f hdiv
  · rw [Silmaril.Proofs.Wasm.Game.Start.instFails_closedInstT_iff]
    constructor
    · rintro ⟨c', r, hs, hc, -, rfl⟩
      rw [result_doomed hs hc]
      rfl
    · rintro rfl
      exact ⟨_, .trap, reach_trap_host E s f, rfl, .inl rfl, rfl⟩

/-- **Trapping segment initialisation fails instantiation with `traps`**, every profile and
environment: when the residue preparation of single allocation succeeds and its direct segment
initialisation traps, the closed program with the spec's instantiation phase is never ready,
never diverges during instantiation, and fails exactly with `traps`. -/
theorem spec_trap_outcome {s : Store Nat} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length) (hm : OffsetsConst m)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    {s'' : Store Nat}
    (htrap : initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue = .trap s'') :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile) (K : Env I.E),
        ¬ (I.closedSpec P (c.withStart st) K).InstReady ∧
        ¬ (I.closedSpec P (c.withStart st) K).InstDiverges ∧
        ∀ b, (I.closedSpec P (c.withStart st) K).InstFails b ↔ b = .traps := by
  obtain ⟨c, hc, hall⟩ := spec_trap_seg hs hw hxb hm hg hp htrap
  refine ⟨c, hc, fun I P K => ?_⟩
  obtain ⟨W, R, -, hcl⟩ := hall I P
  have hfill : vals W ++ .trap :: R = (Ctx.top W R).fill [.trap] := by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append]
  rw [hcl K]
  have ht : configThread ⟨s'', c₁.frame, vals W ++ .trap :: R⟩ =
      .active c₁.frame ((Ctx.top W R).fill [.trap]) := by
    rw [← hfill]
    rfl
  rw [ht]
  exact closedInstT_trapped I P K s'' c₁.frame (Ctx.top W R)

/-- `spec_trap_outcome` for validated modules (`OffsetsConst` from validation). -/
theorem spec_trap_outcome_valid {s : Store Nat} {m : Module} {mt : CModuleType}
    {xas : List ExternAddr} (hv : validate? m = some mt) (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    {s'' : Store Nat}
    (htrap : initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue = .trap s'') :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile) (K : Env I.E),
        ¬ (I.closedSpec P (c.withStart st) K).InstReady ∧
        ¬ (I.closedSpec P (c.withStart st) K).InstDiverges ∧
        ∀ b, (I.closedSpec P (c.withStart st) K).InstFails b ↔ b = .traps :=
  spec_trap_outcome hs hw hxb (offsetsConst_of_validate hv) hg hp htrap

/-- `spec_eq_once_seg` for validated modules. -/
theorem spec_eq_once_seg_valid {s s' : Store Nat} {m : Module} {mt : CModuleType}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx} (hv : validate? m = some mt)
    (hs : StoreOk s) (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile),
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) ∧
        ∀ K : Env I.E, I.closedSpec P (c.withStart st) K =
          I.closedInstT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) K :=
  spec_eq_once_seg hs hw hxb (offsetsConst_of_validate hv) ho

end Silmaril.Proofs.Wasm.Game.SpecGlobals
