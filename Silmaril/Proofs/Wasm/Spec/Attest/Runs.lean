module

public import Silmaril.Proofs.Wasm.Spec.Attest.Shape
public import Silmaril.Proofs.Wasm.Spec.Attest.CoreTrap

/-!
# Core 3.0 runs of the gate and of the `true` module

Explicit host-free Core runs, at every profile `P` (no determinism; every step is one rule of
Core `Step P`):

* `run_gate_trap`: a gate function whose other flag is `0` sets its own flag and traps;
* `run_gate_call`: a gate function whose other flag is nonzero sets its own flag and reaches the
  call of `attest`;
* `gate_live`: the play `attestL`, trap, `attestR`, call of `attest` of the gate's strategy;
* `tt_play`: the play `fire`, call of `attest` of the `true` module's strategy.

New proofs, following `Silmaril.Proofs.Wasm.Game.UntypedExample` (this repository).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify Silmaril.Wasm.Spec.Attest
  Silmaril.Wasm.Spec.Attest.Core Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-! ### Steps in context -/

/-- A step of a head of the code, in front of a non-empty rest. -/
theorem step_head {s s' : Store Nat} {f f' : Frame} {is is' rest : List Admin}
    (h : Step P Det.noHost ⟨s, f, is⟩ ⟨s', f', is'⟩) (hr : rest ≠ []) :
    Step P Det.noHost ⟨s, f, is ++ rest⟩ ⟨s', f', is' ++ rest⟩ := by
  simpa [vals] using Step.ctxtInstrs (vs := []) (rest := rest) h (.inr hr)

/-- A step in the body of a called function (inside its frame and label). -/
theorem step_body {s s' : Store Nat} {F : Frame} {X X' : List Admin}
    (h : Step P Det.noHost ⟨s, F, X⟩ ⟨s', F, X'⟩) :
    Step P Det.noHost ⟨s, {}, [.frame 0 F [.label 0 [] X]]⟩ ⟨s', {}, [.frame 0 F [.label 0 [] X']]⟩ :=
  Step.ctxtFrame (Step.ctxtLabel h)

/-- Entering a function `[] → []` with no locals. -/
theorem step_enter {s : Store Nat} {a : Nat} {fi : FuncInst Nat} {t : TypeIdx} {body : List Instr}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type voidTy)
    (hc : fi.code = .wasm ⟨t, [], body⟩) :
    Step P Det.noHost (invoke s a [])
      ⟨s, {}, [.frame 0 (Frame.forCall fi.module [] []) [.label 0 [] (expression body)]]⟩ :=
  Step.callRefFunc (vs := []) (c := .callRefType ((s.funcs[a]?.map FuncInst.type).getD default))
    trivial hf he rfl hc

/-- The callout of `attest` at the end of a run, inside the body's frame and label. -/
theorem decompose_label {s : Store Nat} (n : Nat) (cont : List Instr) (body rest : List Admin) :
    decompose? s (.label n cont body :: rest) =
      (decompose? s body).map fun (E, a, h, args) => (.label [] n cont E rest, a, h, args) := by
  rw [decompose?_of_split (splitVals_cons_nonval rfl rest)]
  rfl

theorem decompose_frame {s : Store Nat} (n : Nat) (F : Frame) (body rest : List Admin) :
    decompose? s (.frame n F body :: rest) =
      (decompose? s body).map fun (E, a, h, args) => (.frame [] n F E rest, a, h, args) := by
  rw [decompose?_of_split (splitVals_cons_nonval rfl rest)]
  rfl

/-- A call of the host function `attest` (host code `0`, at address `0`) is a callout. -/
theorem decompose_attest {s : Store Nat} {fi₀ : FuncInst Nat} (hf : s.funcs[0]? = some fi₀)
    (he : Expand fi₀.type voidTy) (hc : fi₀.code = .host 0) :
    decompose? s [.ref (.func 0), .callRefType fi₀.type] = some (.top [] [], 0, 0, []) :=
  decompose?_redex (vs := []) (c := .callRefType fi₀.type) trivial hf he rfl hc

/-! ### The gate's functions -/

section Gate

variable {s : Store Nat} {F : Frame} {m o : Fin (2 ^ 32)} {am ao : Nat} {gm go : GlobalInst}

/-- Setting the own flag and reading the other one. -/
theorem steps_set_get (hset : s.global? F ⟨m⟩ = some (am, gm))
    (hget : (s.setGlobal am (.i32 1)).global? F ⟨o⟩ = some (ao, go)) :
    Steps P Det.noHost ⟨s, F, expression (gateBody m o)⟩
      ⟨s.setGlobal am (.i32 1), F, [go.value.toAdmin, .plain (.if_ .empty [.call ⟨0⟩] []),
        .plain .unreachable]⟩ := by
  have h₁ : Step P Det.noHost ⟨s, F, [(Val.i32 1).toAdmin, .plain (.globalSet ⟨m⟩)] ++
      [.plain (.globalGet ⟨o⟩), .plain (.if_ .empty [.call ⟨0⟩] []), .plain .unreachable]⟩
      ⟨s.setGlobal am (.i32 1), F, [] ++ [.plain (.globalGet ⟨o⟩),
        .plain (.if_ .empty [.call ⟨0⟩] []), .plain .unreachable]⟩ :=
    step_head (Step.variable (VariableStep.globalSet hset)) (by simp)
  have h₂ : Step P Det.noHost ⟨s.setGlobal am (.i32 1), F, [.plain (.globalGet ⟨o⟩)] ++
      [.plain (.if_ .empty [.call ⟨0⟩] []), .plain .unreachable]⟩
      ⟨s.setGlobal am (.i32 1), F, [go.value.toAdmin] ++ [.plain (.if_ .empty [.call ⟨0⟩] []),
        .plain .unreachable]⟩ :=
    step_head (Step.variable (VariableStep.globalGet hget)) (by simp)
  exact (Relation.ReflTransGen.single h₁).tail h₂

/-- **A gate function whose other flag is `0` traps**, after setting its own flag. -/
theorem steps_body_trap (hset : s.global? F ⟨m⟩ = some (am, gm))
    (hget : (s.setGlobal am (.i32 1)).global? F ⟨o⟩ = some (ao, go)) (hv : go.value = .i32 0) :
    Steps P Det.noHost ⟨s, F, expression (gateBody m o)⟩ ⟨s.setGlobal am (.i32 1), F, [.trap]⟩ := by
  have h₀ := steps_set_get (P := P) hset hget
  rw [hv] at h₀
  have h₃ : Step P Det.noHost ⟨s.setGlobal am (.i32 1), F, [constI32 0,
      .plain (.if_ .empty [.call ⟨0⟩] [])] ++ [.plain .unreachable]⟩
      ⟨s.setGlobal am (.i32 1), F, [.plain (.block .empty [])] ++ [.plain .unreachable]⟩ :=
    step_head Step.ifFalse (by simp)
  have h₄ : Step P Det.noHost ⟨s.setGlobal am (.i32 1), F, [.plain (.block .empty [])] ++
      [.plain .unreachable]⟩ ⟨s.setGlobal am (.i32 1), F, [.label 0 [] []] ++ [.plain .unreachable]⟩ :=
    step_head (Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl) (by simp)
  have h₅ : Step P Det.noHost ⟨s.setGlobal am (.i32 1), F, [.label 0 [] []] ++ [.plain .unreachable]⟩
      ⟨s.setGlobal am (.i32 1), F, [] ++ [.plain .unreachable]⟩ :=
    step_head (Step.labelVals (vs := [])) (by simp)
  have h₆ : Step P Det.noHost ⟨s.setGlobal am (.i32 1), F, [.plain .unreachable]⟩
      ⟨s.setGlobal am (.i32 1), F, [.trap]⟩ := Step.parametric .unreachable
  exact ((((h₀.tail h₃).tail h₄).tail h₅).tail h₆)

/-- **A gate function whose other flag is set calls `attest`**, after setting its own flag. -/
theorem steps_body_call {c : BitVec 32} {fi₀ : FuncInst Nat}
    (hset : s.global? F ⟨m⟩ = some (am, gm))
    (hget : (s.setGlobal am (.i32 1)).global? F ⟨o⟩ = some (ao, go)) (hv : go.value = .i32 c)
    (hc : c ≠ 0) (hx : F.module.funcs[0]? = some 0) (hf : s.funcs[0]? = some fi₀) :
    Steps P Det.noHost ⟨s, F, expression (gateBody m o)⟩ ⟨s.setGlobal am (.i32 1), F,
      [.label 0 [] [.ref (.func 0), .callRefType fi₀.type], .plain .unreachable]⟩ := by
  have h₀ := steps_set_get (P := P) hset hget
  rw [hv] at h₀
  have hf' : (s.setGlobal am (.i32 1)).funcs[0]? = some fi₀ := hf
  have h₃ : Step P Det.noHost ⟨s.setGlobal am (.i32 1), F, [constI32 c,
      .plain (.if_ .empty [.call ⟨0⟩] [])] ++ [.plain .unreachable]⟩
      ⟨s.setGlobal am (.i32 1), F, [.plain (.block .empty [.call ⟨0⟩])] ++ [.plain .unreachable]⟩ :=
    step_head (Step.ifTrue hc) (by simp)
  have h₄ : Step P Det.noHost ⟨s.setGlobal am (.i32 1), F, [.plain (.block .empty [.call ⟨0⟩])] ++
      [.plain .unreachable]⟩ ⟨s.setGlobal am (.i32 1), F, [.label 0 [] [.plain (.call ⟨0⟩)]] ++
        [.plain .unreachable]⟩ :=
    step_head (Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl) (by simp)
  have h₅ : Step P Det.noHost ⟨s.setGlobal am (.i32 1), F, [.label 0 [] [.plain (.call ⟨0⟩)]] ++
      [.plain .unreachable]⟩ ⟨s.setGlobal am (.i32 1), F,
        [.label 0 [] [.ref (.func 0), .callRefType fi₀.type]] ++ [.plain .unreachable]⟩ :=
    step_head (Step.ctxtLabel (Step.call hx hf')) (by simp)
  exact (((h₀.tail h₃).tail h₄).tail h₅)

end Gate

/-- The body steps, lifted into the frame and label of the call. -/
theorem steps_in_body {c c' : Config Nat} (h : Steps P Det.noHost c c') :
    Steps P Det.noHost ⟨c.store, {}, [.frame 0 c.frame [.label 0 [] c.code]]⟩
      ⟨c'.store, {}, [.frame 0 c'.frame [.label 0 [] c'.code]]⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (Step.ctxtFrame (Step.ctxtLabel hst))

/-! ### Plays -/

/-- A host-free Core run of an export call, read as a run of the machine from the pending
invocation. -/
theorem reach_of_invoke {s s' : Store Nat} {a : Nat} {X₀ : List Admin} {c' : Config Nat}
    (h₀ : Step P Det.noHost (invoke s a []) ⟨s, {}, X₀⟩)
    (h : Steps P Det.noHost ⟨s, {}, X₀⟩ c') (hs : c'.store = s') :
    Reach P (s, .pending a []) (s', .active c'.frame c'.code) := by
  have h₁ : InternalP P (s, .pending a []) (s, .active {} X₀) := ⟨{}, X₀, rfl, h₀⟩
  rw [← hs]
  exact Relation.ReflTransGen.head h₁ (reach_of_steps_active h)

/-- The import question of a callout of host code `0` without arguments. -/
theorem importOp_attest {I : ScalarInstance} (hI : I.imports = [unitFn]) :
    ∃ e, I.importOp? 0 [] = some e := by
  have hlt : 0 < I.imports.length := by rw [hI]; decide
  have ht : List.Forall₂ ScalarType.HasVal (I.imports.get ⟨0, hlt⟩).params [] := by
    have hg : I.imports.get ⟨0, hlt⟩ = unitFn := by simp [hI]
    rw [hg]
    exact .nil
  exact ⟨⟨⟨0, hlt⟩, ⟨[], ht⟩⟩, by simp only [ScalarInstance.importOp?, ifaceOp?, dite_eq_left hlt,
    dite_eq_left ht]⟩

/-- **The gate's liveness play** (every profile): `attestL` is called and traps after setting
`gL`; then `attestR`, finding `gL` set, calls `attest`. -/
theorem gate_live (P : Profile) : ∃ e, [.inr (.ask (gateOp 0)), .inr (.ans (gateOp 0) .trap),
    .inr (.ask (gateOp 1)), .inl (.ask e)] ∈ gateI.strategy P gateI.store := by
  obtain ⟨fi₀, fi₁, fi₂, g₀, g₁, h⟩ := gateShape
  obtain ⟨t₁, hc₁⟩ := h.code₁
  obtain ⟨t₂, hc₂⟩ := h.code₂
  have hf₀ : gS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  have hf₁ : gS.funcs[1]? = some fi₁ := by rw [h.funcs]; rfl
  have hf₂ : gS.funcs[2]? = some fi₂ := by rw [h.funcs]; rfl
  let s₁ : Store Nat := gS.setGlobal 0 (.i32 1)
  let s₂ : Store Nat := s₁.setGlobal 1 (.i32 1)
  have hgl₁ : s₁.globals = [{ g₀ with value := .i32 1 }, g₁] := by
    simp only [s₁, Store.setGlobal, h.globals, List.modify_zero_cons]
  have hset₁ : gS.global? (Frame.forCall fi₁.module [] []) ⟨0⟩ = some (0, g₀) := by
    simp [Store.global?, Frame.forCall, h.glob₁, h.globals, Idx.toNat]
  have hget₁ : s₁.global? (Frame.forCall fi₁.module [] []) ⟨1⟩ = some (1, g₁) := by
    simp [Store.global?, Frame.forCall, h.glob₁, hgl₁, Idx.toNat]
  have hset₂ : s₁.global? (Frame.forCall fi₂.module [] []) ⟨1⟩ = some (1, g₁) := by
    simp [Store.global?, Frame.forCall, h.glob₂, hgl₁, Idx.toNat]
  have hget₂ : s₂.global? (Frame.forCall fi₂.module [] []) ⟨0⟩ =
      some (0, { g₀ with value := .i32 1 }) := by
    simp [s₂, Store.global?, Frame.forCall, h.glob₂, Store.setGlobal, hgl₁, Idx.toNat]
  have hx : (Frame.forCall fi₂.module [] []).module.funcs[0]? = some 0 := by
    simp [Frame.forCall, h.mfun₂]
  -- the run of `attestL`
  have runL₁ := steps_in_body (P := P) (steps_body_trap (P := P) hset₁ hget₁ h.val₁)
  have runL : Steps P Det.noHost ⟨gS, {}, [.frame 0 (Frame.forCall fi₁.module [] [])
      [.label 0 [] (expression (gateBody 0 1))]]⟩ ⟨s₁, {}, [.trap]⟩ :=
    (runL₁.tail (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame
  have reachL : Reach P (gS, gateI.initThread (gateOp 0)) (s₁, .active {} [.trap]) := by
    show Reach P (gS, .pending (gateI.addr (gateOp 0).1) []) _
    rw [gateI_addr0]
    exact reach_of_invoke (step_enter hf₁ h.ty₁ hc₁) runL rfl
  -- the run of `attestR`
  have hf₀' : s₁.funcs[0]? = some fi₀ := hf₀
  have hf₂' : s₁.funcs[2]? = some fi₂ := hf₂
  have runR := steps_in_body (P := P) (steps_body_call (P := P) hset₂ hget₂ rfl (by decide) hx hf₀')
  have reachR : Reach P (s₁, gateI.initThread (gateOp 1)) (s₂, .active {}
      [.frame 0 (Frame.forCall fi₂.module [] []) [.label 0 []
        [.label 0 [] [.ref (.func 0), .callRefType fi₀.type], .plain .unreachable]]]) := by
    show Reach P (s₁, .pending (gateI.addr (gateOp 1).1) []) _
    rw [gateI_addr1]
    exact reach_of_invoke (step_enter hf₂' h.ty₂ hc₂) runR rfl
  have hf₀'' : s₂.funcs[0]? = some fi₀ := hf₀
  have hcall : CalloutAt s₂ (.active {} [.frame 0 (Frame.forCall fi₂.module [] []) [.label 0 []
      [.label 0 [] [.ref (.func 0), .callRefType fi₀.type], .plain .unreachable]]]) 0 [] := by
    show ∃ E a, decompose? s₂ [.frame 0 (Frame.forCall fi₂.module [] []) [.label 0 []
      [.label 0 [] [.ref (.func 0), .callRefType fi₀.type], .plain .unreachable]]] = some (E, a, 0, [])
    rw [decompose_frame, decompose_label, decompose_label, decompose_attest hf₀'' h.ty₀ h.code₀]
    exact ⟨_, _, rfl⟩
  obtain ⟨e, he⟩ := importOp_attest (I := gateI) rfl
  refine ⟨e, gateI.mem_strategy_iff.2 ⟨_, .cons (.call _ _) (.cons (.oret (r := .trap) reachL
    (show ((Thread.active {} [.trap]).config s₁).code = [.trap] from rfl) (ofResult_trap _)) (.cons (.call _ _) (.cons (.ucall reachR hcall he) (.nil _))))⟩⟩

/-- **The `true` module may attest** (every profile): `fire` calls `attest`. -/
theorem tt_play (P : Profile) : ∃ f e, [.inr (.ask f), .inl (.ask e)] ∈
    (leafOf ttMod).prog.inst.strategy P (leafOf ttMod).prog.store := by
  obtain ⟨fi₀, fi₁, h⟩ := ttShape
  obtain ⟨t₁, hc₁⟩ := h.code₁
  have hf₀ : tS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  have hf₁ : tS.funcs[1]? = some fi₁ := by rw [h.funcs]; rfl
  have hx : (Frame.forCall fi₁.module [] []).module.funcs[0]? = some 0 := by
    simp [Frame.forCall, h.mfun₁]
  have hlt : 0 < (instOf ttMod).exports.length := by rw [tt_exports]; decide
  have haddr : (leafOf ttMod).prog.inst.addr ⟨0, hlt⟩ = 1 := by
    show (instOf ttMod).addrs.getD 0 0 = 1
    rw [tt_addrs]
    rfl
  have hty : List.Forall₂ ScalarType.HasVal ((leafOf ttMod).prog.inst.exports.get ⟨0, hlt⟩).params
      [] := by
    have hg : (leafOf ttMod).prog.inst.exports.get ⟨0, hlt⟩ = unitFn := by
      show (instOf ttMod).exports.get ⟨0, hlt⟩ = unitFn
      simp [tt_exports]
    rw [hg]
    exact .nil
  obtain ⟨e, he⟩ := importOp_attest (I := (leafOf ttMod).prog.inst) rfl
  have hsteps : Steps P Det.noHost (invoke tS ((leafOf ttMod).prog.inst.addr ⟨0, hlt⟩) [])
      ⟨tS, {}, [.frame 0 (Frame.forCall fi₁.module [] [])
        [.label 0 [] [.ref (.func 0), .callRefType fi₀.type]]]⟩ := by
    rw [haddr]
    exact .tail (.single (step_enter hf₁ h.ty₁ hc₁)) (step_body (Step.call hx hf₀))
  have hdec : ∃ E, decompose? tS [.frame 0 (Frame.forCall fi₁.module [] [])
      [.label 0 [] [.ref (.func 0), .callRefType fi₀.type]]] = some (E, 0, 0, []) := by
    rw [decompose_frame, decompose_label, decompose_attest hf₀ h.ty₀ h.code₀]
    exact ⟨_, rfl⟩
  obtain ⟨E, hE⟩ := hdec
  exact ⟨⟨⟨0, hlt⟩, ⟨[], hty⟩⟩, e, ScalarInstance.ask_call_iff.2 ⟨_, hsteps, E, 0, 0, [], hE, he⟩⟩

end Silmaril.Proofs.Wasm.Spec.Attest
