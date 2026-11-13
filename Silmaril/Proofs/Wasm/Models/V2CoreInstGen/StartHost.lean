module

public import Silmaril.Wasm.Models.V2CoreInstHostFn.Thms
public import Silmaril.Wasm.Models.V2CoreInst.Thms

/-!
# `domInstP` fails at a store with a host function

An earlier step put `hostDivPt` (one host function of type `[] → []`, host `divV`) in the new domain
`domInstHost P` and left open whether it is 's `domInstP P`, which reads behaviours at
the closed host `closedV`. It is not:

* `startMod`: a 2.0 module importing one function of type `[] → []` and starting with it. It is
  valid (`startMod_ok`) and has a Core image (`startMod_toCore`).
* Core instantiates the image at `hostDivPt`'s Core point (`core_inst_startMod`, through the
  copied `instantiate_sim` and an earlier `instantiate_imports_any`).
* Every 2.0 instantiation of `startMod` at `hostDivPt` starts at `CALL 0` over a store whose only
  function is the host function (`inst_startMod_cfg`). Under `closedV` that code steps once, to
  `CALL_ADDR 0` (`step_call_inv`), which is stuck (`step_callAddr_inv`: a host function has no
  outcome under `closedV`). Neither code is a result, so the behaviours are empty
  (`behaviours_startMod_closed`).
* **`not_domInstP_hostDivPt`**: `hostDivPt` is not in `domInstP P`, at every profile. With
  an earlier `domInstHost_hostDivPt`, the two domains differ, and `domInstHost` is the one that
  fits stores with host functions.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstGen

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Models.V2CoreInstFn (nopType nopModInst)
open Silmaril.Wasm.Models.V2CoreInstImp (domInstP)
open Silmaril.Wasm.Models.V2CoreInstHostFn (hostFunc hostFnStore hostDivPt)
open Silmaril.Proofs.Wasm.Models.V2Core (step_callAddr_inv steps_of_stuck callAddr_not_result)

variable {H : Type}

/-! ## The module -/

/-- A module importing one function of type `[] → []` and starting with it. -/
def startMod : Module :=
  { types := [nopType], imports := [⟨"", "", .func ⟨0⟩⟩], start := some ⟨0⟩ }

/-- Its validation context. -/
def startCtx : Context :=
  { types := [nopType], funcs := [nopType], globals := [], tables := [], mems := [], elems := [],
    datas := [], refs := [] }

/-- Its constant context. -/
def startCtx' : Context :=
  { types := [nopType], funcs := [nopType], globals := [], tables := [], mems := [], refs := [] }

/-- **`startMod` is valid**: it imports `FUNC nopType` and exports nothing. -/
theorem startMod_ok : ModuleOk startMod [.func nopType] [] :=
  ModuleOk.mk (ft' := [nopType]) (ft := []) (gt := []) (tt := []) (mt := []) (rt := [])
    (C := startCtx) (C' := startCtx') (.cons (by decide) .nil) (.cons (by decide) .nil) .nil .nil
    .nil .nil (fun _ h => by simp [startMod] at h) .nil
    (fun x hx => by
      simp only [startMod, Option.some.injEq] at hx
      subst hx
      rfl)
    .nil (by decide) (by decide) rfl rfl

theorem startMod_valid : ModuleValid startMod := ⟨_, _, startMod_ok⟩

/-- The Core image of `startMod`. -/
def startModC : Silmaril.Wasm.Module := (Module.toCore startMod).getD {}

theorem startMod_toCore : Module.toCore startMod = some startModC := rfl

theorem segBounded_startMod :
    Silmaril.Proofs.Wasm.Models.V2CoreInstDom.SegBounded startMod := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [startMod]

/-- `hostDivPt`'s store types the import `FUNC 0` at `nopType`. -/
theorem hostFn_importable : List.Forall₂ (ExternAddrOk hostFnStore) [.func 0] [.func nopType] :=
  .cons (.func (fi := hostFunc) rfl) .nil

/-! ## Core instantiates the image -/

/-- **Core instantiates `startMod`'s image at `hostDivPt`'s Core point.** -/
theorem core_inst_startMod (P : Profile) :
    ∃ C, Silmaril.Wasm.Execution.Core.Instantiate P (ptCore hostDivPt).2 (ptCore hostDivPt).1
      startModC ([ExternAddr.func 0].map ExternAddr.toCore) C := by
  obtain ⟨c, hc⟩ := Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.instantiate_imports_any (H := Nat) P
    Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.storeOk_hostFnStore startMod_ok hostFn_importable
    segBounded_startMod
  have hwf : StoreWF hostFnStore :=
    (Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.hostDivPt_dom P).1.1
  obtain ⟨C, hC, -⟩ := Silmaril.Wasm.V2.Execution.instantiate_sim (tgt := (ptCore hostDivPt).2)
    ⟨hwf, rfl⟩ (S := (ptCore hostDivPt).1) rfl startMod_toCore (hc hostDivPt.2)
  exact ⟨C, hC⟩

/-! ## Every 2.0 instantiation is stuck under the closed host -/

/-- The store and module instance `allocModule?` gives `startMod` over `hostFnStore`. -/
theorem allocModule?_startMod :
    allocModule? hostFnStore startMod [.func 0] [] [] =
      some (hostFnStore, { types := [nopType], funcs := [0] }) := rfl

/-- **The configuration of every 2.0 instantiation of `startMod` at `hostDivPt`.** -/
theorem inst_startMod_cfg {P : Profile} {host : HostSemantics Nat} {c : Config Nat}
    (h : Instantiate P host hostFnStore startMod [.func 0] c) :
    c = ⟨hostFnStore, { module := { types := [nopType], funcs := [0] } }, [.plain (.call ⟨0⟩)]⟩ := by
  obtain ⟨vs, rss, s', mi, hvs, hrss, hal, hc⟩ := h.run
  have hv : vs = [] := by cases hvs; rfl
  have hr : rss = [] := by cases hrss; rfl
  subst hv hr
  rw [allocModule?_startMod] at hal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hal).symm
  rw [hc]
  rfl

/-! ## `CALL x` steps only to `CALL_ADDR` -/

/-- Values, `CALL` and `CALL_ADDR`: what no pure rule's left-hand side consists of. -/
def callish : Admin → Bool
  | .plain (.intConst _ _) | .plain (.floatConst _ _) | .plain (.vecConst _)
  | .plain (.refNull _) | .refFuncAddr _ | .refHostAddr _ | .callAddr _ | .plain (.call _) => true
  | _ => false

@[simp] theorem callish_toAdmin (v : VVal) : callish (Val.toAdmin v) = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> rfl

theorem pure_not_callish {P : Profile} {is is' : List Admin} (hp : PureStep P is is')
    (hb : is.all callish = true) : False := by
  cases hp <;> simp [callish, vals, constI32] at hb

theorem not_vals_callAddr_call {vs : List VVal} {a : Nat} {x : Silmaril.Wasm.FuncIdx} :
    vals vs ++ [Admin.callAddr a] ≠ [.plain (.call x)] := by
  intro h
  have := congrArg List.getLast? h
  simp at this

/-- The read rules at `CALL x`. -/
theorem read_call_inv {s : VStore H} {f : Frame} {is' : List Admin} {x : Silmaril.Wasm.FuncIdx}
    (hr : ReadStep s f [.plain (.call x)] is') :
    ∃ a, f.module.funcAddr? x = some a ∧ is' = [.callAddr a] := by
  generalize e : [Admin.plain (.call x)] = l at hr
  cases hr with
  | call hx =>
    obtain rfl : _ = x := by simpa using e.symm
    exact ⟨_, hx, rfl⟩
  | callAddr => exact absurd e.symm not_vals_callAddr_call
  | _ =>
    have e' := congrArg List.getLast? e
    simp [vals, constI32] at e'

theorem callish_of_code {is : List Admin} {x : Silmaril.Wasm.FuncIdx}
    (hc : is = [.plain (.call x)]) : is.all callish = true := by
  subst hc
  rfl

theorem read_call_inv' {s : VStore H} {f : Frame} {is is' : List Admin} {x : Silmaril.Wasm.FuncIdx}
    (hr : ReadStep s f is is') (hc : is = [.plain (.call x)]) :
    ∃ a, f.module.funcAddr? x = some a ∧ is' = [.callAddr a] := by
  subst hc
  exact read_call_inv hr

/-- A context split of a one-instruction code has an empty context. -/
theorem ctxt_one {vs : List VVal} {is rest : List Admin} {y : Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (his : is ≠ []) (h : vals vs ++ is ++ rest = [y]) : False := by
  have hl := congrArg List.length h
  simp only [List.length_append, vals, List.length_map, List.length_singleton] at hl
  have h₁ := List.length_pos_iff.2 his
  rcases hne with h' | h'
  · have := List.length_pos_iff.2 h'; omega
  · have := List.length_pos_iff.2 h'; omega

/-- **Inversion at `CALL x`**: a step goes to `CALL_ADDR a` for the function address `a` of `x`. -/
theorem step_call_inv {P : Profile} {host : VHost H} {c c' : Config H} (h : Step P host c c') :
    ∀ {x : Silmaril.Wasm.FuncIdx}, c.code = [.plain (.call x)] →
      ∃ a, c.frame.module.funcAddr? x = some a ∧ c' = ⟨c.store, c.frame, [.callAddr a]⟩ := by
  induction h with
  | pure hp => exact fun hc => (pure_not_callish hp (callish_of_code hc)).elim
  | read hr =>
    intro x hc
    obtain ⟨a, ha, he⟩ := read_call_inv' hr hc
    exact ⟨a, ha, by subst he; rfl⟩
  | ctxtInstrs hstep hne _ =>
    refine fun hc => (ctxt_one hne (fun h => ?_) hc).elim
    have hv := hstep.not_allVals
    simp [h] at hv
  | ctxtLabel _ _ => exact fun hc => by simp at hc
  | ctxtFrame _ _ => exact fun hc => by simp at hc
  | callAddrHost => exact fun hc => absurd hc not_vals_callAddr_call
  | callAddrHostDiv => exact fun hc => absurd hc not_vals_callAddr_call
  | _ => exact fun hc => by simp [constI32] at hc

/-- `CALL x` is not a result. -/
theorem call_not_result {x : Silmaril.Wasm.FuncIdx} (r : Result) :
    [Admin.plain (.call x)] ≠ r.toAdmin := by
  intro h
  cases r with
  | values ws =>
    have hb := congrArg (fun l => List.all l Admin.isVal) h
    simp [Result.toAdmin, Admin.isVal, Admin.val?] at hb
  | trap => simp [Result.toAdmin] at h

/-! ## The behaviours -/

/-- The instantiation frame of `startMod`. -/
def startFrame : Frame := { module := { types := [nopType], funcs := [0] } }

/-- `CALL_ADDR 0` over `hostFnStore` is stuck under the closed host. -/
theorem stuck_callAddr {P : Profile} (c' : Config Nat) :
    ¬ Step P closedV ⟨hostFnStore, startFrame, [.callAddr 0]⟩ c' := by
  intro h
  obtain ⟨fi, hf, pre, args, -, -, hcase⟩ := step_callAddr_inv (vs := []) h rfl
  have hfi : fi = hostFunc := by simpa [Store.funcInst?, hostFnStore] using hf.symm
  subst hfi
  rcases hcase with ⟨fn, hfn⟩ | ⟨hh, -, ⟨_, _, hr, -⟩ | ⟨hr, -⟩⟩
  · simp [hostFunc] at hfn
  · exact hr
  · exact hr

/-- `CALL 0` over `hostFnStore` steps only to `CALL_ADDR 0`. -/
theorem step_start {P : Profile} {c' : Config Nat}
    (h : Step P closedV ⟨hostFnStore, startFrame, [.plain (.call ⟨0⟩)]⟩ c') :
    c' = ⟨hostFnStore, startFrame, [.callAddr 0]⟩ := by
  obtain ⟨a, ha, rfl⟩ := step_call_inv h rfl
  have h0 : startFrame.module.funcAddr? ⟨0⟩ = some 0 := rfl
  obtain rfl : a = 0 := Option.some.inj (ha.symm.trans h0)
  rfl

/-- A run from `CALL 0` stays at `CALL 0` or `CALL_ADDR 0`. -/
theorem steps_start {P : Profile} {c' : Config Nat}
    (h : Steps P closedV ⟨hostFnStore, startFrame, [.plain (.call ⟨0⟩)]⟩ c') :
    c' = ⟨hostFnStore, startFrame, [.plain (.call ⟨0⟩)]⟩ ∨
      c' = ⟨hostFnStore, startFrame, [.callAddr 0]⟩ := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c₁, h₁, h₂⟩
  · exact .inl rfl
  · rw [step_start h₁] at h₂
    exact .inr (steps_of_stuck stuck_callAddr h₂)

/-- **No behaviour under the closed host.** -/
theorem behaviours_startMod_closed (P : Profile) :
    behavioursOf P closedV
      (⟨hostFnStore, startFrame, [.plain (.call ⟨0⟩)]⟩ : Config Nat) = ∅ := by
  ext b
  simp only [behavioursOf, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨c', r, hrun, hcode, -⟩
    rcases steps_start hrun with rfl | rfl
    · exact call_not_result r hcode
    · exact callAddr_not_result (vs := []) r hcode
  · rintro ⟨-, hdiv⟩
    obtain ⟨c₁, h₁, hdiv₁⟩ := Silmaril.InfiniteTrace.unfold hdiv
    rw [step_start h₁] at hdiv₁
    obtain ⟨c₂, h₂, -⟩ := Silmaril.InfiniteTrace.unfold hdiv₁
    exact stuck_callAddr _ h₂

/-- **`hostDivPt` is not in `domInstP P`**, at every profile: `startMod` is valid, Core
instantiates its image there, and no 2.0 instantiation of it has a behaviour under `closedV`. -/
theorem not_domInstP_hostDivPt (P : Profile) : ¬ domInstP P hostDivPt := by
  rintro ⟨-, hd⟩
  obtain ⟨c, hc, b, hb⟩ := hd startMod startModC [.func 0] startMod_valid startMod_toCore
    (core_inst_startMod P)
  rw [inst_startMod_cfg hc] at hb
  have h := behaviours_startMod_closed P
  rw [startFrame] at h
  rw [h] at hb
  exact hb

end Silmaril.Proofs.Wasm.Models.V2CoreInstGen
