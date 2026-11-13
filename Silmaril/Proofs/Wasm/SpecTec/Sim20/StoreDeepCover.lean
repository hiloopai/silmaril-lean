module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepRules

/-!
# The cover lemma with stores at every depth, and what a step keeps

* `BaseD P`: the base steps. Round 5's `GoodMerge.BaseM` (store-free windows of the widened round
  3 fragment, packed loads, the second pure fragment, the six store steps), plus round 3's first
  pure fragment (`Whole.PureFrag20`, whose `label-vals` and `trap-label` may now carry a
  continuation with stores) and `block`/`loop` (`Whole.BlockFwd20`, whose body may hold stores).
* **`cover20D`**: every V2 step from plain-tail code that is `okD` in the frame's module, over a
  `StoreOkM` store, is a step of `Nest20 (BaseD P)`.
* **`okD_step`**: such a step keeps the code `okD` in the frame's module, the store's functions,
  whole pages and the frame's module.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreDeep

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk Nest20 PureFwd20B PureFrag20 PureFrag20B StoreTop20
  Tail20 WholePages BlockFwd20)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (storeOkI)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (ctrlOkI FwdStep20G fwdF_of_D)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (ctrlOkM okA StoreOkM BaseM LoadPackFwd20)

variable {H : Type}

/-! ## The base -/

/-- **The base steps with stores at every depth.** -/
inductive BaseD (P : Profile) : Config H → Config H → Prop where
  | old {c c' : Config H} (h : FwdStep20G P c c') (hok : c.code.all (okA false c.frame.module) = true) :
      BaseD P c c'
  | pack {c c' : Config H} (h : LoadPackFwd20 c c') : BaseD P c c'
  | store {c c' : Config H} (h : StoreTop20 c c') : BaseD P c c'
  | pureA {s : Store H} {f : Frame} {is is' : List Admin} (h : PureFrag20 P is is') :
      BaseD P ⟨s, f, is⟩ ⟨s, f, is'⟩
  | pureB {c c' : Config H} (h : PureFwd20B P c c') : BaseD P c c'
  | block {c c' : Config H} (h : BlockFwd20 c c') : BaseD P c c'

/-- Every base step is a V2 step. -/
theorem BaseD.step {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseD P c c') :
    Step P host c c' := by
  cases h with
  | old h _ => exact h.step
  | pack h => exact h.step
  | store h => exact h.step
  | pureA h => exact .pure h.pureStep
  | pureB h =>
    cases h with
    | mk h => exact .pure h.pureStep
  | block h => exact h.step

/-- `Good20M`'s base steps are base steps here. -/
theorem BaseD.ofM {P : Profile} {c c' : Config H} (h : BaseM P c c') : BaseD P c c' := by
  cases h with
  | old h hok => exact .old h hok
  | pack h => exact .pack h
  | pureB h => exact .pureB h
  | store h => exact .store h

/-! ## Windows -/

/-- `PureRest20N` has an instruction that is neither covered nor a store. -/
theorem not_pureRest20N_okD {m : ModuleInst} {is : List Admin} (h : Whole.PureRest20N is)
    (hok : is.all (okD m) = true) : False := by
  cases h with
  | @vec is i hm hv =>
    have hi : okD m (.plain i) = true := List.all_eq_true.1 hok _ hm
    have hc : ctrlOkD m i = false := by
      cases i <;> simp_all [vecOp20, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]
    rw [okD_plain, hc] at hi
    exact absurd hi (by decide)
  | unOpInvalid h => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]
  | cvtUndefined h => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

/-- **A read step from covered code is `block`/`loop`, or has a store-free window.** -/
theorem readStep_cases {s : Store H} {f : Frame} {m : ModuleInst} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all (okD m) = true) :
    BlockFwd20 ⟨s, f, is⟩ ⟨s, f, is'⟩ ∨ is.all (okA false m) = true := by
  cases h with
  | block hbt hk => exact .inl (.block hbt hk)
  | loop hbt hk => exact .inl (.loop hbt hk)
  | _ => exact .inr (by simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, List.all_append])

/-! ## The cover lemma -/

/-- The pure steps. -/
theorem cover20D_pure {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hp : PureStep P is is') (ht : Tail20 s f is) (hok : is.all (okD f.module) = true) :
    BaseD P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rcases Whole.pureStep_cover_tail hp ht with h | h | h
  · exact .pureA h
  · exact .pureB (.mk h)
  · exact (not_pureRest20N_okD h hok).elim

/-- The read steps. -/
theorem cover20D_read {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') (hok : is.all (okD f.module) = true) :
    BaseD P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rcases readStep_cases hr hok with h | h
  · exact .block h
  · exact .ofM (GoodMerge.cover20M_read hr (GoodMerge.all_okA_true_of_false h))

theorem okD_ctx_inner {m : ModuleInst} {vs : List Val} {is rest : List Admin}
    (h : (vals vs ++ is ++ rest).all (okD m) = true) : is.all (okD m) = true := by
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.1.2

theorem okD_label_parts {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h : [Admin.label n cont body].all (okD m) = true) :
    cont.all (ctrlOkD m) = true ∧ body.all (okD m) = true := by
  simpa using h

theorem okD_frame_body {m : ModuleInst} {n : Nat} {fr : Frame} {body : List Admin}
    (h : [Admin.frame n fr body].all (okD m) = true) : body.all (okD fr.module) = true := by
  simpa using h

/-- **Every V2 step from plain-tail covered code over a `StoreOkM` store is in the nested
fragment with stores at every depth.** -/
theorem cover20D {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (ht : Tail20 c.store c.frame c.code) (hok : c.code.all (okD c.frame.module) = true)
    (hs : StoreOkM c.store) : Nest20 (BaseD P) c c' := by
  induction h with
  | pure hp => exact .base (cover20D_pure hp ht hok)
  | read hr => exact .base (cover20D_read hr hok)
  | ctxtInstrs hstep hne ih =>
    exact .ctx (ih (Whole.tail20_ctx hstep.not_allVals ht) (okD_ctx_inner hok) hs) hne
  | ctxtLabel _ ih => exact .label (ih (Whole.tail20_label ht).tail (okD_label_parts hok).2 hs)
  | ctxtFrame _ ih => exact .frame (ih (Whole.tail20_frame ht).tail (okD_frame_body hok) hs)
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet hx =>
    exact .base (.old (fwdF_of_D (Whole.fwdC_top (.var (.localSet hx))))
      (by simp [ctrlOkM, ctrlOkI, ctrlOk]))
  | globalSet ha hg =>
    exact .base (.old (fwdF_of_D (Whole.fwdC_top (.var (.globalSet ha hg))))
      (by simp [ctrlOkM, ctrlOkI, ctrlOk]))
  | storeIntTrap ha hm h => exact .base (.store (.intTrap ha hm h))
  | storeIntVal ha hm hw => exact .base (.store (.intVal ha hm hw))
  | storeFloatTrap ha hm h => exact .base (.store (.floatTrap ha hm h))
  | storeFloatVal ha hm hw => exact .base (.store (.floatVal ha hm hw))
  | storePackTrap ha hm h => exact .base (.store (.packTrap ha hm h))
  | storePackVal ha hm hw => exact .base (.store (.packVal ha hm hw))
  | _ => exact absurd hok (by simp [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI])

/-! ## What a step keeps -/

/-- What a step from covered code keeps. -/
def KeepsD (c c' : Config H) : Prop :=
  c'.code.all (okD c'.frame.module) = true ∧ c'.store.funcs = c.store.funcs ∧
    (WholePages c.store → WholePages c'.store) ∧ c'.frame.module = c.frame.module

theorem keepsD_same {s : Store H} {f f' : Frame} {is is' : List Admin}
    (h : is'.all (okD f'.module) = true) (hm : f'.module = f.module) :
    KeepsD ⟨s, f, is⟩ ⟨s, f', is'⟩ := ⟨h, rfl, id, hm⟩

/-- **Every pure step keeps covered code covered** in the same module. -/
theorem okD_pureStep {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureStep P is is') (hok : is.all (okD m) = true) : is'.all (okD m) = true := by
  cases h <;> simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, List.all_append]

/-- **Every read step keeps covered code covered**, over a covered store. -/
theorem okD_readStep {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all (okD f.module) = true) (hs : StoreOkM s) :
    is'.all (okD f.module) = true := by
  cases h with
  | @callAddr a vs fi fn hf hcode hk =>
    obtain ⟨fn', hc', hb⟩ := hs a fi hf
    rw [hcode] at hc'
    cases hc'
    simpa using all_ctrlOkD_of_ctrlOkM hb
  | _ => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, List.all_append]

/-- The six store steps keep the functions and whole pages, and end in `trap` or nothing. -/
theorem keepsD_storeTop {c c' : Config H} (h : StoreTop20 c c') : KeepsD c c' := by
  cases h with
  | intTrap _ _ _ | floatTrap _ _ _ | packTrap _ _ _ => exact keepsD_same rfl rfl
  | intVal _ hm hw | floatVal _ hm hw | packVal _ hm hw =>
    exact ⟨rfl, rfl, fun hp => StoreGood.WholePages.setMemInst hp hm
      (StoreGood.writeBytes?_size hw), rfl⟩

/-- **Every V2 step from covered code over a covered store keeps the code covered, the store's
functions, whole pages and the frame's module.** -/
theorem okD_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : c.code.all (okD c.frame.module) = true)
    (hs : StoreOkM c.store) : KeepsD c c' := by
  induction h with
  | pure hp => exact keepsD_same (okD_pureStep hp hok) rfl
  | read hr => exact keepsD_same (okD_readStep hr hok hs) rfl
  | ctxtInstrs _ _ ih =>
    simp only [List.all_append, Bool.and_eq_true] at hok
    obtain ⟨hi, hm, hw, hmod⟩ := ih hok.1.2 hs
    have hi' : _ = true := hmod ▸ hi
    refine ⟨?_, hm, hw, hmod⟩
    rw [hmod]
    simp [List.all_append, hi', hok.2]
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    have hb : cont.all (ctrlOkD f.module) = true ∧ is.all (okD f.module) = true := by
      simpa using hok
    obtain ⟨hi, hm, hw, hmod⟩ := ih hb.2 hs
    have hi' : _ = true := hmod ▸ hi
    refine ⟨?_, hm, hw, hmod⟩
    rw [hmod]
    simp [hb.1, hi']
  | ctxtFrame _ ih =>
    obtain ⟨hi, hm, hw, -⟩ := ih (by simpa using hok) hs
    exact ⟨by simpa using hi, hm, hw, rfl⟩
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet => exact ⟨rfl, rfl, id, rfl⟩
  | globalSet => exact ⟨rfl, rfl, fun hp => hp, rfl⟩
  | storeIntTrap ha hm h => exact keepsD_storeTop (.intTrap ha hm h)
  | storeIntVal ha hm hw => exact keepsD_storeTop (.intVal ha hm hw)
  | storeFloatTrap ha hm h => exact keepsD_storeTop (.floatTrap ha hm h)
  | storeFloatVal ha hm hw => exact keepsD_storeTop (.floatVal ha hm hw)
  | storePackTrap ha hm h => exact keepsD_storeTop (.packTrap ha hm h)
  | storePackVal ha hm hw => exact keepsD_storeTop (.packVal ha hm hw)
  | _ => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

end Silmaril.Wasm.SpecTec.Sim20.StoreDeep
