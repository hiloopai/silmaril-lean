module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnCall
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepNest

/-!
# The base steps once the store's functions hold stores, and the cover lemma

* `BaseF P`: the two pure fragments, `block`/`loop`, the read rules  and round 5
  (`local.get`, `global.get`, `ref.func`, `call`, `call_addr`, the unpacked and packed loads,
  `table.size`, `memory.size`, `table.get`, both `call_indirect` rules), `local.set`,
  `global.set` and the six scalar stores. Unlike `StoreDeep.BaseD`, every kind is listed by its
  leaf relation, so each can be fired in `simEnv20T` from a state typed there.
* **`cover20F`**: every V2 step from plain-tail code that is `okD` in the frame's module, over a
  `StoreOkD` store, is a step of `Nest20 (BaseF P)`.
* **`okF_step`**: such a step keeps the code `okD`, the store's functions, whole pages and the
  frame's module (`StoreDeep.KeepsD`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk Nest20 PureFwd20B PureFrag20 StoreTop20 Tail20
  WholePages BlockFwd20 ReadFwd20 CallFwd20 CallAddrFwd20 LoadFwd20 CallIndFwd20 CallIndTrapFwd20)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (storeOkI)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (ctrlOkI SizeFwd20 TableGetFwd20)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (ctrlOkM okA LoadPackFwd20)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (ctrlOkD okD KeepsD keepsD_same okD_pureStep
  okD_ctx_inner okD_label_parts okD_frame_body keepsD_storeTop)

variable {H : Type}

/-! ## The base -/

/-- **The base steps once the store's functions may hold stores.** -/
inductive BaseF (P : Profile) : Config H → Config H → Prop where
  | pureA {s : Store H} {f : Frame} {is is' : List Admin} (h : PureFrag20 P is is') :
      BaseF P ⟨s, f, is⟩ ⟨s, f, is'⟩
  | pureB {c c' : Config H} (h : PureFwd20B P c c') : BaseF P c c'
  | block {c c' : Config H} (h : BlockFwd20 c c') : BaseF P c c'
  | read {c c' : Config H} (h : ReadFwd20 c c') : BaseF P c c'
  | call {c c' : Config H} (h : CallFwd20 c c') : BaseF P c c'
  | callAddr {c c' : Config H} (h : CallAddrFwd20 c c') : BaseF P c c'
  | load {c c' : Config H} (h : LoadFwd20 c c') : BaseF P c c'
  | pack {c c' : Config H} (h : LoadPackFwd20 c c') : BaseF P c c'
  | size {c c' : Config H} (h : SizeFwd20 c c') : BaseF P c c'
  | tget {c c' : Config H} (h : TableGetFwd20 c c') : BaseF P c c'
  | callInd {c c' : Config H} (h : CallIndFwd20 c c') : BaseF P c c'
  | callIndTrap {c c' : Config H} (h : CallIndTrapFwd20 c c') : BaseF P c c'
  | localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
      (hx : x.toNat < f.locals.length) :
      BaseF P ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩
  | globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : GlobalAddr}
      {gi : GlobalInst} (ha : f.module.globalAddr? x = some a) (hg : s.globalInst? a = some gi) :
      BaseF P ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩
        ⟨s.setGlobalInst a { gi with value := v }, f, []⟩
  | store {c c' : Config H} (h : StoreTop20 c c') : BaseF P c c'

/-- Every base step is a V2 step. -/
theorem BaseF.step {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseF P c c') :
    Step P host c c' := by
  cases h with
  | pureA h => exact .pure h.pureStep
  | pureB h =>
    cases h with
    | mk h => exact .pure h.pureStep
  | block h => exact h.step
  | read h => exact h.step
  | call h =>
    cases h with
    | call ha => exact .read (State.call_step ha)
  | callAddr h => exact h.step
  | load h => exact h.step
  | pack h => exact h.step
  | size h => exact h.step
  | tget h => exact h.step
  | callInd h => exact h.step
  | callIndTrap h => exact h.step
  | localSet hx => exact .localSet hx
  | globalSet ha hg => exact .globalSet ha hg
  | store h => exact h.step

/-! ## The cover lemma -/

/-- The pure steps. -/
theorem cover20F_pure {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hp : PureStep P is is') (ht : Tail20 s f is) (hok : is.all (okD f.module) = true) :
    BaseF P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rcases Whole.pureStep_cover_tail hp ht with h | h | h
  · exact .pureA h
  · exact .pureB (.mk h)
  · exact (StoreDeep.not_pureRest20N_okD h hok).elim

/-- **The read steps from covered code.** -/
theorem cover20F_read {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') (hok : is.all (okD f.module) = true) :
    BaseF P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases hr with
  | block hbt hk => exact .block (.block hbt hk)
  | loop hbt hk => exact .block (.loop hbt hk)
  | call hx => exact .call (.call (by simpa [ModuleInst.funcAddr?] using hx))
  | callAddr hf hcode hk => exact .callAddr (.mk hf hcode hk)
  | loadIntTrap hm h => exact .load (.intTrap hm h)
  | loadIntVal hm hb => exact .load (.intVal hm hb)
  | loadFloatTrap hm h => exact .load (.floatTrap hm h)
  | loadFloatVal hm hb => exact .load (.floatVal hm hb)
  | loadPackTrap hm h => exact .pack (.trap hm h)
  | @loadPackVal t sz sx ao i mi c hm hb => cases sx <;> exact .pack (.val hm hb)
  | localGet h => exact .read (.localGet (by simpa [State.local?, Frame.local?] using h))
  | globalGet h =>
    obtain ⟨a, ha, hg⟩ := Whole.global?_some h
    exact .read (.globalGet ha hg)
  | refFunc hx => exact .read (.refFunc (by simpa [ModuleInst.funcAddr?] using hx))
  | callIndirectCall ht hr hf hy => exact .callInd (.mk ht hr hf hy)
  | tableSize ht hn => exact .size (.table ht hn)
  | memorySize hm hn => exact .size (.memory hm hn)
  | tableGetTrap ht h => exact .tget (.trap ht h)
  | tableGetVal ht hr => exact .tget (.val ht hr)
  | @callIndirectTrap x y i ti ht h =>
    have hy : (f.module.type? y).isSome = true := by
      simpa [ctrlOkD, ctrlOkM, ctrlOkI, storeOkI] using (by simpa [ctrlOkD, ctrlOkM, ctrlOkI, storeOkI] using hok : _ ∧ _).2
    obtain ⟨ft, hft⟩ := Option.isSome_iff_exists.1 hy
    exact .callIndTrap (.mk ht (ft := ft) hft h)
  | _ => simp [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI] at hok

/-- **Every V2 step from plain-tail covered code over a `StoreOkD` store is in the nested
fragment `BaseF`.** -/
theorem cover20F {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (ht : Tail20 c.store c.frame c.code) (hok : c.code.all (okD c.frame.module) = true)
    (hs : StoreOkD c.store) : Nest20 (BaseF P) c c' := by
  induction h with
  | pure hp => exact .base (cover20F_pure hp ht hok)
  | read hr => exact .base (cover20F_read hr hok)
  | ctxtInstrs hstep hne ih =>
    exact .ctx (ih (Whole.tail20_ctx hstep.not_allVals ht) (okD_ctx_inner hok) hs) hne
  | ctxtLabel _ ih => exact .label (ih (Whole.tail20_label ht).tail (okD_label_parts hok).2 hs)
  | ctxtFrame _ ih => exact .frame (ih (Whole.tail20_frame ht).tail (okD_frame_body hok) hs)
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet hx => exact .base (.localSet hx)
  | globalSet ha hg => exact .base (.globalSet ha hg)
  | storeIntTrap ha hm h => exact .base (.store (.intTrap ha hm h))
  | storeIntVal ha hm hw => exact .base (.store (.intVal ha hm hw))
  | storeFloatTrap ha hm h => exact .base (.store (.floatTrap ha hm h))
  | storeFloatVal ha hm hw => exact .base (.store (.floatVal ha hm hw))
  | storePackTrap ha hm h => exact .base (.store (.packTrap ha hm h))
  | storePackVal ha hm hw => exact .base (.store (.packVal ha hm hw))
  | _ => exact absurd hok (by simp [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI])

/-! ## What a step keeps -/

/-- **Every read step keeps covered code covered**, over a `StoreOkD` store. -/
theorem okF_readStep {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all (okD f.module) = true) (hs : StoreOkD s) :
    is'.all (okD f.module) = true := by
  cases h with
  | @callAddr a vs fi fn hf hcode hk =>
    obtain ⟨fn', hc', hb⟩ := hs a fi hf
    rw [hcode] at hc'
    cases hc'
    simpa using hb
  | _ => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, List.all_append]

/-- **Every V2 step from covered code over a `StoreOkD` store keeps the code covered, the
store's functions, whole pages and the frame's module.** -/
theorem okF_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : c.code.all (okD c.frame.module) = true)
    (hs : StoreOkD c.store) : KeepsD c c' := by
  induction h with
  | pure hp => exact keepsD_same (okD_pureStep hp hok) rfl
  | read hr => exact keepsD_same (okF_readStep hr hok hs) rfl
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

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
