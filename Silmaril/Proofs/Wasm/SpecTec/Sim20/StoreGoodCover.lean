module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodTyp

/-!
# A cover lemma that admits stores, and what a step keeps

* `BaseS P`: the base steps of the storing fragment. A step 's fragment
  (`Whole.FwdStep20D`) whose redex window is store-free (`adminOk`), a step of the second pure
  fragment (`Whole.PureFwd20B`, whose `br`, `return` and `trap-vals` tails may now hold stores),
  or one of V2's six scalar store steps (`Whole.StoreTop20`).
* **`cover20CS`**: every V2 step from plain-tail code (`Whole.Tail20`) that is `adminOkS`, over a
  store all of whose functions are covered Wasm functions (`Whole.StoreOk`), is a step of
  `Nest20 (BaseS P)`. It follows `Whole.cover20C`: a redex window with a store is either a store
  step or a concatenation rule whose tail holds it; every other window is store-free.
* **`adminOkS_step`**: such a step keeps the code `adminOkS`, keeps the functions of the store,
  and keeps whole pages (a store writes inside the memory and does not resize it,
  `writeBytes?_size`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreGood

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk adminOk Nest20 FwdStep20D PureFwd20B PureFrag20
  PureFrag20B StoreTop20 StoreOk Tail20 WholePages)

variable {H : Type}

/-! ## The base -/

/-- **The base steps of the storing fragment.** -/
inductive BaseS (P : Profile) : Config H → Config H → Prop where
  | old {c c' : Config H} (h : FwdStep20D P c c') (hok : c.code.all adminOk = true) :
      BaseS P c c'
  | pureB {c c' : Config H} (h : PureFwd20B P c c') : BaseS P c c'
  | store {c c' : Config H} (h : StoreTop20 c c') : BaseS P c c'

/-- Every base step is a V2 step. -/
theorem BaseS.step {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseS P c c') :
    Step P host c c' := by
  cases h with
  | old h _ => exact h.step
  | pureB h =>
    cases h with
    | mk h => exact .pure h.pureStep
  | store h => exact h.step

/-! ## Store-free windows -/

/-- A plain administrative instruction that is not a store is covered when it is covered with
stores. -/
theorem ctrlOk_of_adminOkS {i : V2.Instr} (h : adminOkS (.plain i) = true)
    (hs : storeOkI i = false) : ctrlOk i = true := by
  simpa [hs] using h

/-- The windows 's first pure fragment are store-free. -/
theorem adminOk_of_pureFrag20 {P : Profile} {is is' : List Admin} (h : PureFrag20 P is is')
    (hok : is.all adminOkS = true) : is.all adminOk = true := by
  cases h <;> simp_all [Whole.ctrlOk, storeOkI]

/-- The windows of the read steps are store-free. -/
theorem adminOk_of_readStep {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all adminOkS = true) : is.all adminOk = true := by
  cases h <;> simp_all [Whole.ctrlOk, storeOkI, List.all_append]

/-- `PureRest20N` has an instruction that is neither covered nor a store. -/
theorem not_pureRest20N_okS {is : List Admin} (h : Whole.PureRest20N is)
    (hok : is.all adminOkS = true) : False := by
  cases h with
  | @vec is i hm hv =>
    have hi : adminOkS (.plain i) = true := List.all_eq_true.1 hok _ hm
    have hs : storeOkI i = false := by
      cases i <;> simp_all [storeOkI, vecOp20]
    have hc := Whole.ctrlOk_of_vecOp hv
    simp [hs, hc] at hi
  | unOpInvalid h => simp_all [Whole.ctrlOk, storeOkI]
  | cvtUndefined h => simp_all [Whole.ctrlOk, storeOkI]

/-! ## The cover lemma -/

theorem okS_ctx_inner {vs : List Val} {is rest : List Admin}
    (h : (vals vs ++ is ++ rest).all adminOkS = true) : is.all adminOkS = true := by
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.1.2

theorem bodyOk_label {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h : [Admin.label n cont body].all adminOkS = true) : body.all adminOkS = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, adminOkS_label, Bool.and_eq_true] at h
  exact h.2

theorem bodyOk_frame {n : Nat} {fr : Frame} {body : List Admin}
    (h : [Admin.frame n fr body].all adminOkS = true) : body.all adminOkS = true := by
  simpa using h

/-- The pure steps. -/
theorem cover20CS_pure {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hp : PureStep P is is') (ht : Tail20 s f is) (hok : is.all adminOkS = true) :
    BaseS P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  by_cases ha : is.all adminOk = true
  · exact .old (Whole.cover20C_pure hp ht ha) ha
  · rcases Whole.pureStep_cover_tail hp ht with h | h | h
    · exact absurd (adminOk_of_pureFrag20 h hok) ha
    · exact .pureB (.mk h)
    · exact (not_pureRest20N_okS h hok).elim

/-- **Every V2 step from plain-tail code that is covered with stores, over a covered store, is in
the nested storing fragment.** -/
theorem cover20CS {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (ht : Tail20 c.store c.frame c.code) (hok : c.code.all adminOkS = true)
    (hs : StoreOk c.store) : Nest20 (BaseS P) c c' := by
  induction h with
  | pure hp => exact .base (cover20CS_pure hp ht hok)
  | read hr =>
    exact .base (.old (Whole.cover20C_read hr (adminOk_of_readStep hr hok))
      (adminOk_of_readStep hr hok))
  | ctxtInstrs hstep hne ih =>
    exact .ctx (ih (Whole.tail20_ctx hstep.not_allVals ht) (okS_ctx_inner hok) hs) hne
  | ctxtLabel _ ih => exact .label (ih (Whole.tail20_label ht).tail (bodyOk_label hok) hs)
  | ctxtFrame _ ih => exact .frame (ih (Whole.tail20_frame ht).tail (bodyOk_frame hok) hs)
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet hx => exact .base (.old (Whole.fwdC_top (.var (.localSet hx))) (by simp [ctrlOk]))
  | globalSet ha hg => exact .base (.old (Whole.fwdC_top (.var (.globalSet ha hg))) (by simp [ctrlOk]))
  | storeIntTrap ha hm h => exact .base (.store (.intTrap ha hm h))
  | storeIntVal ha hm hw => exact .base (.store (.intVal ha hm hw))
  | storeFloatTrap ha hm h => exact .base (.store (.floatTrap ha hm h))
  | storeFloatVal ha hm hw => exact .base (.store (.floatVal ha hm hw))
  | storePackTrap ha hm h => exact .base (.store (.packTrap ha hm h))
  | storePackVal ha hm hw => exact .base (.store (.packVal ha hm hw))
  | _ => exact absurd hok (by simp [ctrlOk, storeOkI])

/-! ## What a step keeps -/

/-- Copying a slice inside a byte array keeps its size. -/
theorem copySlice_size {bs m : ByteArray} {i : Nat} (h : i + bs.size ≤ m.size) :
    (bs.copySlice 0 m i bs.size).size = m.size := by
  rw [ByteArray.size] at h ⊢
  rw [ByteArray.size] at h
  show (m.data.extract 0 i ++ bs.data.extract 0 (0 + bs.data.size) ++
        m.data.extract (i + min bs.data.size (bs.data.size - 0))).size = m.data.size
  simp only [Array.size_append, Array.size_extract]
  omega

/-- Writing bytes inside a memory keeps its size. -/
theorem writeBytes?_size {mi mi' : MemInst} {i j : Nat} {bs : Silmaril.Wasm.Execution.Memory.Bytes}
    (h : mi.writeBytes? i j bs = some mi') : mi'.bytes.size = mi.bytes.size := by
  unfold MemInst.writeBytes? at h
  split at h
  · unfold Silmaril.Wasm.Execution.Memory.writeBytes at h
    split at h
    · rename_i hle
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact copySlice_size hle
    · simp at h
  · simp at h

/-- A store that writes inside a memory keeps whole pages. -/
theorem WholePages.setMemInst {s : Store H} {a : MemAddr} {mi mi' : MemInst}
    (hw : WholePages s) (hm : s.memInst? a = some mi) (hs : mi'.bytes.size = mi.bytes.size) :
    WholePages (s.setMemInst a mi') := by
  intro m hmem
  rcases List.mem_or_eq_of_mem_set hmem with h | rfl
  · exact hw m h
  · have hmi : s.mems[a]? = some mi := by simpa [Store.memInst?] using hm
    rw [hs]
    exact hw mi (List.mem_of_getElem? hmi)

/-- What a step from covered code with stores keeps. -/
def KeepsS (c c' : Config H) : Prop :=
  c'.code.all adminOkS = true ∧ c'.store.funcs = c.store.funcs ∧
    (WholePages c.store → WholePages c'.store)

theorem keepsS_same {s : Store H} {f f' : Frame} {is is' : List Admin}
    (h : is'.all adminOkS = true) : KeepsS ⟨s, f, is⟩ ⟨s, f', is'⟩ := ⟨h, rfl, id⟩

/-- **Every pure step keeps covered code with stores covered.** -/
theorem adminOkS_pureStep {P : Profile} {is is' : List Admin} (h : PureStep P is is')
    (hok : is.all adminOkS = true) : is'.all adminOkS = true := by
  cases h <;> simp_all [Whole.ctrlOk, storeOkI, List.all_append]

/-- The six store steps keep the functions and whole pages, and end in `trap` or nothing. -/
theorem keepsS_storeTop {c c' : Config H} (h : StoreTop20 c c') : KeepsS c c' := by
  cases h with
  | intTrap _ _ _ | floatTrap _ _ _ | packTrap _ _ _ => exact keepsS_same rfl
  | intVal _ hm hw | floatVal _ hm hw | packVal _ hm hw =>
    exact ⟨rfl, rfl, fun hp => WholePages.setMemInst hp hm (writeBytes?_size hw)⟩

theorem keepsS_ctx {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hok : (vals vs ++ is ++ rest).all adminOkS = true)
    (ih : is.all adminOkS = true → KeepsS ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    KeepsS ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  simp only [List.all_append, Bool.and_eq_true] at hok
  obtain ⟨hi, hm, hw⟩ := ih hok.1.2
  exact ⟨by simp [List.all_append, hi, hok.2], hm, hw⟩

/-- **Every V2 step from covered code with stores, over a covered store, keeps the code covered
with stores, the functions of the store, and whole pages.** -/
theorem adminOkS_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : c.code.all adminOkS = true) (hs : StoreOk c.store) :
    KeepsS c c' := by
  induction h with
  | pure hp => exact keepsS_same (adminOkS_pureStep hp hok)
  | read hr =>
    exact keepsS_same (all_adminOkS_of_adminOk
      (Whole.adminOk_readStep hr (adminOk_of_readStep hr hok) hs))
  | ctxtInstrs _ _ ih => exact keepsS_ctx hok fun hi => ih hi hs
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    have hb : cont.all ctrlOk = true ∧ is.all adminOkS = true := by simpa using hok
    obtain ⟨hi, hm, hw⟩ := ih hb.2 hs
    exact ⟨by simp [hb.1, hi], hm, hw⟩
  | ctxtFrame _ ih =>
    obtain ⟨hi, hm, hw⟩ := ih (by simpa using hok) hs
    exact ⟨by simp [hi], hm, hw⟩
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet => exact keepsS_same rfl
  | globalSet => exact ⟨rfl, rfl, fun hp => hp⟩
  | storeIntTrap ha hm h => exact keepsS_storeTop (.intTrap ha hm h)
  | storeIntVal ha hm hw => exact keepsS_storeTop (.intVal ha hm hw)
  | storeFloatTrap ha hm h => exact keepsS_storeTop (.floatTrap ha hm h)
  | storeFloatVal ha hm hw => exact keepsS_storeTop (.floatVal ha hm hw)
  | storePackTrap ha hm h => exact keepsS_storeTop (.packTrap ha hm h)
  | storePackVal ha hm hw => exact keepsS_storeTop (.packVal ha hm hw)
  | _ => simp_all [ctrlOk, storeOkI]

/-- `StoreOk` reads only the functions of the store. -/
theorem storeOk_of_funcs {s s' : Store H} (h : StoreOk s) (e : s'.funcs = s.funcs) : StoreOk s' := by
  intro a fi hf
  exact h a fi (by simpa [Store.funcInst?, e] using hf)

end Silmaril.Wasm.SpecTec.Sim20.StoreGood
