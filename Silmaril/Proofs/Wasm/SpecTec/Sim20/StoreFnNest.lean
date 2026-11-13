module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnBase

/-!
# Stores inside the store's functions, forward in `simEnv20T`, nested under every context

The typing part is `TypF`: the state with its function bodies **deeply erased** (`eraseS`) is
typed in `simEnv20`, and so is the deeply erased code. Over a `StoreOkD` store the state itself
is typed in `simEnv20T` (`typedT_state_of_erased`), and the code too (`typedT_of_eDL`).

* Subject reduction: the erased successor is typed in `simEnv20` 's lemmas. The reads
  leave the state alone and produce a value, a trap, a constant or `CALL_ADDR`; `call_addr`
  reads the erased function (`eraseS_funcInst`) and round 3's `typed20_succ_callAddr20` types
  its erased body; `local.set`, `global.set` and the stores update the frame, a global or a
  memory, which erasure commutes with.
* The forward derivation: every state-reading rule is fired in `simEnv20T` from the state typed
  there (`StoreFn.firesT_*`); the pure fragments and `block`/`loop` as in `StoreDeep`.

**`fwd_nestF`**: every `Nest20 (BaseF P)` step from a configuration with `TypF`, `okD` code,
whole pages and a `StoreOkD` store is a step of `simEnv20T (storeB P)` between the images, and
the successor has `TypF`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV SPure stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T sstepB20T_iff)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Nest20 PureFwd20B PureFrag20 StoreTop20 WholePages BlockFwd20
  ReadFwd20 CallFwd20 CallAddrFwd20 LoadFwd20 CallIndFwd20 CallIndTrapFwd20 storeB typed20_iff
  typedV_admins_val20 typedV_admins_trap20 typedV_admins_nil20 typedV_admins_const20
  typedV_admins_callAddr20 mem?_some loadNumV_int loadNumV_float storeNumV_int storeNumV_float)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (SizeFwd20 TableGetFwd20)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (LoadPackFwd20)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eD eDA okD ctrlOkD typedT_of_eDL typedT_instrs_of_eD
  okD_ctx_inner okD_label_parts okD_frame_body)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The typing invariant -/

/-- **The typing part of the invariant**: the state with its function bodies erased, and the
erased code, typed in `simEnv20`. -/
structure TypF (B : Builtins) (hn : H → String) (c : Config H) : Prop where
  state : TypedV (E20 B) stateT (stateV hn (eraseS c.store) c.frame)
  code : TypedV (E20 B) adminsTy (.list (adminsToV (c.code.map eDA)))

theorem TypF.stateT {c : Config H} (h : TypF B hn c) (hs : StoreOkD c.store) :
    TypedV (simEnv20T B) stateT (stateV hn c.store c.frame) :=
  typedT_state_of_erased hs h.state

theorem TypF.codeT {m : ModuleInst} {c : Config H} (h : TypF B hn c)
    (hok : c.code.all (okD m) = true) : TypedV (simEnv20T B) adminsTy (.list (adminsToV c.code)) :=
  typedT_of_eDL hok h.code

/-- The erased configuration is typed in `simEnv20`. -/
theorem TypF.erased {c : Config H} (h : TypF B hn c) :
    Typed20 (E20 B) hn ⟨eraseS c.store, c.frame, c.code.map eDA⟩ :=
  typed20_iff.2 ⟨h.state, h.code⟩

/-- `TypD` is `TypF` over a `StoreOkM` store. -/
theorem typF_of_typD {c : Config H} (h : StoreDeep.TypD B hn c) (hs : GoodMerge.StoreOkM c.store) :
    TypF B hn c := ⟨by rw [eraseS_of_storeOkM hs]; exact h.state, h.code⟩

@[simp] theorem eDA_toAdmin (v : Val) : eDA v.toAdmin = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> rfl

@[simp] theorem eDA_constI32 (n : BitVec 32) : eDA (constI32 n) = constI32 n := rfl

theorem eraseS_setMem (s : Store H) (a : MemAddr) (mi : MemInst) :
    eraseS (s.setMemInst a mi) = (eraseS s).setMemInst a mi := rfl

theorem eraseS_setGlobal (s : Store H) (a : GlobalAddr) (gi : GlobalInst) :
    eraseS (s.setGlobalInst a gi) = (eraseS s).setGlobalInst a gi := rfl

/-! ## The read rules -/

/-- A `Step_read` firing of `simEnv20T` from a configuration with `TypF`, the state unchanged and
the erased successor code typed. -/
theorem fwdF_of_fires {s : Store H} {f : Frame} {is is' : List Admin} {k : Nat}
    (ht : TypF B hn ⟨s, f, is⟩) (hs : StoreOkD s) (hok : is.all (okD f.module) = true)
    (hok' : is'.all (okD f.module) = true)
    (hc' : TypedV (E20 B) adminsTy (.list (adminsToV (is'.map eDA))))
    (hf : Sim.Fires (simEnv20T B) "Step_read" k
      (.tuple [configV hn ⟨s, f, is⟩, .list (adminsToV is')])) :
    TypF B hn ⟨s, f, is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) := by
  have ht' : TypF B hn ⟨s, f, is'⟩ := ⟨ht.state, hc'⟩
  exact ⟨ht', sstepT_read (ht.stateT hs) (ht.codeT hok) (ht'.codeT hok') hf⟩

/-- A one-value result, erased and typed. -/
theorem typedE_val (v : Val) : TypedV (E20 B) adminsTy (.list (adminsToV ([v.toAdmin].map eDA))) := by
  simpa using typedV_admins_val20 (B := B) v

theorem typedE_trap : TypedV (E20 B) adminsTy (.list (adminsToV ([Admin.trap].map eDA))) := by
  simpa using typedV_admins_trap20 (B := B)

theorem typedE_callAddr (a : FuncAddr) :
    TypedV (E20 B) adminsTy (.list (adminsToV ([Admin.callAddr a].map eDA))) := by
  simpa using typedV_admins_callAddr20 (B := B) a

theorem typedE_const (n : BitVec 32) :
    TypedV (E20 B) adminsTy (.list (adminsToV ([constI32 n].map eDA))) := by
  show TypedV _ _ (.list (adminsToV [eDA (constI32 n)]))
  rw [eDA_constI32]
  exact typedV_admins_const20 (B := B) n

/-- **`call_addr`, forward**: the erased callee body is typed . -/
theorem fwdF_callAddr {c c' : Config H} (h : CallAddrFwd20 c c') (ht : TypF B hn c)
    (hs : StoreOkD c.store) (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF B hn c' ∧ SStepB (simEnv20T B) (configV hn c) (configV hn c') := by
  cases h with
  | @mk s f a vs fi fn hf hcode hk =>
    have hc : Typed20 (E20 B) hn ⟨eraseS s, f, vals vs ++ [.callAddr a]⟩ :=
      typed20_iff.2 ⟨ht.state, by simpa using ht.code⟩
    have hT := Whole.typed20_succ_callAddr20 hc (.mk (eraseS_funcInst hf) (eraseFI_code hcode) hk)
    exact fwdF_of_fires ht hs hok hok' (by simpa using (typed20_iff.1 hT).2)
      (firesT_callAddr (ht.stateT hs) hf hcode hk)

/-- **`block` and `loop`, forward.** -/
theorem fwdF_block {c c' : Config H} (h : BlockFwd20 c c') (ht : TypF B hn c)
    (hs : StoreOkD c.store) (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF B hn c' ∧ SStepB (simEnv20T B) (configV hn c) (configV hn c') := by
  cases h with
  | @block s f bt body vs ft hbt hk =>
    have hT := Whole.typed20_succ_block20 ht.erased (StoreDeep.erase_block (.block hbt hk))
    exact fwdF_of_fires ht hs hok hok' (typed20_iff.1 hT).2
      (StoreDeep.firesT_block (ht.stateT hs) (StoreDeep.blockTD (.inl rfl) hok ht.code) hbt hk)
  | @loop s f bt body vs ft hbt hk =>
    have hT := Whole.typed20_succ_block20 ht.erased (StoreDeep.erase_block (.loop hbt hk))
    exact fwdF_of_fires ht hs hok hok' (typed20_iff.1 hT).2
      (StoreDeep.firesT_loop (ht.stateT hs) (StoreDeep.blockTD (.inr rfl) hok ht.code) hbt hk)

/-- `local.get`, `global.get`, `ref.func`, forward. -/
theorem fwdF_var {P : Profile} {c c' : Config H} (h : ReadFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkD c.store)
    (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | localGet hv => exact fwdF_of_fires ht hs hok hok' (typedE_val _) (firesT_localGet hv (ht.stateT hs))
  | globalGet ha hg =>
    exact fwdF_of_fires ht hs hok hok' (typedE_val _) (firesT_globalGet ha hg (ht.stateT hs))
  | refFunc ha =>
    exact fwdF_of_fires ht hs hok hok' (typedE_val (.ref (.funcAddr _)))
      (firesT_refFunc ha (ht.stateT hs))

/-- `call`, forward. -/
theorem fwdF_call {P : Profile} {c c' : Config H} (h : CallFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkD c.store)
    (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | call ha => exact fwdF_of_fires ht hs hok hok' (typedE_callAddr _) (firesT_call ha (ht.stateT hs))

/-- The unpacked loads, forward. -/
theorem fwdF_load {P : Profile} {c c' : Config H} (h : LoadFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkD c.store)
    (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hz := ht.stateT hs
  cases h with
  | intTrap hm hlt =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdF_of_fires ht hs hok hok' typedE_trap
      (firesT_loadNumTrap (loadNumV_int _ _) hz ha hm' hlt)
  | @intVal s f t ao i mi c hm hb =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdF_of_fires ht hs hok hok' (typedE_val (.num ⟨.int t, c⟩))
      (firesT_loadNumVal (Whole.nbytes20_storeB P) (loadNumV_int _ _) hz ha hm' hb)
  | floatTrap hm hlt =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdF_of_fires ht hs hok hok' typedE_trap
      (firesT_loadNumTrap (loadNumV_float _ _) hz ha hm' hlt)
  | @floatVal s f t ao i mi c hm hb =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdF_of_fires ht hs hok hok' (typedE_val (.num ⟨.float t, c⟩))
      (firesT_loadNumVal (Whole.nbytes20_storeB P) (loadNumV_float _ _) hz ha hm' hb)

/-- The packed loads, forward. -/
theorem fwdF_pack {P : Profile} {c c' : Config H} (h : LoadPackFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkD c.store)
    (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap hm hlt =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdF_of_fires ht hs hok hok' typedE_trap (firesT_loadPackTrap (ht.stateT hs) ha hm' hlt)
  | @val s f t sz sx ao i mi c hm hb =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdF_of_fires ht hs hok hok' (typedE_val (.num ⟨.int t, GoodMerge.extPack20 t sx c⟩))
      (firesT_loadPackVal (Whole.floatB_storeB P) (Whole.laneCalls20_storeB P) (ht.stateT hs)
        ha hm' hb)

/-- `table.size`, `memory.size`, forward. -/
theorem fwdF_size {P : Profile} {c c' : Config H} (h : SizeFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkD c.store)
    (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | table ht' hn' =>
    exact fwdF_of_fires ht hs hok hok' (typedE_const _) (firesT_tableSize (ht.stateT hs) ht' hn')
  | memory hm hn' =>
    exact fwdF_of_fires ht hs hok hok' (typedE_const _) (firesT_memorySize (ht.stateT hs) hm hn')

/-- `table.get`, forward. -/
theorem fwdF_tget {P : Profile} {c c' : Config H} (h : TableGetFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkD c.store)
    (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap ht' hge =>
    exact fwdF_of_fires ht hs hok hok' typedE_trap (firesT_tableGetTrap (ht.stateT hs) ht' hge)
  | @val s f x i ti r ht' hr =>
    exact fwdF_of_fires ht hs hok hok' (typedE_val (.ref r)) (firesT_tableGetVal (ht.stateT hs) ht' hr)

/-- `call_indirect`, both rules, forward. -/
theorem fwdF_callInd {P : Profile} {c c' : Config H} (h : CallIndFwd20 c c' ∨ CallIndTrapFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkD c.store)
    (hok : c.code.all (okD c.frame.module) = true)
    (hok' : c'.code.all (okD c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  rcases h with h | h
  · cases h with
    | mk ht' hr hf hy =>
      exact fwdF_of_fires ht hs hok hok' (typedE_callAddr _)
        (firesT_callIndirectCall (ht.stateT hs) ht' hr hf hy)
  · cases h with
    | mk ht' hft h =>
      exact fwdF_of_fires ht hs hok hok' typedE_trap
        (firesT_callIndirectTrap (ht.stateT hs) ht' hft h)

/-! ## The writes -/

/-- **`local.set`, `global.set` and the six stores, forward.** -/
theorem fwdF_local {P : Profile} {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hx : x.toNat < f.locals.length) (ht : TypF (storeB P) hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩)
    (hs : StoreOkD s) :
    TypF (storeB P) hn ⟨s, f.setLocal x v, []⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩)
        (configV hn ⟨s, f.setLocal x v, []⟩) := by
  obtain ⟨hst, hfr⟩ := Whole.typedV_stateV_iff.1 ht.state
  exact ⟨⟨Whole.typedV_stateV_iff.2 ⟨hst, Whole.typedV_frameV_setLocal hfr x v⟩,
    by simpa using typedV_admins_nil20⟩, sstepT_of_firesStep (firesT_localSet (ht.stateT hs) hx)⟩

theorem fwdF_global {P : Profile} {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val}
    {a : GlobalAddr} {gi : GlobalInst} (ha : f.module.globalAddr? x = some a)
    (hg : s.globalInst? a = some gi)
    (ht : TypF (storeB P) hn ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩) (hs : StoreOkD s) :
    TypF (storeB P) hn ⟨s.setGlobalInst a { gi with value := v }, f, []⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩)
        (configV hn ⟨s.setGlobalInst a { gi with value := v }, f, []⟩) := by
  have ha' : f.module.globals[x.toNat]? = some a := by simpa [ModuleInst.globalAddr?] using ha
  have hg' : s.globals[a]? = some gi := by simpa [Store.globalInst?] using hg
  obtain ⟨hst, hfr⟩ := Whole.typedV_stateV_iff.1 ht.state
  have S := Whole.typedV_storeV_iff.1 hst
  have hgi := Whole.typedV_globalInstV_value (Whole.typedV_of_getElem? S.globals
    (show (eraseS s).globals[a]? = some gi from hg')) v
  refine ⟨⟨?_, by simpa using typedV_admins_nil20⟩,
    sstepT_of_firesStep (firesT_globalSet (ht.stateT hs) ha' hg')⟩
  rw [eraseS_setGlobal]
  exact Whole.typedV_stateV_iff.2 ⟨Whole.typedV_storeV_iff.2 (Whole.storeTy20_setGlobal S a hgi), hfr⟩

theorem fwdF_store {P : Profile} {c c' : Config H} (h : StoreTop20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkD c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hz := ht.stateT hs
  obtain ⟨hst, hfr⟩ := Whole.typedV_stateV_iff.1 ht.state
  have S := Whole.typedV_storeV_iff.1 hst
  have hmem : ∀ (a : MemAddr) (mi : MemInst), TypedV (E20 (storeB P)) stateT
      (stateV hn (eraseS (c.store.setMemInst a mi)) c.frame) := fun a mi => by
    rw [eraseS_setMem]
    exact Whole.typedV_stateV_iff.2 ⟨Whole.typedV_storeV_iff.2 (Whole.storeTy20_setMem S a mi), hfr⟩
  have htrap : TypedV (E20 (storeB P)) adminsTy (.list (adminsToV ([Admin.trap].map eDA))) :=
    typedE_trap
  have hnil : TypedV (E20 (storeB P)) adminsTy (.list (adminsToV (([] : List Admin).map eDA))) := by
    simpa using typedV_admins_nil20
  cases h with
  | intTrap ha hm h =>
    exact ⟨⟨ht.state, htrap⟩, sstepT_of_firesStep
      (firesT_storeNumTrap (storeNumV_int _ _) hz ha hm h)⟩
  | intVal ha hm hw =>
    exact ⟨⟨hmem _ _, hnil⟩, sstepT_of_firesStep
      (firesT_storeNumVal (Whole.nbytes20_storeB P) (storeNumV_int _ _) hz ha hm hw)⟩
  | floatTrap ha hm h =>
    exact ⟨⟨ht.state, htrap⟩, sstepT_of_firesStep
      (firesT_storeNumTrap (storeNumV_float _ _) hz ha hm h)⟩
  | floatVal ha hm hw =>
    exact ⟨⟨hmem _ _, hnil⟩, sstepT_of_firesStep
      (firesT_storeNumVal (Whole.nbytes20_storeB P) (storeNumV_float _ _) hz ha hm hw)⟩
  | packTrap ha hm h =>
    exact ⟨⟨ht.state, htrap⟩, sstepT_of_firesStep (firesT_storePackTrap hz ha hm h)⟩
  | packVal ha hm hw =>
    exact ⟨⟨hmem _ _, hnil⟩, sstepT_of_firesStep
      (firesT_storePackVal (Whole.floatB_storeB P) (Whole.laneCalls20_storeB P) hz ha hm hw)⟩

/-! ## The pure fragments -/

theorem fwdF_pureA {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : PureFrag20 P is is') (hok : is.all (okD f.module) = true)
    (ht : TypF (storeB P) hn ⟨s, f, is⟩) (hs : StoreOkD s) :
    TypF (storeB P) hn ⟨s, f, is'⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) := by
  have ht' : TypF (storeB P) hn ⟨s, f, is'⟩ :=
    ⟨ht.state, Whole.typedV_succ_pureFrag20 ht.code (StoreDeep.erase_pureFrag20D h hok)⟩
  have hok' : is'.all (okD f.module) = true := StoreDeep.okD_pureStep h.pureStep hok
  have A := Pure.numAgree_simEnv20 (Whole.intB_storeB P) (Whole.floatB_storeB P)
  refine ⟨ht', (sstepB20T_iff _).2 ?_⟩
  exact StoreRun.sstepT_pure (ht.stateT hs) (ht.codeT hok) (ht'.codeT hok')
    (StoreDeep.spureT_of_pureFrag20D A h hok ht.code)

theorem fwdF_pureB {P : Profile} {c c' : Config H} (h : PureFwd20B P c c')
    (hok : c.code.all (okD c.frame.module) = true) (ht : TypF (storeB P) hn c)
    (hs : StoreOkD c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | @mk s f is is' h =>
    have ht' : TypF (storeB P) hn ⟨s, f, is'⟩ :=
      ⟨ht.state, Whole.typedV_succ_pureFrag20B ht.code (StoreDeep.erase_pureFrag20BD h hok)⟩
    have hok' : is'.all (okD f.module) = true := StoreDeep.okD_pureStep h.pureStep hok
    refine ⟨ht', (sstepB20T_iff _).2 ?_⟩
    exact StoreRun.sstepT_pure (ht.stateT hs) (ht.codeT hok) (ht'.codeT hok')
      (StoreDeep.spureT_of_pureFrag20BD (Pure.cvtAgree_simEnv20 (Whole.floatB_storeB P)) h hok
        ht.code)

/-! ## One base step -/

/-- **One base step, forward.** -/
theorem fwdF_base {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseF P c c')
    (ht : TypF (storeB P) hn c) (hok : c.code.all (okD c.frame.module) = true)
    (hs : StoreOkD c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hok' := (okF_step (host := host) h.step hok hs).1
  cases h with
  | pureA h => exact fwdF_pureA h hok ht hs
  | pureB h => exact fwdF_pureB h hok ht hs
  | block h => exact fwdF_block h ht hs hok hok'
  | read h => exact fwdF_var h ht hs hok hok'
  | call h => exact fwdF_call h ht hs hok hok'
  | callAddr h => exact fwdF_callAddr h ht hs hok hok'
  | load h => exact fwdF_load h ht hs hok hok'
  | pack h => exact fwdF_pack h ht hs hok hok'
  | size h => exact fwdF_size h ht hs hok hok'
  | tget h => exact fwdF_tget h ht hs hok hok'
  | callInd h => exact fwdF_callInd (.inl h) ht hs hok hok'
  | callIndTrap h => exact fwdF_callInd (.inr h) ht hs hok hok'
  | localSet hx => exact fwdF_local hx ht hs
  | globalSet ha hg => exact fwdF_global ha hg ht hs
  | store h => exact fwdF_store h ht hs

/-! ## The three contexts -/

/-- `ctxt-instrs`. -/
theorem fwdF_ctx {m m' : ModuleInst} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ []) (hs : StoreOkD s) (hs' : StoreOkD s')
    (ht : TypF B hn ⟨s, f, vals vs ++ is ++ rest⟩)
    (hok : (vals vs ++ is ++ rest).all (okD m) = true) (hok' : is'.all (okD m') = true)
    (ih : TypF B hn ⟨s, f, is⟩ → TypF B hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypF B hn ⟨s', f', vals vs ++ is' ++ rest⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, vals vs ++ is ++ rest⟩)
        (configV hn ⟨s', f', vals vs ++ is' ++ rest⟩) := by
  simp only [List.all_append, Bool.and_eq_true] at hok
  have hcode := ht.code
  simp only [List.map_append, StoreDeep.map_eDA_vals] at hcode
  obtain ⟨hvi, hrest⟩ := Whole.typedV_admins_append20_iff.1 hcode
  obtain ⟨hvals, his⟩ := Whole.typedV_admins_append20_iff.1 hvi
  have hin : TypF B hn ⟨s, f, is⟩ := ⟨ht.state, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  refine ⟨⟨ht'.state, ?_⟩, ?_⟩
  · simp only [List.map_append, StoreDeep.map_eDA_vals]
    exact Whole.typedV_admins_append20_iff.2
      ⟨Whole.typedV_admins_append20_iff.2 ⟨hvals, ht'.code⟩, hrest⟩
  · have hst' := StoreFix.sstepT_ctxtInstrs (hin.stateT hs) (ht'.stateT hs')
      (StoreGood.typedV_valsTy20T vs) (hin.codeT hok.1.2) (ht'.codeT hok')
      (typedT_of_eDL hok.2 hrest) (by simpa [Pure.adminsToV_eq_map, vals] using hne)
      ((sstepB20T_iff B).1 hst)
    refine (sstepB20T_iff B).2 ?_
    simpa only [configV, Pure.adminsToV_append] using hst'

/-- `ctxt-label`. -/
theorem fwdF_label {m m' : ModuleInst} {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List V2.Instr} {is is' : List Admin} (hs : StoreOkD s) (hs' : StoreOkD s')
    (ht : TypF B hn ⟨s, f, [.label n cont is]⟩) (hcok : cont.all (ctrlOkD m) = true)
    (hok : is.all (okD m) = true) (hok' : is'.all (okD m') = true)
    (ih : TypF B hn ⟨s, f, is⟩ → TypF B hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypF B hn ⟨s', f', [.label n cont is']⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, [.label n cont is]⟩)
        (configV hn ⟨s', f', [.label n cont is']⟩) := by
  have hcode := ht.code
  simp only [List.map_cons, List.map_nil, StoreDeep.eDA_label] at hcode
  obtain ⟨hn', hcont, his⟩ := Whole.label_all20 hcode
  have hin : TypF B hn ⟨s, f, is⟩ := ⟨ht.state, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  refine ⟨⟨ht'.state, ?_⟩, ?_⟩
  · simp only [List.map_cons, List.map_nil, StoreDeep.eDA_label]
    exact Whole.typedV_admins_single20_iff.2 (Whole.typedV_adminLabel20_iff.2 ⟨hn', hcont, ht'.code⟩)
  · have hst' := StoreRun.sstepT_ctxtLabel (hin.stateT hs) (ht'.stateT hs')
      (StoreGood.typedV_nT20T hn') (typedT_instrs_of_eD hcok hcont) (hin.codeT hok)
      (ht'.codeT hok') ((sstepB20T_iff B).1 hst)
    exact (sstepB20T_iff B).2 (by simpa only [configV, adminsToV, adminToV] using hst')

/-- `ctxt-frame`. -/
theorem fwdF_frame {m m' : ModuleInst} {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (hs : StoreOkD s) (hs' : StoreOkD s')
    (ht : TypF B hn ⟨s, f, [.frame n fi is]⟩)
    (hok : is.all (okD m) = true) (hok' : is'.all (okD m') = true)
    (ih : TypF B hn ⟨s, fi, is⟩ → TypF B hn ⟨s', fi', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, fi, is⟩) (configV hn ⟨s', fi', is'⟩)) :
    TypF B hn ⟨s', f, [.frame n fi' is']⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, [.frame n fi is]⟩)
        (configV hn ⟨s', f, [.frame n fi' is']⟩) := by
  have hcode := ht.code
  simp only [List.map_cons, List.map_nil, StoreDeep.eDA_frame] at hcode
  obtain ⟨hn', hfi, his⟩ := Whole.frame_all20 hcode
  obtain ⟨hst, hf⟩ := Whole.typedV_stateV_iff.1 ht.state
  have hin : TypF B hn ⟨s, fi, is⟩ := ⟨Whole.typedV_stateV_iff.2 ⟨hst, hfi⟩, his⟩
  obtain ⟨ht', hstep⟩ := ih hin
  obtain ⟨hst', hfi'⟩ := Whole.typedV_stateV_iff.1 ht'.state
  refine ⟨⟨Whole.typedV_stateV_iff.2 ⟨hst', hf⟩, ?_⟩, ?_⟩
  · simp only [List.map_cons, List.map_nil, StoreDeep.eDA_frame]
    exact Whole.typedV_admins_single20_iff.2 (Whole.typedV_adminFrame20_iff.2 ⟨hn', hfi', ht'.code⟩)
  · have hsT := (typedT_stateV_iff.1 (hin.stateT hs)).1
    have hsT' := (typedT_stateV_iff.1 (ht'.stateT hs')).1
    have hst'' := StoreRun.sstepT_ctxtFrame hsT hsT' (StoreAgree.typedV_to20T (by decide) hf)
      (StoreAgree.typedV_to20T (by decide) hfi) (StoreAgree.typedV_to20T (by decide) hfi')
      (StoreGood.typedV_nT20T hn') (hin.codeT hok) (ht'.codeT hok') ((sstepB20T_iff B).1 hstep)
    exact (sstepB20T_iff B).2 (by simpa only [configV, stateV, adminsToV, adminToV] using hst'')

/-! ## The forward theorem -/

/-- **Stores inside the store's functions, forward**: every `Nest20 (BaseF P)` step from a
configuration with `TypF`, covered code and a `StoreOkD` store is a step of
`simEnv20T (storeB P)` between the images, and the successor has `TypF`. -/
theorem fwd_nestF {P : Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Nest20 (BaseF P) c c') (ht : TypF (storeB P) hn c)
    (hok : c.code.all (okD c.frame.module) = true) (hs : StoreOkD c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  induction h with
  | base h => exact fwdF_base (host := host) h ht hok hs
  | ctx hin hne ih =>
    have hok₁ : (vals _ ++ _ ++ _).all (okD _) = true := hok
    have hi := okD_ctx_inner hok
    have hk := okF_step (host := host) (hin.step fun _ _ h => h.step) hi hs
    exact fwdF_ctx hne hs (storeOkD_of_funcs hs hk.2.1) ht hok₁ hk.1
      fun hin' => ih hin' hi hs
  | label hin ih =>
    have hb := okD_label_parts hok
    have hk := okF_step (host := host) (hin.step fun _ _ h => h.step) hb.2 hs
    exact fwdF_label hs (storeOkD_of_funcs hs hk.2.1) ht hb.1 hb.2 hk.1
      fun hin' => ih hin' hb.2 hs
  | frame hin ih =>
    have hb := okD_frame_body hok
    have hk := okF_step (host := host) (hin.step fun _ _ h => h.step) hb hs
    exact fwdF_frame hs (storeOkD_of_funcs hs hk.2.1) ht hb hk.1 fun hin' => ih hin' hb hs

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
