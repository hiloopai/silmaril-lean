module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkBase
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkInit

/-!
# `memory.fill` and stores inside the store's functions, forward in `simEnv20T`

The typing part is round 5's `StoreFn.TypF` (the erased state and the erased code typed in
`simEnv20`), unchanged: the deep erasure keeps `memory.fill`. Over a `StoreOkB` store the state
is typed in `simEnv20T` (`typF_stateB`), and `okB` code too (`typF_codeB`).

* The pure fragments: an earlier `StoreDeep` lemmas restated for `okB` windows (a label
  continuation, an `if` branch or a frame body may now hold `memory.fill`): `erase_pureFragB`,
  `spureT_of_pureFragB`, `erase_pureFragBB`, `spureT_of_pureFragBB`.
* Every other base kind of `StoreFn.BaseF`: the state-reading rules fired in `simEnv20T` by
  round 5's `StoreFn.firesT_*`, from the state typed there.
* `memory.fill` (`fwdB_fill`): the three rules fired 's `StoreFn.firesT_memFill*`.
  Subject reduction: the state is unchanged, and the erased successor of `-succ`
  (`i32.const i; v; nop; i32.const (i + 1); v; i32.const (n - 1); memory.fill`) is typed in
  `simEnv20`. `-succ` needs `i + 1 < 2 ^ 32` (the script does not wrap, V2 does); it follows
  from `i + n ≤ |mem|`, `n ≠ 0` and `StoreSmall` (every memory below `2 ^ 32` bytes).

**`fwd_nestB`**: every `Nest20 (BaseB P)` step from a configuration with `TypF`, `okB` code, a
`StoreOkB` store and `StoreSmall` is a step of `simEnv20T (storeB P)` between the images, and the
successor has `TypF`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

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
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk Nest20 PureFwd20B PureFrag20 PureFrag20B StoreTop20
  BlockFwd20 ReadFwd20 CallFwd20 CallAddrFwd20 LoadFwd20 CallIndFwd20 CallIndTrapFwd20 storeB
  typed20_iff typedV_admins_nil20 mem?_some loadNumV_int loadNumV_float storeNumV_int
  storeNumV_float)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (storeOkI)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (ctrlOkI SizeFwd20 TableGetFwd20)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (ctrlOkM okA LoadPackFwd20)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (BlockTypedT eD eDA ctrlOkD okD map_eDA_of_okA_false frameTD
  spureT_labelVals spureT_trapLabel spureT_ifTrue spureT_ifFalse)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (TypF BaseF typedT_stateV_iff eraseS eraseS_funcInst eraseFI_code
  sstepT_read sstepT_of_firesStep typedE_val typedE_trap typedE_callAddr typedE_const
  eraseS_setMem eraseS_setGlobal firesT_localGet firesT_globalGet firesT_refFunc firesT_call
  firesT_callAddr firesT_loadNumTrap firesT_loadNumVal firesT_loadPackTrap firesT_loadPackVal
  firesT_tableSize firesT_memorySize firesT_tableGetTrap firesT_tableGetVal
  firesT_callIndirectCall firesT_callIndirectTrap firesT_localSet firesT_globalSet
  firesT_storeNumTrap firesT_storeNumVal firesT_storePackTrap firesT_storePackVal
  firesT_memFillTrap firesT_memFillZero firesT_memFillSucc)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## Pieces of an erased typed window -/

/-- The parts of a label: the arity and the continuation in `simEnv20T`, the erased body in
`simEnv20`. -/
theorem labelTB {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (hok : [Admin.label n cont body].all (okB m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ([Admin.label n cont body].map eDA)))) :
    TypedV (simEnv20T B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont)) ∧
      TypedV (E20 B) adminsTy (.list (adminsToV (body.map eDA))) := by
  have hc' : TypedV (E20 B) adminsTy
      (.list (adminsToV [Admin.label n (cont.map eD) (body.map eDA)])) := by
    simpa using hc
  obtain ⟨h₁, h₂, h₃⟩ := Whole.label_all20 hc'
  exact ⟨StoreGood.typedV_nT20T h₁, typedT_instrs_of_eB (okB_label_parts hok).1 h₂, h₃⟩

/-- The plain tail of a typed erased body, as an `instr*` of `simEnv20T`. -/
theorem tailTB {m : ModuleInst} {l : List Admin} {is : List V2.Instr}
    (hok : (l ++ expression is).all (okB m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ((l ++ expression is).map eDA)))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV (expression is))) := by
  have hT := typedT_of_eBL hok hc
  rw [Pure.adminsToV_append] at hT
  refine StoreGood.typedV_instrs_of_admins20T (Sim.typedV_list_iff.2 fun u hu => ?_)
  exact Sim.typedV_list_iff.1 hT u (List.mem_append_right _ hu)

/-! ## The first pure fragment -/

/-- **Erasure keeps a step of the first pure fragment**, with the erased successor. -/
theorem erase_pureFragB {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20 P is is') (hok : is.all (okB m) = true) :
    PureFrag20 P (is.map eDA) (is'.map eDA) := by
  by_cases ha : is.all (okA false m) = true
  · have ha' : is'.all (okA false m) = true := GoodMerge.okA_pureStep h.pureStep ha
    rw [map_eDA_of_okA_false ha, map_eDA_of_okA_false ha']
    exact h
  · cases h with
    | @labelVals n cont vs => simpa using PureFrag20.labelVals (P := P) (n := n) (cont := cont.map eD) (vs := vs)
    | @trapLabel n cont => simpa using PureFrag20.trapLabel (P := P) (n := n) (cont := cont.map eD)
    | _ => simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

/-- **The first pure fragment, from an erased typed window, in `simEnv20T`.** -/
theorem spureT_of_pureFragB {P : Profile} (A : Pure.NumAgree (E20 B) P) {m : ModuleInst}
    {is is' : List Admin} (h : PureFrag20 P is is') (hok : is.all (okB m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eDA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  by_cases ha : is.all (okA false m) = true
  · exact StoreGood.spureT_of_spure20 (Whole.spure_of_pureFrag20 A (map_eDA_of_okA_false ha ▸ hc) h)
  · cases h with
    | labelVals =>
      obtain ⟨hn, hcont, -⟩ := labelTB hok hc
      exact spureT_labelVals hn hcont
    | trapLabel =>
      obtain ⟨hn, hcont, -⟩ := labelTB hok hc
      exact spureT_trapLabel hn hcont
    | _ => simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

/-! ## The second pure fragment -/

/-- **Erasure keeps a step of the second pure fragment**, with the erased successor. -/
theorem erase_pureFragBB {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all (okB m) = true) :
    PureFrag20B P (is.map eDA) (is'.map eDA) := by
  by_cases ha : is.all (okA false m) = true
  · have ha' : is'.all (okA false m) = true := GoodMerge.okA_pureStep h.pureStep ha
    rw [map_eDA_of_okA_false ha, map_eDA_of_okA_false ha']
    exact h
  · cases h with
    | ifTrue hc => simpa [eD] using PureFrag20B.ifTrue (P := P) (b₁ := _) (b₂ := _) (bt := _) hc
    | ifFalse => simpa [eD] using PureFrag20B.ifFalse (P := P) (b₁ := _) (b₂ := _) (bt := _)
    | brZero hl hn =>
      simpa [eD] using PureFrag20B.brZero (P := P) (cont := _) (is := _) hl hn
    | brSucc hl => simpa [eD] using PureFrag20B.brSucc (P := P) (cont := _) (is := _) hl
    | returnFrame hn => simpa [eD] using PureFrag20B.returnFrame (P := P) (is := _) hn
    | returnLabel => simpa [eD] using PureFrag20B.returnLabel (P := P) (cont := _) (is := _)
    | trapVals hne =>
      simpa [eD] using PureFrag20B.trapVals (P := P) (is := _) (by simpa [expression] using hne)
    | _ => simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, aref]

/-- `if` in `simEnv20T`, from an erased typed window: the block type and both branches. -/
theorem ifTB {m : ModuleInst} {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (hok : [constI32 c, Admin.plain (.if_ bt b₁ b₂)].all (okB m) = true)
    (hc : TypedV (E20 B) adminsTy
      (.list (adminsToV ([constI32 c, Admin.plain (.if_ bt b₁ b₂)].map eDA)))) :
    TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt) ∧
      TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₁)) ∧
      TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₂)) := by
  have hb : b₁.all (ctrlOkB m) = true ∧ b₂.all (ctrlOkB m) = true := by
    simpa [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk] using hok
  have hc' : TypedV (E20 B) adminsTy
      (.list (adminsToV [constI32 c, Admin.plain (.if_ bt (b₁.map eD) (b₂.map eD))])) := by
    simpa [eD] using hc
  obtain ⟨h₀, h₁, h₂⟩ :=
    Whole.typed_if20 (Whole.typedI_of_mem (i := .if_ bt (b₁.map eD) (b₂.map eD)) hc' (by simp))
  exact ⟨StoreAgree.typedV_to20T (by decide) h₀, typedT_instrs_of_eB hb.1 h₁,
    typedT_instrs_of_eB hb.2 h₂⟩

/-- `br-zero` in `simEnv20T` from an erased typed window. -/
theorem spureT_brZeroB {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {vs' vs : List Val}
    {l : LabelIdx} {is₀ : List V2.Instr} (hl : l.toNat = 0) (hn : vs.length = n)
    (hok : [Admin.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)].all
      (okB m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV
      ([Admin.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)].map eDA)))) :
    SPure (simEnv20T B)
      (adminsToV [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)])
      (adminsToV (vals vs ++ expression cont)) := by
  subst hn
  obtain ⟨hn', hcont, hbody⟩ := labelTB hok hc
  rw [← Pure.vals_append]
  exact StoreGood.spureT_brZero hl hn' hcont (tailTB (okB_label_parts hok).2 hbody)

/-- `return-frame` in `simEnv20T` from an erased typed window. -/
theorem spureT_returnFrameB {m : ModuleInst} {n : Nat} {fr : Frame} {vs' vs : List Val}
    {is₀ : List V2.Instr} (hn : vs.length = n)
    (hok : [Admin.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)].all
      (okB m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV
      ([Admin.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)].map eDA)))) :
    SPure (simEnv20T B)
      (adminsToV [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)])
      (adminsToV (vals vs)) := by
  subst hn
  obtain ⟨hn', hfr, hbody⟩ := frameTD hc
  rw [← Pure.vals_append]
  exact StoreGood.spureT_returnFrame hn' hfr (tailTB (okB_frame_body hok) hbody)

/-- A window with a store, of the second pure fragment, in `simEnv20T`. -/
theorem spureT_of_pureFragBB_store {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all (okB m) = true) (ha : ¬ is.all (okA false m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eDA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  cases h with
  | ifTrue h0 => exact spureT_ifTrue h0 (ifTB hok hc).1 (ifTB hok hc).2.1 (ifTB hok hc).2.2
  | ifFalse => exact spureT_ifFalse (ifTB hok hc).1 (ifTB hok hc).2.1 (ifTB hok hc).2.2
  | brZero hl hn => exact spureT_brZeroB hl hn hok hc
  | brSucc hl =>
    obtain ⟨hn', hcont, hbody⟩ := labelTB hok hc
    exact StoreGood.spureT_brSucc hl hn' hcont (tailTB (okB_label_parts hok).2 hbody)
  | returnFrame hn => exact spureT_returnFrameB hn hok hc
  | returnLabel =>
    obtain ⟨hn', hcont, hbody⟩ := labelTB hok hc
    exact StoreGood.spureT_returnLabel hn' hcont (tailTB (okB_label_parts hok).2 hbody)
  | trapVals hne => exact StoreGood.spureT_trapVals hne (tailTB hok hc)
  | _ => simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, aref]

/-- **The second pure fragment, from an erased typed window, in `simEnv20T`.** -/
theorem spureT_of_pureFragBB {P : Profile} (C : Pure.CvtAgree (E20 B) P) {m : ModuleInst}
    {is is' : List Admin} (h : PureFrag20B P is is') (hok : is.all (okB m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eDA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  by_cases ha : is.all (okA false m) = true
  · exact StoreGood.spureT_of_spure20
      (Whole.spure_of_pureFrag20B C (map_eDA_of_okA_false ha ▸ hc) h)
  · exact spureT_of_pureFragBB_store h hok ha hc


/-! ## `block` and `loop` -/

/-- The block type and the body of a block, typed in `simEnv20T`, from an erased typed window. -/
theorem blockTB {m : ModuleInst} {vs : List Val} {bt : V2.BlockType} {body : List V2.Instr}
    {i : V2.Instr} (hi : i = .block bt body ∨ i = .loop bt body)
    (hok : (vals vs ++ [Admin.plain i]).all (okB m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ((vals vs ++ [Admin.plain i]).map eDA)))) :
    BlockTypedT B bt body := by
  have hb : body.all (ctrlOkB m) = true := by
    rcases hi with rfl | rfl <;> simpa using hok
  have hI : Whole.TypedI B (eD i) := Whole.typedI_of_mem (i := eD i) hc (by simp)
  have hp : TypedV (E20 B) Pure.blocktypeT (blockTypeV bt) ∧
      TypedV (E20 B) Pure.instrsT (.list (instrsToV (body.map eD))) := by
    rcases hi with rfl | rfl
    · exact Whole.typed_block_inv20 (by simpa using hI)
    · exact Whole.typed_loop_inv20 (by simpa using hI)
  exact ⟨StoreAgree.typedV_to20T (by decide) hp.1, typedT_instrs_of_eB hb hp.2⟩

/-! ## The read rules -/

/-- A `Step_read` firing of `simEnv20T` from a configuration with `TypF`, the state unchanged and
the erased successor code typed. -/
theorem fwdB_of_fires {s : Store H} {f : Frame} {is is' : List Admin} {k : Nat}
    (ht : TypF B hn ⟨s, f, is⟩) (hs : StoreOkB s) (hok : is.all (okB f.module) = true)
    (hok' : is'.all (okB f.module) = true)
    (hc' : TypedV (E20 B) adminsTy (.list (adminsToV (is'.map eDA))))
    (hf : Sim.Fires (simEnv20T B) "Step_read" k
      (.tuple [configV hn ⟨s, f, is⟩, .list (adminsToV is')])) :
    TypF B hn ⟨s, f, is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) := by
  have ht' : TypF B hn ⟨s, f, is'⟩ := ⟨ht.state, hc'⟩
  exact ⟨ht', sstepT_read ((typF_stateB ht hs)) ((typF_codeB ht hok)) ((typF_codeB ht' hok')) hf⟩

/-- **`call_addr`, forward**: the erased callee body is typed . -/
theorem fwdB_callAddr {c c' : Config H} (h : CallAddrFwd20 c c') (ht : TypF B hn c)
    (hs : StoreOkB c.store) (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF B hn c' ∧ SStepB (simEnv20T B) (configV hn c) (configV hn c') := by
  cases h with
  | @mk s f a vs fi fn hf hcode hk =>
    have hc : Typed20 (E20 B) hn ⟨eraseS s, f, vals vs ++ [.callAddr a]⟩ :=
      typed20_iff.2 ⟨ht.state, by simpa using ht.code⟩
    have hT := Whole.typed20_succ_callAddr20 hc (.mk (eraseS_funcInst hf) (eraseFI_code hcode) hk)
    exact fwdB_of_fires ht hs hok hok' (by simpa using (typed20_iff.1 hT).2)
      (firesT_callAddr ((typF_stateB ht hs)) hf hcode hk)

/-- **`block` and `loop`, forward.** -/
theorem fwdB_block {c c' : Config H} (h : BlockFwd20 c c') (ht : TypF B hn c)
    (hs : StoreOkB c.store) (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF B hn c' ∧ SStepB (simEnv20T B) (configV hn c) (configV hn c') := by
  cases h with
  | @block s f bt body vs ft hbt hk =>
    have hT := Whole.typed20_succ_block20 ht.erased (StoreDeep.erase_block (.block hbt hk))
    exact fwdB_of_fires ht hs hok hok' (typed20_iff.1 hT).2
      (StoreDeep.firesT_block ((typF_stateB ht hs)) (blockTB (.inl rfl) hok ht.code) hbt hk)
  | @loop s f bt body vs ft hbt hk =>
    have hT := Whole.typed20_succ_block20 ht.erased (StoreDeep.erase_block (.loop hbt hk))
    exact fwdB_of_fires ht hs hok hok' (typed20_iff.1 hT).2
      (StoreDeep.firesT_loop ((typF_stateB ht hs)) (blockTB (.inr rfl) hok ht.code) hbt hk)

/-- `local.get`, `global.get`, `ref.func`, forward. -/
theorem fwdB_var {P : Profile} {c c' : Config H} (h : ReadFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | localGet hv => exact fwdB_of_fires ht hs hok hok' (typedE_val _) (firesT_localGet hv ((typF_stateB ht hs)))
  | globalGet ha hg =>
    exact fwdB_of_fires ht hs hok hok' (typedE_val _) (firesT_globalGet ha hg ((typF_stateB ht hs)))
  | refFunc ha =>
    exact fwdB_of_fires ht hs hok hok' (typedE_val (.ref (.funcAddr _)))
      (firesT_refFunc ha ((typF_stateB ht hs)))

/-- `call`, forward. -/
theorem fwdB_call {P : Profile} {c c' : Config H} (h : CallFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | call ha => exact fwdB_of_fires ht hs hok hok' (typedE_callAddr _) (firesT_call ha ((typF_stateB ht hs)))

/-- The unpacked loads, forward. -/
theorem fwdB_load {P : Profile} {c c' : Config H} (h : LoadFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hz := (typF_stateB ht hs)
  cases h with
  | intTrap hm hlt =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdB_of_fires ht hs hok hok' typedE_trap
      (firesT_loadNumTrap (loadNumV_int _ _) hz ha hm' hlt)
  | @intVal s f t ao i mi c hm hb =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdB_of_fires ht hs hok hok' (typedE_val (.num ⟨.int t, c⟩))
      (firesT_loadNumVal (Whole.nbytes20_storeB P) (loadNumV_int _ _) hz ha hm' hb)
  | floatTrap hm hlt =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdB_of_fires ht hs hok hok' typedE_trap
      (firesT_loadNumTrap (loadNumV_float _ _) hz ha hm' hlt)
  | @floatVal s f t ao i mi c hm hb =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdB_of_fires ht hs hok hok' (typedE_val (.num ⟨.float t, c⟩))
      (firesT_loadNumVal (Whole.nbytes20_storeB P) (loadNumV_float _ _) hz ha hm' hb)

/-- The packed loads, forward. -/
theorem fwdB_pack {P : Profile} {c c' : Config H} (h : LoadPackFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap hm hlt =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdB_of_fires ht hs hok hok' typedE_trap (firesT_loadPackTrap ((typF_stateB ht hs)) ha hm' hlt)
  | @val s f t sz sx ao i mi c hm hb =>
    obtain ⟨ad, ha, hm'⟩ := mem?_some hm
    exact fwdB_of_fires ht hs hok hok' (typedE_val (.num ⟨.int t, GoodMerge.extPack20 t sx c⟩))
      (firesT_loadPackVal (Whole.floatB_storeB P) (Whole.laneCalls20_storeB P) ((typF_stateB ht hs))
        ha hm' hb)

/-- `table.size`, `memory.size`, forward. -/
theorem fwdB_size {P : Profile} {c c' : Config H} (h : SizeFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | table ht' hn' =>
    exact fwdB_of_fires ht hs hok hok' (typedE_const _) (firesT_tableSize ((typF_stateB ht hs)) ht' hn')
  | memory hm hn' =>
    exact fwdB_of_fires ht hs hok hok' (typedE_const _) (firesT_memorySize ((typF_stateB ht hs)) hm hn')

/-- `table.get`, forward. -/
theorem fwdB_tget {P : Profile} {c c' : Config H} (h : TableGetFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap ht' hge =>
    exact fwdB_of_fires ht hs hok hok' typedE_trap (firesT_tableGetTrap ((typF_stateB ht hs)) ht' hge)
  | @val s f x i ti r ht' hr =>
    exact fwdB_of_fires ht hs hok hok' (typedE_val (.ref r)) (firesT_tableGetVal ((typF_stateB ht hs)) ht' hr)

/-- `call_indirect`, both rules, forward. -/
theorem fwdB_callInd {P : Profile} {c c' : Config H} (h : CallIndFwd20 c c' ∨ CallIndTrapFwd20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  rcases h with h | h
  · cases h with
    | mk ht' hr hf hy =>
      exact fwdB_of_fires ht hs hok hok' (typedE_callAddr _)
        (firesT_callIndirectCall ((typF_stateB ht hs)) ht' hr hf hy)
  · cases h with
    | mk ht' hft h =>
      exact fwdB_of_fires ht hs hok hok' typedE_trap
        (firesT_callIndirectTrap ((typF_stateB ht hs)) ht' hft h)

/-! ## The writes -/

/-- **`local.set`, `global.set` and the six stores, forward.** -/
theorem fwdB_local {P : Profile} {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hx : x.toNat < f.locals.length) (ht : TypF (storeB P) hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩)
    (hs : StoreOkB s) :
    TypF (storeB P) hn ⟨s, f.setLocal x v, []⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩)
        (configV hn ⟨s, f.setLocal x v, []⟩) := by
  obtain ⟨hst, hfr⟩ := Whole.typedV_stateV_iff.1 ht.state
  exact ⟨⟨Whole.typedV_stateV_iff.2 ⟨hst, Whole.typedV_frameV_setLocal hfr x v⟩,
    by simpa using typedV_admins_nil20⟩, sstepT_of_firesStep (firesT_localSet ((typF_stateB ht hs)) hx)⟩

theorem fwdB_global {P : Profile} {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val}
    {a : GlobalAddr} {gi : GlobalInst} (ha : f.module.globalAddr? x = some a)
    (hg : s.globalInst? a = some gi)
    (ht : TypF (storeB P) hn ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩) (hs : StoreOkB s) :
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
    sstepT_of_firesStep (firesT_globalSet ((typF_stateB ht hs)) ha' hg')⟩
  rw [eraseS_setGlobal]
  exact Whole.typedV_stateV_iff.2 ⟨Whole.typedV_storeV_iff.2 (Whole.storeTy20_setGlobal S a hgi), hfr⟩

theorem fwdB_store {P : Profile} {c c' : Config H} (h : StoreTop20 c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hz := (typF_stateB ht hs)
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

theorem fwdB_pureA {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : PureFrag20 P is is') (hok : is.all (okB f.module) = true)
    (ht : TypF (storeB P) hn ⟨s, f, is⟩) (hs : StoreOkB s) :
    TypF (storeB P) hn ⟨s, f, is'⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) := by
  have ht' : TypF (storeB P) hn ⟨s, f, is'⟩ :=
    ⟨ht.state, Whole.typedV_succ_pureFrag20 ht.code (erase_pureFragB h hok)⟩
  have hok' : is'.all (okB f.module) = true := okB_pureStep h.pureStep hok
  have A := Pure.numAgree_simEnv20 (Whole.intB_storeB P) (Whole.floatB_storeB P)
  refine ⟨ht', (sstepB20T_iff _).2 ?_⟩
  exact StoreRun.sstepT_pure ((typF_stateB ht hs)) ((typF_codeB ht hok)) ((typF_codeB ht' hok'))
    (spureT_of_pureFragB A h hok ht.code)

theorem fwdB_pureB {P : Profile} {c c' : Config H} (h : PureFwd20B P c c')
    (hok : c.code.all (okB c.frame.module) = true) (ht : TypF (storeB P) hn c)
    (hs : StoreOkB c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | @mk s f is is' h =>
    have ht' : TypF (storeB P) hn ⟨s, f, is'⟩ :=
      ⟨ht.state, Whole.typedV_succ_pureFrag20B ht.code (erase_pureFragBB h hok)⟩
    have hok' : is'.all (okB f.module) = true := okB_pureStep h.pureStep hok
    refine ⟨ht', (sstepB20T_iff _).2 ?_⟩
    exact StoreRun.sstepT_pure ((typF_stateB ht hs)) ((typF_codeB ht hok)) ((typF_codeB ht' hok'))
      (spureT_of_pureFragBB (Pure.cvtAgree_simEnv20 (Whole.floatB_storeB P)) h hok
        ht.code)

/-! ## `memory.fill` -/

theorem typedV_admin_nop20 : TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain .nop)) :=
  Pure.typedV_closedCase20 (Whole.findTyp_admininstr20 (B := B)) (op := "NOP") rfl hasTyp_tupT_nil

theorem typedV_admin_memoryFill20 :
    TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain .memoryFill)) :=
  Pure.typedV_closedCase20 (Whole.findTyp_admininstr20 (B := B)) (op := "MEMORY.FILL") rfl
    hasTyp_tupT_nil

theorem typedV_admin_const20 (k : BitVec 32) :
    TypedV (E20 B) (.varT "admininstr" []) (adminToV (constI32 k)) :=
  Whole.typedV_admins_single20_iff.1 (Whole.typedV_admins_const20 k)

theorem typedV_admin_val20 (v : Val) :
    TypedV (E20 B) (.varT "admininstr" []) (adminToV v.toAdmin) :=
  Whole.typedV_admins_single20_iff.1 (Whole.typedV_admins_val20 v)

/-- **The erased successor of `memory.fill-succ` is typed in `simEnv20`**: its `i32.store8` is
erased to `nop`. -/
theorem typedE_fillSucc (i n : BitVec 32) (v : Val) :
    TypedV (E20 B) adminsTy (.list (adminsToV ([constI32 i, v.toAdmin, store8, constI32 (i + 1),
      v.toAdmin, constI32 (n - 1), .plain .memoryFill].map eDA))) := by
  have e : [constI32 i, v.toAdmin, store8, constI32 (i + 1), v.toAdmin, constI32 (n - 1),
      Admin.plain .memoryFill].map eDA = [constI32 i, v.toAdmin, .plain .nop, constI32 (i + 1),
      v.toAdmin, constI32 (n - 1), .plain .memoryFill] := by
    simp [store8, eD, StoreFn.eDA_toAdmin]
  rw [e]
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact typedV_admin_const20 i
  · exact typedV_admin_val20 v
  · exact typedV_admin_nop20
  · exact typedV_admin_const20 _
  · exact typedV_admin_val20 v
  · exact typedV_admin_const20 _
  · exact typedV_admin_memoryFill20

/-- **`memory.fill`, forward**: the three rules fire in `simEnv20T`; at `-succ`, `i + 1` does not
wrap since the memory has fewer than `2 ^ 32` bytes. -/
theorem fwdB_fill {P : Profile} {c c' : Config H} (h : MemFillFwd c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) (hm : StoreSmall c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap hm' hlt =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    exact fwdB_of_fires ht hs hok hok' typedE_trap
      (firesT_memFillTrap (typF_stateB ht hs) ha hma hlt)
  | zero hm' hb =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    exact fwdB_of_fires ht hs hok hok' (by simpa using typedV_admins_nil20)
      (firesT_memFillZero (typF_stateB ht hs) ha hma hb)
  | @succ s f i n v mi hm' hb hn0 =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    have hsz := hm.lt hm'
    have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
    exact fwdB_of_fires ht hs hok hok' (typedE_fillSucc i n v)
      (firesT_memFillSucc (typF_stateB ht hs) ha hma hb hn0 (by omega))

/-! ## `memory.copy` and `memory.init` -/

/-- An element of erased code typed in `simEnv20`. -/
theorem typedE_mem {l : List Admin} (h : TypedV (E20 B) adminsTy (.list (adminsToV (l.map eDA))))
    {a : Admin} (ha : a ∈ l) : TypedV (E20 B) (.varT "admininstr" []) (adminToV (eDA a)) :=
  Sim.typedV_list_iff.1 h _ (by
    rw [Pure.adminsToV_eq_map]
    exact List.mem_map_of_mem (List.mem_map_of_mem ha))

/-- A list whose elements are typed `admininstr`s. -/
theorem typedE_of_all {l : List Admin}
    (h : ∀ a ∈ l, TypedV (E20 B) (.varT "admininstr" []) (adminToV a)) :
    TypedV (E20 B) adminsTy (.list (adminsToV l)) :=
  Sim.typedV_list_iff.2 fun u hu => by
    rw [Pure.adminsToV_eq_map] at hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
    exact h a ha

set_option maxHeartbeats 1000000 in
/-- `i32.load8_u` is an `admininstr` of `simEnv20`. -/
theorem typedV_admin_load8u20 : TypedV (E20 B) (.varT "admininstr" []) (adminToV load8u) :=
  Whole.typedV_of_empty20 ⟨100, by with_unfolding_all rfl⟩

theorem typedV_admin_memoryCopy20 :
    TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain .memoryCopy)) :=
  Pure.typedV_closedCase20 (Whole.findTyp_admininstr20 (B := B)) (op := "MEMORY.COPY") rfl
    hasTyp_tupT_nil

theorem eDA_load8u : eDA load8u = load8u := rfl

theorem eDA_store8 : eDA store8 = .plain .nop := rfl

/-- The erased successors of `memory.copy-le` and `-gt` are typed in `simEnv20`. -/
theorem typedE_copySucc (a b c d e : BitVec 32) :
    TypedV (E20 B) adminsTy (.list (adminsToV ([constI32 a, constI32 b, load8u, store8,
      constI32 c, constI32 d, constI32 e, .plain .memoryCopy].map eDA))) := by
  simp only [List.map_cons, List.map_nil, eDA_load8u, eDA_store8,
    StoreDeep.eDA_plain]
  refine typedE_of_all fun u hu => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · exact typedV_admin_load8u20
  · exact typedV_admin_nop20
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · simpa [eD] using typedV_admin_memoryCopy20 (B := B)

/-- **`memory.copy`, forward**: the four rules fire in `simEnv20T`; the sums of `-le` and `-gt`
do not wrap since the memory has fewer than `2 ^ 32` bytes. -/
theorem fwdB_copy {P : Profile} {c c' : Config H} (h : MemCopyFwd c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) (hm : StoreSmall c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap hm' hlt =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    exact fwdB_of_fires ht hs hok hok' typedE_trap
      (firesT_memCopyTrap (typF_stateB ht hs) ha hma hlt)
  | zero hm' hb =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    exact fwdB_of_fires ht hs hok hok' (by simpa using typedV_admins_nil20)
      (firesT_memCopyZero (typF_stateB ht hs) ha hma hb)
  | @le s f j i n mi hm' hb hn0 hle =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    have hsz : mi.bytes.size < 2 ^ 32 := hm.lt hm'
    have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
    exact fwdB_of_fires ht hs hok hok' (typedE_copySucc _ _ _ _ _)
      (firesT_memCopyLe (typF_stateB ht hs) ha hma hb hn0 hle (by omega) (by omega))
  | @gt s f j i n mi hm' hb hn0 hgt =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    have hsz : mi.bytes.size < 2 ^ 32 := hm.lt hm'
    exact fwdB_of_fires ht hs hok hok' (typedE_copySucc _ _ _ _ _)
      (firesT_memCopyGt (typF_stateB ht hs) ha hma hb hn0 hgt (by omega) (by omega))

/-- The erased successor of `memory.init-succ` is typed in `simEnv20`, given the typing of
`memory.init x`. -/
theorem typedE_initSucc (a b c d e : BitVec 32) (x : DataIdx)
    (hx : TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain (.memoryInit x)))) :
    TypedV (E20 B) adminsTy (.list (adminsToV ([constI32 a, constI32 b, store8, constI32 c,
      constI32 d, constI32 e, .plain (.memoryInit x)].map eDA))) := by
  simp only [List.map_cons, List.map_nil, eDA_store8, StoreDeep.eDA_plain]
  refine typedE_of_all fun u hu => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · exact typedV_admin_nop20
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · simpa [eD] using hx

/-- `memory.init-succ`, forward. -/
theorem fwdB_initSucc {P : Profile} {s : Store H} {f : Frame} {x : DataIdx} {j i n : BitVec 32}
    {mi : MemInst} {di : DataInst} {b : UInt8} (hm' : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hd : (⟨s, f⟩ : State H).data? x = some di)
    (hb : i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
    (hn0 : n ≠ 0) (hbyte : di.bytes.data[i.toNat]? = some b)
    (ht : TypF (storeB P) hn ⟨s, f, initCode j i n x⟩) (hs : StoreOkB s) (hm : StoreSmall s)
    (hok : (initCode j i n x).all (okB f.module) = true)
    (hok' : [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8, constI32 (j + 1),
      constI32 (i + 1), constI32 (n - 1), Admin.plain (.memoryInit x)].all (okB f.module) = true) :
    TypF (storeB P) hn ⟨s, f, [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8,
        constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.memoryInit x)]⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, initCode j i n x⟩)
        (configV hn ⟨s, f, [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8,
          constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.memoryInit x)]⟩) := by
  obtain ⟨a, ha, hma⟩ := mem?_some hm'
  obtain ⟨ad, had, hdd⟩ := data?_some hd
  have hsz : mi.bytes.size < 2 ^ 32 := hm.lt hm'
  have hdz : di.bytes.size < 2 ^ 32 := hm.ltData hdd
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hx : TypedV (E20 (storeB P)) (.varT "admininstr" []) (adminToV (.plain (.memoryInit x))) :=
    by simpa [eD] using typedE_mem ht.code (a := .plain (.memoryInit x)) (by simp)
  exact fwdB_of_fires ht hs hok hok' (typedE_initSucc _ _ _ _ _ x hx)
    (firesT_memInitSucc (typF_stateB ht hs) ha hma had hdd hb hn0 hbyte (by omega) (by omega))

/-- **`memory.init`, forward**: the three rules fire in `simEnv20T`; the sums of `-succ` do not
wrap since the memory and the data segment have fewer than `2 ^ 32` bytes. -/
theorem fwdB_init {P : Profile} {c c' : Config H} (h : MemInitFwd c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) (hm : StoreSmall c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap hm' hd hlt =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    obtain ⟨ad, had, hdd⟩ := data?_some hd
    exact fwdB_of_fires ht hs hok hok' typedE_trap
      (firesT_memInitTrap (typF_stateB ht hs) ha hma had hdd hlt)
  | zero hm' hd hb =>
    obtain ⟨a, ha, hma⟩ := mem?_some hm'
    obtain ⟨ad, had, hdd⟩ := data?_some hd
    exact fwdB_of_fires ht hs hok hok' (by simpa using typedV_admins_nil20)
      (firesT_memInitZero (typF_stateB ht hs) ha hma had hdd hb)
  | succ hm' hd hb hn0 hbyte => exact fwdB_initSucc hm' hd hb hn0 hbyte ht hs hm hok hok'

/-! ## `table.set` and `table.fill` -/

theorem findTyp_tableidx20 : (E20 B).findTyp? "tableidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

theorem typedV_admin_tableSet20 (x : TableIdx) :
    TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain (.tableSet x))) :=
  Pure.typedV_closedCase20 (Whole.findTyp_admininstr20 (B := B)) (op := "TABLE.SET") rfl
    (Whole.typedV_aliasG findTyp_tableidx20 (Whole.typedV_idx20 x _ ⟨rfl, rfl, rfl⟩) _
      ⟨rfl, rfl, rfl⟩)

/-- **`table.set`, forward**: rules 7 and 8 of `simEnv20T`; the table write commutes with the
erasure. -/
theorem fwdB_tset {P : Profile} {c c' : Config H} (h : TableSetFwd c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | @trap s f x i r a ti ha ht' hge =>
    have ha' : f.module.tables[x.toNat]? = some a := by simpa [ModuleInst.tableAddr?] using ha
    have ht'' : s.tables[a]? = some ti := by simpa [Store.tableInst?] using ht'
    exact ⟨⟨ht.state, typedE_trap⟩, sstepT_of_firesStep
      (firesT_tableSetTrap (typF_stateB ht hs) ha' ht'' hge)⟩
  | @val s f x i r a ti ha ht' hlt =>
    have ha' : f.module.tables[x.toNat]? = some a := by simpa [ModuleInst.tableAddr?] using ha
    have ht'' : s.tables[a]? = some ti := by simpa [Store.tableInst?] using ht'
    have hst : TypedV (E20 (storeB P)) stateT
        (stateV hn (eraseS (s.setTableInst a (ti.setRef i.toNat r))) f) := by
      obtain ⟨hS, hfr⟩ := Whole.typedV_stateV_iff.1 ht.state
      exact Whole.typedV_stateV_iff.2 ⟨Whole.typedV_storeV_iff.2
        (Whole.storeTy20_setTable (Whole.typedV_storeV_iff.1 hS) a _), hfr⟩
    exact ⟨⟨hst, by simpa using typedV_admins_nil20⟩, sstepT_of_firesStep
      (firesT_tableSetVal (typF_stateB ht hs) ha' ht'' hlt)⟩

/-- The erased successor of `table.fill-succ` is typed in `simEnv20`, given the typing of
`table.fill x`. -/
theorem typedE_tfillSucc (i n : BitVec 32) (v : Val) (x : TableIdx)
    (hx : TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain (.tableFill x)))) :
    TypedV (E20 B) adminsTy (.list (adminsToV ([constI32 i, v.toAdmin, .plain (.tableSet x),
      constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.tableFill x)].map eDA))) := by
  have e : [constI32 i, v.toAdmin, Admin.plain (.tableSet x), constI32 (i + 1), v.toAdmin,
      constI32 (n - 1), Admin.plain (.tableFill x)].map eDA = [constI32 i, v.toAdmin,
      .plain (.tableSet x), constI32 (i + 1), v.toAdmin, constI32 (n - 1),
      .plain (.tableFill x)] := by
    simp [eD, StoreFn.eDA_toAdmin]
  rw [e]
  refine typedE_of_all fun u hu => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact typedV_admin_const20 _
  · exact typedV_admin_val20 v
  · exact typedV_admin_tableSet20 x
  · exact typedV_admin_const20 _
  · exact typedV_admin_val20 v
  · exact typedV_admin_const20 _
  · exact hx

/-- `table.fill-succ`, forward. -/
theorem fwdB_tfillSucc {P : Profile} {s : Store H} {f : Frame} {x : TableIdx} {i n : BitVec 32}
    {v : Val} {ti : TableInst} (ht' : (⟨s, f⟩ : State H).table? x = some ti)
    (hb : i.toNat + n.toNat ≤ ti.refs.length) (hn0 : n ≠ 0)
    (ht : TypF (storeB P) hn ⟨s, f, tfillCode i v n x⟩) (hs : StoreOkB s) (hm : StoreSmall s)
    (hok : (tfillCode i v n x).all (okB f.module) = true)
    (hok' : [constI32 i, v.toAdmin, .plain (.tableSet x), constI32 (i + 1), v.toAdmin,
      constI32 (n - 1), Admin.plain (.tableFill x)].all (okB f.module) = true) :
    TypF (storeB P) hn ⟨s, f, [constI32 i, v.toAdmin, .plain (.tableSet x), constI32 (i + 1),
        v.toAdmin, constI32 (n - 1), .plain (.tableFill x)]⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, tfillCode i v n x⟩)
        (configV hn ⟨s, f, [constI32 i, v.toAdmin, .plain (.tableSet x), constI32 (i + 1),
          v.toAdmin, constI32 (n - 1), .plain (.tableFill x)]⟩) := by
  obtain ⟨a, ha, hta⟩ := table?_some ht'
  have hsz : ti.refs.length < 2 ^ 32 := hm.ltTable ht'
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hx : TypedV (E20 (storeB P)) (.varT "admininstr" []) (adminToV (.plain (.tableFill x))) :=
    by simpa [eD] using typedE_mem ht.code (a := .plain (.tableFill x)) (by simp)
  exact fwdB_of_fires ht hs hok hok' (typedE_tfillSucc i n v x hx)
    (firesT_tableFillSucc (typF_stateB ht hs) ha hta hb hn0 (by omega))

/-- **`table.fill`, forward.** -/
theorem fwdB_tfill {P : Profile} {c c' : Config H} (h : TableFillFwd c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) (hm : StoreSmall c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap ht' hlt =>
    obtain ⟨a, ha, hta⟩ := table?_some ht'
    exact fwdB_of_fires ht hs hok hok' typedE_trap
      (firesT_tableFillTrap (typF_stateB ht hs) ha hta hlt)
  | zero ht' hb =>
    obtain ⟨a, ha, hta⟩ := table?_some ht'
    exact fwdB_of_fires ht hs hok hok' (by simpa using typedV_admins_nil20)
      (firesT_tableFillZero (typF_stateB ht hs) ha hta hb)
  | succ ht' hb hn0 => exact fwdB_tfillSucc ht' hb hn0 ht hs hm hok hok'

/-! ## `table.copy` -/

theorem typedV_admin_tableGet20 (x : TableIdx) :
    TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain (.tableGet x))) :=
  Pure.typedV_closedCase20 (Whole.findTyp_admininstr20 (B := B)) (op := "TABLE.GET") rfl
    (Whole.typedV_aliasG findTyp_tableidx20 (Whole.typedV_idx20 x _ ⟨rfl, rfl, rfl⟩) _
      ⟨rfl, rfl, rfl⟩)

/-- The erased successors of `table.copy-le` and `-gt` are typed in `simEnv20`, given the typing
of `table.copy x y`. -/
theorem typedE_tcopySucc (a b c d e : BitVec 32) (x y : TableIdx)
    (hxy : TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain (.tableCopy x y)))) :
    TypedV (E20 B) adminsTy (.list (adminsToV ([constI32 a, constI32 b, .plain (.tableGet y),
      .plain (.tableSet x), constI32 c, constI32 d, constI32 e, .plain (.tableCopy x y)].map
        eDA))) := by
  simp only [List.map_cons, List.map_nil, StoreDeep.eDA_plain]
  refine typedE_of_all fun u hu => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · simpa [eD] using typedV_admin_tableGet20 (B := B) y
  · simpa [eD] using typedV_admin_tableSet20 (B := B) x
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · simpa [eD] using hxy

/-- The redex instruction of a `TypF` configuration is typed in `simEnv20`. -/
theorem typedE_last {P : Profile} {s : Store H} {f : Frame} {pre : List Admin} {i : V2.Instr}
    (ht : TypF (storeB P) hn ⟨s, f, pre ++ [.plain i]⟩) :
    TypedV (E20 (storeB P)) (.varT "admininstr" []) (adminToV (.plain (eD i))) := by
  simpa using typedE_mem ht.code (a := .plain i) (by simp)

/-- `table.copy x y` at the redex of a `TypF` configuration is typed in `simEnv20`. -/
theorem typedE_tcopyI {P : Profile} {s : Store H} {f : Frame} {j i n : BitVec 32}
    {x y : TableIdx} (ht : TypF (storeB P) hn ⟨s, f, tcopyCode j i n x y⟩) :
    TypedV (E20 (storeB P)) (.varT "admininstr" []) (adminToV (.plain (.tableCopy x y))) := by
  simpa [eD] using typedE_last (pre := [constI32 j, constI32 i, constI32 n]) ht

/-- `table.init x y` at the redex of a `TypF` configuration is typed in `simEnv20`. -/
theorem typedE_tinitI {P : Profile} {s : Store H} {f : Frame} {j i n : BitVec 32}
    {x : TableIdx} {y : ElemIdx} (ht : TypF (storeB P) hn ⟨s, f, tinitCode j i n x y⟩) :
    TypedV (E20 (storeB P)) (.varT "admininstr" []) (adminToV (.plain (.tableInit x y))) := by
  simpa [eD] using typedE_last (pre := [constI32 j, constI32 i, constI32 n]) ht

/-- The sums of the `-le`, `-gt` and `-succ` rules do not wrap below a bound under `2 ^ 32`. -/
theorem sums_lt32 {a n L : Nat} (hL : L < 2 ^ 32) (hb : a + n ≤ L) (hn : 1 ≤ n) :
    a + 1 < 2 ^ 32 ∧ a + n - 1 < 2 ^ 32 := by
  omega

theorem one_le_toNat {n : BitVec 32} (hn0 : n ≠ 0) : 1 ≤ n.toNat :=
  Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)

/-- **`table.copy`, forward**: the four rules fire in `simEnv20T`; the sums of `-le` and `-gt`
do not wrap since both tables have fewer than `2 ^ 32` entries. -/
theorem fwdB_tcopy {P : Profile} {c c' : Config H} (h : TableCopyFwd c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) (hm : StoreSmall c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap hx hy hlt =>
    obtain ⟨ax, hax, htx⟩ := table?_some hx
    obtain ⟨ay, hay, hty⟩ := table?_some hy
    exact fwdB_of_fires ht hs hok hok' typedE_trap
      (firesT_tableCopyTrap (typF_stateB ht hs) hax htx hay hty hlt)
  | zero hx hy hb =>
    obtain ⟨ax, hax, htx⟩ := table?_some hx
    obtain ⟨ay, hay, hty⟩ := table?_some hy
    exact fwdB_of_fires ht hs hok hok' (by simpa using typedV_admins_nil20)
      (firesT_tableCopyZero (typF_stateB ht hs) hax htx hay hty hb)
  | @le s f x y j i n tx ty hx hy hb hn0 hle =>
    obtain ⟨ax, hax, htx⟩ := table?_some hx
    obtain ⟨ay, hay, hty⟩ := table?_some hy
    exact fwdB_of_fires ht hs hok hok' (typedE_tcopySucc _ _ _ _ _ x y (typedE_tcopyI ht))
      (firesT_tableCopyLe (typF_stateB ht hs) hax htx hay hty hb hn0 hle
        (sums_lt32 (hm.ltTable hx) hb.2 (one_le_toNat hn0)).1
        (sums_lt32 (hm.ltTable hy) hb.1 (one_le_toNat hn0)).1)
  | @gt s f x y j i n tx ty hx hy hb hn0 hgt =>
    obtain ⟨ax, hax, htx⟩ := table?_some hx
    obtain ⟨ay, hay, hty⟩ := table?_some hy
    exact fwdB_of_fires ht hs hok hok' (typedE_tcopySucc _ _ _ _ _ x y (typedE_tcopyI ht))
      (firesT_tableCopyGt (typF_stateB ht hs) hax htx hay hty hb hn0 hgt
        (sums_lt32 (hm.ltTable hx) hb.2 (one_le_toNat hn0)).2
        (sums_lt32 (hm.ltTable hy) hb.1 (one_le_toNat hn0)).2)

/-! ## `table.init` -/

/-- An element segment of the frame's module, from V2's `elem?`. -/
theorem elem?_some {s : Store H} {f : Frame} {y : ElemIdx} {ei : ElemInst}
    (h : (⟨s, f⟩ : State H).elem? y = some ei) :
    ∃ a, f.module.elems[y.toNat]? = some a ∧ s.elems[a]? = some ei := by
  simp only [State.elem?, ModuleInst.elemAddr?, Store.elemInst?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  exact h

/-- The erased successor of `table.init-succ` is typed in `simEnv20`, given the typing of
`table.init x y`. -/
theorem typedE_tinitSucc (a c d e : BitVec 32) (r : Ref) (x : TableIdx) (y : ElemIdx)
    (hxy : TypedV (E20 B) (.varT "admininstr" []) (adminToV (.plain (.tableInit x y)))) :
    TypedV (E20 B) adminsTy (.list (adminsToV ([constI32 a, aref r, .plain (.tableSet x),
      constI32 c, constI32 d, constI32 e, .plain (.tableInit x y)].map eDA))) := by
  have e₀ : [constI32 a, aref r, Admin.plain (.tableSet x), constI32 c, constI32 d, constI32 e,
      Admin.plain (.tableInit x y)].map eDA = [constI32 a, aref r, .plain (.tableSet x),
      constI32 c, constI32 d, constI32 e, .plain (.tableInit x y)] := by
    simp [eD, aref, StoreFn.eDA_toAdmin]
  rw [e₀]
  refine typedE_of_all fun u hu => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact typedV_admin_const20 _
  · exact typedV_admin_val20 (.ref r)
  · exact typedV_admin_tableSet20 x
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · exact typedV_admin_const20 _
  · exact hxy

/-- **`table.init`, forward**: the three rules fire in `simEnv20T`; the sums of `-succ` do not
wrap since the table and the element segment have fewer than `2 ^ 32` entries. -/
theorem fwdB_tinit {P : Profile} {c c' : Config H} (h : TableInitFwd c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) (hm : StoreSmall c.store)
    (hok : c.code.all (okB c.frame.module) = true)
    (hok' : c'.code.all (okB c'.frame.module) = true) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | trap htx hey hlt =>
    obtain ⟨ax, hax, htx'⟩ := table?_some htx
    obtain ⟨ay, hay, hey'⟩ := elem?_some hey
    exact fwdB_of_fires ht hs hok hok' typedE_trap
      (firesT_tableInitTrap (typF_stateB ht hs) hax htx' hay hey' hlt)
  | zero htx hey hb =>
    obtain ⟨ax, hax, htx'⟩ := table?_some htx
    obtain ⟨ay, hay, hey'⟩ := elem?_some hey
    exact fwdB_of_fires ht hs hok hok' (by simpa using typedV_admins_nil20)
      (firesT_tableInitZero (typF_stateB ht hs) hax htx' hay hey' hb)
  | @succ s f x y j i n ti ei r htx hey hb hn0 hr =>
    obtain ⟨ax, hax, htx'⟩ := table?_some htx
    obtain ⟨ay, hay, hey'⟩ := elem?_some hey
    exact fwdB_of_fires ht hs hok hok' (typedE_tinitSucc _ _ _ _ r x y (typedE_tinitI ht))
      (firesT_tableInitSucc (typF_stateB ht hs) hax htx' hay hey' hb hn0 hr
        (sums_lt32 (hm.ltTable htx) hb.2 (one_le_toNat hn0)).1
        (sums_lt32 (hm.ltElem hey) hb.1 (one_le_toNat hn0)).1)

/-! ## `elem.drop` and `data.drop` -/

theorem eraseS_setElem (s : Store H) (a : ElemAddr) (ei : ElemInst) :
    eraseS (s.setElemInst a ei) = (eraseS s).setElemInst a ei := rfl

theorem eraseS_setData (s : Store H) (a : DataAddr) (di : DataInst) :
    eraseS (s.setDataInst a di) = (eraseS s).setDataInst a di := rfl

/-- **`elem.drop`, forward**: rule 11 of `simEnv20T`; the segment write commutes with the
erasure. -/
theorem fwdB_edrop {P : Profile} {s : Store H} {f : Frame} {x : ElemIdx} {a : ElemAddr}
    {ei : ElemInst} (ha : f.module.elemAddr? x = some a) (he : s.elemInst? a = some ei)
    (ht : TypF (storeB P) hn ⟨s, f, [.plain (.elemDrop x)]⟩) (hs : StoreOkB s) :
    TypF (storeB P) hn ⟨s.setElemInst a { ei with refs := [] }, f, []⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, [.plain (.elemDrop x)]⟩)
        (configV hn ⟨s.setElemInst a { ei with refs := [] }, f, []⟩) := by
  obtain ⟨hS, hfr⟩ := Whole.typedV_stateV_iff.1 ht.state
  have S : Whole.StoreTy20 (storeB P) hn (eraseS s) := Whole.typedV_storeV_iff.1 hS
  have ha' : f.module.elems[x.toNat]? = some a := by simpa [ModuleInst.elemAddr?] using ha
  have he' : s.elems[a]? = some ei := by simpa [Store.elemInst?] using he
  have hei : TypedV (E20 (storeB P)) (.varT "eleminst" []) (elemInstV { ei with refs := [] }) :=
    Whole.typedV_elemInstV_drop
      (Whole.typedV_of_getElem? S.elems (show (eraseS s).elems[a]? = some ei from he'))
  refine ⟨⟨?_, by simpa using typedV_admins_nil20⟩,
    sstepT_of_firesStep (firesT_elemDrop (typF_stateB ht hs) ha' he')⟩
  rw [eraseS_setElem]
  exact Whole.typedV_stateV_iff.2 ⟨Whole.typedV_storeV_iff.2 (Whole.storeTy20_setElem S a hei),
    hfr⟩

/-- **`data.drop`, forward**: rule 22 of `simEnv20T`; the segment write commutes with the
erasure. -/
theorem fwdB_ddrop {P : Profile} {s : Store H} {f : Frame} {x : DataIdx} {a : DataAddr}
    {di : DataInst} (ha : f.module.dataAddr? x = some a) (hd : s.dataInst? a = some di)
    (ht : TypF (storeB P) hn ⟨s, f, [.plain (.dataDrop x)]⟩) (hs : StoreOkB s) :
    TypF (storeB P) hn ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, [.plain (.dataDrop x)]⟩)
        (configV hn ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩) := by
  obtain ⟨hS, hfr⟩ := Whole.typedV_stateV_iff.1 ht.state
  have S : Whole.StoreTy20 (storeB P) hn (eraseS s) := Whole.typedV_storeV_iff.1 hS
  have ha' : f.module.datas[x.toNat]? = some a := by simpa [ModuleInst.dataAddr?] using ha
  have hd' : s.datas[a]? = some di := by simpa [Store.dataInst?] using hd
  refine ⟨⟨?_, by simpa using typedV_admins_nil20⟩,
    sstepT_of_firesStep (firesT_dataDrop (typF_stateB ht hs) ha' hd')⟩
  rw [eraseS_setData]
  exact Whole.typedV_stateV_iff.2 ⟨Whole.typedV_storeV_iff.2
    (Whole.storeTy20_setData S a (Whole.typedV_dataInst20 _)), hfr⟩

/-- **`elem.drop` and `data.drop`, forward.** -/
theorem fwdB_drop {P : Profile} {c c' : Config H} (h : DropFwd c c')
    (ht : TypF (storeB P) hn c) (hs : StoreOkB c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | elem ha he => exact fwdB_edrop ha he ht hs
  | data ha hd => exact fwdB_ddrop ha hd ht hs

/-! ## One base step -/

/-- **One base step, forward.** -/
theorem fwdB_baseF {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseF P c c')
    (ht : TypF (storeB P) hn c) (hok : c.code.all (okB c.frame.module) = true)
    (hs : StoreOkB c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hok' := (okB_step (host := host) h.step hok hs).1
  cases h with
  | pureA h => exact fwdB_pureA h hok ht hs
  | pureB h => exact fwdB_pureB h hok ht hs
  | block h => exact fwdB_block h ht hs hok hok'
  | read h => exact fwdB_var h ht hs hok hok'
  | call h => exact fwdB_call h ht hs hok hok'
  | callAddr h => exact fwdB_callAddr h ht hs hok hok'
  | load h => exact fwdB_load h ht hs hok hok'
  | pack h => exact fwdB_pack h ht hs hok hok'
  | size h => exact fwdB_size h ht hs hok hok'
  | tget h => exact fwdB_tget h ht hs hok hok'
  | callInd h => exact fwdB_callInd (.inl h) ht hs hok hok'
  | callIndTrap h => exact fwdB_callInd (.inr h) ht hs hok hok'
  | localSet hx => exact fwdB_local hx ht hs
  | globalSet ha hg => exact fwdB_global ha hg ht hs
  | store h => exact fwdB_store h ht hs

/-- **One base step with `memory.fill`, forward.** -/
theorem fwdB_base {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseB P c c')
    (ht : TypF (storeB P) hn c) (hok : c.code.all (okB c.frame.module) = true)
    (hs : StoreOkB c.store) (hm : StoreSmall c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hok' := (okB_step (host := host) h.step hok hs).1
  cases h with
  | old h => exact fwdB_baseF (host := host) h ht hok hs
  | fill h => exact fwdB_fill h ht hs hm hok hok'
  | copy h => exact fwdB_copy h ht hs hm hok hok'
  | init h => exact fwdB_init h ht hs hm hok hok'
  | tset h => exact fwdB_tset h ht hs
  | tfill h => exact fwdB_tfill h ht hs hm hok hok'
  | tcopy h => exact fwdB_tcopy h ht hs hm hok hok'
  | tinit h => exact fwdB_tinit h ht hs hm hok hok'
  | drop h => exact fwdB_drop h ht hs

/-! ## The three contexts -/

/-- `ctxt-instrs`. -/
theorem fwdB_ctx {m m' : ModuleInst} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ []) (hs : StoreOkB s) (hs' : StoreOkB s')
    (ht : TypF B hn ⟨s, f, vals vs ++ is ++ rest⟩)
    (hok : (vals vs ++ is ++ rest).all (okB m) = true) (hok' : is'.all (okB m') = true)
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
  · have hst' := StoreFix.sstepT_ctxtInstrs ((typF_stateB hin hs)) ((typF_stateB ht' hs'))
      (StoreGood.typedV_valsTy20T vs) ((typF_codeB hin hok.1.2)) ((typF_codeB ht' hok'))
      (typedT_of_eBL hok.2 hrest) (by simpa [Pure.adminsToV_eq_map, vals] using hne)
      ((sstepB20T_iff B).1 hst)
    refine (sstepB20T_iff B).2 ?_
    simpa only [configV, Pure.adminsToV_append] using hst'

/-- `ctxt-label`. -/
theorem fwdB_label {m m' : ModuleInst} {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List V2.Instr} {is is' : List Admin} (hs : StoreOkB s) (hs' : StoreOkB s')
    (ht : TypF B hn ⟨s, f, [.label n cont is]⟩) (hcok : cont.all (ctrlOkB m) = true)
    (hok : is.all (okB m) = true) (hok' : is'.all (okB m') = true)
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
  · have hst' := StoreRun.sstepT_ctxtLabel ((typF_stateB hin hs)) ((typF_stateB ht' hs'))
      (StoreGood.typedV_nT20T hn') (typedT_instrs_of_eB hcok hcont) ((typF_codeB hin hok))
      ((typF_codeB ht' hok')) ((sstepB20T_iff B).1 hst)
    exact (sstepB20T_iff B).2 (by simpa only [configV, adminsToV, adminToV] using hst')

/-- `ctxt-frame`. -/
theorem fwdB_frame {m m' : ModuleInst} {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (hs : StoreOkB s) (hs' : StoreOkB s')
    (ht : TypF B hn ⟨s, f, [.frame n fi is]⟩)
    (hok : is.all (okB m) = true) (hok' : is'.all (okB m') = true)
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
  · have hsT := (typedT_stateV_iff.1 ((typF_stateB hin hs))).1
    have hsT' := (typedT_stateV_iff.1 ((typF_stateB ht' hs'))).1
    have hst'' := StoreRun.sstepT_ctxtFrame hsT hsT' (StoreAgree.typedV_to20T (by decide) hf)
      (StoreAgree.typedV_to20T (by decide) hfi) (StoreAgree.typedV_to20T (by decide) hfi')
      (StoreGood.typedV_nT20T hn') ((typF_codeB hin hok)) ((typF_codeB ht' hok')) ((sstepB20T_iff B).1 hstep)
    exact (sstepB20T_iff B).2 (by simpa only [configV, stateV, adminsToV, adminToV] using hst'')

/-! ## The forward theorem -/

/-- **`memory.fill` and stores inside the store's functions, forward**: every
`Nest20 (BaseB P)` step from a configuration with `TypF`, `okB` code, a `StoreOkB` store and
`StoreSmall` is a step of `simEnv20T (storeB P)` between the images, and the successor has
`TypF`. -/
theorem fwd_nestB {P : Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Nest20 (BaseB P) c c') (ht : TypF (storeB P) hn c)
    (hok : c.code.all (okB c.frame.module) = true) (hs : StoreOkB c.store)
    (hm : StoreSmall c.store) :
    TypF (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  induction h with
  | base h => exact fwdB_base (host := host) h ht hok hs hm
  | ctx hin hne ih =>
    have hok₁ : (vals _ ++ _ ++ _).all (okB _) = true := hok
    have hi := okB_ctx_inner hok
    have hk := okB_step (host := host) (hin.step fun _ _ h => h.step) hi hs
    exact fwdB_ctx hne hs (storeOkB_of_funcs hs hk.2.1) ht hok₁ hk.1
      fun hin' => ih hin' hi hs hm
  | label hin ih =>
    have hb := okB_label_parts hok
    have hk := okB_step (host := host) (hin.step fun _ _ h => h.step) hb.2 hs
    exact fwdB_label hs (storeOkB_of_funcs hs hk.2.1) ht hb.1 hb.2 hk.1
      fun hin' => ih hin' hb.2 hs hm
  | frame hin ih =>
    have hb := okB_frame_body hok
    have hk := okB_step (host := host) (hin.step fun _ _ h => h.step) hb hs
    exact fwdB_frame hs (storeOkB_of_funcs hs hk.2.1) ht hb hk.1 fun hin' => ih hin' hb hs hm

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
