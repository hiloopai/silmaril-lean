module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepCover

/-!
# Stores at every depth, forward in `simEnv20T`, nested under every context

The typing part is `TypD`: the state typed in `simEnv20` (the store's functions are store-free),
and the **deeply erased** code typed there. The code itself is then typed in `simEnv20T`
(`typedT_of_eDL`).

Each base step erases to a step 's fragment with the erased successor
(`erase_pureFrag20D`, `erase_pureFrag20BD`, `erase_block`), which gives subject reduction by round
3's lemmas. The forward derivation is

* round 3's, moved to `simEnv20T`, when the window is store-free;
* otherwise one of the rules that copy an `instr*`, fired in `simEnv20T` with the trees typed
  there (`spureT_labelVals`, `spureT_trapLabel`, `spureT_ifTrue`, `spureT_ifFalse`,
  `firesT_block`, `firesT_loop`, and round 5's `StoreGood.spureT_brZero`, …).

**`fwd_nestD`**: every `Nest20 (BaseD P)` step from a configuration with `TypD`, covered code,
whole pages and a `StoreOkM` store is a step of `simEnv20T (storeB P)` between the images, and
the successor has `TypD`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreDeep

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
  WholePages BlockFwd20 storeB typed20_iff)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (storeOkI)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (ctrlOkI FwdStep20G)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (ctrlOkM okA StoreOkM LoadPackFwd20)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The typing invariant -/

/-- **The typing part of the invariant**: the state typed in `simEnv20`, and the code typed there
after its stores are erased at every depth. -/
structure TypD (B : Builtins) (hn : H → String) (c : Config H) : Prop where
  state : TypedV (E20 B) stateT (stateV hn c.store c.frame)
  code : TypedV (E20 B) adminsTy (.list (adminsToV (c.code.map eDA)))

theorem TypD.stateT {c : Config H} (h : TypD B hn c) :
    TypedV (simEnv20T B) stateT (stateV hn c.store c.frame) :=
  StoreAgree.typedV_to20T (by decide) h.state

/-- The code of a configuration with `TypD` and covered code, typed in `simEnv20T`. -/
theorem codeTD {m : ModuleInst} {c : Config H} (h : TypD B hn c) (hok : c.code.all (okD m) = true) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV c.code)) :=
  typedT_of_eDL hok h.code

theorem typD_of_typed20 {m : ModuleInst} {c : Config H} (h : Typed20 (E20 B) hn c)
    (ha : c.code.all (okA false m) = true) : TypD B hn c :=
  ⟨(typed20_iff.1 h).1, by simpa [map_eDA_of_okA_false ha] using (typed20_iff.1 h).2⟩

theorem typed20_of_typD {m : ModuleInst} {c : Config H} (h : TypD B hn c)
    (ha : c.code.all (okA false m) = true) : Typed20 (E20 B) hn c :=
  typed20_iff.2 ⟨h.state, by simpa [map_eDA_of_okA_false ha] using h.code⟩

/-- The erased configuration of a configuration with `TypD` is typed in `simEnv20`. -/
theorem TypD.erased {c : Config H} (h : TypD B hn c) :
    Typed20 (E20 B) hn ⟨c.store, c.frame, c.code.map eDA⟩ :=
  typed20_iff.2 ⟨h.state, h.code⟩

/-! ## Store-free windows, packed loads and stores -/

/-- **A store-free window of the widened fragment**, forward in `simEnv20T`. -/
theorem fwdD_old {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20G P c c') (ha : c.code.all (okA false c.frame.module) = true)
    (ht : TypD (storeB P) hn c) (hw : WholePages c.store) (hs : StoreOkM c.store) :
    TypD (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hT := typed20_of_typD ht ha
  have F := CallIndGood.fwdBase20_fwdG (H := H) (hn := hn) P
  have ha' := (GoodMerge.okA_step (host := host) h.step ha hs).1
  exact ⟨typD_of_typed20 (F.sr c c' hT h) ha', ElseAgree.sstepB20T_of_sstepB20S' (F.fwd c c' hT hw h)⟩

/-- **The packed loads**, forward in `simEnv20T`. -/
theorem fwdD_pack {P : Profile} {c c' : Config H} (h : LoadPackFwd20 c c')
    (ht : TypD (storeB P) hn c) (hw : WholePages c.store) :
    TypD (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  obtain ⟨ha, ha'⟩ := GoodMerge.okA_false_loadPack h c.frame.module
  have hT := typed20_of_typD ht ha
  have F := GoodMerge.fwdBase20_loadPack_storeB (H := H) (hn := hn) (W := WholePages) P
  exact ⟨typD_of_typed20 (F.sr c c' hT h) ha', ElseAgree.sstepB20T_of_sstepB20S' (F.fwd c c' hT hw h)⟩

/-- **The scalar stores**, forward in `simEnv20T`, from a state typed in `simEnv20`. -/
theorem fwdD_store {P : Profile} {c c' : Config H} (h : StoreTop20 c c') (ht : TypD (storeB P) hn c) :
    TypD (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  refine ⟨⟨Whole.typedV_state_storeTop20 ht.state h, ?_⟩,
    StoreAgree.sstepT_storeTop20 (Whole.floatB_storeB P) (Whole.laneCalls20_storeB P)
      (Whole.nbytes20_storeB P) ht.state h⟩
  cases h with
  | intTrap _ _ _ | floatTrap _ _ _ | packTrap _ _ _ => exact Whole.typedV_admins_trap20
  | intVal _ _ _ | floatVal _ _ _ | packVal _ _ _ => exact Whole.typedV_admins_nil20

/-! ## Pieces of an erased typed window -/

/-- The parts of a label: the arity and the continuation in `simEnv20T`, the erased body in
`simEnv20`. -/
theorem labelTD {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (hok : [Admin.label n cont body].all (okD m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ([Admin.label n cont body].map eDA)))) :
    TypedV (simEnv20T B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont)) ∧
      TypedV (E20 B) adminsTy (.list (adminsToV (body.map eDA))) := by
  have hc' : TypedV (E20 B) adminsTy
      (.list (adminsToV [Admin.label n (cont.map eD) (body.map eDA)])) := by
    simpa using hc
  obtain ⟨h₁, h₂, h₃⟩ := Whole.label_all20 hc'
  exact ⟨StoreGood.typedV_nT20T h₁, typedT_instrs_of_eD (okD_label_parts hok).1 h₂, h₃⟩

/-- The parts of a frame: the arity and the frame in `simEnv20T`, the erased body in
`simEnv20`. -/
theorem frameTD {n : Nat} {fr : Frame} {body : List Admin}
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ([Admin.frame n fr body].map eDA)))) :
    TypedV (simEnv20T B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20T B) Pure.frameT (frameV fr) ∧
      TypedV (E20 B) adminsTy (.list (adminsToV (body.map eDA))) := by
  have hc' : TypedV (E20 B) adminsTy (.list (adminsToV [Admin.frame n fr (body.map eDA)])) := by
    simpa using hc
  obtain ⟨h₁, h₂, h₃⟩ := Whole.frame_all20 hc'
  exact ⟨StoreGood.typedV_nT20T h₁, StoreAgree.typedV_to20T (by decide) h₂, h₃⟩

/-- The plain tail of a typed erased body, as an `instr*` of `simEnv20T`. -/
theorem tailTD {m : ModuleInst} {l : List Admin} {is : List V2.Instr}
    (hok : (l ++ expression is).all (okD m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ((l ++ expression is).map eDA)))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV (expression is))) := by
  have hT := typedT_of_eDL hok hc
  rw [Pure.adminsToV_append] at hT
  refine StoreGood.typedV_instrs_of_admins20T (Sim.typedV_list_iff.2 fun u hu => ?_)
  exact Sim.typedV_list_iff.1 hT u (List.mem_append_right _ hu)

/-! ## The first pure fragment -/

/-- **Erasure keeps a step of the first pure fragment**, with the erased successor. -/
theorem erase_pureFrag20D {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20 P is is') (hok : is.all (okD m) = true) :
    PureFrag20 P (is.map eDA) (is'.map eDA) := by
  by_cases ha : is.all (okA false m) = true
  · have ha' : is'.all (okA false m) = true := GoodMerge.okA_pureStep h.pureStep ha
    rw [map_eDA_of_okA_false ha, map_eDA_of_okA_false ha']
    exact h
  · cases h with
    | @labelVals n cont vs => simpa using PureFrag20.labelVals (P := P) (n := n) (cont := cont.map eD) (vs := vs)
    | @trapLabel n cont => simpa using PureFrag20.trapLabel (P := P) (n := n) (cont := cont.map eD)
    | _ => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

/-- **The first pure fragment, from an erased typed window, in `simEnv20T`.** -/
theorem spureT_of_pureFrag20D {P : Profile} (A : Pure.NumAgree (E20 B) P) {m : ModuleInst}
    {is is' : List Admin} (h : PureFrag20 P is is') (hok : is.all (okD m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eDA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  by_cases ha : is.all (okA false m) = true
  · exact StoreGood.spureT_of_spure20 (Whole.spure_of_pureFrag20 A (map_eDA_of_okA_false ha ▸ hc) h)
  · cases h with
    | labelVals =>
      obtain ⟨hn, hcont, -⟩ := labelTD hok hc
      exact spureT_labelVals hn hcont
    | trapLabel =>
      obtain ⟨hn, hcont, -⟩ := labelTD hok hc
      exact spureT_trapLabel hn hcont
    | _ => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

/-- **The first pure fragment**, forward in `simEnv20T`. -/
theorem fwdD_pureA {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : PureFrag20 P is is') (hok : is.all (okD f.module) = true)
    (ht : TypD (storeB P) hn ⟨s, f, is⟩) :
    TypD (storeB P) hn ⟨s, f, is'⟩ ∧
      SStepB (simEnv20T (storeB P)) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) := by
  have ht' : TypD (storeB P) hn ⟨s, f, is'⟩ :=
    ⟨ht.state, Whole.typedV_succ_pureFrag20 ht.code (erase_pureFrag20D h hok)⟩
  have hok' : is'.all (okD f.module) = true := okD_pureStep h.pureStep hok
  have A := Pure.numAgree_simEnv20 (Whole.intB_storeB P) (Whole.floatB_storeB P)
  refine ⟨ht', (sstepB20T_iff _).2 ?_⟩
  exact StoreRun.sstepT_pure ht.stateT (codeTD ht hok) (codeTD ht' hok')
    (spureT_of_pureFrag20D A h hok ht.code)

/-! ## The second pure fragment -/

/-- **Erasure keeps a step of the second pure fragment**, with the erased successor. -/
theorem erase_pureFrag20BD {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all (okD m) = true) :
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
    | _ => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, aref]

/-- `if` in `simEnv20T`, from an erased typed window: the block type and both branches. -/
theorem ifTD {m : ModuleInst} {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (hok : [constI32 c, Admin.plain (.if_ bt b₁ b₂)].all (okD m) = true)
    (hc : TypedV (E20 B) adminsTy
      (.list (adminsToV ([constI32 c, Admin.plain (.if_ bt b₁ b₂)].map eDA)))) :
    TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt) ∧
      TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₁)) ∧
      TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₂)) := by
  have hb : b₁.all (ctrlOkD m) = true ∧ b₂.all (ctrlOkD m) = true := by
    simpa [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk] using hok
  have hc' : TypedV (E20 B) adminsTy
      (.list (adminsToV [constI32 c, Admin.plain (.if_ bt (b₁.map eD) (b₂.map eD))])) := by
    simpa [eD] using hc
  obtain ⟨h₀, h₁, h₂⟩ :=
    Whole.typed_if20 (Whole.typedI_of_mem (i := .if_ bt (b₁.map eD) (b₂.map eD)) hc' (by simp))
  exact ⟨StoreAgree.typedV_to20T (by decide) h₀, typedT_instrs_of_eD hb.1 h₁,
    typedT_instrs_of_eD hb.2 h₂⟩

/-- `br-zero` in `simEnv20T` from an erased typed window. -/
theorem spureT_brZeroD {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {vs' vs : List Val}
    {l : LabelIdx} {is₀ : List V2.Instr} (hl : l.toNat = 0) (hn : vs.length = n)
    (hok : [Admin.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)].all
      (okD m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV
      ([Admin.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)].map eDA)))) :
    SPure (simEnv20T B)
      (adminsToV [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)])
      (adminsToV (vals vs ++ expression cont)) := by
  subst hn
  obtain ⟨hn', hcont, hbody⟩ := labelTD hok hc
  rw [← Pure.vals_append]
  exact StoreGood.spureT_brZero hl hn' hcont (tailTD (okD_label_parts hok).2 hbody)

/-- `return-frame` in `simEnv20T` from an erased typed window. -/
theorem spureT_returnFrameD {m : ModuleInst} {n : Nat} {fr : Frame} {vs' vs : List Val}
    {is₀ : List V2.Instr} (hn : vs.length = n)
    (hok : [Admin.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)].all
      (okD m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV
      ([Admin.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)].map eDA)))) :
    SPure (simEnv20T B)
      (adminsToV [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)])
      (adminsToV (vals vs)) := by
  subst hn
  obtain ⟨hn', hfr, hbody⟩ := frameTD hc
  rw [← Pure.vals_append]
  exact StoreGood.spureT_returnFrame hn' hfr (tailTD (okD_frame_body hok) hbody)

/-- A window with a store, of the second pure fragment, in `simEnv20T`. -/
theorem spureT_of_pureFrag20BD_store {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all (okD m) = true) (ha : ¬ is.all (okA false m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eDA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  cases h with
  | ifTrue h0 => exact spureT_ifTrue h0 (ifTD hok hc).1 (ifTD hok hc).2.1 (ifTD hok hc).2.2
  | ifFalse => exact spureT_ifFalse (ifTD hok hc).1 (ifTD hok hc).2.1 (ifTD hok hc).2.2
  | brZero hl hn => exact spureT_brZeroD hl hn hok hc
  | brSucc hl =>
    obtain ⟨hn', hcont, hbody⟩ := labelTD hok hc
    exact StoreGood.spureT_brSucc hl hn' hcont (tailTD (okD_label_parts hok).2 hbody)
  | returnFrame hn => exact spureT_returnFrameD hn hok hc
  | returnLabel =>
    obtain ⟨hn', hcont, hbody⟩ := labelTD hok hc
    exact StoreGood.spureT_returnLabel hn' hcont (tailTD (okD_label_parts hok).2 hbody)
  | trapVals hne => exact StoreGood.spureT_trapVals hne (tailTD hok hc)
  | _ => simp_all [ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, aref]

/-- **The second pure fragment, from an erased typed window, in `simEnv20T`.** -/
theorem spureT_of_pureFrag20BD {P : Profile} (C : Pure.CvtAgree (E20 B) P) {m : ModuleInst}
    {is is' : List Admin} (h : PureFrag20B P is is') (hok : is.all (okD m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eDA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  by_cases ha : is.all (okA false m) = true
  · exact StoreGood.spureT_of_spure20
      (Whole.spure_of_pureFrag20B C (map_eDA_of_okA_false ha ▸ hc) h)
  · exact spureT_of_pureFrag20BD_store h hok ha hc

/-- **The second pure fragment**, forward in `simEnv20T`. -/
theorem fwdD_pureB {P : Profile} {c c' : Config H} (h : PureFwd20B P c c')
    (hok : c.code.all (okD c.frame.module) = true) (ht : TypD (storeB P) hn c) :
    TypD (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | @mk s f is is' h =>
    have ht' : TypD (storeB P) hn ⟨s, f, is'⟩ :=
      ⟨ht.state, Whole.typedV_succ_pureFrag20B ht.code (erase_pureFrag20BD h hok)⟩
    have hok' : is'.all (okD f.module) = true := okD_pureStep h.pureStep hok
    refine ⟨ht', (sstepB20T_iff _).2 ?_⟩
    exact StoreRun.sstepT_pure ht.stateT (codeTD ht hok) (codeTD ht' hok')
      (spureT_of_pureFrag20BD (Pure.cvtAgree_simEnv20 (Whole.floatB_storeB P)) h hok ht.code)

/-! ## `block` and `loop` -/

/-- **Erasure keeps `block` and `loop`**, with the erased successor. -/
theorem erase_block {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : BlockFwd20 ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    BlockFwd20 ⟨s, f, is.map eDA⟩ ⟨s', f', is'.map eDA⟩ := by
  cases h with
  | block hbt hk => simpa [eD] using BlockFwd20.block (body := _) hbt hk
  | loop hbt hk => simpa [eD] using BlockFwd20.loop (body := _) hbt hk

/-- The block type and the body of a block, typed in `simEnv20T`, from an erased typed window. -/
theorem blockTD {m : ModuleInst} {vs : List Val} {bt : V2.BlockType} {body : List V2.Instr}
    {i : V2.Instr} (hi : i = .block bt body ∨ i = .loop bt body)
    (hok : (vals vs ++ [Admin.plain i]).all (okD m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ((vals vs ++ [Admin.plain i]).map eDA)))) :
    BlockTypedT B bt body := by
  have hb : body.all (ctrlOkD m) = true := by
    rcases hi with rfl | rfl <;> simpa using hok
  have hI : Whole.TypedI B (eD i) := Whole.typedI_of_mem (i := eD i) hc (by simp)
  have hp : TypedV (E20 B) Pure.blocktypeT (blockTypeV bt) ∧
      TypedV (E20 B) Pure.instrsT (.list (instrsToV (body.map eD))) := by
    rcases hi with rfl | rfl
    · exact Whole.typed_block_inv20 (by simpa using hI)
    · exact Whole.typed_loop_inv20 (by simpa using hI)
  exact ⟨StoreAgree.typedV_to20T (by decide) hp.1, typedT_instrs_of_eD hb hp.2⟩

/-- The successor of `block` and `loop` is covered. -/
theorem okD_block_succ {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : BlockFwd20 ⟨s, f, is⟩ ⟨s', f', is'⟩) (hok : is.all (okD f.module) = true) :
    is'.all (okD f'.module) = true := by
  cases h <;> simp_all [List.all_append]

/-- **`block` and `loop`**, forward in `simEnv20T`. -/
theorem fwdD_block {P : Profile} {c c' : Config H} (h : BlockFwd20 c c')
    (hok : c.code.all (okD c.frame.module) = true) (ht : TypD (storeB P) hn c) :
    TypD (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', is'⟩ := c'
  have hT' := Whole.typed20_succ_block20 ht.erased (erase_block h)
  have ht' : TypD (storeB P) hn ⟨s', f', is'⟩ := ⟨(typed20_iff.1 hT').1, (typed20_iff.1 hT').2⟩
  have hok' : is'.all (okD f'.module) = true := okD_block_succ h hok
  cases h with
  | block hbt hk =>
    exact ⟨ht', sstepT_of_firesRead ht.stateT (codeTD ht hok) (codeTD ht' hok')
      (firesT_block ht.stateT (blockTD (.inl rfl) hok ht.code) hbt hk)⟩
  | loop hbt hk =>
    exact ⟨ht', sstepT_of_firesRead ht.stateT (codeTD ht hok) (codeTD ht' hok')
      (firesT_loop ht.stateT (blockTD (.inr rfl) hok ht.code) hbt hk)⟩

/-! ## The three contexts -/

/-- `ctxt-instrs`: the erased typing splits, and the inner step lifts in `simEnv20T`. -/
theorem fwdD_ctx {m m' : ModuleInst} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ []) (ht : TypD B hn ⟨s, f, vals vs ++ is ++ rest⟩)
    (hok : (vals vs ++ is ++ rest).all (okD m) = true) (hok' : is'.all (okD m') = true)
    (ih : TypD B hn ⟨s, f, is⟩ → TypD B hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypD B hn ⟨s', f', vals vs ++ is' ++ rest⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, vals vs ++ is ++ rest⟩)
        (configV hn ⟨s', f', vals vs ++ is' ++ rest⟩) := by
  simp only [List.all_append, Bool.and_eq_true] at hok
  have hcode := ht.code
  simp only [List.map_append, map_eDA_vals] at hcode
  obtain ⟨hvi, hrest⟩ := Whole.typedV_admins_append20_iff.1 hcode
  obtain ⟨hvals, his⟩ := Whole.typedV_admins_append20_iff.1 hvi
  have hin : TypD B hn ⟨s, f, is⟩ := ⟨ht.state, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  refine ⟨⟨ht'.state, ?_⟩, ?_⟩
  · simp only [List.map_append, map_eDA_vals]
    exact Whole.typedV_admins_append20_iff.2
      ⟨Whole.typedV_admins_append20_iff.2 ⟨hvals, ht'.code⟩, hrest⟩
  · have hs := StoreFix.sstepT_ctxtInstrs hin.stateT ht'.stateT (StoreGood.typedV_valsTy20T vs)
      (codeTD hin hok.1.2) (codeTD ht' hok') (typedT_of_eDL hok.2 hrest)
      (by simpa [Pure.adminsToV_eq_map, vals] using hne) ((sstepB20T_iff B).1 hst)
    refine (sstepB20T_iff B).2 ?_
    simpa only [configV, Pure.adminsToV_append] using hs

/-- `ctxt-label`: the erased label inverts, and the inner step lifts in `simEnv20T`. -/
theorem fwdD_label {m m' : ModuleInst} {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List V2.Instr} {is is' : List Admin} (ht : TypD B hn ⟨s, f, [.label n cont is]⟩)
    (hcok : cont.all (ctrlOkD m) = true)
    (hok : is.all (okD m) = true) (hok' : is'.all (okD m') = true)
    (ih : TypD B hn ⟨s, f, is⟩ → TypD B hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypD B hn ⟨s', f', [.label n cont is']⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, [.label n cont is]⟩)
        (configV hn ⟨s', f', [.label n cont is']⟩) := by
  have hcode := ht.code
  simp only [List.map_cons, List.map_nil, eDA_label] at hcode
  obtain ⟨hn', hcont, his⟩ := Whole.label_all20 hcode
  have hin : TypD B hn ⟨s, f, is⟩ := ⟨ht.state, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  refine ⟨⟨ht'.state, ?_⟩, ?_⟩
  · simp only [List.map_cons, List.map_nil, eDA_label]
    exact Whole.typedV_admins_single20_iff.2 (Whole.typedV_adminLabel20_iff.2 ⟨hn', hcont, ht'.code⟩)
  · have hs := StoreRun.sstepT_ctxtLabel hin.stateT ht'.stateT (StoreGood.typedV_nT20T hn')
      (typedT_instrs_of_eD hcok hcont) (codeTD hin hok) (codeTD ht' hok')
      ((sstepB20T_iff B).1 hst)
    exact (sstepB20T_iff B).2 (by simpa only [configV, adminsToV, adminToV] using hs)

/-- `ctxt-frame`: the erased frame and the state invert; the inner configuration runs under the
inner frame, and its step lifts in `simEnv20T`. -/
theorem fwdD_frame {m m' : ModuleInst} {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (ht : TypD B hn ⟨s, f, [.frame n fi is]⟩)
    (hok : is.all (okD m) = true) (hok' : is'.all (okD m') = true)
    (ih : TypD B hn ⟨s, fi, is⟩ → TypD B hn ⟨s', fi', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, fi, is⟩) (configV hn ⟨s', fi', is'⟩)) :
    TypD B hn ⟨s', f, [.frame n fi' is']⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, [.frame n fi is]⟩)
        (configV hn ⟨s', f, [.frame n fi' is']⟩) := by
  have hcode := ht.code
  simp only [List.map_cons, List.map_nil, eDA_frame] at hcode
  obtain ⟨hn', hfi, his⟩ := Whole.frame_all20 hcode
  obtain ⟨hs, hf⟩ := Whole.typedV_stateV_iff.1 ht.state
  have hin : TypD B hn ⟨s, fi, is⟩ := ⟨Whole.typedV_stateV_iff.2 ⟨hs, hfi⟩, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  obtain ⟨hs', hfi'⟩ := Whole.typedV_stateV_iff.1 ht'.state
  refine ⟨⟨Whole.typedV_stateV_iff.2 ⟨hs', hf⟩, ?_⟩, ?_⟩
  · simp only [List.map_cons, List.map_nil, eDA_frame]
    exact Whole.typedV_admins_single20_iff.2 (Whole.typedV_adminFrame20_iff.2 ⟨hn', hfi', ht'.code⟩)
  · have hst' := StoreRun.sstepT_ctxtFrame (StoreAgree.typedV_to20T (by decide) hs)
      (StoreAgree.typedV_to20T (by decide) hs') (StoreAgree.typedV_to20T (by decide) hf)
      (StoreAgree.typedV_to20T (by decide) hfi) (StoreAgree.typedV_to20T (by decide) hfi')
      (StoreGood.typedV_nT20T hn') (codeTD hin hok) (codeTD ht' hok') ((sstepB20T_iff B).1 hst)
    exact (sstepB20T_iff B).2 (by simpa only [configV, stateV, adminsToV, adminToV] using hst')

/-! ## The forward theorem -/

/-- One base step, forward. -/
theorem fwdD_base {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseD P c c')
    (ht : TypD (storeB P) hn c) (hok : c.code.all (okD c.frame.module) = true)
    (hw : WholePages c.store) (hs : StoreOkM c.store) :
    TypD (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | old h ha => exact fwdD_old (host := host) h ha ht hw hs
  | pack h => exact fwdD_pack h ht hw
  | store h => exact fwdD_store h ht
  | pureA h => exact fwdD_pureA h hok ht
  | pureB h => exact fwdD_pureB h hok ht
  | block h => exact fwdD_block h hok ht

/-- **Stores at every depth, forward**: every `Nest20 (BaseD P)` step from a configuration with
`TypD`, covered code, whole pages and a `StoreOkM` store is a step of `simEnv20T (storeB P)`
between the images, and the successor has `TypD`. -/
theorem fwd_nestD {P : Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Nest20 (BaseD P) c c') (ht : TypD (storeB P) hn c)
    (hok : c.code.all (okD c.frame.module) = true) (hw : WholePages c.store)
    (hs : StoreOkM c.store) :
    TypD (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  induction h with
  | base h => exact fwdD_base (host := host) h ht hok hw hs
  | ctx hin hne ih =>
    have hok₁ : (vals _ ++ _ ++ _).all (okD _) = true := hok
    have hi := okD_ctx_inner hok
    have hok' := (okD_step (host := host) (hin.step fun _ _ h => h.step) hi hs).1
    exact fwdD_ctx hne ht hok₁ hok' fun hin' => ih hin' hi hw hs
  | label hin ih =>
    have hb := okD_label_parts hok
    have hok' := (okD_step (host := host) (hin.step fun _ _ h => h.step) hb.2 hs).1
    exact fwdD_label ht hb.1 hb.2 hok' fun hin' => ih hin' hb.2 hw hs
  | frame hin ih =>
    have hb := okD_frame_body hok
    have hok' := (okD_step (host := host) (hin.step fun _ _ h => h.step) hb hs).1
    exact fwdD_frame ht hb hok' fun hin' => ih hin' hb hw hs

end Silmaril.Wasm.SpecTec.Sim20.StoreDeep
