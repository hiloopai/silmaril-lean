module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.GoodMergeCode

/-!
# The merged fragment forward in `simEnv20T`, nested under every context

The typing part is round 5's `StoreGood.TypS`: the state typed in `simEnv20`, and the code typed
there after its administrative stores are erased. The code itself is then typed in `simEnv20T`
(`typedT_of_eraseM`).

* `fwdM_old`: a store-free window of `CallIndGood.FwdStep20G` is typed in `simEnv20` and steps by
  `CallIndGood.fwdBase20_fwdG`; its successor is store-free (`okA_step` at `false`), and the step
  moves to `simEnv20T` by `ElseAgree.sstepB20T_of_sstepB20S'`.
* `fwdM_pack`: the packed loads, by `fwdBase20_loadPack_storeB`, moved the same way.
* `fwdM_pureB`: the second pure fragment. A store-free window is round 3's derivation, moved;
  a window holding a store is one of the five concatenation rules, restated in `simEnv20T` by
  `StoreGood.spureT_brZero`, …; the tail is typed there by `typedT_of_eraseM`. Erasure keeps the
  step with the same successor (`erase_pureFrag20BM`), which gives subject reduction.
* the six store steps: `StoreGood.fwdS_store`.
* the three contexts: `fwdM_ctx`, `fwdM_label`, `fwdM_frame` (the frame body read in the inner
  frame's module).
* **`fwd_nestM`**: every `Nest20 (BaseM P)` step from a configuration with `TypS`, covered code,
  whole pages and a `StoreOkM` store is a step of `simEnv20T (storeB P)` between the images, and
  the successor has `TypS`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.GoodMerge

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
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk Nest20 PureFwd20B PureFrag20B StoreTop20 WholePages
  storeB typed20_iff)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (TypS storeOkI eraseA eraseI)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (ctrlOkI FwdStep20G)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## `TypS` and store-free code -/

theorem typS_of_typed20M {m : ModuleInst} {c : Config H} (h : Typed20 (E20 B) hn c)
    (ha : c.code.all (okA false m) = true) : TypS B hn c :=
  ⟨(typed20_iff.1 h).1, by simpa [map_eraseA_of_okA_false ha] using (typed20_iff.1 h).2⟩

theorem typed20_of_typSM {m : ModuleInst} {c : Config H} (h : TypS B hn c)
    (ha : c.code.all (okA false m) = true) : Typed20 (E20 B) hn c :=
  typed20_iff.2 ⟨h.state, by simpa [map_eraseA_of_okA_false ha] using h.code⟩

/-- The code of a configuration with `TypS` and covered code, typed in `simEnv20T`. -/
theorem codeTM {m : ModuleInst} {c : Config H} (h : TypS B hn c)
    (hok : c.code.all (okA true m) = true) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV c.code)) :=
  typedT_of_eraseM hok h.code

/-! ## The base: store-free windows and the packed loads -/

/-- **A store-free window of the widened fragment**, forward in `simEnv20T`. -/
theorem fwdM_old {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20G P c c') (ha : c.code.all (okA false c.frame.module) = true)
    (ht : TypS (storeB P) hn c) (hw : WholePages c.store) (hs : StoreOkM c.store) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hT := typed20_of_typSM ht ha
  have F := CallIndGood.fwdBase20_fwdG (H := H) (hn := hn) P
  have ha' := (okA_step (host := host) h.step ha hs).1
  exact ⟨typS_of_typed20M (F.sr c c' hT h) ha', ElseAgree.sstepB20T_of_sstepB20S' (F.fwd c c' hT hw h)⟩

/-- The windows and successors of the packed loads are store-free. -/
theorem okA_false_loadPack {c c' : Config H} (h : LoadPackFwd20 c c') (m : ModuleInst) :
    c.code.all (okA false m) = true ∧ c'.code.all (okA false m) = true := by
  cases h <;> simp [ctrlOkM, ctrlOkI, ctrlOk]

/-- **The packed loads**, forward in `simEnv20T`. -/
theorem fwdM_pack {P : Profile} {c c' : Config H} (h : LoadPackFwd20 c c')
    (ht : TypS (storeB P) hn c) (hw : WholePages c.store) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  obtain ⟨ha, ha'⟩ := okA_false_loadPack h c.frame.module
  have hT := typed20_of_typSM ht ha
  have F := fwdBase20_loadPack_storeB (H := H) (hn := hn) (W := WholePages) P
  exact ⟨typS_of_typed20M (F.sr c c' hT h) ha', ElseAgree.sstepB20T_of_sstepB20S' (F.fwd c c' hT hw h)⟩

/-! ## The base: the second pure fragment -/

/-- The successor of the second pure fragment from covered code is store-free. -/
theorem okA_false_succ_pureFrag20B {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all (okA true m) = true) :
    is'.all (okA false m) = true := by
  cases h <;> simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI, List.all_append]

/-- Erasure keeps a step of the second pure fragment whose window holds a store. -/
theorem erase_pureFrag20BM_store {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all (okA true m) = true)
    (ha : ¬ is.all (okA false m) = true) : PureFrag20B P (is.map eraseA) is' := by
  cases h with
  | brZero hl hn =>
    simpa only [List.map_cons, List.map_nil, StoreGood.eraseA_label, List.map_append,
      StoreGood.map_eraseA_vals, StoreGood.map_eraseA_expression, StoreGood.eraseA_plain, eraseI]
      using PureFrag20B.brZero (P := P) (is := _) hl hn
  | brSucc hl =>
    simpa only [List.map_cons, List.map_nil, StoreGood.eraseA_label, List.map_append,
      StoreGood.map_eraseA_vals, StoreGood.map_eraseA_expression, StoreGood.eraseA_plain, eraseI]
      using PureFrag20B.brSucc (P := P) (is := _) hl
  | returnFrame hn =>
    simpa only [List.map_cons, List.map_nil, StoreGood.eraseA_frame, List.map_append,
      StoreGood.map_eraseA_vals, StoreGood.map_eraseA_expression, StoreGood.eraseA_plain, eraseI]
      using PureFrag20B.returnFrame (P := P) (is := _) hn
  | returnLabel =>
    simpa only [List.map_cons, List.map_nil, StoreGood.eraseA_label, List.map_append,
      StoreGood.map_eraseA_vals, StoreGood.map_eraseA_expression, StoreGood.eraseA_plain, eraseI]
      using PureFrag20B.returnLabel (P := P) (is := _)
  | trapVals hne =>
    simpa only [List.map_append, StoreGood.map_eraseA_vals, StoreGood.map_eraseA_expression,
      List.map_cons, List.map_nil, StoreGood.eraseA_trap]
      using PureFrag20B.trapVals (P := P) (by simpa [expression] using hne)
  | _ => simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI, aref]

/-- **Erasure keeps a step of the second pure fragment, with the same successor.** -/
theorem erase_pureFrag20BM {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all (okA true m) = true) :
    PureFrag20B P (is.map eraseA) is' := by
  by_cases ha : is.all (okA false m) = true
  · exact (map_eraseA_of_okA_false ha).symm ▸ h
  · exact erase_pureFrag20BM_store h hok ha

/-- The tail of a typed erased body, moved to `simEnv20T` as an `instr*`. -/
theorem tailT_of_eraseM {m : ModuleInst} {l : List Admin} {is : List V2.Instr}
    (hok : (l ++ expression is).all (okA true m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ((l ++ expression is).map eraseA)))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV (expression is))) := by
  have hT := typedT_of_eraseM hok hc
  rw [Pure.adminsToV_append] at hT
  refine StoreGood.typedV_instrs_of_admins20T (Sim.typedV_list_iff.2 fun u hu => ?_)
  exact Sim.typedV_list_iff.1 hT u (List.mem_append_right _ hu)

/-- `br-zero` in `simEnv20T` from an erased typed window. -/
theorem spureT_brZeroM {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {vs' vs : List Val}
    {l : LabelIdx} {is₀ : List V2.Instr} (hl : l.toNat = 0) (hn : vs.length = n)
    (hok : [Admin.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)].all
      (okA true m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV
      ([Admin.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)].map
        eraseA)))) :
    SPure (simEnv20T B)
      (adminsToV [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)])
      (adminsToV (vals vs ++ expression cont)) := by
  subst hn
  obtain ⟨hn', hcont, hbody⟩ := StoreGood.labelT_of_erase hc
  rw [← Pure.vals_append]
  exact StoreGood.spureT_brZero hl hn' hcont (tailT_of_eraseM (bodyOk_labelM hok) hbody)

/-- `return-frame` in `simEnv20T` from an erased typed window. -/
theorem spureT_returnFrameM {m : ModuleInst} {n : Nat} {fr : Frame} {vs' vs : List Val}
    {is₀ : List V2.Instr} (hn : vs.length = n)
    (hok : [Admin.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)].all
      (okA true m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV
      ([Admin.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)].map
        eraseA)))) :
    SPure (simEnv20T B)
      (adminsToV [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)])
      (adminsToV (vals vs)) := by
  subst hn
  obtain ⟨hn', hfr, hbody⟩ := StoreGood.frameT_of_erase hc
  rw [← Pure.vals_append]
  exact StoreGood.spureT_returnFrame hn' hfr (tailT_of_eraseM (bodyOk_frameM hok) hbody)

/-- A window with a store is one of the five concatenation rules, in `simEnv20T`. -/
theorem spureT_of_pureFrag20BM_store {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all (okA true m) = true)
    (ha : ¬ is.all (okA false m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eraseA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  cases h with
  | brZero hl hn => exact spureT_brZeroM hl hn hok hc
  | brSucc hl =>
    exact StoreGood.spureT_brSucc hl (StoreGood.labelT_of_erase hc).1
      (StoreGood.labelT_of_erase hc).2.1
      (tailT_of_eraseM (bodyOk_labelM hok) (StoreGood.labelT_of_erase hc).2.2)
  | returnFrame hn => exact spureT_returnFrameM hn hok hc
  | returnLabel =>
    exact StoreGood.spureT_returnLabel (StoreGood.labelT_of_erase hc).1
      (StoreGood.labelT_of_erase hc).2.1
      (tailT_of_eraseM (bodyOk_labelM hok) (StoreGood.labelT_of_erase hc).2.2)
  | trapVals hne => exact StoreGood.spureT_trapVals hne (tailT_of_eraseM hok hc)
  | _ => simp_all [ctrlOkM, ctrlOkI, ctrlOk, storeOkI, aref]

/-- **The second pure fragment, from an erased typed window, is a `Step_pure` derivation of
`simEnv20T`.** -/
theorem spureT_of_pureFrag20BM {P : Profile} (C : Pure.CvtAgree (E20 B) P) {m : ModuleInst}
    {is is' : List Admin} (h : PureFrag20B P is is') (hok : is.all (okA true m) = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eraseA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  by_cases ha : is.all (okA false m) = true
  · exact StoreGood.spureT_of_spure20
      (Whole.spure_of_pureFrag20B C (map_eraseA_of_okA_false ha ▸ hc) h)
  · exact spureT_of_pureFrag20BM_store h hok ha hc

/-- **The second pure fragment with stores in the tail**, forward in `simEnv20T`. -/
theorem fwdM_pureB {P : Profile} {c c' : Config H} (h : PureFwd20B P c c')
    (hok : c.code.all (okA true c.frame.module) = true) (ht : TypS (storeB P) hn c) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | @mk s f is is' h =>
    have ha' := okA_false_succ_pureFrag20B h hok
    have hc' : TypedV (E20 (storeB P)) adminsTy (.list (adminsToV is')) :=
      Whole.typedV_succ_pureFrag20B ht.code (erase_pureFrag20BM h hok)
    have ht' : TypS (storeB P) hn ⟨s, f, is'⟩ :=
      ⟨ht.state, by simpa [map_eraseA_of_okA_false ha'] using hc'⟩
    refine ⟨ht', (sstepB20T_iff _).2 ?_⟩
    exact StoreRun.sstepT_pure ht.stateT (codeTM ht hok) (codeTM ht' (all_okA_true_of_false ha'))
      (spureT_of_pureFrag20BM (Pure.cvtAgree_simEnv20 (Whole.floatB_storeB P)) h hok ht.code)

/-! ## The three contexts -/

/-- `ctxt-instrs`: the erased typing splits, and the inner step lifts in `simEnv20T`. -/
theorem fwdM_ctx {m m' : ModuleInst} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ []) (ht : TypS B hn ⟨s, f, vals vs ++ is ++ rest⟩)
    (hok : (vals vs ++ is ++ rest).all (okA true m) = true) (hok' : is'.all (okA true m') = true)
    (ih : TypS B hn ⟨s, f, is⟩ → TypS B hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypS B hn ⟨s', f', vals vs ++ is' ++ rest⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, vals vs ++ is ++ rest⟩)
        (configV hn ⟨s', f', vals vs ++ is' ++ rest⟩) := by
  simp only [List.all_append, Bool.and_eq_true] at hok
  have hcode := ht.code
  simp only [List.map_append, StoreGood.map_eraseA_vals] at hcode
  obtain ⟨hvi, hrest⟩ := Whole.typedV_admins_append20_iff.1 hcode
  obtain ⟨hvals, his⟩ := Whole.typedV_admins_append20_iff.1 hvi
  have hin : TypS B hn ⟨s, f, is⟩ := ⟨ht.state, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  refine ⟨⟨ht'.state, ?_⟩, ?_⟩
  · simp only [List.map_append, StoreGood.map_eraseA_vals]
    exact Whole.typedV_admins_append20_iff.2
      ⟨Whole.typedV_admins_append20_iff.2 ⟨hvals, ht'.code⟩, hrest⟩
  · have hs := StoreFix.sstepT_ctxtInstrs hin.stateT ht'.stateT (StoreGood.typedV_valsTy20T vs)
      (codeTM hin hok.1.2) (codeTM ht' hok') (typedT_of_eraseM hok.2 hrest)
      (by simpa [Pure.adminsToV_eq_map, vals] using hne) ((sstepB20T_iff B).1 hst)
    refine (sstepB20T_iff B).2 ?_
    simpa only [configV, Pure.adminsToV_append] using hs

/-- `ctxt-label`: the erased label inverts, and the inner step lifts in `simEnv20T`. -/
theorem fwdM_label {m m' : ModuleInst} {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List V2.Instr} {is is' : List Admin} (ht : TypS B hn ⟨s, f, [.label n cont is]⟩)
    (hok : is.all (okA true m) = true) (hok' : is'.all (okA true m') = true)
    (ih : TypS B hn ⟨s, f, is⟩ → TypS B hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypS B hn ⟨s', f', [.label n cont is']⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, [.label n cont is]⟩)
        (configV hn ⟨s', f', [.label n cont is']⟩) := by
  have hcode := ht.code
  simp only [List.map_cons, List.map_nil, StoreGood.eraseA_label] at hcode
  obtain ⟨hn', hcont, his⟩ := Whole.label_all20 hcode
  have hin : TypS B hn ⟨s, f, is⟩ := ⟨ht.state, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  refine ⟨⟨ht'.state, ?_⟩, ?_⟩
  · simp only [List.map_cons, List.map_nil, StoreGood.eraseA_label]
    exact Whole.typedV_admins_single20_iff.2 (Whole.typedV_adminLabel20_iff.2 ⟨hn', hcont, ht'.code⟩)
  · have hs := StoreRun.sstepT_ctxtLabel hin.stateT ht'.stateT (StoreGood.typedV_nT20T hn')
      (StoreGood.typedV_instrsT20T hcont) (codeTM hin hok) (codeTM ht' hok')
      ((sstepB20T_iff B).1 hst)
    exact (sstepB20T_iff B).2 (by simpa only [configV, adminsToV, adminToV] using hs)

/-- `ctxt-frame`: the erased frame and the state invert; the inner configuration runs under the
inner frame, and its step lifts in `simEnv20T`. -/
theorem fwdM_frame {m m' : ModuleInst} {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (ht : TypS B hn ⟨s, f, [.frame n fi is]⟩)
    (hok : is.all (okA true m) = true) (hok' : is'.all (okA true m') = true)
    (ih : TypS B hn ⟨s, fi, is⟩ → TypS B hn ⟨s', fi', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, fi, is⟩) (configV hn ⟨s', fi', is'⟩)) :
    TypS B hn ⟨s', f, [.frame n fi' is']⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, [.frame n fi is]⟩)
        (configV hn ⟨s', f, [.frame n fi' is']⟩) := by
  have hcode := ht.code
  simp only [List.map_cons, List.map_nil, StoreGood.eraseA_frame] at hcode
  obtain ⟨hn', hfi, his⟩ := Whole.frame_all20 hcode
  obtain ⟨hs, hf⟩ := Whole.typedV_stateV_iff.1 ht.state
  have hin : TypS B hn ⟨s, fi, is⟩ := ⟨Whole.typedV_stateV_iff.2 ⟨hs, hfi⟩, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  obtain ⟨hs', hfi'⟩ := Whole.typedV_stateV_iff.1 ht'.state
  refine ⟨⟨Whole.typedV_stateV_iff.2 ⟨hs', hf⟩, ?_⟩, ?_⟩
  · simp only [List.map_cons, List.map_nil, StoreGood.eraseA_frame]
    exact Whole.typedV_admins_single20_iff.2 (Whole.typedV_adminFrame20_iff.2 ⟨hn', hfi', ht'.code⟩)
  · have hst' := StoreRun.sstepT_ctxtFrame (StoreAgree.typedV_to20T (by decide) hs)
      (StoreAgree.typedV_to20T (by decide) hs') (StoreAgree.typedV_to20T (by decide) hf)
      (StoreAgree.typedV_to20T (by decide) hfi) (StoreAgree.typedV_to20T (by decide) hfi')
      (StoreGood.typedV_nT20T hn') (codeTM hin hok) (codeTM ht' hok') ((sstepB20T_iff B).1 hst)
    exact (sstepB20T_iff B).2 (by simpa only [configV, stateV, adminsToV, adminToV] using hst')

/-! ## The forward theorem -/

/-- One base step, forward. -/
theorem fwdM_base {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseM P c c')
    (ht : TypS (storeB P) hn c) (hok : c.code.all (okA true c.frame.module) = true)
    (hw : WholePages c.store) (hs : StoreOkM c.store) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | old h ha => exact fwdM_old (host := host) h ha ht hw hs
  | pack h => exact fwdM_pack h ht hw
  | pureB h => exact fwdM_pureB h hok ht
  | store h => exact StoreGood.fwdS_store h ht

/-- **The merged fragment forward**: every `Nest20 (BaseM P)` step from a configuration with
`TypS`, covered code, whole pages and a `StoreOkM` store is a step of `simEnv20T (storeB P)`
between the images, and the successor has `TypS`. -/
theorem fwd_nestM {P : Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Nest20 (BaseM P) c c') (ht : TypS (storeB P) hn c)
    (hok : c.code.all (okA true c.frame.module) = true) (hw : WholePages c.store)
    (hs : StoreOkM c.store) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  induction h with
  | base h => exact fwdM_base (host := host) h ht hok hw hs
  | ctx hin hne ih =>
    have hok₁ : (vals _ ++ _ ++ _).all (okA true _) = true := hok
    have hi := okA_ctx_inner hok
    have hok' := (okA_step (host := host) (hin.step fun _ _ h => h.step) hi hs).1
    exact fwdM_ctx hne ht hok₁ hok' fun hin' => ih hin' hi hw hs
  | label hin ih =>
    have hb := bodyOk_labelM hok
    have hok' := (okA_step (host := host) (hin.step fun _ _ h => h.step) hb hs).1
    exact fwdM_label ht hb hok' fun hin' => ih hin' hb hw hs
  | frame hin ih =>
    have hb := bodyOk_frameM hok
    have hok' := (okA_step (host := host) (hin.step fun _ _ h => h.step) hb hs).1
    exact fwdM_frame ht hb hok' fun hin' => ih hin' hb hw hs

end Silmaril.Wasm.SpecTec.Sim20.GoodMerge
