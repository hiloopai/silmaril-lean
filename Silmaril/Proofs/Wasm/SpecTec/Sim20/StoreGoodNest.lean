module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodConcat
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodCover

/-!
# The storing fragment forward in `simEnv20T`, nested under every context

The invariant's typing part is `TypS`: the state is typed in the original `simEnv20` (the store's
functions are store-free), and the **erased** code is a typed `admininstr*` there. The code
itself is then typed in `simEnv20T` (`StoreGood.typedT_of_erase`).

* `typS_old`, `fwdS_old`: a store-free window 's fragment is typed in `simEnv20` and
  steps by `Whole.fwdBase20_fwdD`; its successor is store-free, and the step moves to `simEnv20T`
  by `ElseAgree.sstepB20T_of_sstepB20S'`.
* `erase_pureFrag20B`, `spureT_of_pureFrag20B`: a step of the second pure fragment erases to a
  step to the same successor (only a `br`, `return` or `trap-vals` tail is changed), which gives
  subject reduction; the forward derivation is round 3's when the window is store-free, and
  `spureT_brZero`, … when the tail holds a store.
* the six store steps: `StoreAgree.sstepT_storeTop20` from the state typed in `simEnv20`.
* the three contexts: inversions of the erased typing in `simEnv20` (`Whole.typedV_admins_
  append20_iff`, `typedV_adminLabel20_iff`, `typedV_adminFrame20_iff`, `typedV_stateV_iff`),
  and the structural rules of `simEnv20T` (`StoreFix.sstepT_ctxtInstrs`,
  `StoreRun.sstepT_ctxtLabel`, `sstepT_ctxtFrame`) on the typing lifted by `typedT_of_erase`.
* **`fwd_nestS`**: every `Nest20 (BaseS P)` step from a configuration with `TypS`, covered code
  with stores, whole pages and a covered store is a step of `simEnv20T (storeB P)` between the
  images, and the successor has `TypS`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreGood

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV SPure stateT storeT frameT nT instrsT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy valsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T sstepB20T_iff)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk adminOk Nest20 FwdStep20D PureFwd20B PureFrag20B
  StoreTop20 StoreOk WholePages storeB typed20_iff)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-- **The typing part of the storing invariant**: the state typed in `simEnv20`, and the code
typed there after its administrative stores are erased. -/
structure TypS (B : Builtins) (hn : H → String) (c : Config H) : Prop where
  state : TypedV (E20 B) stateT (stateV hn c.store c.frame)
  code : TypedV (E20 B) adminsTy (.list (adminsToV (c.code.map eraseA)))

/-- The image of a configuration with `TypS` and covered code with stores is typed in
`simEnv20T`: its state and its code. -/
theorem TypS.codeT {c : Config H} (h : TypS B hn c) (hok : c.code.all adminOkS = true) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV c.code)) :=
  typedT_of_erase hok h.code

theorem TypS.stateT {c : Config H} (h : TypS B hn c) :
    TypedV (simEnv20T B) stateT (stateV hn c.store c.frame) :=
  StoreAgree.typedV_to20T (by decide) h.state

/-- `TypS` of store-free code is `Typed20`. -/
theorem TypS.typed20 {c : Config H} (h : TypS B hn c) (ha : c.code.all adminOk = true) :
    Typed20 (E20 B) hn c :=
  typed20_iff.2 ⟨h.state, by simpa [map_eraseA_of_adminOk ha] using h.code⟩

theorem typS_of_typed20 {c : Config H} (h : Typed20 (E20 B) hn c) (ha : c.code.all adminOk = true) :
    TypS B hn c :=
  ⟨(typed20_iff.1 h).1, by simpa [map_eraseA_of_adminOk ha] using (typed20_iff.1 h).2⟩

/-! ## Moving a `simEnv20` derivation to `simEnv20T` -/

/-- A `Step_pure` derivation of the original script is one of `simEnv20T`. -/
theorem spureT_of_spure20 {is js : List Value} (h : SPure (E20 B) is js) : SPure (simEnv20T B) is js :=
  StoreAgree.dderives_of (StoreAgree.envSame20T B) (StoreAgree.typRepair20T B)
    (ElseAgree.elseAgree20T B) ((RelFree.spure20S_iff B _ _).2 h)

/-! ## The base: store-free windows 's fragment -/

/-- **A store-free window 's fragment**, forward in `simEnv20T`. -/
theorem fwdS_old {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20D P c c') (ha : c.code.all adminOk = true) (ht : TypS (storeB P) hn c)
    (hw : WholePages c.store) (hs : StoreOk c.store) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hT := ht.typed20 ha
  have F := Whole.fwdBase20_fwdD (H := H) (hn := hn) P
  have ha' : c'.code.all adminOk = true := (Whole.adminOk_step (host := host) h.step ha hs).1
  exact ⟨typS_of_typed20 (F.sr c c' hT h) ha', ElseAgree.sstepB20T_of_sstepB20S' (F.fwd c c' hT hw h)⟩

/-! ## The base: the second pure fragment with stores in the tail -/

theorem map_eraseA_expression (is : List V2.Instr) :
    (expression is).map eraseA = expression (is.map eraseI) := by
  simp [expression, Function.comp_def]

/-- The successor of the second pure fragment from covered code with stores is store-free. -/
theorem adminOk_succ_pureFrag20B {P : Profile} {is is' : List Admin} (h : PureFrag20B P is is')
    (hok : is.all adminOkS = true) : is'.all adminOk = true := by
  cases h <;> simp_all [Whole.ctrlOk, storeOkI, List.all_append]

/-- Erasure keeps a step of the second pure fragment whose window holds a store. -/
theorem erase_pureFrag20B_store {P : Profile} {is is' : List Admin} (h : PureFrag20B P is is')
    (hok : is.all adminOkS = true) (ha : ¬ is.all adminOk = true) :
    PureFrag20B P (is.map eraseA) is' := by
  cases h with
  | brZero hl hn =>
    simpa only [List.map_cons, List.map_nil, eraseA_label, List.map_append, map_eraseA_vals,
      map_eraseA_expression, eraseA_plain, eraseI] using PureFrag20B.brZero (P := P) (is := _) hl hn
  | brSucc hl =>
    simpa only [List.map_cons, List.map_nil, eraseA_label, List.map_append, map_eraseA_vals,
      map_eraseA_expression, eraseA_plain, eraseI] using PureFrag20B.brSucc (P := P) (is := _) hl
  | returnFrame hn =>
    simpa only [List.map_cons, List.map_nil, eraseA_frame, List.map_append, map_eraseA_vals,
      map_eraseA_expression, eraseA_plain, eraseI] using PureFrag20B.returnFrame (P := P) (is := _) hn
  | returnLabel =>
    simpa only [List.map_cons, List.map_nil, eraseA_label, List.map_append, map_eraseA_vals,
      map_eraseA_expression, eraseA_plain, eraseI] using PureFrag20B.returnLabel (P := P) (is := _)
  | trapVals hne =>
    simpa only [List.map_append, map_eraseA_vals, map_eraseA_expression, List.map_cons,
      List.map_nil, eraseA_trap] using PureFrag20B.trapVals (P := P) (by simpa [expression] using hne)
  | _ => simp_all [Whole.ctrlOk, storeOkI, aref]

/-- **Erasure keeps a step of the second pure fragment, with the same successor.** -/
theorem erase_pureFrag20B {P : Profile} {is is' : List Admin} (h : PureFrag20B P is is')
    (hok : is.all adminOkS = true) : PureFrag20B P (is.map eraseA) is' := by
  by_cases ha : is.all adminOk = true
  · exact (map_eraseA_of_adminOk ha).symm ▸ h
  · exact erase_pureFrag20B_store h hok ha

/-- The tail of a typed erased body, moved to `simEnv20T` as an `instr*`. -/
theorem tailT_of_erase {l : List Admin} {is : List V2.Instr}
    (hok : (l ++ expression is).all adminOkS = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ((l ++ expression is).map eraseA)))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV (expression is))) := by
  have hT := typedT_of_erase hok hc
  rw [Pure.adminsToV_append] at hT
  refine typedV_instrs_of_admins20T (Sim.typedV_list_iff.2 fun u hu => ?_)
  exact Sim.typedV_list_iff.1 hT u (List.mem_append_right _ hu)

/-- The parts of an erased typed label, the continuation and arity moved to `simEnv20T`. -/
theorem labelT_of_erase {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ([Admin.label n cont body].map eraseA)))) :
    TypedV (simEnv20T B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont)) ∧
      TypedV (E20 B) adminsTy (.list (adminsToV (body.map eraseA))) := by
  simp only [List.map_cons, List.map_nil, eraseA_label] at hc
  obtain ⟨h₁, h₂, h₃⟩ := Whole.label_all20 hc
  exact ⟨typedV_nT20T h₁, typedV_instrsT20T h₂, h₃⟩

/-- The parts of an erased typed frame, the arity and frame moved to `simEnv20T`. -/
theorem frameT_of_erase {n : Nat} {fr : Frame} {body : List Admin}
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV ([Admin.frame n fr body].map eraseA)))) :
    TypedV (simEnv20T B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20T B) Pure.frameT (frameV fr) ∧
      TypedV (E20 B) adminsTy (.list (adminsToV (body.map eraseA))) := by
  simp only [List.map_cons, List.map_nil, eraseA_frame] at hc
  obtain ⟨h₁, h₂, h₃⟩ := Whole.frame_all20 hc
  exact ⟨typedV_nT20T h₁, StoreAgree.typedV_to20T (by decide) h₂, h₃⟩

/-- `br-zero` in `simEnv20T` from an erased typed window. -/
theorem spureT_brZeroE {n : Nat} {cont : List V2.Instr} {vs' vs : List Val} {l : LabelIdx}
    {is₀ : List V2.Instr} (hl : l.toNat = 0) (hn : vs.length = n)
    (hok : [Admin.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)].all
      adminOkS = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV
      ([Admin.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)].map eraseA)))) :
    SPure (simEnv20T B)
      (adminsToV [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is₀)])
      (adminsToV (vals vs ++ expression cont)) := by
  subst hn
  obtain ⟨hn', hcont, hbody⟩ := labelT_of_erase hc
  rw [← Pure.vals_append]
  exact spureT_brZero hl hn' hcont (tailT_of_erase (bodyOk_label hok) hbody)

/-- `return-frame` in `simEnv20T` from an erased typed window. -/
theorem spureT_returnFrameE {n : Nat} {fr : Frame} {vs' vs : List Val} {is₀ : List V2.Instr}
    (hn : vs.length = n)
    (hok : [Admin.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)].all
      adminOkS = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV
      ([Admin.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)].map eraseA)))) :
    SPure (simEnv20T B)
      (adminsToV [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is₀)])
      (adminsToV (vals vs)) := by
  subst hn
  obtain ⟨hn', hfr, hbody⟩ := frameT_of_erase hc
  rw [← Pure.vals_append]
  exact spureT_returnFrame hn' hfr (tailT_of_erase (bodyOk_frame hok) hbody)

/-- A window with a store is one of the five concatenation rules, in `simEnv20T`. -/
theorem spureT_of_pureFrag20B_store {P : Profile} {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all adminOkS = true) (ha : ¬ is.all adminOk = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eraseA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  cases h with
  | brZero hl hn => exact spureT_brZeroE hl hn hok hc
  | brSucc hl =>
    exact spureT_brSucc hl (labelT_of_erase hc).1 (labelT_of_erase hc).2.1
      (tailT_of_erase (bodyOk_label hok) (labelT_of_erase hc).2.2)
  | returnFrame hn => exact spureT_returnFrameE hn hok hc
  | returnLabel =>
    exact spureT_returnLabel (labelT_of_erase hc).1 (labelT_of_erase hc).2.1
      (tailT_of_erase (bodyOk_label hok) (labelT_of_erase hc).2.2)
  | trapVals hne => exact spureT_trapVals hne (tailT_of_erase hok hc)
  | _ => simp_all [Whole.ctrlOk, storeOkI, aref]

/-- **The second pure fragment, from an erased typed window, is a `Step_pure` derivation of
`simEnv20T`.** -/
theorem spureT_of_pureFrag20B {P : Profile} (C : Pure.CvtAgree (E20 B) P) {is is' : List Admin}
    (h : PureFrag20B P is is') (hok : is.all adminOkS = true)
    (hc : TypedV (E20 B) adminsTy (.list (adminsToV (is.map eraseA)))) :
    SPure (simEnv20T B) (adminsToV is) (adminsToV is') := by
  by_cases ha : is.all adminOk = true
  · exact spureT_of_spure20 (Whole.spure_of_pureFrag20B C (map_eraseA_of_adminOk ha ▸ hc) h)
  · exact spureT_of_pureFrag20B_store h hok ha hc

/-- **The second pure fragment with stores in the tail**, forward in `simEnv20T`. -/
theorem fwdS_pureB {P : Profile} {c c' : Config H} (h : PureFwd20B P c c')
    (hok : c.code.all adminOkS = true) (ht : TypS (storeB P) hn c) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | @mk s f is is' h =>
    have ha' := adminOk_succ_pureFrag20B h hok
    have hc' : TypedV (E20 (storeB P)) adminsTy (.list (adminsToV is')) :=
      Whole.typedV_succ_pureFrag20B ht.code (erase_pureFrag20B h hok)
    have ht' : TypS (storeB P) hn ⟨s, f, is'⟩ :=
      ⟨ht.state, by simpa [map_eraseA_of_adminOk ha'] using hc'⟩
    refine ⟨ht', (sstepB20T_iff _).2 ?_⟩
    exact StoreRun.sstepT_pure ht.stateT (ht.codeT hok)
      (ht'.codeT (all_adminOkS_of_adminOk ha'))
      (spureT_of_pureFrag20B (Pure.cvtAgree_simEnv20 (Whole.floatB_storeB P)) h hok ht.code)

/-! ## The base: the six store steps -/

/-- **The scalar stores**, forward in `simEnv20T`, from a state typed in `simEnv20`. -/
theorem fwdS_store {P : Profile} {c c' : Config H} (h : StoreTop20 c c') (ht : TypS (storeB P) hn c) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  refine ⟨⟨Whole.typedV_state_storeTop20 ht.state h, ?_⟩,
    StoreAgree.sstepT_storeTop20 (Whole.floatB_storeB P) (Whole.laneCalls20_storeB P)
      (Whole.nbytes20_storeB P) ht.state h⟩
  cases h with
  | intTrap _ _ _ | floatTrap _ _ _ | packTrap _ _ _ => exact Whole.typedV_admins_trap20
  | intVal _ _ _ | floatVal _ _ _ | packVal _ _ _ => exact Whole.typedV_admins_nil20

/-! ## The three contexts -/

theorem typedV_valsTy20T (vs : List Val) :
    TypedV (simEnv20T B) valsTy (.list (adminsToV (vals vs))) := by
  rw [Pure.adminsToV_vals]
  exact StoreAgree.typedV_list_to20T (by decide) (Whole.typedV_vals20 vs)

/-- `ctxt-instrs`: the erased typing splits, and the inner step lifts in `simEnv20T`. -/
theorem fwdS_ctx {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (ht : TypS B hn ⟨s, f, vals vs ++ is ++ rest⟩)
    (hok : (vals vs ++ is ++ rest).all adminOkS = true) (hok' : is'.all adminOkS = true)
    (ih : TypS B hn ⟨s, f, is⟩ → TypS B hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypS B hn ⟨s', f', vals vs ++ is' ++ rest⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, vals vs ++ is ++ rest⟩)
        (configV hn ⟨s', f', vals vs ++ is' ++ rest⟩) := by
  simp only [List.all_append, Bool.and_eq_true] at hok
  have hcode := ht.code
  simp only [List.map_append, map_eraseA_vals] at hcode
  obtain ⟨hvi, hrest⟩ := Whole.typedV_admins_append20_iff.1 hcode
  obtain ⟨hvals, his⟩ := Whole.typedV_admins_append20_iff.1 hvi
  have hin : TypS B hn ⟨s, f, is⟩ := ⟨ht.state, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  refine ⟨⟨ht'.state, ?_⟩, ?_⟩
  · simp only [List.map_append, map_eraseA_vals]
    exact Whole.typedV_admins_append20_iff.2
      ⟨Whole.typedV_admins_append20_iff.2 ⟨hvals, ht'.code⟩, hrest⟩
  · have hs := StoreFix.sstepT_ctxtInstrs hin.stateT ht'.stateT (typedV_valsTy20T vs)
      (hin.codeT hok.1.2) (ht'.codeT hok') (typedT_of_erase hok.2 hrest)
      (by simpa [Pure.adminsToV_eq_map, vals] using hne) ((sstepB20T_iff B).1 hst)
    refine (sstepB20T_iff B).2 ?_
    simpa only [configV, Pure.adminsToV_append] using hs

/-- `ctxt-label`: the erased label inverts, and the inner step lifts in `simEnv20T`. -/
theorem fwdS_label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List V2.Instr}
    {is is' : List Admin} (ht : TypS B hn ⟨s, f, [.label n cont is]⟩)
    (hok : is.all adminOkS = true) (hok' : is'.all adminOkS = true)
    (ih : TypS B hn ⟨s, f, is⟩ → TypS B hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypS B hn ⟨s', f', [.label n cont is']⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, [.label n cont is]⟩)
        (configV hn ⟨s', f', [.label n cont is']⟩) := by
  have hcode := ht.code
  simp only [List.map_cons, List.map_nil, eraseA_label] at hcode
  obtain ⟨hn', hcont, his⟩ := Whole.label_all20 hcode
  have hin : TypS B hn ⟨s, f, is⟩ := ⟨ht.state, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  refine ⟨⟨ht'.state, ?_⟩, ?_⟩
  · simp only [List.map_cons, List.map_nil, eraseA_label]
    exact Whole.typedV_admins_single20_iff.2 (Whole.typedV_adminLabel20_iff.2 ⟨hn', hcont, ht'.code⟩)
  · have hs := StoreRun.sstepT_ctxtLabel hin.stateT ht'.stateT (typedV_nT20T hn')
      (typedV_instrsT20T hcont) (hin.codeT hok) (ht'.codeT hok') ((sstepB20T_iff B).1 hst)
    exact (sstepB20T_iff B).2 (by simpa only [configV, adminsToV, adminToV] using hs)

/-- `ctxt-frame`: the erased frame and the state invert; the inner configuration runs under the
inner frame, and its step lifts in `simEnv20T`. -/
theorem fwdS_frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ht : TypS B hn ⟨s, f, [.frame n fi is]⟩)
    (hok : is.all adminOkS = true) (hok' : is'.all adminOkS = true)
    (ih : TypS B hn ⟨s, fi, is⟩ → TypS B hn ⟨s', fi', is'⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, fi, is⟩) (configV hn ⟨s', fi', is'⟩)) :
    TypS B hn ⟨s', f, [.frame n fi' is']⟩ ∧
      SStepB (simEnv20T B) (configV hn ⟨s, f, [.frame n fi is]⟩)
        (configV hn ⟨s', f, [.frame n fi' is']⟩) := by
  have hcode := ht.code
  simp only [List.map_cons, List.map_nil, eraseA_frame] at hcode
  obtain ⟨hn', hfi, his⟩ := Whole.frame_all20 hcode
  obtain ⟨hs, hf⟩ := Whole.typedV_stateV_iff.1 ht.state
  have hin : TypS B hn ⟨s, fi, is⟩ := ⟨Whole.typedV_stateV_iff.2 ⟨hs, hfi⟩, his⟩
  obtain ⟨ht', hst⟩ := ih hin
  obtain ⟨hs', hfi'⟩ := Whole.typedV_stateV_iff.1 ht'.state
  refine ⟨⟨Whole.typedV_stateV_iff.2 ⟨hs', hf⟩, ?_⟩, ?_⟩
  · simp only [List.map_cons, List.map_nil, eraseA_frame]
    exact Whole.typedV_admins_single20_iff.2 (Whole.typedV_adminFrame20_iff.2 ⟨hn', hfi', ht'.code⟩)
  · have hst' := StoreRun.sstepT_ctxtFrame (StoreAgree.typedV_to20T (by decide) hs)
      (StoreAgree.typedV_to20T (by decide) hs') (StoreAgree.typedV_to20T (by decide) hf)
      (StoreAgree.typedV_to20T (by decide) hfi) (StoreAgree.typedV_to20T (by decide) hfi')
      (typedV_nT20T hn') (hin.codeT hok) (ht'.codeT hok') ((sstepB20T_iff B).1 hst)
    exact (sstepB20T_iff B).2 (by simpa only [configV, stateV, adminsToV, adminToV] using hst')

/-! ## The forward theorem -/

/-- One base step, forward. -/
theorem fwdS_base {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseS P c c')
    (ht : TypS (storeB P) hn c) (hok : c.code.all adminOkS = true) (hw : WholePages c.store)
    (hs : StoreOk c.store) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  cases h with
  | old h ha => exact fwdS_old (host := host) h ha ht hw hs
  | pureB h => exact fwdS_pureB h hok ht
  | store h => exact fwdS_store h ht

/-- **The storing fragment forward**: every `Nest20 (BaseS P)` step from a configuration with
`TypS`, covered code with stores, whole pages and a covered store is a step of
`simEnv20T (storeB P)` between the images, and the successor has `TypS`. -/
theorem fwd_nestS {P : Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Nest20 (BaseS P) c c') (ht : TypS (storeB P) hn c) (hok : c.code.all adminOkS = true)
    (hw : WholePages c.store) (hs : StoreOk c.store) :
    TypS (storeB P) hn c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  induction h with
  | base h => exact fwdS_base (host := host) h ht hok hw hs
  | ctx hin hne ih =>
    have hok₁ : (vals _ ++ _ ++ _).all adminOkS = true := hok
    simp only [List.all_append, Bool.and_eq_true] at hok
    have hok' := (adminOkS_step (host := host) (hin.step fun _ _ h => h.step) hok.1.2 hs).1
    exact fwdS_ctx hne ht hok₁ hok' fun hin' => ih hin' hok.1.2 hw hs
  | label hin ih =>
    have hb := bodyOk_label hok
    have hok' := (adminOkS_step (host := host) (hin.step fun _ _ h => h.step) hb hs).1
    exact fwdS_label ht hb hok' fun hin' => ih hin' hb hw hs
  | frame hin ih =>
    have hb := bodyOk_frame hok
    have hok' := (adminOkS_step (host := host) (hin.step fun _ _ h => h.step) hb hs).1
    exact fwdS_frame ht hb hok' fun hin' => ih hin' hb hw hs

end Silmaril.Wasm.SpecTec.Sim20.StoreGood
