module

public import Silmaril.Proofs.Wasm.LimeCompile.Select.Leaf

/-!
# Erasing `select` annotations: the bisimulation

`step_sim`: every Core 3.0 step is matched from every configuration that erases like its source
(`Sim`), for a host that respects erasure. The relation `selC c = selC d` is symmetric, so this
one simulation gives equal behaviours (`behavioursOf_eq`): finite results (rigid, so carried over
exactly) and divergence (by coinduction).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Select

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril (InfiniteTrace)
open Silmaril.Wasm.LimeCompile.Select

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem flatRig {i : Instr} (h₁ : i.bodies = []) (h₂ : ∀ ts, i ≠ .select ts) :
    AllRig [.plain i] :=
  allRig_one (rigP h₁ h₂)

theorem throwRig (a : Nat) : AllRig (throwing a) :=
  allRig_two (rig_ref _) (rigP rfl fun _ h => nomatch h)

/-- **One step is matched from every configuration erasing like its source.** -/
theorem step_sim (hh : HostResp host) {c c' : Config H} (h : Step P host c c') :
    Sim P host c c' := by
  induction h with
  | parametric h => exact sim_parametric h
  | numeric h => exact sim_pure (numeric_rig h) fun _ => .numeric h
  | vector h => exact sim_pure (vector_rig h) fun _ => .vector h
  | «variable» h => exact sim_variable h
  | table h => exact sim_table h
  | memory h => exact sim_memory h
  | reference h => exact sim_reference h
  | aggregate h => exact sim_aggregate h
  | ctxtInstrs _ hne ih => exact sim_ctxtInstrs ih hne
  | ctxtLabel _ ih => exact sim_ctxtLabel ih
  | ctxtHandler _ ih => exact sim_ctxtHandler ih
  | ctxtFrame _ ih => exact sim_ctxtFrame ih
  | block hbt hm => exact sim_block hbt hm
  | loop hbt hm => exact sim_loop hbt hm
  | ifTrue hc => exact sim_ifTrue hc
  | ifFalse => exact sim_ifFalse
  | labelVals => exact sim_labelVals
  | brLabelZero hl hn => exact sim_brLabelZero hl hn
  | brLabelSucc hl => exact sim_brLabelSucc hl
  | brHandler => exact sim_brHandler
  | brIfTrue hc =>
    exact sim_pure (allRig_cons (rig_constI32 _) (flatRig rfl fun _ h => nomatch h))
      fun _ => .brIfTrue hc
  | brIfFalse =>
    exact sim_pure (allRig_cons (rig_constI32 _) (flatRig rfl fun _ h => nomatch h))
      fun _ => .brIfFalse
  | brTableLt hi =>
    exact sim_pure (allRig_cons (rig_constI32 _) (flatRig rfl fun _ h => nomatch h))
      fun _ => .brTableLt hi
  | brTableGe hi =>
    exact sim_pure (allRig_cons (rig_constI32 _) (flatRig rfl fun _ h => nomatch h))
      fun _ => .brTableGe hi
  | brOnNullNull =>
    exact sim_pure (allRig_cons (rig_ref _) (flatRig rfl fun _ h => nomatch h))
      fun _ => .brOnNullNull
  | brOnNullAddr hv =>
    exact sim_pure (allRig_cons (rig_val _) (flatRig rfl fun _ h => nomatch h))
      fun _ => .brOnNullAddr hv
  | brOnNonNullNull =>
    exact sim_pure (allRig_cons (rig_ref _) (flatRig rfl fun _ h => nomatch h))
      fun _ => .brOnNonNullNull
  | brOnNonNullAddr hv =>
    exact sim_pure (allRig_cons (rig_val _) (flatRig rfl fun _ h => nomatch h))
      fun _ => .brOnNonNullAddr hv
  | brOnCastSucceed h =>
    exact sim_funcs (allRig_cons (rig_ref _) (flatRig rfl fun _ h => nomatch h)) rfl
      fun _ hF => .brOnCastSucceed ((refOk_funcs_iff hF).mpr h)
  | brOnCastFail h =>
    exact sim_funcs (allRig_cons (rig_ref _) (flatRig rfl fun _ h => nomatch h)) rfl
      fun _ hF => .brOnCastFail fun h' => h ((refOk_funcs_iff hF).mp h')
  | brOnCastFailSucceed h =>
    exact sim_funcs (allRig_cons (rig_ref _) (flatRig rfl fun _ h => nomatch h)) rfl
      fun _ hF => .brOnCastFailSucceed ((refOk_funcs_iff hF).mpr h)
  | brOnCastFailFail h =>
    exact sim_funcs (allRig_cons (rig_ref _) (flatRig rfl fun _ h => nomatch h)) rfl
      fun _ hF => .brOnCastFailFail fun h' => h ((refOk_funcs_iff hF).mp h')
  | call hx hf => exact sim_call hx hf
  | callRefNull hc =>
    exact sim_pure (allRig_two (rig_ref _) (rig_isCallRef hc)) fun _ => .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact sim_callRefFunc hc hf he hn hcode
  | callRefHost hc hf he hn hcode hhost => exact sim_callRefHost hh hc hf he hn hcode hhost
  | callRefHostDiv hc hf he hn hcode hhost =>
    exact sim_callRefHostDiv hh hc hf he hn hcode hhost
  | returnCall hx hf => exact sim_returnCall hx hf
  | returnCallRefLabel hc => exact sim_returnCallRefLabel hc
  | returnCallRefHandler hc => exact sim_returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact sim_returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact sim_returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact sim_pure (flatRig rfl fun _ h => nomatch h) fun _ => .callIndirect
  | returnCallIndirect =>
    exact sim_pure (flatRig rfl fun _ h => nomatch h) fun _ => .returnCallIndirect
  | frameVals hn => exact sim_pure (allRig_one (rig_frame (allRig_vals _))) fun _ => .frameVals hn
  | returnFrame hn => exact sim_returnFrame hn
  | returnLabel => exact sim_returnLabel
  | returnHandler => exact sim_returnHandler
  | throw ht he hn =>
    exact sim_funcs (allRig_append (allRig_vals _) (flatRig rfl fun _ h => nomatch h)) rfl
      fun _ _ => .throw ht he hn
  | throwRefNull =>
    exact sim_pure (allRig_two (rig_ref _) (rigP rfl fun _ h => nomatch h)) fun _ => .throwRefNull
  | throwRefInstrs hne => exact sim_throwRefInstrs hne
  | throwRefLabel => exact sim_throwRefLabel
  | throwRefFrame => exact sim_pure (allRig_one (rig_frame (throwRig _))) fun _ => .throwRefFrame
  | throwRefHandlerEmpty =>
    exact sim_pure (allRig_one (rig_handler (throwRig _))) fun _ => .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht =>
    exact sim_funcs (allRig_one (rig_handler (throwRig _))) rfl
      fun _ _ => .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht =>
    exact sim_funcs (allRig_one (rig_handler (throwRig _))) rfl
      fun _ _ => .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll =>
    exact sim_pure (allRig_one (rig_handler (throwRig _))) fun _ => .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef =>
    exact sim_pure (allRig_one (rig_handler (throwRig _))) fun _ => .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h =>
    exact sim_funcs (allRig_one (rig_handler (throwRig _))) rfl
      fun _ _ => .throwRefHandlerNext h
  | tryTable hbt hm => exact sim_tryTable hbt hm
  | handlerVals => exact sim_pure (allRig_one (rig_handler (allRig_vals _))) fun _ => .handlerVals
  | trapInstrs hne => exact sim_trapInstrs hne
  | trapLabel => exact sim_trapLabel
  | trapHandler =>
    exact sim_pure (allRig_one (rig_handler (allRig_one rig_trap))) fun _ => .trapHandler
  | trapFrame => exact sim_pure (allRig_one (rig_frame (allRig_one rig_trap))) fun _ => .trapFrame

/-! ## Runs and behaviours -/

theorem steps_sim (hh : HostResp host) {c c' : Config H} (h : Steps P host c c') :
    ∀ d, selC c = selC d → ∃ d', Steps P host d d' ∧ selC c' = selC d' := by
  induction h with
  | refl => exact fun d hd => ⟨d, .refl, hd⟩
  | tail _ hstep ih =>
    intro d hd
    obtain ⟨d₁, hs₁, h₁⟩ := ih d hd
    obtain ⟨d₂, hs₂, h₂⟩ := step_sim hh hstep d₁ h₁
    exact ⟨d₂, hs₁.tail hs₂, h₂⟩

theorem diverges_sim (hh : HostResp host) {c d : Config H} (h : Diverges P host c)
    (hd : selC c = selC d) : Diverges P host d := by
  refine InfiniteTrace.coinduct (fun d => ∃ c, selC c = selC d ∧ Diverges P host c) ?_ ⟨c, hd, h⟩
  rintro d ⟨c, hcd, hc⟩
  obtain ⟨c₁, hs, hc₁⟩ := hc.unfold
  obtain ⟨d₁, hs', h₁⟩ := step_sim hh hs d hcd
  exact ⟨d₁, hs', c₁, h₁, hc₁⟩

theorem allRig_result (r : Result) : AllRig r.toAdmin := by
  cases r with
  | values vs => exact allRig_vals vs
  | throw a => exact throwRig a
  | trap => exact allRig_one rig_trap

theorem behavioursOf_sub (hh : HostResp host) {c d : Config H} (hd : selC c = selC d) :
    behavioursOf P host c ⊆ behavioursOf P host d := by
  rintro b (⟨c', r, hs, hr, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨d', hs', h'⟩ := steps_sim hh hs d hd
    have hcode : selAs d'.code = selAs r.toAdmin := by
      rw [← hr]
      exact ((selC_iff.mp h').2.2).symm
    exact Or.inl ⟨d', r, hs', eq_of_selAs_rig (allRig_result r) hcode, rfl⟩
  · exact Or.inr ⟨rfl, diverges_sim hh hdiv hd⟩

/-- **Configurations equal after erasure have the same behaviours.** -/
theorem behavioursOf_eq (hh : HostResp host) {c d : Config H} (hd : selC c = selC d) :
    behavioursOf P host c = behavioursOf P host d :=
  Set.Subset.antisymm (behavioursOf_sub hh hd) (behavioursOf_sub hh hd.symm)

theorem invoke_sel {s t : Store H} (h : selS s = selS t) (a : Nat) (vs : List Val) :
    selC (invoke s a vs) = selC (invoke t a vs) := by
  have hty : (s.funcs[a]?).map FuncInst.type = (t.funcs[a]?).map FuncInst.type := by
    rw [← List.getElem?_map, ← List.getElem?_map, types_eq_of_selS h]
  simp only [invoke, selC, h, hty]

/-- **Stores equal after erasure have the same behaviours at every call.** -/
theorem behaviours_eq (hh : HostResp host) {s t : Store H} (h : selS s = selS t) (a : Nat)
    (vs : List Val) : behaviours P host s a vs = behaviours P host t a vs :=
  behavioursOf_eq hh (invoke_sel h a vs)

end Silmaril.Proofs.Wasm.LimeCompile.Select
