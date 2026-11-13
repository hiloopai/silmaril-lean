module

public import Silmaril.Wasm.LimeCompile.TailSim.Defs
public import Silmaril.Wasm.Execution.Core.Sim.TypedPrefix
public import Silmaril.Wasm.Execution.Core.Sim.TypedProgress
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# The two-way simulation of the tail-call rewrite: typing facts

The simulation carries the typing of both configurations (silmaril's `ContextTyped`: the code
sits at the active hole of a well-typed whole configuration). This file proves what it uses:

* `CT_step`, `CT_steps`, `CT_trans`: typing is kept by steps under a host meeting `HostOk`
  (silmaril's `Step.preservation` under the active context);
* `leaf_typing`, `frame_typing`: the active instruction of a typed fragment is typed, and a
  typed frame has a body typed with the frame's return type, of length the frame's arity;
* **`frameAddr_arity`**: at `return_call_ref-frame-addr` in a typed frame of arity `k`, the
  callee returns `k` values, and the `CALL_REF` the source continues with has an annotation `d`
  with the callee's parameter and result counts (`Arity d k vs`). This is the arity invariant
  that the target's `call; return` needs. The proof is the first half of silmaril's
  `PC.pres_returnCallRefFrameAddr` (copied and cut at the subtyping facts);
* **`callRef_types`**: at a typed `CALL_REF d` of a Wasm or host function, the callee's
  parameter and result counts are those of `d`, and the arguments are typed (the first half of
  silmaril's `PC.callRef_front`, copied).

New proofs (the two inversions copy parts of silmaril's soundness proofs).
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (ContextTyped ActiveCtx)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Typing along steps -/

theorem CT_step (hhost : HostOk host) {c c' : Config H} (h : ContextTyped c)
    (hs : Step P host c c') : ContextTyped c' := by
  obtain ⟨E, ts, h⟩ := h
  exact ⟨E, ts, (Step.preservation hhost h (E.step hs)).1⟩

theorem CT_steps (hhost : HostOk host) {c c' : Config H} (h : ContextTyped c)
    (hs : Steps P host c c') : ContextTyped c' := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact CT_step hhost ih hs

theorem CT_trans (hhost : HostOk host) {c c' : Config H} (h : ContextTyped c)
    (hs : Relation.TransGen (Step P host) c c') : ContextTyped c' :=
  CT_steps hhost h hs.to_reflTransGen

/-! ## Leaves and frames -/

theorem prefix_typing' {s : Store H} {C : Context} {body rest : List Admin}
    {it : InstrType} (hC : C.Wf) (h : AdminsOk s C (body ++ rest) it) :
    ∃ xs ts, AdminsOk s C body ⟨it.params, xs, ts⟩ := by
  by_cases hr : rest = []
  · subst rest
    exact ⟨it.inits, it.results, by simpa using h⟩
  · obtain ⟨ts, xs, _, hb, _, _⟩ := AdminsOk.split h hC body rest rfl hr
    exact ⟨xs, ts, hb⟩

/-- The active instruction of a typed fragment is typed. -/
theorem leaf_typing {s : Store H} {f : Frame} {V : List Val} {a : Admin} {L : List Admin}
    (h : ContextTyped ⟨s, f, vals V ++ a :: L⟩) :
    StoreOk s ∧ ∃ C it, C.Wf ∧ AdminOk s C a it := by
  obtain ⟨C, ts, xs, hs, hC, -, hcode⟩ := h.fragment_ctx
  obtain ⟨_, xs₁, _, hp, ht, _⟩ :=
    AdminsOk.split hcode hC (vals V) (a :: L) rfl (List.cons_ne_nil _ _)
  have hC' := hC.initLocals xs₁
  obtain ⟨_, _, hsingle⟩ := prefix_typing' hC' (body := [a]) (by simpa using ht)
  obtain ⟨_, it', ha, _⟩ := AdminsOk.single_inv hC'.types hsingle
  exact ⟨hs, _, it', hC', ha⟩

/-- **A typed frame**: its body is typed with the frame's return type, whose length is the
frame's arity. -/
theorem frame_typing {s : Store H} {f fi : Frame} {k : Nat} {V : List Val} {b L : List Admin}
    (h : ContextTyped ⟨s, f, vals V ++ .frame k fi b :: L⟩) :
    StoreOk s ∧ ∃ (C' : Context) (ts : List CValType), FrameOk s fi C' ∧ ts.length = k ∧
      ResultOk {} ts ∧ AdminsOk s { C' with return_ := some ts } b (.plain [] ts) := by
  obtain ⟨hs, C, it, -, ha⟩ := leaf_typing h
  cases ha with
  | frame hf hn hb hok => exact ⟨hs, _, _, hf, hn, hok, hb⟩

/-! ## The arity at `return_call_ref-frame-addr` -/

/-- **The arity invariant.** In a typed frame of arity `k` about to leave by
`return_call_ref-frame-addr` to the function `a`, the callee returns `k` values, and the
`CALL_REF` the source continues with is annotated by a type `d` with the callee's parameter and
result counts. -/
theorem frameAddr_arity {s : Store H} {f fi : Frame} {k : Nat} {V vs' vs : List Val} {a : Nat}
    {c : Admin} {rest L : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hT : ContextTyped ⟨s, f, vals V ++
      .frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) :: L⟩)
    (hcr : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length) :
    rs.length = k ∧ ∃ d, c.retToCallIn fi.module = .callRefType d ∧ Arity d k vs ∧
      ∃ psd rsd : Ty (.list .val), Expand d (.func psd rsd) := by
  obtain ⟨hs, C', ts, hfr, hk, hts, hb⟩ := frame_typing hT
  have hsT : PC.StoreTypesOk s := ⟨hs.structsClosed, hs.arraysClosed⟩
  have hW := PC.frame_ctx_wf hs hsT hfr hts
  have hΔ3 : PC.TypesOk ({ C' with return_ := some ts } : Context).toTypeCtx := by
    show PC.TypesOk C'.toTypeCtx
    exact PC.FrameOk.typesOk' hfr
  have hR : C'.recs = [] := hfr.recs_nil
  have e0 : vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest =
      (vals (vs' ++ vs ++ [.ref (.func a)]) ++ [c]) ++ rest := by
    simp [vals, Val.toAdmin]
  rw [e0] at hb
  obtain ⟨m, ys₁, ys₂, hpre, -, -⟩ := AdminsOk.append_inv hW (.inr (PC.resultOk_weaken hts)) hb
  obtain ⟨tvs'', it₁, M, T, hc1, hvs'', hsub, hM, hT', hMs, -, -⟩ :=
    PC.redex_rep hW (PC.returnCallRef_inits hcr) hpre
  obtain ⟨dc, psc, rsc, rs', t₃, t₄, hec, hret, hrs, hok, rfl, h1, h2⟩ :=
    PC.inv_returnCallRef hcr hc1
  simp only [Option.some.injEq] at hret
  subst hret
  have hdc : TyOk {} dc := by
    cases c with
    | plain i =>
      cases i <;> simp [Admin.IsReturnCallRef] at hcr
      exact hΔ3.get (h1 _ rfl)
    | returnCallRefType d =>
      obtain ⟨rfl, -⟩ := h2 _ rfl
      obtain ⟨-, hd⟩ := h2 _ rfl
      exact hd
    | _ => simp [Admin.IsReturnCallRef] at hcr
  have hpc := Expand.func_ok hdc hec
  obtain ⟨tvsA, trtl, rfl, hvsA, htr⟩ := PC.forall₂_split_left hvs''
  obtain ⟨trt, rfl, htr1⟩ : ∃ trt, trtl = [trt] ∧ ValOk s (.ref (.func a)) trt := by
    cases htr with | cons h hnil => cases hnil; exact ⟨_, rfl, h⟩
  have hall : ResultSub ({ C' with return_ := some ts } : Context).toTypeCtx
      (tvsA ++ [trt]) (((T ++ t₃) ++ psc.toList) ++ [Ty.refT true (Ty.defHeap dc)]) := by
    have := ResultSub.trans hW.types hM hsub hMs
    simpa using this
  obtain ⟨-, htrs⟩ := PC.forall₂_append_eq_len hall (by simp)
  have htrc : Sub ({ C' with return_ := some ts } : Context).toTypeCtx trt
      (Ty.refT true (Ty.defHeap dc)) := by
    cases htrs with | cons h _ => exact h
  obtain ⟨rt, rfl, hrt⟩ : ∃ rt, trt = .refv rt ∧ RefOk s (.func a) rt := by
    cases htr1 with | ref h => exact ⟨_, rfl, h⟩
  have hsubrt : Sub ({ C' with return_ := some ts } : Context).toTypeCtx rt
      (.ref true (Ty.defHeap dc)) := by
    cases htrc with | refv h => exact h
  have hfit := PC.StoreOk.func_tyOk hs hf
  obtain ⟨rt₀, e, hrt0, -⟩ := hrt.principal
  simp only [Ref.type?, hf, Option.map_some, Option.some.injEq] at e
  subst e
  have hI₀ : PC.RefI (.ref false (Ty.defHeap fn.type)) := by
    simpa [PC.RefI, PC.HeapI, Ty.defHeap] using hfit
  have hdcok : TyOk {} (Ty.ref true (Ty.defHeap dc)) := .ref (.use (.dt hdc))
  have hsub0 : Sub {} (Ty.ref false (Ty.defHeap fn.type)) (.ref true (Ty.defHeap dc)) := by
    rcases hrt0 with rfl | ⟨hok', hs0⟩
    · exact (PC.ref_toEmpty hΔ3 hsubrt hI₀ hdcok).1
    · have hIrt := (PC.ref_toEmpty PC.typesOk_empty hs0 hI₀ hok').2
      exact Sub.trans TypeCtx.ok_empty hok' hs0 (PC.ref_toEmpty hΔ3 hsubrt hIrt hdcok).1
  have hheap : Sub {} (Ty.defHeap fn.type) (Ty.defHeap dc) := by
    cases hsub0 with | refNull h => exact h
  obtain ⟨hpsub, hrsub⟩ := PC.ds_func hfit hdc hheap he hec
  have hrts : ResultSub {} rsc.toList ts :=
    PC.results_sub_toEmpty_norecs hΔ3 hR hpc.2 hts hrs
  have l1 := hrsub.length_eq
  have l2 := hrts.length_eq
  have l3 := hpsub.length_eq
  refine ⟨?_, dc, ?_, ?_, psc, rsc, hec⟩
  · simp only [Ty.length] at l1 ⊢
    omega
  · cases c with
    | plain i =>
      cases i <;> simp [Admin.IsReturnCallRef] at hcr
      rename_i y
      have hy := h1 y rfl
      have hC3 : ({ C' with return_ := some ts } : Context).types = fi.module.types := by
        obtain ⟨C₀, lts, hm, -, rfl⟩ := hfr
        exact (ModuleInstOk.ctx_fields hm).2.2.2
      have hyF : fi.module.types[y.toNat]? = some dc := by
        simp only [Context.type?] at hy
        rw [← hC3]; exact hy
      simp only [Admin.retToCallIn, hyF]
    | returnCallRefType d =>
      obtain ⟨rfl, -⟩ := h2 _ rfl
      rfl
    | _ => simp [Admin.IsReturnCallRef] at hcr
  · intro ps' rs' he'
    have heq := Expand.detWire he' hec
    cases heq
    simp only [Ty.length] at l1 l3 hn ⊢
    omega

/-! ## The callee's counts at `CALL_REF` -/

/-- **At a typed `CALL_REF`** of the function `a`, the arguments are typed at the callee's
parameter types, and an annotation `d` has the callee's parameter and result counts. -/
theorem callRef_types {s : Store H} {f : Frame} {W vs : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hT : ContextTyped ⟨s, f, vals (W ++ vs) ++ [.ref (.func a), c] ++ rest⟩)
    (hcr : c.IsCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length) :
    List.Forall₂ (ValOk s) vs ps.toList ∧
      ∀ (d : DefType), c = .callRefType d → ∃ psd rsd : Ty (.list .val),
        Expand d (.func psd rsd) ∧ psd.length = ps.length ∧ rsd.length = rs.length := by
  obtain ⟨C, ts₀, xs₀, hs, hC, hc, hcode⟩ := hT.fragment_ctx
  have hsT : PC.StoreTypesOk s := ⟨hs.structsClosed, hs.arraysClosed⟩
  have hcode' : AdminsOk s C (vals W ++ (vals vs ++ [.ref (.func a), c]) ++ rest)
      ⟨[], xs₀, ts₀⟩ := by simpa using hcode
  obtain ⟨_, _, hpre⟩ := prefix_typing' hC hcode'
  have hpre' : AdminsOk s C (vals W ++ (vals vs ++ [.ref (.func a), c])) _ := hpre
  obtain ⟨mid, ya, _, hV, h, _⟩ := AdminsOk.split hpre' hC (vals W) (vals vs ++ [.ref (.func a), c])
    rfl (by simp)
  have hya : C.initLocals ya = C := Context.initLocals_of_set (AdminsOk.vals_inits hV)
  rw [hya] at h
  have hcd := wireCallRef_hcd hC hcr h
  have hΔ := PC.CtxOk.typesOk' hc
  have e0 : vals (vs ++ [.ref (.func a)]) ++ [c] = vals vs ++ [.ref (.func a), c] := by
    simp [vals, Val.toAdmin]
  have h' := h
  rw [← e0] at h'
  obtain ⟨tvs', it₀, M, T, hc0, hvs', hsub, hM, hT0, hMs, hP, -⟩ :=
    PC.redex_rep hC (PC.callRef_inits hcr) h'
  obtain ⟨dc, psc, rsc, hec, rfl, h1, h2⟩ := PC.inv_callRef hcr hc0
  have hdc : TyOk {} dc := by
    cases c with
    | plain i =>
      cases i <;> simp [Admin.IsCallRef] at hcr
      exact hΔ.get (h1 _ rfl)
    | callRefType d =>
      obtain ⟨rfl, -⟩ := h2 _ rfl
      exact hcd _ rfl
    | _ => simp [Admin.IsCallRef] at hcr
  have hpc := Expand.func_ok hdc hec
  obtain ⟨tvs, trtl, rfl, hvs, htr⟩ := PC.forall₂_split_left hvs'
  obtain ⟨trt, rfl, htr1⟩ : ∃ trt, trtl = [trt] ∧ ValOk s (.ref (.func a)) trt := by
    cases htr with | cons h hnil => cases hnil; exact ⟨_, rfl, h⟩
  have hall : ResultSub C.toTypeCtx ((mid ++ tvs) ++ [trt])
      ((T ++ psc.toList) ++ [Ty.refT true (Ty.defHeap dc)]) := by
    have := ResultSub.trans hC.types hM hsub hMs
    simpa using this
  obtain ⟨hX, htrs⟩ := PC.forall₂_append_eq_len hall rfl
  have htrc : Sub C.toTypeCtx trt (Ty.refT true (Ty.defHeap dc)) := by
    cases htrs with | cons h _ => exact h
  obtain ⟨rt, rfl, hrt⟩ : ∃ rt, trt = .refv rt ∧ RefOk s (.func a) rt := by
    cases htr1 with | ref h => exact ⟨_, rfl, h⟩
  have hsubrt : Sub C.toTypeCtx rt (.ref true (Ty.defHeap dc)) := by
    cases htrc with | refv h => exact h
  have hfit := PC.StoreOk.func_tyOk hs hf
  obtain ⟨rt₀, e, hrt0, -⟩ := hrt.principal
  simp only [Ref.type?, hf, Option.map_some, Option.some.injEq] at e
  subst e
  have hI₀ : PC.RefI (.ref false (Ty.defHeap fn.type)) := by
    simpa [PC.RefI, PC.HeapI, Ty.defHeap] using hfit
  have hdcok : TyOk {} (Ty.ref true (Ty.defHeap dc)) := .ref (.use (.dt hdc))
  have hsub0 : Sub {} (Ty.ref false (Ty.defHeap fn.type)) (.ref true (Ty.defHeap dc)) := by
    rcases hrt0 with rfl | ⟨hok, hs0⟩
    · exact (PC.ref_toEmpty hΔ hsubrt hI₀ hdcok).1
    · have hIrt := (PC.ref_toEmpty PC.typesOk_empty hs0 hI₀ hok).2
      exact Sub.trans TypeCtx.ok_empty hok hs0 (PC.ref_toEmpty hΔ hsubrt hIrt hdcok).1
  have hheap : Sub {} (Ty.defHeap fn.type) (Ty.defHeap dc) := by
    cases hsub0 with | refNull h => exact h
  obtain ⟨hpsub, hrsub⟩ := PC.ds_func hfit hdc hheap he hec
  have hlen : tvs.length = psc.toList.length := by
    have e1 := hvs.length_eq
    have e2 := hpsub.length_eq
    simp only [Ty.length] at hn
    omega
  obtain ⟨-, htv⟩ := PC.forall₂_append_eq_len hX hlen
  have hargs : List.Forall₂ (ValOk s) vs ps.toList :=
    PC.valsOk_transfer hs hsT PC.typesOk_empty (PC.valsOk_transfer hs hsT hΔ hvs htv hpc.1) hpsub
      (Expand.func_ok hfit he).1
  refine ⟨hargs, fun d hd => ?_⟩
  subst hd
  obtain ⟨rfl, -⟩ := h2 _ rfl
  refine ⟨psc, rsc, hec, ?_⟩
  have l1 := hpsub.length_eq
  have l2 := hrsub.length_eq
  simp only [Ty.length] at l1 l2 ⊢
  omega

/-- **At a typed `CALL_REF d`** of the function `a`, the annotation `d` has the callee's
parameter and result counts (whatever the values before it). -/
theorem callRef_counts {s : Store H} {f : Frame} {W : List Val} {a : Nat} {d : DefType}
    {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hT : ContextTyped ⟨s, f, vals W ++ [.ref (.func a), .callRefType d] ++ rest⟩)
    (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs)) :
    ∃ psd rsd : Ty (.list .val), Expand d (.func psd rsd) ∧ psd.length = ps.length ∧
      rsd.length = rs.length := by
  obtain ⟨C, ts₀, xs₀, hs, hC, hc, hcode⟩ := hT.fragment_ctx
  have hsT : PC.StoreTypesOk s := ⟨hs.structsClosed, hs.arraysClosed⟩
  obtain ⟨_, _, hpre⟩ := prefix_typing' hC hcode
  have hcr : (Admin.callRefType d).IsCallRef := trivial
  have hcd := wireCallRef_hcd hC hcr hpre
  have hΔ := PC.CtxOk.typesOk' hc
  have h' := hpre
  rw [show vals W ++ [Admin.ref (.func a), .callRefType d] =
    vals (W ++ [.ref (.func a)]) ++ [.callRefType d] by simp [vals, Val.toAdmin]] at h'
  obtain ⟨tvs', it₀, M, T, hc0, hvs', hsub, hM, hT0, hMs, hP, -⟩ :=
    PC.redex_rep hC (PC.callRef_inits hcr) h'
  obtain ⟨dc, psc, rsc, hec, rfl, h1, h2⟩ := PC.inv_callRef hcr hc0
  obtain ⟨hdd, hdc⟩ := h2 _ rfl
  subst d
  obtain ⟨tvs, trtl, rfl, hvs, htr⟩ := PC.forall₂_split_left hvs'
  obtain ⟨trt, rfl, htr1⟩ : ∃ trt, trtl = [trt] ∧ ValOk s (.ref (.func a)) trt := by
    cases htr with | cons h hnil => cases hnil; exact ⟨_, rfl, h⟩
  have hall : ResultSub C.toTypeCtx (([] ++ tvs) ++ [trt])
      ((T ++ psc.toList) ++ [Ty.refT true (Ty.defHeap dc)]) := by
    have := ResultSub.trans hC.types hM hsub hMs
    simpa using this
  obtain ⟨-, htrs⟩ := PC.forall₂_append_eq_len hall rfl
  have htrc : Sub C.toTypeCtx trt (Ty.refT true (Ty.defHeap dc)) := by
    cases htrs with | cons h _ => exact h
  obtain ⟨rt, rfl, hrt⟩ : ∃ rt, trt = .refv rt ∧ RefOk s (.func a) rt := by
    cases htr1 with | ref h => exact ⟨_, rfl, h⟩
  have hsubrt : Sub C.toTypeCtx rt (.ref true (Ty.defHeap dc)) := by
    cases htrc with | refv h => exact h
  have hfit := PC.StoreOk.func_tyOk hs hf
  obtain ⟨rt₀, e, hrt0, -⟩ := hrt.principal
  simp only [Ref.type?, hf, Option.map_some, Option.some.injEq] at e
  subst e
  have hI₀ : PC.RefI (.ref false (Ty.defHeap fn.type)) := by
    simpa [PC.RefI, PC.HeapI, Ty.defHeap] using hfit
  have hdcok : TyOk {} (Ty.ref true (Ty.defHeap dc)) := .ref (.use (.dt hdc))
  have hsub0 : Sub {} (Ty.ref false (Ty.defHeap fn.type)) (.ref true (Ty.defHeap dc)) := by
    rcases hrt0 with rfl | ⟨hok, hs0⟩
    · exact (PC.ref_toEmpty hΔ hsubrt hI₀ hdcok).1
    · have hIrt := (PC.ref_toEmpty PC.typesOk_empty hs0 hI₀ hok).2
      exact Sub.trans TypeCtx.ok_empty hok hs0 (PC.ref_toEmpty hΔ hsubrt hIrt hdcok).1
  have hheap : Sub {} (Ty.defHeap fn.type) (Ty.defHeap dc) := by
    cases hsub0 with | refNull h => exact h
  obtain ⟨hpsub, hrsub⟩ := PC.ds_func hfit hdc hheap he hec
  refine ⟨psc, rsc, hec, ?_⟩
  have l1 := hpsub.length_eq
  have l2 := hrsub.length_eq
  simp only [Ty.length] at l1 l2 ⊢
  omega

/-! ## Operands of a `CALL_REF` -/

/-- `c` is a `CALL_REF` whose annotation resolves to `d` in a frame of module instance `mi`. -/
def Resolves (mi : ModuleInst) (c : Admin) (d : DefType) : Prop :=
  c = .callRefType d ∨ ∃ y, c = .plain (.callRef y) ∧ mi.types[y.toNat]? = some d

/-- **A typed `CALL_REF` has its operands**: one more value than the parameters of its
annotation. -/
theorem callRef_operands {s : Store H} {f : Frame} {ws : List Val} {c : Admin}
    {Y : List Admin} {d : DefType} {ps rs : Ty (.list .val)}
    (hT : ContextTyped ⟨s, f, vals ws ++ c :: Y⟩) (hcr : c.IsCallRef)
    (hd : Resolves f.module c d) (he : Expand d (.func ps rs)) :
    ps.length + 1 ≤ ws.length := by
  refine hT.active_arity_types (n := ps.length + 1) fun C it htypes ha => ?_
  obtain ⟨dc, psc, rsc, hec, rfl, h1, h2⟩ := PC.inv_callRef hcr ha
  have hdd : dc = d := by
    rcases hd with rfl | ⟨y, rfl, hy⟩
    · exact (h2 _ rfl).1.symm
    · have := h1 y rfl
      simp only [Context.type?, htypes, hy, Option.some.injEq] at this
      exact this.symm
  subst hdd
  have heq := Expand.detWire he hec
  cases heq
  simp [Ty.length]

/-- A typed `CALL_REF` has at least its reference operand. -/
theorem callRef_operand_one {s : Store H} {f : Frame} {ws : List Val} {c : Admin}
    {Y : List Admin} (hT : ContextTyped ⟨s, f, vals ws ++ c :: Y⟩) (hcr : c.IsCallRef) :
    1 ≤ ws.length := by
  refine hT.active_arity_types (n := 1) fun C it _ ha => ?_
  obtain ⟨dc, psc, rsc, hec, rfl, -, -⟩ := PC.inv_callRef hcr ha
  simp

end Silmaril.Raw.Wasm.LimeCompile.TailSim
