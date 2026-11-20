module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Machine

/-!
# Forward runs of a call of `HLinked2.toRef`: frames after host calls, traps with the host state

A host callout of the importer appends a subtask and a caller record to the store and moves the
host state, but adds no task and no thread. The configurations of a call with host calls are
therefore `extG` extensions of the call's frame (`LinkedSessionFwd.extG`), not `extN` ones. Here:

* `extN_extG`: an `extN` extension of an `extG` extension is an `extG` extension (the records of
  the nested calls appended); `extG_hostCall`: so is the configuration after a host callout;
* `GFrame M₀ th`: `LFrame` for every `extG` extension (the entry check of instance `2` passes
  and instance `2` may leave); `GFrame.lframe`: every `extG` extension is an `LFrame`;
  `gframe_of`: the frame of a call is a `GFrame`;
* `TrapEndH M c h`: `TrapEnd` whose trapped configuration has the host state `h`, so that a
  session resumed after a trap (`resumeCfg`) knows its host state. `TrapsAtSH.trapEndH`,
  `TrapsAtRH.trapEndH`, `TrapEndH.steps`, `coreTrap_endH`, and the trapping nested calls
  `nest_trapCoreH`, `nest_trapLiftH`, `nest_trapArgsH` (all at the host state of the frame).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Frames extended by arbitrary records -/

theorem set_set_self {α : Type} (l : Arena α) (n : Nat) (a b : α) :
    (l.set n a).set n b = l.set n b := by
  show List.set (List.set l n a) n b = List.set l n b
  refine List.ext_getElem? fun j => ?_
  simp only [List.getElem?_set, List.length_set]
  split <;> simp_all

/-- **Frame absorption**: an `extN` extension of an `extG` extension is an `extG` extension. -/
theorem extN_extG (M₀ : Machine.Config (E3 P) σ) (ιe : InstState) (SL : List Subtask)
    (CL : List (Caller (E3 P))) (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) (ιe' : InstState) (N : List (NRec P))
    (C' : List (Option (Activation (E3 P) σ))) :
    extN (extG M₀ ιe SL CL TL HL C h) ιe' N C' =
      extG M₀ ιe' (SL ++ N.map (·.sub)) (CL ++ N.map (·.caller)) (TL ++ N.map (·.task))
        (HL ++ N.map (·.thread)) C' h := by
  simp only [extN, extG, List.append_assoc]
  rw [set_set_self]

/-- The `extG` extension is its own `extN` extension without nested calls. -/
theorem extN_extG_nil (M₀ : Machine.Config (E3 P) σ) (ιe : InstState) (SL : List Subtask)
    (CL : List (Caller (E3 P))) (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) :
    extN (extG M₀ ιe SL CL TL HL C h) ιe [] C = extG M₀ ιe SL CL TL HL C h := by
  rw [extN_extG]
  simp

/-- **A host callout keeps the configuration an `extG` extension**: one more subtask and caller
record, the new host state. -/
theorem extG_hostCall (M₀ : Machine.Config (E3 P) σ) (ιe : InstState) (SL : List Subtask)
    (CL : List (Caller (E3 P))) (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h h' : σ) (x : Subtask) (c : Caller (E3 P)) :
    ({ extG M₀ ιe SL CL TL HL C h with
      host := h'
      store := { (extG M₀ ιe SL CL TL HL C h).store with
        subtasks := (extG M₀ ιe SL CL TL HL C h).store.subtasks ++ [x]
        callers := (extG M₀ ιe SL CL TL HL C h).store.callers ++ [c] } } :
      Machine.Config (E3 P) σ) = extG M₀ ιe (SL ++ [x]) (CL ++ [c]) TL HL C h' := by
  simp [extG, List.append_assoc]

/-- The component functions of an `extG` extension are those of the frame. -/
theorem funcs_extG (M₀ : Machine.Config (E3 P) σ) (ιe : InstState) (SL : List Subtask)
    (CL : List (Caller (E3 P))) (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) (f : FuncId) :
    ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C h).store f =
      ArenaField.funcs.get? M₀.store f := rfl

/-- **The static facts of the importer's frame for every `extG` extension**: callouts of
instance `2` pass the entry check, and instance `2` may leave. -/
structure GFrame (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId) : Prop where
  entry : ∀ f ft ιe (SL : List Subtask) (CL : List (Caller (E3 P)))
    (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ),
    calloutEntry (extG M₀ ιe SL CL TL HL C h).store th (.lowered f ft {} ⟨2⟩) = none
  inst : ∃ ιi, M₀.store.insts[2]? = some ιi ∧ ιi.mayLeave = true

theorem GFrame.inst2 {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId} (hF : GFrame M₀ th)
    (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
    (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) :
    ∃ ιi, ArenaField.insts.get? (extG M₀ ιe SL CL TL HL C h).store ⟨2⟩ = some ιi ∧
      ιi.mayLeave = true := by
  obtain ⟨ιi, h2, hl⟩ := hF.inst
  exact ⟨ιi, (List.getElem?_set_ne (l := M₀.store.insts) (a := ιe)
    (show (1 : Nat) ≠ 2 by decide)).trans h2, hl⟩

/-- **Every `extG` extension of a `GFrame` is an `LFrame`.** -/
theorem GFrame.lframe {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId} (hF : GFrame M₀ th)
    (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
    (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) :
    LFrame (extG M₀ ιe SL CL TL HL C h) th where
  entry := fun f ft ιe' N C' => by
    rw [extN_extG]
    exact hF.entry _ _ _ _ _ _ _ _ _
  inst := by
    obtain ⟨ιi, h2, hl⟩ := hF.inst
    exact ⟨ιi, (List.getElem?_set_ne (l := M₀.store.insts) (a := ιe)
      (show (1 : Nat) ≠ 2 by decide)).trans h2, hl⟩

/-- **The frame of a call is a `GFrame`.** -/
theorem gframe_of {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi' : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k j : Nat}
    {x : SimpleExport} {a : Nat} {vs : List Silmaril.Wasm.Component.Val}
    {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)}
    (hat : CallAtLKTS prof P impl cs ιe ιi' fs G ST h₀ k j x a vs M₀ th K segs rest) :
    GFrame M₀ th where
  entry := fun f ft ιe SL CL TL HL C h => by
    rw [hat.thread]
    exact calloutEntry_mid (Gt := G.tasks) (Gth := G.threads) (R := TL) (R' := HL)
      (show M₀.store.tasks ++ TL = _ by rw [hat.tasks])
      (show M₀.store.threads ++ HL = _ by rw [hat.threads]) rfl rfl f ft {}
  inst := hat.frame.inst

/-! ## Trapped ends with the host state -/

/-- `TrapEnd` whose trapped configuration has the host state `h`. -/
def TrapEndH (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (M : Machine.Config (E3 P) σ) (c : (E3 P).Store (CanonHost (E3 P))) (h : σ) : Prop :=
  ∃ tr m', Steps prof (fun _ _ => false) (DI P impl) M tr m' ∧ (∀ ev, Label.host ev ∉ tr) ∧
    (∀ msg, Label.trap (.internal msg) ∉ tr) ∧ m'.store.lockdown = true ∧ m'.core = c ∧
    m'.host = h

theorem TrapEndH.toEnd {M : Machine.Config (E3 P) σ} {c : (E3 P).Store (CanonHost (E3 P))}
    {h : σ} (H : TrapEndH prof P impl M c h) : TrapEnd prof P impl M c := by
  obtain ⟨tr, m', r, hh, hi, hl, hc, -⟩ := H
  exact ⟨tr, m', r, hh, hi, hl, hc⟩

theorem TrapsAtSH.trapEndH {M : Machine.Config (E3 P) σ} {c : (E3 P).Store (CanonHost (E3 P))}
    {h : σ} (H : TrapsAtSH prof P impl M c h) : TrapEndH prof P impl M c h := by
  obtain ⟨tr, mT, r, hr, hrun, hl, hu, hc, hh⟩ := H
  refine ⟨tr ++ [.trap r], trapCfg mT, Adequacy.steps_append hrun.steps (.cons hu.1 (.refl _)),
    ?_, ?_, rfl, hc, hh⟩
  · intro ev hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Adequacy.LRun.no_host hrun ev hm
    · simp at hm
  · intro msg hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Adequacy.LRun.no_trap hrun hl _ hm
    · simp only [List.mem_singleton, Label.trap.injEq] at hm
      exact hr msg hm.symm

theorem TrapsAtRH.trapEndH {M : Machine.Config (E3 P) σ} {c : (E3 P).Store (CanonHost (E3 P))}
    {r : TrapReason} {h : σ} (hr : ∀ msg, r ≠ .internal msg)
    (H : TrapsAtRH prof P impl M c r h) : TrapEndH prof P impl M c h := by
  obtain ⟨tr, mT, hrun, hl, hu, hc, hh⟩ := H
  exact TrapsAtSH.trapEndH ⟨tr, mT, r, hr, hrun, hl, hu, hc, hh⟩

theorem TrapEndH.steps {M M' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    {c : (E3 P).Store (CanonHost (E3 P))} {h : σ}
    (H : Steps prof (fun _ _ => false) (DI P impl) M tr M') (hq : Quiet tr)
    (H' : TrapEndH prof P impl M' c h) : TrapEndH prof P impl M c h := by
  obtain ⟨tr', m', r, hh, hi, hl, hc, hho⟩ := H'
  refine ⟨tr ++ tr', m', Adequacy.steps_append H r, ?_, ?_, hl, hc, hho⟩
  · intro ev hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hq.1 ev hm
    · exact hh ev hm
  · intro msg hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hq.2 _ hm
    · exact hi msg hm

/-- A core activation whose status is a trap traps the machine at its core store, in the host
state of the frame. -/
theorem coreTrap_endH {M : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {x : CoreSt (E3 P)}
    (hst : (E3 P).status x.1 x.2 = .returned .trap) :
    TrapEndH prof P impl (coreCfg M th K segs rest x) x.1 M.host :=
  ⟨[.trap .coreTrap], _, .cons (Step.coreTrap rfl hst) (.refl _), fun _ h => by simp at h,
    fun _ h => by simp at h, rfl, rfl, rfl⟩

/-! ## Trapping nested calls, with the host state -/

section Nest

variable {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
  {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
  {rest : List (Activation (E3 P) σ)}

/-- `nest_trapCore`, at the host state of the frame. -/
theorem nest_trapCoreH (hB : LFrame B th) {ιe : InstState} {N : List (NRec P)}
    {C : List (Option (Activation (E3 P) σ))} (hte : ThreadsOk ιe) {y : CoreSt (E3 P)}
    {f : FuncId} {a : (E3 P).FuncAddr} {p : Silmaril.Wasm.Component.FuncTy} {ys : List Flat}
    (hs : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hr : p.results.length ≤ 1) (hS : LinkSite B y (.lowered f (witFt p) {} ⟨2⟩) ys)
    {ws : List Silmaril.Wasm.Component.Val} (hws : liftArgs p.params ys = some ws)
    {e : CoreSt (E3 P)}
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e)
    (hst : (E3 P).status e.1 e.2 = .returned .trap) :
    TrapEndH prof P impl (coreCfg (extN B ιe N C) th K segs rest y) e.1 B.host := by
  obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, -⟩ := site_of hS hf hr
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, hlock, hhost, -, -⟩ :=
    nest_atTSH (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hs
      (hB.entry _ _ _ _ _) hi hleave hf hB.len (addThread?_ok hte _) (removeThread?_enter ιe _)
      hpf hys hmaxp hws hr hrf hmaxr
  have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y.1,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) := by
    rw [← hcore]
    exact eq_coreCfg hctl
  obtain ⟨tr₃, htr₃, r₃⟩ := Adequacy.coreCfg_steps_of (prof := prof)
    (hr := fun _ _ => false) (dispatch := DI P impl) (B := M₁) (th := th') (K := K')
    (segs := segs') (rest := rest') he
  rw [← hM] at r₃
  have hlive₁ : Live M₁ := ⟨by rw [hctl]; exact List.cons_ne_nil _ _, hlock⟩
  have hT := coreTrap_endH (prof := prof) (impl := impl) (M := M₁) (th := th') (K := K')
    (segs := segs') (rest := rest') hst
  rw [hhost] at hT
  exact TrapEndH.steps (Adequacy.steps_append hrun.steps r₃)
    ((Quiet.of_lrun hrun hlive₁).append (Quiet.of_core htr₃)) hT

/-- `nest_trapLift`, at the host state of the frame. -/
theorem nest_trapLiftH (hB : LFrame B th) {ιe : InstState} {N : List (NRec P)}
    {C : List (Option (Activation (E3 P) σ))} (hte : ThreadsOk ιe) {y : CoreSt (E3 P)}
    {f : FuncId} {a : (E3 P).FuncAddr} {p : Silmaril.Wasm.Component.FuncTy} {ys : List Flat}
    (hs : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hr : p.results.length ≤ 1) (hS : LinkSite B y (.lowered f (witFt p) {} ⟨2⟩) ys)
    {ws : List Silmaril.Wasm.Component.Val} (hws : liftArgs p.params ys = some ws)
    {e : CoreSt (E3 P)}
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e)
    {zs : List Flat} (hst : (E3 P).status e.1 e.2 = .returned (.values zs))
    (hn : liftArgs p.results zs = none) :
    TrapEndH prof P impl (coreCfg (extN B ιe N C) th K segs rest y) e.1 B.host := by
  obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, hexp⟩ := site_of hS hf hr
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, hlock, -, -, htrap⟩ :=
    nest_atTSH (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hs
      (hB.entry _ _ _ _ _) hi hleave hf hB.len (addThread?_ok hte _) (removeThread?_enter ιe _)
      hpf hys hmaxp hws hr hrf hmaxr
  have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y.1,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) := by
    rw [← hcore]
    exact eq_coreCfg hctl
  obtain ⟨tr₃, htr₃, r₃⟩ := Adequacy.coreCfg_steps_of (prof := prof)
    (hr := fun _ _ => false) (dispatch := DI P impl) (B := M₁) (th := th') (K := K')
    (segs := segs') (rest := rest') he
  rw [← hM] at r₃
  have hlive₁ : Live M₁ := ⟨by rw [hctl]; exact List.cons_ne_nil _ _, hlock⟩
  have s₄ : Step prof (fun _ _ => false) (DI P impl) (coreCfg M₁ th' K' segs' rest' e) .tau
      (retCfg M₁ th' K' segs' rest' e zs) := Step.coreReturned rfl hst
  have hty : zs.map (·.type) = ValTy.flatList p.results := (hexp ws hws e he).2 zs hst
  exact TrapEndH.steps (Adequacy.steps_append hrun.steps
      (Adequacy.steps_append r₃ (.cons s₄ (.refl _))))
    ((Quiet.of_lrun hrun hlive₁).append ((Quiet.of_core htr₃).append Quiet.tau))
    (TrapsAtSH.trapEndH (htrap e zs hty hn))

/-- `nest_trapArgs`, at the host state of the frame. -/
theorem nest_trapArgsH (hB : LFrame B th) {ιe : InstState} {N : List (NRec P)}
    {C : List (Option (Activation (E3 P) σ))} (hte : ThreadsOk ιe) {y : CoreSt (E3 P)}
    {f : FuncId} {a : (E3 P).FuncAddr} {p : Silmaril.Wasm.Component.FuncTy} {ys : List Flat}
    (hs : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hr : p.results.length ≤ 1) (hS : LinkSite B y (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hws : liftArgs p.params ys = none) :
    TrapEndH prof P impl (coreCfg (extN B ιe N C) th K segs rest y) y.1 B.host := by
  obtain ⟨hpf, hys, hmaxp, -, -, -⟩ := site_of hS hf hr
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
  exact TrapsAtSH.trapEndH (nest_trap_argsTSH (prof := prof) (impl := impl) B ιe _ N C th K segs
    rest y f a p ys ιi hs (hB.entry _ _ _ _ _) hi hleave hf hB.len (addThread?_ok hte _) hpf hys
    hmaxp hws)

end Nest

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
