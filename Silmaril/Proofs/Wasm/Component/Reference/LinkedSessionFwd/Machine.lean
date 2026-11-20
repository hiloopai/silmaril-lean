module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.TrapS

/-!
# Forward runs of a linked call: the machine

The forward counterpart of `lsegs_inv`: segmented runs of the importer's core phase (`LSeg`)
are runs of the reference machine, and the ways a nested call traps are machine traps with
specification traps.

* `Quiet tr`: the trace has no host event and no trap;
* `lseg_run`: an `LSeg` from `x` to `z` whose callouts are link sites (`LinkOk`) is a quiet
  machine run from the importer's core activation at `x`, in any frame `extN B ιe N C` with a
  reusable thread table of the exporter, to its core activation at `z`, in a frame with the
  records of the nested calls (`nest_atTS`, `coreCfg_steps_of`, `Step.coreReturned`);
* `TrapEnd M c`: from `M`, a run without host events and without `internal` faults to a trapped
  configuration holding the core store `c`; `TrapsAtS.trapEnd`;
* `nest_trapCore`, `nest_trapLift`, `nest_trapArgs`: a nested call whose exporter run traps,
  whose exporter results do not lift, or whose arguments do not lift, is a `TrapEnd`, at the
  core store of the exporter's end (the first two) or of the callout (the last).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Quiet traces -/

/-- The trace has no host event and no trap. -/
def Quiet (tr : List (Label (E3 P) σ)) : Prop :=
  (∀ ev, Label.host ev ∉ tr) ∧ ∀ r, Label.trap r ∉ tr

theorem Quiet.nil : Quiet (σ := σ) (P := P) [] :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem Quiet.append {tr₁ tr₂ : List (Label (E3 P) σ)} (h₁ : Quiet tr₁) (h₂ : Quiet tr₂) :
    Quiet (tr₁ ++ tr₂) :=
  ⟨fun ev hm => (List.mem_append.mp hm).elim (h₁.1 ev) (h₂.1 ev),
    fun r hm => (List.mem_append.mp hm).elim (h₁.2 r) (h₂.2 r)⟩

theorem Quiet.tau : Quiet (σ := σ) (P := P) [.tau] :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem Quiet.of_core {tr : List (Label (E3 P) σ)} (h : ∀ l ∈ tr, l = .core) : Quiet tr :=
  ⟨Adequacy.not_host_of_core h, Adequacy.not_trap_of_core h⟩

theorem Quiet.of_lrun {M M' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    (h : LRun prof (fun _ _ => false) (DI P impl) M tr M') (hl : Live M') : Quiet tr :=
  ⟨Adequacy.LRun.no_host h, Adequacy.LRun.no_trap h hl⟩

/-! ## Segmented runs, forward -/

/-- **A segmented run of the importer's core phase is a quiet machine run.** -/
theorem lseg_run {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} (hB : LFrame B th) {x z : CoreSt (E3 P)}
    {recs : List (LRec P)} (h : LSeg B x recs z) :
    ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))),
      ThreadsOk ιe → LinkOk B x →
      ∃ (ιe' : InstState) (N' : List (NRec P)) (C' : List (Option (Activation (E3 P) σ)))
        (tr : List (Label (E3 P) σ)), ThreadsOk ιe' ∧ Quiet tr ∧
        Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest x) tr
          (coreCfg (extN B ιe' N' C') th K segs rest z) := by
  induction h with
  | done hy =>
    intro ιe N C hte _
    obtain ⟨tr, htr, r⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := extN B ιe N C) (th := th) (K := K) (segs := segs)
      (rest := rest) hy
    exact ⟨ιe, N, C, tr, hte, Quiet.of_core htr, r⟩
  | @call x y e z f a p ys zs ws us rest₁ hy hs hf hr hws he hst hus _ ih =>
    intro ιe N C hte hk
    obtain ⟨tr₁, htr₁, r₁⟩ := Adequacy.coreCfg_steps_of (prof := prof)
      (hr := fun _ _ => false) (dispatch := DI P impl) (B := extN B ιe N C) (th := th) (K := K)
      (segs := segs) (rest := rest) hy
    obtain ⟨f', a', p', heq, hf', hpf, hys, hmaxp, hres', hrf, hmaxr, hexp⟩ :=
      (hk [] y _ ys (.done hy) hs).site
    have hfe : f = f' ∧ witFt p = witFt p' := by
      simp only [CanonHost.lowered.injEq] at heq
      exact ⟨heq.1, heq.2.1⟩
    obtain ⟨rfl, hpp⟩ := hfe
    have hpp' : p = p' := witFt_inj hpp hr hres'
    subst hpp'
    have ha : a = a' := by
      have e' := hf.symm.trans hf'
      simp only [Option.some.injEq, CFuncInst.lifted.injEq] at e'
      exact e'.1
    subst ha
    obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
    have hadd := addThread?_ok hte ⟨(extN B ιe N C).store.threads.length⟩
    have hrem := removeThread?_enter ιe ⟨(extN B ιe N C).store.threads.length⟩
    obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, hlock, hret, -⟩ :=
      nest_atTS (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hs
        (hB.entry _ _ _ _ _) hi hleave hf hB.len hadd hrem hpf hys hmaxp hws hr hrf hmaxr
    have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y.1,
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) := by
      rw [← hcore]
      exact eq_coreCfg hctl
    obtain ⟨tr₃, htr₃, r₃⟩ := Adequacy.coreCfg_steps_of (prof := prof)
      (hr := fun _ _ => false) (dispatch := DI P impl) (B := M₁) (th := th') (K := K')
      (segs := segs') (rest := rest') he
    have s₄ : Step prof (fun _ _ => false) (DI P impl) (coreCfg M₁ th' K' segs' rest' e) .tau
        (retCfg M₁ th' K' segs' rest' e zs) := Step.coreReturned rfl hst
    have hty : zs.map (·.type) = ValTy.flatList p.results := (hexp ws hws e he).2 zs hst
    obtain ⟨tr₅, h₅⟩ := hret e zs us hty hus
    obtain ⟨ιe'', N'', C'', tr₆, hte', hq₆, r₆⟩ := ih _ _ C₁ (threadsOk_after _ _)
      (hk.after hy hs hf hr hws he hst hus)
    have hlive₁ : Live M₁ := ⟨by rw [hctl]; exact List.cons_ne_nil _ _, hlock⟩
    refine ⟨ιe'', N'', C'', tr₁ ++ (tr₂ ++ (tr₃ ++ (.tau :: (tr₅ ++ tr₆)))), hte', ?_, ?_⟩
    · refine (Quiet.of_core htr₁).append ((Quiet.of_lrun hrun hlive₁).append
        ((Quiet.of_core htr₃).append (?_ : Quiet (.tau :: (tr₅ ++ tr₆)))))
      exact (Quiet.tau (P := P) (σ := σ)).append ((Quiet.of_lrun h₅
        (coreCfg_extN_live _ _ _ _ _ _ _ _ _)).append hq₆)
    · refine Adequacy.steps_append r₁ (Adequacy.steps_append hrun.steps ?_)
      rw [← hM] at r₃
      refine Adequacy.steps_append r₃ (.cons s₄ (Adequacy.steps_append h₅.steps r₆))

/-! ## Trapped ends -/

/-- From `M`, a run without host events and without `internal` faults to a trapped
configuration holding the core store `c`. -/
def TrapEnd (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (M : Machine.Config (E3 P) σ) (c : (E3 P).Store (CanonHost (E3 P))) : Prop :=
  ∃ tr m', Steps prof (fun _ _ => false) (DI P impl) M tr m' ∧ (∀ ev, Label.host ev ∉ tr) ∧
    (∀ msg, Label.trap (.internal msg) ∉ tr) ∧ m'.store.lockdown = true ∧ m'.core = c

theorem TrapsAtS.trapEnd {M : Machine.Config (E3 P) σ} {c : (E3 P).Store (CanonHost (E3 P))}
    (h : TrapsAtS prof P impl M c) : TrapEnd prof P impl M c := by
  obtain ⟨tr, mT, r, hr, hrun, hl, hu, hc⟩ := h
  refine ⟨tr ++ [.trap r], trapCfg mT, Adequacy.steps_append hrun.steps (.cons hu.1 (.refl _)),
    ?_, ?_, rfl, hc⟩
  · intro ev hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Adequacy.LRun.no_host hrun ev hm
    · simp at hm
  · intro msg hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Adequacy.LRun.no_trap hrun hl _ hm
    · simp only [List.mem_singleton, Label.trap.injEq] at hm
      exact hr msg hm.symm

theorem TrapEnd.steps {M M' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    {c : (E3 P).Store (CanonHost (E3 P))}
    (h : Steps prof (fun _ _ => false) (DI P impl) M tr M') (hq : Quiet tr)
    (h' : TrapEnd prof P impl M' c) : TrapEnd prof P impl M c := by
  obtain ⟨tr', m', r, hh, hi, hl, hc⟩ := h'
  refine ⟨tr ++ tr', m', Adequacy.steps_append h r, ?_, ?_, hl, hc⟩
  · intro ev hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hq.1 ev hm
    · exact hh ev hm
  · intro msg hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hq.2 _ hm
    · exact hi msg hm

/-- A core activation whose status is a trap traps the machine at its core store. -/
theorem coreTrap_end {M : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {x : CoreSt (E3 P)}
    (hst : (E3 P).status x.1 x.2 = .returned .trap) :
    TrapEnd prof P impl (coreCfg M th K segs rest x) x.1 :=
  ⟨[.trap .coreTrap], _, .cons (Step.coreTrap rfl hst) (.refl _), fun _ h => by simp at h,
    fun _ h => by simp at h, rfl, rfl⟩

section Nest

variable {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
  {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
  {rest : List (Activation (E3 P) σ)}

/-- The link site of a callout, with the exporter's lifted function of the trampoline. -/
theorem site_of {y : CoreSt (E3 P)} {f : FuncId} {p : Silmaril.Wasm.Component.FuncTy}
    {ys : List Flat} {a : (E3 P).FuncAddr} (hS : LinkSite B y (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hr : p.results.length ≤ 1) :
    floatFreeList p.params = true ∧ ys.map (·.type) = ValTy.flatList p.params ∧
      (ValTy.flatList p.params).length ≤ 16 ∧ floatFreeList p.results = true ∧
      (ValTy.flatList p.results).length ≤ 1 ∧
      ∀ ws, liftArgs p.params ys = some ws → ∀ e,
        Relation.ReflTransGen (CoreStep (E3 P))
          (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e →
        (∀ h' ys', (E3 P).status e.1 e.2 ≠ .callout h' ys') ∧
        ∀ zs, (E3 P).status e.1 e.2 = .returned (.values zs) →
          zs.map (·.type) = ValTy.flatList p.results := by
  obtain ⟨f', a', p', heq, hf', hpf, hys, hmaxp, hres', hrf, hmaxr, hexp⟩ := hS.site
  have hfe : f = f' ∧ witFt p = witFt p' := by
    simp only [CanonHost.lowered.injEq] at heq
    exact ⟨heq.1, heq.2.1⟩
  obtain ⟨rfl, hpp⟩ := hfe
  have hpp' : p = p' := witFt_inj hpp hr hres'
  subst hpp'
  have ha : a = a' := by
    have e' := hf.symm.trans hf'
    simp only [Option.some.injEq, CFuncInst.lifted.injEq] at e'
    exact e'.1
  subst ha
  exact ⟨hpf, hys, hmaxp, hrf, hmaxr, hexp⟩

/-- **A nested call whose exporter run traps traps the machine** at the core store of the
exporter's end. -/
theorem nest_trapCore (hB : LFrame B th) {ιe : InstState} {N : List (NRec P)}
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
    TrapEnd prof P impl (coreCfg (extN B ιe N C) th K segs rest y) e.1 := by
  obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, -⟩ := site_of hS hf hr
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, hlock, -, -⟩ :=
    nest_atTS (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hs
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
  exact TrapEnd.steps (Adequacy.steps_append hrun.steps r₃)
    ((Quiet.of_lrun hrun hlive₁).append (Quiet.of_core htr₃)) (coreTrap_end hst)

/-- **A nested call whose exporter results do not lift traps the machine** at the core store
of the exporter's end. -/
theorem nest_trapLift (hB : LFrame B th) {ιe : InstState} {N : List (NRec P)}
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
    TrapEnd prof P impl (coreCfg (extN B ιe N C) th K segs rest y) e.1 := by
  obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, hexp⟩ := site_of hS hf hr
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
  obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, hlock, -, htrap⟩ :=
    nest_atTS (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hs
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
  exact TrapEnd.steps (Adequacy.steps_append hrun.steps
      (Adequacy.steps_append r₃ (.cons s₄ (.refl _))))
    ((Quiet.of_lrun hrun hlive₁).append ((Quiet.of_core htr₃).append Quiet.tau))
    (htrap e zs hty hn).trapEnd

/-- **A callout whose arguments do not lift traps the machine** at the core store of the
callout. -/
theorem nest_trapArgs (hB : LFrame B th) {ιe : InstState} {N : List (NRec P)}
    {C : List (Option (Activation (E3 P) σ))} (hte : ThreadsOk ιe) {y : CoreSt (E3 P)}
    {f : FuncId} {a : (E3 P).FuncAddr} {p : Silmaril.Wasm.Component.FuncTy} {ys : List Flat}
    (hs : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hr : p.results.length ≤ 1) (hS : LinkSite B y (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hws : liftArgs p.params ys = none) :
    TrapEnd prof P impl (coreCfg (extN B ιe N C) th K segs rest y) y.1 := by
  obtain ⟨hpf, hys, hmaxp, -, -, -⟩ := site_of hS hf hr
  obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
  exact (nest_trap_argsTS (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi
    hs (hB.entry _ _ _ _ _) hi hleave hf hB.len (addThread?_ok hte _) hpf hys hmaxp
    hws).trapEnd

end Nest

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
