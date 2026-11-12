module

public import Silmaril.Proofs.Wasm.Component.Reference.CallPath
public import Silmaril.Proofs.Wasm.Component.Reference.CoreRun

/-!
# The call phase of `RefToSpecAll`

`callPhase : CallPhase`: every behaviour of calling function `j` from `afterInst` (the
configuration after instantiating `c.toRef`) on the reference images of well-typed IR values is
an outcome of `exportSpec`. The run is the deterministic prefix of `call_at`, the core
activation (inverted by `coreCfg_steps_inv`, `coreCfg_diverges_inv`; its runs are Core runs of
the instance, `coreRun_values`, `coreRun_trap`, `coreRun_diverges`, typed by
`run_results_typed`, never at a host call by `run_no_callout`), and the deterministic suffix of
`call_at`, after which only ticks, which return to the same configuration, are possible.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-- A live configuration has no call outcome. -/
theorem Live.not_holds {m : Machine.Config E σ} (h : Live m) (c : CallId) (out : CallOutcome) :
    ¬ out.Holds hr c m := by
  cases out with
  | resolved r => exact fun hh => h.1 hh.1
  | trap => exact fun hh => absurd (hh.symm.trans h.2) (by decide)
  | deadlock => exact fun hh => h.1 hh.1.1

/-- A locked-down configuration with the host in control takes no step. -/
theorem steps_of_locked {m m' : Machine.Config E σ} {tr : List (Label E σ)}
    (hc : m.ctl = []) (hl : m.store.lockdown = true) (h : Steps prof hr dispatch m tr m') :
    m' = m := by
  cases h with
  | refl => rfl
  | cons s _ =>
    obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc s
    exact absurd ((Step.host_ready s).2.1.symm.trans hl) (by decide)

/-- A trapped configuration does not diverge. -/
theorem not_diverges_trapCfg (m : Machine.Config E σ) :
    ¬ Diverges prof hr dispatch (trapCfg m) :=
  not_diverges_of_ctl_nil rfl

/-- One step of the allowed host events from a quiet configuration: a tick, which returns to
it through a live run. -/
theorem quiet_cons {mE m₁ m' : Machine.Config E σ} {c : CallId} {l : Label E σ}
    {tr : List (Label E σ)} (hc : mE.ctl = []) (hres : mE.result? c ≠ none)
    (htick : ∀ m₁, Step prof hr dispatch mE (.host .tick) m₁ →
      ∃ trT, LRun prof hr dispatch m₁ trT mE)
    (s : Step prof hr dispatch mE l m₁) (r : Steps prof hr dispatch m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ l :: tr → CallHostEvent c ev) :
    Live m' ∨ ∃ tr'', tr''.length < tr.length + 1 ∧ Steps prof hr dispatch mE tr'' m' ∧
      ∀ ev, Label.host ev ∈ tr'' → CallHostEvent c ev := by
  have hl : ∃ ev, l = .host ev := Step.host_of_ctl_nil hc s
  obtain ⟨ev, rfl⟩ := hl
  have hallowed : CallHostEvent c ev := hev ev List.mem_cons_self
  rcases hallowed with rfl | rfl
  · obtain ⟨trT, hT⟩ := htick m₁ s
    rcases hT.inv r with hl | ⟨tr'', e, r'⟩
    · exact .inl hl
    · have hlen : tr''.length < tr.length + 1 := by rw [e, List.length_append]; omega
      exact .inr ⟨tr'', hlen, r', fun ev' hm =>
        hev ev' (List.mem_cons_of_mem _ (e ▸ List.mem_append_right _ hm))⟩
  · cases s with
    | hostCancel _ _ hn' => exact absurd hn' hres

/-- **Quiet configurations**: from a configuration with the host in control whose call `c`
resolved, and from which a tick returns to itself, the allowed host events lead back to it or
through live configurations. -/
theorem quiet {mE : Machine.Config E σ} {c : CallId} (hc : mE.ctl = [])
    (hres : mE.result? c ≠ none)
    (htick : ∀ m₁, Step prof hr dispatch mE (.host .tick) m₁ →
      ∃ trT, LRun prof hr dispatch m₁ trT mE) :
    ∀ (n : Nat) (tr : List (Label E σ)) (m' : Machine.Config E σ), tr.length ≤ n →
      Steps prof hr dispatch mE tr m' → (∀ ev, Label.host ev ∈ tr → CallHostEvent c ev) →
      m' = mE ∨ Live m' := by
  intro n
  induction n with
  | zero =>
    intro tr m' hn h _
    cases h with
    | refl => exact .inl rfl
    | cons _ _ => exact absurd hn (by simp)
  | succ n ih =>
    intro tr m' hn h hev
    cases h with
    | refl => exact .inl rfl
    | cons s r =>
      rcases quiet_cons hc hres htick s r hev with hl | ⟨tr'', hlen, r', hev'⟩
      · exact .inr hl
      · exact ih tr'' m' (by simp only [List.length_cons] at hn; omega) r' hev'

/-- A configuration running a core activation is the core configuration of itself. -/
theorem eq_coreCfg {M : Machine.Config E σ} {th : Option ThreadId}
    {t : E.Thread (CanonHost E)} {K : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} (h : M.ctl = ⟨th, .core t K, segs⟩ :: rest) :
    M = coreCfg M th K segs rest (M.store.core, t) := by
  obtain ⟨⟨⟩⟩ := M
  cases h
  rfl

end Generic

/-! ## The core activation of the call -/

section Core

/-- A flat callout status is a callout. -/
theorem flatStatus_callout {H : Type} {st : Silmaril.Wasm.SingleThreaded.Status H} {h : H}
    {args : List FlatValue} (hs : flatStatus st = .callout h args) :
    ∃ h' args', st = .callout h' args' := by
  cases st with
  | callout h' args' => exact ⟨h', args', rfl⟩
  | returned r =>
    cases r with
    | values vs =>
      simp only [flatStatus] at hs
      split at hs <;> cases hs
    | trap => cases hs
  | running => cases hs
  | stuck => cases hs

open Silmaril.Wasm.SingleThreaded in
/-- A callout status of `statusP` is a host-call redex. -/
theorem statusP_callout {P : Profile} {H : Type} {s : Silmaril.Wasm.Execution.Core.Store H}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {h : H} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hs : Silmaril.Wasm.Game.statusP P s t = .callout h args) :
    ∃ E a, decompose? s (t.config s).code = some (E, a, h, args) := by
  unfold Silmaril.Wasm.Game.statusP at hs
  dsimp only at hs
  split_ifs at hs
  all_goals
    split at hs
    next E a h₁ args₁ hd =>
      cases hs
      exact ⟨E, a, hd⟩
    next => cases hs

/-- A callout status of `core3P P` is a host-call redex. -/
theorem status_callout {P : Profile} {s : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {h : CanonHost (E3 P)} {args : List FlatValue}
    (hs : (E3 P).status s t = .callout h args) :
    ∃ E a h' args', Silmaril.Wasm.SingleThreaded.decompose? s (t.config s).code =
      some (E, a, h', args') := by
  obtain ⟨h', args', hst⟩ := flatStatus_callout (H := CanonHost (E3 P)) hs
  obtain ⟨E, a, hd⟩ := statusP_callout hst
  exact ⟨E, a, h', args', hd⟩

variable {P : Profile} {cs : (core3P P).Store (CanonHost (core3P P))} {a : Nat}
  {xs : List Flat}

/-- Runs of the core activation are runs of the reference engine's threads. -/
theorem coreSteps_internal {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y) :
    Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P)
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y :=
  Relation.ReflTransGen.mono (fun _ _ h => h.2) _ _ hy

/-- Runs of the core activation are Core runs of the renamed store. -/
theorem coreSteps_run {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y) :
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke (Store.mapH (fun _ => 0) cs) a
        (xs.map Silmaril.Wasm.SingleThreaded.ofFlat))
      (Config.mapH (fun _ => 0) (y.2.config y.1)) :=
  invoke_steps_mapH _ (internalP_steps (coreSteps_internal hy))

variable {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} {x : SimpleExport} {nm : String}

/-- The core activation never calls out. -/
theorem no_callout (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (ha : a = I.addrs.getD x.core 0)
    (hcore : c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (hxs : xs.map (·.type) = ValTy.flatList x.ty.params) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y)
    {h : CanonHost (E3 P)} {args : List FlatValue} (hs : (E3 P).status y.1 y.2 = .callout h args) :
    False := by
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨E, a', h', args', hd⟩ := status_callout hs
  obtain ⟨E', hd'⟩ := decompose?_mapH (fun _ => 0) hd
  have run := coreSteps_run hy
  rw [hcs, ha] at run
  have hxs' : xs.map (·.type) = c.mod.exports[x.core].2.params := by rw [hget]; exact hxs
  have hn := run_no_callout hI hk hxs' run
  have hstore : (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).store =
      Store.mapH (fun _ => 0) y.1 := by
    exact congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  rw [hstore] at hn
  exact absurd (hd'.symm.trans hn) (by simp)

/-- A returned core activation gives an outcome of `coreOut`, with values of the flat
result types. -/
theorem values_coreOut (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (ha : a = I.addrs.getD x.core 0)
    (hcore : c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (hxs : xs.map (·.type) = ValTy.flatList x.ty.params) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y)
    {vs : List FlatValue} (hs : (E3 P).status y.1 y.2 = .returned (.values vs)) :
    some vs ∈ coreOut P c.mod x.core xs ∧ vs.map (·.type) = ValTy.flatList x.ty.results := by
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨cvs, hc, hm⟩ := status_values hs
  have run := coreSteps_run hy
  rw [hcs, ha] at run
  have hxs' : xs.map (·.type) = c.mod.exports[x.core].2.params := by rw [hget]; exact hxs
  have ht := run_results_typed hI hk hxs' run hc hm
  rw [hget] at ht
  exact ⟨⟨I, hI, _, .values cvs, run, hc, hm.symm⟩, ht⟩

/-- A trapped core activation gives the outcome `none` of `coreOut`. -/
theorem trap_coreOut (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (ha : a = I.addrs.getD x.core 0) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y)
    (hs : (E3 P).status y.1 y.2 = .returned .trap) : none ∈ coreOut P c.mod x.core xs := by
  obtain ⟨c', res, run, hc, hr⟩ := coreRun_trap (fun _ => (0 : Nat)) (coreSteps_internal hy) hs
  rw [hcs, ha] at run
  exact ⟨I, hI, c', res, run, hc, hr.symm⟩

/-- A divergent core activation diverges in `coreDiverges`. -/
theorem diverges_core (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (ha : a = I.addrs.getD x.core 0)
    (hd : Silmaril.InfiniteTrace (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)) :
    coreDiverges P c.mod x.core xs := by
  have hd' := coreRun_diverges (P := P) (fun _ => (0 : Nat))
    (Silmaril.InfiniteTrace.map id (fun _ _ h => h.2) hd)
  rw [hcs, ha] at hd'
  exact ⟨I, hI, hd'⟩

end Core

/-! ## Outcomes -/

section Outcomes

variable {P : Profile} {prof : ProfileKind}

/-- A trapped configuration has only the trap outcome. -/
theorem holds_trapCfg {m : Machine.Config (E3 P) Unit} {out : CallOutcome}
    (ho : out.Holds (refHost P).hr ⟨0⟩ (trapCfg m)) : out = .trap := by
  cases out with
  | resolved r => exact absurd ho.2.1 (by simp)
  | trap => rfl
  | deadlock => exact absurd ho.1.2.1 (by simp)

/-- After a resolving suffix, the only outcome is the resolution. -/
theorem out_of_resolves {m₁ m' : Machine.Config (E3 P) Unit} {rs : List Val}
    {tr : List (Label (E3 P) Unit)} {out : CallOutcome} (hR : Resolves prof P m₁ rs)
    (hs : Steps prof (refHost P).hr (D P) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨0⟩ m') : out = .resolved (some rs) := by
  obtain ⟨tr₃, mE, hlr, hctl, hlock, hres, htick⟩ := hR
  rcases hlr.inv hs with hl | ⟨tr₄, e, r⟩
  · exact absurd ho (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₄ → CallHostEvent ⟨0⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  have hq := quiet hctl (by rw [hres]; simp) htick _ tr₄ m' le_rfl r hev'
  rcases hq with rfl | hl
  · cases out with
    | resolved r => exact congrArg _ (Option.some.inj (ho.2.2.symm.trans hres))
    | trap => exact absurd (ho.symm.trans hlock) (by decide)
    | deadlock => exact absurd (ho.2.symm.trans hres) (by simp)
  · exact absurd ho (hl.not_holds _ _)

/-- After a trapping suffix, the only outcome is the trap. -/
theorem out_of_trapsNext {m₁ m' : Machine.Config (E3 P) Unit}
    {tr : List (Label (E3 P) Unit)} {out : CallOutcome} (hT : TrapsNext prof P m₁)
    (hs : Steps prof (refHost P).hr (D P) m₁ tr m')
    (ho : out.Holds (refHost P).hr ⟨0⟩ m') : out = .trap := by
  obtain ⟨mT, r, hlr, hlive, hu⟩ := hT
  rcases hlr.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  cases r' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    rw [steps_of_locked rfl rfl r''] at ho
    exact holds_trapCfg ho

/-- A resolving suffix does not diverge. -/
theorem resolves_not_diverges {m₁ : Machine.Config (E3 P) Unit} {rs : List Val}
    (hR : Resolves prof P m₁ rs) : ¬ Diverges prof (refHost P).hr (D P) m₁ := by
  obtain ⟨tr₃, mE, hlr, hctl, -⟩ := hR
  exact fun hd => not_diverges_of_ctl_nil hctl (hlr.diverges hd)

/-- A trapping suffix does not diverge. -/
theorem trapsNext_not_diverges {m₁ : Machine.Config (E3 P) Unit} (hT : TrapsNext prof P m₁) :
    ¬ Diverges prof (refHost P).hr (D P) m₁ := by
  obtain ⟨mT, r, hlr, -, hu⟩ := hT
  intro hd
  obtain ⟨m', ⟨l, -, s⟩, hd'⟩ := (hlr.diverges hd).unfold
  obtain ⟨-, rfl⟩ := hu.2 _ _ s
  exact not_diverges_trapCfg _ hd'

end Outcomes

/-! ## The call phase -/

section Call

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val}

/-- The static facts of a call of export `x` of `c` on `vs`. -/
structure CallCtx (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P P).Store (CanonHost (core3P P))) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) : Prop where
  inst : c.mod.IsInst I
  store : Store.mapH (fun _ => 0) cs = I.store
  core : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)
  typed : ValTy.checkList x.ty.params vs = true

/-- The lowered arguments have the flat parameter types. -/
theorem CallCtx.lowered (C : CallCtx P c I cs x vs) :
    (lowerArgs x.ty.params vs).map (·.type) = ValTy.flatList x.ty.params :=
  lowerList_types _ _ C.typed

/-- The specification of a call with typed arguments. -/
theorem CallCtx.spec (C : CallCtx P c I cs x vs) {b : Silmaril.Wasm.Component.Reference.Outcome}
    (h : ∃ r ∈ coreOut P c.mod x.core (lowerArgs x.ty.params vs), b = liftOutcome x.ty r) :
    b ∈ exportSpec P c x vs := by
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd C.typed h)]
  unfold exportSpec
  rw [hl]
  exact .inl h

/-- **Calls after the core activation left it.** -/
theorem exit_spec (C : CallCtx P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hat : CallAt prof P cs x (I.addrs.getD x.core 0) vs M₀ th K segs rest) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) y)
    {l : Label (E3 P) Unit} {m₁ m' : Machine.Config (E3 P) Unit} {tr : List (Label (E3 P) Unit)}
    {out : CallOutcome} (hx : CoreExit M₀ th K segs rest y l m₁)
    (hs : Steps prof (refHost P).hr (D P) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨0⟩ m') : Outcome.ofCall out ∈ exportSpec P c x vs := by
  obtain ⟨nm, hcore⟩ := C.core
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨hout, hty⟩ := values_coreOut C.inst C.store rfl hcore C.lowered hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      rw [out_of_resolves (hat.ret y ys ws hty hl) hs hev ho]
      exact C.spec ⟨_, hout, by simp only [Outcome.ofCall, liftOutcome, hl]⟩
    | none =>
      rw [out_of_trapsNext (hat.trap y ys hty hl) hs ho]
      exact C.spec ⟨_, hout, by simp only [Outcome.ofCall, liftOutcome, hl]⟩
  · rw [steps_of_locked rfl rfl hs] at ho
    rw [holds_trapCfg ho]
    exact C.spec ⟨_, trap_coreOut C.inst C.store rfl hy hst, rfl⟩
  · exact (no_callout C.inst C.store rfl hcore C.lowered hy hst).elim

/-- **Divergence after the core activation left it** is impossible. -/
theorem exit_not_diverges (C : CallCtx P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hat : CallAt prof P cs x (I.addrs.getD x.core 0) vs M₀ th K segs rest) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) y)
    {l : Label (E3 P) Unit} {m₁ : Machine.Config (E3 P) Unit}
    (hx : CoreExit M₀ th K segs rest y l m₁) : ¬ Diverges prof (refHost P).hr (D P) m₁ := by
  obtain ⟨nm, hcore⟩ := C.core
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨-, hty⟩ := values_coreOut C.inst C.store rfl hcore C.lowered hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws => exact resolves_not_diverges (hat.ret y ys ws hty hl)
    | none => exact trapsNext_not_diverges (hat.trap y ys hty hl)
  · exact not_diverges_trapCfg _
  · exact (no_callout C.inst C.store rfl hcore C.lowered hy hst).elim

/-- The host invocation from `afterInst`. -/
theorem invoke_inv {fs : List (CFuncInst (core3P P))} {j : Nat} {args : List Val}
    {m : Machine.Config (E3 P) Unit}
    (h : Step prof (refHost P).hr (D P) (afterInst P cs fs) (.host (.invoke ⟨0⟩ ⟨j⟩ args)) m) :
    m = invokedCfg P cs fs j args := by
  cases h
  rfl

end Call

section Main

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val} {fs : List (CFuncInst (core3P P))} {j : Nat}
  {M₀ : Machine.Config (E3 P) Unit} {th : Option ThreadId}
  {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
  {rest : List (Activation (E3 P) Unit)} {tr₁ : List (Label (E3 P) Unit)}

/-- The specification of a divergent call with typed arguments. -/
theorem CallCtx.spec_diverges (C : CallCtx P c I cs x vs)
    (h : coreDiverges P c.mod x.core (lowerArgs x.ty.params vs)) :
    .diverges ∈ exportSpec P c x vs := by
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd C.typed h)]
  unfold exportSpec
  rw [hl]
  exact .inr ⟨rfl, h⟩

/-- **Terminating calls** follow the specification. -/
theorem calls_spec (C : CallCtx P c I cs x vs)
    (hpre : LRun prof (refHost P).hr (D P) (invokedCfg P cs fs j (vs.map toRefVal)) tr₁ M₀)
    (hat : CallAt prof P cs x (I.addrs.getD x.core 0) vs M₀ th K segs rest)
    {m' : Machine.Config (E3 P) Unit} {out : CallOutcome}
    (hcalls : Calls prof (refHost P).hr (D P) (afterInst P cs fs) ⟨0⟩ ⟨j⟩ (vs.map toRefVal) m'
      out) : Outcome.ofCall out ∈ exportSpec P c x vs := by
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, s, r⟩ := Steps.cons_iff.mp hs
  rw [invoke_inv s] at r
  rcases hpre.inv r with hl | ⟨tr'', e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  rw [eq_coreCfg hat.ctl, hat.core] at r'
  rcases coreCfg_steps_inv r' with ⟨y, -, rfl, -⟩ | ⟨y, pre, l, m₁, tr₂, hy, -, e', hx, r''⟩
  · have hl : Live (coreCfg M₀ th K segs rest y) := ⟨List.cons_ne_nil _ _, hat.lock⟩
    exact absurd ho (hl.not_holds _ _)
  · have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev := fun ev hm =>
      hev ev (by rw [e, e']; exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_cons_of_mem _ hm)))
    exact exit_spec C hat hy hx r'' hev' ho

/-- **Divergent calls** follow the specification. -/
theorem diverges_spec (C : CallCtx P c I cs x vs)
    (hpre : LRun prof (refHost P).hr (D P) (invokedCfg P cs fs j (vs.map toRefVal)) tr₁ M₀)
    (hat : CallAt prof P cs x (I.addrs.getD x.core 0) vs M₀ th K segs rest)
    (hd : CallDiverges prof (refHost P).hr (D P) (afterInst P cs fs) ⟨0⟩ ⟨j⟩ (vs.map toRefVal)) :
    coreDiverges P c.mod x.core (lowerArgs x.ty.params vs) := by
  obtain ⟨m₂, s, hd⟩ := hd
  rw [invoke_inv s] at hd
  have hd₀ := hpre.diverges hd
  rw [eq_coreCfg hat.ctl, hat.core] at hd₀
  rcases coreCfg_diverges_inv hd₀ with hi | ⟨y, l, m₁, hy, hx, hd'⟩
  · exact diverges_core C.inst C.store rfl hi
  · exact (exit_not_diverges C hat hy hx hd').elim

/-- The `j`-th lifted function. -/
theorem liftedFuncs_get? (c : Simple) (addr : Nat → Nat) {j : Nat}
    (hj : j < c.exports.length) :
    (liftedFuncs P addr c)[j]? =
      some (.lifted (addr c.exports[j].core) (liftedFt c.exports[j]) {} ⟨0⟩) := by
  simp only [liftedFuncs, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]

end Main

/-- **The call phase of `RefToSpecAll`.** -/
theorem callPhase : CallPhase := by
  intro P prof c hc hf ha I cs hI hcs j hj vs hvs b hb
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem hj
  have C : CallCtx P c I cs c.exports[j] vs := ⟨hI, hcs, hc.core _ hx, hvs⟩
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_at prof cs _ j _ c.exports[j] vs hff hvs
    hmax hres hmaxr hffr (liftedFuncs_get? c (fun k => I.addrs.getD k 0) hj)
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, hd⟩
  · exact calls_spec C hpre hat hcalls
  · exact C.spec_diverges (diverges_spec C hpre hat hd)

end Silmaril.Proofs.Wasm.Component.Reference
