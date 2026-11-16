module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.CallAt
public import Silmaril.Proofs.Wasm.Component.Reference.MultiSeq
public import Silmaril.Proofs.Wasm.Component.Core3G.Sim

/-!
# The reference machine follows the specification: forward runs

The converse of the reference half of soundness (`seq_refToSpec`): every chain of returned calls
of the canonical-ABI specification (`SeqSpec`), followed by a terminating outcome of the last
call (`specAt`), is a behaviour of the reference machine (`seq_specToRef`). The machine run is
built, not inverted:

* instantiation (`inst_forward`): the deterministic run of `inst_detRunL` from the host event;
* each call (`call_forward_ret`, `call_forward_out`): the host's invocation, the deterministic
  prefix of `call_at_kS`, the core activation, and the deterministic suffix (`ResolvesAt`, or
  `TrapsNextS` where the lift fails);
* the core activation (`coreSteps_of_reach`): a host-free run of the instance's Core store is
  a run of the machine's core activation. The machine's store has host type `CanonHost`; it has
  no host function (the instance has no import), so it is the renaming of the instance's store
  (`mapH_mapH_of_noHostFns`), and host-free steps carry over (`internalP_mapH'`). Every step of a
  host-free run starts at a running status (`statusP_running_of`: no value, trap or exception
  at the top, no host-call redex).

No determinism is needed: the machine follows the given Core run, at every profile `P` and
component choice profile `prof`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)
open Silmaril.Wasm.Execution.Core (Store Config Steps invoke vals throwing Result)
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat?)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
open Silmaril.Wasm.Game (InternalP Reach ResultAt statusP)

/-! ## Stores without host functions -/

section HostFree

variable {H H' : Type}

/-- The store has no host function. -/
def NoHostFns (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ h, fi.code ≠ Silmaril.Wasm.Execution.Core.FuncCode.host h

theorem noHostFns_of_mapH {f : H → H'} {s : Store H} (h : NoHostFns (Store.mapH f s)) :
    NoHostFns s := by
  intro fi hfi hh hc
  have hm : FuncInst.mapH f fi ∈ (Store.mapH f s).funcs := List.mem_map_of_mem hfi
  exact h _ hm (f hh) (by simp [FuncInst.mapH, hc, FuncCode.mapH])

theorem mapH_mapH_of_noHostFns (f : H → H') (g : H' → H) {s : Store H} (hs : NoHostFns s) :
    Store.mapH g (Store.mapH f s) = s := by
  have hf : (s.funcs.map (FuncInst.mapH f)).map (FuncInst.mapH g) = s.funcs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id s.funcs]
    apply List.map_congr_left
    intro fi hfi
    obtain ⟨ty, mo, code⟩ := fi
    cases code with
    | wasm fn => rfl
    | host hh => exact absurd rfl (hs _ hfi hh)
  cases s
  simp only [Store.mapH] at hf ⊢
  rw [hf]

theorem noHostFns_of_wf {I : Silmaril.Wasm.Game.ScalarInstance} (hI : I.imports = [])
    {s : Store Nat} (hw : I.WellFormed s) : NoHostFns s := by
  intro fi hfi h hc
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hfi
  obtain ⟨hlt, -⟩ := hw.host_type a fi h ha hc
  have h0 : I.imports.length = 0 := by rw [hI]; rfl
  omega

/-- Host-free thread steps commute with renaming the host type. -/
theorem internalP_mapH' {P : Profile} (g : H → H') {x y : Store H × STh}
    (h : InternalP P x y) : InternalP P (Store.mapH g x.1, x.2) (Store.mapH g y.1, y.2) := by
  obtain ⟨f', code', hy, hs⟩ := h
  refine ⟨f', code', hy, ?_⟩
  have hc : Config.mapH g (x.2.config x.1) = x.2.config (Store.mapH g x.1) := by
    cases x.2 with
    | pending a args => exact invoke_mapH g _ _ _
    | active f code => rfl
  have hs' := Step.mapH g hs
  rw [hc] at hs'
  exact hs'

theorem config_code_mapH' (g : H → H') (s : Store H) (t : STh) :
    (t.config (Store.mapH g s)).code = (t.config s).code := by
  cases t with
  | pending a args => exact congrArg Config.code (invoke_mapH g _ _ _).symm
  | active f code => rfl

/-- **A thread with a host-free step is running.** -/
theorem statusP_running_of {P : Profile} {s : Store H} {t : STh} {y : Store H × STh}
    (h : InternalP P (s, t) y) : statusP P s t = .running := by
  have hy : ∃ y, InternalP P (s, t) y := ⟨y, h⟩
  obtain ⟨f', code', -, hs⟩ := h
  have hq := Silmaril.Wasm.SingleThreaded.Step.not_quiet hs
  have hn := Silmaril.Wasm.SingleThreaded.decompose?_none_of_noRedex
    (Silmaril.Wasm.SingleThreaded.Step.noRedex hs)
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hn
  unfold statusP
  dsimp only
  split_ifs with h1 h2 h3
  · obtain ⟨vs, hv⟩ := h1
    exact absurd (hv ▸ Silmaril.Wasm.SingleThreaded.quiet_vals vs) hq
  · exact absurd (h2 ▸ Silmaril.Wasm.SingleThreaded.quiet_trap) hq
  · obtain ⟨a, ha⟩ := h3
    exact absurd (ha ▸ Silmaril.Wasm.SingleThreaded.quiet_throwing a) hq
  · simp only [hn]

end HostFree

/-! ## The core activation -/

section Core

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-- **Runs of the core activation are machine runs**, labelled by core steps. -/
theorem coreCfg_steps_of {B : Machine.Config E σ} {th : Option ThreadId}
    {K : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x y : CoreSt E}
    (h : Relation.ReflTransGen (CoreStep E) x y) :
    ∃ tr, (∀ l ∈ tr, l = .core) ∧
      Machine.Steps prof hr dispatch (coreCfg B th K segs rest x) tr (coreCfg B th K segs rest y) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], ⟨fun _ h => absurd h List.not_mem_nil, .refl _⟩⟩
  | head hs _ ih =>
    obtain ⟨tr, htr, r⟩ := ih
    obtain ⟨hst, hi⟩ := hs
    refine ⟨.core :: tr, ?_, .cons (Step.coreInternal rfl hst hi) r⟩
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · rfl
    · exact htr l hl

end Core

variable {P : Profile}

/-- **A host-free run of the instance's store is a run of the machine's core activation**, on
the store renamed to the machine's host type. -/
theorem coreSteps_of_reach (g : Nat → CanonHost (E3 P)) {x y : Store Nat × STh}
    (h : Reach P x y) :
    Relation.ReflTransGen (CoreStep (E3 P)) (Store.mapH g x.1, x.2) (Store.mapH g y.1, y.2) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hs ih =>
    have hs' : InternalP P (Store.mapH g b.1, b.2) (Store.mapH g c.1, c.2) := internalP_mapH' g hs
    refine ih.tail ⟨.inl ?_, hs'⟩
    show flatStatus (statusP P (Store.mapH g b.1) b.2) = .running
    rw [statusP_running_of hs']
    rfl

/-- A host code of the machine. -/
def someHost (P : Profile) : Nat → CanonHost (E3 P) := fun _ => .embedder "" ⟨[], []⟩

/-! ## Machine traces -/

section Labels

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

theorem steps_append {m₁ m₂ m₃ : Machine.Config E σ} {tr₁ tr₂ : List (Label E σ)}
    (h₁ : Machine.Steps prof hr dispatch m₁ tr₁ m₂) (h₂ : Machine.Steps prof hr dispatch m₂ tr₂ m₃) :
    Machine.Steps prof hr dispatch m₁ (tr₁ ++ tr₂) m₃ := by
  induction h₁ with
  | refl => exact h₂
  | cons s _ ih => exact .cons s (ih h₂)

/-- A trap step locks the store down. -/
theorem step_trap_lockdown {m m' : Machine.Config E σ} {r : TrapReason}
    (h : Step prof hr dispatch m (.trap r) m') : m'.store.lockdown = true := by
  cases h <;> rfl

/-- Live runs have no host event. -/
theorem LRun.no_host {m m' : Machine.Config E σ} {tr : List (Label E σ)}
    (h : LRun prof hr dispatch m tr m') : ∀ ev, Label.host ev ∉ tr := by
  induction h with
  | refl => intro _ h; exact nomatch h
  | cons hl s _ ih =>
    intro ev hm
    rcases List.mem_cons.mp hm with he | hm
    · subst he
      exact hl.1 (Step.host_ready s.1).1
    · exact ih ev hm

/-- A live run ending live has no trap. -/
theorem LRun.no_trap {m m' : Machine.Config E σ} {tr : List (Label E σ)}
    (h : LRun prof hr dispatch m tr m') (hl' : Live m') : ∀ r, Label.trap r ∉ tr := by
  induction h with
  | refl => intro _ h; exact nomatch h
  | cons hl s r ih =>
    intro t hm
    rcases List.mem_cons.mp hm with he | hm
    · subst he
      have hlock := step_trap_lockdown s.1
      cases r with
      | refl => exact absurd hlock (by rw [hl'.2]; decide)
      | cons hl₁ _ _ => exact absurd hlock (by rw [hl₁.2]; decide)
    · exact ih hl' t hm

theorem not_host_of_core {tr : List (Label E σ)} (h : ∀ l ∈ tr, l = .core) :
    ∀ ev, Label.host ev ∉ tr := fun ev hm => by cases h _ hm

theorem not_trap_of_core {tr : List (Label E σ)} (h : ∀ l ∈ tr, l = .core) :
    ∀ r, Label.trap r ∉ tr := fun r hm => by cases h _ hm

end Labels

/-! ## One call -/

section Call

variable {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val} {ι : InstState} {fs : List (CFuncInst (core3P P))}
  {G : Garb P} {k j : Nat}

/-- The host's invocation of call `k` from a configuration between calls. -/
theorem invoke_step (R : ReadyAt I cs ι G k) (args : List Silmaril.Wasm.Component.Reference.Val) :
    Step prof (refHost P).hr (D P) (readyCfg cs ι fs G) (.host (.invoke ⟨k⟩ ⟨j⟩ args))
      (invokedAt cs ι fs G k j args) := by
  refine Step.hostInvoke ⟨rfl, rfl, rfl⟩ fun y hy e => ?_
  have hlt := R.fresh.pending y hy
  rw [e] at hlt
  exact Nat.lt_irrefl _ hlt

/-- The static data of a call: the deterministic prefix up to the core activation and its
continuation. -/
structure CallRun (prof : ProfileKind) (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (I : Silmaril.Wasm.Game.ScalarInstance) : Prop where
  run : ∃ M₀ th K segs rest tr₁, LRun prof (refHost P).hr (D P)
      (invokedAt cs ι fs G k j (vs.map toRefVal)) tr₁ M₀ ∧
    CallAtKS prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x (I.addrs.getD x.core 0) vs
      M₀ th K segs rest

theorem callRun (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (hff : floatFreeList x.ty.params = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted (I.addrs.getD x.core 0) (liftedFt x) {} ⟨0⟩)) :
    CallRun prof P cs ι fs G k j x vs I :=
  ⟨call_at_kS prof cs ι _ fs G k j _ x vs hff C.typed hmax hres hmaxr hffr
    (addThread?_ok R.threads _) (removeThread?_enter _ _) hf⟩

/-- The machine store of the call is the renaming of its Core store. -/
theorem store_eq (C : CallCtxAt P c I cs x vs) :
    Store.mapH (someHost P) (Store.mapH (fun _ => (0 : Nat)) cs) = cs :=
  mapH_mapH_of_noHostFns _ _ (noHostFns_of_mapH (noHostFns_of_wf C.inst.2.1 C.wf))

/-- The core activation of a call, run from its start to a result `res` at the store `s'`. -/
theorem core_to_result (C : CallCtxAt P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
      (lowerArgs x.ty.params vs)) K, segs⟩ :: rest) (hcore : M₀.core = cs)
    {s' : Store Nat} {t' : STh}
    (run : Reach P (Store.mapH (fun _ => 0) cs,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) (s', t')) :
    ∃ tr, (∀ l ∈ tr, l = .core) ∧ Machine.Steps prof (refHost P).hr (D P) M₀ tr
      (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')) := by
  have h := coreSteps_of_reach (someHost P) run
  rw [store_eq C] at h
  obtain ⟨tr, htr, r⟩ := coreCfg_steps_of (prof := prof) (hr := (refHost P).hr) (dispatch := D P)
    (B := M₀) (th := th) (K := K) (segs := segs) (rest := rest) h
  exact ⟨tr, htr, eq_core_k hctl hcore ▸ r⟩

/-- **A returned call of the specification is a resolved call of the machine**, ending at the
next configuration between calls, whose Core store is the store the call left. -/
theorem call_forward_ret (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (CR : CallRun prof P cs ι fs G k j x vs I) {ws : List Silmaril.Wasm.Component.Val}
    {s' : Store Nat} (hret : RetAt P c I x vs (Store.mapH (fun _ => 0) cs) ws s') :
    ∃ cs', Store.mapH (fun _ => (0 : Nat)) cs' = s' ∧
      Calls prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal)
        (nextCfg cs' ι fs G x k j (I.addrs.getD x.core 0) (vs.map toRefVal) (ws.map toRefVal))
        (.resolved (some (ws.map toRefVal))) := by
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := CR.run
  obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := hret.run
  obtain ⟨tr₂, htr₂, r₂⟩ := core_to_result (prof := prof) C hat.toCallAtK.ctl hat.toCallAtK.core run
  obtain ⟨nm, hcore⟩ := C.core
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  have hxs : (lowerArgs x.ty.params vs).map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact C.lowered
  have steps : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke (Store.mapH (fun _ => 0) cs) (I.addrs.getD x.core 0)
        ((lowerArgs x.ty.params vs).map ofFlat)) (t'.config s') :=
    internalP_steps (H := Nat) run
  have hty : ys.map (·.type) = ValTy.flatList x.ty.results := by
    have ht := run_typed_at C.inst C.wf hk hxs steps final hys
    rw [hget] at ht
    exact ht
  have hst : (E3 P).status (Store.mapH (someHost P) s') t' = .returned (.values ys) := by
    show flatStatus (statusP P _ _) = _
    rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values
      ((config_code_mapH' _ _ _).trans final)]
    simp only [flatStatus, hys]
  have s₃ : Step prof (refHost P).hr (D P)
      (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')) .tau
      (retCfg M₀ th K segs rest (Store.mapH (someHost P) s', t') ys) :=
    Step.coreReturned rfl hst
  obtain ⟨tr₃, mE, hlr, rfl⟩ := hat.toCallAtK.ret (Store.mapH (someHost P) s', t') ys ws hty hws
  have hwf : I.WellFormed s' :=
    hret.wellFormed C.inst C.core C.wf
  have hs' : Store.mapH (fun _ => (0 : Nat)) (Store.mapH (someHost P) s') = s' :=
    mapH_mapH_of_noHostFns _ _ (noHostFns_of_wf C.inst.2.1 hwf)
  refine ⟨Store.mapH (someHost P) s', hs', tr₁ ++ (tr₂ ++ (.tau :: tr₃)), ?_, ?_, ?_, ?_⟩
  · exact .cons (invoke_step R _) (steps_append hpre.steps (steps_append r₂ (.cons s₃ hlr.steps)))
  · intro ev hm
    exfalso
    rcases List.mem_append.mp hm with hm | hm
    · exact LRun.no_host hpre ev hm
    rcases List.mem_append.mp hm with hm | hm
    · exact not_host_of_core htr₂ ev hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact LRun.no_host hlr ev hm
  · intro h
    cases h
  · refine ⟨rfl, rfl, ?_⟩
    exact result?_next R.fresh x j _ _ _ _ _ _

/-- **A terminating outcome of the core activation is a call outcome of the machine.** -/
theorem call_forward_out (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (CR : CallRun prof P cs ι fs G k j x vs I) {r : Option (List Flat)}
    (hr : r ∈ coreAt P I x.core (lowerArgs x.ty.params vs) (Store.mapH (fun _ => 0) cs)) :
    ∃ m' out, Calls prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal) m'
      out ∧ Outcome.ofCall out = liftOutcome x.ty r := by
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := CR.run
  obtain ⟨c', res, steps, final, rfl⟩ := hr
  obtain ⟨s', t', run, final'⟩ := (Silmaril.Wasm.Game.ret_iff_core (s := Store.mapH (fun _ => 0) cs)
    (t := Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
      (lowerArgs x.ty.params vs))).mpr ⟨c', steps, final⟩
  obtain ⟨tr₂, htr₂, r₂⟩ := core_to_result (prof := prof) C hat.toCallAtK.ctl hat.toCallAtK.core run
  obtain ⟨nm, hcore⟩ := C.core
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  have hxs : (lowerArgs x.ty.params vs).map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact C.lowered
  have hlive : Live M₀ := ⟨by rw [hat.toCallAtK.ctl]; exact List.cons_ne_nil _ _,
    hat.toCallAtK.lock⟩
  have hcode : (t'.config (Store.mapH (someHost P) s')).code = res.toAdmin :=
    (config_code_mapH' _ _ _).trans final'
  have hinv : Machine.Steps prof (refHost P).hr (D P) (readyCfg cs ι fs G)
      (.host (.invoke ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) :: (tr₁ ++ tr₂))
      (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')) :=
    .cons (invoke_step R _) (steps_append hpre.steps r₂)
  have hnh : ∀ ev, Label.host ev ∉ tr₁ ++ tr₂ := by
    intro ev hm
    rcases List.mem_append.mp hm with hm | hm
    · exact LRun.no_host hpre ev hm
    · exact not_host_of_core htr₂ ev hm
  have hnt : ∀ r, Label.trap r ∉ tr₁ ++ tr₂ := by
    intro r hm
    rcases List.mem_append.mp hm with hm | hm
    · exact LRun.no_trap hpre hlive r hm
    · exact not_trap_of_core htr₂ r hm
  -- a trap of the core activation
  have trapCase : (E3 P).status (Store.mapH (someHost P) s') t' = .returned .trap →
      ∃ m' out, Calls prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal)
        m' out ∧ Outcome.ofCall out = .traps := by
    intro hst
    have s₃ : Step prof (refHost P).hr (D P)
        (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')) (.trap .coreTrap)
        (trapCfg (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t'))) :=
      Step.coreTrap rfl hst
    refine ⟨trapCfg (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')), .trap,
      ⟨(tr₁ ++ tr₂) ++ [.trap .coreTrap], ?_, ?_, ?_, ?_⟩, rfl⟩
    · simpa only [List.cons_append] using steps_append hinv (.cons s₃ (.refl _))
    · intro ev hm
      rcases List.mem_append.mp hm with hm | hm
      · exact absurd hm (hnh ev)
      · simp at hm
    · intro _ msg hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hnt _ hm
      · simp at hm
    · exact trapCfg_lockdown _
  cases res with
  | trap =>
    exact trapCase (by
      show flatStatus (statusP P _ _) = _
      rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_trap hcode]
      rfl)
  | throw a =>
    exact trapCase (by
      show flatStatus (statusP P _ _) = _
      rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_throwing hcode]
      rfl)
  | values cvs =>
    -- the values are flat: they have the result types of the export
    obtain ⟨w, hw⟩ := answer_at C.inst C.wf hk hxs steps final
    have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
        (I.exports.get (opAt C.inst hk hxs).1).results cvs := by
      unfold Silmaril.Wasm.Game.Answer.ofResult? at hw
      dsimp only at hw
      split_ifs at hw with ht
      exact ht
    rw [opAt_type] at htyped
    obtain ⟨ys, hys⟩ : ∃ ys, cvs.mapM toFlat? = some ys :=
      Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
    have hty : ys.map (·.type) = ValTy.flatList x.ty.results := by
      have ht := run_typed_at C.inst C.wf hk hxs steps final hys
      rw [hget] at ht
      exact ht
    have hst : (E3 P).status (Store.mapH (someHost P) s') t' = .returned (.values ys) := by
      show flatStatus (statusP P _ _) = _
      rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values hcode]
      simp only [flatStatus, hys]
    have s₃ : Step prof (refHost P).hr (D P)
        (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')) .tau
        (retCfg M₀ th K segs rest (Store.mapH (someHost P) s', t') ys) :=
      Step.coreReturned rfl hst
    have hpre' : Machine.Steps prof (refHost P).hr (D P) (readyCfg cs ι fs G)
        (.host (.invoke ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) :: ((tr₁ ++ tr₂) ++ [.tau]))
        (retCfg M₀ th K segs rest (Store.mapH (someHost P) s', t') ys) := by
      simpa only [List.cons_append] using steps_append hinv (.cons s₃ (.refl _))
    dsimp only
    rw [hys]
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      obtain ⟨tr₃, mE, hlr, rfl⟩ := hat.toCallAtK.ret _ ys ws hty hl
      refine ⟨readyCfg (Store.mapH (someHost P) s') (InstState.removeThread 1
          (enterInst ι ⟨G.threads.length⟩)) fs
          (nextGarb G x k j (I.addrs.getD x.core 0) (vs.map toRefVal) (ws.map toRefVal)),
        .resolved (some (ws.map toRefVal)),
        ⟨((tr₁ ++ tr₂) ++ [.tau]) ++ tr₃, ?_, ?_, (fun h => nomatch h), ?_⟩, ?_⟩
      · simpa only [List.cons_append] using steps_append hpre' hlr.steps
      · intro ev hm
        exfalso
        rcases List.mem_append.mp hm with hm | hm
        · rcases List.mem_append.mp hm with hm | hm
          · exact hnh ev hm
          · simp at hm
        · exact LRun.no_host hlr ev hm
      · exact ⟨rfl, rfl, result?_next R.fresh x j _ _ _ _ _ _⟩
      · simp only [Outcome.ofCall, liftOutcome, hl]
    | none =>
      obtain ⟨mT, rT, hrT, hl₁, hlive₁, hu⟩ := hat.trapS _ ys hty hl
      have hmT : Machine.Steps prof (refHost P).hr (D P) (readyCfg cs ι fs G)
          (.host (.invoke ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) ::
            ((((tr₁ ++ tr₂) ++ [.tau]) ++ [.tau]) ++ [.trap rT])) (trapCfg mT) := by
        simpa only [List.cons_append] using
          steps_append (steps_append hpre' hl₁.steps) (.cons hu.1 (.refl _))
      refine ⟨trapCfg mT, .trap, ⟨_, hmT, ?_, ?_, rfl⟩, ?_⟩
      · intro ev hm
        exfalso
        rcases List.mem_append.mp hm with hm | hm
        · rcases List.mem_append.mp hm with hm | hm
          · rcases List.mem_append.mp hm with hm | hm
            · exact hnh ev hm
            · simp at hm
          · simp at hm
        · simp at hm
      · intro _ msg hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases List.mem_append.mp hm with hm | hm
          · rcases List.mem_append.mp hm with hm | hm
            · exact hnt _ hm
            · simp at hm
          · simp at hm
        · simp only [List.mem_singleton, Label.trap.injEq] at hm
          exact hrT msg hm.symm
      · simp only [Outcome.ofCall, liftOutcome, hl]

end Call

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
