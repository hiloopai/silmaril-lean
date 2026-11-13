module

public import Silmaril.Proofs.Wasm.Component.FXEngine.HostMap
public import Silmaril.Proofs.Wasm.Component.FXRefE.Run
public import Silmaril.Proofs.Wasm.Component.FXEngineV.Lawful
public import Silmaril.Wasm.Component.FXEngineV.Defs

/-!
# Changing the host type of the WasmFX engine with suspension

The reference component machine runs the engine `fxEV P` in stores `Store (FXCode H)` with
`H = CanonHost (fxEV P)`, while the engine's own specification `exportSpecE` instantiates in
`Store (FXCode Nat)`. This module renames the component host code along `g : H → H'`
(`mapC g`: `FXCode.host h ↦ FXCode.host (g h)`, FX functions kept) and shows:

* `stepFX'_mapC`: a `StepFX'` step with no host is a step of the renamed configurations (all
  rules; the Core rule by `Reference.Step.mapH`);
* `internalV_mapC`, `steps_mapC`: engine steps and runs of `fxEV P` survive renaming;
* **host-freedom** (`HostFree s`: no function of `s` has component host code): it is kept by
  steps (`internalV_funcs`), and on a host-free store renaming is invertible
  (`mapC_mapC_of_hostFree`), so a renamed thread takes a step only if the thread does
  (`internalV_of_mapC`) and returned statuses are preserved (`statusV_mapC_returned`);
* `no_callout_of_hostFree`: a thread in a host-free store that is not parked is not at a
  callout.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXRefV

open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Game (statusP InternalP)
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH Config.mapH FuncInst.mapH FuncCode.mapH
  Store.mapH_funcs_getElem? Step.mapH funcs_mapH noHostH)
open Silmaril.Proofs.Wasm.Component.FXEngine (config_mapH' decompose?_mapH' mapR' step_funcs_eq)
open Silmaril.Proofs.Wasm.Component.FXRefE (internalP_mapH statusP_mapH_returned)
open Silmaril.Wasm.Execution.Core (Store Config Step Val Admin FuncInst Frame)
open Silmaril.Wasm.SingleThreaded (Thread decompose?)
open Silmaril.Wasm.Models.FX (ofCore ConfigFX ContFX AdminFX resolve blockFX cvals)
open Silmaril.Wasm.Models.FXV (StepFX' CtxV)
open Silmaril.Wasm.Component.Reference (flatStatus)
open Silmaril.Wasm.Numerics (Profile)

variable {H H' H'' : Type} {P : Profile}

/-! ## Renaming component host code -/

/-- Rename the component host code of an FX store code (FX functions are kept). -/
def mapC (g : H → H') : FXCode H → FXCode H'
  | .host h => .host (g h)
  | .fx F => .fx F

/-- The renamed store. -/
abbrev SM (g : H → H') (s : Store (FXCode H)) : Store (FXCode H') := Store.mapH (mapC g) s

/-- The renamed configuration. -/
def cfgC (g : H → H') (c : ConfigFX (FXCode H)) : ConfigFX (FXCode H') :=
  ⟨SM g c.store, c.conts, c.frame, c.code⟩

/-- The renamed thread. -/
def thrC (g : H → H') : ThreadV H → ThreadV H'
  | .core t => .core t
  | .fx K f code => .fx K f code
  | .parked K f E Ec h args => .parked K f E Ec (g h) args

theorem fxOf_mapC (g : H → H') (c : FXCode H) : fxOf (mapC g c) = fxOf c := by
  cases c <;> rfl

theorem blockFX_noHost (H : Type) : blockFX (noHostFX H) fxOf = noHostH (FXCode H) := by
  funext h s vs out
  simp [blockFX, noHostFX]

theorem resolve_SM (g : H → H') (s : Store (FXCode H)) (f : Frame) :
    resolve (SM g s) f = resolve s f := by
  funext c
  cases c <;> rfl

theorem tag?_SM (g : H → H') (s : Store (FXCode H)) (f : Frame) (x) :
    (SM g s).tag? f x = s.tag? f x := rfl

/-! ## Steps -/

/-- **A host-free `StepFX'` step survives renaming the component host code.** -/
theorem stepFX'_mapC (g : H → H') {x y : ConfigFX (FXCode H)}
    (h : StepFX' P (noHostFX H) fxOf x y) :
    StepFX' P (noHostFX H') fxOf (cfgC g x) (cfgC g y) := by
  induction h with
  | @core s s' K f f' cs cs' h =>
    have h₀ : Step P (noHostH (FXCode H)) ⟨s, f, cs⟩ ⟨s', f', cs'⟩ := blockFX_noHost H ▸ h
    have h₁ := Step.mapH (mapC g) h₀
    exact .core (blockFX_noHost H' ▸ h₁)
  | seq _ hne ih => exact .seq ih hne
  | ctxLabel _ ih => exact .ctxLabel ih
  | ctxFrame _ ih => exact .ctxFrame ih
  | ctxHandler _ ih => exact .ctxHandler ih
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | handlerVals => exact .handlerVals
  | dropCont => exact .dropCont
  | trapSeq hne => exact .trapSeq hne
  | trapLabel => exact .trapLabel
  | trapFrame => exact .trapFrame
  | trapHandler => exact .trapHandler
  | throwSeq hne => exact .throwSeq hne
  | throwLabel => exact .throwLabel
  | throwFrame => exact .throwFrame
  | throwHandler => exact .throwHandler
  | @invoke s K f c vs a fi h F hc hf hcode hfx hn =>
    refine .invoke (fi := FuncInst.mapH (mapC g) fi) (h := mapC g h) hc (funcs_mapH _ hf) ?_
      ((fxOf_mapC g h).trans hfx) hn
    simp only [FuncInst.mapH, hcode, FuncCode.mapH]
  | @contNew s K f a fi ct hf =>
    exact .contNew (fi := FuncInst.mapH (mapC g) fi) (funcs_mapH _ hf)
  | contNewNull => exact .contNewNull
  | contBind hk => exact .contBind hk
  | contBindNull => exact .contBindNull
  | contBindUsed hk => exact .contBindUsed hk
  | @resume s K f vs k C ct hs hs' hk hr =>
    exact .resume hk ((resolve_SM g s f).symm ▸ hr)
  | resumeNull => exact .resumeNull
  | resumeUsed hk => exact .resumeUsed hk
  | @resumeThrow s K f vs k C ct x hs hs' ta ti hk ht hr =>
    exact .resumeThrow hk ht ((resolve_SM g s f).symm ▸ hr)
  | resumeThrowNull => exact .resumeThrowNull
  | suspend ht hE hc => exact .suspend ht hE hc
  | switch hk ht hE hc => exact .switch hk ht hE hc

/-- A Core status is a callout exactly at a host-call redex of non-final code. -/
theorem statusP_of_decompose {s : Store H} {t : Thread}
    (n₁ : ¬ ∃ vs, (t.config s).code = Silmaril.Wasm.Execution.Core.vals vs)
    (n₂ : ¬ (t.config s).code = [.trap])
    (n₃ : ¬ ∃ a, (t.config s).code = Silmaril.Wasm.Execution.Core.throwing a)
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat} {c : H} {args : List Val}
    (hd : decompose? s (t.config s).code = some (E, a, c, args)) :
    statusP P s t = .callout c args := by
  unfold statusP
  dsimp only
  split_ifs
  all_goals rw [hd]

/-- A Core callout survives renaming the component host code. -/
theorem statusP_mapC_callout (g : H → H') {s : Store (FXCode H)} {t : Thread} {c : FXCode H}
    {args : List Val} (h : statusP P s t = .callout c args) :
    statusP P (SM g s) t = .callout (mapC g c) args := by
  have hc : (t.config (SM g s)).code = (t.config s).code := by
    rw [config_mapH']
    rfl
  obtain ⟨E, a, hd⟩ := Silmaril.Proofs.Wasm.Component.FXEngineV.decompose?_of_statusP_callout h
  obtain ⟨n₁, n₂, n₃⟩ : (¬ ∃ vs, (t.config s).code = Silmaril.Wasm.Execution.Core.vals vs) ∧
      ¬ (t.config s).code = [.trap] ∧
      ¬ ∃ a, (t.config s).code = Silmaril.Wasm.Execution.Core.throwing a := by
    unfold statusP at h
    dsimp only at h
    split_ifs at h
    all_goals first
      | cases h
      | exact ⟨by assumption, by assumption, by assumption⟩
  refine statusP_of_decompose (hc ▸ n₁) (hc ▸ n₂) (hc ▸ n₃) (E := E) (a := a) ?_
  rw [hc, decompose?_mapH', hd]
  rfl

/-- **An engine step survives renaming the component host code.** -/
theorem internalV_mapC (g : H → H') {s s' : Store (FXCode H)} {t t' : ThreadV H}
    (h : InternalV P (s, t) (s', t')) :
    InternalV P (SM g s, thrC g t) (SM g s', thrC g t') := by
  cases t with
  | core t₀ =>
    rcases h with ⟨t₁, rfl, h⟩ | ⟨⟨F, args, e⟩, K, f, code, rfl, h⟩
    · exact Or.inl ⟨t₁, rfl, internalP_mapH (mapC g) h⟩
    · refine Or.inr ⟨⟨F, args, statusP_mapC_callout g e⟩, K, f, code, rfl, ?_⟩
      have h' := stepFX'_mapC g h
      have e' : cfgC g (ofCore (t₀.config s)) = ofCore (t₀.config (SM g s)) := by
        rw [config_mapH']
        rfl
      rw [e'] at h'
      exact h'
  | fx K f code =>
    rcases h with ⟨K', f', code', rfl, h⟩ | ⟨rfl, E, cs, Ec, a, hh, args, rfl, hd, rfl⟩
    · exact Or.inl ⟨K', f', code', rfl, stepFX'_mapC g h⟩
    · refine Or.inr ⟨rfl, E, cs, Ec, a, g hh, args, rfl, ?_, rfl⟩
      rw [decompose?_mapH', hd]
      rfl
  | parked => exact h.elim

/-- Engine runs survive renaming the component host code. -/
theorem steps_mapC (g : H → H') {x y : Store (FXCode H) × ThreadV H}
    (h : Relation.ReflTransGen (InternalV P) x y) :
    Relation.ReflTransGen (InternalV P) (SM g x.1, thrC g x.2) (SM g y.1, thrC g y.2) :=
  Relation.ReflTransGen.lift (fun z : Store (FXCode H) × ThreadV H => (SM g z.1, thrC g z.2))
    (fun a b hab => internalV_mapC (s := a.1) (t := a.2) (s' := b.1) (t' := b.2) g hab) x y h

/-- Divergence survives renaming the component host code. -/
theorem diverges_mapC (g : H → H') {x : Store (FXCode H) × ThreadV H}
    (h : Silmaril.InfiniteTrace (InternalV P) x) :
    Silmaril.InfiniteTrace (InternalV P) (SM g x.1, thrC g x.2) :=
  Silmaril.InfiniteTrace.map (fun z : Store (FXCode H) × ThreadV H => (SM g z.1, thrC g z.2))
    (fun a b hab => internalV_mapC (s := a.1) (t := a.2) (s' := b.1) (t' := b.2) g hab) h

/-! ## Host-free stores -/

/-- No function of the store has component host code (Core and FX functions only). -/
def HostFree (s : Store (FXCode H)) : Prop :=
  ∀ fi ∈ s.funcs, ∀ h, fi.code ≠ .host (.host h)

theorem SM_comp (g : H → H') (g' : H' → H'') (s : Store (FXCode H)) :
    SM g' (SM g s) = SM (g' ∘ g) s := by
  have hf : (SM g' (SM g s)).funcs = (SM (g' ∘ g) s).funcs := by
    show (s.funcs.map (FuncInst.mapH (mapC g))).map (FuncInst.mapH (mapC g')) =
      s.funcs.map (FuncInst.mapH (mapC (g' ∘ g)))
    rw [List.map_map]
    refine List.map_congr_left fun fi _ => ?_
    rcases fi with ⟨ty, md, code⟩
    rcases code with _ | (_ | _) <;> rfl
  cases s
  simp only [Store.mapH] at hf ⊢
  rw [hf]

/-- **On a host-free store, renaming does not depend on the renaming.** -/
theorem SM_hostFree {s : Store (FXCode H)} (hs : HostFree s) (g₁ g₂ : H → H') :
    SM g₁ s = SM g₂ s := by
  have hf : (SM g₁ s).funcs = (SM g₂ s).funcs := by
    show s.funcs.map (FuncInst.mapH (mapC g₁)) = s.funcs.map (FuncInst.mapH (mapC g₂))
    refine List.map_congr_left fun fi hfi => ?_
    rcases fi with ⟨ty, md, code⟩
    rcases code with _ | (h | _)
    · rfl
    · exact absurd rfl (hs _ hfi h)
    · rfl
  cases s
  simp only [Store.mapH] at hf ⊢
  rw [hf]

theorem SM_id (s : Store (FXCode H)) : SM id s = s := by
  have hf : (SM id s).funcs = s.funcs := by
    show s.funcs.map (FuncInst.mapH (mapC id)) = s.funcs
    refine List.map_id'' (fun fi => ?_) s.funcs
    rcases fi with ⟨ty, md, code⟩
    rcases code with _ | (_ | _) <;> rfl
  cases s
  simp only [Store.mapH] at hf ⊢
  rw [hf]

/-- **On a host-free store, renaming is invertible.** -/
theorem mapC_mapC_of_hostFree {s : Store (FXCode H)} (hs : HostFree s) (g : H → H')
    (g' : H' → H) : SM g' (SM g s) = s := by
  rw [SM_comp, SM_hostFree hs (g' ∘ g) id, SM_id]

theorem hostFree_SM {s : Store (FXCode H)} (hs : HostFree s) (g : H → H') : HostFree (SM g s) := by
  intro fi hfi h e
  obtain ⟨fi₀, hfi₀, rfl⟩ := List.mem_map.1 hfi
  rcases fi₀ with ⟨ty, md, code⟩
  rcases code with _ | (h₀ | _)
  · cases e
  · exact hs _ hfi₀ h₀ rfl
  · cases e

/-- Two renamings into `Bool` that agree on a store make it host-free. -/
theorem hostFree_of_SM_eq {s : Store (FXCode H)}
    (he : SM (fun _ => true) s = SM (fun _ => false) s) : HostFree s := by
  intro fi hfi h e
  have hf := congrArg Store.funcs he
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hfi
  have h₁ := congrArg (·[k]?) hf
  simp only [SM, Store.mapH_funcs_getElem?, hk, Option.map_some, Option.some.injEq] at h₁
  have h₂ := congrArg FuncInst.code h₁
  simp [FuncInst.mapH, e, FuncCode.mapH, mapC] at h₂

/-! ## Host-free stores along runs -/

theorem stepFX'_funcs {x y : ConfigFX (FXCode H)} (h : StepFX' P (noHostFX H) fxOf x y) :
    y.store.funcs = x.store.funcs := by
  induction h with
  | core h => exact step_funcs_eq (blockFX_noHost H ▸ h)
  | seq _ _ ih => exact ih
  | ctxLabel _ ih => exact ih
  | ctxFrame _ ih => exact ih
  | ctxHandler _ ih => exact ih
  | _ => rfl

theorem internalV_funcs {s s' : Store (FXCode H)} {t t' : ThreadV H}
    (h : InternalV P (s, t) (s', t')) : s'.funcs = s.funcs := by
  cases t with
  | core t₀ =>
    rcases h with ⟨t₁, -, f', code', -, h⟩ | ⟨-, K, f, code, -, h⟩
    · have e := step_funcs_eq h
      rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at e
    · have e := stepFX'_funcs h
      simp only [ofCore] at e
      rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at e
  | fx K f code =>
    rcases h with ⟨K', f', code', -, h⟩ | ⟨rfl, -⟩
    · exact stepFX'_funcs h
    · rfl
  | parked => exact h.elim

theorem steps_funcs {x y : Store (FXCode H) × ThreadV H}
    (h : Relation.ReflTransGen (InternalV P) x y) : y.1.funcs = x.1.funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    exact (internalV_funcs (s := _) (t := _) (s' := _) (t' := _) hs).trans ih

theorem hostFree_of_funcs {s s' : Store (FXCode H)} (hs : HostFree s) (e : s'.funcs = s.funcs) :
    HostFree s' := by
  intro fi hfi
  exact hs fi (e ▸ hfi)

/-- In a host-free store no redex calls a component host function. -/
theorem decompose?_hostFree {s : Store (FXCode H)} (hs : HostFree s) {code : List Admin}
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat} {h : H} {args : List Val}
    (hd : decompose? s code = some (E, a, .host h, args)) : False := by
  have e₁ := decompose?_mapH' (mapC fun _ : H => true) s code
  have e₂ := decompose?_mapH' (mapC fun _ : H => false) s code
  rw [show Store.mapH (mapC fun _ : H => true) s = Store.mapH (mapC fun _ : H => false) s from
    SM_hostFree hs (fun _ => true) (fun _ => false)] at e₁
  rw [e₁, hd] at e₂
  simp [mapR', mapC] at e₂

/-- A Core thread in a host-free store is not at a component host call. -/
theorem statusP_hostFree {s : Store (FXCode H)} (hs : HostFree s) {t : Thread} {h : H}
    {args : List Val} (e : statusP P s t = .callout (.host h) args) : False := by
  obtain ⟨E, a, hd⟩ :=
    Silmaril.Proofs.Wasm.Component.FXEngineV.decompose?_of_statusP_callout e
  exact decompose?_hostFree hs hd

/-- **No step from a host-free store parks a thread.** -/
theorem internalV_not_parked {s s' : Store (FXCode H)} (hs : HostFree s) {t t' : ThreadV H}
    (h : InternalV P (s, t) (s', t')) (hp : ∀ K f E Ec hh args, t ≠ .parked K f E Ec hh args) :
    ∀ K f E Ec hh args, t' ≠ .parked K f E Ec hh args := by
  cases t with
  | core t₀ =>
    rcases h with ⟨t₁, rfl, -⟩ | ⟨-, K, f, code, rfl, -⟩
    · intros; exact fun e => by cases e
    · intros; exact fun e => by cases e
  | fx K f code =>
    rcases h with ⟨K', f', code', rfl, -⟩ | ⟨rfl, E, cs, Ec, a, hh, args, -, hd, -⟩
    · intros; exact fun e => by cases e
    · exact (decompose?_hostFree hs hd).elim
  | parked K f E Ec hh args => exact (hp K f E Ec hh args rfl).elim

/-- The callout status of a thread that is not parked, in a host-free store, is impossible. -/
theorem no_callout_of_hostFree {s : Store (FXCode H)} (hs : HostFree s) {t : ThreadV H}
    (hp : ∀ K f E Ec hh args, t ≠ .parked K f E Ec hh args) (h : H)
    (args : List Silmaril.Wasm.Component.Engine.FlatValue) :
    statusV P s t ≠ .callout h args := by
  intro e
  cases t with
  | core t₀ =>
    obtain ⟨args', e'⟩ := Silmaril.Proofs.Wasm.Component.FXEngineV.liftR_eq_callout e
    exact statusP_hostFree hs e'
  | fx K f code =>
    simp only [statusV] at e
    split_ifs at e
    exact Silmaril.Proofs.Wasm.Component.FXEngineV.fxResult_ne_callout code h args e
  | parked K f E Ec hh args' => exact hp K f E Ec hh args' rfl

/-! ## Statuses -/

/-- **A renamed thread in a host-free store steps only if the thread does.** -/
theorem internalV_of_mapC {s : Store (FXCode H)} (hs : HostFree s) (g : H → H') (g' : H' → H)
    {t : ThreadV H} (h : ∃ y, InternalV P (SM g s, thrC g t) y) : ∃ y, InternalV P (s, t) y := by
  obtain ⟨⟨s', t'⟩, hy⟩ := h
  have h' := internalV_mapC g' hy
  rw [mapC_mapC_of_hostFree hs] at h'
  cases t with
  | core t₀ => exact ⟨_, h'⟩
  | fx K f code => exact ⟨_, h'⟩
  | parked => exact hy.elim

theorem liftR_eq_returned {st : Silmaril.Wasm.SingleThreaded.Status (FXCode H)}
    {R : Silmaril.Wasm.Component.Engine.CallResult} (e : liftR st = .returned R) :
    ∃ r, st = .returned r := by
  rcases st with _ | r | ⟨c, args⟩ | _
  · cases e
  · exact ⟨r, rfl⟩
  · cases c with
    | host hh =>
      simp only [liftR, flatStatus] at e
      split at e <;> simp [mapHostS] at e
    | fx F => cases e
  · cases e

theorem liftR_returned {r : Silmaril.Wasm.SingleThreaded.CallResult}
    {R : Silmaril.Wasm.Component.Engine.CallResult}
    (h : liftR (.returned r : Silmaril.Wasm.SingleThreaded.Status (FXCode H)) = .returned R) :
    liftR (.returned r : Silmaril.Wasm.SingleThreaded.Status (FXCode H')) = .returned R := by
  rcases r with vs | _
  · simp only [liftR, flatStatus] at h ⊢
    cases hm : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? <;> simp only [hm, mapHostS] at h ⊢
    · cases h
    · cases Silmaril.Wasm.Component.Engine.Status.returned.inj h
      rfl
  · simp only [liftR, flatStatus, mapHostS] at h ⊢
    cases Silmaril.Wasm.Component.Engine.Status.returned.inj h
    rfl

set_option linter.unusedTactic false in
theorem fxResult_returned {code : List AdminFX} {R : Silmaril.Wasm.Component.Engine.CallResult}
    (h : (fxResult code : Silmaril.Wasm.Component.Engine.Status H) = .returned R) :
    (fxResult code : Silmaril.Wasm.Component.Engine.Status H') = .returned R := by
  unfold fxResult at h ⊢
  split_ifs at h ⊢ with h1
  · cases hm : h1.choose.mapM Silmaril.Wasm.SingleThreaded.toFlat? <;> simp only [hm] at h ⊢
    · cases h
    · cases Silmaril.Wasm.Component.Engine.Status.returned.inj h
      rfl
  all_goals
    cases h
    try rfl

/-- A returned status of a Core thread survives renaming. -/
theorem statusV_core_mapC_returned (g : H → H') {s : Store (FXCode H)} {t₀ : Thread}
    {R : Silmaril.Wasm.Component.Engine.CallResult}
    (h : liftR (statusP P s t₀) = .returned R) :
    liftR (statusP P (SM g s) t₀) = .returned R := by
  obtain ⟨r, hr⟩ := liftR_eq_returned h
  have h' : liftR (.returned r : Silmaril.Wasm.SingleThreaded.Status (FXCode H)) = .returned R :=
    hr ▸ h
  rw [statusP_mapH_returned (mapC g) hr]
  exact liftR_returned h'

/-- A returned status of an FX thread survives renaming, in a host-free store. -/
theorem statusV_fx_mapC_returned {s : Store (FXCode H)} (hs : HostFree s) (g : H → H')
    (g' : H' → H) {K : List (Option ContFX)} {f : Frame} {code : List AdminFX}
    {R : Silmaril.Wasm.Component.Engine.CallResult}
    (h : statusV P s (.fx K f code) = .returned R) :
    statusV P (SM g s) (.fx K f code) = .returned R := by
  have hn : ¬ ∃ y, InternalV P (s, .fx K f code) y := by
    intro hex
    have e : statusV P s (.fx K f code) = .running := by
      simp only [statusV, hex, ↓reduceIte]
    rw [e] at h
    cases h
  have h' : (fxResult code : Silmaril.Wasm.Component.Engine.Status H) = .returned R := by
    simpa only [statusV, hn, ↓reduceIte] using h
  have hn' : ¬ ∃ y, InternalV P (SM g s, .fx K f code) y :=
    fun hex => hn (internalV_of_mapC hs g g' (t := .fx K f code) hex)
  simpa only [statusV, hn', ↓reduceIte] using fxResult_returned h'

/-- **A returned status survives renaming, in a host-free store.** -/
theorem statusV_mapC_returned {s : Store (FXCode H)} (hs : HostFree s) (g : H → H')
    (g' : H' → H) {t : ThreadV H} {R : Silmaril.Wasm.Component.Engine.CallResult}
    (h : statusV P s t = .returned R) : statusV P (SM g s) (thrC g t) = .returned R := by
  cases t with
  | core t₀ => exact statusV_core_mapC_returned g h
  | fx K f code => exact statusV_fx_mapC_returned hs g g' h
  | parked K f E Ec hh args =>
    simp only [statusV] at h
    split at h <;> cases h

end Silmaril.Proofs.Wasm.Component.FXRefV
