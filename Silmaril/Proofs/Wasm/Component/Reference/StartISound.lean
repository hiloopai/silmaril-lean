module

public import Silmaril.Proofs.Wasm.Component.Reference.StartIIR
public import Silmaril.Proofs.Wasm.Component.Reference.StartIPhase

/-!
# Soundness with imports and a start function, assembled

`simpleI_sound_seq_startS`: for a component with canon-lowered imports answered by a stateful
host `g`, whose module may have a start function that makes no import call
(`ImpModule.StartNoCall`), every behaviour of instantiating `c.toRef` (running the start
function) and calling its exports one after another (`seqBehavioursI`) is matched by the IR
denotation over `impSemS P`. The instantiation phase is `instBehaviours_startI` (with a start
function) or `instPhaseIS` (without); the calls are those of `StartISeq` from the configuration
after instantiation (`afterStartCfgI`, functions `fsS`, or `afterInstH`, functions `afterFuncs`),
at the component without its start function; the IR side is `seqI_denS` from the store the start
phase returns at, and `trap_denIS` when the start function traps.

`simpleI_sound_startS`: the case of a single export call.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy Payload sigN)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)}
  {prof : ProfileKind}
  {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## Export maps and function lists -/

/-- The export map with a start function finds export `j` at function `n + 1 + j`. -/
theorem exportMapIS_lookup (hc : c.Good) (j : Nat) (hj : j < c.exports.length) :
    (exportMapIS c).lookup c.exports[j].name = some ⟨c.imports.length + 1 + j⟩ :=
  lookup_mapIdx_val (·.name) (fun i => (⟨i⟩ : FuncId)) (c.imports.length + 1) c.exports j hj
    hc.names

theorem mapM_lookupIS (hc : c.Good) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)),
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).mapM
          (fun q => (exportMapIS c).lookup q.1) =
        some (calls.map fun q => (⟨c.imports.length + 1 + q.1⟩ : FuncId))
  | [] => rfl
  | q :: calls => by
    have hq : (exportMapIS c).lookup c.exports[q.1].name = some ⟨c.imports.length + 1 + q.1⟩ :=
      exportMapIS_lookup hc q.1 q.1.isLt
    simp only [List.map_cons, List.mapM_cons, hq, mapM_lookupIS hc calls]
    rfl

theorem zip_callArgsIO (o : Nat)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    (calls.map fun q => (⟨o + q.1⟩ : FuncId)).zip
        ((calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd) =
      callArgsIO c o calls := by
  induction calls with
  | nil => rfl
  | cons q calls ih =>
    simp only [List.map_cons, List.zip_cons_cons, ih]
    rfl

theorem hostPre_append (rest : List (CFuncInst (core3P P))) :
    HostPre c (hostList 0 c.imports ++ rest) := by
  intro k hk
  rw [List.getElem?_append_left (by rw [hostList_length]; exact hk), hostList,
    List.getElem?_mapIdx, List.getElem?_eq_getElem hk, Nat.zero_add]
  rfl

theorem fsS_hostPre (addr : Nat → Nat) (a : Nat) : HostPre c (fsS P addr c a) := by
  unfold fsS
  rw [List.append_assoc]
  exact hostPre_append _

theorem fsS_liftsAt (a : Nat) :
    LiftsAt c I (fsS P (fun k => I.addrs.getD k 0) c a) (c.imports.length + 1) := by
  intro j
  have hl : (hostList (Pf := P) 0 c.imports ++ [startFn a]).length = c.imports.length + 1 := by
    rw [List.length_append, hostList_length]
    rfl
  rw [fsS, List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
  show (c.exports.map fun x => _)[(j : Nat)]? = _
  rw [List.getElem?_map, List.getElem?_eq_getElem j.isLt]
  rfl

theorem afterFuncs_liftsAt :
    LiftsAt c I (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) c.imports.length :=
  fun j => afterFuncs_lifted _ j.isLt

theorem afterFuncs_hostPre : HostPre c (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) :=
  fun _ hk => afterFuncs_host _ hk

/-- The configuration after the start function is between calls, with nothing left over but the
start function's leftovers. -/
theorem ready_afterStartI {cs : (core3P P).Store (CanonHost (core3P P))} (a : Nat)
    (hw : I.WellFormed (Store.mapH trampIdx cs)) (htr : c.TrampOk cs) :
    ReadyAtI c.noStart I cs instAfterStart (startGarbA P g a) 0 where
  wf := hw
  tramp := htr
  threads := threadsOk_after _ _
  leave := rfl
  fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) }

/-- Core runs keep the trampolines. -/
theorem trampOk_coreSteps {x y : CoreSt (E3 P)} (h : Relation.ReflTransGen (CoreStep (E3 P)) x y)
    (ht : c.TrampOk x.1) : c.TrampOk y.1 := by
  intro a fi hh hfi hcode
  have hf : (x.1 : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))).funcs[a]? = some fi := by
    rw [← coreSteps_funcs h]
    exact hfi
  exact ht a fi hh hf hcode

theorem seqMovesI_nil (c : SimpleI) :
    ∀ calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val),
      seqMovesI c calls [] [] = []
  | [] => rfl
  | _ :: _ => rfl

/-! ## The calls after instantiation -/

theorem seqRoundsI_noStart (c : SimpleI) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (dss : List (List (Round (sigN c.imports.length))))
      (wss : List (List Silmaril.Wasm.Component.Val)),
      seqRoundsI c.noStart calls dss wss = seqRoundsI c calls dss wss
  | [], _, _ => rfl
  | (_, _) :: _, [], _ => rfl
  | (_, _) :: _, _ :: _, [] => rfl
  | (j, vs) :: cs, ds :: dss, ws :: wss => by
    show _ :: seqRoundsI c.noStart cs dss wss = _ :: seqRoundsI c cs dss wss
    rw [seqRoundsI_noStart c cs dss wss]
    rfl

/-- **The calls after instantiation**, from a configuration between calls whose store renames to
a store the start phase returns at: the resolved calls and the last outcome as the IR over
`impSemS P` prescribes. -/
theorem seq_tailIS (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hg : c.HostOkS g)
    {st : Option Nat} (hIS : c.mod.IsInstS I st) {cs : (core3P P).Store (CanonHost (core3P P))}
    (h₀ : Silmaril.Wasm.Game.StartsTo P Silmaril.Wasm.SingleThreaded.Det.noHost I.store st
      (Store.mapH trampIdx cs))
    {fs : List (CFuncInst (core3P P))} {o : Nat} (hfh : HostPre c fs) (hfo : LiftsAt c I fs o)
    {ι : InstState} {G : Garb P σ} {ST : List Subtask} {s₀ : σ}
    (R : ReadyAtI c.noStart I cs ι G 0)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {rss : List (List Silmaril.Wasm.Component.Reference.Val)} {b : Silmaril.Wasm.Component.Reference.Outcome}
    {mₙ : Machine.Config (E3 P) σ}
    (hS : SeqCalls prof (answerHostS P g) (readyCfgI cs ι fs G ST s₀) 0 (callArgsIO c o calls)
      rss mₙ)
    (hb : b ∈ callBehaviours prof (answerHostS P g) mₙ ⟨calls.length⟩ ⟨o + j⟩
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))) (s₁ : σ),
      rss = wss.map (·.map toRefVal) ∧ calls.length = dss.length ∧ calls.length = wss.length ∧
      HostRun g s₀ dss.flatten s₁ ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSemS P) ∧
      SeqIRObsIS c (c.toComp.den (impSemS P)) calls dss wss j vs g s₁ b := by
  have hc₀ : c.noStart.Good := noStart_good hc
  obtain ⟨lr, dss, wss, cs', ι', G', ST', s₁, hact, hrel, hds, hrss, hl₁, hl₂, hmₙ, R'⟩ :=
    seqI_invP (c := c.noStart) (prof := prof) hc₀ hff har hIS.noStart hg hfh hfo calls cs ι G ST
      s₀ 0 _ _ R ht hS
  have hb' : b ∈ callBehaviours prof (answerHostS P g) (readyCfgI cs' ι' fs G' ST' s₁)
      ⟨0 + calls.length⟩ ⟨o + j⟩ (vs.map toRefVal) := by
    rw [← hmₙ, Nat.zero_add]
    exact hb
  have hrel' : List.Forall₂ (fun r u => ∃ j vs, IRRoundI c I j vs r u) lr
      (seqRoundsI c calls dss wss) := by
    have h : List.Forall₂ (fun r u => ∃ j vs, IRRoundI c.noStart I j vs r u) lr
        (seqRoundsI c calls dss wss) := seqRoundsI_noStart c calls dss wss ▸ hrel
    exact h
  have hpre : seqMovesI c calls dss wss ∈ c.toComp.den (impSemS P) := by
    rw [seqMovesI_eq c calls dss wss]
    exact seqI_denS hc hIS h₀ hrel' (cplay_mem_strategy hact)
  refine ⟨wss, dss, s₁, hrss, hl₁, hl₂, hds, hpre, ?_⟩
  rcases last_callIP (c := c.noStart) hc₀ hff har hIS.noStart hg hfh hfo R' j hvs hb' with
    hd | ⟨r, u, q, s', hu, hdu, hpath, hobs⟩
  · rw [hd]
    trivial
  · show SeqIRObsIS c (c.toComp.den (impSemS P)) calls dss wss j vs g s₁ b
    have hall : I.Path P (.idle (Store.mapH trampIdx cs)) (cplay (lr ++ [r])) q := by
      rw [cplay_append]
      exact path_append hact hpath
    let u' : CRound (sigN c.imports.length) (sigN c.toComp.exports.length) := u
    have hu' : IRRoundI c I j vs r u' := hu
    have hdu' : HostRun g s₁ u'.cs s' := hdu
    have hobs' : ObsAns b u'.a := hobs
    have hden : cplay (seqRoundsI c calls dss wss ++ [u']) ∈ c.toComp.den (impSemS P) :=
      seqI_denS hc hIS h₀ (forall₂_append hrel' (.cons ⟨j, vs, hu'⟩ .nil))
        (cplay_mem_strategy hall)
    exact seqIRObsIS_of (c := c) hl₁ hl₂ hu' hdu' b hobs' hden

/-! ## Assembly -/

/-- What the IR exhibits for a behaviour `p` of a sequence of calls with imports and a start
function: IR results `wss` (none when no call resolved), component import calls `dss` answered by
`g` from `s₀` to `s₁`, the play of the resolved calls and the last outcome. -/
abbrev SeqStartConcl (P : Profile) (c : SimpleI) {σ : Type}
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (s₀ : σ)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome) : Prop :=
  ∃ (wss : List (List Silmaril.Wasm.Component.Val))
    (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))) (s₁ : σ),
    p.1 = wss.map (·.map toRefVal) ∧ (p.1 = [] → dss = []) ∧ HostRun g s₀ dss.flatten s₁ ∧
    seqMovesI c calls dss wss ∈ c.toComp.den (impSemS P) ∧
    SeqIRObsIS c (c.toComp.den (impSemS P)) calls dss wss j vs g s₁ p.2

theorem dss_nil_of {c : SimpleI} {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {rss : List (List Silmaril.Wasm.Component.Reference.Val)} {wss : List (List Silmaril.Wasm.Component.Val)}
    {dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))}
    (h₀ : rss = wss.map (·.map toRefVal)) (h₁ : calls.length = dss.length)
    (h₂ : calls.length = wss.length) (h₄ : rss = []) : dss = [] := by
  have hw : wss = [] := List.map_eq_nil_iff.mp (h₄ ▸ h₀).symm
  have h₃ : calls.length = 0 := by rw [h₂, hw, List.length_nil]
  exact List.length_eq_zero_iff.mp (h₁ ▸ h₃)

/-- **Soundness of the component IR for sequences of calls with imports and a start function**
(every profile and component choice profile), with no import-call lists when no call resolved. -/
theorem simpleI_sound_seq_startS' (P : Profile) (prof : ProfileKind) (c : SimpleI)
    (hc : c.Good) (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree)
    (har : c.Arity) {σ : Type} (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (hg : c.HostOkS g) (s₀ : σ)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    SeqStartConcl P c g s₀ calls j vs p := by
  obtain ⟨I, st, cs, ci, hF⟩ := coreFactsIS (Pf := P) hc hi
  cases st with
  | none =>
    show SeqStartConcl P c g s₀ calls j vs p
    have hi' : c.Inst := hi.inst_none hF.isInst
    obtain ⟨I', cs', hI', hcs', htr', hinst⟩ := instPhaseIS P prof c hc hi' har
    have hIS : c.mod.IsInstS I' none :=
      ⟨hI'.1.elim fun mt h => ⟨mt, Silmaril.Wasm.Game.isInstanceStart_none_iff.2 h⟩, hI'.2⟩
    rcases hp with ⟨m₀, inst, es, fs, mₙ, f, hr, hfs, hS, hl, hb⟩ | ⟨hpe, hr⟩ | ⟨hpe, hr⟩
    · show SeqStartConcl P c g s₀ calls j vs p
      have he : m₀ = afterInstH P cs' (fsI P c I') s₀ ∧ inst = ⟨0⟩ ∧ es = exportMapI c := by
        simpa only [InstResult.instance.injEq] using hinst σ _ s₀ _ hr
      have hfs' : fs = calls.map fun q => (⟨c.imports.length + q.1⟩ : FuncId) :=
        Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookupI hc calls))
      have hf' : f = ⟨c.imports.length + j⟩ :=
        Option.some.inj (hl.symm.trans (he.2.2 ▸ exportMapI_lookup hc j j.isLt))
      have hS₁ : SeqCalls prof (answerHostS P g) (readyCfgI cs' {} (fsI P c I')
          (⟨[], [], [], [], [], [], []⟩ : Garb P σ) [] s₀) 0
          (callArgsIO c c.imports.length calls) p.1 mₙ := by
        have hS₀ : SeqCalls prof (answerHostS P g) (afterInstH P cs' (fsI P c I') s₀) 0
            (fs.zip ((calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd))
            p.1 mₙ := he.1 ▸ hS
        rw [← zip_callArgsIO, ← hfs']
        exact hS₀
      have hb' : p.2 ∈ callBehaviours prof (answerHostS P g) mₙ ⟨calls.length⟩
          ⟨c.imports.length + j⟩ (vs.map toRefVal) := by
        rw [← hf', ← List.length_map (f := fun q => (c.exports[q.1].name, q.2.map toRefVal))]
        exact hb
      have R : ReadyAtI c.noStart I' cs' {} (⟨[], [], [], [], [], [], []⟩ : Garb P σ) 0 :=
        have R₀ := ready_afterInstI (P := P) (σ := σ) (c := c) hI' hcs' htr'
        ⟨R₀.wf, R₀.tramp, R₀.threads, R₀.leave, R₀.fresh⟩
      obtain ⟨wss, dss, s₁, h₁, h₂, h₂', h₃, h₄, h₅⟩ := seq_tailIS hc hff har hg hIS
        (hcs'.symm ▸ Silmaril.Wasm.Game.startsTo_none.2 rfl) afterFuncs_hostPre afterFuncs_liftsAt
        R calls j vs ht hvs hS₁ hb'
      exact ⟨wss, dss, s₁, h₁, dss_nil_of h₁ h₂ h₂', h₃, h₄, h₅⟩
    · exact absurd (hinst σ _ s₀ _ hr) (by simp)
    · exact absurd (hinst σ _ s₀ _ hr) (by simp)
  | some a =>
    show SeqStartConcl P c g s₀ calls j vs p
    rcases hp with ⟨m₀, inst, es, fs, mₙ, f, hr, hfs, hS, hl, hb⟩ | ⟨hpe, hr⟩ | ⟨hpe, hr⟩
    · show SeqStartConcl P c g s₀ calls j vs p
      rcases instBehaviours_startI (g := g) hc hi har hn hF prof s₀ _ hr with
        ⟨y, hy, ⟨ys, hst⟩, he⟩ | ⟨-, -, -, he⟩ | he
      · show SeqStartConcl P c g s₀ calls j vs p
        obtain ⟨rfl, -, rfl⟩ : m₀ = afterStartCfgI P g y.1 a (fun k => I.addrs.getD k 0) c s₀ ∧
            inst = ⟨0⟩ ∧ es = exportMapIS c := by
          simpa only [InstResult.instance.injEq] using he
        obtain ⟨hstart, hw⟩ := start_returnsI hF hy hst
        have hfs' : fs = calls.map fun q => (⟨c.imports.length + 1 + q.1⟩ : FuncId) :=
          Option.some.inj (hfs.symm.trans (mapM_lookupIS hc calls))
        have hf' : f = ⟨c.imports.length + 1 + j⟩ :=
          Option.some.inj (hl.symm.trans (exportMapIS_lookup hc j j.isLt))
        have hS₁ : SeqCalls prof (answerHostS P g) (readyCfgI y.1 instAfterStart
            (fsS P (fun k => I.addrs.getD k 0) c a) (startGarbA P g a) [] s₀) 0
            (callArgsIO c (c.imports.length + 1) calls) p.1 mₙ := by
          rw [← zip_callArgsIO, ← hfs']
          exact hS
        have hb' : p.2 ∈ callBehaviours prof (answerHostS P g) mₙ ⟨calls.length⟩
            ⟨c.imports.length + 1 + j⟩ (vs.map toRefVal) := by
          rw [← hf', ← List.length_map (f := fun q => (c.exports[q.1].name, q.2.map toRefVal))]
          exact hb
        obtain ⟨wss, dss, s₁, h₁, h₂, h₂', h₃, h₄, h₅⟩ := seq_tailIS hc hff har hg hF.isInst hstart
          (fsS_hostPre _ a) (fsS_liftsAt a)
          (ready_afterStartI a hw (trampOk_coreSteps hy hF.tramp)) calls j vs ht hvs hS₁ hb'
        exact ⟨wss, dss, s₁, h₁, dss_nil_of h₁ h₂ h₂', h₃, h₄, h₅⟩
      · cases he
      · cases he
    · show SeqStartConcl P c g s₀ calls j vs p
      rcases instBehaviours_startI (g := g) hc hi har hn hF prof s₀ _ hr with
        ⟨_, _, _, he⟩ | ⟨y, hy, hst, -⟩ | he
      · cases he
      · show SeqStartConcl P c g s₀ calls j vs p
        have hfail : c.mod.StartFails P := start_failsI hF hy hst
        rw [hpe]
        refine ⟨[], [], s₀, rfl, fun _ => rfl, .nil _, ?_, ⟨[], s₀, .nil _, ?_⟩⟩
        · rw [seqMovesI_nil]
          exact (c.toComp.den (impSemS P)).nil_mem
        · rw [seqMovesI_nil]
          exact trap_denIS hc hfail j vs
      · cases he
    · rw [hpe]
      refine ⟨[], [], s₀, rfl, fun _ => rfl, .nil _, ?_, trivial⟩
      rw [seqMovesI_nil]
      exact (c.toComp.den (impSemS P)).nil_mem

/-- **Soundness of the component IR for sequences of calls with imports and a start function**
(every profile and component choice profile): for a component whose module may have a start
function that makes no import call, every behaviour of instantiating `c.toRef` from host state
`s₀` (running the start function), calling its exports `calls` in order (each resolving), then
export `j`, over `core3P P` with `answerHostS P g`, records reference images of IR results `wss`;
the IR denotation over `impSemS P` plays the resolved calls with these results, their component
import calls `dss` answered by `g` with the host state threaded from `s₀` to `s₁`, and the last
outcome as `SeqIRObsIS` prescribes from `s₁`. -/
theorem simpleI_sound_seq_startS (P : Profile) (prof : ProfileKind) (c : SimpleI)
    (hc : c.Good) (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree)
    (har : c.Arity) {σ : Type} (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (hg : c.HostOkS g) (s₀ : σ)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))) (s₁ : σ),
      p.1 = wss.map (·.map toRefVal) ∧ HostRun g s₀ dss.flatten s₁ ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSemS P) ∧
      SeqIRObsIS c (c.toComp.den (impSemS P)) calls dss wss j vs g s₁ p.2 := by
  obtain ⟨wss, dss, s₁, h₁, -, h₃, h₄, h₅⟩ :=
    simpleI_sound_seq_startS' P prof c hc hi hn hff har g hg s₀ calls j vs ht hvs p hp
  exact ⟨wss, dss, s₁, h₁, h₃, h₄, h₅⟩

/-- A behaviour of an export call is a behaviour of the sequence without earlier calls. -/
theorem seqBehavioursI_of_export {E : CoreEngine}
    [∀ a b, Decidable (E.ExternSub a b)] {h : Silmaril.Wasm.Component.Reference.Host E σ} {s₀ : σ}
    {d : CompAst E.Module} {ims : Silmaril.Wasm.Component.Iface} {name : String} {vals : List Silmaril.Wasm.Component.Reference.Val}
    {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ exportBehavioursI prof h s₀ d ims name vals) :
    (([] : List (List Silmaril.Wasm.Component.Reference.Val)), b) ∈ seqBehavioursI prof h s₀ d ims [] name vals := by
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩
  · exact .inl ⟨m₁, inst, es, [], m₁, f, hr, rfl, .nil _ _, hl, hb⟩
  · exact .inr (.inl ⟨rfl, hr⟩)
  · exact .inr (.inr ⟨rfl, hr⟩)

/-- The observation of a sequence without earlier calls is that of a single call. -/
theorem irObsIS_of_seq {σI : Strategy (sigN c.imports.length) (sigN c.toComp.exports.length)}
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} {s : σ} :
    ∀ b : Silmaril.Wasm.Component.Reference.Outcome, SeqIRObsIS c σI [] [] [] j vs g s b →
      IRObsIS σI ⟨j, by simp [SimpleI.toComp]⟩ vs g s b
  | .returns (some _), h => h
  | .returns none, _ => trivial
  | .traps, h => h
  | .deadlocks, _ => trivial
  | .diverges, _ => trivial

/-- **Soundness of the component IR with imports and a start function**, for one export call
(every profile and component choice profile): every behaviour of instantiating `c.toRef` from
host state `s₀` (running the start function, which makes no import call) and calling export `j`
on the reference images of well-typed IR values, over `core3P P` with `answerHostS P g`, is
matched by the IR denotation over `impSemS P` (`IRObsIS`). -/
theorem simpleI_sound_startS (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree) (har : c.Arity) {σ : Type}
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (hg : c.HostOkS g) (s₀ : σ)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports c.exports[j].name
        (vs.map toRefVal),
      IRObsIS (c.toComp.den (impSemS P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g s₀ b := by
  intro b hb
  obtain ⟨wss, dss, s₁, h₁, h₂, h₃, -, h₅⟩ := simpleI_sound_seq_startS' P prof c hc hi hn hff har
    g hg s₀ [] j vs (fun _ h => nomatch h) hvs _ (seqBehavioursI_of_export hb)
  have hw : wss = [] := List.map_eq_nil_iff.1 h₁.symm
  have hd : dss = [] := h₂ rfl
  subst hw hd
  cases h₃
  exact irObsIS_of_seq b h₅

/-- **`impSemS` extends `impSem`** on modules with an instance (no start function). -/
theorem impSem_le_impSemS {m : ImpModule} (hI : m.IsInst I) :
    (impSem P).sem m ≤ (impSemS P).sem m := by
  rw [impSem_sem hI]
  exact le_sSup (.inl ⟨I, none, I.store, ⟨hI.1.elim fun mt h => ⟨mt,
    Silmaril.Wasm.Game.isInstanceStart_none_iff.2 h⟩, hI.2⟩,
    Silmaril.Wasm.Game.startsTo_none.2 rfl, rfl⟩)

/-! ## Stateless hosts -/

/-- **Soundness with imports and a start function, stateless host** (every profile and
component choice profile). -/
theorem simpleI_sound_start (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree) (har : c.Arity)
    (g : HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val)) (hg : c.HostOk g)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehavioursI prof (answerHost P g) () c.toRef c.imports c.exports[j].name
        (vs.map toRefVal),
      IRObsI (c.toComp.den (impSemS P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g b :=
  fun b hb => irObsI_of_S (simpleI_sound_startS P prof c hc hi hn hff har (statelessG g)
    (hostOkS_stateless hg) () j vs hvs b hb)

/-- **Soundness for sequences of calls with imports and a start function, stateless host**
(every profile and component choice profile). -/
theorem simpleI_sound_seq_start (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree) (har : c.Arity)
    (g : HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val)) (hg : c.HostOk g)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHost P g) () c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))),
      p.1 = wss.map (·.map toRefVal) ∧ (∀ ds ∈ dss, ∀ d ∈ ds, HostAnswers g d) ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSemS P) ∧
      SeqIRObsI c (c.toComp.den (impSemS P)) calls dss wss j vs g p.2 := by
  obtain ⟨wss, dss, _, hrss, hrun, hpre, hobs⟩ := simpleI_sound_seq_startS P prof c hc hi hn hff
    har (statelessG g) (hostOkS_stateless hg) () calls j vs ht hvs p hp
  exact ⟨wss, dss, hrss, fun ds hds d hd =>
    hostAnswers_of_run hrun d (List.mem_flatten.mpr ⟨ds, hds, hd⟩), hpre, seqIRObsI_of_S hobs⟩

end Silmaril.Proofs.Wasm.Component.Reference
