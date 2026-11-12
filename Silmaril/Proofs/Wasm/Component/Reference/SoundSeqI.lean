module

public import Silmaril.Proofs.Wasm.Component.Reference.CallPhaseKI
public import Silmaril.Proofs.Wasm.Component.Reference.SoundI

/-!
# Sequences of calls with imports, assembled

`simpleI_sound_seq`: for a component with canon-lowered imports answered by a host `g`, every
behaviour of instantiating `c.toRef` and calling its exports one after another on one instance
(`seqBehavioursI`) is matched by the IR denotation over `impSem P`: the resolved calls are the
multi-question play `seqMovesI` (each call with its import calls answered by `g`), and the last
outcome is as `SeqIRObsI` prescribes.

The proof: the instantiation phase (`instPhaseI`) reaches the first configuration between calls;
each resolved call is a complete activation of the core instance from store to store
(`calls_factsKI`), the configuration between calls persisting (`seqI_inv`); the last call is a
play from the store reached (`last_callI`); the activations and the last play are one play of
the instance's strategy, which is a play of the IR (`seqI_den`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy Payload sigN)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Val → Option (List Val × σ)}
  {prof : ProfileKind}
  {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

export Silmaril.Wasm.Component.Reference (seqMovesI SeqIRObsI SeqIRObsIS seqBehavioursI
  SimpleI.TypedCalls)

/-! ## IR rounds of sequences -/

/-- The IR rounds of resolved calls with their component import calls and IR results. -/
def seqRoundsI (c : SimpleI) :
    List (Fin c.exports.length × List Silmaril.Wasm.Component.Val) →
    List (List (Round (sigN c.imports.length))) → List (List Silmaril.Wasm.Component.Val) →
    List (CRound (sigN c.imports.length) (sigN c.toComp.exports.length))
  | (j, vs) :: cs, ds :: dss, ws :: wss =>
    ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), ds, some (.vals ws)⟩ :: seqRoundsI c cs dss wss
  | _, _, _ => []

theorem seqMovesI_eq (c : SimpleI) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (dss : List (List (Round (sigN c.imports.length))))
      (wss : List (List Silmaril.Wasm.Component.Val)),
      seqMovesI c calls dss wss = cplay (seqRoundsI c calls dss wss)
  | [], _, _ => rfl
  | (_, _) :: _, [], _ => rfl
  | (_, _) :: _, _ :: _, [] => rfl
  | (j, vs) :: cs, ds :: dss, ws :: wss => by
    show _ :: (callMoves ds ++ (_ :: seqMovesI c cs dss wss)) =
      _ :: (callMoves ds ++ (_ :: cplay (seqRoundsI c cs dss wss)))
    rw [seqMovesI_eq c cs dss wss]

theorem seqRoundsI_append (c : SimpleI) (j : Fin c.exports.length)
    (vs ws : List Silmaril.Wasm.Component.Val) (ds : List (Round (sigN c.imports.length))) :
    ∀ (cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (dss : List (List (Round (sigN c.imports.length))))
      (wss : List (List Silmaril.Wasm.Component.Val)), cs.length = dss.length →
      cs.length = wss.length →
      seqRoundsI c (cs ++ [(j, vs)]) (dss ++ [ds]) (wss ++ [ws]) =
        seqRoundsI c cs dss wss ++ [⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), ds, some (.vals ws)⟩]
  | [], [], [], _, _ => rfl
  | [], _ :: _, _, h, _ => absurd h (by simp)
  | [], [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h, _ => absurd h (by simp)
  | _ :: _, _ :: _, [], _, h => absurd h (by simp)
  | (j', vs') :: cs, ds' :: dss, ws' :: wss, h₁, h₂ => by
    have h₁' : cs.length = dss.length := by
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using h₁
    have h₂' : cs.length = wss.length := by
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using h₂
    show _ :: seqRoundsI c (cs ++ [(j, vs)]) (dss ++ [ds]) (wss ++ [ws]) =
      _ :: (seqRoundsI c cs dss wss ++ _)
    rw [seqRoundsI_append c j vs ws ds cs dss wss h₁' h₂']

/-- The IR round of export `j` on `vs` with the IR answer `A`. -/
theorem IRRoundI.eq {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val}
    {r : CRound I.E I.F} {u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length)}
    (h : IRRoundI c I j vs r u) {A : Option Payload} (ha : u.a = A) :
    u = ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), u.cs, A⟩ := by
  obtain ⟨xs, dss, -, -, -, -, rfl⟩ := h
  subst ha
  rfl

/-! ## The reference side -/

/-- Calls of exports (by index) on IR values, as reference function values (import `k` is
function `k`, export `j` function `n + j`) and arguments. -/
def callArgsI (c : SimpleI)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (FuncId × List Val) :=
  calls.map fun q => (⟨c.imports.length + q.1⟩, q.2.map toRefVal)

/-- The component functions after instantiation, at the instance's addresses. -/
abbrev fsI (P : Profile) (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance) :
    List (CFuncInst (core3P P)) :=
  SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c

/-- One resolved call between calls, from host state `s`. -/
theorem seqI_step (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hI : c.mod.IsInst I)
    (hg : c.HostOkS g) {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
    {G : Garb P σ} {ST : List Subtask} {k : Nat} {s : σ} (R : ReadyAtI c I cs ι G k)
    (j : Fin c.exports.length)
    {vs : List Silmaril.Wasm.Component.Val} (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {m₁ : Machine.Config (E3 P) σ} {rs : List Val}
    (hcall : Calls prof (answerHostS P g).hr (DA P g) (readyCfgI cs ι (fsI P c I) G ST s) ⟨k⟩
      ⟨c.imports.length + j⟩ (vs.map toRefVal) m₁ (.resolved (some rs))) :
    ∃ (r : CRound I.E I.F) (ds : List (Round (sigN c.imports.length)))
      (ws : List Silmaril.Wasm.Component.Val) (cs' : (core3P P).Store (CanonHost (core3P P)))
      (ι' : InstState) (G' : Garb P σ) (ST' : List Subtask) (s' : σ),
      IRRoundI c I j vs r ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), ds, some (.vals ws)⟩ ∧
      HostRun g s ds s' ∧ rs = ws.map toRefVal ∧
      I.Activation P (Store.mapH trampIdx cs) (cplay [r]) (Store.mapH trampIdx cs') ∧
      m₁ = readyCfgI cs' ι' (fsI P c I) G' ST' s' ∧ ReadyAtI c I cs' ι' G' (k + 1) := by
  obtain ⟨r, u, q, s', hu, hds, hpath, hobs, hnext⟩ := calls_factsKI hc hff har hI hg R j hvs hcall
  obtain ⟨ws, hrs, hua⟩ : ∃ ws : List Silmaril.Wasm.Component.Val, rs = ws.map toRefVal ∧
      u.a = some (.vals ws) := hobs
  obtain ⟨cs', ι', G', ST', rfl, hm, R'⟩ := hnext rs rfl
  have hu' : u = ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), u.cs, some (.vals ws)⟩ := hu.eq hua
  exact ⟨r, u.cs, ws, cs', ι', G', ST', s', hu' ▸ hu, hds, hrs, hpath, hm, R'⟩

/-- What a sequence of resolved calls with imports between calls shows, from host state `s`. -/
def SeqFactsI (P : Profile) (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (g : σ → HostFuncId → List Val → Option (List Val × σ))
    (cs : (core3P P).Store (CanonHost (core3P P))) (k : Nat) (s : σ)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (rss : List (List Val)) (mₙ : Machine.Config (E3 P) σ) : Prop :=
  ∃ (lr : List (CRound I.E I.F)) (dss : List (List (Round (sigN c.imports.length))))
    (wss : List (List Silmaril.Wasm.Component.Val)) (cs' : (core3P P).Store (CanonHost (core3P P)))
    (ι' : InstState) (G' : Garb P σ) (ST' : List Subtask) (s' : σ),
    I.Activation P (Store.mapH trampIdx cs) (cplay lr) (Store.mapH trampIdx cs') ∧
    List.Forall₂ (fun r u => ∃ j vs, IRRoundI c I j vs r u) lr (seqRoundsI c calls dss wss) ∧
    HostRun g s dss.flatten s' ∧ rss = wss.map (·.map toRefVal) ∧
    calls.length = dss.length ∧ calls.length = wss.length ∧
    mₙ = readyCfgI cs' ι' (fsI P c I) G' ST' s' ∧ ReadyAtI c I cs' ι' G' (k + calls.length)

/-- Sequences of resolved calls from one configuration between calls. -/
theorem seqFactsI_cons {cs cs₁ : (core3P P).Store (CanonHost (core3P P))} {k : Nat} {s s₁ : σ}
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val}
    {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)} {r : CRound I.E I.F}
    {ds : List (Round (sigN c.imports.length))} {ws : List Silmaril.Wasm.Component.Val}
    {rss : List (List Val)} {mₙ : Machine.Config (E3 P) σ}
    (hu : IRRoundI c I j vs r ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), ds, some (.vals ws)⟩)
    (hds : HostRun g s ds s₁)
    (hact : I.Activation P (Store.mapH trampIdx cs) (cplay [r]) (Store.mapH trampIdx cs₁))
    (h : SeqFactsI P c I g cs₁ (k + 1) s₁ calls rss mₙ) :
    SeqFactsI P c I g cs k s ((j, vs) :: calls) ((ws.map toRefVal) :: rss) mₙ := by
  obtain ⟨lr, dss, wss, cs', ι', G', ST', s', hact', hrel, hdss, rfl, hl₁, hl₂, hm, R'⟩ := h
  have hk : k + 1 + calls.length = k + ((j, vs) :: calls).length := by
    simp only [List.length_cons]
    omega
  refine ⟨r :: lr, ds :: dss, ws :: wss, cs', ι', G', ST', s', ?_, .cons ⟨j, vs, hu⟩ hrel, ?_,
    rfl, by rw [List.length_cons, hl₁, List.length_cons],
    by rw [List.length_cons, hl₂, List.length_cons], hm, hk ▸ R'⟩
  · show I.Activation P _ (cplay ([r] ++ lr)) _
    rw [cplay_append]
    exact path_append hact hact'
  · rw [List.flatten_cons]
    exact hds.append hdss

/-- **Sequences of resolved calls with imports** are activations of the instance from store to
store, with IR rounds, the host state threaded through their import calls. -/
theorem seqI_inv (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hI : c.mod.IsInst I)
    (hg : c.HostOkS g) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P σ)
      (ST : List Subtask) (s : σ) (k : Nat) (rss : List (List Val))
      (mₙ : Machine.Config (E3 P) σ),
      ReadyAtI c I cs ι G k → c.TypedCalls calls →
      SeqCalls prof (answerHostS P g) (readyCfgI cs ι (fsI P c I) G ST s) k (callArgsI c calls)
        rss mₙ →
      SeqFactsI P c I g cs k s calls rss mₙ
  | [], cs, ι, G, ST, s, k, rss, mₙ, R, _, hS => by
    cases hS
    exact ⟨[], [], [], cs, ι, G, ST, s, .nil _, .nil, .nil _, rfl, rfl, rfl, rfl, R⟩
  | (j, vs) :: calls, cs, ι, G, ST, s, k, rss, mₙ, R, ht, hS => by
    cases hS with
    | cons hcall hS' =>
      have hvs : ValTy.checkList c.exports[j].ty.params vs = true := ht _ List.mem_cons_self
      obtain ⟨r, ds, ws, cs₁, ι₁, G₁, ST₁, s₁, hu, hds, rfl, hact, rfl, R₁⟩ :=
        seqI_step hc hff har hI hg R j hvs hcall
      exact seqFactsI_cons hu hds hact (seqI_inv hc hff har hI hg calls cs₁ ι₁ G₁ ST₁ s₁ (k + 1)
        _ _ R₁ (fun q hq => ht q (List.mem_cons_of_mem _ hq)) hS')

/-- The last call of a sequence with imports, from host state `s`. -/
theorem last_callI (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hI : c.mod.IsInst I)
    (hg : c.HostOkS g) {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
    {G : Garb P σ} {ST : List Subtask} {n : Nat} {s : σ} (R : ReadyAtI c I cs ι G n)
    (j : Fin c.exports.length)
    {vs : List Silmaril.Wasm.Component.Val} (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ callBehaviours prof (answerHostS P g) (readyCfgI cs ι (fsI P c I) G ST s) ⟨n⟩
      ⟨c.imports.length + j⟩ (vs.map toRefVal)) :
    b = .diverges ∨ ∃ (r : CRound I.E I.F)
      (u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length)) (q : I.HState)
      (s' : σ), IRRoundI c I j vs r u ∧ HostRun g s u.cs s' ∧
      I.Path P (.idle (Store.mapH trampIdx cs)) (cplay [r]) q ∧ ObsAns b u.a := by
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, -⟩
  · obtain ⟨r, u, q, s', hu, hds, hpath, hobs, -⟩ := calls_factsKI hc hff har hI hg R j hvs hcalls
    exact .inr ⟨r, u, q, s', hu, hds, hpath, hobs⟩
  · exact .inl rfl

/-! ## The IR observation of the last call -/

theorem seqIRObsIS_of {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {dss : List (List (Round (sigN c.imports.length)))}
    {wss : List (List Silmaril.Wasm.Component.Val)} (hl₁ : calls.length = dss.length)
    (hl₂ : calls.length = wss.length) {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {r : CRound I.E I.F}
    {u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length)} {s s' : σ}
    (hu : IRRoundI c I j vs r u) (hds : HostRun g s u.cs s')
    {σI : Strategy (sigN c.imports.length) (sigN c.toComp.exports.length)} :
    ∀ b : Silmaril.Wasm.Component.Reference.Outcome, ObsAns b u.a →
      cplay (seqRoundsI c calls dss wss ++ [u]) ∈ σI →
      SeqIRObsIS c σI calls dss wss j vs g s b
  | .returns (some rs), ⟨ws, hrs, hA⟩, h => by
    refine ⟨ws, u.cs, s', hrs, hds, ?_⟩
    rw [seqMovesI_eq, seqRoundsI_append c j vs ws u.cs calls dss wss hl₁ hl₂]
    rw [hu.eq hA] at h
    exact h
  | .traps, hA, h => by
    refine ⟨u.cs, s', hds, ?_⟩
    rw [hu.eq hA, cplay_append] at h
    rw [seqMovesI_eq]
    exact h
  | .returns none, _, _ => trivial
  | .deadlocks, _, _ => trivial
  | .diverges, _, _ => trivial

/-! ## Assembly -/

theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {m₁ m₂ : List β}
    (h₁ : List.Forall₂ R l₁ m₁) (h₂ : List.Forall₂ R l₂ m₂) :
    List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

/-- The export map finds the calls. -/
theorem mapM_lookupI (hc : c.Good) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)),
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).mapM
          (fun q => (exportMapI c).lookup q.1) =
        some (calls.map fun q => (⟨c.imports.length + q.1⟩ : FuncId))
  | [] => rfl
  | q :: calls => by
    have hq : (exportMapI c).lookup c.exports[q.1].name = some ⟨c.imports.length + q.1⟩ :=
      exportMapI_lookup hc q.1 q.1.isLt
    simp only [List.map_cons, List.mapM_cons, hq, mapM_lookupI hc calls]
    rfl

theorem zip_callArgsI (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    (calls.map fun q => (⟨c.imports.length + q.1⟩ : FuncId)).zip
        ((calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd) =
      callArgsI c calls := by
  induction calls with
  | nil => rfl
  | cons q calls ih =>
    simp only [List.map_cons, List.zip_cons_cons, ih]
    rfl

/-- The configuration after instantiation is between calls, with nothing left over. -/
theorem ready_afterInstI (hI : c.mod.IsInst I) {cs : (core3P P).Store (CanonHost (core3P P))}
    (hcs : Store.mapH trampIdx cs = I.store) (htr : c.TrampOk cs) :
    ReadyAtI c I cs {} (⟨[], [], [], [], [], [], []⟩ : Garb P σ) 0 where
  wf := hcs ▸ hI.1.choose_spec.ok
  tramp := htr
  threads := .inl rfl
  leave := rfl
  fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) }

/-- **Soundness of the component IR for sequences of calls with imports answered by a stateful
host** (every profile and component choice profile): every behaviour of instantiating `c.toRef`
from host state `s₀`, calling its exports `calls` in order (each resolving), then export `j`,
over `core3P P` with `answerHostS P g`, records reference images of IR results `wss`; the IR
denotation plays the resolved calls with these results, their component import calls `dss`
answered by `g` with the host state threaded from `s₀` to `s₁` (`HostRun`), and the last
outcome as `SeqIRObsIS` prescribes from `s₁`. -/
theorem simpleI_sound_seqS (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.Inst) (hff : c.FloatFree) (har : c.Arity) {σ : Type}
    (g : σ → HostFuncId → List Val → Option (List Val × σ)) (hg : c.HostOkS g) (s₀ : σ)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))) (s₁ : σ),
      p.1 = wss.map (·.map toRefVal) ∧ HostRun g s₀ dss.flatten s₁ ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSem P) ∧
      SeqIRObsIS c (c.toComp.den (impSem P)) calls dss wss j vs g s₁ p.2 := by
  obtain ⟨I, cs, hI, hcs, htr, hinst⟩ := instPhaseIS P prof c hc hi har
  rcases hp with ⟨m₀, inst, es, fs, mₙ, f, hr, hfs, hS, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · show ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))) (s₁ : σ),
      p.1 = wss.map (·.map toRefVal) ∧ HostRun g s₀ dss.flatten s₁ ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSem P) ∧
      SeqIRObsIS c (c.toComp.den (impSem P)) calls dss wss j vs g s₁ p.2
    have he : m₀ = afterInstH P cs (fsI P c I) s₀ ∧ inst = ⟨0⟩ ∧ es = exportMapI c := by
      simpa only [InstResult.instance.injEq] using hinst σ _ s₀ _ hr
    have hfs' : fs = calls.map fun q => (⟨c.imports.length + q.1⟩ : FuncId) :=
      Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookupI hc calls))
    have hf' : f = ⟨c.imports.length + j⟩ :=
      Option.some.inj (hl.symm.trans (he.2.2 ▸ exportMapI_lookup hc j j.isLt))
    have hS₁ : SeqCalls prof (answerHostS P g) (readyCfgI cs {} (fsI P c I)
        (⟨[], [], [], [], [], [], []⟩ : Garb P σ) [] s₀) 0 (callArgsI c calls) p.1 mₙ := by
      have hS₀ : SeqCalls prof (answerHostS P g) (afterInstH P cs (fsI P c I) s₀) 0
          (fs.zip ((calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd))
          p.1 mₙ := he.1 ▸ hS
      rw [← zip_callArgsI, ← hfs']
      exact hS₀
    obtain ⟨lr, dss, wss, cs', ι', G', ST', s₁, hact, hrel, hds, hrss, hl₁, hl₂, hmₙ, R'⟩ :=
      seqI_inv hc hff har hI hg calls cs {} _ [] s₀ 0 _ _ (ready_afterInstI hI hcs htr) ht hS₁
    have hb' : p.2 ∈ callBehaviours prof (answerHostS P g)
        (readyCfgI cs' ι' (fsI P c I) G' ST' s₁)
        ⟨0 + calls.length⟩ ⟨c.imports.length + j⟩ (vs.map toRefVal) := by
      rw [← hmₙ, ← hf', Nat.zero_add, ← List.length_map (f := fun q =>
        (c.exports[q.1].name, q.2.map toRefVal))]
      exact hb
    have hact₀ : I.Activation P I.store (cplay lr) (Store.mapH trampIdx cs') := hcs ▸ hact
    have hpre : seqMovesI c calls dss wss ∈ c.toComp.den (impSem P) := by
      rw [seqMovesI_eq]
      exact seqI_den hc hI hrel (cplay_mem_strategy hact₀)
    refine ⟨wss, dss, s₁, hrss, hds, hpre, ?_⟩
    rcases last_callI hc hff har hI hg R' j hvs hb' with hd | ⟨r, u, q, s', hu, hdu, hpath, hobs⟩
    · rw [hd]
      trivial
    · have hall : I.Path P (.idle I.store) (cplay (lr ++ [r])) q := by
        rw [cplay_append]
        exact path_append hact₀ hpath
      have hden : cplay (seqRoundsI c calls dss wss ++ [u]) ∈ c.toComp.den (impSem P) :=
        seqI_den hc hI (forall₂_append hrel (.cons ⟨j, vs, hu⟩ .nil)) (cplay_mem_strategy hall)
      exact seqIRObsIS_of hl₁ hl₂ hu hdu p.2 hobs hden
  · exact absurd (hinst σ _ s₀ _ hr) (by simp)
  · exact absurd (hinst σ _ s₀ _ hr) (by simp)

/-! ## Stateless hosts -/

/-- `SeqIRObsIS` of the stateless `statelessG g₀` is `SeqIRObsI` of `g₀`. -/
theorem seqIRObsI_of_S {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))}
    {wss : List (List Silmaril.Wasm.Component.Val)} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {g₀ : HostFuncId → List Val → Option (List Val)}
    {σI : Strategy (sigN c.imports.length) (sigN c.toComp.exports.length)}
    {b : Silmaril.Wasm.Component.Reference.Outcome}
    (h : SeqIRObsIS c σI calls dss wss j vs (statelessG g₀) () b) :
    SeqIRObsI c σI calls dss wss j vs g₀ b := by
  cases b with
  | returns r =>
    cases r with
    | none => trivial
    | some rs =>
      obtain ⟨ws, ds, _, hrs, hrun, hp⟩ := h
      exact ⟨ws, ds, hrs, hostAnswers_of_run hrun, hp⟩
  | traps =>
    obtain ⟨ds, _, hrun, hp⟩ := h
    exact ⟨ds, hostAnswers_of_run hrun, hp⟩
  | deadlocks => trivial
  | diverges => trivial

/-- **Soundness of the component IR for sequences of calls with imports answered by a host**
(every profile and component choice profile); the stateless instance of `simpleI_sound_seqS`. -/
theorem simpleI_sound_seq (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.Inst) (hff : c.FloatFree) (har : c.Arity)
    (g : HostFuncId → List Val → Option (List Val)) (hg : c.HostOk g)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHost P g) () c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))),
      p.1 = wss.map (·.map toRefVal) ∧ (∀ ds ∈ dss, ∀ d ∈ ds, HostAnswers g d) ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSem P) ∧
      SeqIRObsI c (c.toComp.den (impSem P)) calls dss wss j vs g p.2 := by
  obtain ⟨wss, dss, _, hrss, hrun, hpre, hobs⟩ := simpleI_sound_seqS P prof c hc hi hff har
    (statelessG g) (hostOkS_stateless hg) () calls j vs ht hvs p hp
  exact ⟨wss, dss, hrss, fun ds hds d hd =>
    hostAnswers_of_run hrun d (List.mem_flatten.mpr ⟨ds, hds, hd⟩), hpre, seqIRObsI_of_S hobs⟩

end Silmaril.Proofs.Wasm.Component.Reference
