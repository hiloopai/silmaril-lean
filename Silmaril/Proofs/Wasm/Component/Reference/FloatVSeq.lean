module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVSeqPath
public import Silmaril.Proofs.Wasm.Component.Reference.FloatVSound
public import Silmaril.Proofs.Wasm.Component.Reference.MultiSeq
public import Silmaril.Proofs.Wasm.Component.Reference.MultiIR

/-!
# Sequences of export calls with floats

`Simple.sound_seq_floatV`: `Simple.sound_seq` with floats at every type, variant payloads
included (`FloatSeq` without floats in variant payloads). Every behaviour of a sequence of
calls is the IR play of the calls on
**some** admissible lowerings of their arguments (`NanCallsV prof calls calls'`, one
`NanAtVList` witness per call), the reference reporting the IR results canonicalised
(`canonResultsV`), and the last call on an admissible lowering `vs'`, as `SeqIRObsFV` prescribes.

The reference half (`seq_refToSpecFV`) follows `seq_refToSpec` (`MultiSeq`) with the branching
run of each call (`call_trunKV`): call `k` from a configuration between calls runs the core
activation of some admissible argument list, and a resolution ends at the next configuration
between calls with the canonicalised results (`calls_factsFV`, `diverges_factsFV`). The IR half
is `seqSpecToIR` on the admissible lowerings, which does not depend on floats.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower FuncTy)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## The specification at a store, with canonicalised results -/

/-- `specAt` with the returned values canonicalised. -/
def specAtFV (P : Profile) (_c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) (x : SimpleExport)
    (vs : List IVal) (s : Silmaril.Wasm.Execution.Core.Store Nat) :
    Set Silmaril.Wasm.Component.Reference.Outcome :=
  match checkLower x.ty.params vs with
  | none => {.traps}
  | some xs =>
    {b | ∃ r ∈ coreAt P I x.core xs s, b = liftOutcomeFV x.ty r} ∪
      {b | b = .diverges ∧ Silmaril.Wasm.Execution.Core.Diverges P
        Silmaril.Wasm.SingleThreaded.Det.noHost
        (Silmaril.Wasm.Execution.Core.invoke s (I.addrs.getD x.core 0)
          (xs.map Silmaril.Wasm.SingleThreaded.ofFlat))}

/-- **`specAtFV` is `specAt` with canonicalised results.** -/
theorem specAtF_casesV {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {x : SimpleExport} {vs : List IVal} {s : Silmaril.Wasm.Execution.Core.Store Nat}
    {b : Silmaril.Wasm.Component.Reference.Outcome} (hb : b ∈ specAtFV P c I x vs s) :
    (b = .traps ∧ .traps ∈ specAt P c I x vs s) ∨ b = .diverges ∨
      ∃ ws, b = .returns (some ((canonAtVList x.ty.results ws).map toRefVal)) ∧
        .returns (some (ws.map toRefVal)) ∈ specAt P c I x vs s := by
  unfold specAtFV at hb
  unfold specAt
  cases hl : checkLower x.ty.params vs with
  | none =>
    rw [hl] at hb
    exact .inl ⟨hb, rfl⟩
  | some xs =>
    rw [hl] at hb
    rcases hb with ⟨r, hr, rfl⟩ | ⟨rfl, -⟩
    · rcases liftOutcomeF_casesV x.ty r with ⟨e₁, e₂⟩ | ⟨ws, e₁, e₂⟩
      · exact .inl ⟨e₁, .inl ⟨r, hr, e₂.symm⟩⟩
      · exact .inr (.inr ⟨ws, e₁, .inl ⟨r, hr, e₂.symm⟩⟩)
    · exact .inr (.inl rfl)

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport} {vs : List IVal}

theorem CallCtxAt.specFV (C : CallCtxAt P c I cs x vs)
    {b : Silmaril.Wasm.Component.Reference.Outcome}
    (h : ∃ r ∈ coreAt P I x.core (lowerArgs x.ty.params vs) (Store.mapH (fun _ => 0) cs),
      b = liftOutcomeFV x.ty r) :
    b ∈ specAtFV P c I x vs (Store.mapH (fun _ => 0) cs) := by
  unfold specAtFV
  rw [C.lowerOk]
  exact .inl h

theorem CallCtxAt.specF_divergesV (C : CallCtxAt P c I cs x vs)
    (h : Silmaril.Wasm.Execution.Core.Diverges P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke (Store.mapH (fun _ => 0) cs) (I.addrs.getD x.core 0)
        ((lowerArgs x.ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat))) :
    .diverges ∈ specAtFV P c I x vs (Store.mapH (fun _ => 0) cs) := by
  unfold specAtFV
  rw [C.lowerOk]
  exact .inr ⟨rfl, h⟩

/-! ## Call `k` with floats -/

variable {ι : InstState} {fs : List (CFuncInst (core3P P))} {G : Garb P} {k j : Nat}

/-- What a call outcome says about call `k` of export `x` on `vs` whose core activation runs
the admissible lowering `vs'`: an outcome of `specAtFV` on `vs'` at the current store, and for a
resolution a returned call on `vs'` with canonicalised results, ending between calls. -/
def CallFactsFV (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) (x : SimpleExport) (k j : Nat)
    (vs vs' : List IVal) (m' : Machine.Config (E3 P) Unit) (out : CallOutcome) : Prop :=
  Outcome.ofCall out ∈ specAtFV P c I x vs' (Store.mapH (fun _ => 0) cs) ∧
    ∀ rs, out = .resolved (some rs) → ∃ cs' ws,
      rs = (canonAtVList x.ty.results ws).map toRefVal ∧
      RetAt P c I x vs' (Store.mapH (fun _ => 0) cs) ws (Store.mapH (fun _ => 0) cs') ∧
      m' = nextCfg cs' ι fs G x k j (I.addrs.getD x.core 0) (vs.map toRefVal) rs

/-- Call `k` after a returned core activation, with floats. -/
theorem values_factsFV {vs' : List IVal} (C : CallCtxAt P c I cs x vs') (R : ReadyAt I cs ι G k)
    {M₀ : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtKFV prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x
      (I.addrs.getD x.core 0) (vs.map toRefVal) (lowerArgs x.ty.params vs') M₀ th K segs rest)
    {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs')) y)
    {ys : List FlatValue} (hst : (E3 P).status y.1 y.2 = .returned (.values ys))
    {tr : List (Label (E3 P) Unit)} {m' : Machine.Config (E3 P) Unit} {out : CallOutcome}
    (hs : Steps prof (refHost P).hr (D P) (retCfg M₀ th K segs rest y ys) tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨k⟩ m') : CallFactsFV P c I cs ι fs G x k j vs vs' m' out := by
  obtain ⟨hout, hty, hret⟩ := C.values hy hst
  cases hl : liftArgs x.ty.results ys with
  | some ws =>
    have hres := result?_next R.fresh x j (I.addrs.getD x.core 0) (vs.map toRefVal)
      ((canonAtVList x.ty.results ws).map toRefVal) y.1
      (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩)) fs
    obtain ⟨rfl, hm⟩ := out_of_resolvesK (hat.ret y ys ws hty hl) hres hs hev ho
    refine ⟨C.specFV ⟨_, hout, by simp only [Outcome.ofCall, liftOutcomeFV, hl]⟩, ?_⟩
    intro rs hrs
    have hrs' : rs = (canonAtVList x.ty.results ws).map toRefVal :=
      (Option.some.inj (CallOutcome.resolved.inj hrs)).symm
    exact ⟨y.1, ws, hrs', hret ws hl, hrs' ▸ hm⟩
  | none =>
    obtain rfl := out_of_trapsNextK (hat.trap y ys hty hl) hs ho
    exact ⟨C.specFV ⟨_, hout, by simp only [Outcome.ofCall, liftOutcomeFV, hl]⟩,
      fun _ h => nomatch h⟩

/-- **Call `k` after the core activation left it**, with floats. -/
theorem exit_factsFV {vs' : List IVal} (C : CallCtxAt P c I cs x vs') (R : ReadyAt I cs ι G k)
    {M₀ : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtKFV prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x
      (I.addrs.getD x.core 0) (vs.map toRefVal) (lowerArgs x.ty.params vs') M₀ th K segs rest)
    {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs')) y)
    {l : Label (E3 P) Unit} {m₁ m' : Machine.Config (E3 P) Unit} {tr : List (Label (E3 P) Unit)}
    {out : CallOutcome} (hx : CoreExit M₀ th K segs rest y l m₁)
    (hs : Steps prof (refHost P).hr (D P) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨k⟩ m') : CallFactsFV P c I cs ι fs G x k j vs vs' m' out := by
  rcases hx with ⟨ys, hst, -, hm⟩ | ⟨hst, -, hm⟩ | ⟨h, args, hst⟩
  · exact values_factsFV C R hat hy hst (hm ▸ hs) hev ho
  · have hm' : m' = trapCfg (coreCfg M₀ th K segs rest y) := steps_of_locked rfl rfl (hm ▸ hs)
    have hout : out = .trap := by
      cases out with
      | resolved r => exact absurd (hm' ▸ ho).2.1 (by simp)
      | trap => rfl
      | deadlock => exact absurd (hm' ▸ ho).1.2.1 (by simp)
    exact hout ▸ ⟨C.specFV ⟨_, C.trap hy hst, rfl⟩, fun _ h => nomatch h⟩
  · exact (C.no_callout hy hst).elim

/-- After the core activation left it, call `k` with floats does not diverge. -/
theorem exit_not_diverges_kFV {vs' : List IVal} (C : CallCtxAt P c I cs x vs')
    {M₀ : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtKFV prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x
      (I.addrs.getD x.core 0) (vs.map toRefVal) (lowerArgs x.ty.params vs') M₀ th K segs rest)
    {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs')) y)
    {l : Label (E3 P) Unit} {m₁ : Machine.Config (E3 P) Unit}
    (hx : CoreExit M₀ th K segs rest y l m₁) : ¬ Diverges prof (refHost P).hr (D P) m₁ := by
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨-, hty, -⟩ := C.values hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      obtain ⟨tr₃, mE, hlr, rfl⟩ := hat.ret y ys ws hty hl
      exact fun hd => not_diverges_of_ctl_nil rfl (hlr.diverges hd)
    | none => exact trapsNext_not_diverges (hat.trap y ys hty hl)
  · exact not_diverges_trapCfg _
  · exact (C.no_callout hy hst).elim

/-- The branching run of call `k` of export `x` from a configuration between calls. -/
theorem trunK_ofV (R : ReadyAt I cs ι G k)
    (hvs : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hf : fs[j]? = some (.lifted (I.addrs.getD x.core 0) (liftedFt x) {} ⟨0⟩)) :
    TRun prof (refHost P).hr (D P)
      (QFKV prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x (I.addrs.getD x.core 0) vs)
      (invokedAt cs ι fs G k j (vs.map toRefVal)) :=
  call_trunKV prof cs ι _ fs G k j _ x vs hvs hmax hres hmaxr
    (addThread?_ok R.threads _) (removeThread?_enter _ _) hf

/-- **Terminating calls between calls with floats** follow the specification at the current
store on some admissible lowering. -/
theorem calls_factsFV (hI : c.mod.IsInst I) (R : ReadyAt I cs ι G k)
    (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (ht : TRun prof (refHost P).hr (D P)
      (QFKV prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x (I.addrs.getD x.core 0) vs)
      (invokedAt cs ι fs G k j (vs.map toRefVal)))
    {m' : Machine.Config (E3 P) Unit} {out : CallOutcome}
    (hcalls : Calls prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal) m'
      out) :
    ∃ vs', NanAtVList prof x.ty.params vs vs' ∧ ValTy.checkList x.ty.params vs' = true ∧
      CallFactsFV P c I cs ι fs G x k j vs vs' m' out := by
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, s, r⟩ := Steps.cons_iff.mp hs
  have r₁ : Steps prof (refHost P).hr (D P) (invokedAt cs ι fs G k j (vs.map toRefVal)) tr m' :=
    invoke_inv_k s ▸ r
  rcases ht.inv r₁ with hl | ⟨mq, tr₁, tr₂, ⟨vs', th, K, segs, rest, hn, hck, hat⟩, e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  have C : CallCtxAt P c I cs x vs' := ⟨hI, R.wf, hcore, hck⟩
  refine ⟨vs', hn, hck, ?_⟩
  rcases coreCfg_steps_inv (core_run_k hat.ctl hat.core r') with
    ⟨y, -, hm, -⟩ | ⟨y, pre, l, m₁, tr₃, hy, -, e', hx, r''⟩
  · have hl : Live (coreCfg mq th K segs rest y) := ⟨List.cons_ne_nil _ _, hat.lock⟩
    exact absurd (hm ▸ ho) (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₃ → CallHostEvent ⟨k⟩ ev := fun ev hm =>
    hev ev (by rw [e, e']; exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_cons_of_mem _ hm)))
  exact exit_factsFV C R hat hy hx r'' hev' ho

/-- **Divergent calls between calls with floats** diverge in the core on some admissible
lowering. -/
theorem diverges_factsFV (hI : c.mod.IsInst I) (R : ReadyAt I cs ι G k)
    (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (ht : TRun prof (refHost P).hr (D P)
      (QFKV prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x (I.addrs.getD x.core 0) vs)
      (invokedAt cs ι fs G k j (vs.map toRefVal)))
    (hd : CallDiverges prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) :
    ∃ vs', NanAtVList prof x.ty.params vs vs' ∧ ValTy.checkList x.ty.params vs' = true ∧
      .diverges ∈ specAtFV P c I x vs' (Store.mapH (fun _ => 0) cs) := by
  obtain ⟨m₂, s, hd⟩ := hd
  have hd₁ : Diverges prof (refHost P).hr (D P) (invokedAt cs ι fs G k j (vs.map toRefVal)) :=
    invoke_inv_k s ▸ hd
  obtain ⟨mq, ⟨vs', th, K, segs, rest, hn, hck, hat⟩, hd'⟩ := ht.diverges hd₁
  have C : CallCtxAt P c I cs x vs' := ⟨hI, R.wf, hcore, hck⟩
  refine ⟨vs', hn, hck, ?_⟩
  have hd₀ : Diverges prof (refHost P).hr (D P) (coreCfg mq th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs'))) :=
    eq_core_k hat.ctl hat.core ▸ hd'
  rcases coreCfg_diverges_inv hd₀ with hi | ⟨y, l, m₁, hy, hx, hd''⟩
  · exact C.specF_divergesV (coreRun_diverges (P := P) (fun _ => (0 : Nat))
      (Silmaril.InfiniteTrace.map id (fun _ _ h => h.2) hi))
  · exact (exit_not_diverges_kFV C hat hy hx hd'').elim

end Silmaril.Proofs.Wasm.Component.Reference
