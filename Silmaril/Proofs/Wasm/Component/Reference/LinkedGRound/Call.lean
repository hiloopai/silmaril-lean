module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.CallG

/-!
# One session round of a linked component with an abstract exporter, forward

`linkCall_fwd` of `LinkedSessionFwd` for `LinkedG` with an exporter given by reference data `d`
(R1, R2, R5, R6) at a placement `pl`: from a configuration between calls (`ReadyB`), a
`LinkedG.SessSpec` round (`SessRound.Ok`, the importer's instance play from `u` to `u₁`, its
component import calls an `ExpRun` of the exporter from `s` to `s₁`) is a top-level call of the
reference machine (`Calls`):

* a round answering results `ws` is a resolved call ending between calls, `ReadyB` holding at
  `s₁`, `u₁` and the next call id;
* a round answering a trap is a trapped call (with a specification trap), and `ReadyB` holds at
  `resumeCfg` of it (R5).

The machine run is the host's invocation (`invoke_stepG`), the importer's `canon lift` up to its
core activation (`call_atG`), the importer's round (`rounds_fwdB`), and its end: the return
(`CallAtG.ret`), a lift of the results that fails (`CallAtG.trap`), a trap of the importer's core
activation (`coreTrap_end`), or a trapped end of the round.

* `StatB`: the static facts: the importer's `ImpStatG` (at its store after instantiation), its
  wiring `WireG`, its instance `ii` outside the exporter's block, its functions owned in the
  shared store, and its exports lifted at the function ids `jf j` of the store between calls;
* `ReadyB`: between calls: control empty, not locked down, nesting depth zero, the functions
  `fs`, the importer's instance reusable and allowed to leave, the export instances reusable,
  earlier calls with smaller ids, and `LReadyG`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload checkLower)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## The static facts and the configurations between calls -/

/-- **The static facts of a round**: the importer's static facts at its store `ui` after
instantiation, its wiring, its instance `ii` outside the exporter's block, its functions owned
in the shared store (above the `s₀.funcs.length` functions of its relocation), and its export
`j` the `canon lift` of its core export at function id `jf j` of `fs`. -/
structure StatB (P : Profile) (lg : LinkedG) (d : lg.exp.RefData P) (pl : d.Pl) (ii : Nat)
    (Ii : SInst) (s₀ ui : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P))))
    (g : CanonHost (E3 P) → Nat) (tr : Nat → CanonHost (E3 P)) (Oc₀ : Own)
    (fs : List (CFuncInst (core3P P))) (jf : Nat → Nat) : Prop where
  imp : ImpStatG P lg.imp Ii ui F₀ g tr
  wire : WireG lg d pl tr ii
  out : ¬ d.block pl ii
  own : ∀ a, a < ui.funcs.length → Oc₀.fn (s₀.funcs.length + a)
  lifted : ∀ j : Fin lg.imp.exports.length, fs[jf j.val]? =
    some (.lifted (s₀.funcs.length + Ii.addrs.getD lg.imp.exports[j].core 0)
      (liftedFt lg.imp.exports[j]) {} ⟨ii⟩)

/-- **A configuration between calls**: ready for the host, the importer's and the export
instances reusable, earlier calls with ids below `k`, and the importer's invariant `LReadyG` at
the exporter's state `s` and the importer's store `u`. -/
structure ReadyB {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (ii : Nat) (Ii : SInst)
    (s₀ ui : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat)
    (Oc₀ : Own) (fs : List (CFuncInst (core3P P))) (m : Machine.Config (E3 P) σ) (s : e.St)
    (u : Store Nat) (k : Nat) : Prop where
  ctl : m.ctl = []
  lock : m.store.lockdown = false
  nest : m.store.nestingDepth = 0
  funcs : m.store.funcs = fs
  imp : ∃ ι : InstState, m.store.insts[ii]? = some ι ∧ ThreadsOk ι ∧ ι.mayLeave = true
  exp : ∀ w : Nat, (∃ xe, e.comp.exports[w]? = some xe) →
    ∃ ι : InstState, m.store.insts[d.inst pl w]? = some ι ∧ ThreadsOk ι
  pending : ∀ x ∈ m.pending, x.1.idx < k
  results : ∀ x ∈ m.results, x.1.idx < k
  inv : LReadyG d pl Ii s₀ ui F₀ g Oc₀ m.ref s u

/-- What a forward round shows for its outcome `o`: results `ws` are a resolved call ending
between calls; a trap is a trapped call, `resumeCfg` of which is between calls. -/
def FwdOutB (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) {e : ExpSpec}
    (d : e.RefData P) (pl : d.Pl) (ii : Nat) (Ii : SInst) (s₀ ui : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (fs : List (CFuncInst (core3P P))) (m : Machine.Config (E3 P) σ) (k j : Nat)
    (args : List RVal) (s₁ : e.St) (u₁ : Store Nat) : Option (List IVal) → Prop
  | some ws => ∃ m', Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨j⟩ args m'
      (.resolved (some (ws.map toRefVal))) ∧ ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m' s₁ u₁ (k + 1)
  | none => ∃ m', Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨j⟩ args m' .trap ∧
      ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs (resumeCfg m m') s₁ u₁ (k + 1)

/-! ## The host's invocation -/

theorem invoke_stepG {m : Machine.Config (E3 P) σ} {k : Nat} (hc : m.ctl = [])
    (hl : m.store.lockdown = false) (hn : m.store.nestingDepth = 0)
    (hp : ∀ x ∈ m.pending, x.1.idx < k) (j : Nat) (args : List RVal) :
    Step prof (fun _ _ => false) (DI P impl) m (.host (.invoke ⟨k⟩ ⟨j⟩ args))
      (invokedG m k j args) := by
  refine Step.hostInvoke ⟨hc, hl, hn⟩ fun y hy e => ?_
  have hlt := hp y hy
  rw [e] at hlt
  exact Nat.lt_irrefl _ hlt

/-- **A trapped end after the invocation is a trapped call.** -/
theorem calls_of_trapEndG {m : Machine.Config (E3 P) σ} {k j : Nat} (hc : m.ctl = [])
    (hl : m.store.lockdown = false) (hn : m.store.nestingDepth = 0)
    (hp : ∀ x ∈ m.pending, x.1.idx < k) {args : List RVal}
    {c : (E3 P).Store (CanonHost (E3 P))}
    (h : TrapEnd prof P impl (invokedG m k j args) c) :
    ∃ m', Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨j⟩ args m' .trap ∧
      m'.core = c := by
  obtain ⟨tr, m', r, hh, hi, hl', hc'⟩ := h
  exact ⟨m', ⟨tr, .cons (invoke_stepG hc hl hn hp j args) r, fun ev hm => absurd hm (hh ev),
    fun _ msg => hi msg, hl'⟩, hc'⟩

theorem find?_freshG {L : List (CallId × Option (List RVal))} {k : Nat}
    (h : ∀ x ∈ L, x.1.idx < k) : L.find? (·.1 == (⟨k⟩ : CallId)) = none := by
  rw [List.find?_eq_none]
  intro x hx e
  have hlt := h x hx
  have hx' : x.1 = ⟨k⟩ := by simpa using e
  rw [hx'] at hlt
  exact Nat.lt_irrefl _ hlt

theorem prefix_concat_split {α : Type} {l l' : List α} {a : α} (h : l ++ [a] <+: l') :
    ∃ R, l' = l ++ [a] ++ R := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, hR.symm⟩

theorem callExt_nest {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {S S'' : RefStore (E3 P)}
    (h : CallExt d pl S S'') : S''.nestingDepth = S.nestingDepth := by
  rw [h.eq]

/-- The trapped end of the round is a trapped call, `resumeCfg` of which is between calls. -/
theorem trap_outB {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {ii : Nat} {Ii : SInst}
    {s₀ ui : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
    {Oc₀ : Own} {fs : List (CFuncInst (core3P P))} (hRes : d.Resume)
    {m : Machine.Config (E3 P) σ} {s s₁ : lg.exp.St} {u u₁ : Store Nat} {k j : Nat}
    (R : ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k) {args : List RVal} {f : Ii.F.Op}
    {c : (E3 P).Store (CanonHost (E3 P))} (hT : TrapEnd prof P impl (invokedG m k j args) c)
    (hTA : TrapAtG d pl Ii s₀ u F₀ g Oc₀ f m.store s₁ c u₁) :
    ∃ m', Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨j⟩ args m' .trap ∧
      ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs (resumeCfg m m') s₁ u₁ (k + 1) := by
  obtain ⟨m', hc, hcore⟩ := calls_of_trapEndG R.ctl R.lock R.nest R.pending hT
  refine ⟨m', hc, R.ctl, R.lock, R.nest, R.funcs, R.imp, R.exp,
    fun x hx => Nat.lt_succ_of_lt (R.pending x hx), fun x hx => Nat.lt_succ_of_lt (R.results x hx),
    ?_⟩
  show LReadyG d pl Ii s₀ ui F₀ g Oc₀ { m.store with core := m'.core } s₁ u₁
  rw [hcore]
  exact lready_trapG hRes R.inv hTA

/-! ## One round -/

section Round

variable {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {ii : Nat} {Ii : SInst}
  {s₀ ui : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fs : List (CFuncInst (core3P P))}
  {jf : Nat → Nat}

/-- **A specification round of a linked component with an abstract exporter is a call of the
reference machine** (`FwdOutB`). -/
theorem linkCall_fwdB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hFw : d.Fwd) (hRes : d.Resume) (hB : d.Bounded) {m : Machine.Config (E3 P) σ}
    {s : lg.exp.St} {u : Store Nat} {k : Nat}
    (R : ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k) (dr : LinkedG.SessRound lg Ii)
    (hok : dr.Ok) {u₁ : Store Nat} (hpath : Ii.Path P (.idle u) dr.instMoves (.idle u₁))
    {s₁ : lg.exp.St} (hexp : LinkedG.ExpRun P lg s dr.dss.flatten s₁)
    {o : Option (List IVal)} (hans : dr.ans = o.map .vals) :
    FwdOutB prof P impl d pl ii Ii s₀ ui F₀ g Oc₀ fs m k (jf dr.j) (dr.vs.map toRefVal) s₁ u₁
      o := by
  obtain ⟨xs, hck, hf₁, hf₂, hrel⟩ := hok
  have hvs : ValTy.checkList lg.imp.exports[dr.j].ty.params dr.vs = true := by
    unfold checkLower at hck
    split_ifs at hck with h
    exact h
  have hxs : xs = lowerArgs lg.imp.exports[dr.j].ty.params dr.vs := by
    simp only [checkLower, hvs, ↓reduceIte, Option.some.injEq] at hck
    exact hck.symm
  subst hxs
  have SI := ST.imp
  have hx : lg.imp.exports[dr.j] ∈ lg.imp.exports := List.getElem_mem dr.j.isLt
  obtain ⟨nm, hcore⟩ := SI.good.core _ hx
  have hflat : lg.imp.mod.exports[lg.imp.exports[dr.j].core]? =
      some (nm, lg.imp.exports[dr.j].ty.flat) := hcore
  have hft' : Ii.exports.get dr.f.1 = fnOf lg.imp.exports[dr.j].ty.flat := by
    have hlt : dr.f.1.val < lg.imp.mod.exports.length := by
      rw [hf₁]
      exact (List.getElem?_eq_some_iff.mp hflat).1
    have e₁ : Ii.exports.get dr.f.1 = fnOf (lg.imp.mod.exports[dr.f.1.val]'hlt).2 := by
      simp only [List.get_eq_getElem, SI.inst.2.2, List.getElem_map]
    rw [e₁]
    have e₂ : lg.imp.mod.exports[dr.f.1.val]'hlt = (nm, lg.imp.exports[dr.j].ty.flat) := by
      have := (List.getElem?_eq_some_iff.mp hflat).2
      simp only [← hf₁] at this
      exact this
    rw [e₂]
  obtain ⟨hmax, hmaxr, hres⟩ := ST.wire.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := ST.wire.floats.1 _ hx
  have ha : Ii.addrs.getD lg.imp.exports[dr.j].core 0 = Ii.addr dr.f.1 := by
    rw [← hf₁]
    rfl
  have hfj : m.store.funcs[jf dr.j]? = some (.lifted (s₀.funcs.length + Ii.addr dr.f.1)
      (liftedFt lg.imp.exports[dr.j]) {} ⟨ii⟩) := by
    rw [R.funcs, ← ha]
    exact ST.lifted dr.j
  obtain ⟨ιi, hii, hth, hleave⟩ := R.imp
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atG (impl := impl) prof m R.lock k
    (jf dr.j) _ ii lg.imp.exports[dr.j] dr.vs hpf hvs hmax hres hmaxr hrf hii hth hfj
  -- the invariants at the start of the importer's core activation
  have hR₀ : LReadyG d pl Ii s₀ ui F₀ g Oc₀ M₀.ref s u := by
    refine lready_frame hFr R.inv hat.core (by show M₀.store.funcs = _; rw [hat.store]; rfl) ?_
    intro i hi
    show M₀.store.insts[i]? = _
    rw [hat.store]
    exact List.getElem?_set_ne (fun h => ST.out (by rw [h]; exact hi))
  obtain ⟨F, hI₀⟩ := linv_readyG hR₀ ST.own (f := dr.f) hf₂
  have SIu : ImpStatG P lg.imp Ii u F₀ g tr := ⟨SI.good, SI.inst, R.inv.wfI, SI.tramp, SI.inv⟩
  obtain ⟨F₁, -, -, -, -, -, -, hH₀⟩ := R.inv.rel
  have hFG₀ : FrameG d pl ii th M₀.store := by
    refine ⟨by rw [hat.store]; exact R.lock, ?_, ?_, ST.out, ?_⟩
    · rw [hat.store, hat.thread]
      have h₁ : ArenaField.threads.get? (storeG₃ m.store lg.imp.exports[dr.j] ii
          (enterInst ιi ⟨m.store.threads.length⟩) k (dr.vs.map toRefVal))
          ⟨m.store.threads.length⟩ = some ((thread₁ m.store.tasks).withIndex 1) :=
        threads_get_last rfl
      have h₂ : ArenaField.tasks.get? (storeG₃ m.store lg.imp.exports[dr.j] ii
          (enterInst ιi ⟨m.store.threads.length⟩) k (dr.vs.map toRefVal))
          ((thread₁ m.store.tasks).withIndex 1).task =
          some ((taskG₁ lg.imp.exports[dr.j] ii m.store.callers
            ⟨m.store.threads.length⟩).withState .started) :=
        tasks_get_last rfl
      simp only [instOfThread?, h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
    · rw [hat.store]
      exact ⟨enterInst ιi ⟨m.store.threads.length⟩, List.getElem?_set_self (lt_of_getElem? hii),
        hleave⟩
    · intro w hw
      obtain ⟨xe, hxe⟩ := hw
      obtain ⟨-, hblk⟩ := hFr.lifted pl s m.ref F₁ w xe hH₀ hxe
      rw [hat.store]
      show ∃ ι, (List.set m.store.insts ii (enterInst ιi ⟨m.store.threads.length⟩))[d.inst pl w]? =
        some ι ∧ _
      have hne : ii ≠ d.inst pl w := fun h => ST.out (by rw [h]; exact hblk)
      rw [List.getElem?_set_ne hne]
      exact R.exp w ⟨xe, hxe⟩
  -- the instance's play
  have hpath' : Ii.Path P (.running dr.f u (Ii.initThread dr.f))
      (callMoves dr.cs ++ [.inr (.ans dr.f dr.w)]) (.idle u₁) := by
    have h : Ii.Path P (.idle u) (.inr (.ask dr.f) :: (callMoves dr.cs ++
        [.inr (.ans dr.f dr.w)])) (.idle u₁) := hpath
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      exact h₂
  have hM₀ : M₀ = coreCfg M₀ th K segs rest (M₀.ref.core,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr dr.f.1)
        (lowerArgs lg.imp.exports[dr.j].ty.params dr.vs)) := eq_coreCfg hat.ctl
  have hlive₀ : Live M₀ := ⟨by rw [hat.ctl]; exact List.cons_ne_nil _ _, by
    rw [hat.store]; exact R.lock⟩
  have hq₁ := Quiet.of_lrun hpre hlive₀
  have hround := rounds_fwdB (prof := prof) (impl := impl) SIu ST.wire hFr hFw hB th K segs rest
    dr.cs dr.dss M₀ s s₁ F _ _ u₁ hI₀ hFG₀ hrel hexp hpath'
  -- a trapped end
  have hfr : ∀ c, TrapEnd prof P impl M₀ c →
      TrapAtG d pl Ii s₀ u F₀ g Oc₀ dr.f m.store s₁ c u₁ → dr.ans = none →
      FwdOutB prof P impl d pl ii Ii s₀ ui F₀ g Oc₀ fs m k (jf dr.j) (dr.vs.map toRefVal) s₁ u₁
        o := by
    intro c hT hTA hn
    have ho : o = none := by
      cases o with
      | none => rfl
      | some ws =>
        rw [hn] at hans
        cases hans
    subst ho
    exact trap_outB hRes R (TrapEnd.steps hpre.steps hq₁ hT) hTA
  rcases hround with ⟨trc, C', S'', F', yc, t', r, hrun, hq, hIc, final, hw, hFG', hX'⟩ |
    ⟨c, hT, hTA, hw⟩
  · -- the importer's part finished
    rw [← hM₀] at hrun
    have hS₀ : S''.funcs = m.store.funcs := by
      rw [callExt_funcs hX', Machine.Config.ref_toCStore, hat.store]
      rfl
    have hTA₀ : TrapAtG d pl Ii s₀ u F₀ g Oc₀ dr.f m.store s₁ yc.1 u₁ :=
      trapAt_of_linv hIc hS₀
    obtain ⟨ρc, Oc, hLc, -⟩ := hIc.rel
    cases r with
    | throw b => exact (not_result_throw hLc final).elim
    | trap =>
      exact hfr _ (TrapEnd.stepsI hrun hq (coreTrap_end (status_of_trap g hLc final))) hTA₀
        (lifted_trap (x := lg.imp.exports[dr.j]) (fun _ h => by cases h) hw)
    | values cvs =>
      have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
          (Ii.exports.get dr.f.1).results cvs := by
        unfold Silmaril.Wasm.Game.Answer.ofResult? at hw
        dsimp only at hw
        split_ifs at hw with ht
        exact ht
      rw [hft'] at htyped
      obtain ⟨zs, hm⟩ := Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
      have hst := status_of_values g hLc final hm
      have hty : zs.map (·.type) = ValTy.flatList lg.imp.exports[dr.j].ty.results :=
        results_typed hft' hw hm
      have hR' : dr.ans = (liftArgs lg.imp.exports[dr.j].ty.results zs).map .vals :=
        lifted_answer hw hm
      have s₃ : Step prof (fun _ _ => false) (DI P impl)
          (coreCfg { M₀ with conts := C', store := S''.toCStore, core := S''.core } th K segs rest yc) .tau
          (retCfg { M₀ with conts := C', store := S''.toCStore, core := S''.core } th K segs rest yc zs) :=
        Step.coreReturned rfl hst
      have hlS'' : S''.lockdown = false := hFG'.lock
      cases hl : liftArgs lg.imp.exports[dr.j].ty.results zs with
      | none =>
        rw [hl] at hR'
        exact hfr _ (TrapEnd.stepsI hrun hq (TrapEnd.steps (.cons s₃ (.refl _)) Quiet.tau
          (hat.trap S'' C' yc zs hlS'' hty hl).trapEnd)) hTA₀ hR'
      | some ws =>
        rw [hl] at hR'
        have ho : o = some ws := by
          cases o with
          | none =>
            rw [hans] at hR'
            cases hR'
          | some ws' =>
            rw [hans] at hR'
            simp only [Option.map_some, Option.some.injEq, Payload.vals.injEq] at hR'
            rw [hR']
        subst ho
        -- the call's records in the store at the return
        have hM₀s : M₀.ref.toCStore = _ := hat.store
        obtain ⟨RT, hRT⟩ := prefix_concat_split (hM₀s ▸ hX'.tasks)
        obtain ⟨RH, hRH⟩ := prefix_concat_split (hM₀s ▸ hX'.threads)
        obtain ⟨CL, hCL⟩ := prefix_concat_split (hM₀s ▸ hX'.callers)
        have hIi : S''.insts[ii]? = some (enterInst ιi ⟨m.store.threads.length⟩) := by
          rw [hX'.insts_out ii ST.out, hM₀s]
          exact List.getElem?_set_self (lt_of_getElem? hii)
        obtain ⟨tr₃, mE, hlr, rfl⟩ := hat.ret S'' C' RT RH CL yc zs ws hRT hRH hCL hIi hlS''
          hty hl
        have hnest : S''.nestingDepth = 1 := by
          rw [callExt_nest hX', hM₀s]
          show m.store.nestingDepth + 1 = 1
          rw [R.nest]
        refine ⟨_, ⟨tr₁ ++ (trc ++ (.tau :: tr₃)), .cons (invoke_stepG R.ctl R.lock R.nest
          R.pending _ _) (Adequacy.steps_append hpre.steps (Adequacy.steps_append hrun
            (.cons s₃ hlr.steps))), ?_, (fun h => by cases h), ⟨rfl, hlS'', ?_⟩⟩, ?_⟩
        · intro ev hm
          exfalso
          rcases List.mem_append.mp hm with hm | hm
          · exact hq₁.1 ev hm
          · rcases List.mem_append.mp hm with hm | hm
            · exact hq.1 ev hm
            · rcases List.mem_cons.mp hm with hm | hm
              · cases hm
              · exact Adequacy.LRun.no_host hlr ev hm
        · unfold Machine.Config.result?
          show ((M₀.results ++ [((⟨k⟩ : CallId), some (ws.map toRefVal))]).find?
            (fun p => p.1 == (⟨k⟩ : CallId))).map Prod.snd = _
          rw [hat.results, List.find?_append, find?_freshG R.results]
          simp
        · -- between calls again
          have hR₁ := lready_afterG R.inv hIc
          refine ⟨rfl, hlS'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · show S''.nestingDepth - 1 = 0
            rw [hnest]
          · show S''.funcs = fs
            rw [hS₀, R.funcs]
          · exact ⟨_, List.getElem?_set_self (lt_of_getElem? hIi),
              threadsOk_after ιi ⟨m.store.threads.length⟩,
              (removeThread_enter_mayLeave _ _).trans hleave⟩
          · intro w hw
            obtain ⟨xe, hxe⟩ := hw
            obtain ⟨-, hblk⟩ := hFr.lifted pl s m.ref F₁ w xe hH₀ hxe
            show ∃ ι, (List.set S''.insts ii _)[d.inst pl w]? = some ι ∧ _
            have hne : ii ≠ d.inst pl w := fun h => ST.out (by rw [h]; exact hblk)
            rw [List.getElem?_set_ne hne]
            exact hFG'.exp w ⟨xe, hxe⟩
          · intro x hx
            have hx' : x ∈ M₀.pending := hx
            rw [hat.pending] at hx'
            rcases List.mem_append.mp hx' with hx' | hx'
            · exact Nat.lt_succ_of_lt (R.pending x hx')
            · rw [List.mem_singleton.mp hx']
              exact Nat.lt_succ_self k
          · intro x hx
            have hx' : x ∈ M₀.results ++ [((⟨k⟩ : CallId), some (ws.map toRefVal))] := hx
            rw [hat.results] at hx'
            rcases List.mem_append.mp hx' with hx' | hx'
            · exact Nat.lt_succ_of_lt (R.results x hx')
            · rw [List.mem_singleton.mp hx']
              exact Nat.lt_succ_self k
          · refine lready_frame hFr hR₁ hIc.core.symm rfl ?_
            intro i hi
            show (S''.insts.set ii _)[i]? = _
            exact List.getElem?_set_ne (fun h => ST.out (by rw [h]; exact hi))
  · -- a trapped end of the round
    rw [← hM₀] at hT
    exact hfr c hT (hTA.funcs_congr (by rw [hat.store]; rfl))
      (lifted_trap (x := lg.imp.exports[dr.j]) (fun _ h => by cases h) hw)

end Round

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
