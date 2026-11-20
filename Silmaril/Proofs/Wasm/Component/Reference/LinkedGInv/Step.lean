module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.Imp

/-!
# One import call of the importer, read back

`call_stepB` of `LinkedGRound` backward. From the importer's core activation stopped at a callout
to the trampoline of import `k` (wired to the exporter's export `w`, `LInvG` and the importer's
frame `FrameG`), on arguments that lift to `ws`, every host-free run to a configuration `E` that
is not live is read back (`call_backB`):

* the nested call (`nest_atX`) up to the exporter's core activation is a live run, so the run
  continues from it;
* R3 (`RefData.BwdF`) on the rest: still running is excluded (`E` is not live); a return of the
  exporter (`EndsT` with a non-empty control chain is R2's return) for a step answering results
  `us` continues with the return half of `nest_atX` to the importer's resumed activation, where
  `LInvG` holds at the exporter's state after the step (`LInvG.resume_fwd`), with the frame and
  `CallExt` (as in `call_stepB`); a return whose results do not lift is a specification trap
  (`trapsAtSH_back`) at the returned core store; R3's trapped case ends at `E`, with the
  footprint discipline of `BwdF`;
* in the trapped ends, `E` is locked down with an empty control chain and the parts are related
  at its core store (`TrapAtG`), for a trapped step of the exporter.

`call_backB'` states the same read-back with the exporter's end (its relation, `Within`, `Grows`)
in place of `LInvG`/`TrapAtG`, for the tracked read-back of `LinkedGChain`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

section Call

variable {b : SimpleI} {Ii : SInst} {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {g : CanonHost (E3 P) → Nat} {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fq : Ii.F.Op}
  {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {ii : Nat}

/-- **One import call read back, with the exporter's end** (`call_backB` below is derived from
it): as `call_backB`, but the returning case gives the run up to the importer's resumed activation
and the exporter's relation and footprint discipline (`Within`, `Grows`) at the returned store
instead of `LInvG`, and the trapping case gives them at a store with the trapped core store
instead of `TrapAtG`. -/
theorem call_backB' (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) (hBw : d.BwdF)
    {s : e.St} {M : Machine.Config (E3 P) σ} {F : CoreFoot}
    {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ fq s M.ref F y x) (th : Option ThreadId)
    (hFG : FrameG d pl ii th M.store)
    {k : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hc : Silmaril.Wasm.Game.CalloutAt x.1 x.2 k args) {q : Ii.E.Op}
    (he : Ii.importOp? k args = some q) {nm : String} {p : FuncTy}
    (hk : b.imports[k]? = some (nm, p)) {w : Nat} {xe : Export}
    (hw : e.comp.exports[w]? = some xe) (hty : xe.ty = p)
    (htr : tr k = .lowered ⟨d.fid pl w⟩ (witFt p) {} ⟨ii⟩)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ))
    (hpf : floatFreeList p.params = true) (hmaxp : (ValTy.flatList p.params).length ≤ 16)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    {ys : List Flat} (hys : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys)
    {ws : List IVal} (hws : liftArgs p.params ys = some ws)
    {trr : List (Label (E3 P) σ)} {E : Machine.Config (E3 P) σ}
    (r : Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trr E)
    (hh : ∀ ev, Label.host ev ∉ trr) (hE : ¬ Live E)
    (hni : E.store.lockdown = true → E.ctl = [] → ∀ msg, Label.trap (.internal msg) ∉ trr) :
    (∃ (us : List IVal) (s' : e.St) (trc tr₂ : List (Label (E3 P) σ))
        (C' : List (Option (Activation (E3 P) σ))) (S'' : RefStore (E3 P)) (F' : CoreFoot),
        e.Step P s ⟨(w, .vals ws), some (.vals us)⟩ s' ∧ ValTy.checkList p.results us = true ∧
        trr = trc ++ tr₂ ∧ trc ≠ [] ∧
        Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trc
          (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest
            (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))) ∧
        Machine.Steps prof (fun _ _ => false) (DI P impl)
          (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest
            (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))) tr₂ E ∧
        d.Hold pl s' S'' F' ∧ F.Within (M.core : Store (CanonHost (E3 P))) S''.core ∧
        F.Grows F' (M.core : Store (CanonHost (E3 P))) ∧
        FrameG d pl ii th S'' ∧ CallExt d pl M.ref S'') ∨
    (∃ s' : e.St, e.Step P s ⟨(w, .vals ws), none⟩ s' ∧ E.store.lockdown = true ∧ E.ctl = [] ∧
      ∃ (S' : RefStore (E3 P)) (F' : CoreFoot), S'.core = E.core ∧ S'.funcs = M.store.funcs ∧
        d.Hold pl s' S' F' ∧ F.Within (M.core : Store (CanonHost (E3 P))) E.core ∧
        F.Grows F' (M.core : Store (CanonHost (E3 P)))) := by
  obtain ⟨nm', p', ys', -, -, hk', -, hys', hst, hyty⟩ := hI.callout_fwd SI hc he
  rw [hk] at hk'
  have hnp := Prod.mk.inj (Option.some.inj hk')
  obtain ⟨hn, hp⟩ := hnp
  subst nm'
  subst p'
  rw [hys] at hys'
  have hy := Option.some.inj hys'
  subst ys'
  have hentry : calloutEntry M.store th (tr k) = none := by
    rw [htr]
    exact hFG.entry _ _ _
  have hl : M.store.lockdown = false := hFG.lock
  obtain ⟨ιi, hi, hleave⟩ := hFG.imp
  obtain ⟨ιe, hie, hth⟩ := hFG.exp w ⟨xe, hw⟩
  rw [htr] at hst hentry
  obtain ⟨hf, hblk⟩ := hFr.lifted pl s M.ref F w xe hI.hold hw
  rw [hty] at hf
  let ie := d.inst pl w
  let t : ThreadId := ⟨M.store.threads.length⟩
  have hadd : ιe.addThread? t = some (1, enterInst ιe t) := addThread?_ok hth t
  have hrem : (enterInst ιe t).removeThread? 1 =
      some (t, InstState.removeThread 1 (enterInst ιe t)) := removeThread?_enter ιe t
  obtain ⟨pos, M₁, K', segs', rest', tr₁, h₁, hc₁, hst₁, hcore₁, hh₁, -, -, -, hinst₁, hret, htrap⟩ :=
    nest_atX (prof := prof) (impl := impl) ie ii M hl ιe (enterInst ιe t) th K segs rest y
      ⟨d.fid pl w⟩ (d.addr pl w) p ys ιi ws hst hentry hi hleave hf hie hadd hrem hpf hyty hmaxp
      hws hres hrf hmaxr
  have hS₁ : M₁.store = nstore M.store { inst := ⟨ii⟩, state := .started }
      (lowerRec ⟨M.store.subtasks.length⟩ ⟨ii⟩ ys p pos)
      ((ntask₁G ie M.store p).withState .started)
      ((thread₁ M.store.tasks).withIndex 1) (M.store.insts.set ie (enterInst ιe t)) :=
    hst₁.trans (nstoreCore_eqG _ _ _ _ _ _ _)
  have hH₁ : d.Hold pl s M₁.ref F :=
    hold_threads hFr hI.hold hie _ (hcore₁.trans hI.core.symm)
      (by show M₁.store.funcs = _; rw [hS₁]; rfl) (by show M₁.store.insts = _; rw [hS₁]; rfl)
  have hl₁ : M₁.store.lockdown = false := by rw [hS₁]; exact hl
  have hfun₁ : M₁.store.funcs = M.store.funcs := by rw [hS₁]; rfl
  have hc₁' : M₁.core = M.core := hcore₁.trans hI.core.symm
  have hstart : d.startCfg pl w xe ws M₁ (some t) K' segs' rest' = M₁ := by
    show { M₁ with ctl := _ } = M₁
    rw [hty, ← hc₁]
  -- the run passes through the exporter's core activation
  rcases h₁.inv r with hl' | ⟨tra, etr, ra⟩
  · exact absurd hl' hE
  have htr₁ : tr₁ ≠ [] := by
    rintro rfl
    cases h₁
    have h := congrArg (fun S : CStore (E3 P) => S.subtasks.length) hS₁
    simp [coreCfg, nstore] at h
  have hha : ∀ ev, Label.host ev ∉ tra := fun ev hm => hh ev (etr ▸ List.mem_append_right _ hm)
  have hck : ValTy.checkList xe.ty.params ws = true := by
    rw [hty]
    exact Silmaril.Wasm.Component.checkList_of_liftArgs hws
  rcases hBw pl s w ws xe hw hck M₁.ref F hH₁ prof impl M₁ (some t) K' segs' rest' rfl hl₁
      hinst₁ tra E (by rw [hstart]; exact ra) hha with
    ⟨hc', hl'⟩ | ⟨tra₁, tra₂, m, R, s', etra, ra₁, ra₂, hstep, ⟨hEnds, hEndsT⟩, hmc⟩ |
      ⟨hlock, hctl, hfn⟩
  · exact absurd ⟨hc', hl'⟩ hE
  · -- a return of the exporter
    rcases hEnds with ⟨S', C', zs, F', rfl, hzty, hlift, hext, hH', hwi, hgr⟩ |
      ⟨-, hlock, -⟩
    swap
    · exact absurd (hEndsT hlock) hmc
    have hzty' : zs.map (·.type) = ValTy.flatList p.results := by rw [← hty]; exact hzty
    have hlS' : S'.lockdown = false := by
      rw [hext.eq]
      exact hl₁
    have hfS' : S'.funcs = M.store.funcs := by
      rw [hext.eq]
      exact hfun₁
    have hiS' : S'.insts[ie]? = some (enterInst ιe t) := by
      rw [hext.insts_exp w]
      show M₁.store.insts[ie]? = _
      rw [hS₁]
      exact List.getElem?_set_self (lt_of_getElem? hie)
    have hcal : CalleeAt ie ii M.store ys p (enterInst ιe t) pos S'.toCStore :=
      calleeAt_ext hst₁ hext hiS' hlS'
    have hwi' : F.Within (M.core : Store (CanonHost (E3 P))) S'.core := hc₁' ▸ hwi
    have hgr' : F.Grows F' (M.core : Store (CanonHost (E3 P))) := hc₁' ▸ hgr
    rcases R with _ | ⟨xs | us⟩
    · -- the results do not lift: a specification trap at the returned core store
      have hn : liftArgs p.results zs = none := by rw [← hty]; exact hlift
      rcases trapsAtSH_back (htrap S' C' zs hcal hzty' hn).2 ra₂ with hl' |
        ⟨mT, rr, -, rfl, hcT, -⟩
      · exact absurd hl' hE
      exact .inr ⟨s', hstep, rfl, rfl, S', F', hcT.symm, hfS', hH', hcT ▸ hwi', hgr'⟩
    · exact hlift.elim
    · -- the results lift: the importer resumes
      have hlift' : liftArgs p.results zs = some us := by rw [← hty]; exact hlift
      have hck' : ValTy.checkList p.results us = true :=
        Silmaril.Wasm.Component.checkList_of_liftArgs hlift'
      obtain ⟨tr₃, h₃⟩ := hret S' C' zs us hcal hzty' hlift'
      rcases h₃.inv ra₂ with hl' | ⟨tr₄, etr₄, r₄⟩
      · exact absurd hl' hE
      let S'' : RefStore (E3 P) := ⟨retStoreG S'.toCStore M.store ie
        (InstState.removeThread 1 (enterInst ιe t))
        (nrecG ie ii M.store ys p pos (lowerArgs p.results us)), S'.core⟩
      have hie' : S'.insts[ie]? = some (enterInst ιe t) := hcal.inst
      have hH'' : d.Hold pl _ S'' F' :=
        hold_threads hFr hH' hie' _ rfl rfl rfl
      have hX : CallExt d pl M.ref S'' := by
        have hpre : ∀ {α : Type} {l : List α} {a : α} {l' : List α}, l ++ [a] <+: l' →
            l <+: l' :=
          fun h => (List.prefix_append _ _).trans h
        have hsub : M.store.subtasks <+: S'.subtasks := hpre ((storeExt_prefixes hS₁ hext).1)
        have hcal' : M.store.callers <+: S'.callers := hpre ((storeExt_prefixes hS₁ hext).2.1)
        have htk : M.store.tasks <+: S'.tasks := hpre ((storeExt_prefixes hS₁ hext).2.2.1)
        have hthr : M.store.threads <+: S'.threads := hpre ((storeExt_prefixes hS₁ hext).2.2.2)
        refine ⟨?_, ?_, ?_, prefix_set hsub (le_refl _) _, hcal', prefix_set htk (le_refl _) _,
          prefix_set hthr (le_refl _) _⟩
        · have key : ∀ T : RefStore (E3 P), T = { M₁.ref with
              core := T.core, insts := T.insts, subtasks := T.subtasks, callers := T.callers,
              tasks := T.tasks, threads := T.threads } →
              (⟨retStoreG T.toCStore M.store ie (InstState.removeThread 1 (enterInst ιe t))
                (nrecG ie ii M.store ys p pos (lowerArgs p.results us)), T.core⟩ : RefStore (E3 P)) =
              { M.ref with
                core := T.core
                insts := T.insts.set ie (InstState.removeThread 1 (enterInst ιe t))
                subtasks := T.subtasks.set M.store.subtasks.length
                  (nrecG ie ii M.store ys p pos (lowerArgs p.results us)).sub
                callers := T.callers
                tasks := T.tasks.set M.store.tasks.length
                  (nrecG ie ii M.store ys p pos (lowerArgs p.results us)).task
                threads := T.threads.set M.store.threads.length
                  (nrecG ie ii M.store ys p pos
                    (lowerArgs p.results us)).thread } := by
            intro T hT
            rw [hT]
            simp only [Machine.Config.ref]
            rw [hS₁]
            rfl
          exact key S' hext.eq
        · show (List.set S'.insts ie _).length = _
          rw [List.length_set, hext.insts_len, Machine.Config.ref_toCStore, hS₁]
          exact List.length_set
        · intro i hi
          have hne : ie ≠ i := fun h => hi (h ▸ hblk)
          show (List.set S'.insts ie _)[i]? = _
          rw [List.getElem?_set_ne hne, hext.insts_out i hi, Machine.Config.ref_toCStore, hS₁]
          exact List.getElem?_set_ne hne
      have hexp : ∀ w' : Nat, (∃ ι, M.store.insts[d.inst pl w']? = some ι ∧ ThreadsOk ι) →
          ∃ ι, S''.insts[d.inst pl w']? = some ι ∧ ThreadsOk ι := by
        rintro w' ⟨ι, hι, hιt⟩
        show ∃ ι', (List.set S'.insts ie _)[d.inst pl w']? = some ι' ∧ _
        by_cases hw' : ie = d.inst pl w'
        · rw [← hw']
          exact ⟨_, List.getElem?_set_self (lt_of_getElem? hie'), threadsOk_after ιe t⟩
        · rw [List.getElem?_set_ne hw', hext.insts_exp w', Machine.Config.ref_toCStore, hS₁]
          exact ⟨ι, (List.getElem?_set_ne hw').trans hι, hιt⟩
      rw [hstart] at ra₁
      refine .inl ⟨us, s', tr₁ ++ (tra₁ ++ tr₃), tr₄, C', S'', F', hstep, hck', ?_, ?_,
        Adequacy.steps_append h₁.steps (Adequacy.steps_append ra₁ h₃.steps), r₄, hH'', hwi',
        hgr', hFG.of_callExt hX hexp, hX⟩
      · rw [etr, etra, etr₄]
        simp only [List.append_assoc]
      · intro h
        exact htr₁ (List.append_eq_nil_iff.mp h).1
  · -- the exporter's run trapped
    have hni' : ∀ msg, Label.trap (.internal msg) ∉ tra :=
      fun msg hm => hni hlock hctl msg (etr ▸ List.mem_append_right _ hm)
    obtain ⟨s', S', F', hstep, hcore, hfun, hH', hwi, hgr⟩ := hfn hni'
    refine .inr ⟨s', hstep, hlock, hctl, ?_⟩
    have hwi'' : F.Within (M.core : Store (CanonHost (E3 P))) S'.core := by
      rw [hcore, ← hc₁']
      exact hwi
    have hgr'' : F.Grows F' (M.core : Store (CanonHost (E3 P))) := by
      rw [← hc₁']
      exact hgr
    exact ⟨S', F', hcore, hfun.trans hfun₁, hH', hcore ▸ hwi'', hgr''⟩

/-- **One import call read back**: a host-free run from the importer's callout to a configuration
that is not live passes through the importer's resumed activation after a returning exporter
step (with `LInvG`, the frame and `CallExt` there), or ends locked down at a trapped exporter
step with the parts related at its core store. -/
theorem call_backB (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) (hBw : d.BwdF)
    (hB : d.Bounded) {s : e.St} {M : Machine.Config (E3 P) σ} {F : CoreFoot}
    {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ fq s M.ref F y x) (th : Option ThreadId)
    (hFG : FrameG d pl ii th M.store)
    {k : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hc : Silmaril.Wasm.Game.CalloutAt x.1 x.2 k args) {q : Ii.E.Op}
    (he : Ii.importOp? k args = some q) {nm : String} {p : FuncTy}
    (hk : b.imports[k]? = some (nm, p)) {w : Nat} {xe : Export}
    (hw : e.comp.exports[w]? = some xe) (hty : xe.ty = p)
    (htr : tr k = .lowered ⟨d.fid pl w⟩ (witFt p) {} ⟨ii⟩)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ))
    (hpf : floatFreeList p.params = true) (hmaxp : (ValTy.flatList p.params).length ≤ 16)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    {ys : List Flat} (hys : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys)
    {ws : List IVal} (hws : liftArgs p.params ys = some ws)
    {trr : List (Label (E3 P) σ)} {E : Machine.Config (E3 P) σ}
    (r : Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trr E)
    (hh : ∀ ev, Label.host ev ∉ trr) (hE : ¬ Live E)
    (hni : E.store.lockdown = true → E.ctl = [] → ∀ msg, Label.trap (.internal msg) ∉ trr) :
    (∃ (us : List IVal) (s' : e.St) (trc tr₂ : List (Label (E3 P) σ))
        (C' : List (Option (Activation (E3 P) σ))) (S'' : RefStore (E3 P)) (F' : CoreFoot),
        e.Step P s ⟨(w, .vals ws), some (.vals us)⟩ s' ∧ ValTy.checkList p.results us = true ∧
        trr = trc ++ tr₂ ∧ trc ≠ [] ∧
        Machine.Steps prof (fun _ _ => false) (DI P impl)
          (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest
            (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))) tr₂ E ∧
        LInvG d pl Ii s₀ u₀ F₀ g Oc₀ fq s' S'' F'
          (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))
          (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
            (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) ∧
        FrameG d pl ii th S'' ∧ CallExt d pl M.ref S'') ∨
    (∃ s' : e.St, e.Step P s ⟨(w, .vals ws), none⟩ s' ∧ E.store.lockdown = true ∧ E.ctl = [] ∧
      TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ fq M.store s' E.core x.1) := by
  obtain ⟨nm', p', ys', E', a', hk', hdx, -, -, -⟩ := hI.callout_fwd SI hc he
  rw [hk] at hk'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hk')
  rcases call_backB' (prof := prof) (impl := impl) SI hFr hBw hI th hFG hc he hk hw hty htr K
      segs rest hpf hmaxp hres hrf hmaxr hys hws r hh hE hni with
    ⟨us, s', trc, tr₂, C', S'', F', hstep, hck, etr, hne, -, r₂, hH, hwi, hgr, hFG', hX⟩ |
    ⟨s', hstep, hlock, hctl, S', F', hc', hf, hH, hwi, hgr⟩
  · exact .inl ⟨us, s', trc, tr₂, C', S'', F', hstep, hck, etr, hne, r₂,
      LInvG.resume_fwd SI hI hk hdx he hck hH hwi hgr (hB pl _ S'' F' hH), hFG', hX⟩
  · refine .inr ⟨s', hstep, hlock, hctl, ?_⟩
    rw [← hc']
    exact trapAt_of_within hI hH hf (hc' ▸ hwi) hgr (hB pl _ S' F' hH)

end Call

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
