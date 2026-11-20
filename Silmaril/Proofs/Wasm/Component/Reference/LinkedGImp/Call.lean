module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.Inv
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.NestExt

/-!
# One import call of the importer answered by an abstract exporter

The importer's part, at `LInvG d pl …`, stops at a callout to its import `k`, whose trampoline
`tr k` is the `canon lower` (of the importer's instance `ii`) of the export `w` of the exporter
`d` at placement `pl`. On the reference machine this is the nested call of `NestExt`
(`nest_atX`: the `canon lower`/`canon lift` wrapper at the instances `ii`, `d.inst pl w`) around
the exporter's core activation, which R2 (`RefData.Fwd`) runs for each step of the exporter's
specification. Here the three are composed:

* `call_ret`: for a returning step `e.Step P s ⟨(w, .vals ws), some (.vals us)⟩ s'` on the lifted
  arguments `ws`, the machine runs, without host events or `internal` traps, from the importer's
  core activation at the callout to its core activation resumed with the lowering of `us`, at a
  store `S''` and continuation slots `C'`, where `LInvG` holds again at `s'` (R1, R2, R6 and
  `LInvG.resume_fwd`), the exporter's export instance has its thread table reset
  (`ThreadsOk`), the instances outside the exporter's block are unchanged, and the store
  otherwise only grows (`CallExt`);
* `call_trap`: for a trapping step (`R = none`), the machine traps (a lockdown) without host
  events or `internal` traps, the exporter's relation holding the trapped core store at `s'`.

R2's `Ends` is used as stated: its continuation slots `C'` are carried to the resumed frame
(the machine never reads them on this path, `NestExt`), and its `StoreExt` gives the callee's
records at their indices (`CalleeAt`), R2 having appended its own records after them.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## The importer's store after a call -/

/-- **The store `S''` after an import call from `S`**: the component store of `S` with the core
store, the instances and the subtask, caller, task and thread arenas replaced, the arenas
extending those of `S`, and the instances outside the exporter's block unchanged. -/
structure CallExt {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (S S'' : RefStore (E3 P)) :
    Prop where
  eq : S'' = { S with
    core := S''.core
    insts := S''.insts
    subtasks := S''.subtasks
    callers := S''.callers
    tasks := S''.tasks
    threads := S''.threads }
  insts_len : S''.insts.length = S.insts.length
  insts_out : ∀ i, ¬ d.block pl i → S''.insts[i]? = S.insts[i]?
  subtasks : S.subtasks <+: S''.subtasks
  callers : S.callers <+: S''.callers
  tasks : S.tasks <+: S''.tasks
  threads : S.threads <+: S''.threads

theorem prefix_set {α : Type} {l l' : List α} (h : l <+: l') {n : Nat} (hn : l.length ≤ n)
    (v : α) : l <+: l'.set n v := by
  obtain ⟨t, rfl⟩ := h
  rw [List.set_append_right _ _ hn]
  exact List.prefix_append _ _

theorem agree_of_eq {H : Type} (F : CoreFoot) {σ₁ σ₂ : Store H} (h : σ₂ = σ₁) :
    F.Agree σ₁ σ₂ := by
  subst h
  exact ⟨List.prefix_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The exporter's relation survives a change of the thread table of one export instance
and of the arenas outside its block**: from `Hold` at `S`, at a store with the same core store
and functions whose instances are those of `S` with the thread table of `d.inst pl w`
replaced. -/
theorem hold_threads {e : ExpSpec} {d : e.RefData P} (hFr : d.Frame) {pl : d.Pl} {s : e.St}
    {S S'' : RefStore (E3 P)} {F : CoreFoot} (hH : d.Hold pl s S F) {w : Nat} {ι : InstState}
    (hι : S.insts[d.inst pl w]? = some ι) (t : Silmaril.Wasm.Component.Runtime.Table ThreadId)
    (hcore : S''.core = S.core) (hfuncs : S''.funcs = S.funcs)
    (hinsts : S''.insts = S.insts.set (d.inst pl w) { ι with threads := t }) :
    d.Hold pl s S'' F := by
  have h₁ := hFr.threads pl s S F w ι t hH hι
  refine hFr.agree pl s _ S'' F h₁ (agree_of_eq F (by rw [hcore])) (by rw [hfuncs]) ?_
  intro i _
  rw [hinsts]

/-! ## One import call -/

section Call

variable {b : SimpleI} {Ii : SInst} {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {g : CanonHost (E3 P) → Nat} {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fq : Ii.F.Op}
  {e : ExpSpec} {d : e.RefData P} {pl : d.Pl}

/-- **A returning import call answered by the exporter** (R1, R2, R6 and `nest_atX`): from the
importer's core activation `y` at the callout of its part `x` to import `k` (of type `p`), whose
trampoline is the `canon lower` (instance `ii`) of the lifted export `w` of the exporter, the
exporter's export instance having a reusable thread table, for a returning step of the
exporter on the lifted arguments `ws`, the machine runs without host events or `internal`
traps to the importer's core activation resumed with the lowering of `us`, at a store `S''`
and continuation slots `C'`, where `LInvG` holds at the exporter's state `s'`. -/
theorem call_ret (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) (hFw : d.Fwd)
    (hB : d.Bounded) {s s' : e.St} {M : Machine.Config (E3 P) σ} {F : CoreFoot}
    {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ fq s M.ref F y x) (hl : M.store.lockdown = false)
    {k : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hc : Silmaril.Wasm.Game.CalloutAt x.1 x.2 k args) {q : Ii.E.Op}
    (he : Ii.importOp? k args = some q) {nm : String} {p : FuncTy}
    (hk : b.imports[k]? = some (nm, p)) {w : Nat} {xe : Export}
    (hw : e.comp.exports[w]? = some xe) (hty : xe.ty = p) {ii : Nat}
    (htr : tr k = .lowered ⟨d.fid pl w⟩ (witFt p) {} ⟨ii⟩)
    (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ))
    (hentry : calloutEntry M.store th (tr k) = none) {ιi : InstState}
    (hi : ArenaField.insts.get? M.store ⟨ii⟩ = some ιi) (hleave : ιi.mayLeave = true)
    {ιe : InstState} (hie : M.store.insts[d.inst pl w]? = some ιe) (hth : ThreadsOk ιe)
    (hpf : floatFreeList p.params = true) (hmaxp : (ValTy.flatList p.params).length ≤ 16)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    {ys : List Flat} (hys : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys)
    {ws us : List IVal} (hws : liftArgs p.params ys = some ws)
    (hstep : e.Step P s ⟨(w, .vals ws), some (.vals us)⟩ s') :
    ∃ (trc : List (Label (E3 P) σ)) (C' : List (Option (Activation (E3 P) σ)))
      (S'' : RefStore (E3 P)) (F' : CoreFoot),
      Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trc
        (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest
          (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))) ∧
      (∀ ev, Label.host ev ∉ trc) ∧ (∀ msg, Label.trap (.internal msg) ∉ trc) ∧
      LInvG d pl Ii s₀ u₀ F₀ g Oc₀ fq s' S'' F'
        (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))
        (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
          (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) ∧
      S''.lockdown = false ∧ CallExt d pl M.ref S'' ∧
      ∀ w' : Nat, (∃ ι, M.store.insts[d.inst pl w']? = some ι ∧ ThreadsOk ι) →
        ∃ ι, S''.insts[d.inst pl w']? = some ι ∧ ThreadsOk ι := by
  obtain ⟨nm', p', ys', E, a', hk', hdx, hys', hst, hyty⟩ := hI.callout_fwd SI hc he
  rw [hk] at hk'
  have hnp := Prod.mk.inj (Option.some.inj hk')
  obtain ⟨hn, hp⟩ := hnp
  subst nm'
  subst p'
  rw [hys] at hys'
  have hy := Option.some.inj hys'
  subst ys'
  rw [htr] at hst hentry
  obtain ⟨hf, hblk⟩ := hFr.lifted pl s M.ref F w xe hI.hold hw
  rw [hty] at hf
  let ie := d.inst pl w
  let t : ThreadId := ⟨M.store.threads.length⟩
  have hadd : ιe.addThread? t = some (1, enterInst ιe t) := addThread?_ok hth t
  have hrem : (enterInst ιe t).removeThread? 1 =
      some (t, InstState.removeThread 1 (enterInst ιe t)) := removeThread?_enter ιe t
  obtain ⟨pos, M₁, K', segs', rest', tr₁, h₁, hc₁, hst₁, hcore₁, hh₁, hp₁, hr₁, hcn₁, hinst₁, hret,
    -⟩ :=
    nest_atX (prof := prof) (impl := impl) ie ii M hl ιe (enterInst ιe t) th K segs rest y
      ⟨d.fid pl w⟩ (d.addr pl w) p ys ιi ws hst hentry hi hleave hf hie hadd hrem hpf hyty hmaxp
      hws hres hrf hmaxr
  -- the exporter's relation at the start of its core activation
  have hS₁ : M₁.store = nstore M.store { inst := ⟨ii⟩, state := .started }
      (lowerRec ⟨M.store.subtasks.length⟩ ⟨ii⟩ ys p pos)
      ((ntask₁G ie M.store p).withState .started)
      ((thread₁ M.store.tasks).withIndex 1) (M.store.insts.set ie (enterInst ιe t)) :=
    hst₁.trans (nstoreCore_eqG _ _ _ _ _ _ _)
  have hH₁ : d.Hold pl s M₁.ref F :=
    hold_threads hFr hI.hold hie _ (hcore₁.trans hI.core.symm)
      (by show M₁.store.funcs = _; rw [hS₁]; rfl) (by show M₁.store.insts = _; rw [hS₁]; rfl)
  have hl₁ : M₁.store.lockdown = false := by rw [hS₁]; exact hl
  -- R2
  obtain ⟨tr₂, m, h₂, hnh₂, hni₂, hEnds⟩ := hFw pl s s' w ws (some (.vals us)) xe hstep hw
    M₁.ref F hH₁ prof impl M₁ (some t) K' segs' rest' rfl hl₁ hinst₁
  have hstart : d.startCfg pl w xe ws M₁ (some t) K' segs' rest' = M₁ := by
    show { M₁ with ctl := _ } = M₁
    rw [hty, ← hc₁]
  rw [hstart] at h₂
  rcases hEnds with ⟨S', C', zs, F', rfl, hzty, hlift, hext, hH', hwi, hgr⟩ | ⟨hR, -⟩
  swap
  · exact absurd hR (by simp)
  have hlift' : liftArgs p.results zs = some us := by rw [← hty]; exact hlift
  have hzty' : zs.map (·.type) = ValTy.flatList p.results := by rw [← hty]; exact hzty
  -- the callee's records are kept
  have hlS' : S'.lockdown = false := by
    rw [hext.eq]
    exact hl₁
  have hiS' : S'.insts[ie]? = some (enterInst ιe t) := by
    rw [hext.insts_exp w]
    show M₁.store.insts[ie]? = _
    rw [hS₁]
    exact List.getElem?_set_self (lt_of_getElem? hie)
  have hcal : CalleeAt ie ii M.store ys p (enterInst ιe t) pos S'.toCStore :=
    calleeAt_ext hst₁ hext hiS' hlS'
  obtain ⟨tr₃, h₃⟩ := hret S' C' zs us hcal hzty' hlift'
  let S'' : RefStore (E3 P) := ⟨retStoreG S'.toCStore M.store ie
    (InstState.removeThread 1 (enterInst ιe t))
    (nrecG ie ii M.store ys p pos (lowerArgs p.results us)), S'.core⟩
  have hS'core : S''.core = S'.core := rfl
  -- the exporter's relation after the call
  have hie' : S'.insts[ie]? = some (enterInst ιe t) := hcal.inst
  have hH'' : d.Hold pl s' S'' F' :=
    hold_threads hFr hH' hie' _ rfl rfl rfl
  have hc₁' : M₁.core = M.core := hcore₁.trans hI.core.symm
  have hwi' : F.Within (M.core : Store (CanonHost (E3 P))) S''.core := hc₁' ▸ hwi
  have hgr' : F.Grows F' (M.core : Store (CanonHost (E3 P))) := hc₁' ▸ hgr
  have hI' := LInvG.resume_fwd SI hI hk hdx he
    (Silmaril.Wasm.Component.checkList_of_liftArgs hlift') hH'' hwi' hgr' (hB pl s' S'' F' hH'')
  have hl'' : S''.lockdown = false := hlS'
  -- the run
  have hlive₁ : Live M₁ := ⟨by rw [hc₁]; exact List.cons_ne_nil _ _, hl₁⟩
  have hlive₃ : Live (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest
      (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))) :=
    ⟨List.cons_ne_nil _ _, hl''⟩
  have hq₁ := Quiet.of_lrun h₁ hlive₁
  have hq₃ := Quiet.of_lrun h₃ hlive₃
  refine ⟨tr₁ ++ tr₂ ++ tr₃, C', S'', F',
    Adequacy.steps_append (Adequacy.steps_append h₁.steps h₂) h₃.steps, ?_, ?_, hI', hl'', ?_, ?_⟩
  · intro ev hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact hq₁.1 ev hm
      · exact hnh₂ ev hm
    · exact hq₃.1 ev hm
  · intro msg hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact hq₁.2 _ hm
      · exact hni₂ msg hm
    · exact hq₃.2 _ hm
  · have hpre : ∀ {α : Type} {l : List α} {a : α} {l' : List α}, l ++ [a] <+: l' → l <+: l' :=
      fun h => (List.prefix_append _ _).trans h
    have hsub : M.store.subtasks <+: S'.subtasks := hpre (storeExt_prefixes hS₁ hext).1
    have hcal' : M.store.callers <+: S'.callers := hpre (storeExt_prefixes hS₁ hext).2.1
    have htk : M.store.tasks <+: S'.tasks := hpre (storeExt_prefixes hS₁ hext).2.2.1
    have hthr : M.store.threads <+: S'.threads := hpre (storeExt_prefixes hS₁ hext).2.2.2
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
              (nrecG ie ii M.store ys p pos (lowerArgs p.results us)).thread } := by
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
  · rintro w' ⟨ι, hι, hιt⟩
    show ∃ ι', (List.set S'.insts ie _)[d.inst pl w']? = some ι' ∧ _
    by_cases hw' : ie = d.inst pl w'
    · rw [← hw']
      exact ⟨_, List.getElem?_set_self (lt_of_getElem? hie'), threadsOk_after ιe t⟩
    · rw [List.getElem?_set_ne hw', hext.insts_exp w', Machine.Config.ref_toCStore, hS₁]
      exact ⟨ι, (List.getElem?_set_ne hw').trans hι, hιt⟩

/-- **A trapping import call answered by the exporter** (R1, R2 and `nest_atX`): as `call_ret`,
for a trapping step of the exporter (`R = none`), the machine traps (its store locked down)
without host events or `internal` traps; the exporter's relation holds at `s'` at a store with
the trapped core store, which differs from the callout's inside the footprint `F` and by fresh
addresses. -/
theorem call_trap (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) (hFw : d.Fwd)
    {s s' : e.St} {M : Machine.Config (E3 P) σ} {F : CoreFoot}
    {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ fq s M.ref F y x) (hl : M.store.lockdown = false)
    {k : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hc : Silmaril.Wasm.Game.CalloutAt x.1 x.2 k args) {q : Ii.E.Op}
    (he : Ii.importOp? k args = some q) {nm : String} {p : FuncTy}
    (hk : b.imports[k]? = some (nm, p)) {w : Nat} {xe : Export}
    (hw : e.comp.exports[w]? = some xe) (hty : xe.ty = p) {ii : Nat}
    (htr : tr k = .lowered ⟨d.fid pl w⟩ (witFt p) {} ⟨ii⟩)
    (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ))
    (hentry : calloutEntry M.store th (tr k) = none) {ιi : InstState}
    (hi : ArenaField.insts.get? M.store ⟨ii⟩ = some ιi) (hleave : ιi.mayLeave = true)
    {ιe : InstState} (hie : M.store.insts[d.inst pl w]? = some ιe) (hth : ThreadsOk ιe)
    (hpf : floatFreeList p.params = true) (hmaxp : (ValTy.flatList p.params).length ≤ 16)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    {ys : List Flat} (hys : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys)
    {ws : List IVal} (hws : liftArgs p.params ys = some ws)
    (hstep : e.Step P s ⟨(w, .vals ws), none⟩ s') :
    ∃ (trc : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ),
      Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trc m' ∧
      (∀ ev, Label.host ev ∉ trc) ∧ (∀ msg, Label.trap (.internal msg) ∉ trc) ∧
      m'.store.lockdown = true ∧
      ∃ (S' : RefStore (E3 P)) (F' : CoreFoot), S'.core = m'.core ∧ d.Hold pl s' S' F' ∧
        F.Within (M.core : Store (CanonHost (E3 P))) S'.core ∧
        F.Grows F' (M.core : Store (CanonHost (E3 P))) := by
  obtain ⟨nm', p', ys', E, a', hk', hdx, hys', hst, hyty⟩ := hI.callout_fwd SI hc he
  rw [hk] at hk'
  have hnp := Prod.mk.inj (Option.some.inj hk')
  obtain ⟨hn, hp⟩ := hnp
  subst nm'
  subst p'
  rw [hys] at hys'
  have hy := Option.some.inj hys'
  subst ys'
  rw [htr] at hst hentry
  obtain ⟨hf, hblk⟩ := hFr.lifted pl s M.ref F w xe hI.hold hw
  rw [hty] at hf
  let ie := d.inst pl w
  let t : ThreadId := ⟨M.store.threads.length⟩
  have hadd : ιe.addThread? t = some (1, enterInst ιe t) := addThread?_ok hth t
  have hrem : (enterInst ιe t).removeThread? 1 =
      some (t, InstState.removeThread 1 (enterInst ιe t)) := removeThread?_enter ιe t
  obtain ⟨pos, M₁, K', segs', rest', tr₁, h₁, hc₁, hst₁, hcore₁, hh₁, -, -, -, hinst₁, -, htrap⟩ :=
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
  obtain ⟨tr₂, m, h₂, hnh₂, hni₂, hEnds⟩ := hFw pl s s' w ws none xe hstep hw
    M₁.ref F hH₁ prof impl M₁ (some t) K' segs' rest' rfl hl₁ hinst₁
  have hstart : d.startCfg pl w xe ws M₁ (some t) K' segs' rest' = M₁ := by
    show { M₁ with ctl := _ } = M₁
    rw [hty, ← hc₁]
  rw [hstart] at h₂
  have hc₁' : M₁.core = M.core := hcore₁.trans hI.core.symm
  have hlive₁ : Live M₁ := ⟨by rw [hc₁]; exact List.cons_ne_nil _ _, hl₁⟩
  have hq₁ := Quiet.of_lrun h₁ hlive₁
  rcases hEnds with ⟨S', C', zs, F', rfl, hzty, hlift, hext, hH', hwi, hgr⟩ |
    ⟨-, hlock, S', F', hcore, -, hH', hwi, hgr⟩
  · have hn : liftArgs p.results zs = none := by rw [← hty]; exact hlift
    have hzty' : zs.map (·.type) = ValTy.flatList p.results := by rw [← hty]; exact hzty
    have hlS' : S'.lockdown = false := by
      rw [hext.eq]
      exact hl₁
    have hiS' : S'.insts[ie]? = some (enterInst ιe t) := by
      rw [hext.insts_exp w]
      show M₁.store.insts[ie]? = _
      rw [hS₁]
      exact List.getElem?_set_self (lt_of_getElem? hie)
    have hcal : CalleeAt ie ii M.store ys p (enterInst ιe t) pos S'.toCStore :=
      calleeAt_ext hst₁ hext hiS' hlS'
    obtain ⟨tr₃, mT, r, hr, h₃, hliveT, hu, hcT, -⟩ := (htrap S' C' zs hcal hzty' hn).2
    have hq₃ := Quiet.of_lrun h₃ hliveT
    refine ⟨tr₁ ++ tr₂ ++ (tr₃ ++ [.trap r]), StepDefs.trapCfg mT,
      Adequacy.steps_append (Adequacy.steps_append h₁.steps h₂)
        (Adequacy.steps_append h₃.steps (.cons hu.1 (.refl _))), ?_, ?_, rfl, S', F', hcT.symm,
      hH', hc₁' ▸ hwi, hc₁' ▸ hgr⟩
    · intro ev hm
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact hq₁.1 ev hm
        · exact hnh₂ ev hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact hq₃.1 ev hm
        · simp at hm
    · intro msg hm
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact hq₁.2 _ hm
        · exact hni₂ msg hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact hq₃.2 _ hm
        · simp only [List.mem_singleton, Label.trap.injEq] at hm
          exact hr msg hm.symm
  · refine ⟨tr₁ ++ tr₂, m, Adequacy.steps_append h₁.steps h₂, ?_, ?_, hlock, S', F', hcore, hH',
      hcore ▸ hc₁' ▸ hwi, hc₁' ▸ hgr⟩
    · intro ev hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq₁.1 ev hm
      · exact hnh₂ ev hm
    · intro msg hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq₁.2 _ hm
      · exact hni₂ msg hm

end Call

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
