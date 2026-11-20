module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.Call
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Call

/-!
# One import call of a round, with the facts the next call needs

`call_ret`/`call_trap` of `LinkedGImp.Call` take, at each callout, the machine facts of the
importer's frame (its thread's instance, its instance's `mayLeave`, the export instance's
thread table). Along a round these facts have to be re-established after every call; here they
are packaged as `FrameG` and kept:

* `FrameG d pl ii th S`: the store is not locked down, the importer's thread `th` runs in
  instance `ii`, which may leave and lies outside the exporter's block, and the thread table of
  every export instance is reusable. It gives `calloutEntry … = none` for every trampoline of
  instance `ii` (`FrameG.entry`) and survives every `CallExt` keeping the export instances'
  thread tables (`FrameG.of_callExt`: the importer's thread and task records are found at their
  indices in the arena prefixes);
* `CallExt` is reflexive and transitive, and holds for a change of the core store;
* `TrapAtG`: the importer's part and the exporter's relation at a trapped core store `c`;
* `call_stepB`: one import call answered by **any** exporter step on the lifted arguments. A
  returning step (`R = some (vals us)`, the results checking against the result types) is
  `call_ret` with `FrameG` again and the results checked; a trapping step (`R = none`) is a
  `TrapEnd` with `TrapAtG` at the trapped core store and the exporter's state after the step;
  a step answering a flat payload has no `Ends`, so does not occur; `call_stepB'` states it with
  the exporter's end (its relation, `Within`, `Grows`) in place of `LInvG`/`TrapAtG`, for the
  tracked rounds of `LinkedGChain`. A returning call's run is non-empty (it passes through the
  exporter's activation, whose start and return differ in their control chain), which the
  coinduction over served calls in `LinkedGDiv` uses.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
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

/-! ## The importer's frame -/

/-- **The importer's frame at the store `S`**: not locked down, the importer's thread `th` in
instance `ii`, which may leave and is outside the exporter's block, and the thread tables of
the export instances reusable. -/
structure FrameG {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (ii : Nat) (th : Option ThreadId)
    (S : CStore (E3 P)) : Prop where
  lock : S.lockdown = false
  cur : instOfThread? S th = some ⟨ii⟩
  imp : ∃ ι : InstState, S.insts[ii]? = some ι ∧ ι.mayLeave = true
  out : ¬ d.block pl ii
  exp : ∀ w : Nat, (∃ xe, e.comp.exports[w]? = some xe) →
    ∃ ι : InstState, S.insts[d.inst pl w]? = some ι ∧ ThreadsOk ι

section Frame

variable {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {ii : Nat} {th : Option ThreadId}

theorem instOfThread?_prefix {S S' : CStore (E3 P)} (ht : S.threads <+: S'.threads)
    (hk : S.tasks <+: S'.tasks) {th : Option ThreadId} {i : InstId}
    (h : instOfThread? S th = some i) : instOfThread? S' th = some i := by
  cases th with
  | none => cases h
  | some t =>
    unfold instOfThread? at h ⊢
    cases h₁ : ArenaField.threads.get? S t with
    | none => simp [h₁] at h
    | some thr =>
      cases h₂ : ArenaField.tasks.get? S thr.task with
      | none => simp [h₁, h₂] at h
      | some tk =>
        have e₁ : ArenaField.threads.get? S' t = some thr :=
          prefix_getElem? (l := S.threads) (l' := S'.threads) ht h₁
        have e₂ : ArenaField.tasks.get? S' thr.task = some tk :=
          prefix_getElem? (l := S.tasks) (l' := S'.tasks) hk h₂
        simpa [h₁, h₂, e₁, e₂] using h

/-- The entry check of a trampoline of instance `ii` passes on the importer's thread. -/
theorem FrameG.entry {S : CStore (E3 P)} (hF : FrameG d pl ii th S) (fid : FuncId)
    (ft : WIT.FuncType Empty RtId) (opts : CanonOpts (E3 P)) :
    calloutEntry S th (.lowered fid ft opts ⟨ii⟩) = none := by
  simp only [calloutEntry, hF.cur, ↓reduceIte]

/-- The frame does not read the core store. -/
theorem FrameG.core {S : CStore (E3 P)} (hF : FrameG d pl ii th S)
    (c : (E3 P).Store (CanonHost (E3 P))) :
    FrameG d pl ii th ({ S with core := c } : RefStore (E3 P)).toCStore :=
  hF

theorem callExt_refl {S : RefStore (E3 P)} (c : (E3 P).Store (CanonHost (E3 P))) :
    CallExt d pl S { S with core := c } :=
  ⟨rfl, rfl, fun _ _ => rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
    List.prefix_refl _⟩

theorem callExt_funcs {S S'' : RefStore (E3 P)} (h : CallExt d pl S S'') : S''.funcs = S.funcs := by
  rw [h.eq]

theorem callExt_lockdown {S S'' : RefStore (E3 P)} (h : CallExt d pl S S'') :
    S''.lockdown = S.lockdown := by
  rw [h.eq]

theorem callExt_trans {S S' S'' : RefStore (E3 P)} (h₁ : CallExt d pl S S')
    (h₂ : CallExt d pl S' S'') : CallExt d pl S S'' where
  eq := by
    rw [h₂.eq, h₁.eq]
  insts_len := h₂.insts_len.trans h₁.insts_len
  insts_out i hi := (h₂.insts_out i hi).trans (h₁.insts_out i hi)
  subtasks := h₁.subtasks.trans h₂.subtasks
  callers := h₁.callers.trans h₂.callers
  tasks := h₁.tasks.trans h₂.tasks
  threads := h₁.threads.trans h₂.threads

/-- **The frame survives a call**: a `CallExt` keeping the export instances' thread tables
reusable. -/
theorem FrameG.of_callExt {S S'' : RefStore (E3 P)} (hF : FrameG d pl ii th S.toCStore)
    (hX : CallExt d pl S S'')
    (hexp : ∀ w : Nat, (∃ ι, S.insts[d.inst pl w]? = some ι ∧ ThreadsOk ι) →
      ∃ ι, S''.insts[d.inst pl w]? = some ι ∧ ThreadsOk ι) : FrameG d pl ii th S''.toCStore where
  lock := (callExt_lockdown hX).trans hF.lock
  cur := instOfThread?_prefix hX.threads hX.tasks hF.cur
  imp := by
    rw [hX.insts_out ii hF.out]
    exact hF.imp
  out := hF.out
  exp w hw := hexp w (hF.exp w hw)

end Frame

/-! ## The parts at a trapped core store -/

/-- **The parts at a trapped core store `c`**: the exporter's relation at the state `s` holds at
a store with the core store `c` and the functions of `S₀`, with a footprint disjoint from the
importer's image of its store `u` in `c`; the importer's functions are in `c`, and `u` is the
store of a run of the importer's activation of `f`. -/
structure TrapAtG {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (Ii : SInst) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (f : Ii.F.Op) (S₀ : CStore (E3 P)) (s : e.St) (c : (E3 P).Store (CanonHost (E3 P)))
    (u : Store Nat) : Prop where
  hold : ∃ (S' : RefStore (E3 P)) (F' : CoreFoot), S'.core = c ∧ S'.funcs = S₀.funcs ∧
    d.Hold pl s S' F' ∧ ∃ ρc Oc, PartRel ρc Oc (reloc s₀ u) (Store.mapH g c) ∧
      Oc.fn = Oc₀.fn ∧ Oc.gl = Oc₀.gl ∧ FootDisj F' ρc Oc c
  fnC : FnPre s₀ (Store.mapH g c) u
  funcs : c.funcs = F₀
  run : ∃ t : STh, Silmaril.Wasm.Game.SSteps P (valEnv Ii)
    (Silmaril.Wasm.Execution.Core.invoke u₀ (Ii.addr f.1) f.2.1, ()) (t.config u, ())

section Trap

variable {b : SimpleI} {Ii : SInst} {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {g : CanonHost (E3 P) → Nat} {Oc₀ : Own} {f : Ii.F.Op}
  {e : ExpSpec} {d : e.RefData P} {pl : d.Pl}

/-- **The parts where the importer stopped**, from `LInvG`. -/
theorem trapAt_of_linv {s : e.St} {S : RefStore (E3 P)} {S₀ : CStore (E3 P)} {F : CoreFoot} {y : CoreSt (E3 P)}
    {x : Store Nat × STh} (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s S F y x)
    (hf : S.funcs = S₀.funcs) : TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f S₀ s y.1 x.1 := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD⟩ := hI.rel
  have hR0 : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g y.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  exact ⟨⟨S, F, hI.core, hf, hI.hold, ρc, Oc, hR0, hfn, hgl, hD⟩, hL.fn, hI.funcs, ⟨x.2, hI.run⟩⟩

/-- **The parts after the exporter trapped**: the exporter changed the core store inside its
footprint and by fresh addresses, holding the state `s'` at `S'` with an allocated, grown
footprint. -/
theorem trapAt_of_within {s s' : e.St} {S S' : RefStore (E3 P)} {S₀ : CStore (E3 P)} {F F' : CoreFoot}
    {y : CoreSt (E3 P)} {x : Store Nat × STh} (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s S F y x)
    (hH : d.Hold pl s' S' F') (hf : S'.funcs = S₀.funcs)
    (hw : F.Within (S.core : Store (CanonHost (E3 P))) S'.core)
    (hgF : F.Grows F' (S.core : Store (CanonHost (E3 P))))
    (hB : F'.Bounded (S'.core : Store (CanonHost (E3 P)))) :
    TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f S₀ s' S'.core x.1 := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD⟩ := hI.rel
  rw [hI.core] at hw hgF
  have hR0 : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g y.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  have hrc : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g S'.core) := partRel_within hR0 hD hw
  exact ⟨⟨S', F', rfl, hf, hH, ρc, Oc, hrc, hfn, hgl, hD.after_owner hR0 hgF hB⟩,
    hL.fn.congr (mapH_funcs_eq g hw.funcs) rfl, hw.funcs.trans hI.funcs, ⟨x.2, hI.run⟩⟩

end Trap

/-- A run with an empty trace does not move. -/
theorem steps_nil_eqG {m m' : Machine.Config (E3 P) σ}
    (h : Machine.Steps prof (fun _ _ => false) (DI P impl) m [] m') : m = m' := by
  cases h
  rfl

/-! ## One import call, for any step of the exporter -/

section Call

variable {b : SimpleI} {Ii : SInst} {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {g : CanonHost (E3 P) → Nat} {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fq : Ii.F.Op}
  {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {ii : Nat}

/-- **One import call answered by the exporter, with the exporter's end**: `call_stepB` whose
returning case gives the exporter's relation at the returned store and its footprint discipline
(`CoreFoot.Within`, `CoreFoot.Grows`) instead of `LInvG`, and whose trapping case gives them at
a store with the trapped core store instead of `TrapAtG`. -/
theorem call_stepB' (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) (hFw : d.Fwd)
    {s s' : e.St} {M : Machine.Config (E3 P) σ} {F : CoreFoot}
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
    {ws : List IVal} (hws : liftArgs p.params ys = some ws) {R : Option Payload}
    (hstep : e.Step P s ⟨(w, .vals ws), R⟩ s') :
    (∃ us : List IVal, R = some (.vals us) ∧ ValTy.checkList p.results us = true ∧
      ∃ (trc : List (Label (E3 P) σ)) (C' : List (Option (Activation (E3 P) σ)))
        (S'' : RefStore (E3 P)) (F' : CoreFoot),
        Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trc
          (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest
            (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))) ∧
        (∀ ev, Label.host ev ∉ trc) ∧ (∀ msg, Label.trap (.internal msg) ∉ trc) ∧
        d.Hold pl s' S'' F' ∧ F.Within (M.core : Store (CanonHost (E3 P))) S''.core ∧
        F.Grows F' (M.core : Store (CanonHost (E3 P))) ∧
        FrameG d pl ii th S''.toCStore ∧ CallExt d pl M.ref S'' ∧ trc ≠ []) ∨
    (R = none ∧ ∃ c, TrapEnd prof P impl (coreCfg M th K segs rest y) c ∧
      ∃ (S' : RefStore (E3 P)) (F' : CoreFoot), S'.core = c ∧ S'.funcs = M.store.funcs ∧
        d.Hold pl s' S' F' ∧ F.Within (M.core : Store (CanonHost (E3 P))) c ∧
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
  obtain ⟨tr₂, m, h₂, hnh₂, hni₂, hEnds⟩ := hFw pl s s' w ws R xe hstep hw
    M₁.ref F hH₁ prof impl M₁ (some t) K' segs' rest' rfl hl₁ hinst₁
  have hstart : d.startCfg pl w xe ws M₁ (some t) K' segs' rest' = M₁ := by
    show { M₁ with ctl := _ } = M₁
    rw [hty, ← hc₁]
  rw [hstart] at h₂
  have hc₁' : M₁.core = M.core := hcore₁.trans hI.core.symm
  have hlive₁ : Live M₁ := ⟨by rw [hc₁]; exact List.cons_ne_nil _ _, hl₁⟩
  have hq₁ := Quiet.of_lrun h₁ hlive₁
  rcases hEnds with ⟨S', C', zs, F', rfl, hzty, hlift, hext, hH', hwi, hgr⟩ |
    ⟨hR, hlock, S', F', hcore, hfun, hH', hwi, hgr⟩
  · have hzty' : zs.map (·.type) = ValTy.flatList p.results := by rw [← hty]; exact hzty
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
    · -- the results do not lift
      have hn : liftArgs p.results zs = none := by rw [← hty]; exact hlift
      obtain ⟨tr₃, mT, r, hr, h₃, hliveT, hu, hcT, -⟩ := (htrap S' C' zs hcal hzty' hn).2
      have hq₃ := Quiet.of_lrun h₃ hliveT
      refine .inr ⟨rfl, S'.core, ⟨tr₁ ++ tr₂ ++ (tr₃ ++ [.trap r]), StepDefs.trapCfg mT,
        Adequacy.steps_append (Adequacy.steps_append h₁.steps h₂)
          (Adequacy.steps_append h₃.steps (.cons hu.1 (.refl _))), ?_, ?_, rfl, hcT⟩,
        S', F', rfl, hfS', hH', hwi', hgr'⟩
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
    · exact hlift.elim
    · -- the results lift
      have hlift' : liftArgs p.results zs = some us := by rw [← hty]; exact hlift
      have hck : ValTy.checkList p.results us = true :=
        Silmaril.Wasm.Component.checkList_of_liftArgs hlift'
      obtain ⟨tr₃, h₃⟩ := hret S' C' zs us hcal hzty' hlift'
      let S'' : RefStore (E3 P) := ⟨retStoreG S'.toCStore M.store ie
        (InstState.removeThread 1 (enterInst ιe t))
        (nrecG ie ii M.store ys p pos (lowerArgs p.results us)), S'.core⟩
      have hie' : S'.insts[ie]? = some (enterInst ιe t) := hcal.inst
      have hH'' : d.Hold pl _ S'' F' :=
        hold_threads hFr hH' hie' _ rfl rfl rfl
      have hl'' : S''.lockdown = false := hlS'
      have hlive₃ : Live (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest
          (S''.core, (E3 P).resume S''.core y.2 (.values (lowerArgs p.results us)))) :=
        ⟨List.cons_ne_nil _ _, hl''⟩
      have hq₃ := Quiet.of_lrun h₃ hlive₃
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
      have htr₂ : tr₂ ≠ [] := by
        rintro rfl
        have e := congrArg Machine.Config.ctl (steps_nil_eqG h₂)
        rw [hc₁] at e
        simp [ExpSpec.RefData.retCfg'] at e
      refine .inl ⟨us, rfl, hck, tr₁ ++ tr₂ ++ tr₃, C', S'', F',
        Adequacy.steps_append (Adequacy.steps_append h₁.steps h₂) h₃.steps, ?_, ?_, hH'', hwi',
        hgr', hFG.of_callExt hX hexp, hX, fun h =>
          htr₂ (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2⟩
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
  · -- the exporter trapped
    subst hR
    refine .inr ⟨rfl, m.core, ⟨tr₁ ++ tr₂, m, Adequacy.steps_append h₁.steps h₂, ?_, ?_,
      hlock, rfl⟩, ?_⟩
    · intro ev hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq₁.1 ev hm
      · exact hnh₂ ev hm
    · intro msg hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq₁.2 _ hm
      · exact hni₂ msg hm
    · have hwi'' : F.Within (M.core : Store (CanonHost (E3 P))) S'.core := by
        rw [hcore, ← hc₁']
        exact hwi
      have hgr'' : F.Grows F' (M.core : Store (CanonHost (E3 P))) := by
        rw [← hc₁']
        exact hgr
      exact ⟨S', F', hcore, hfun.trans hfun₁, hH', hcore ▸ hwi'', hgr''⟩

/-- **One import call answered by the exporter**, for any step on the lifted arguments: a
returning step resumes the importer as `call_ret` (with its frame again and the results
checked), a trapping step is a trapped end with the parts at the trapped core store. -/
theorem call_stepB (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) (hFw : d.Fwd)
    (hB : d.Bounded) {s s' : e.St} {M : Machine.Config (E3 P) σ} {F : CoreFoot}
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
    {ws : List IVal} (hws : liftArgs p.params ys = some ws) {R : Option Payload}
    (hstep : e.Step P s ⟨(w, .vals ws), R⟩ s') :
    (∃ us : List IVal, R = some (.vals us) ∧ ValTy.checkList p.results us = true ∧
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
        FrameG d pl ii th S''.toCStore ∧ CallExt d pl M.ref S'' ∧ trc ≠ []) ∨
    (R = none ∧ ∃ c, TrapEnd prof P impl (coreCfg M th K segs rest y) c ∧
      TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ fq M.store s' c x.1) := by
  obtain ⟨nm', p', ys', E, a', hk', hdx, -, -, -⟩ := hI.callout_fwd SI hc he
  rw [hk] at hk'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hk')
  rcases call_stepB' (prof := prof) (impl := impl) SI hFr hFw hI th hFG hc he hk hw hty htr
      K segs rest hpf hmaxp hres hrf hmaxr hys hws hstep with
    ⟨us, hR, hck, trc, C', S'', F', hrun, hnh, hni, hH, hwi, hgr, hFG', hX, hne⟩ |
    ⟨hR, c, hT, S', F', hc', hf, hH, hwi, hgr⟩
  · exact .inl ⟨us, hR, hck, trc, C', S'', F', hrun, hnh, hni,
      LInvG.resume_fwd SI hI hk hdx he hck hH hwi hgr (hB pl _ S'' F' hH), hFG', hX, hne⟩
  · subst hc'
    exact .inr ⟨hR, S'.core, hT, trapAt_of_within hI hH hf hwi hgr (hB pl _ S' F' hH)⟩

end Call

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
