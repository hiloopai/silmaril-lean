module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.UStep

/-!
# Backward simulation: `resume`

The converse of `sim_resume`: an encoded `resume` takes the entries of `block btD` and
`block btH`, the FX `resume` (with nothing but the continuation in front of it, so its split is
forced), and for a fresh continuation the FX `invoke` of its function; these are the only steps
(`lpath_resume`, `ucont_start`), so the next related configuration is inevitable (`u_resume`,
`umatched_resume`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (SX FS outer code_top step_seq step_block step_resume
  resolve_clause bodyH calleeAnn top_module forall₂_getElem? forall₂_set mainOk_seg stkCtx_append
  lowCtx_plug plug_comp opsF_cons topCtx_plug opsF_nil Top cfgOf sstep_exec sexec_resume)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval?)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} (S : Setup H) {W : Prog (Ins Val)}

/-- The FX `invoke` that starts a fresh continuation is its only step. -/
theorem ucont_fresh {f : Nat} {fi : FuncInst H} {h : H} {Yb : List InstrFX} (G : Frame)
    (K : List (Option ContFX)) (hfi : S.s.funcs[S.fa f]? = some fi) (hcode : fi.code = .host h)
    (hfx : S.fx h = some ⟨S.M, 0, 1, [], localGets 0 ++ Yb⟩) :
    LU o S.fx S.s G (K, [.core (.ref (.func (S.fa f))), .core (.callRefType fi.type)])
      (K, [.frame 1 (Frame.forCall S.M [] []) [.label 1 [] (adm Yb)]]) := by
  have hl : LU o S.fx S.s G (K, fvals ([] ++ liftV [] ++ [.val (.ref (.func (S.fa f)))]) ++
      .core (.callRefType fi.type) :: [])
      (K, fvals [] ++ [.frame 1 (Frame.forCall S.M [] [])
        [.label 1 [] ((localGets 0 ++ Yb).map InstrFX.toAdmin)]] ++ []) := by
    refine ⟨?_, fun d hd => uniq_invoke (Fn := ⟨S.M, 0, 1, [], localGets 0 ++ Yb⟩)
      (c := .callRefType fi.type) trivial hfi hcode hfx rfl hd,
      quiet_of rfl (isCallRef_fval trivial) trivial id trivial⟩
    have hst := StepFX'.invoke (P := Profile.deterministic o) (host := noHost) (fx := S.fx)
      (s := S.s) (K := K) (f := G) (vs := [])
      (show Admin.IsCallRef (.callRefType fi.type) from trivial) hfi hcode hfx rfl
    simpa [cvals, vals, liftV, FVal.toAdmin, Val.toAdmin] using hst
  simpa [liftV, FVal.toAdmin, Val.toAdmin, localGets, adm] using hl

/-- **The start of a resumed continuation**, by unique steps: a captured segment as it is, a
fresh one after the FX `invoke` of its function. -/
theorem ucont_start (hok : Ok S W) {seg : List (SFrame Val)} {C : ContFX}
    (h : KRel S W (some seg) (some C)) :
    ∃ st, seg = st.map Prod.fst ∧ SegOk S W st ∧ ∀ (G : Frame) (K : List (Option ContFX)),
      LRun o S.fx S.s G (K, C.plug []) (K, (stkCtx S st).plug []) := by
  rcases h with ⟨f, body, fi, hW, hfi, rfl, rfl⟩ | ⟨st, rfl, hst, rfl⟩
  · obtain ⟨-, fi', h, Yb, -, hfi', hcode, hfx, henc⟩ := hok.funcs f 0 body hW
    have hfi_eq : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
    let q : SFrame Val × Ann := (⟨body, [], none⟩, calleeAnn S [] Yb)
    have hq : SegOk S W [q] := ⟨List.cons_ne_nil _ _, fun p hp => by
      rcases List.mem_singleton.mp hp with rfl
      exact ⟨⟨henc, fun _ h => by cases h; rfl⟩, rfl⟩, fun _ h => absurd h List.not_mem_nil⟩
    have hc : (stkCtx S [q]).plug [] = [.frame 1 (Frame.forCall S.M [] []) [.label 1 [] (adm Yb)]] := by
      simp [stkCtx, lowsCtx, plug_comp, q, topCtx_plug, kindCtx, calleeAnn, opsF, CtxV.plug]
    refine ⟨[q], rfl, hq, fun G K => .inr (.one ?_)⟩
    rw [hc]
    exact ucont_fresh S G K hfi (hfi_eq ▸ hcode) hfx
  · exact ⟨st, rfl, hst, fun _ _ => .inl rfl⟩

/-- **The unique run of an encoded `resume`**, at the frame `F` of the resumer. -/
theorem lpath_resume {K : List (Option ContFX)} {F : Frame} (hF : F.module = S.M) {k t hf : Nat}
    {C : ContFX} (hk : K[k]? = some (some C)) (htag : TagOk S t) {btD btH : BlockType}
    {d₁ d₂ e₁ e₂ : List Silmaril.Wasm.Validation.CValType}
    (hD : S.M.blockType? btD = some (d₁, d₂)) (hD₁ : d₁.length = 1) (hD₂ : d₂.length = 1)
    (hH : S.M.blockType? btH = some (e₁, e₂)) (hH₁ : e₁.length = 1)
    (hH₂ : e₂.length = S.ar t + 1) {Z Y : List InstrFX} (O : List FVal) {Xst : List AdminFX}
    (hst : LRun o S.fx S.s F (K.set k none, C.plug []) (K.set k none, Xst)) :
    LPath o S.fx S.s F
      (K, fvals (O ++ [.cont k]) ++ .block btD (.block btH (bodyH S t) :: Z) :: adm Y)
      (K.set k none, fvals O ++ (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug Xst ++ adm Y) := by
  have hD' : F.module.blockType? btD = some (d₁, d₂) := by rw [hF]; exact hD
  have hH' : F.module.blockType? btH = some (e₁, e₂) := by rw [hF]; exact hH
  have hr := resolve_clause S htag hF
  -- `block btD`
  have l₁ : LU o S.fx S.s F
      (K, fvals (O ++ [.cont k]) ++ .block btD (.block btH (bodyH S t) :: Z) :: adm Y)
      (K, fvals O ++ [.label 1 [] (fvals [.cont k] ++ .block btH (bodyH S t) :: adm Z)] ++
        adm Y) := by
    refine ⟨?_, fun d hd => ?_, quiet_of rfl rfl trivial id trivial⟩
    · simpa [hD₂, adm, InstrFX.toAdmin] using step_seq O (adm Y) (StepFX'.block (P := Profile.deterministic o)
        (host := noHost) (fx := S.fx) (s := S.s) (K := K) (body := .block btH (bodyH S t) :: Z)
        (vs := [.cont k]) hD' (by rw [hD₁]; rfl))
    · simpa [hD₂, adm, InstrFX.toAdmin] using uniq_block hD' (by rw [hD₁]; rfl) hd
  -- `block btH`, inside the label of `btD`
  have l₂ : LU o S.fx S.s F
      (K, fvals O ++ [.label 1 [] (fvals [.cont k] ++ .block btH (bodyH S t) :: adm Z)] ++ adm Y)
      (K, fvals O ++ [.label 1 [] (.label (S.ar t + 1) [] (fvals [.cont k] ++
        [.fx (.resume S.ct [.onLabel (S.xt t) (ix 0)]), br1]) :: adm Z)] ++ adm Y) := by
    have h := lu_plug (o := o) (fx := S.fx) (s := S.s) (F := F)
      (E := .seq O (.label 1 [] .hole) (adm Y)) trivial
      (show LU o S.fx S.s F (K, fvals ([] ++ [.cont k]) ++ .block btH (bodyH S t) :: adm Z)
        (K, fvals [] ++ [.label e₂.length [] (fvals [.cont k] ++ (bodyH S t).map InstrFX.toAdmin)] ++
          adm Z) from
      ⟨by simpa using step_seq [] (adm Z) (StepFX'.block (P := Profile.deterministic o)
          (host := noHost) (fx := S.fx) (s := S.s) (K := K) (body := bodyH S t)
          (vs := [.cont k]) hH' (by rw [hH₁]; rfl)),
        fun d hd => uniq_block hH' (by rw [hH₁]; rfl) hd, quiet_of rfl rfl trivial id trivial⟩)
    simpa [CtxV.plug, hH₂, bodyH, br1, adm, InstrFX.toAdmin] using h
  -- the FX `resume`, inside the label of `btH`
  have l₃ : LU o S.fx S.s F
      (K, fvals O ++ [.label 1 [] (.label (S.ar t + 1) [] (fvals [.cont k] ++
        [.fx (.resume S.ct [.onLabel (S.xt t) (ix 0)]), br1]) :: adm Z)] ++ adm Y)
      (K.set k none, fvals O ++ [.label 1 [] (.label (S.ar t + 1) []
        [.handler [.onLabel (S.ta t) (ix 0)] (C.plug []), br1] :: adm Z)] ++ adm Y) := by
    have h := lu_plug (o := o) (fx := S.fx) (s := S.s) (F := F)
      (E := .seq O (.label 1 [] (.seq [] (.label (S.ar t + 1) [] .hole) (adm Z))) (adm Y)) trivial
      (show LU o S.fx S.s F (K, fvals [.cont k] ++ .fx (.resume S.ct [.onLabel (S.xt t) (ix 0)]) ::
          [br1]) (K.set k none, [.handler [.onLabel (S.ta t) (ix 0)] (C.plug [])] ++ [br1]) from
      ⟨by simpa [FVal.toAdmin] using step_seq [] [br1] (StepFX'.resume (P := Profile.deterministic o)
          (host := noHost) (fx := S.fx) (vs := []) (ct := S.ct) hk hr),
        fun d hd => uniq_resume hk hr hd, quiet_of rfl rfl trivial id trivial⟩)
    simpa [CtxV.plug] using h
  -- the start of the continuation, under the handler
  have l₄ := lrun_plug (o := o) (fx := S.fx) (s := S.s) (F := F)
    (E := .seq O (.label 1 [] (.seq [] (.label (S.ar t + 1) []
      (.seq [] (.handler [.onLabel (S.ta t) (ix 0)] .hole) [br1])) (adm Z))) (adm Y)) trivial hst
  have l₄' : LRun o S.fx S.s F
      (K.set k none, fvals O ++ [.label 1 [] (.label (S.ar t + 1) []
        [.handler [.onLabel (S.ta t) (ix 0)] (C.plug []), br1] :: adm Z)] ++ adm Y)
      (K.set k none, fvals O ++ (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug Xst ++ adm Y) := by
    simpa [CtxV.plug, waitCtx] using l₄
  exact .cons l₁ (.cons l₂ (LPath.run (.one l₃) l₄'))

/-- **`resume 0 [(on t hf)]`** on continuation `k` (segment `top :: seg`): the converse of
`sim_resume`. -/
theorem u_resume (hS : SX S = SD o S.fx) (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {k t hf np : Nat} {top : SFrame Val} {seg : List (SFrame Val)}
    {o' : List (SV Val)} {c bh : List (Ins Val)} {Y Z : List InstrFX} {btD btH : BlockType}
    {d₁ d₂ e₁ e₂ : List Silmaril.Wasm.Validation.CValType}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = .cont k :: o') (hKK : KK[k]? = some (some (top :: seg)))
    (hY : a.code = .block btD (.block btH (bodyH S t) :: Z) :: Y) (htag : TagOk S t)
    (hh : W hf = some (np, bh)) (hZ : EncI S W bh Z)
    (hD : S.M.blockType? btD = some (d₁, d₂)) (hD₁ : d₁.length = 1) (hD₂ : d₂.length = 1)
    (hH : S.M.blockType? btH = some (e₁, e₂)) (hH₁ : e₁.length = 1)
    (hH₂ : e₂.length = S.ar t + 1) (henc : EncI S W c Y) :
    InevP (SX S) TermFX
      (Rel S W ⟨KK.set k none, top :: seg ++ { fr with code := c, ops := o', wait := some [⟨t, hf⟩] } ::
        rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  obtain ⟨C', hC', hrel⟩ := forall₂_getElem? hK hKK
  obtain ⟨C, rfl⟩ : ∃ C, C' = some C := by
    cases C' with
    | none => exact absurd hrel id
    | some C => exact ⟨C, rfl⟩
  obtain ⟨st, hseg, hst, hrun⟩ := ucont_start (o := o) S hok hrel
  let F := (outer S rs a.kind).frameAt S.f0
  have hF : F.module = S.M := top_module S hok hmain
  have hres := lpath_resume S (K := K) hF hC' htag hD hD₁ hD₂ hH hH₁ hH₂ (hf := hf) (Z := Z)
    (Y := Y) (opsF o') (hrun F (K.set k none))
  let p' : SFrame Val × Ann := ({ fr with code := c, ops := o', wait := some [⟨t, hf⟩] },
    { a with code := Y, wa := .res Z })
  have hmain' : MainOk S W (st ++ p' :: rs) :=
    mainOk_seg S hmain hst ⟨henc, hfr.2⟩ rfl (Or.inr ⟨t, hf, np, bh, Z, rfl, rfl, hh, hZ⟩)
  have hstk : top :: seg ++ p'.1 :: rs.map Prod.fst = (st ++ p' :: rs).map Prod.fst := by
    rw [List.map_append, ← hseg]
    rfl
  have hstart : fvals (opsF fr.ops) ++ adm a.code =
      fvals (opsF o' ++ [.cont k]) ++ .block btD (.block btH (bodyH S t) :: Z) :: adm Y := by
    rw [hops, hY, opsF_cons]
    rfl
  have hend : (stkCtx S (st ++ p' :: rs)).plug [] = (outer S rs a.kind).plug
      (fvals (opsF o') ++ (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug ((stkCtx S st).plug []) ++
        adm Y) := by
    rw [stkCtx_append S hst.1]
    simp only [lowsCtx, outer, plug_comp, lowCtx_plug, p']
  rw [hS, code_top]
  refine inevP_of_upath (upath_of_lpath (iso_outer S hmain) (hstart ▸ hres)) ?_
  exact ⟨rfl, rfl, Silmaril.Proofs.Wasm.Models.FXAsyncFX.forall₂_set trivial k hK, st ++ p' :: rs,
    hstk, hmain', hend.symm⟩

variable {KK : List (Option (List (SFrame Val)))} {K : List (Option ContFX)} {fr : SFrame Val}
  {a : Ann} {rs : List (SFrame Val × Ann)}

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (sexec_resume popN_zero) in
theorem umatched_resume (hS : SX S = SD o S.fx) (hok : Ok S W) (hT : Top S W KK K fr a rs)
    {t hf np : Nat} {c bh : List (Ins Val)} {Y Z : List InstrFX} {btD btH : BlockType}
    {d₁ d₂ e₁ e₂ : List Silmaril.Wasm.Validation.CValType} (hc : fr.code = .resume 0 [⟨t, hf⟩] :: c)
    (hY : a.code = .block btD (.block btH (bodyH S t) :: Z) :: Y) (htag : TagOk S t)
    (hh : W hf = some (np, bh)) (hZ : EncI S W bh Z)
    (hD : S.M.blockType? btD = some (d₁, d₂)) (hD₁ : d₁.length = 1) (hD₂ : d₂.length = 1)
    (hH : S.M.blockType? btH = some (e₁, e₂)) (hH₁ : e₁.length = 1)
    (hH₂ : e₂.length = S.ar t + 1) (henc : EncI S W c Y) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr (.resume 0 [⟨t, hf⟩]) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  obtain ⟨k, o', ho⟩ : ∃ k o', fr.ops = .cont k :: o' := by
    match hops : fr.ops with
    | .cont k :: o' => exact ⟨k, o', rfl⟩
    | [] => exact absurd (by simp only [sexec, hops]) hnt
    | .val _ :: _ => exact absurd (by simp only [sexec, hops]) hnt
  obtain ⟨top, seg, hk⟩ : ∃ top seg, KK[k]? = some (some (top :: seg)) := by
    match hkk : KK[k]? with
    | some (some (top :: seg)) => exact ⟨top, seg, rfl⟩
    | none => exact absurd (by simp only [sexec, ho, popN_zero, hkk]) hnt
    | some none => exact absurd (by simp only [sexec, ho, popN_zero, hkk]) hnt
    | some (some []) => exact absurd (by simp only [sexec, ho, popN_zero, hkk]) hnt
  rw [sexec_resume ho hk]
  exact u_resume S hS hok hT.main hT.conts ho hk hY htag hh hZ hD hD₁ hD₂ hH hH₁ hH₂ henc

/-- The top frame's next instruction is not `suspend`. -/
def CalmTop (fr : SFrame Val) : Bool :=
  match fr.code with
  | .suspend .. :: _ => false
  | _ => true

/-- **Every calm kernel step from a top frame in the fragment is matched backwards.** -/
theorem umatched_top (hS : SX S = SD o S.fx) (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (hok : Ok S W) (hT : Top S W KK K fr a rs)
    (hcalm : CalmTop fr = true) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have henc : EncI S W fr.code a.code := (hT.main.1 _ (List.mem_cons_self ..)).1
  generalize hc : fr.code = code at henc
  generalize hY : a.code = Y at henc
  cases henc with
  | nil => exact umatched_nil S hS hT hc
  | push hv h => exact umatched_push S hS hT hc hY hv h
  | prim hi h => exact umatched_prim S hS hP hH hok hT hc hY hi h
  | drop h => exact umatched_drop S hS hT hc hY h
  | call h => exact umatched_call S hS hok hT hc hY h
  | cond hf hg hbt ht h => exact umatched_cond S hS hok hT hc hY hf hg hbt ht h
  | contNew hf h => exact umatched_contNew S hS hok hT hc hY hf h
  | resume htag hh hZ hD hD₁ hD₂ hH hH₁ hH₂ h =>
    exact umatched_resume S hS hok hT hc hY htag hh hZ hD hD₁ hD₂ hH hH₁ hH₂ h
  | suspend => simp [CalmTop, hc] at hcalm

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
