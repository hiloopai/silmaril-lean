module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.Normal

/-!
# The simulation with in-bounds target runs: calls, suspensions, all cases, and `Task.fits`

The remaining cases of `SimSafe`: a call of a defined function (normal mode, no access), and a
suspension, where the target writes the request below `SB`, saves one record per source frame
at `SB, SB + 4F, …` and rewinds the chain: every access ends at or below
`SB + 4 F · depth`, which `FitsIn` bounds by `cap`. `simSafe_of_rel`: every related pair whose
source fits satisfies `SimSafe`. `safe_of_rel`: the target run from a related pair never accesses
memory past `cap` (by induction on the number of target steps and, for stuttering steps, on
the measure). `asyncify_fits`: the same from the initial states.

New proofs (the cases of `Call`, `SuspendSim` and `Main`, with `SafeT` added).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

theorem steps_guard_takenS {cap : Nat} {E : Env} {fr : Frame} {rest : List Frame} {g : List W}
    {m : Nat → W} {seg t K : List Instr} {x : W} {ops : List W} {ls : List W}
    (h : runSeg seg ⟨fr.locals, fr.ops, g, m⟩ = some ⟨ls, x :: ops, g, m⟩) (hx : x ≠ 0)
    (hfree : ∀ i ∈ seg, AccFree i) :
    StepsS cap E (seg.length + 1) ⟨{ fr with code := seg ++ ifThen t :: K } :: rest, g, m⟩
      ⟨{ fr with locals := ls, ops := ops, code := t ++ K } :: rest, g, m⟩ := by
  have h1 := steps_guardS (cap := cap) (E := E) (rest := rest) (t := t) (K := K) h hfree
  rwa [ite_eq_right hx] at h1

/-- The target side of a call statement to a defined function, in bounds (`tgt_call_def`). -/
theorem tgt_call_defS {cap : Nat} {P : Prog} {fid k : Nat} {fn fn' : FnSrc} {tl : List W}
    {tw : List Frame} {tm : Nat → W} {f : FuncIdx} {as rs : List LocalIdx} {K0 : List Instr}
    (htl : tl.length = P.frameWords) (hF : 1 ≤ P.frameWords) (hF2 : P.frameWords < 2 ^ 32)
    (hasl : ∀ a ∈ as, a.value.val < tl.length) (himp : ¬ f.value.val < P.imps.length)
    (hfn' : P.fnAt f.value.val = some fn') (hnp : fn'.nparams = as.length) :
    StepsS cap (asyncifyProg P) ((7 + 1) + (as.length + (1 + (3 + 1))))
      ⟨⟨fid, tl, [], trStmt (P.ctx fn) k (.call f as rs) ++ K0, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨f.value.val, as.map (lv tl) ++ List.replicate (P.frameWords - fn'.nparams) 0, [],
        trS (P.ctx fn') 0 fn'.stmts ++ fn'.tail, fn'.nres⟩ ::
        ⟨fid, tl, [], chk P.frameWords k fn.nres ++ setsCode rs ++ K0, fn.nres⟩ :: tw,
        P.tGlobals, tm⟩ := by
  obtain ⟨x, hx0, hseg⟩ := seg_site_normal P tl tm k (by omega) hF2
  let K := chk P.frameWords k fn.nres ++ setsCode rs ++ K0
  have m1 : StepsS cap (asyncifyProg P) (7 + 1)
      ⟨⟨fid, tl, [], trStmt (P.ctx fn) k (.call f as rs) ++ K0, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, [], getsCode as ++ .call f :: K, fn.nres⟩ :: tw, P.tGlobals, tm⟩ := by
    have e1 := steps_guard_takenS (cap := cap) (E := asyncifyProg P)
      (fr := ⟨fid, tl, [], [], fn.nres⟩) (rest := tw)
      (t := getsCode as ++ [.call f] ++ chk P.frameWords k fn.nres ++ setsCode rs)
      (K := K0) hseg hx0 (accFree_site P.frameWords k)
    simpa [trStmt, Prog.ctx, himp, K, List.append_assoc] using e1
  have hgets : ∀ i ∈ getsCode as, AccFree i := by
    intro i hi
    simp only [getsCode, List.mem_map] at hi
    obtain ⟨b, -, rfl⟩ := hi
    exact accFree_get b
  have m2 : StepsS cap (asyncifyProg P) as.length
      ⟨⟨fid, tl, [], getsCode as ++ .call f :: K, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, (as.map (lv tl)).reverse, .call f :: K, fn.nres⟩ :: tw, P.tGlobals, tm⟩ := by
    have e2 := steps_segS (cap := cap) (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩)
      (rest := tw) (code := .call f :: K)
      (getsCode_seg (gs := P.tGlobals) (mem := tm) (ops := []) hasl) (segSafe_free hgets)
    simpa [getsCode] using e2
  let d : FnDef := ⟨fn'.nparams, P.frameWords - fn'.nparams, fn'.nres, P.tBody fn'⟩
  let c3 : Cfg := ⟨⟨fid, tl, (as.map (lv tl)).reverse, .call f :: K, fn.nres⟩ :: tw, P.tGlobals, tm⟩
  have e3 : step (asyncifyProg P) c3 = .next ⟨entry f.value.val d (as.map (lv tl)) ::
        ⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals, tm⟩ :=
    step_call_args (E := asyncifyProg P)
      (fr := ⟨fid, tl, (as.map (lv tl)).reverse, .call f :: K, fn.nres⟩) (args := as.map (lv tl))
      (low := []) rfl rfl (by simp) (by simpa [asyncifyProg] using himp)
      (by simpa using Prog.tgt_fn hfn') (by simp [d, hnp])
  have ho3 : ¬ OOB cap c3 := not_oob_free (c := c3) rfl rfl (accFree_call f)
  have m4 : StepsS cap (asyncifyProg P) (3 + 1)
      ⟨entry f.value.val d (as.map (lv tl)) :: ⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨f.value.val, as.map (lv tl) ++ List.replicate (P.frameWords - fn'.nparams) 0, [],
        trS (P.ctx fn') 0 fn'.stmts ++ fn'.tail, fn'.nres⟩ :: ⟨fid, tl, [], K, fn.nres⟩ :: tw,
        P.tGlobals, tm⟩ := by
    have e4 := steps_guardS (cap := cap) (E := asyncifyProg P)
      (fr := entry f.value.val d (as.map (lv tl))) (rest := ⟨fid, tl, [], K, fn.nres⟩ :: tw)
      (t := restoreCode P.frameWords) (K := trS (P.ctx fn') 0 fn'.stmts ++ fn'.tail)
      (seg_prologue_normal P _ tm) (accFree_guard 2 .eq)
    simpa [entry, d, Prog.tBody, prologue, ifThen] using e4
  exact m1.trans (m2.trans ((StepsS.one ho3 e3).trans m4))

/-- A call statement to a defined function, after its arguments are read. -/
theorem sim_callS {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt}
    {f : FuncIdx} {as rs : List LocalIdx} (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
      .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : P.imps.length ≤ f.value.val) : SimSafe cap P H (c, s) t := by
  have hok : FnOk P fn := Prog.fnOk hR.wf hfn
  obtain ⟨hsig, has, -⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  obtain ⟨fn', hfn', hnp, -⟩ := Prog.sig_fn hsig hf
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  have hF2 : P.frameWords < 2 ^ 32 := by have := (Prog.wf_bounds hR.wf).2; omega
  have hasl : ∀ a ∈ as, a.value.val < tl.length := fun a ha => by
    have := has a ha; have := hok.nloc; omega
  have hargs : as.map (lv tl) = as.map (lv sl) :=
    List.map_congr_left fun a ha => hloc.lv (has a ha)
  have hsrc := src_call_def (H := H) (s := s) hcs hf hfn' hnp
  have htgt := tgt_call_defS (cap := cap) (fid := fid) (k := pre.length) (fn := fn) (tw := tw)
    (tm := t.cfg.mem) (rs := rs) (K0 := trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail) htl
    (by have := hok.nloc; omega) hF2 hasl (Nat.not_lt.2 hf) hfn' hnp
  have hcfg : t.cfg = ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      (trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail), fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by
    rw [← List.append_assoc, ← hct, ← hR.globals]
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  have hw : WaitR P f.value.val pre.length ⟨fid, sl, [], setsCode rs ++ flatS rest ++ fn.tail,
      fn.nres⟩ ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++ setsCode rs ++
        (trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail), fn.nres⟩ := by
    simpa only [List.append_assoc] using WaitR.mk hfn hloc hst hf
  refine ⟨_, _, htgt.steps.tgt_of hcfg, ?_, Or.inl (by omega), htgt.safeT hcfg⟩
  exact ⟨hR.wf, hR.host, ⟨_, _, _, _, _, rfl, rfl, TopR.ofEntry hR.wf hfn' hargs (by simp [hnp]),
    .cons hw hch⟩, rfl, hR.entry, hR.bound.next hsrc⟩

/-- After the host's answer the target rewinds the whole chain in bounds (`rewind_after`). -/
theorem rewind_afterS {P : Prog} (hP : P.WF) {cap : Nat} {fid e : Nat} {fn fnE : FnSrc}
    {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} {ks : List Nat}
    {sw tw : List Frame} {tl : List W} {tm : Nat → W} {args ta ws : List W}
    (hch : Chain P fid e ks sw tw)
    (hfn : P.fnAt fid = some fn) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : f.value.val < P.imps.length) (htl : tl.length = P.frameWords)
    (hlocs : ∀ w ∈ tw, w.locals.length = P.frameWords) (hm : 4 * ws.length ≤ P.sb)
    (hws : ws.length = rs.length) (hbd : P.sb + 4 * P.frameWords * (tw.length + 1) < 2 ^ 32)
    (hcap : P.sb + 4 * P.frameWords * (tw.length + 1) ≤ cap)
    (hfnE : P.fnAt e = some fnE) (hargsE : ta.length = fnE.nparams) :
    ∃ nR, StepsS cap (asyncifyProg P) nR
      ⟨[entry e (tdef P fnE) ta], [2, BitVec.ofNat 32 (P.sb + 4 * P.frameWords +
        4 * P.frameWords * tw.length)],
        writeWords (unwMem P tm f.value.val args (recOf P.frameWords pre.length tl) ks tw) 0 ws⟩
      ⟨⟨fid, recOf P.frameWords pre.length tl, ws.reverse,
        setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ ::
        (restore P.frameWords ks tw ++ []), [0, BitVec.ofNat 32 P.sb],
        writeWords (unwMem P tm f.value.val args (recOf P.frameWords pre.length tl) ks tw) 0 ws⟩ := by
  have hF : 1 ≤ P.frameWords := by have := (Prog.fnOk hP hfn).nloc; omega
  let r := recOf P.frameWords pre.length tl
  let memU := unwMem P tm f.value.val args r ks tw
  let M := writeWords memU 0 ws
  have hMhi : ∀ x, P.sb ≤ x → M x = memU x := fun x hx => writeWords_ge (by omega)
  have hrecsM : RecsAt P.frameWords M (P.sb + 4 * P.frameWords) ks tw :=
    recsAt_mono (fun x hx => hMhi x (by omega)) (recsAt_writeRecs hF hlocs)
  have hrec0 : readWords M P.sb P.frameWords = r :=
    calc readWords M P.sb P.frameWords
        = readWords (writeWords (reqMem tm f.value.val args) P.sb r) P.sb P.frameWords :=
          readWords_congr fun j hj => by rw [hMhi _ (by omega)]; exact writeRecs_lt (by omega)
      _ = readWords (writeWords (reqMem tm f.value.val args) P.sb r) P.sb r.length := by
          rw [recOf_length htl hF]
      _ = r := readWords_writeWords
  have hans : readWords M 0 rs.length = ws :=
    calc readWords M 0 rs.length = readWords M 0 ws.length := by rw [hws]
      _ = ws := readWords_writeWords
  have hle1 : P.sb + 4 * P.frameWords ≤ P.sb + 4 * P.frameWords * (tw.length + 1) :=
    addr_le P.sb P.frameWords tw.length
  have hchain := rewinds_chainS hP (cap := cap) hch hfn
    (rewinds_baseS hP hfn hst hf htl hrec0 (by omega)) hrecsM
    (by have := addr_step P.sb P.frameWords tw.length; omega)
    (by have := addr_step P.sb P.frameWords tw.length; omega) fnE hfnE
  obtain ⟨nR, eR⟩ := hchain [] ta hargsE
  exact ⟨nR, by simpa only [hans] using eR⟩

/-- A call statement to an import, after its arguments are read: the suspension stays in bounds
when the source frames fit. -/
theorem sim_impS {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt}
    {f : FuncIdx} {as rs : List LocalIdx} (hR : Rel P H (c, s) t)
    (hfit : P.sb + 4 * P.frameWords * c.frames.length ≤ cap)
    (hcs : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
      .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : f.value.val < P.imps.length) : SimSafe cap P H (c, s) t := by
  have hP : P.WF := hR.wf
  have hok : FnOk P fn := Prog.fnOk hP hfn
  obtain ⟨hsig, has, hrs⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  have himpf : P.imps[f.value.val] = (as.length, rs.length) := Prog.sig_imp hsig hf
  obtain ⟨hreq1, hreq2⟩ := Prog.imp_le (List.mem_of_getElem himpf)
  have hb1 : P.imps.length + P.fns.length < 2 ^ 31 := (Prog.wf_bounds hP).1
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  obtain ⟨hlen, hlocs⟩ := hch.len hP
  have hl : c.frames.length = tw.length + 1 := by rw [hcs, List.length_cons, hlen]
  have hbd : P.sb + 4 * P.frameWords * (tw.length + 1) < 2 ^ 32 := by
    rw [← hl]; exact hR.bound.now
  have hcap : P.sb + 4 * P.frameWords * (tw.length + 1) ≤ cap := by rw [← hl]; exact hfit
  have hargs : as.map (lv tl) = as.map (lv sl) := List.map_congr_left fun a ha => hloc.lv (has a ha)
  have hsrc := src_imp (H := H) (s := s) hcs hf himpf
  have hcfg : t.cfg = ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by
    rw [← hct, ← hR.globals]
  obtain ⟨nU, cU, vs, eU, hoU, hdone⟩ := tgt_imp_unwindS (cap := cap) (sl := sl) (tm := t.cfg.mem)
    hP hch hfn hloc hst hf hbd hcap
  obtain ⟨fnE, hfnE, hargsE⟩ := hR.entry
  obtain ⟨hf0, hrd⟩ := unwMem_request (P := P) (m := t.cfg.mem) (args := as.map (lv tl))
    (r := recOf P.frameWords pre.length tl) (ks := ks) (tw := tw)
    (by simp [Prog.sb]; omega) (show f.value.val < 2 ^ 32 by omega)
  let ans := H.answer s f.value.val (as.map (lv sl))
  have hfitlen : (fit rs.length ans.2).length = rs.length := by simp [fit]
  have hsb : P.sb = 4 * P.reqWords := rfl
  have hhost := host_resume (H := H) (th := s) (ta := t.args) (n := as.length) (m := rs.length)
    (args := as.map (lv sl)) hdone hf0 (by simpa [hargs] using hrd)
    (by simp [List.getElem?_eq_getElem hf, himpf]) hfnE
  obtain ⟨nR, eR⟩ := rewind_afterS (cap := cap) (args := as.map (lv tl))
    (ws := fit rs.length ans.2) (tm := t.cfg.mem) (rs := rs) hP hch hfn hst hf htl hlocs
    (by rw [hfitlen]; omega) hfitlen hbd hcap hfnE hargsE
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  let M := writeWords (unwMem P t.cfg.mem f.value.val (as.map (lv tl))
    (recOf P.frameWords pre.length tl) ks tw) 0 (fit rs.length ans.2)
  let tU : TSt σ := { t with cfg := cU }
  let tH : TSt σ := ⟨⟨[entry t.fid (tdef P fnE) t.args], [2, BitVec.ofNat 32 (P.sb + 4 * P.frameWords +
    4 * P.frameWords * tw.length)], M⟩, ans.1, t.fid, t.args⟩
  have rU : runN (tgtStep (asyncifyProg P) H) nU t = .next tU := eU.steps.tgt_of hcfg
  have rH : runN (tgtStep (asyncifyProg P) H) 1 tU = .next tH := by
    simp only [runN, tU, hR.host]
    rw [hhost]
  have sU : SafeT cap (asyncifyProg P) H nU t := eU.safeT hcfg
  have sH : SafeT cap (asyncifyProg P) H 1 tU := SafeT.one hoU
  have sR : SafeT cap (asyncifyProg P) H nR tH := eR.safeT rfl
  refine ⟨nU + (1 + nR), ⟨⟨⟨fid, recOf P.frameWords pre.length tl, (fit rs.length ans.2).reverse,
    setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ ::
    (restore P.frameWords ks tw ++ []), [0, BitVec.ofNat 32 P.sb], M⟩, ans.1, t.fid, t.args⟩,
    ?_, ?_, Or.inl (by omega), SafeT.trans rU sU (SafeT.trans rH sH sR)⟩
  · show runN (tgtStep (asyncifyProg P) H) (nU + (1 + nR)) t = _
    rw [runN_add_next rU, runN_add_next rH]
    exact eR.steps.tgt ans.1 t.fid t.args
  · show Rel P H _ _
    have hT := TopR.mk (ops := (fit rs.length ans.2).reverse) (p := setsCode rs)
      (pre := pre ++ [Stmt.call f as rs]) (rest := rest) hP hfn (hloc.recOf pre.length hok.nloc)
      (by rw [hst]; simp) (setsCode_pure hrs)
      (by rw [List.length_reverse, hfitlen]; simpa using depthAfter_sets rs 0)
    refine ⟨hP, rfl, ⟨_, _, sw, _, ks, rfl, rfl, by simpa [pushTop, ans] using hT,
      by simpa using hch.restore⟩, rfl, ⟨fnE, hfnE, hargsE⟩, hR.bound.next hsrc⟩

/-- A call statement, while or after its arguments are read. -/
theorem sim_preS {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt}
    {f : FuncIdx} {as rs : List LocalIdx} {j : Nat} (hR : Rel P H (c, s) t)
    (hfit : P.sb + 4 * P.frameWords * c.frames.length ≤ cap)
    (hcs : c.frames = ⟨fid, sl, ((as.take j).map (lv sl)).reverse,
      (getsCode as).drop j ++ [.call f] ++ setsCode rs ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hj : j ≤ as.length) : SimSafe cap P H (c, s) t := by
  rcases Nat.lt_or_ge j as.length with hlt | hge
  · exact sim_getS hR hcs hct hch hfn hloc hst hlt
  · have hj' : j = as.length := by omega
    subst hj'
    have hd : (getsCode as).drop as.length = [] := List.drop_eq_nil_of_le (by simp [getsCode])
    rw [hd, List.take_length] at hcs
    have hcs' : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
        .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw := by
      rw [hcs]; simp
    by_cases hf : f.value.val < P.imps.length
    · exact sim_impS hR hfit hcs' hct hch hfn hloc hst hf
    · exact sim_callS hR hcs' hct hch hfn hloc hst (by omega)

/-- A pure statement opens: the target passes its guard (normal mode), then both run it. -/
theorem sim_open_pureS {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre r : List Stmt}
    {i : Instr} {is : List Instr}
    (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, [], [] ++ flatS (Stmt.pure (i :: is) :: r) ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length (Stmt.pure (i :: is) :: r) ++
      fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.pure (i :: is) :: r) :
    SimSafe cap P H (c, s) t := by
  obtain ⟨-, hpure, hdep⟩ :=
    Stmt.wf_pure ((Prog.fnOk hR.wf hfn).stmts (Stmt.pure (i :: is)) (by rw [hst]; simp))
  let pre' := pre ++ [Stmt.pure (i :: is)]
  let K := (i :: is) ++ trS (P.ctx fn) pre'.length r ++ fn.tail
  have e : StepsS cap (asyncifyProg P) (3 + 1) ⟨⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length
      (Stmt.pure (i :: is) :: r) ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩
      ⟨⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by
    have e1 := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩)
      (rest := tw) (t := i :: is) (e := []) (K := trS (P.ctx fn) (pre.length + 1) r ++ fn.tail)
      (seg_guard_ne P tl [] t.cfg.mem) (accFree_guard 2 .ne)
    simpa [trS, trStmt, ifThen, K, pre', List.append_assoc] using e1
  have hcfg : t.cfg = ⟨⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length (Stmt.pure (i :: is) :: r) ++
      fn.tail, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by rw [← hct, ← hR.globals]
  have hcs' : c.frames = ⟨fid, sl, [], (i :: is) ++ flatS r ++ fn.tail, fn.nres⟩ :: sw := by
    rw [hcs]; simp [flatS, Stmt.code]
  have hst' : fn.stmts = pre' ++ r := by rw [hst]; simp [pre']
  have hd : depthAfter (i :: is) ([] : List W).length = some 0 := by simpa using hdep
  have hR' : Rel P H (c, s) { t with cfg := ⟨⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals,
      t.cfg.mem⟩ } :=
    ⟨hR.wf, hR.host, ⟨_, _, sw, tw, ks, hcs', rfl, TopR.mk hR.wf hfn hloc hst' hpure hd, hch⟩, rfl,
      hR.entry, hR.bound⟩
  exact SimSafe.pre (e.steps.tgt_of hcfg) (e.safeT hcfg)
    (sim_runS hR' hcs' rfl hch hfn hloc hst' hpure hd)

/-- A top frame at the start of a statement (no pure code pending). -/
theorem sim_stmtS {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre r : List Stmt} {st : Stmt}
    (hR : Rel P H (c, s) t) (hfit : P.sb + 4 * P.frameWords * c.frames.length ≤ cap)
    (hcs : c.frames = ⟨fid, sl, [], [] ++ flatS (st :: r) ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], [] ++ trS (P.ctx fn) pre.length (st :: r) ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ st :: r) : SimSafe cap P H (c, s) t := by
  cases st with
  | pure is =>
    cases is with
    | nil =>
      exact absurd rfl (Stmt.wf_pure ((Prog.fnOk hR.wf hfn).stmts (Stmt.pure [])
        (by rw [hst]; simp))).1
    | cons i is => exact sim_open_pureS hR hcs hct hch hfn hloc hst
  | call f as rs =>
    exact sim_preS (j := 0) hR hfit (by rw [hcs]; simp [flatS, Stmt.code, getsCode])
      (by rw [hct]; simp [trS]) hch hfn hloc hst (Nat.zero_le _)

/-- A top frame inside a pure statement or at the start of one. -/
theorem sim_top_runS {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {p : List Instr}
    {pre rest : List Stmt}
    (hR : Rel P H (c, s) t) (hfit : P.sb + 4 * P.frameWords * c.frames.length ≤ cap)
    (hcs : c.frames = ⟨fid, sl, ops, p ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, p ++ trS (P.ctx fn) pre.length rest ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ rest) (hrest : rest ≠ [])
    (hp : ∀ i ∈ p, pureIns fn.nloc i = true) (hd : depthAfter p ops.length = some 0) :
    SimSafe cap P H (c, s) t := by
  cases p with
  | cons i p => exact sim_runS hR hcs hct hch hfn hloc hst hp hd
  | nil =>
    have hops : ops = [] := List.eq_nil_of_length_eq_zero (by simpa [depthAfter] using hd)
    cases rest with
    | nil => exact absurd rfl hrest
    | cons st r =>
      exact sim_stmtS hR hfit (by rw [hcs, hops]) (by rw [hct, hops]) hch hfn hloc hst

/-- Every related pair whose source frames fit satisfies the in-bounds obligation. -/
theorem simSafe_of_rel {cap : Nat} {P : Prog} {H : Host σ} {x : Cfg × σ} {t : TSt σ}
    (hR : Rel P H x t) (hfit : FitsIn cap P H x) : SimSafe cap P H x t := by
  obtain ⟨c, s⟩ := x
  have hnow : P.sb + 4 * P.frameWords * c.frames.length ≤ cap := hfit.now
  obtain ⟨s0, t0, sw, tw, ks, hcs, hct, htop, hch⟩ := hR.frames
  cases htop with
  | run hfn hloc hst hrest hp hd => exact sim_top_runS hR hnow hcs hct hch hfn hloc hst hrest hp hd
  | @fin _ _ _ _ _ q hfn hloc hq hd =>
    cases q with
    | nil => exact sim_retS hR hcs hct hch hfn hd
    | cons i q => exact sim_finS hR hcs hct hch hfn hloc hq hd
  | pre hfn hloc hst hj => exact sim_preS hR hnow hcs hct hch hfn hloc hst hj

/-- One case of `safe_of_rel`: the target state `y` after `N` steps from a related pair is in
bounds, given the claim for fewer steps and, at the same `N`, for source states of smaller
measure. -/
theorem safe_split {cap : Nat} {P : Prog} {H : Host σ} {N : Nat} {x : Cfg × σ} {t : TSt σ}
    {y : TSt σ} (hok : SimSafe cap P H x t) (hfit : FitsIn cap P H x)
    (hy : runN (tgtStep (asyncifyProg P) H) N t = .next y)
    (ihN : ∀ M < N, ∀ (x' : Cfg × σ) (t' : TSt σ), Rel P H x' t' → FitsIn cap P H x' →
      ∀ y', runN (tgtStep (asyncifyProg P) H) M t' = .next y' → ¬ OOB cap y'.cfg)
    (ihk : ∀ (x' : Cfg × σ) (t' : TSt σ), mu x' < mu x → Rel P H x' t' → FitsIn cap P H x' →
      ∀ y', runN (tgtStep (asyncifyProg P) H) N t' = .next y' → ¬ OOB cap y'.cfg) :
    ¬ OOB cap y.cfg := by
  cases hsx : srcStep P.env H x with
  | stop o =>
    show ¬ OOB cap y.cfg
    obtain ⟨n, hn, hs⟩ := hok.1 o hsx
    by_cases hNn : N < n
    · exact hs N hNn y hy
    · have hstop : runN (tgtStep (asyncifyProg P) H) N t = .stop o :=
        runN_stop_mono hn (by omega)
      cases hy.symm.trans hstop
  | next x' =>
    show ¬ OOB cap y.cfg
    obtain ⟨n, t', hn, hR', hd, hs⟩ := hok.2 x' hsx
    have hfit' : FitsIn cap P H x' := hfit.next hsx
    by_cases hNn : N < n
    · exact hs N hNn y hy
    · have hy' : runN (tgtStep (asyncifyProg P) H) (N - n) t' = .next y := by
        have hsplit : N = n + (N - n) := by omega
        rw [hsplit, runN_add_next hn] at hy; exact hy
      by_cases hn0 : 0 < n
      · exact ihN (N - n) (by omega) x' t' hR' hfit' y hy'
      · have hmu : mu x' < mu x := by omega
        have hNeq : N - n = N := by omega
        exact ihk x' t' hmu hR' hfit' y (hNeq ▸ hy')

/-- **In bounds from a related pair**: if the source fits its frames into `cap` bytes, no state
of the target run accesses memory past `cap`. -/
theorem safe_of_rel {cap : Nat} {P : Prog} {H : Host σ} (N : Nat) :
    ∀ (k : Nat) (x : Cfg × σ) (t : TSt σ), mu x = k → Rel P H x t → FitsIn cap P H x →
      ∀ y, runN (tgtStep (asyncifyProg P) H) N t = .next y → ¬ OOB cap y.cfg := by
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro x t hk hR hfit y hy
      exact safe_split (simSafe_of_rel hR hfit) hfit hy
        (fun M hM x' t' hR' hfit' y' hy' => ihN M hM (mu x') x' t' rfl hR' hfit' y' hy')
        (fun x' t' hmu hR' hfit' y' hy' => ihk (mu x') (hk ▸ hmu) x' t' rfl hR' hfit' y' hy')

/-- **The asyncified program stays in bounds**: for a well-formed program, a call within
`DepthBound` whose source states all fit their frames into `cap` bytes, the target run never
accesses memory past `cap`. -/
theorem asyncify_fits_safe (P : Prog) (hP : P.WF) (H : Host σ) (cap : Nat) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (s : σ)
    (hbound : DepthBound P H (srcCfg e fn args, s)) (hfit : FitsIn cap P H (srcCfg e fn args, s)) :
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg) (tgtSt P e fn args s) := by
  let t1 : TSt σ := ⟨⟨[⟨e, args ++ List.replicate (P.frameWords - fn.nparams) 0, [],
    trS (P.ctx fn) 0 fn.stmts ++ fn.tail, fn.nres⟩], P.tGlobals, fun _ => 0⟩, s, e, args⟩
  have e1 : StepsS cap (asyncifyProg P) (3 + 1) ⟨[entry e (tdef P fn) args], P.tGlobals, fun _ => 0⟩
      t1.cfg := by
    have h := steps_guardS (cap := cap) (E := asyncifyProg P) (fr := ⟨e, args ++
      List.replicate (P.frameWords - fn.nparams) 0, [], [], fn.nres⟩) (rest := [])
      (t := restoreCode P.frameWords) (K := trS (P.ctx fn) 0 fn.stmts ++ fn.tail)
      (seg_prologue_normal P _ (fun _ => 0)) (accFree_guard 2 .eq)
    simpa [entry, tdef, Prog.tBody, prologue, ifThen, List.append_assoc, t1] using h
  have r1 : runN (tgtStep (asyncifyProg P) H) (3 + 1) (tgtSt P e fn args s) = .next t1 :=
    e1.steps.tgt_of rfl
  have s1 : SafeT cap (asyncifyProg P) H (3 + 1) (tgtSt P e fn args s) := e1.safeT rfl
  have hR : Rel P H (srcCfg e fn args, s) t1 := ⟨hP, rfl, ⟨_, _, [], [], [], rfl, rfl,
    TopR.ofEntry hP hfn rfl hargs, .nil e⟩, rfl, ⟨fn, hfn, hargs⟩, hbound⟩
  intro n y hy
  by_cases hn : n < 3 + 1
  · exact s1 n hn y hy
  · have hsplit : n = (3 + 1) + (n - (3 + 1)) := by omega
    have hy' : runN (tgtStep (asyncifyProg P) H) (n - (3 + 1)) t1 = .next y := by
      rw [hsplit, runN_add_next r1] at hy; exact hy
    exact safe_of_rel (n - (3 + 1)) _ _ t1 rfl hR hfit y hy'

end Silmaril.Wasm.FX.Asyncify.Tool
