module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Suspend

/-!
# The simulation of a suspension

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/SuspendSim.lean` and restyled: `sim_imp`
is split into its phases, the source step `src_imp`, the unwinding `tgt_imp_unwind`, the host's
answer `host_resume`, the memory facts about `unwMem` and the rewinding `rewind_after`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- The memory after the request of import `f` with arguments `args`. -/
def reqMem (m : Nat → W) (f : Nat) (args : List W) : Nat → W :=
  writeWords (upd m 0 (BitVec.ofNat 32 f)) 4 args

/-- The memory after a suspension has unwound: the request, the record `r` of the suspending
frame at `SB`, and the records of the waiting frames above it. -/
def unwMem (P : Prog) (m : Nat → W) (f : Nat) (args r : List W) (ks : List Nat)
    (tw : List Frame) : Nat → W :=
  writeRecs P.frameWords (writeWords (reqMem m f args) P.sb r) (P.sb + 4 * P.frameWords)
    (recs P.frameWords ks tw)

theorem seg_req {tl ops : List W} {g0 sp : W} {mem : Nat → W} {f : FuncIdx} {as : List LocalIdx}
    (has : ∀ a ∈ as, a.value.val < tl.length) (hn : 4 * (1 + as.length) < 2 ^ 32) :
    runSeg (reqCode f as ++ [c32 1, sState]) ⟨tl, ops, [g0, sp], mem⟩ =
      some ⟨tl, ops, [1, sp], reqMem mem f.value.val (as.map (lv tl))⟩ := by
  unfold reqCode
  rw [runSeg_append, runSeg_append]
  have h1 : runSeg [c32 0, c32 f.value.val, st 0] ⟨tl, ops, [g0, sp], mem⟩ =
      some ⟨tl, ops, [g0, sp], upd mem 0 (BitVec.ofNat 32 f.value.val)⟩ := by
    simp [runSeg, segStep, ctlOf, segCore, c32, st, pexec, marg_off (show 0 < 2 ^ 64 by omega)]
  rw [h1, Option.bind_some, reqArgs_seg (j := 1) (by omega) has, Option.bind_some]
  rfl

theorem unwMem_low {P : Prog} {m : Nat → W} {f : Nat} {args r : List W} {ks : List Nat}
    {tw : List Frame} {x : Nat} (hx : x < P.sb) :
    unwMem P m f args r ks tw x = reqMem m f args x := by
  unfold unwMem
  rw [writeRecs_lt (by omega), writeWords_lt hx]

theorem reqMem_zero {m : Nat → W} {f : Nat} {args : List W} :
    reqMem m f args 0 = BitVec.ofNat 32 f := by
  unfold reqMem
  rw [writeWords_lt (by omega)]
  simp [upd]

theorem reqMem_args {m : Nat → W} {f : Nat} {args : List W} :
    (List.range args.length).map (fun i => reqMem m f args (4 * (i + 1))) = args := by
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [List.getElem_map, List.getElem_range, reqMem]
  rw [show 4 * (i + 1) = 4 + 4 * i by omega, writeWords_at (by simpa using h1)]

/-- The host reads the request below `SB`: the import index, then the arguments. -/
theorem unwMem_request {P : Prog} {m : Nat → W} {f : Nat} {args r : List W} {ks : List Nat}
    {tw : List Frame} (hlo : 4 * (args.length + 1) ≤ P.sb) (hf : f < 2 ^ 32) :
    (unwMem P m f args r ks tw 0).toNat = f ∧
      (List.range args.length).map (fun i => unwMem P m f args r ks tw (4 * (i + 1))) = args := by
  refine ⟨by rw [unwMem_low (by omega), reqMem_zero]; exact toNat_ofNat32 hf, ?_⟩
  calc (List.range args.length).map (fun i => unwMem P m f args r ks tw (4 * (i + 1)))
      = (List.range args.length).map (fun i => reqMem m f args (4 * (i + 1))) :=
        List.map_congr_left fun i hi => unwMem_low (by simp at hi; omega)
    _ = args := reqMem_args

/-- The source side of an import call: the host answers. -/
theorem src_imp {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {sw : List Frame} {fid : Nat}
    {fn : FnSrc} {sl : List W} {f : FuncIdx} {as : List LocalIdx} {K : List Instr} {m : Nat}
    (hcs : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse, .call f :: K, fn.nres⟩ :: sw)
    (hf : f.value.val < P.imps.length) (himpf : P.imps[f.value.val] = (as.length, m)) :
    srcStep P.env H (c, s) = .next (pushTop ⟨⟨fid, sl, [], K, fn.nres⟩ :: sw, c.globals, c.mem⟩
      (fit m (H.answer s f.value.val (as.map (lv sl))).2).reverse,
      (H.answer s f.value.val (as.map (lv sl))).1) := by
  have hfE : f.value.val < P.env.imps.length := hf
  have himpE : P.env.imps[f.value.val]'hfE = (as.length, m) := himpf
  have hs : step P.env c = .ask f.value.val (as.map (lv sl))
      ⟨⟨fid, sl, [], K, fn.nres⟩ :: sw, c.globals, c.mem⟩ := by
    have htk : (as.map (lv sl)).reverse.take as.length = (as.map (lv sl)).reverse :=
      List.take_of_length_le (by simp)
    have hdr : (as.map (lv sl)).reverse.drop as.length = [] := List.drop_eq_nil_of_le (by simp)
    rw [step_call_imp (E := P.env) hcs rfl hfE (by rw [himpE]; simp), himpE]
    simp [htk, hdr]
  have hm : ((P.env.imps[f.value.val]?).map Prod.snd).getD 0 = m := by
    simp [Prog.env, List.getElem?_eq_getElem hf, himpf]
  simp only [srcStep, hs, hm]

/-- The target at an import site in normal mode: it writes the request, sets `state := 1`, saves
the frame at `SB` and unwinds the waiting frames. -/
theorem tgt_imp_unwind {P : Prog} (hP : P.WF) {fid e : Nat} {fn : FnSrc} {sl tl : List W}
    {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} {ks : List Nat}
    {sw tw : List Frame} {tm : Nat → W} (hch : Chain P fid e ks sw tw)
    (hfn : P.fnAt fid = some fn) (hloc : LocR P fn sl tl)
    (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest) (hf : f.value.val < P.imps.length)
    (hbd : P.sb + 4 * P.frameWords * (tw.length + 1) < 2 ^ 32) :
    ∃ n cU vs, Steps (asyncifyProg P) n
      ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
        trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, tm⟩ cU ∧
      step (asyncifyProg P) cU = .done vs ⟨[], [1, BitVec.ofNat 32 (P.sb + 4 * P.frameWords +
        4 * P.frameWords * tw.length)], unwMem P tm f.value.val (as.map (lv tl))
          (recOf P.frameWords pre.length tl) ks tw⟩ := by
  have hok : FnOk P fn := Prog.fnOk hP hfn
  obtain ⟨hsig, has, -⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  have hreq : as.length + 1 ≤ P.reqWords :=
    (Prog.imp_le (List.mem_of_getElem (Prog.sig_imp hsig hf))).1
  have hb2 : 4 * P.frameWords + 4 * P.reqWords < 2 ^ 24 := (Prog.wf_bounds hP).2
  have hF : 1 ≤ P.frameWords := by have := hok.nloc; omega
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  have hk : pre.length < 2 ^ 32 := by have := hok.pre_lt hst; omega
  have hsb : P.sb = 4 * P.reqWords := rfl
  have hasl : ∀ a ∈ as, a.value.val < tl.length := fun a ha => by
    have := has a ha; have := hok.nloc; omega
  let K' := trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail
  let save := reqCode f as ++ [c32 1, sState] ++ saveCode P.frameWords pre.length ++
    dummies fn.nres
  let mem2 := writeWords (reqMem tm f.value.val (as.map (lv tl))) P.sb
    (recOf P.frameWords pre.length tl)
  have m1 : Steps (asyncifyProg P) (3 + 1)
      ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
        trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, [], save ++ .return_ :: K', fn.nres⟩ :: tw, P.tGlobals, tm⟩ := by
    have e1 := steps_ite (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩) (rest := tw)
      (t := [.localGet (lidx (P.frameWords - 1)), c32 pre.length, eqI,
        ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)])
      (e := save ++ [.return_]) (K := K') (seg_guard_eq2 P tl [] tm)
    simpa [trStmt, hf, Prog.ctx, K', save, List.append_assoc] using e1
  have hseg : runSeg save ⟨tl, [], P.tGlobals, tm⟩ = some ⟨tl, List.replicate fn.nres 0,
      [1, BitVec.ofNat 32 (P.sb + 4 * P.frameWords)], mem2⟩ := by
    rw [runSeg_append, runSeg_append, tGlobals_eq, seg_req hasl (by omega), Option.bind_some,
      saveCode_seg htl hF (by omega) hk, Option.bind_some, dummies_seg]
    simp [mem2]
  have m2 : Steps (asyncifyProg P) save.length
      ⟨⟨fid, tl, [], save ++ .return_ :: K', fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ [], .return_ :: K', fn.nres⟩ :: tw,
        [1, BitVec.ofNat 32 (P.sb + 4 * P.frameWords)], mem2⟩ := by
    simpa using steps_seg (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩) (rest := tw)
      (code := .return_ :: K') hseg
  obtain ⟨nU, cU, vs, eU, hdone⟩ := unwind hP hch ⟨fid, tl, List.replicate fn.nres 0 ++ [],
    .return_ :: K', fn.nres⟩ K' mem2 (P.sb + 4 * P.frameWords) rfl (by simp)
    (by have := addr_step P.sb P.frameWords tw.length; omega)
  exact ⟨_, cU, vs, m1.trans (m2.trans eU), hdone⟩

/-- The host protocol after an unwind: read the request, answer, call the export again in
rewind mode. -/
theorem host_resume {P : Prog} {H : Host σ} {cU : Cfg} {vs : List W} {sp : Nat}
    {mem : Nat → W} {te : Nat} {ta args : List W} {th : σ} {fnE : FnSrc} {f n m : Nat}
    (hdone : step (asyncifyProg P) cU = .done vs ⟨[], [1, BitVec.ofNat 32 sp], mem⟩)
    (hf0 : (mem 0).toNat = f) (hrd : (List.range n).map (fun i => mem (4 * (i + 1))) = args)
    (hfi : P.imps[f]? = some (n, m)) (hfnE : P.fnAt te = some fnE) :
    tgtStep (asyncifyProg P) H ⟨cU, th, te, ta⟩ =
      .next ⟨⟨[entry te (tdef P fnE) ta], [2, BitVec.ofNat 32 sp],
        writeWords mem 0 (fit m (H.answer th f args).2)⟩, (H.answer th f args).1, te, ta⟩ := by
  have hgi : (asyncifyProg P).imps[f]? = some (n, m) := hfi
  have hgf : (asyncifyProg P).fns[te - (asyncifyProg P).imps.length]? = some (tdef P fnE) := by
    simpa [tdef] using Prog.tgt_fn hfnE
  simp only [tgtStep, hdone, hf0, hgi, hgf, hrd]
  simp

/-- After the host's answer `ws`, the target rewinds the whole chain back to the import site. -/
theorem rewind_after {P : Prog} (hP : P.WF) {fid e : Nat} {fn fnE : FnSrc} {pre rest : List Stmt}
    {f : FuncIdx} {as rs : List LocalIdx} {ks : List Nat} {sw tw : List Frame} {tl : List W}
    {tm : Nat → W} {args ta ws : List W} (hch : Chain P fid e ks sw tw)
    (hfn : P.fnAt fid = some fn) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : f.value.val < P.imps.length) (htl : tl.length = P.frameWords)
    (hlocs : ∀ w ∈ tw, w.locals.length = P.frameWords) (hm : 4 * ws.length ≤ P.sb)
    (hws : ws.length = rs.length) (hbd : P.sb + 4 * P.frameWords * (tw.length + 1) < 2 ^ 32)
    (hfnE : P.fnAt e = some fnE) (hargsE : ta.length = fnE.nparams) :
    ∃ nR, Steps (asyncifyProg P) nR
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
  have hchain := rewinds_chain hP hch hfn (rewinds_base hP hfn hst hf htl hrec0) hrecsM
    (by have := addr_step P.sb P.frameWords tw.length; omega) fnE hfnE
  obtain ⟨nR, eR⟩ := hchain [] ta hargsE
  exact ⟨nR, by simpa only [hans] using eR⟩

/-- A call statement to an import, after its arguments are read. -/
theorem sim_imp {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
    {as rs : List LocalIdx} (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
      .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : f.value.val < P.imps.length) : SimOk P H (c, s) t := by
  have hP : P.WF := hR.wf
  have hok : FnOk P fn := Prog.fnOk hP hfn
  obtain ⟨hsig, has, hrs⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  have himpf : P.imps[f.value.val] = (as.length, rs.length) := Prog.sig_imp hsig hf
  obtain ⟨hreq1, hreq2⟩ := Prog.imp_le (List.mem_of_getElem himpf)
  have hb1 : P.imps.length + P.fns.length < 2 ^ 31 := (Prog.wf_bounds hP).1
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  obtain ⟨hlen, hlocs⟩ := hch.len hP
  have hbd : P.sb + 4 * P.frameWords * (tw.length + 1) < 2 ^ 32 := by
    have hl : c.frames.length = tw.length + 1 := by rw [hcs, List.length_cons, hlen]
    rw [← hl]; exact hR.bound.now
  have hargs : as.map (lv tl) = as.map (lv sl) := List.map_congr_left fun a ha => hloc.lv (has a ha)
  have hsrc := src_imp (H := H) (s := s) hcs hf himpf
  have hcfg : t.cfg = ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by
    rw [← hct, ← hR.globals]
  obtain ⟨nU, cU, vs, eU, hdone⟩ := tgt_imp_unwind (sl := sl) (tm := t.cfg.mem) hP hch hfn hloc
    hst hf hbd
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
  obtain ⟨nR, eR⟩ := rewind_after (args := as.map (lv tl)) (ws := fit rs.length ans.2) (tm := t.cfg.mem)
    (rs := rs) hP hch hfn hst hf htl hlocs (by rw [hfitlen]; omega) hfitlen hbd hfnE hargsE
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  let M := writeWords (unwMem P t.cfg.mem f.value.val (as.map (lv tl))
    (recOf P.frameWords pre.length tl) ks tw) 0 (fit rs.length ans.2)
  refine ⟨nU + (1 + nR), ⟨⟨⟨fid, recOf P.frameWords pre.length tl, (fit rs.length ans.2).reverse,
    setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ ::
    (restore P.frameWords ks tw ++ []), [0, BitVec.ofNat 32 P.sb], M⟩, ans.1, t.fid, t.args⟩,
    ?_, ?_, Or.inl (by omega)⟩
  · show runN (tgtStep (asyncifyProg P) H) (nU + (1 + nR)) t = _
    rw [runN_add_next (eU.tgt_of hcfg), show 1 + nR = nR + 1 by omega]
    simp only [runN, hR.host, hhost]
    exact eR.tgt ans.1 t.fid t.args
  · show Rel P H _ _
    have hT := TopR.mk (ops := (fit rs.length ans.2).reverse) (p := setsCode rs)
      (pre := pre ++ [Stmt.call f as rs]) (rest := rest) hP hfn (hloc.recOf pre.length hok.nloc)
      (by rw [hst]; simp) (setsCode_pure hrs)
      (by rw [List.length_reverse, hfitlen]; simpa using depthAfter_sets rs 0)
    refine ⟨hP, rfl, ⟨_, _, sw, _, ks, rfl, rfl, by simpa [pushTop, ans] using hT,
      by simpa using hch.restore⟩, rfl, ⟨fnE, hfnE, hargsE⟩, hR.bound.next hsrc⟩

end Silmaril.Wasm.FX.Asyncify.Tool
