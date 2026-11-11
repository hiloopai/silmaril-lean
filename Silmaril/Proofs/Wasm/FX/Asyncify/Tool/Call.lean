module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Normal

/-!
# The simulation in normal mode: argument reads, calls of defined functions, opening statements

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/Call.lean` and restyled: `sim_call` is
split into the source step `src_call_def`, the target steps `tgt_call_def` and the entry relation
`TopR.ofEntry`, which `asyncify_beh` shares).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

theorem lv_eq_getElem {ls : List W} {a : LocalIdx} (h : a.value.val < ls.length) :
    lv ls a = ls[a.value.val] := by
  simp [lv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem pexec_get {ls ops : List W} {a : LocalIdx} (h : a.value.val < ls.length) :
    pexec (.localGet a) ls ops = some (ls, lv ls a :: ops) := by
  simp [pexec, List.getElem?_eq_getElem h, lv_eq_getElem h]

/-- Target steps from a state whose configuration is `a`. -/
theorem Steps.tgt_of {E : Env} {H : Host σ} {n : Nat} {a b : Cfg} {t : TSt σ} (h : Steps E n a b)
    (hc : t.cfg = a) : runN (tgtStep E H) n t = .next { t with cfg := b } := by
  obtain ⟨c, s, e, as⟩ := t
  cases hc
  exact h.tgt s e as

/-- A guard whose condition holds. -/
theorem steps_guard_taken {E : Env} {fr : Frame} {rest : List Frame} {g : List W} {m : Nat → W}
    {seg t K : List Instr} {x : W} {ops : List W} {ls : List W}
    (h : runSeg seg ⟨fr.locals, fr.ops, g, m⟩ = some ⟨ls, x :: ops, g, m⟩) (hx : x ≠ 0) :
    Steps E (seg.length + 1) ⟨{ fr with code := seg ++ ifThen t :: K } :: rest, g, m⟩
      ⟨{ fr with locals := ls, ops := ops, code := t ++ K } :: rest, g, m⟩ := by
  have h1 := steps_guard (E := E) (rest := rest) (t := t) (K := K) h
  rwa [ite_eq_right hx] at h1

/-- The code of a call statement while argument `j` is read. -/
theorem getsCode_drop_code {as : List LocalIdx} {j : Nat} (hj : j < as.length) (f : FuncIdx)
    (K : List Instr) :
    (getsCode as).drop j ++ [.call f] ++ K =
      .localGet as[j] :: ((getsCode as).drop (j + 1) ++ [.call f] ++ K) := by
  rw [getsCode_drop hj]; simp

/-- The source reads an argument of a call statement; the target waits. -/
theorem sim_get {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
    {as rs : List LocalIdx} {j : Nat} (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ((as.take j).map (lv sl)).reverse,
      (getsCode as).drop j ++ [.call f] ++ setsCode rs ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hj : j < as.length) : SimOk P H (c, s) t := by
  have has : ∀ a ∈ as, a.value.val < fn.nloc :=
    (Stmt.wf_call ((Prog.fnOk hR.wf hfn).stmts (Stmt.call f as rs) (by rw [hst]; simp))).2.1
  have ha : as[j].value.val < sl.length := by rw [hloc.1]; exact has _ (List.getElem_mem hj)
  let K := (getsCode as).drop (j + 1) ++ [.call f] ++ setsCode rs ++ flatS rest ++ fn.tail
  have hcs' : c.frames = ⟨fid, sl, ((as.take j).map (lv sl)).reverse, .localGet as[j] :: K,
      fn.nres⟩ :: sw := by
    rw [hcs, getsCode_drop hj]; simp [K]
  let ops' := ((as.take (j + 1)).map (lv sl)).reverse
  have hs : step P.env c = .next ⟨⟨fid, sl, ops', K, fn.nres⟩ :: sw, c.globals, c.mem⟩ :=
    step_seg hcs' rfl (s' := ⟨sl, ops', c.globals, c.mem⟩) (by
      rw [segStep_pure (S := fn.nloc) (PureShape.get _ (by rw [← hloc.1]; exact ha))]
      simp [Frame.ls, pexec_get ha, ops', take_succ_map_rev hj])
  have hsrc : srcStep P.env H (c, s) = .next (⟨⟨fid, sl, ops', K, fn.nres⟩ :: sw, c.globals,
      c.mem⟩, s) := by simp only [srcStep, hs]
  have htop : TopR P ⟨fid, sl, ops', K, fn.nres⟩ ⟨fid, tl, [], trStmt (P.ctx fn) pre.length
      (.call f as rs) ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :=
    TopR.pre (j := j + 1) hfn hloc hst (by omega)
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  exact ⟨0, t, rfl, ⟨hR.wf, hR.host, ⟨_, _, sw, tw, ks, rfl, hct, htop, hch⟩, hR.globals,
    hR.entry, hR.bound.next hsrc⟩, Or.inr (by simp [mu, hcs', K, getsCode])⟩

theorem step_call_def {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {f : FuncIdx}
    {K : List Instr} {d : FnDef} (hf : c.frames = fr :: rest) (hcode : fr.code = .call f :: K)
    (himp : ¬ f.value.val < E.imps.length) (hd : E.fns[f.value.val - E.imps.length]? = some d)
    (hn : d.nparams ≤ fr.ops.length) :
    step E c = .next ⟨entry f.value.val d (fr.ops.take d.nparams).reverse ::
      { fr with ops := fr.ops.drop d.nparams, code := K } :: rest, c.globals, c.mem⟩ := by
  simp [step, hf, hcode, exec, ctlOf, himp, hd, hn, Cfg.setTop]

/-- A call of a defined function whose arguments are on top of the stack. -/
theorem step_call_args {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {f : FuncIdx}
    {K : List Instr} {d : FnDef} {args low : List W} (hf : c.frames = fr :: rest)
    (hcode : fr.code = .call f :: K) (hops : fr.ops = args.reverse ++ low)
    (himp : ¬ f.value.val < E.imps.length) (hd : E.fns[f.value.val - E.imps.length]? = some d)
    (hn : d.nparams = args.length) :
    step E c = .next ⟨entry f.value.val d args :: { fr with ops := low, code := K } :: rest,
      c.globals, c.mem⟩ := by
  have htk : fr.ops.take d.nparams = args.reverse := by
    rw [hops, hn]; exact List.take_left' (by simp)
  have hdr : fr.ops.drop d.nparams = low := by
    rw [hops, hn]; exact List.drop_left' (by simp)
  rw [step_call_def hf hcode himp hd (by rw [hops, hn]; simp), htk, hdr, List.reverse_reverse]

theorem one_or_ne_zero (b : W) : (1 : W) ||| b ≠ 0 := by
  intro h
  have := congrArg (fun x : W => x.getLsbD 0) h
  simp at this

theorem seg_site_normal (P : Prog) (tl : List W) (m : Nat → W) (k : Nat)
    (hF : P.frameWords - 1 < tl.length) (hF2 : P.frameWords < 2 ^ 32) :
    ∃ x, x ≠ 0 ∧ runSeg [gState, c32 2, neI, .localGet (lidx (P.frameWords - 1)), c32 k, eqI, orI]
      ⟨tl, [], P.tGlobals, m⟩ = some ⟨tl, [x], P.tGlobals, m⟩ := by
  refine ⟨_, one_or_ne_zero (Numerics.bool32 (tl[P.frameWords - 1] == BitVec.ofNat 32 k)), ?_⟩
  have h1 : [gState, c32 2, neI, .localGet (lidx (P.frameWords - 1)), c32 k, eqI, orI] =
      [gState, c32 2, neI] ++ [.localGet (lidx (P.frameWords - 1)), c32 k, eqI, orI] := rfl
  rw [h1, runSeg_append, seg_guard_ne, Option.bind_some]
  simp [runSeg, segStep, ctlOf, segCore, pexec, lidx_val (show P.frameWords - 1 < 2 ^ 32 by omega),
    hF, c32, eqI, orI, Numerics.intRelOp, Numerics.intBinOp]
  rfl

theorem seg_prologue_normal (P : Prog) (ls : List W) (m : Nat → W) :
    runSeg [gState, c32 2, eqI] ⟨ls, [], P.tGlobals, m⟩ = some ⟨ls, [0], P.tGlobals, m⟩ :=
  seg_guard_eq2 P ls [] m

/-- The locals of an entry frame: the arguments, then zeros. -/
theorem LocR.ofEntry {P : Prog} {fn : FnSrc} (hnl : fn.nloc + 1 ≤ P.frameWords)
    {sargs targs : List W} (heq : targs = sargs) (hlen : sargs.length = fn.nparams) :
    LocR P fn (sargs ++ List.replicate fn.nlocals 0)
      (targs ++ List.replicate (P.frameWords - fn.nparams) 0) := by
  have hnl' : fn.nparams + fn.nlocals + 1 ≤ P.frameWords := hnl
  have hrep : List.replicate (P.frameWords - fn.nparams) (0 : W) =
      List.replicate fn.nlocals 0 ++ List.replicate (P.frameWords - fn.nloc) 0 := by
    rw [← List.replicate_add]; congr 1; unfold FnSrc.nloc; omega
  refine ⟨by simp [FnSrc.nloc, hlen], List.replicate (P.frameWords - fn.nloc) 0, ?_, by simp⟩
  rw [heq, List.append_assoc, hrep]

/-- The entry frame of a call, after the target's prologue (normal mode). -/
theorem TopR.ofEntry {P : Prog} (hP : P.WF) {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn)
    {sargs targs : List W} (heq : targs = sargs) (hlen : sargs.length = fn.nparams) :
    TopR P (Tool.entry e ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ sargs)
      ⟨e, targs ++ List.replicate (P.frameWords - fn.nparams) 0, [],
        trS (P.ctx fn) 0 fn.stmts ++ fn.tail, fn.nres⟩ := by
  have hloc := LocR.ofEntry (P := P) (Prog.fnOk hP hfn).nloc heq hlen
  have h := TopR.mk (ops := []) (p := []) (pre := []) (rest := fn.stmts) hP hfn hloc (by simp)
    (by simp) (by simp [depthAfter])
  simpa [Tool.entry, FnSrc.body] using h

/-- The source side of a call of a defined function. -/
theorem src_call_def {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {sw : List Frame} {fid : Nat}
    {fn fn' : FnSrc} {sl : List W} {f : FuncIdx} {as : List LocalIdx} {K : List Instr}
    (hcs : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse, .call f :: K, fn.nres⟩ :: sw)
    (hf : P.imps.length ≤ f.value.val) (hfn' : P.fnAt f.value.val = some fn')
    (hnp : fn'.nparams = as.length) :
    srcStep P.env H (c, s) = .next (⟨entry f.value.val ⟨fn'.nparams, fn'.nlocals, fn'.nres,
      fn'.body⟩ (as.map (lv sl)) :: ⟨fid, sl, [], K, fn.nres⟩ :: sw, c.globals, c.mem⟩, s) := by
  have himp : ¬ f.value.val < P.env.imps.length := Nat.not_lt.2 hf
  have hs := step_call_args (E := P.env) (args := as.map (lv sl)) (low := [])
    (d := ⟨fn'.nparams, fn'.nlocals, fn'.nres, fn'.body⟩) hcs rfl (by simp) himp
    (by simpa using Prog.env_fn hfn') (by simp [hnp])
  simp only [srcStep, hs]

/-- The target side of a call statement to a defined function, from its guard to the callee's
code after the prologue (normal mode). -/
theorem tgt_call_def {P : Prog} {fid k : Nat} {fn fn' : FnSrc} {tl : List W} {tw : List Frame}
    {tm : Nat → W} {f : FuncIdx} {as rs : List LocalIdx} {K0 : List Instr}
    (htl : tl.length = P.frameWords) (hF : 1 ≤ P.frameWords) (hF2 : P.frameWords < 2 ^ 32)
    (hasl : ∀ a ∈ as, a.value.val < tl.length) (himp : ¬ f.value.val < P.imps.length)
    (hfn' : P.fnAt f.value.val = some fn') (hnp : fn'.nparams = as.length) :
    Steps (asyncifyProg P) ((7 + 1) + (as.length + (1 + (3 + 1))))
      ⟨⟨fid, tl, [], trStmt (P.ctx fn) k (.call f as rs) ++ K0, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨f.value.val, as.map (lv tl) ++ List.replicate (P.frameWords - fn'.nparams) 0, [],
        trS (P.ctx fn') 0 fn'.stmts ++ fn'.tail, fn'.nres⟩ ::
        ⟨fid, tl, [], chk P.frameWords k fn.nres ++ setsCode rs ++ K0, fn.nres⟩ :: tw,
        P.tGlobals, tm⟩ := by
  obtain ⟨x, hx0, hseg⟩ := seg_site_normal P tl tm k (by omega) hF2
  let K := chk P.frameWords k fn.nres ++ setsCode rs ++ K0
  have m1 : Steps (asyncifyProg P) (7 + 1)
      ⟨⟨fid, tl, [], trStmt (P.ctx fn) k (.call f as rs) ++ K0, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, [], getsCode as ++ .call f :: K, fn.nres⟩ :: tw, P.tGlobals, tm⟩ := by
    have e1 := steps_guard_taken (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩)
      (rest := tw) (t := getsCode as ++ [.call f] ++ chk P.frameWords k fn.nres ++ setsCode rs)
      (K := K0) hseg hx0
    simpa [trStmt, Prog.ctx, himp, K, List.append_assoc] using e1
  have m2 : Steps (asyncifyProg P) as.length
      ⟨⟨fid, tl, [], getsCode as ++ .call f :: K, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, (as.map (lv tl)).reverse, .call f :: K, fn.nres⟩ :: tw, P.tGlobals, tm⟩ := by
    have e2 := steps_seg (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩) (rest := tw)
      (code := .call f :: K) (getsCode_seg (gs := P.tGlobals) (mem := tm) (ops := []) hasl)
    simpa [getsCode] using e2
  let d : FnDef := ⟨fn'.nparams, P.frameWords - fn'.nparams, fn'.nres, P.tBody fn'⟩
  have e3 : step (asyncifyProg P) ⟨⟨fid, tl, (as.map (lv tl)).reverse, .call f :: K, fn.nres⟩ ::
      tw, P.tGlobals, tm⟩ = .next ⟨entry f.value.val d (as.map (lv tl)) ::
        ⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals, tm⟩ :=
    step_call_args (E := asyncifyProg P)
      (fr := ⟨fid, tl, (as.map (lv tl)).reverse, .call f :: K, fn.nres⟩) (args := as.map (lv tl))
      (low := []) rfl rfl (by simp) (by simpa [asyncifyProg] using himp)
      (by simpa using Prog.tgt_fn hfn') (by simp [d, hnp])
  have m4 : Steps (asyncifyProg P) (3 + 1)
      ⟨entry f.value.val d (as.map (lv tl)) :: ⟨fid, tl, [], K, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨f.value.val, as.map (lv tl) ++ List.replicate (P.frameWords - fn'.nparams) 0, [],
        trS (P.ctx fn') 0 fn'.stmts ++ fn'.tail, fn'.nres⟩ :: ⟨fid, tl, [], K, fn.nres⟩ :: tw,
        P.tGlobals, tm⟩ := by
    have e4 := steps_guard (E := asyncifyProg P) (fr := entry f.value.val d (as.map (lv tl)))
      (rest := ⟨fid, tl, [], K, fn.nres⟩ :: tw) (t := restoreCode P.frameWords)
      (K := trS (P.ctx fn') 0 fn'.stmts ++ fn'.tail) (seg_prologue_normal P _ tm)
    simpa [entry, d, Prog.tBody, prologue, ifThen] using e4
  exact m1.trans (m2.trans ((Steps.one e3).trans m4))

/-- A call statement to a defined function, after its arguments are read. -/
theorem sim_call {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
    {as rs : List LocalIdx} (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
      .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : P.imps.length ≤ f.value.val) : SimOk P H (c, s) t := by
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
  have htgt := tgt_call_def (fid := fid) (k := pre.length) (fn := fn) (tw := tw) (tm := t.cfg.mem)
    (rs := rs) (K0 := trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail) htl (by have := hok.nloc; omega) hF2 hasl (Nat.not_lt.2 hf)
    hfn' hnp
  have hcfg : t.cfg = ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      (trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail), fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by
    rw [← List.append_assoc, ← hct, ← hR.globals]
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  have hw : WaitR P f.value.val pre.length ⟨fid, sl, [], setsCode rs ++ flatS rest ++ fn.tail,
      fn.nres⟩ ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++ setsCode rs ++
        (trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail), fn.nres⟩ := by
    simpa only [List.append_assoc] using WaitR.mk hfn hloc hst hf
  refine ⟨_, _, htgt.tgt_of hcfg, ?_, Or.inl (by omega)⟩
  exact ⟨hR.wf, hR.host, ⟨_, _, _, _, _, rfl, rfl, TopR.ofEntry hR.wf hfn' hargs (by simp [hnp]),
    .cons hw hch⟩, rfl, hR.entry, hR.bound.next hsrc⟩

end Silmaril.Wasm.FX.Asyncify.Tool
