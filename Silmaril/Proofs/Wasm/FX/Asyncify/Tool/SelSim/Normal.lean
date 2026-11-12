module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.SelSim.Macro

/-!
# The selective simulation: the cases of the `Rel` shape

Copies of the case lemmas of `Silmaril/Proofs/Wasm/FX/Asyncify/Tool/{Normal,Call,SuspendSim}.lean`
for the relation `RelS` in its `Rel` shape, under `SelOk P C` instead of `P.WF`: pure steps,
returns, argument reads, calls of defined functions and suspensions. Each concludes the
obligation `SimOkS`, whose next states are in `RelS` (here always in the `Rel` shape).

New proofs (copies).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type} {C : Nat → Prop}

/-- A pure instruction that traps, in both machines. -/
theorem sim_lock_trap_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl ex ops : List W} {i : Instr} {cs ct : List Instr}
    (hR : RelS P C H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw)
    (hl : sl.length = fn.nloc) (hi : PureShape fn.nloc i) (hp : pexec i sl ops = none) :
    SimOkS P C H (c, s) t := by
  have hctl : ctlOf i = none := ctlOf_pure hi
  have hs : step P.env c = .trap := step_trap_seg hcs rfl hctl (by
    rw [segStep_pure hi]; simp [Frame.ls, hp])
  have ht : step (asyncifyProg P) t.cfg = .trap := step_trap_seg hct rfl hctl (by
    rw [segStep_pure hi]; simp [Frame.ls, pexec_ext hi hl, hp])
  have hsrc : srcStep P.env H (c, s) = .stop (.trap s) := by simp only [srcStep, hs]
  have htgt : runN (tgtStep (asyncifyProg P) H) 1 t = .stop (.trap s) := by
    simp [runN, tgtStep, ht, hR.host]
  refine ⟨fun o ho => ⟨1, ?_⟩, fun x' hx => ?_⟩
  · rw [← SRes.stop.inj (hsrc.symm.trans ho)]
    exact htgt
  · cases hsrc.symm.trans hx

/-- A pure instruction that continues, in both machines. -/
theorem sim_lock_ok_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl ex ops sl' ops' : List W} {i : Instr} {cs ct : List Instr}
    (hR : RelS P C H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hl : sl.length = fn.nloc)
    (hex : ex.length = P.frameWords - fn.nloc) (hi : PureShape fn.nloc i)
    (hp : pexec i sl ops = some (sl', ops'))
    (hnext : LocR P fn sl' (sl' ++ ex) →
      TopR P ⟨fid, sl', ops', cs, fn.nres⟩ ⟨fid, sl' ++ ex, ops', ct, fn.nres⟩) :
    SimOkS P C H (c, s) t := by
  have hs : step P.env c = .next ⟨⟨fid, sl', ops', cs, fn.nres⟩ :: sw, c.globals, c.mem⟩ :=
    step_seg hcs rfl (s' := ⟨sl', ops', c.globals, c.mem⟩) (by
      rw [segStep_pure hi]; simp [Frame.ls, hp])
  have ht : step (asyncifyProg P) t.cfg =
      .next ⟨⟨fid, sl' ++ ex, ops', ct, fn.nres⟩ :: tw, t.cfg.globals, t.cfg.mem⟩ :=
    step_seg hct rfl (s' := ⟨sl' ++ ex, ops', t.cfg.globals, t.cfg.mem⟩) (by
      rw [segStep_pure hi]; simp [Frame.ls, pexec_ext hi hl, hp])
  have hl' : sl'.length = fn.nloc := by rw [pexec_len hi hp]; exact hl
  have hsrc : srcStep P.env H (c, s) =
      .next (⟨⟨fid, sl', ops', cs, fn.nres⟩ :: sw, c.globals, c.mem⟩, s) := by
    simp only [srcStep, hs]
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  refine ⟨1, _, by simp only [runN, tgtStep, ht]; rfl, ?_, Or.inl Nat.one_pos⟩
  exact ⟨hR.ok, hR.host, .inl ⟨_, _, sw, tw, ks, rfl, rfl, hnext ⟨hl', ex, rfl, by omega⟩, hch⟩,
    hR.globals, hR.entry, hR.bound.next hsrc⟩

/-- A pure instruction executed in both machines. -/
theorem sim_lock_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr} {cs ct : List Instr}
    (hR : RelS P C H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, i :: ct, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hloc : LocR P fn sl tl) (hi : PureShape fn.nloc i)
    (hnext : ∀ sl' ops' tl', pexec i sl ops = some (sl', ops') → LocR P fn sl' tl' →
      TopR P ⟨fid, sl', ops', cs, fn.nres⟩ ⟨fid, tl', ops', ct, fn.nres⟩) :
    SimOkS P C H (c, s) t := by
  obtain ⟨hl, ex, htl, hex⟩ := hloc
  have hct' : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw := htl ▸ hct
  cases hp : pexec i sl ops with
  | none => exact sim_lock_trap_q hR hcs hct' hl hi hp
  | some r => exact sim_lock_ok_q hR hcs hct' hch hl hex hi hp (hnext r.1 r.2 _ hp)

/-- A step inside a pure statement or the tail. -/
theorem sim_run_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr} {p : List Instr}
    {pre rest : List Stmt} (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, (i :: p) ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, (i :: p) ++ trS (P.ctx fn) pre.length rest ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn) (hloc : LocR P fn sl tl)
    (hst : fn.stmts = pre ++ rest) (hp : ∀ j ∈ i :: p, pureIns fn.nloc j = true)
    (hd : depthAfter (i :: p) ops.length = some 0) : SimOkS P C H (c, s) t := by
  have hi := pureShape (hp i (by simp))
  refine sim_lock_q hR hcs hct hch hloc hi fun sl' ops' tl' he hloc' => ?_
  exact TopR.mkS hR.ok hfn hloc' hst (fun j hj => hp j (by simp [hj])) (depthAfter_cons hi hd he)

/-- A step in the tail. -/
theorem sim_fin_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr} {q : List Instr}
    (hR : RelS P C H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: q, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, i :: q, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn) (hloc : LocR P fn sl tl)
    (hq : ∀ j ∈ i :: q, pureIns fn.nloc j = true)
    (hd : depthAfter (i :: q) ops.length = some fn.nres) : SimOkS P C H (c, s) t := by
  have hi := pureShape (hq i (by simp))
  refine sim_lock_q hR hcs hct hch hloc hi fun sl' ops' tl' he hloc' => ?_
  exact .fin hfn hloc' (fun j hj => hq j (by simp [hj])) (depthAfter_cons hi hd he)

/-- The target's return to a waiting frame: the return, then the check of the call site (the
mode is normal, so the frame continues after its check). -/
theorem ret_wait_tgt_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {tw' : List Frame}
    {fid fid1 nres nres1 k : Nat} {tl tl1 ops : List W} {K : List Instr}
    (hR : RelS P C H (c, s) t)
    (hct : t.cfg.frames = ⟨fid, tl, ops, [], nres⟩ ::
      ⟨fid1, tl1, [], chk P.frameWords k nres1 ++ K, nres1⟩ :: tw') :
    runN (tgtStep (asyncifyProg P) H) (1 + 4) t =
      .next ⟨⟨⟨fid1, tl1, ops ++ [], K, nres1⟩ :: tw', t.cfg.globals, t.cfg.mem⟩,
        t.host, t.fid, t.args⟩ := by
  have hret : step (asyncifyProg P) t.cfg = .next ⟨⟨fid1, tl1, ops ++ [],
      chk P.frameWords k nres1 ++ K, nres1⟩ :: tw', t.cfg.globals, t.cfg.mem⟩ := by
    rw [step_ret hct rfl]
    simp [ret]
  have hsteps := steps_guard (E := asyncifyProg P) (fr := ⟨fid1, tl1, ops ++ [], [], nres1⟩)
    (rest := tw') (t := saveCode P.frameWords k ++ dummies nres1 ++ [.return_]) (K := K)
    (seg_guard_eq1 P tl1 (ops ++ []) t.cfg.mem)
  rw [runN_add_next (by simp only [runN, tgtStep, hret]; rfl), hR.globals]
  simpa [chk, List.append_assoc] using hsteps.tgt (H := H) t.host t.fid t.args

/-- The bottom frame returns: both machines stop with the same results. -/
theorem sim_ret_bottom_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {fid : Nat} {nres : Nat} {sl tl ops : List W}
    (hR : RelS P C H (c, s) t) (hcs : c.frames = [⟨fid, sl, ops, [], nres⟩])
    (hct : t.cfg.frames = [⟨fid, tl, ops, [], nres⟩]) : SimOkS P C H (c, s) t := by
  have hs : step P.env c = ret c ops [] := step_ret hcs rfl
  have ht : step (asyncifyProg P) t.cfg = ret t.cfg ops [] := step_ret hct rfl
  have hsrc : srcStep P.env H (c, s) = .stop (.done ops s) := by simp only [srcStep, hs, ret]
  have hg : t.cfg.globals[0]? = some 0 := by rw [hR.globals]; rfl
  have htgt : runN (tgtStep (asyncifyProg P) H) 1 t = .stop (.done ops s) := by
    simp only [runN, tgtStep, ht, ret, hg, hR.host]
    simp
  refine ⟨fun o ho => ⟨1, ?_⟩, fun x' hx => ?_⟩
  · rw [← SRes.stop.inj (hsrc.symm.trans ho)]
    exact htgt
  · cases hsrc.symm.trans hx

/-- A frame returns to the frame waiting on its call statement. -/
theorem sim_ret_wait_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw' tw' : List Frame} {fn fn1 : FnSrc} {sl tl ops sl1 tl1 : List W} {fid1 : Nat}
    {pre1 rest1 : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} {ks' : List Nat}
    (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨f.value.val, sl, ops, [], fn.nres⟩ ::
      ⟨fid1, sl1, [], setsCode rs ++ flatS rest1 ++ fn1.tail, fn1.nres⟩ :: sw')
    (hct : t.cfg.frames = ⟨f.value.val, tl, ops, [], fn.nres⟩ ::
      ⟨fid1, tl1, [], chk P.frameWords pre1.length fn1.nres ++ setsCode rs ++
        trS (P.ctx fn1) (pre1.length + 1) rest1 ++ fn1.tail, fn1.nres⟩ :: tw')
    (hch' : Chain P fid1 t.fid ks' sw' tw') (hfn : P.fnAt f.value.val = some fn)
    (hd : ops.length = fn.nres) (hfn1 : P.fnAt fid1 = some fn1) (hloc1 : LocR P fn1 sl1 tl1)
    (hst1 : fn1.stmts = pre1 ++ Stmt.call f as rs :: rest1) (hf1 : P.imps.length ≤ f.value.val) :
    SimOkS P C H (c, s) t := by
  have hok1 : FnOkS P C fn1 := hR.ok.fn hfn1
  have hsw : (Stmt.call f as rs).wf P fn1.nloc = true := hok1.call (by rw [hst1]; simp)
  obtain ⟨hsig, -, hrs⟩ := Stmt.wf_call hsw
  obtain ⟨fn', hfn', -, hres⟩ := Prog.sig_fn hsig hf1
  have hfn'' : fn' = fn := Option.some.inj (hfn'.symm.trans hfn)
  have hsrc : srcStep P.env H (c, s) = .next (⟨⟨fid1, sl1, ops ++ [], setsCode rs ++ flatS rest1 ++
      fn1.tail, fn1.nres⟩ :: sw', c.globals, c.mem⟩, s) := by
    simp only [srcStep, step_ret hcs rfl, ret]
  have hct' : t.cfg.frames = ⟨f.value.val, tl, ops, [], fn.nres⟩ ::
      ⟨fid1, tl1, [], chk P.frameWords pre1.length fn1.nres ++ (setsCode rs ++
        trS (P.ctx fn1) (pre1.length + 1) rest1 ++ fn1.tail), fn1.nres⟩ :: tw' := by
    rw [hct]
    simp only [List.append_assoc]
  have hT := TopR.mkS (ops := ops ++ []) (p := setsCode rs) (pre := pre1 ++ [Stmt.call f as rs])
    (rest := rest1) hR.ok hfn1 hloc1 (by rw [hst1]; simp) (setsCode_pure hrs)
    (by rw [List.append_nil, hd, ← hfn'', hres]; simpa using depthAfter_sets rs 0)
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  refine ⟨1 + 4, _, ret_wait_tgt_q hR hct', ?_, Or.inl (by omega)⟩
  refine ⟨hR.ok, hR.host, .inl ⟨_, _, sw', tw', _, rfl, rfl, ?_, hch'⟩, hR.globals, hR.entry,
    hR.bound.next hsrc⟩
  simpa using hT

/-- The top frame returns. -/
theorem sim_ret_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W}
    (hR : RelS P C H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, [], fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, [], fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hd : depthAfter [] ops.length = some fn.nres) : SimOkS P C H (c, s) t := by
  have hd' : ops.length = fn.nres := by simpa only [depthAfter, Option.some.injEq] using hd
  cases hch with
  | nil => exact sim_ret_bottom_q hR hcs hct
  | cons hw hch' =>
    cases hw with
    | mk hfn1 hloc1 hst1 hf1 => exact sim_ret_wait_q hR hcs hct hch' hfn hd' hfn1 hloc1 hst1 hf1

/-- The source reads an argument of a call statement; the target waits. -/
theorem sim_get_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
    {as rs : List LocalIdx} {j : Nat} (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ((as.take j).map (lv sl)).reverse,
      (getsCode as).drop j ++ [.call f] ++ setsCode rs ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hj : j < as.length) : SimOkS P C H (c, s) t := by
  have has : ∀ a ∈ as, a.value.val < fn.nloc :=
    (Stmt.wf_call ((hR.ok.fn hfn).stmts (Stmt.call f as rs) (by rw [hst]; simp))).2.1
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
  exact ⟨0, t, rfl, ⟨hR.ok, hR.host, .inl ⟨_, _, sw, tw, ks, rfl, hct, htop, hch⟩, hR.globals,
    hR.entry, hR.bound.next hsrc⟩, Or.inr (by simp [mu, hcs', K, getsCode])⟩

/-- A call statement to a defined function, after its arguments are read. -/
theorem sim_call_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
    {as rs : List LocalIdx} (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
      .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : P.imps.length ≤ f.value.val) : SimOkS P C H (c, s) t := by
  have hok : FnOkS P C fn := hR.ok.fn hfn
  obtain ⟨hsig, has, -⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  obtain ⟨fn', hfn', hnp, -⟩ := Prog.sig_fn hsig hf
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  have hF2 : P.frameWords < 2 ^ 32 := by have := (hR.ok.bounds).2; omega
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
  exact ⟨hR.ok, hR.host, .inl ⟨_, _, _, _, _, rfl, rfl, TopR.ofEntryS hR.ok hfn' hargs (by simp [hnp]),
    .cons hw hch⟩, rfl, hR.entry, hR.bound.next hsrc⟩

/-- A call statement to an import, after its arguments are read. -/
theorem sim_imp_q {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx}
    {as rs : List LocalIdx} (hR : RelS P C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, (as.map (lv sl)).reverse,
      .call f :: (setsCode rs ++ flatS rest ++ fn.tail), fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : f.value.val < P.imps.length) : SimOkS P C H (c, s) t := by
  have hP : SelOk P C := hR.ok
  have hok : FnOkS P C fn := hP.fn hfn
  obtain ⟨hsig, has, hrs⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  have himpf : P.imps[f.value.val] = (as.length, rs.length) := Prog.sig_imp hsig hf
  obtain ⟨hreq1, hreq2⟩ := Prog.imp_le (List.mem_of_getElem himpf)
  have hb1 : P.imps.length + P.fns.length < 2 ^ 31 := (hP.bounds).1
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  obtain ⟨hlen, hlocs⟩ := hch.lenS hP
  have hbd : P.sb + 4 * P.frameWords * (tw.length + 1) < 2 ^ 32 := by
    have hl : c.frames.length = tw.length + 1 := by rw [hcs, List.length_cons, hlen]
    rw [← hl]; exact hR.bound.now
  have hargs : as.map (lv tl) = as.map (lv sl) := List.map_congr_left fun a ha => hloc.lv (has a ha)
  have hsrc := src_imp (H := H) (s := s) hcs hf himpf
  have hcfg : t.cfg = ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, t.cfg.mem⟩ := by
    rw [← hct, ← hR.globals]
  obtain ⟨nU, cU, vs, eU, hdone⟩ := tgt_imp_unwind_q (sl := sl) (tm := t.cfg.mem) hP hch hfn hloc
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
  obtain ⟨nR, eR⟩ := rewind_after_q (args := as.map (lv tl)) (ws := fit rs.length ans.2) (tm := t.cfg.mem)
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
  · show RelS P C H _ _
    have hT := TopR.mkS (ops := (fit rs.length ans.2).reverse) (p := setsCode rs)
      (pre := pre ++ [Stmt.call f as rs]) (rest := rest) hP hfn (hloc.recOf pre.length hok.nloc)
      (by rw [hst]; simp) (setsCode_pure hrs)
      (by rw [List.length_reverse, hfitlen]; simpa using depthAfter_sets rs 0)
    refine ⟨hP, rfl, .inl ⟨_, _, sw, _, ks, rfl, rfl, by simpa [pushTop, ans] using hT,
      by simpa using hch.restore⟩, rfl, ⟨fnE, hfnE, hargsE⟩, hR.bound.next hsrc⟩

end Silmaril.Wasm.FX.Asyncify.Tool

