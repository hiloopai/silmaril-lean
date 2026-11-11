module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Step

/-!
# The simulation in normal mode: pure steps, returns, argument reads, calls

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/Normal.lean`; `sim_lock` and `sim_ret`
are split by case: `sim_lock_trap`, `sim_lock_ok`, `sim_ret_bottom`, `sim_ret_wait`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- A pure instruction that traps, in both machines. -/
theorem sim_lock_trap {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl ex ops : List W} {i : Instr} {cs ct : List Instr}
    (hR : Rel P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw)
    (hl : sl.length = fn.nloc) (hi : PureShape fn.nloc i) (hp : pexec i sl ops = none) :
    SimOk P H (c, s) t := by
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
theorem sim_lock_ok {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl ex ops sl' ops' : List W} {i : Instr} {cs ct : List Instr}
    (hR : Rel P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hl : sl.length = fn.nloc)
    (hex : ex.length = P.frameWords - fn.nloc) (hi : PureShape fn.nloc i)
    (hp : pexec i sl ops = some (sl', ops'))
    (hnext : LocR P fn sl' (sl' ++ ex) →
      TopR P ⟨fid, sl', ops', cs, fn.nres⟩ ⟨fid, sl' ++ ex, ops', ct, fn.nres⟩) :
    SimOk P H (c, s) t := by
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
  exact ⟨hR.wf, hR.host, ⟨_, _, sw, tw, ks, rfl, rfl, hnext ⟨hl', ex, rfl, by omega⟩, hch⟩,
    hR.globals, hR.entry, hR.bound.next hsrc⟩

/-- A pure instruction executed in both machines. -/
theorem sim_lock {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr} {cs ct : List Instr}
    (hR : Rel P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, i :: ct, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hloc : LocR P fn sl tl) (hi : PureShape fn.nloc i)
    (hnext : ∀ sl' ops' tl', pexec i sl ops = some (sl', ops') → LocR P fn sl' tl' →
      TopR P ⟨fid, sl', ops', cs, fn.nres⟩ ⟨fid, tl', ops', ct, fn.nres⟩) :
    SimOk P H (c, s) t := by
  obtain ⟨hl, ex, htl, hex⟩ := hloc
  have hct' : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw := htl ▸ hct
  cases hp : pexec i sl ops with
  | none => exact sim_lock_trap hR hcs hct' hl hi hp
  | some r => exact sim_lock_ok hR hcs hct' hch hl hex hi hp (hnext r.1 r.2 _ hp)

/-- A step inside a pure statement or the tail. -/
theorem sim_run {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr} {p : List Instr}
    {pre rest : List Stmt} (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, (i :: p) ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, (i :: p) ++ trS (P.ctx fn) pre.length rest ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn) (hloc : LocR P fn sl tl)
    (hst : fn.stmts = pre ++ rest) (hp : ∀ j ∈ i :: p, pureIns fn.nloc j = true)
    (hd : depthAfter (i :: p) ops.length = some 0) : SimOk P H (c, s) t := by
  have hi := pureShape (hp i (by simp))
  refine sim_lock hR hcs hct hch hloc hi fun sl' ops' tl' he hloc' => ?_
  exact TopR.mk hR.wf hfn hloc' hst (fun j hj => hp j (by simp [hj])) (depthAfter_cons hi hd he)

/-- A step in the tail. -/
theorem sim_fin {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr} {q : List Instr}
    (hR : Rel P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: q, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, i :: q, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn) (hloc : LocR P fn sl tl)
    (hq : ∀ j ∈ i :: q, pureIns fn.nloc j = true)
    (hd : depthAfter (i :: q) ops.length = some fn.nres) : SimOk P H (c, s) t := by
  have hi := pureShape (hq i (by simp))
  refine sim_lock hR hcs hct hch hloc hi fun sl' ops' tl' he hloc' => ?_
  exact .fin hfn hloc' (fun j hj => hq j (by simp [hj])) (depthAfter_cons hi hd he)

/-! ## Guards in normal mode -/

theorem tGlobals_eq (P : Prog) : P.tGlobals = [0, BitVec.ofNat 32 P.sb] := rfl

theorem seg_guard_ne (P : Prog) (ls ops : List W) (m : Nat → W) :
    runSeg [gState, c32 2, neI] ⟨ls, ops, P.tGlobals, m⟩ = some ⟨ls, 1 :: ops, P.tGlobals, m⟩ := rfl

theorem seg_guard_eq1 (P : Prog) (ls ops : List W) (m : Nat → W) :
    runSeg [gState, c32 1, eqI] ⟨ls, ops, P.tGlobals, m⟩ = some ⟨ls, 0 :: ops, P.tGlobals, m⟩ := rfl

theorem seg_guard_eq2 (P : Prog) (ls ops : List W) (m : Nat → W) :
    runSeg [gState, c32 2, eqI] ⟨ls, ops, P.tGlobals, m⟩ = some ⟨ls, 0 :: ops, P.tGlobals, m⟩ := rfl

theorem steps_guard {E : Env} {fr : Frame} {rest : List Frame} {g : List W} {m : Nat → W}
    {seg t K : List Instr} {x : W} {ops : List W} {ls : List W}
    (h : runSeg seg ⟨fr.locals, fr.ops, g, m⟩ = some ⟨ls, x :: ops, g, m⟩) :
    Steps E (seg.length + 1) ⟨{ fr with code := seg ++ ifThen t :: K } :: rest, g, m⟩
      ⟨{ fr with locals := ls, ops := ops, code := (if x = 0 then [] else t) ++ K } :: rest, g, m⟩ := by
  have h1 := steps_seg (E := E) (fr := fr) (rest := rest) (code := ifThen t :: K) h
  have h2 : step E ⟨{ fr with locals := ls, ops := x :: ops, code := ifThen t :: K } :: rest, g, m⟩ =
      .next ⟨{ fr with locals := ls, ops := ops, code := (if x = 0 then [] else t) ++ K } :: rest,
        g, m⟩ :=
    step_if (fr := { fr with locals := ls, ops := x :: ops, code := ifThen t :: K }) rfl rfl rfl
  exact h1.trans (.one h2)

/-! ## Returns -/

/-- The bottom frame returns: both machines stop with the same results. -/
theorem sim_ret_bottom {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {fid : Nat} {nres : Nat} {sl tl ops : List W}
    (hR : Rel P H (c, s) t) (hcs : c.frames = [⟨fid, sl, ops, [], nres⟩])
    (hct : t.cfg.frames = [⟨fid, tl, ops, [], nres⟩]) : SimOk P H (c, s) t := by
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

/-- The target's return to a waiting frame: the return, then the check of the call site (the
mode is normal, so the frame continues after its check). -/
theorem ret_wait_tgt {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {tw' : List Frame}
    {fid fid1 nres nres1 k : Nat} {tl tl1 ops : List W} {K : List Instr}
    (hR : Rel P H (c, s) t)
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

/-- A frame returns to the frame waiting on its call statement. -/
theorem sim_ret_wait {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw' tw' : List Frame} {fn fn1 : FnSrc} {sl tl ops sl1 tl1 : List W} {fid1 : Nat}
    {pre1 rest1 : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} {ks' : List Nat}
    (hR : Rel P H (c, s) t)
    (hcs : c.frames = ⟨f.value.val, sl, ops, [], fn.nres⟩ ::
      ⟨fid1, sl1, [], setsCode rs ++ flatS rest1 ++ fn1.tail, fn1.nres⟩ :: sw')
    (hct : t.cfg.frames = ⟨f.value.val, tl, ops, [], fn.nres⟩ ::
      ⟨fid1, tl1, [], chk P.frameWords pre1.length fn1.nres ++ setsCode rs ++
        trS (P.ctx fn1) (pre1.length + 1) rest1 ++ fn1.tail, fn1.nres⟩ :: tw')
    (hch' : Chain P fid1 t.fid ks' sw' tw') (hfn : P.fnAt f.value.val = some fn)
    (hd : ops.length = fn.nres) (hfn1 : P.fnAt fid1 = some fn1) (hloc1 : LocR P fn1 sl1 tl1)
    (hst1 : fn1.stmts = pre1 ++ Stmt.call f as rs :: rest1) (hf1 : P.imps.length ≤ f.value.val) :
    SimOk P H (c, s) t := by
  have hok1 : FnOk P fn1 := Prog.fnOk hR.wf hfn1
  have hsw : (Stmt.call f as rs).wf P fn1.nloc = true := hok1.stmts _ (by rw [hst1]; simp)
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
  have hT := TopR.mk (ops := ops ++ []) (p := setsCode rs) (pre := pre1 ++ [Stmt.call f as rs])
    (rest := rest1) hR.wf hfn1 hloc1 (by rw [hst1]; simp) (setsCode_pure hrs)
    (by rw [List.append_nil, hd, ← hfn'', hres]; simpa using depthAfter_sets rs 0)
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  refine ⟨1 + 4, _, ret_wait_tgt hR hct', ?_, Or.inl (by omega)⟩
  refine ⟨hR.wf, hR.host, ⟨_, _, sw', tw', _, rfl, rfl, ?_, hch'⟩, hR.globals, hR.entry,
    hR.bound.next hsrc⟩
  simpa using hT

/-- The top frame returns. -/
theorem sim_ret {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {sw tw : List Frame}
    {fid : Nat} {fn : FnSrc} {sl tl ops : List W}
    (hR : Rel P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, [], fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, [], fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hd : depthAfter [] ops.length = some fn.nres) : SimOk P H (c, s) t := by
  have hd' : ops.length = fn.nres := by simpa only [depthAfter, Option.some.injEq] using hd
  cases hch with
  | nil => exact sim_ret_bottom hR hcs hct
  | cons hw hch' =>
    cases hw with
    | mk hfn1 hloc1 hst1 hf1 => exact sim_ret_wait hR hcs hct hch' hfn hd' hfn1 hloc1 hst1 hf1

end Silmaril.Wasm.FX.Asyncify.Tool
