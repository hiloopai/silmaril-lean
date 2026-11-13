module

public import Silmaril.Wasm.FX.Asyncify.Tool.Wrap.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Wrap.Rewind

/-!
# The simulation with in-bounds target runs and a wrapping `sp`: the relation, normal mode

`RelW` is `Rel` (`Silmaril.Proofs.Wasm.FX.Asyncify.Tool`) with `DepthBoundW` in place of
`DepthBound`; `SimSafeW` is `SimSafe` (`Fits/Normal`) with `RelW`. The cases of normal mode
(pure instructions, returns, argument reads) never read the bound, so they are the cases of
`Fits/Normal` again.

New proofs (copies of `Fits/Normal` with `RelW`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- `Rel` with the weaker bound `DepthBoundW`. -/
structure RelW (P : Prog) (H : Host σ) (x : Cfg × σ) (t : TSt σ) : Prop where
  wf : P.WF
  host : t.host = x.2
  frames : ∃ s0 t0 sw tw ks, x.1.frames = s0 :: sw ∧ t.cfg.frames = t0 :: tw ∧ TopR P s0 t0 ∧
    Chain P s0.fid t.fid ks sw tw
  globals : t.cfg.globals = P.tGlobals
  entry : ∃ fn, P.fnAt t.fid = some fn ∧ t.args.length = fn.nparams
  bound : DepthBoundW P H x

theorem DepthBoundW.next {P : Prog} {H : Host σ} {x x' : Cfg × σ} (h : DepthBoundW P H x)
    (hx : srcStep P.env H x = .next x') : DepthBoundW P H x' := by
  intro n y hy
  exact h (n + 1) y (by simp only [runN, hx]; exact hy)

theorem DepthBoundW.now {P : Prog} {H : Host σ} {x : Cfg × σ} (h : DepthBoundW P H x) :
    P.sb + 4 * P.frameWords * x.1.frames.length < 2 ^ 32 + 4 * P.frameWords :=
  h 0 x rfl

/-- `DepthBound` gives `DepthBoundW`. -/
theorem DepthBound.toW {P : Prog} {H : Host σ} {x : Cfg × σ} (h : DepthBound P H x) :
    DepthBoundW P H x := fun n y hy => Nat.lt_of_lt_of_le (h n y hy) (Nat.le_add_right _ _)

/-- The simulation obligation with an in-bounds target run, for `RelW`. -/
def SimSafeW (cap : Nat) (P : Prog) (H : Host σ) (x : Cfg × σ) (t : TSt σ) : Prop :=
  (∀ o, srcStep P.env H x = .stop o → ∃ n, runN (tgtStep (asyncifyProg P) H) n t = .stop o ∧
    SafeT cap (asyncifyProg P) H n t) ∧
  (∀ x', srcStep P.env H x = .next x' → ∃ n t', runN (tgtStep (asyncifyProg P) H) n t = .next t' ∧
    RelW P H x' t' ∧ (0 < n ∨ mu x' < mu x) ∧ SafeT cap (asyncifyProg P) H n t)

/-- In-bounds target steps before an obligation. -/
theorem SimSafeW.pre {cap : Nat} {P : Prog} {H : Host σ} {x : Cfg × σ} {t t' : TSt σ} {k : Nat}
    (h : runN (tgtStep (asyncifyProg P) H) k t = .next t')
    (hs : SafeT cap (asyncifyProg P) H k t) (hok : SimSafeW cap P H x t') : SimSafeW cap P H x t := by
  refine ⟨fun o ho => ?_, fun x' hx => ?_⟩
  · obtain ⟨n, hn, hsn⟩ := hok.1 o ho
    exact ⟨k + n, by rw [runN_add_next h]; exact hn, SafeT.trans h hs hsn⟩
  · obtain ⟨n, t'', hn, hR, hd, hsn⟩ := hok.2 x' hx
    refine ⟨k + n, t'', by rw [runN_add_next h]; exact hn, hR, ?_, SafeT.trans h hs hsn⟩
    rcases hd with hd | hd
    · exact Or.inl (by omega)
    · exact Or.inr hd

/-- A pure instruction that traps, in both machines. -/
theorem sim_lock_trapW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl ex ops : List W} {i : Instr}
    {cs ct : List Instr}
    (hR : RelW P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw)
    (hl : sl.length = fn.nloc) (hi : PureShape fn.nloc i) (hp : pexec i sl ops = none) :
    SimSafeW cap P H (c, s) t := by
  have hctl : ctlOf i = none := ctlOf_pure hi
  have hs : step P.env c = .trap := step_trap_seg hcs rfl hctl (by
    rw [segStep_pure hi]; simp [Frame.ls, hp])
  have ht : step (asyncifyProg P) t.cfg = .trap := step_trap_seg hct rfl hctl (by
    rw [segStep_pure hi]; simp [Frame.ls, pexec_ext hi hl, hp])
  have hsrc : srcStep P.env H (c, s) = .stop (.trap s) := by simp only [srcStep, hs]
  have htgt : runN (tgtStep (asyncifyProg P) H) 1 t = .stop (.trap s) := by
    simp [runN, tgtStep, ht, hR.host]
  have hsafe : SafeT cap (asyncifyProg P) H 1 t :=
    SafeT.one (not_oob_free hct rfl (accFree_of_pure hi))
  refine ⟨fun o ho => ⟨1, ?_, hsafe⟩, fun x' hx => ?_⟩
  · rw [← SRes.stop.inj (hsrc.symm.trans ho)]
    exact htgt
  · cases hsrc.symm.trans hx

/-- A pure instruction that continues, in both machines. -/
theorem sim_lock_okW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl ex ops sl' ops' : List W} {i : Instr}
    {cs ct : List Instr}
    (hR : RelW P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hl : sl.length = fn.nloc)
    (hex : ex.length = P.frameWords - fn.nloc) (hi : PureShape fn.nloc i)
    (hp : pexec i sl ops = some (sl', ops'))
    (hnext : LocR P fn sl' (sl' ++ ex) →
      TopR P ⟨fid, sl', ops', cs, fn.nres⟩ ⟨fid, sl' ++ ex, ops', ct, fn.nres⟩) :
    SimSafeW cap P H (c, s) t := by
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
  have hsafe : SafeT cap (asyncifyProg P) H 1 t :=
    SafeT.one (not_oob_free hct rfl (accFree_of_pure hi))
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  refine ⟨1, _, by simp only [runN, tgtStep, ht]; rfl, ?_, Or.inl Nat.one_pos, hsafe⟩
  exact ⟨hR.wf, hR.host, ⟨_, _, sw, tw, ks, rfl, rfl, hnext ⟨hl', ex, rfl, by omega⟩, hch⟩,
    hR.globals, hR.entry, hR.bound.next hsrc⟩

/-- A pure instruction executed in both machines. -/
theorem sim_lockW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr}
    {cs ct : List Instr}
    (hR : RelW P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, i :: ct, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hloc : LocR P fn sl tl)
    (hi : PureShape fn.nloc i)
    (hnext : ∀ sl' ops' tl', pexec i sl ops = some (sl', ops') → LocR P fn sl' tl' →
      TopR P ⟨fid, sl', ops', cs, fn.nres⟩ ⟨fid, tl', ops', ct, fn.nres⟩) :
    SimSafeW cap P H (c, s) t := by
  obtain ⟨hl, ex, htl, hex⟩ := hloc
  have hct' : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, fn.nres⟩ :: tw := htl ▸ hct
  cases hp : pexec i sl ops with
  | none => exact sim_lock_trapW hR hcs hct' hl hi hp
  | some r => exact sim_lock_okW hR hcs hct' hch hl hex hi hp (hnext r.1 r.2 _ hp)

/-- A step inside a pure statement or the tail. -/
theorem sim_runW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr}
    {p : List Instr} {pre rest : List Stmt} (hR : RelW P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, (i :: p) ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, (i :: p) ++ trS (P.ctx fn) pre.length rest ++ fn.tail,
      fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ rest)
    (hp : ∀ j ∈ i :: p, pureIns fn.nloc j = true)
    (hd : depthAfter (i :: p) ops.length = some 0) : SimSafeW cap P H (c, s) t := by
  have hi := pureShape (hp i (by simp))
  refine sim_lockW hR hcs hct hch hloc hi fun sl' ops' tl' he hloc' => ?_
  exact TopR.mk hR.wf hfn hloc' hst (fun j hj => hp j (by simp [hj])) (depthAfter_cons hi hd he)

/-- A step in the tail. -/
theorem sim_finW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {i : Instr}
    {q : List Instr}
    (hR : RelW P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: q, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, i :: q, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hq : ∀ j ∈ i :: q, pureIns fn.nloc j = true)
    (hd : depthAfter (i :: q) ops.length = some fn.nres) : SimSafeW cap P H (c, s) t := by
  have hi := pureShape (hq i (by simp))
  refine sim_lockW hR hcs hct hch hloc hi fun sl' ops' tl' he hloc' => ?_
  exact .fin hfn hloc' (fun j hj => hq j (by simp [hj])) (depthAfter_cons hi hd he)

/-- The bottom frame returns: both machines stop with the same results. -/
theorem sim_ret_bottomW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {fid : Nat} {nres : Nat} {sl tl ops : List W}
    (hR : RelW P H (c, s) t) (hcs : c.frames = [⟨fid, sl, ops, [], nres⟩])
    (hct : t.cfg.frames = [⟨fid, tl, ops, [], nres⟩]) : SimSafeW cap P H (c, s) t := by
  have hs : step P.env c = ret c ops [] := step_ret hcs rfl
  have ht : step (asyncifyProg P) t.cfg = ret t.cfg ops [] := step_ret hct rfl
  have hsrc : srcStep P.env H (c, s) = .stop (.done ops s) := by simp only [srcStep, hs, ret]
  have hg : t.cfg.globals[0]? = some 0 := by rw [hR.globals]; rfl
  have htgt : runN (tgtStep (asyncifyProg P) H) 1 t = .stop (.done ops s) := by
    simp only [runN, tgtStep, ht, ret, hg, hR.host]
    simp
  have hsafe : SafeT cap (asyncifyProg P) H 1 t := SafeT.one (not_oob_nil hct rfl)
  refine ⟨fun o ho => ⟨1, ?_, hsafe⟩, fun x' hx => ?_⟩
  · rw [← SRes.stop.inj (hsrc.symm.trans ho)]
    exact htgt
  · cases hsrc.symm.trans hx

/-- The target's return to a waiting frame is in bounds (`ret_wait_tgt`). -/
theorem ret_wait_safeW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {tw' : List Frame} {fid fid1 nres nres1 k : Nat} {tl tl1 ops : List W} {K : List Instr}
    (hR : RelW P H (c, s) t)
    (hct : t.cfg.frames = ⟨fid, tl, ops, [], nres⟩ ::
      ⟨fid1, tl1, [], chk P.frameWords k nres1 ++ K, nres1⟩ :: tw') :
    SafeT cap (asyncifyProg P) H (1 + 4) t := by
  let c1 : Cfg := ⟨⟨fid1, tl1, ops ++ [], chk P.frameWords k nres1 ++ K, nres1⟩ :: tw',
    t.cfg.globals, t.cfg.mem⟩
  have hret : step (asyncifyProg P) t.cfg = .next c1 := by
    rw [step_ret hct rfl]
    simp [ret, c1]
  have h1 : runN (tgtStep (asyncifyProg P) H) 1 t = .next { t with cfg := c1 } := by
    simp only [runN, tgtStep, hret]
  have hsteps := steps_guardS (cap := cap) (E := asyncifyProg P)
    (fr := ⟨fid1, tl1, ops ++ [], [], nres1⟩) (rest := tw')
    (t := saveCode P.frameWords k ++ dummies nres1 ++ [.return_]) (K := K)
    (seg_guard_eq1 P tl1 (ops ++ []) t.cfg.mem) (accFree_guard 1 .eq)
  have hs4 : SafeT cap (asyncifyProg P) H 4 { t with cfg := c1 } :=
    hsteps.safeT (by simp [c1, hR.globals, chk, List.append_assoc])
  exact SafeT.trans h1 (SafeT.one (not_oob_nil hct rfl)) hs4

/-- `ret_wait_tgt` for `RelW`. -/
theorem ret_wait_tgtW {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {tw' : List Frame}
    {fid fid1 nres nres1 k : Nat} {tl tl1 ops : List W} {K : List Instr}
    (hR : RelW P H (c, s) t)
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
theorem sim_ret_waitW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw' tw' : List Frame} {fn fn1 : FnSrc} {sl tl ops sl1 tl1 : List W} {fid1 : Nat}
    {pre1 rest1 : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} {ks' : List Nat}
    (hR : RelW P H (c, s) t)
    (hcs : c.frames = ⟨f.value.val, sl, ops, [], fn.nres⟩ ::
      ⟨fid1, sl1, [], setsCode rs ++ flatS rest1 ++ fn1.tail, fn1.nres⟩ :: sw')
    (hct : t.cfg.frames = ⟨f.value.val, tl, ops, [], fn.nres⟩ ::
      ⟨fid1, tl1, [], chk P.frameWords pre1.length fn1.nres ++ setsCode rs ++
        trS (P.ctx fn1) (pre1.length + 1) rest1 ++ fn1.tail, fn1.nres⟩ :: tw')
    (hch' : Chain P fid1 t.fid ks' sw' tw') (hfn : P.fnAt f.value.val = some fn)
    (hd : ops.length = fn.nres) (hfn1 : P.fnAt fid1 = some fn1) (hloc1 : LocR P fn1 sl1 tl1)
    (hst1 : fn1.stmts = pre1 ++ Stmt.call f as rs :: rest1) (hf1 : P.imps.length ≤ f.value.val) :
    SimSafeW cap P H (c, s) t := by
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
  refine ⟨1 + 4, _, ret_wait_tgtW hR hct', ?_, Or.inl (by omega), ret_wait_safeW hR hct'⟩
  refine ⟨hR.wf, hR.host, ⟨_, _, sw', tw', _, rfl, rfl, ?_, hch'⟩, hR.globals, hR.entry,
    hR.bound.next hsrc⟩
  simpa using hT

/-- The top frame returns. -/
theorem sim_retW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl ops : List W}
    (hR : RelW P H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, [], fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, ops, [], fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hd : depthAfter [] ops.length = some fn.nres) : SimSafeW cap P H (c, s) t := by
  have hd' : ops.length = fn.nres := by simpa only [depthAfter, Option.some.injEq] using hd
  cases hch with
  | nil => exact sim_ret_bottomW hR hcs hct
  | cons hw hch' =>
    cases hw with
    | mk hfn1 hloc1 hst1 hf1 => exact sim_ret_waitW hR hcs hct hch' hfn hd' hfn1 hloc1 hst1 hf1

/-- The source reads an argument of a call statement; the target waits. -/
theorem sim_getW {cap : Nat} {P : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {sw tw : List Frame} {fid : Nat} {fn : FnSrc} {sl tl : List W} {pre rest : List Stmt}
    {f : FuncIdx} {as rs : List LocalIdx} {j : Nat} (hR : RelW P H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ((as.take j).map (lv sl)).reverse,
      (getsCode as).drop j ++ [.call f] ++ setsCode rs ++ flatS rest ++ fn.tail, fn.nres⟩ :: sw)
    (hct : t.cfg.frames = ⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
      trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw)
    {ks : List Nat} (hch : Chain P fid t.fid ks sw tw) (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hj : j < as.length) : SimSafeW cap P H (c, s) t := by
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
    hR.entry, hR.bound.next hsrc⟩, Or.inr (by simp [mu, hcs', K, getsCode]), SafeT.zero t⟩

end Silmaril.Wasm.FX.Asyncify.Tool
