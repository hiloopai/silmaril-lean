module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.SelSim.Normal

/-!
# The selective simulation: a calm call in progress

The cases of `RelS` in its second shape (`FramesC`): the top frame of the segment runs in
lockstep with the target, which executes the same instructions.

* `sim_lf_pure`: a pure instruction (both trap, or both continue);
* `sim_lf_call`: a call of a calm function: the source enters the callee; the target enters it
  and passes its prologue (normal mode), so the callee's frames are related at their first
  statement;
* `sim_lf_ret`: a calm frame falls off the end of its body and returns to the frame below;
* `sim_lf_open`: a calm frame opens its next statement, which is pure (`SelOk.calmPure`): the
  target passes the guard `state ≠ 2`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type} {C : Nat → Prop}

/-! ## Segments -/

/-- Replace the top frame pair of a segment (same function, same result count). -/
theorem Seg.replace {Q : Prog} {m m' b : Nat} {fs ft fs' ft' : Frame} {xs ts : List Frame}
    (h : Seg Q C m (fs :: xs) (ft :: ts) b) (hl : LF Q C m' fs' ft') (hfid : fs'.fid = fs.fid)
    (hnres : fs'.nres = fs.nres) : Seg Q C m' (fs' :: xs) (ft' :: ts) b := by
  cases h with
  | one _ => rw [← hfid]; exact .one hl
  | cons hc _ hs => exact .cons (hfid ▸ hc) hl (hnres ▸ hs)

/-- Results pushed on a frame that waited for them. -/
theorem LF.push {Q : Prog} {m : Nat} {fr fr' : Frame} (h : LF Q C m fr fr') {vs : List W}
    (hv : vs.length = m) :
    LF Q C 0 { fr with ops := vs ++ fr.ops } { fr' with ops := vs ++ fr'.ops } := by
  cases h with
  | run hfn hloc hst hp hd =>
    exact .run hfn hloc hst hp (by rw [List.length_append, hv, Nat.add_zero, Nat.add_comm]; exact hd)
  | fin hfn hloc hq hd =>
    exact .fin hfn hloc hq (by rw [List.length_append, hv, Nat.add_zero, Nat.add_comm]; exact hd)

theorem LF.fid {Q : Prog} {m : Nat} {fr fr' : Frame} (h : LF Q C m fr fr') :
    fr'.fid = fr.fid ∧ fr'.nres = fr.nres ∧ fr'.ops = fr.ops := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

/-- The relation in the second shape, from its parts. -/
theorem RelS.ofSeg {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {x' : Cfg × σ}
    {t' : TSt σ} {ss tt sw tw : List Frame} {b : Nat} {ks : List Nat}
    (hR : RelS Q C H (c, s) t) (hx : srcStep Q.env H (c, s) = .next x') (hfid : t'.fid = t.fid)
    (hargs : t'.args = t.args) (hhost : t'.host = x'.2) (hg : t'.cfg.globals = Q.tGlobals)
    (hxs : x'.1.frames = ss ++ sw) (hts : t'.cfg.frames = tt ++ tw) (hseg : Seg Q C 0 ss tt b)
    (hch : Chain Q b t.fid ks sw tw) : RelS Q C H x' t' :=
  ⟨hR.ok, hhost, .inr ⟨ss, tt, sw, tw, b, ks, hxs, hts, hseg, hfid ▸ hch⟩, hg,
    by rw [hfid, hargs]; exact hR.entry, hR.bound.next hx⟩

/-! ## A pure instruction in lockstep -/

/-- A pure instruction that traps, in both machines. -/
theorem sim_lf_trap {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ} {rs rt : List Frame}
    {fid nres S : Nat} {sl ex ops : List W} {i : Instr} {cs ct : List Instr}
    (hR : RelS Q C H (c, s) t) (hcs : c.frames = ⟨fid, sl, ops, i :: cs, nres⟩ :: rs)
    (hct : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, nres⟩ :: rt)
    (hl : sl.length = S) (hi : PureShape S i) (hp : pexec i sl ops = none) :
    SimOkS Q C H (c, s) t := by
  have hctl : ctlOf i = none := ctlOf_pure hi
  have hs : step Q.env c = .trap := step_trap_seg hcs rfl hctl (by
    rw [segStep_pure hi]; simp [Frame.ls, hp])
  have ht : step (asyncifyProg Q) t.cfg = .trap := step_trap_seg hct rfl hctl (by
    rw [segStep_pure hi]; simp [Frame.ls, pexec_ext hi hl, hp])
  have hsrc : srcStep Q.env H (c, s) = .stop (.trap s) := by simp only [srcStep, hs]
  have htgt : runN (tgtStep (asyncifyProg Q) H) 1 t = .stop (.trap s) := by
    simp [runN, tgtStep, ht, hR.host]
  refine ⟨fun o ho => ⟨1, ?_⟩, fun x' hx => ?_⟩
  · rw [← SRes.stop.inj (hsrc.symm.trans ho)]
    exact htgt
  · cases hsrc.symm.trans hx

/-- A pure instruction at the top of a segment. -/
theorem sim_lf_pure {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat} {fid nres S : Nat} {sl ex ops : List W}
    {i : Instr} {cs ct : List Instr} (hR : RelS Q C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, i :: cs, nres⟩ :: (xs ++ sw))
    (hct : t.cfg.frames = ⟨fid, sl ++ ex, ops, i :: ct, nres⟩ :: (ts ++ tw))
    (hseg : Seg Q C 0 (⟨fid, sl, ops, i :: cs, nres⟩ :: xs) (⟨fid, sl ++ ex, ops, i :: ct, nres⟩ :: ts) b)
    (hch : Chain Q b t.fid ks sw tw) (hl : sl.length = S) (hi : PureShape S i)
    (hnext : ∀ sl' ops', pexec i sl ops = some (sl', ops') → sl'.length = S →
      LF Q C 0 ⟨fid, sl', ops', cs, nres⟩ ⟨fid, sl' ++ ex, ops', ct, nres⟩) :
    SimOkS Q C H (c, s) t := by
  cases hp : pexec i sl ops with
  | none => exact sim_lf_trap hR hcs hct hl hi hp
  | some r =>
    show SimOkS Q C H (c, s) t
    obtain ⟨sl', ops'⟩ := r
    have hs : step Q.env c = .next ⟨⟨fid, sl', ops', cs, nres⟩ :: (xs ++ sw), c.globals, c.mem⟩ :=
      step_seg hcs rfl (s' := ⟨sl', ops', c.globals, c.mem⟩) (by
        rw [segStep_pure hi]; simp [Frame.ls, hp])
    have ht : step (asyncifyProg Q) t.cfg =
        .next ⟨⟨fid, sl' ++ ex, ops', ct, nres⟩ :: (ts ++ tw), t.cfg.globals, t.cfg.mem⟩ :=
      step_seg hct rfl (s' := ⟨sl' ++ ex, ops', t.cfg.globals, t.cfg.mem⟩) (by
        rw [segStep_pure hi]; simp [Frame.ls, pexec_ext hi hl, hp])
    have hl' : sl'.length = S := by rw [pexec_len hi hp]; exact hl
    have hsrc : srcStep Q.env H (c, s) =
        .next (⟨⟨fid, sl', ops', cs, nres⟩ :: (xs ++ sw), c.globals, c.mem⟩, s) := by
      simp only [srcStep, hs]
    refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
    rw [← SRes.next.inj (hsrc.symm.trans hx)]
    refine ⟨1, _, by simp only [runN, tgtStep, ht]; rfl, ?_, Or.inl Nat.one_pos⟩
    exact RelS.ofSeg hR hsrc rfl rfl hR.host hR.globals (ss := ⟨fid, sl', ops', cs, nres⟩ :: xs)
      (tt := ⟨fid, sl' ++ ex, ops', ct, nres⟩ :: ts) rfl rfl
      (hseg.replace (hnext sl' ops' hp hl') rfl rfl) hch

/-! ## A calm call in lockstep -/

theorem effC_call {Q : Prog} {g : FuncIdx} {n m : Nat} (h : Q.sig g.value.val = some (n, m)) :
    effC Q (.call g) = (n, m) := by
  simp [effC, h]

theorem Prog.sig_of_fnAt {Q : Prog} {g : Nat} {fn : FnSrc} (h : Q.fnAt g = some fn) :
    Q.sig g = some (fn.nparams, fn.nres) := by
  have hge := Prog.fnAt_ge h
  unfold Prog.fnAt at h
  simp only [hge, ↓reduceIte] at h
  simp [Prog.sig, show ¬ g < Q.imps.length by omega, h]

/-- A call of a calm function at the top of a segment: the source enters the callee, the target
enters it and passes its prologue. -/
theorem sim_lf_call {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat} {fid : Nat} {fn : FnSrc}
    {sl tl ops : List W} {g : FuncIdx} {p : List Instr} {pre rest : List Stmt}
    (hR : RelS Q C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, (.call g :: p) ++ flatS rest ++ fn.tail, fn.nres⟩ :: (xs ++ sw))
    (hct : t.cfg.frames =
      ⟨fid, tl, ops, (.call g :: p) ++ trS (Q.ctx fn) pre.length rest ++ fn.tail, fn.nres⟩ :: (ts ++ tw))
    (hseg : Seg Q C 0 (⟨fid, sl, ops, (.call g :: p) ++ flatS rest ++ fn.tail, fn.nres⟩ :: xs)
      (⟨fid, tl, ops, (.call g :: p) ++ trS (Q.ctx fn) pre.length rest ++ fn.tail, fn.nres⟩ :: ts) b)
    (hch : Chain Q b t.fid ks sw tw) (hfn : Q.fnAt fid = some fn) (hloc : LocR Q fn sl tl)
    (hst : fn.stmts = pre ++ rest) (hp : ∀ j ∈ p, cIns C fn.nloc j)
    (hd : depthC Q (.call g :: p) (ops.length + 0) = some 0) (hg : C g.value.val) :
    SimOkS Q C H (c, s) t := by
  have hQ := hR.ok
  obtain ⟨gfn, hgfn⟩ := hQ.calmFn hg
  have hge := Prog.fnAt_ge hgfn
  have hsig := Prog.sig_of_fnAt hgfn
  have hokg := hQ.fn hgfn
  rw [depthC, effC_call hsig] at hd
  have hnp : gfn.nparams ≤ ops.length := by
    by_contra h; simp only [show ¬ gfn.nparams ≤ ops.length + 0 by omega, ite_false] at hd; cases hd
  simp only [show gfn.nparams ≤ ops.length + 0 by omega, ite_true] at hd
  have hF2 : Q.frameWords < 2 ^ 32 := by have := hQ.bounds.2; omega
  let args := (ops.take gfn.nparams).reverse
  let K := p ++ flatS rest ++ fn.tail
  let K' := p ++ trS (Q.ctx fn) pre.length rest ++ fn.tail
  have himp : ¬ g.value.val < Q.imps.length := by omega
  have hs : step Q.env c = .next ⟨entry g.value.val ⟨gfn.nparams, gfn.nlocals, gfn.nres, gfn.body⟩
      args :: ⟨fid, sl, ops.drop gfn.nparams, K, fn.nres⟩ :: (xs ++ sw), c.globals, c.mem⟩ :=
    step_call_def (E := Q.env) (fr := ⟨fid, sl, ops, .call g :: K, fn.nres⟩) hcs rfl himp
      (by simpa using Prog.env_fn hgfn) hnp
  have hsrc : srcStep Q.env H (c, s) = .next (⟨entry g.value.val ⟨gfn.nparams, gfn.nlocals,
      gfn.nres, gfn.body⟩ args :: ⟨fid, sl, ops.drop gfn.nparams, K, fn.nres⟩ :: (xs ++ sw),
      c.globals, c.mem⟩, s) := by
    simp only [srcStep, hs]
  have ht : step (asyncifyProg Q) t.cfg = .next ⟨entry g.value.val (tdef Q gfn) args ::
      ⟨fid, tl, ops.drop gfn.nparams, K', fn.nres⟩ :: (ts ++ tw), t.cfg.globals, t.cfg.mem⟩ :=
    step_call_def (E := asyncifyProg Q) (fr := ⟨fid, tl, ops, .call g :: K', fn.nres⟩) hct rfl
      (by simpa [asyncifyProg] using himp) (by simpa [tdef] using Prog.tgt_fn hgfn)
      (by simpa [tdef] using hnp)
  have hpro : Steps (asyncifyProg Q) (3 + 1)
      ⟨entry g.value.val (tdef Q gfn) args :: ⟨fid, tl, ops.drop gfn.nparams, K', fn.nres⟩ ::
        (ts ++ tw), Q.tGlobals, t.cfg.mem⟩
      ⟨⟨g.value.val, args ++ List.replicate (Q.frameWords - gfn.nparams) 0, [],
        trS (Q.ctx gfn) 0 gfn.stmts ++ gfn.tail, gfn.nres⟩ ::
        ⟨fid, tl, ops.drop gfn.nparams, K', fn.nres⟩ :: (ts ++ tw), Q.tGlobals, t.cfg.mem⟩ := by
    have e4 := steps_guard (E := asyncifyProg Q) (fr := entry g.value.val (tdef Q gfn) args)
      (rest := ⟨fid, tl, ops.drop gfn.nparams, K', fn.nres⟩ :: (ts ++ tw))
      (t := restoreCode Q.frameWords) (K := trS (Q.ctx gfn) 0 gfn.stmts ++ gfn.tail)
      (seg_prologue_normal Q _ t.cfg.mem)
    simpa [entry, tdef, Prog.tBody, prologue, ifThen] using e4
  have hlen : args.length = gfn.nparams := by simp [args, hnp]
  have hcallee : LF Q C 0 (entry g.value.val ⟨gfn.nparams, gfn.nlocals, gfn.nres, gfn.body⟩ args)
      ⟨g.value.val, args ++ List.replicate (Q.frameWords - gfn.nparams) 0, [],
        trS (Q.ctx gfn) 0 gfn.stmts ++ gfn.tail, gfn.nres⟩ := by
    have h := LF.run (C := C) (m := 0) (ops := []) (p := []) (pre := []) (rest := gfn.stmts) hgfn
      (LocR.ofEntry (P := Q) hokg.nloc rfl hlen) (by simp) (by simp) (by simp [depthC])
    simpa [entry, FnSrc.body] using h
  have hcaller : LF Q C gfn.nres ⟨fid, sl, ops.drop gfn.nparams, K, fn.nres⟩
      ⟨fid, tl, ops.drop gfn.nparams, K', fn.nres⟩ :=
    LF.run hfn hloc hst hp (by rw [List.length_drop]; simpa using hd)
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  have hrun : runN (tgtStep (asyncifyProg Q) H) (1 + (3 + 1)) t = .next { t with cfg :=
      ⟨⟨g.value.val, args ++ List.replicate (Q.frameWords - gfn.nparams) 0, [],
        trS (Q.ctx gfn) 0 gfn.stmts ++ gfn.tail, gfn.nres⟩ ::
        ⟨fid, tl, ops.drop gfn.nparams, K', fn.nres⟩ :: (ts ++ tw), Q.tGlobals, t.cfg.mem⟩ } := by
    rw [runN_add_next (m := 1) (by simp only [runN, tgtStep, ht]; rfl)]
    rw [hR.globals]
    exact hpro.tgt_of rfl
  refine ⟨_, _, hrun, ?_, Or.inl (by omega)⟩
  exact RelS.ofSeg hR hsrc rfl rfl hR.host rfl
    (ss := entry g.value.val ⟨gfn.nparams, gfn.nlocals, gfn.nres, gfn.body⟩ args ::
      ⟨fid, sl, ops.drop gfn.nparams, K, fn.nres⟩ :: xs)
    (tt := ⟨g.value.val, args ++ List.replicate (Q.frameWords - gfn.nparams) 0, [],
        trS (Q.ctx gfn) 0 gfn.stmts ++ gfn.tail, gfn.nres⟩ ::
        ⟨fid, tl, ops.drop gfn.nparams, K', fn.nres⟩ :: ts) rfl rfl
    (.cons hg hcallee (hseg.replace hcaller rfl rfl)) hch

/-- A step of lockstep code at the top of a segment. -/
theorem sim_lf_run {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat} {fid : Nat} {fn : FnSrc}
    {sl tl ops : List W} {i : Instr} {p : List Instr} {pre rest : List Stmt}
    (hR : RelS Q C H (c, s) t)
    (hcs : c.frames = ⟨fid, sl, ops, (i :: p) ++ flatS rest ++ fn.tail, fn.nres⟩ :: (xs ++ sw))
    (hct : t.cfg.frames =
      ⟨fid, tl, ops, (i :: p) ++ trS (Q.ctx fn) pre.length rest ++ fn.tail, fn.nres⟩ :: (ts ++ tw))
    (hseg : Seg Q C 0 (⟨fid, sl, ops, (i :: p) ++ flatS rest ++ fn.tail, fn.nres⟩ :: xs)
      (⟨fid, tl, ops, (i :: p) ++ trS (Q.ctx fn) pre.length rest ++ fn.tail, fn.nres⟩ :: ts) b)
    (hch : Chain Q b t.fid ks sw tw) (hfn : Q.fnAt fid = some fn) (hloc : LocR Q fn sl tl)
    (hst : fn.stmts = pre ++ rest) (hp : ∀ j ∈ i :: p, cIns C fn.nloc j)
    (hd : depthC Q (i :: p) (ops.length + 0) = some 0) : SimOkS Q C H (c, s) t := by
  rcases hp i (by simp) with hpi | ⟨g, rfl, hg⟩
  · have hi := pureShape hpi
    obtain ⟨hl, ex, rfl, hex⟩ := hloc
    refine sim_lf_pure (cs := p ++ flatS rest ++ fn.tail)
      (ct := p ++ trS (Q.ctx fn) pre.length rest ++ fn.tail) hR hcs hct hseg hch hl hi ?_
    intro sl' ops' he hl'
    exact LF.run hfn ⟨hl', ex, rfl, hex⟩ hst (fun j hj => hp j (by simp [hj]))
      (depthC_cons hi hd he)
  · exact sim_lf_call hR hcs hct hseg hch hfn hloc hst (fun j hj => hp j (by simp [hj])) hd hg

/-! ## Returns and statements of calm frames -/

/-- A calm frame at the top of a segment falls off the end of its body. -/
theorem sim_lf_ret {Q : Prog} {H : Host σ} {c : Cfg} {s : σ} {t : TSt σ}
    {fs ft fs2 ft2 : Frame} {xs ts sw tw : List Frame} {b : Nat} {ks : List Nat}
    (hR : RelS Q C H (c, s) t) (hcs : c.frames = fs :: fs2 :: (xs ++ sw))
    (hct : t.cfg.frames = ft :: ft2 :: (ts ++ tw)) (hcode : fs.code = []) (hcodet : ft.code = [])
    (hops : ft.ops = fs.ops) (hlen : fs.ops.length = fs.nres)
    (hseg : Seg Q C fs.nres (fs2 :: xs) (ft2 :: ts) b) (hch : Chain Q b t.fid ks sw tw) :
    SimOkS Q C H (c, s) t := by
  have hs : step Q.env c = .next { c with frames := { fs2 with ops := fs.ops ++ fs2.ops } ::
      (xs ++ sw) } := by rw [step_ret hcs hcode]; rfl
  have ht : step (asyncifyProg Q) t.cfg = .next { t.cfg with frames :=
      { ft2 with ops := fs.ops ++ ft2.ops } :: (ts ++ tw) } := by
    rw [step_ret hct hcodet, hops]; rfl
  have hsrc : srcStep Q.env H (c, s) = .next ({ c with frames := { fs2 with ops := fs.ops ++
      fs2.ops } :: (xs ++ sw) }, s) := by simp only [srcStep, hs]
  refine ⟨fun o ho => (by cases hsrc.symm.trans ho), fun x' hx => ?_⟩
  rw [← SRes.next.inj (hsrc.symm.trans hx)]
  refine ⟨1, _, by simp only [runN, tgtStep, ht]; rfl, ?_, Or.inl Nat.one_pos⟩
  have hl2 : LF Q C fs.nres fs2 ft2 := by cases hseg <;> assumption
  exact RelS.ofSeg hR hsrc rfl rfl hR.host hR.globals
    (ss := { fs2 with ops := fs.ops ++ fs2.ops } :: xs)
    (tt := { ft2 with ops := fs.ops ++ ft2.ops } :: ts) rfl rfl
    (hseg.replace (hl2.push hlen) rfl rfl) hch

end Silmaril.Wasm.FX.Asyncify.Tool
