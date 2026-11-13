module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.Seg

/-!
# Unwinding stays in bounds

The steps of `unwind_wait`, `unwind` and `tgt_imp_unwind` (`Silmaril.Proofs.Wasm.FX.Asyncify.Tool`)
as in-bounds steps: every record is saved below `cap` when the last one ends there, and the
request is written below `SB ≤ cap`.

New proofs (the chains of `Unwind` and `SuspendSim`, with the bound carried along).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem accFree_ret : AccFree .return_ := fun _ => rfl

theorem accFree_dummies (n : Nat) : ∀ i ∈ dummies n, AccFree i := by
  intro i hi
  have hi' : i = c32 0 := List.eq_of_mem_replicate hi
  rw [hi']
  exact accFree_c32 0

/-- The guard segments of the generated code do not access memory. -/
theorem accFree_guard (v : Nat) (op : IntRelOp) :
    ∀ i ∈ [gState, c32 v, .intRelOp .i32 op], AccFree i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact accFree_gget _
  · exact accFree_c32 _
  · exact accFree_rel _

/-- Saving a record and pushing dummy results stays in bounds. -/
theorem save_dummies_safe {cap F k a n : Nat} {tl ops : List W} {g0 : W} {mem : Nat → W}
    (hl : tl.length = F) (hF : 1 ≤ F) (ha : a + 4 * F < 2 ^ 32) (hcap : a + 4 * F ≤ cap) :
    SegSafe cap (saveCode F k ++ dummies n) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ :=
  segSafe_append (saveCode_safe hl hF ha hcap) fun _ _ => segSafe_free (accFree_dummies n)

/-- One waiting frame unwinds in bounds (`unwind_wait`). -/
theorem unwind_waitS {P : Prog} (hP : P.WF) {cap : Nat} {fid : Nat} {fn : FnSrc} {sl tl : List W}
    {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    {fr : Frame} {K : List Instr} {ts : List Frame} {mem : Nat → W} {a : Nat}
    (hcode : fr.code = .return_ :: K) (ha : a + 4 * P.frameWords < 2 ^ 32)
    (hcap : a + 4 * P.frameWords ≤ cap) :
    StepsS cap (asyncifyProg P)
      (1 + ((3 + 1) + (saveCode P.frameWords pre.length ++ dummies fn.nres).length))
      ⟨fr :: ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++ setsCode rs ++
          trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ (fr.ops.take fr.nres ++ []),
          .return_ :: (setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail),
          fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 (a + 4 * P.frameWords)],
        writeWords mem a (recOf P.frameWords pre.length tl)⟩ := by
  have hok : FnOk P fn := Prog.fnOk hP hfn
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  have hk : pre.length < 2 ^ 32 := by have := hok.pre_lt hst; omega
  have hF : 1 ≤ P.frameWords := by have := hok.nloc; omega
  let K' := setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail
  let ops := fr.ops.take fr.nres ++ []
  let save := saveCode P.frameWords pre.length ++ dummies fn.nres
  let c0 : Cfg := ⟨fr :: ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++
      setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
      [1, BitVec.ofNat 32 a], mem⟩
  have e1 : step (asyncifyProg P) c0 = .next ⟨⟨fid, tl, ops, chk P.frameWords pre.length fn.nres ++
        setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 a], mem⟩ := by
    rw [step_return rfl hcode, ret_cons]
  have ho1 : ¬ OOB cap c0 := not_oob_free (fr := fr) rfl hcode accFree_ret
  have m2 : StepsS cap (asyncifyProg P) (3 + 1)
      ⟨⟨fid, tl, ops, chk P.frameWords pre.length fn.nres ++ setsCode rs ++
        trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, ops, save ++ .return_ :: K', fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩ := by
    have e2 := steps_guardS (cap := cap) (E := asyncifyProg P) (fr := ⟨fid, tl, ops, [], fn.nres⟩)
      (rest := ts) (t := save ++ [.return_]) (K := K')
      (seg_chk_unwind tl ops (BitVec.ofNat 32 a) mem) (accFree_guard 1 .eq)
    simpa [chk, ifThen, save, K', List.append_assoc] using e2
  have m3 : StepsS cap (asyncifyProg P) save.length
      ⟨⟨fid, tl, ops, save ++ .return_ :: K', fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ ops, .return_ :: K', fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 (a + 4 * P.frameWords)],
        writeWords mem a (recOf P.frameWords pre.length tl)⟩ := by
    have e3 := steps_segS (cap := cap) (E := asyncifyProg P) (fr := ⟨fid, tl, ops, [], fn.nres⟩)
      (rest := ts) (code := .return_ :: K') (g := [1, BitVec.ofNat 32 a]) (m := mem)
      (show runSeg save _ = _ by
        rw [runSeg_append, saveCode_seg (a := a) htl hF ha hk, Option.bind_some, dummies_seg])
      (save_dummies_safe htl hF ha hcap)
    simpa using e3
  exact (StepsS.one ho1 e1).trans (m2.trans m3)

/-- The in-bounds unwinding of the frames `ts` (with records `ks`) from a frame about to
`return`. -/
def UnwindsS (cap : Nat) (P : Prog) (ks : List Nat) (ts : List Frame) : Prop :=
  ∀ (fr : Frame) (K : List Instr) (mem : Nat → W) (a : Nat), fr.code = .return_ :: K →
    fr.nres ≤ fr.ops.length → a + 4 * P.frameWords * ts.length < 2 ^ 32 →
    a + 4 * P.frameWords * ts.length ≤ cap →
    ∃ n c vs, StepsS cap (asyncifyProg P) n ⟨fr :: ts, [1, BitVec.ofNat 32 a], mem⟩ c ∧
      ¬ OOB cap c ∧
      step (asyncifyProg P) c = .done vs ⟨[], [1, BitVec.ofNat 32 (a + 4 * P.frameWords * ts.length)],
        writeRecs P.frameWords mem a (recs P.frameWords ks ts)⟩

/-- No waiting frame: the frame returns from the export call. -/
theorem unwindsS_nil {cap : Nat} {P : Prog} : UnwindsS cap P [] [] := by
  intro fr K mem a hcode _ _ _
  refine ⟨0, _, fr.ops.take fr.nres, .refl _, not_oob_free (fr := fr) rfl hcode accFree_ret, ?_⟩
  rw [step_return rfl hcode]
  simp [ret, recs, writeRecs]

/-- One more waiting frame unwinds in bounds. -/
theorem unwindsS_cons {P : Prog} (hP : P.WF) {cap : Nat} {above k : Nat} {ks : List Nat}
    {fs ft : Frame} {ts : List Frame} (hw : WaitR P above k fs ft) (ih : UnwindsS cap P ks ts) :
    UnwindsS cap P (k :: ks) (ft :: ts) := by
  intro fr K mem a hcode _ hb hc
  rcases hw with ⟨hfn, hloc, hst, -⟩
  rename_i fid fn sl tl pre rest f as rs
  have hb' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length < 2 ^ 32 := by
    rw [addr_step]; simpa using hb
  have hc' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length ≤ cap := by
    rw [addr_step]; simpa using hc
  have hw1 := unwind_waitS hP (cap := cap) hfn hloc hst (ts := ts) (mem := mem) (a := a) hcode
    (by omega) (by omega)
  obtain ⟨n, c, vs, hs, hoc, hd⟩ := ih ⟨fid, tl, List.replicate fn.nres 0 ++
    (fr.ops.take fr.nres ++ []),
    .return_ :: (setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail), fn.nres⟩ _ _
    (a + 4 * P.frameWords) rfl (by simp) hb' hc'
  refine ⟨_, c, vs, hw1.trans hs, hoc, ?_⟩
  rw [hd, List.length_cons, ← addr_step]
  rfl

/-- Unwinding a chain of waiting frames stays in bounds when the last record ends at or below
`cap` (`unwind`); the state before the final `return` is in bounds too. -/
theorem unwindS {P : Prog} (hP : P.WF) {cap : Nat} {above e : Nat} {ks : List Nat}
    {sw tw : List Frame} (hch : Chain P above e ks sw tw) : UnwindsS cap P ks tw := by
  induction hch with
  | nil e => exact unwindsS_nil
  | cons hw _ ih => exact unwindsS_cons hP hw ih

theorem accFree_req_tail : ∀ i ∈ [c32 1, sState], AccFree i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact accFree_c32 _
  · exact accFree_gset _

/-- The target at an import site writes the request and unwinds, in bounds
(`tgt_imp_unwind`). -/
theorem tgt_imp_unwindS {P : Prog} (hP : P.WF) {cap : Nat} {fid e : Nat} {fn : FnSrc}
    {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} {ks : List Nat}
    {sw tw : List Frame} {tm : Nat → W} (hch : Chain P fid e ks sw tw)
    (hfn : P.fnAt fid = some fn) (hloc : LocR P fn sl tl)
    (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest) (hf : f.value.val < P.imps.length)
    (hbd : P.sb + 4 * P.frameWords * (tw.length + 1) < 2 ^ 32)
    (hcap : P.sb + 4 * P.frameWords * (tw.length + 1) ≤ cap) :
    ∃ n cU vs, StepsS cap (asyncifyProg P) n
      ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
        trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, tm⟩ cU ∧
      ¬ OOB cap cU ∧
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
  have hle1 : P.sb + 4 * P.frameWords ≤ P.sb + 4 * P.frameWords * (tw.length + 1) := by
    have := addr_le P.sb P.frameWords tw.length; omega
  let K' := trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail
  let save := reqCode f as ++ [c32 1, sState] ++ saveCode P.frameWords pre.length ++
    dummies fn.nres
  let mem2 := writeWords (reqMem tm f.value.val (as.map (lv tl))) P.sb
    (recOf P.frameWords pre.length tl)
  have m1 : StepsS cap (asyncifyProg P) (3 + 1)
      ⟨⟨fid, tl, [], trStmt (P.ctx fn) pre.length (.call f as rs) ++
        trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, [], save ++ .return_ :: K', fn.nres⟩ :: tw, P.tGlobals, tm⟩ := by
    have e1 := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩)
      (rest := tw) (t := [.localGet (lidx (P.frameWords - 1)), c32 pre.length, eqI,
        ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)])
      (e := save ++ [.return_]) (K := K') (seg_guard_eq2 P tl [] tm) (accFree_guard 2 .eq)
    simpa [trStmt, hf, Prog.ctx, K', save, List.append_assoc] using e1
  have hseg : runSeg save ⟨tl, [], P.tGlobals, tm⟩ = some ⟨tl, List.replicate fn.nres 0,
      [1, BitVec.ofNat 32 (P.sb + 4 * P.frameWords)], mem2⟩ := by
    rw [runSeg_append, runSeg_append, tGlobals_eq, seg_req hasl (by omega), Option.bind_some,
      saveCode_seg htl hF (by omega) hk, Option.bind_some, dummies_seg]
    simp [mem2]
  have hsafe : SegSafe cap save ⟨tl, [], P.tGlobals, tm⟩ := by
    have hreqS : SegSafe cap (reqCode f as ++ [c32 1, sState]) ⟨tl, [], P.tGlobals, tm⟩ :=
      segSafe_append (reqCode_safe (by omega) (by omega) hasl) fun _ _ =>
        segSafe_free accFree_req_tail
    refine segSafe_append (segSafe_append hreqS fun s' hs' => ?_) fun _ _ =>
      segSafe_free (accFree_dummies fn.nres)
    rw [tGlobals_eq, seg_req hasl (by omega)] at hs'
    rw [← Option.some.inj hs']
    exact saveCode_safe htl hF (by omega) (by omega)
  have m2 : StepsS cap (asyncifyProg P) save.length
      ⟨⟨fid, tl, [], save ++ .return_ :: K', fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ [], .return_ :: K', fn.nres⟩ :: tw,
        [1, BitVec.ofNat 32 (P.sb + 4 * P.frameWords)], mem2⟩ := by
    simpa using steps_segS (cap := cap) (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩)
      (rest := tw) (code := .return_ :: K') hseg hsafe
  obtain ⟨nU, cU, vs, eU, hoU, hdone⟩ := unwindS hP (cap := cap) hch ⟨fid, tl,
    List.replicate fn.nres 0 ++ [], .return_ :: K', fn.nres⟩ K' mem2 (P.sb + 4 * P.frameWords) rfl
    (by simp) (by have := addr_step P.sb P.frameWords tw.length; omega)
    (by have := addr_step P.sb P.frameWords tw.length; omega)
  exact ⟨_, cU, vs, m1.trans (m2.trans eU), hoU, hdone⟩

end Silmaril.Wasm.FX.Asyncify.Tool
