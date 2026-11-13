module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.Main

/-!
# Unwinding with a wrapping `sp`: records below `2 ^ 32`, the last one may end above it

The in-bounds unwinding of `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits` asks that every record
*ends* below `2 ^ 32` (`a + 4 F < 2 ^ 32`). Saving and restoring a record at `a` only reads `sp`
as the natural number `a`, so `a < 2 ^ 32` is enough: `sp` is then bumped to
`BitVec.ofNat 32 (a + 4 F)`, which may wrap, and popped back by `sub_ofNat32`, which works
modulo `2 ^ 32`. Here the leaf segments (`saveCode_segW`, `saveCode_safeW`,
`restoreCode_safeW`, `steps_prologue_rwW`) and the unwinding chain (`unwindW`,
`tgt_imp_unwindW`) with that weaker bound: a chain of `d` records at `a, a + 4F, …` needs
`a + 4 F · d < 2 ^ 32 + 4 F`.

New proofs (copies of `Fits/Seg`, `Fits/Unwind` and `Unwind.saveCode_seg` with the weaker bound).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- `saveCode_seg` for a record that starts below `2 ^ 32`. -/
theorem saveCode_segW {F k a : Nat} {tl ops : List W} {g0 : W} {mem : Nat → W}
    (hl : tl.length = F) (hF : 1 ≤ F) (hF4 : 4 * F < 2 ^ 32) (ha : a < 2 ^ 32) :
    runSeg (saveCode F k) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ =
      some ⟨tl, ops, [g0, BitVec.ofNat 32 (a + 4 * F)], writeWords mem a (recOf F k tl)⟩ := by
  have hsp : ([g0, BitVec.ofNat 32 a] : List W)[1]? = some (BitVec.ofNat 32 a) := rfl
  have hta : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 ha
  unfold saveCode
  rw [runSeg_append, saveLocals_seg hsp (by omega) (by omega), Option.bind_some, hta]
  simp only [Nat.mul_zero, Nat.add_zero, List.drop_zero]
  have hseg : runSeg [gSp, c32 k, st (4 * (F - 1)), gSp, c32 (4 * F), addI, sSp]
      ⟨tl, ops, [g0, BitVec.ofNat 32 a], writeWords mem a (tl.take (F - 1))⟩ =
      some ⟨tl, ops, [g0, BitVec.ofNat 32 (a + 4 * F)],
        upd (writeWords mem a (tl.take (F - 1))) (a + 4 * (F - 1)) (BitVec.ofNat 32 k)⟩ := by
    have hadd : BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * F) = BitVec.ofNat 32 (a + 4 * F) :=
      BitVec.ofNat_add_ofNat _ _
    simp [runSeg, segStep, ctlOf, segCore, gSp, sSp, c32, st, addI, pexec, Numerics.intBinOp,
      hta, marg_off (show 4 * (F - 1) < 2 ^ 64 by omega)]
    rw [← hadd]; rfl
  rw [hseg]
  congr 2
  rw [recOf, writeWords_append, List.length_take, hl, Nat.min_eq_left (by omega)]
  rfl

/-- `saveSel_safe` for a record that starts below `2 ^ 32`. -/
theorem saveSel_safeW {cap F k a : Nat} {tl ops : List W} {g0 : W} {mem : Nat → W}
    (hF : 1 ≤ F) (hF4 : 4 * F < 2 ^ 32) (ha : a < 2 ^ 32) (hcap : a + 4 * F ≤ cap) :
    SegSafe cap ([gSp, c32 k, st (4 * (F - 1))] ++ [gSp, c32 (4 * F), addI, sSp])
      ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ := by
  have hsp : ([g0, BitVec.ofNat 32 a] : List W)[1]? = some (BitVec.ofNat 32 a) := rfl
  have hta : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 ha
  refine segSafe_append (segSafe_st (accFree_gget _) (accFree_c32 _) (by omega)
    fun s1 e1 s2 e2 => ?_) fun _ _ => segSafe_free accFree_push
  have h1 : s1 = ⟨tl, BitVec.ofNat 32 a :: ops, [g0, BitVec.ofNat 32 a], mem⟩ :=
    Option.some.inj (e1.symm.trans (segStep_gSp hsp))
  have h2 : s2 = { s1 with ops := BitVec.ofNat 32 k :: s1.ops } :=
    Option.some.inj (e2.symm.trans segStep_c32)
  have hops : s2.ops = BitVec.ofNat 32 k :: BitVec.ofNat 32 a :: ops := by rw [h2, h1]
  exact ⟨_, _, _, hops, by rw [hta]; omega⟩

/-- `saveCode_safe` for a record that starts below `2 ^ 32`. -/
theorem saveCode_safeW {cap F k a : Nat} {tl ops : List W} {g0 : W} {mem : Nat → W}
    (hl : tl.length = F) (hF : 1 ≤ F) (hF4 : 4 * F < 2 ^ 32) (ha : a < 2 ^ 32)
    (hcap : a + 4 * F ≤ cap) :
    SegSafe cap (saveCode F k) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ := by
  have hsp : ([g0, BitVec.ofNat 32 a] : List W)[1]? = some (BitVec.ofNat 32 a) := rfl
  have hta : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 ha
  let mem1 := writeWords mem ((BitVec.ofNat 32 a).toNat + 4 * 0) ((tl.drop 0).take (F - 1))
  have hrun : runSeg (saveLocals 0 (F - 1)) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ =
      some ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem1⟩ :=
    saveLocals_seg hsp (by omega) (by omega)
  have hsave : SegSafe cap (saveLocals 0 (F - 1)) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ :=
    saveLocals_safe hsp (by omega) (by omega) (by omega)
  have htail : SegSafe cap ([gSp, c32 k, st (4 * (F - 1))] ++ [gSp, c32 (4 * F), addI, sSp])
      ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem1⟩ := saveSel_safeW hF hF4 ha hcap
  unfold saveCode
  exact segSafe_append hsave fun s' hs' => (Option.some.inj (hs'.symm.trans hrun)) ▸ htail

/-- `restoreCode_safe` for a record that starts below `2 ^ 32`. -/
theorem restoreCode_safeW {cap F a : Nat} {ls ops : List W} {g0 : W} {mem : Nat → W}
    (hl : ls.length = F) (hF4 : 4 * F < 2 ^ 32) (ha : a < 2 ^ 32) (hcap : a + 4 * F ≤ cap) :
    SegSafe cap (restoreCode F) ⟨ls, ops, [g0, BitVec.ofNat 32 (a + 4 * F)], mem⟩ := by
  unfold restoreCode
  have h1 : runSeg [gSp, c32 (4 * F), subI, sSp] ⟨ls, ops, [g0, BitVec.ofNat 32 (a + 4 * F)], mem⟩ =
      some ⟨ls, ops, [g0, BitVec.ofNat 32 a], mem⟩ := by
    have hs := sub_ofNat32 a (4 * F)
    simp only [runSeg, segStep, ctlOf, segCore, gSp, sSp, c32, subI, pexec, Numerics.intBinOp]
    simp only [Option.bind_some]
    rw [← hs]; rfl
  refine segSafe_append (segSafe_free fun j hj => ?_) fun s' hs' => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact accFree_gget _
    · exact accFree_c32 _
    · exact accFree_bin _
    · exact accFree_gset _
  · have hs : s' = ⟨ls, ops, [g0, BitVec.ofNat 32 a], mem⟩ := Option.some.inj (hs'.symm.trans h1)
    rw [hs]
    exact loadLocals_safe (sp := BitVec.ofNat 32 a) rfl (by simp [hl]) (by omega)
      (by rw [toNat_ofNat32 ha]; omega)

/-- `steps_prologue_rwS` for a record that starts below `2 ^ 32`. -/
theorem steps_prologue_rwW {cap : Nat} {E : Env} {fr : Frame} {rest : List Frame}
    {K : List Instr} {F a : Nat} {M : Nat → W} (hl : fr.locals.length = F) (hF4 : 4 * F < 2 ^ 32)
    (ha : a < 2 ^ 32) (hcap : a + 4 * F ≤ cap) :
    ∃ n, StepsS cap E n
      ⟨{ fr with code := prologue F ++ K } :: rest, [2, BitVec.ofNat 32 (a + 4 * F)], M⟩
      ⟨{ fr with locals := readWords M a F, code := K } :: rest, [2, BitVec.ofNat 32 a], M⟩ := by
  have e1 := steps_iteS (cap := cap) (E := E) (fr := fr) (rest := rest) (t := restoreCode F)
    (e := []) (K := K) (seg_eq2_rw fr.locals fr.ops (BitVec.ofNat 32 (a + 4 * F)) M)
    (accFree_guard 2 .eq)
  have hseg : runSeg (restoreCode F) ⟨fr.locals, fr.ops, [2, BitVec.ofNat 32 (a + 4 * F)], M⟩ =
      some ⟨readWords M a F, fr.ops, [2, BitVec.ofNat 32 a], M⟩ := by
    unfold restoreCode
    rw [runSeg_append]
    have h1 : runSeg [gSp, c32 (4 * F), subI, sSp] ⟨fr.locals, fr.ops,
        [2, BitVec.ofNat 32 (a + 4 * F)], M⟩ = some ⟨fr.locals, fr.ops, [2, BitVec.ofNat 32 a], M⟩ := by
      have hs := sub_ofNat32 a (4 * F)
      simp only [runSeg, segStep, ctlOf, segCore, gSp, sSp, c32, subI, pexec, Numerics.intBinOp]
      simp only [Option.bind_some]
      rw [← hs]; rfl
    rw [h1, Option.bind_some, loadLocals_seg (sp := BitVec.ofNat 32 a) rfl (by simp [hl])
      (by omega), toNat_ofNat32 ha]
    simp
  have e2 := steps_segS (cap := cap) (E := E) (fr := { fr with code := [] }) (rest := rest)
    (code := K) hseg (restoreCode_safeW hl hF4 ha hcap)
  exact ⟨_, StepsS.trans (by simpa [prologue, ifThen] using e1) (by simpa using e2)⟩

/-- Saving a record that starts below `2 ^ 32` and pushing dummy results stays in bounds. -/
theorem save_dummies_safeW {cap F k a n : Nat} {tl ops : List W} {g0 : W} {mem : Nat → W}
    (hl : tl.length = F) (hF : 1 ≤ F) (hF4 : 4 * F < 2 ^ 32) (ha : a < 2 ^ 32)
    (hcap : a + 4 * F ≤ cap) :
    SegSafe cap (saveCode F k ++ dummies n) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ :=
  segSafe_append (saveCode_safeW hl hF hF4 ha hcap) fun _ _ => segSafe_free (accFree_dummies n)

/-- The frame size of a well-formed program fits in 22 bits. -/
theorem Prog.frame4_lt {P : Prog} (hP : P.WF) : 4 * P.frameWords < 2 ^ 32 := by
  have := (Prog.wf_bounds hP).2; omega

/-- One waiting frame unwinds in bounds, its record starting below `2 ^ 32` (`unwind_waitS`). -/
theorem unwind_waitW {P : Prog} (hP : P.WF) {cap : Nat} {fid : Nat} {fn : FnSrc} {sl tl : List W}
    {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    {fr : Frame} {K : List Instr} {ts : List Frame} {mem : Nat → W} {a : Nat}
    (hcode : fr.code = .return_ :: K) (ha : a < 2 ^ 32)
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
  have hF4 := Prog.frame4_lt hP
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
        rw [runSeg_append, saveCode_segW (a := a) htl hF hF4 ha, Option.bind_some, dummies_seg])
      (save_dummies_safeW htl hF hF4 ha hcap)
    simpa using e3
  exact (StepsS.one ho1 e1).trans (m2.trans m3)

/-- The in-bounds unwinding of the frames `ts` (with records `ks`) from a frame about to
`return`, every record starting below `2 ^ 32` (`UnwindsS` with the weaker bound). -/
def UnwindsW (cap : Nat) (P : Prog) (ks : List Nat) (ts : List Frame) : Prop :=
  ∀ (fr : Frame) (K : List Instr) (mem : Nat → W) (a : Nat), fr.code = .return_ :: K →
    fr.nres ≤ fr.ops.length → a + 4 * P.frameWords * ts.length < 2 ^ 32 + 4 * P.frameWords →
    a + 4 * P.frameWords * ts.length ≤ cap →
    ∃ n c vs, StepsS cap (asyncifyProg P) n ⟨fr :: ts, [1, BitVec.ofNat 32 a], mem⟩ c ∧
      ¬ OOB cap c ∧
      step (asyncifyProg P) c = .done vs ⟨[], [1, BitVec.ofNat 32 (a + 4 * P.frameWords * ts.length)],
        writeRecs P.frameWords mem a (recs P.frameWords ks ts)⟩

theorem unwindsW_nil {cap : Nat} {P : Prog} : UnwindsW cap P [] [] := by
  intro fr K mem a hcode _ _ _
  refine ⟨0, _, fr.ops.take fr.nres, .refl _, not_oob_free (fr := fr) rfl hcode accFree_ret, ?_⟩
  rw [step_return rfl hcode]
  simp [ret, recs, writeRecs]

theorem unwindsW_cons {P : Prog} (hP : P.WF) {cap : Nat} {above k : Nat} {ks : List Nat}
    {fs ft : Frame} {ts : List Frame} (hw : WaitR P above k fs ft) (ih : UnwindsW cap P ks ts) :
    UnwindsW cap P (k :: ks) (ft :: ts) := by
  intro fr K mem a hcode _ hb hc
  rcases hw with ⟨hfn, hloc, hst, -⟩
  rename_i fid fn sl tl pre rest f as rs
  have hb' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length <
      2 ^ 32 + 4 * P.frameWords := by
    rw [addr_step]; simpa using hb
  have hc' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length ≤ cap := by
    rw [addr_step]; simpa using hc
  have hw1 := unwind_waitW hP (cap := cap) hfn hloc hst (ts := ts) (mem := mem) (a := a) hcode
    (by omega) (by omega)
  obtain ⟨n, c, vs, hs, hoc, hd⟩ := ih ⟨fid, tl, List.replicate fn.nres 0 ++
    (fr.ops.take fr.nres ++ []),
    .return_ :: (setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail), fn.nres⟩ _ _
    (a + 4 * P.frameWords) rfl (by simp) hb' hc'
  refine ⟨_, c, vs, hw1.trans hs, hoc, ?_⟩
  rw [hd, List.length_cons, ← addr_step]
  rfl

/-- Unwinding a chain of waiting frames whose records start below `2 ^ 32` (`unwindS`). -/
theorem unwindW {P : Prog} (hP : P.WF) {cap : Nat} {above e : Nat} {ks : List Nat}
    {sw tw : List Frame} (hch : Chain P above e ks sw tw) : UnwindsW cap P ks tw := by
  induction hch with
  | nil e => exact unwindsW_nil
  | cons hw _ ih => exact unwindsW_cons hP hw ih

/-- The target at an import site writes the request and unwinds in bounds, the last record
starting below `2 ^ 32` (`tgt_imp_unwindS` with `SB + 4 F · depth < 2 ^ 32 + 4 F`). -/
theorem tgt_imp_unwindW {P : Prog} (hP : P.WF) {cap : Nat} {fid e : Nat} {fn : FnSrc}
    {sl tl : List W} {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} {ks : List Nat}
    {sw tw : List Frame} {tm : Nat → W} (hch : Chain P fid e ks sw tw)
    (hfn : P.fnAt fid = some fn) (hloc : LocR P fn sl tl)
    (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest) (hf : f.value.val < P.imps.length)
    (hbd : P.sb + 4 * P.frameWords * (tw.length + 1) < 2 ^ 32 + 4 * P.frameWords)
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
  have hF4 := Prog.frame4_lt hP
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
      saveCode_segW htl hF hF4 (by omega), Option.bind_some, dummies_seg]
    simp [mem2]
  have hsafe : SegSafe cap save ⟨tl, [], P.tGlobals, tm⟩ := by
    have hreqS : SegSafe cap (reqCode f as ++ [c32 1, sState]) ⟨tl, [], P.tGlobals, tm⟩ :=
      segSafe_append (reqCode_safe (by omega) (by omega) hasl) fun _ _ =>
        segSafe_free accFree_req_tail
    refine segSafe_append (segSafe_append hreqS fun s' hs' => ?_) fun _ _ =>
      segSafe_free (accFree_dummies fn.nres)
    rw [tGlobals_eq, seg_req hasl (by omega)] at hs'
    rw [← Option.some.inj hs']
    exact saveCode_safeW htl hF hF4 (by omega) (by omega)
  have m2 : StepsS cap (asyncifyProg P) save.length
      ⟨⟨fid, tl, [], save ++ .return_ :: K', fn.nres⟩ :: tw, P.tGlobals, tm⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ [], .return_ :: K', fn.nres⟩ :: tw,
        [1, BitVec.ofNat 32 (P.sb + 4 * P.frameWords)], mem2⟩ := by
    simpa using steps_segS (cap := cap) (E := asyncifyProg P) (fr := ⟨fid, tl, [], [], fn.nres⟩)
      (rest := tw) (code := .return_ :: K') hseg hsafe
  obtain ⟨nU, cU, vs, eU, hoU, hdone⟩ := unwindW hP (cap := cap) hch ⟨fid, tl,
    List.replicate fn.nres 0 ++ [], .return_ :: K', fn.nres⟩ K' mem2 (P.sb + 4 * P.frameWords) rfl
    (by simp) (by have := addr_step P.sb P.frameWords tw.length; omega)
    (by have := addr_step P.sb P.frameWords tw.length; omega)
  exact ⟨_, cU, vs, m1.trans (m2.trans eU), hoU, hdone⟩

end Silmaril.Wasm.FX.Asyncify.Tool
