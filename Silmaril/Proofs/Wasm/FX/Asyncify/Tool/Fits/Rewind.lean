module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.Unwind

/-!
# Rewinding stays in bounds

The steps of `steps_prologue_rw`, `steps_skip`, `rewinds_base`, `rewinds_step`, `rewinds_cons`
and `rewinds_chain` (`Silmaril.Proofs.Wasm.FX.Asyncify.Tool`) as in-bounds steps: `RewindsToS` is
`RewindsTo` with `StepsS`. Each prologue pops a record below the `sp` it starts from, so the
whole rewind stays below the `sp` of the export call, `SB + 4 F · depth`.

New proofs (the chains of `Rewind`, `Skip`, `Resume` and `ResumeChain`, with the bound carried
along).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem accFree_call (f : FuncIdx) : AccFree (.call f) := fun _ => rfl

/-- The prologue in rewind mode pops a record in bounds (`steps_prologue_rw`). -/
theorem steps_prologue_rwS {cap : Nat} {E : Env} {fr : Frame} {rest : List Frame} {K : List Instr}
    {F a : Nat} {M : Nat → W} (hl : fr.locals.length = F) (ha : a + 4 * F < 2 ^ 32)
    (hcap : a + 4 * F ≤ cap) :
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
    have h1 : runSeg [gSp, c32 (4 * F), subI, sSp] ⟨fr.locals, fr.ops, [2, BitVec.ofNat 32 (a + 4 * F)],
        M⟩ = some ⟨fr.locals, fr.ops, [2, BitVec.ofNat 32 a], M⟩ := by
      have hs := sub_ofNat32 a (4 * F)
      simp only [runSeg, segStep, ctlOf, segCore, gSp, sSp, c32, subI, pexec, Numerics.intBinOp]
      simp only [Option.bind_some]
      rw [← hs]; rfl
    rw [h1, Option.bind_some, loadLocals_seg (sp := BitVec.ofNat 32 a) rfl (by simp [hl])
      (by omega), toNat_ofNat32 (by omega)]
    simp
  have e2 := steps_segS (cap := cap) (E := E) (fr := { fr with code := [] }) (rest := rest)
    (code := K) hseg (restoreCode_safe hl ha hcap)
  exact ⟨_, StepsS.trans (by simpa [prologue, ifThen] using e1) (by simpa using e2)⟩

theorem accFree_site (F j : Nat) :
    ∀ i ∈ [gState, c32 2, neI, .localGet (lidx (F - 1)), c32 j, eqI, orI], AccFree i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact accFree_gget _
  · exact accFree_c32 _
  · exact accFree_rel _
  · exact accFree_get _
  · exact accFree_c32 _
  · exact accFree_rel _
  · exact accFree_bin _

theorem accFree_sel (F j : Nat) : ∀ i ∈ [.localGet (lidx (F - 1)), c32 j, eqI], AccFree i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact accFree_get _
  · exact accFree_c32 _
  · exact accFree_rel _

/-- One statement before the resume point is skipped in bounds (`steps_skip1`). -/
theorem steps_skip1S {cap : Nat} {P : Prog} {fn : FnSrc} {fr : Frame} {rest : List Frame}
    {K : List Instr} {sp : W} {M : Nat → W} {k j : Nat} (s : Stmt)
    (hl : fr.locals.length = P.frameWords) (hF : 1 ≤ P.frameWords) (hF2 : P.frameWords < 2 ^ 32)
    (hsel : fr.locals[P.frameWords - 1]? = some (BitVec.ofNat 32 k)) (hk : k < 2 ^ 32)
    (hjk : j < k) :
    ∃ n, StepsS cap (asyncifyProg P) n
      ⟨{ fr with code := trStmt (P.ctx fn) j s ++ K } :: rest, [2, sp], M⟩
      ⟨{ fr with code := K } :: rest, [2, sp], M⟩ := by
  have hne : k ≠ j := by omega
  cases s with
  | pure is =>
    have e := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := fr) (rest := rest) (t := is)
      (e := []) (K := K) (seg_ne2_rw fr.locals fr.ops sp M) (accFree_guard 2 .ne)
    exact ⟨_, by simpa [trStmt, ifThen] using e⟩
  | call f as rs =>
    by_cases hf : f.value.val < P.imps.length
    · have e1 := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := fr) (rest := rest)
        (t := [.localGet (lidx (P.frameWords - 1)), c32 j, eqI,
          ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)])
        (e := reqCode f as ++ [c32 1, sState] ++ saveCode P.frameWords j ++ dummies fn.nres ++
          [.return_]) (K := K) (seg_eq2_rw fr.locals fr.ops sp M) (accFree_guard 2 .eq)
      have e2 := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := fr) (rest := rest)
        (t := [c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs) (e := []) (K := K)
        (seg_sel (g := [2, sp]) (m := M) (ops := fr.ops) hl hF hF2 hsel hk (j := j) (by omega))
        (accFree_sel P.frameWords j)
      simp only [hne, ↓reduceIte] at e2
      refine ⟨_, StepsS.trans (by simpa [trStmt, hf, Prog.ctx] using e1)
        (by simpa [ifThen] using e2)⟩
    · have hseg : runSeg [gState, c32 2, neI, .localGet (lidx (P.frameWords - 1)), c32 j, eqI, orI]
          ⟨fr.locals, fr.ops, [2, sp], M⟩ = some ⟨fr.locals, 0 :: fr.ops, [2, sp], M⟩ := by
        have h1 : [gState, c32 2, neI, .localGet (lidx (P.frameWords - 1)), c32 j, eqI, orI] =
            [gState, c32 2, neI] ++ ([.localGet (lidx (P.frameWords - 1)), c32 j, eqI] ++ [orI]) := rfl
        rw [h1, runSeg_append, seg_ne2_rw, Option.bind_some, runSeg_append,
          seg_sel (j := j) hl hF hF2 hsel hk (by omega), Option.bind_some]
        simp [hne, runSeg, segStep, ctlOf, segCore, pexec, orI, Numerics.intBinOp]
      have e := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := fr) (rest := rest)
        (t := getsCode as ++ [.call f] ++ chk P.frameWords j fn.nres ++ setsCode rs) (e := [])
        (K := K) hseg (accFree_site P.frameWords j)
      exact ⟨_, by simpa [trStmt, hf, Prog.ctx, ifThen] using e⟩

/-- The statements before the resume point are skipped in bounds (`steps_skip`). -/
theorem steps_skipS {cap : Nat} {P : Prog} {fn : FnSrc} {fr : Frame} {rest : List Frame}
    {K : List Instr} {sp : W} {M : Nat → W} {k : Nat}
    (hl : fr.locals.length = P.frameWords) (hF : 1 ≤ P.frameWords) (hF2 : P.frameWords < 2 ^ 32)
    (hsel : fr.locals[P.frameWords - 1]? = some (BitVec.ofNat 32 k)) (hk : k < 2 ^ 32) :
    ∀ (ss : List Stmt) (j : Nat), j + ss.length ≤ k →
      ∃ n, StepsS cap (asyncifyProg P) n
        ⟨{ fr with code := trS (P.ctx fn) j ss ++ K } :: rest, [2, sp], M⟩
        ⟨{ fr with code := K } :: rest, [2, sp], M⟩
  | [], j, _ => ⟨0, by simpa [trS] using StepsS.refl _⟩
  | s :: ss, j, h => by
    simp only [List.length_cons] at h
    obtain ⟨n1, e1⟩ := steps_skip1S (cap := cap) (fn := fn) (fr := fr) (rest := rest)
      (K := trS (P.ctx fn) (j + 1) ss ++ K) (sp := sp) (M := M) (j := j) s hl hF hF2 hsel hk
      (by omega)
    obtain ⟨n2, e2⟩ := steps_skipS (cap := cap) (fn := fn) (fr := fr) (rest := rest) (K := K)
      (sp := sp) (M := M) hl hF hF2 hsel hk ss (j + 1) (by omega)
    exact ⟨n1 + n2, by simpa [trS, List.append_assoc] using e1.trans e2⟩

/-- `RewindsTo` with in-bounds steps. -/
def RewindsToS (cap : Nat) (P : Prog) (fid : Nat) (fn : FnSrc) (a : Nat) (M : Nat → W)
    (G : List Frame → List Frame) : Prop :=
  ∀ below args, args.length = fn.nparams → ∃ n, StepsS cap (asyncifyProg P) n
    ⟨entry fid (tdef P fn) args :: below, [2, BitVec.ofNat 32 a], M⟩
    ⟨G below, [0, BitVec.ofNat 32 P.sb], M⟩

/-- The innermost frame resumes at its import site in bounds (`rewinds_base`). -/
theorem rewinds_baseS {P : Prog} (hP : P.WF) {cap : Nat} {fid : Nat} {fn : FnSrc}
    {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} {tl : List W} {M : Nat → W}
    (hfn : P.fnAt fid = some fn) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : f.value.val < P.imps.length) (htl : tl.length = P.frameWords)
    (hrec : readWords M P.sb P.frameWords = recOf P.frameWords pre.length tl)
    (hcap : P.sb + 4 * P.frameWords ≤ cap) :
    RewindsToS cap P fid fn (P.sb + 4 * P.frameWords) M fun below =>
      ⟨fid, recOf P.frameWords pre.length tl, (readWords M 0 rs.length).reverse,
        setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: below := by
  intro below args hargs
  have hok := Prog.fnOk hP hfn
  obtain ⟨hsig, -, -⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  obtain ⟨hb1, hb2⟩ := Prog.wf_bounds hP
  have hm : rs.length ≤ P.reqWords := (Prog.imp_le (List.mem_of_getElem (Prog.sig_imp hsig hf))).2
  have hF : 1 ≤ P.frameWords := by have := hok.nloc; omega
  have hk : pre.length < 2 ^ 32 := by
    have := hok.nstmts; rw [hst] at this; simp at this; omega
  have hsb : P.sb = 4 * P.reqWords := rfl
  let X := P.ctx fn
  let K' := trS X (pre.length + 1) rest ++ fn.tail
  let r := recOf P.frameWords pre.length tl
  let fr1 : Frame := { entry fid (tdef P fn) args with locals := r, code := [] }
  obtain ⟨n1, e1⟩ := steps_prologue_rwS (cap := cap) (E := asyncifyProg P)
    (fr := { entry fid (tdef P fn) args with code := [] }) (rest := below)
    (K := trS X 0 fn.stmts ++ fn.tail) (M := M)
    (by simpa using entry_len (fid := fid) hargs hok.nloc) (a := P.sb) (by omega) hcap
  rw [hrec] at e1
  have hsel := recOf_sel (k := pre.length) htl hF
  obtain ⟨n2, e2⟩ := steps_skipS (cap := cap) (P := P) (fn := fn) (fr := fr1) (rest := below)
    (K := trStmt X pre.length (Stmt.call f as rs) ++ K') (sp := BitVec.ofNat 32 P.sb) (M := M)
    (show r.length = _ from recOf_length htl hF) hF (by omega) hsel hk pre 0 (by omega)
  have e3 := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := fr1) (rest := below)
    (t := [.localGet (lidx (P.frameWords - 1)), c32 pre.length, eqI,
      ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)])
    (e := reqCode f as ++ [c32 1, sState] ++ saveCode P.frameWords pre.length ++ dummies fn.nres ++
      [.return_]) (K := K') (seg_eq2_rw r [] (BitVec.ofNat 32 P.sb) M) (accFree_guard 2 .eq)
  have e4 := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := fr1) (rest := below)
    (t := [c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs) (e := []) (K := K')
    (seg_sel (g := [2, BitVec.ofNat 32 P.sb]) (m := M) (ops := [])
      (show r.length = _ from recOf_length htl hF) hF (by omega) hsel hk (j := pre.length) hk)
    (accFree_sel P.frameWords pre.length)
  simp only [↓reduceIte] at e4
  have h0 : runSeg [c32 0, sState] ⟨r, [], [2, BitVec.ofNat 32 P.sb], M⟩ =
      some ⟨r, [], [0, BitVec.ofNat 32 P.sb], M⟩ := rfl
  have hseg : runSeg ([c32 0, sState] ++ pushAns 0 rs.length) ⟨r, [], [2, BitVec.ofNat 32 P.sb], M⟩ =
      some ⟨r, (readWords M 0 rs.length).reverse, [0, BitVec.ofNat 32 P.sb], M⟩ := by
    rw [runSeg_append, h0, Option.bind_some, pushAns_seg (by omega)]
    simp
  have hsafe : SegSafe cap ([c32 0, sState] ++ pushAns 0 rs.length)
      ⟨r, [], [2, BitVec.ofNat 32 P.sb], M⟩ := by
    refine segSafe_append (segSafe_free fun i hi => ?_) fun s' hs' => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact accFree_c32 _
      · exact accFree_gset _
    · rw [Option.some.inj (hs'.symm.trans h0)]
      exact pushAns_safe (by omega) (by omega)
  have e5 := steps_segS (cap := cap) (E := asyncifyProg P) (fr := fr1) (rest := below)
    (code := setsCode rs ++ K') hseg hsafe
  have hst' : trS X 0 fn.stmts = trS X 0 pre ++ (trStmt X pre.length (Stmt.call f as rs) ++
      trS X (pre.length + 1) rest) := by
    rw [hst, trS_append, Nat.zero_add]; rfl
  let T : List Instr := [c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs
  have m1 : StepsS cap (asyncifyProg P) n1
      ⟨entry fid (tdef P fn) args :: below, [2, BitVec.ofNat 32 (P.sb + 4 * P.frameWords)], M⟩
      ⟨{ fr1 with code := trS X 0 fn.stmts ++ fn.tail } :: below, [2, BitVec.ofNat 32 P.sb], M⟩ := by
    simpa [entry, tdef, Prog.tBody, List.append_assoc, fr1] using e1
  have m2 : StepsS cap (asyncifyProg P) n2
      ⟨{ fr1 with code := trS X 0 fn.stmts ++ fn.tail } :: below, [2, BitVec.ofNat 32 P.sb], M⟩
      ⟨{ fr1 with code := trStmt X pre.length (Stmt.call f as rs) ++ K' } :: below,
        [2, BitVec.ofNat 32 P.sb], M⟩ := by
    simpa [hst', List.append_assoc, K'] using e2
  have m3 : StepsS cap (asyncifyProg P) (3 + 1)
      ⟨{ fr1 with code := trStmt X pre.length (Stmt.call f as rs) ++ K' } :: below,
        [2, BitVec.ofNat 32 P.sb], M⟩
      ⟨{ fr1 with code := [.localGet (lidx (P.frameWords - 1)), c32 pre.length, eqI, ifThen T] ++ K' } ::
        below, [2, BitVec.ofNat 32 P.sb], M⟩ := by
    simpa [trStmt, hf, Prog.ctx, X, T, List.append_assoc, fr1, entry] using e3
  have m4 : StepsS cap (asyncifyProg P) (3 + 1)
      ⟨{ fr1 with code := [.localGet (lidx (P.frameWords - 1)), c32 pre.length, eqI, ifThen T] ++ K' } ::
        below, [2, BitVec.ofNat 32 P.sb], M⟩
      ⟨{ fr1 with code := ([c32 0, sState] ++ pushAns 0 rs.length) ++ (setsCode rs ++ K') } :: below,
        [2, BitVec.ofNat 32 P.sb], M⟩ := by
    simpa [ifThen, T, List.append_assoc, fr1, entry] using e4
  refine ⟨n1 + (n2 + ((3 + 1) + ((3 + 1) + ([c32 0, sState] ++ pushAns 0 rs.length).length))),
    m1.trans (m2.trans (m3.trans (m4.trans ?_)))⟩
  simpa [fr1, entry, tdef, r, X, K', List.append_assoc] using e5

/-- One waiting frame re-enters its call site in bounds (`rewinds_step`). -/
theorem rewinds_stepS {P : Prog} (hP : P.WF) {cap : Nat} {above k : Nat} {fs ft : Frame}
    (hw : WaitR P above k fs ft) {fnA : FnSrc} (hfnA : P.fnAt above = some fnA) {a : Nat}
    {M : Nat → W} {G : List Frame → List Frame} (hRA : RewindsToS cap P above fnA a M G)
    (hrec : readWords M a P.frameWords = recOf P.frameWords k ft.locals)
    (ha : a + 4 * P.frameWords < 2 ^ 32) (hcap : a + 4 * P.frameWords ≤ cap) :
    ∀ fn, P.fnAt ft.fid = some fn → RewindsToS cap P ft.fid fn (a + 4 * P.frameWords) M
      (fun below => G ({ ft with locals := recOf P.frameWords k ft.locals } :: below)) := by
  cases hw with
  | mk hfn hloc hst hf =>
    rename_i fid fn sl tl pre rest f as rs
    intro fn' hfn' below args hargs
    simp only at hfn'
    rw [hfn] at hfn'; cases hfn'
    have hok := Prog.fnOk hP hfn
    obtain ⟨hsig, has, -⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
    obtain ⟨fnA', hfnA', hnp, -⟩ := Prog.sig_fn hsig hf
    rw [hfnA] at hfnA'; cases hfnA'
    obtain ⟨hb1, hb2⟩ := Prog.wf_bounds hP
    have hF : 1 ≤ P.frameWords := by have := hok.nloc; omega
    have hk : pre.length < 2 ^ 32 := by
      have := hok.nstmts; rw [hst] at this; simp at this; omega
    have htl : tl.length = P.frameWords := hloc.len hok.nloc
    have himp : ¬ f.value.val < P.imps.length := by omega
    let X := P.ctx fn
    let K' := trS X (pre.length + 1) rest ++ fn.tail
    let r := recOf P.frameWords pre.length tl
    have hrl : r.length = P.frameWords := recOf_length htl hF
    let fr1 : Frame := { entry fid (tdef P fn) args with locals := r, code := [] }
    obtain ⟨n1, e1⟩ := steps_prologue_rwS (cap := cap) (E := asyncifyProg P)
      (fr := { entry fid (tdef P fn) args with code := [] }) (rest := below)
      (K := trS X 0 fn.stmts ++ fn.tail) (M := M)
      (by simpa using entry_len (fid := fid) hargs hok.nloc) (a := a) ha hcap
    rw [hrec] at e1
    have hsel := recOf_sel (k := pre.length) htl hF
    obtain ⟨n2, e2⟩ := steps_skipS (cap := cap) (P := P) (fn := fn) (fr := fr1) (rest := below)
      (K := trStmt X pre.length (Stmt.call f as rs) ++ K') (sp := BitVec.ofNat 32 a) (M := M)
      (show r.length = _ from hrl) hF (by omega) hsel hk pre 0 (by omega)
    have e3 := steps_iteS (cap := cap) (E := asyncifyProg P) (fr := fr1) (rest := below)
      (t := getsCode as ++ [.call f] ++ chk P.frameWords pre.length fn.nres ++ setsCode rs) (e := [])
      (K := K') (seg_site_rw (sp := BitVec.ofNat 32 a) (M := M) hrl hF (by omega) hsel hk)
      (accFree_site P.frameWords pre.length)
    have hasl : ∀ x ∈ as, x.value.val < r.length := fun x hx => by
      have := has x hx; have := hok.nloc; omega
    have hgets : ∀ i ∈ getsCode as, AccFree i := by
      intro i hi
      simp only [getsCode, List.mem_map] at hi
      obtain ⟨b, -, rfl⟩ := hi
      exact accFree_get b
    have e4 := steps_segS (cap := cap) (E := asyncifyProg P) (fr := fr1) (rest := below)
      (code := .call f :: (chk P.frameWords pre.length fn.nres ++ setsCode rs ++ K'))
      (getsCode_seg (gs := [2, BitVec.ofNat 32 a]) (mem := M) (ops := []) hasl)
      (segSafe_free hgets)
    let c5 : Cfg := ⟨⟨fid, r, (as.map (lv r)).reverse ++ [], .call f ::
      (chk P.frameWords pre.length fn.nres ++ setsCode rs ++ K'), fn.nres⟩ :: below,
      [2, BitVec.ofNat 32 a], M⟩
    have e5 := step_call_def (E := asyncifyProg P) (c := c5)
      (d := tdef P fnA) rfl rfl (by simpa [asyncifyProg] using himp)
      (by simpa [tdef] using Prog.tgt_fn hfnA) (by simp [tdef, hnp])
    have htk : ((as.map (lv r)).reverse ++ []).take (tdef P fnA).nparams = (as.map (lv r)).reverse :=
      by rw [List.append_nil]; exact List.take_of_length_le (by simp [tdef, hnp])
    have hdr : ((as.map (lv r)).reverse ++ []).drop (tdef P fnA).nparams = [] :=
      List.drop_eq_nil_of_le (by simp [tdef, hnp])
    rw [htk, hdr, List.reverse_reverse] at e5
    have ho5 : ¬ OOB cap c5 := not_oob_free (c := c5) rfl rfl (accFree_call f)
    obtain ⟨n6, e6⟩ := hRA (⟨fid, r, [], chk P.frameWords pre.length fn.nres ++ setsCode rs ++ K',
      fn.nres⟩ :: below) (as.map (lv r)) (by simp [hnp])
    have hst' : trS X 0 fn.stmts = trS X 0 pre ++ (trStmt X pre.length (Stmt.call f as rs) ++
        trS X (pre.length + 1) rest) := by
      rw [hst, trS_append, Nat.zero_add]; rfl
    have m1 : StepsS cap (asyncifyProg P) n1
        ⟨entry fid (tdef P fn) args :: below, [2, BitVec.ofNat 32 (a + 4 * P.frameWords)], M⟩
        ⟨{ fr1 with code := trS X 0 fn.stmts ++ fn.tail } :: below, [2, BitVec.ofNat 32 a], M⟩ := by
      simpa [entry, tdef, Prog.tBody, List.append_assoc, fr1] using e1
    have m2 : StepsS cap (asyncifyProg P) n2
        ⟨{ fr1 with code := trS X 0 fn.stmts ++ fn.tail } :: below, [2, BitVec.ofNat 32 a], M⟩
        ⟨{ fr1 with code := trStmt X pre.length (Stmt.call f as rs) ++ K' } :: below,
          [2, BitVec.ofNat 32 a], M⟩ := by
      simpa [hst', List.append_assoc, K'] using e2
    have m3 : StepsS cap (asyncifyProg P) (7 + 1)
        ⟨{ fr1 with code := trStmt X pre.length (Stmt.call f as rs) ++ K' } :: below,
          [2, BitVec.ofNat 32 a], M⟩
        ⟨{ fr1 with code := getsCode as ++ .call f :: (chk P.frameWords pre.length fn.nres ++
          setsCode rs ++ K') } :: below, [2, BitVec.ofNat 32 a], M⟩ := by
      simpa [trStmt, himp, Prog.ctx, X, ifThen, List.append_assoc, fr1, entry] using e3
    have m4 : StepsS cap (asyncifyProg P) (getsCode as).length
        ⟨{ fr1 with code := getsCode as ++ .call f :: (chk P.frameWords pre.length fn.nres ++
          setsCode rs ++ K') } :: below, [2, BitVec.ofNat 32 a], M⟩ c5 := by
      simpa [fr1, entry, tdef, c5] using e4
    refine ⟨n1 + (n2 + ((7 + 1) + ((getsCode as).length + (1 + n6)))),
      m1.trans (m2.trans (m3.trans (m4.trans ((StepsS.one ho5 e5).trans ?_))))⟩
    simpa [tdef, X, K', r, List.append_assoc, chk, c5] using e6

/-- One more waiting frame below a chain that rewinds in bounds (`rewinds_cons`). -/
theorem rewinds_consS {P : Prog} (hP : P.WF) {cap : Nat} {above e k : Nat} {ks : List Nat}
    {fs ft : Frame} {ts : List Frame} (hw : WaitR P above k fs ft)
    (ih : ∀ {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame},
      P.fnAt fs.fid = some fnA → RewindsToS cap P fs.fid fnA a M G →
      RecsAt P.frameWords M a ks ts →
      a + 4 * P.frameWords * ts.length < 2 ^ 32 → a + 4 * P.frameWords * ts.length ≤ cap →
      ∀ fnE, P.fnAt e = some fnE → RewindsToS cap P e fnE (a + 4 * P.frameWords * ts.length) M
        (fun below => G (restore P.frameWords ks ts ++ below)))
    {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame}
    (hA : P.fnAt above = some fnA) (hR : RewindsToS cap P above fnA a M G)
    (hrecs : RecsAt P.frameWords M a (k :: ks) (ft :: ts))
    (hb : a + 4 * P.frameWords * (ft :: ts).length < 2 ^ 32)
    (hc : a + 4 * P.frameWords * (ft :: ts).length ≤ cap) (fnE : FnSrc)
    (hE : P.fnAt e = some fnE) :
    RewindsToS cap P e fnE (a + 4 * P.frameWords * (ft :: ts).length) M
      (fun below => G (restore P.frameWords (k :: ks) (ft :: ts) ++ below)) := by
  have hrec : readWords M a P.frameWords = recOf P.frameWords k ft.locals := hrecs.1
  have hrecs' : RecsAt P.frameWords M (a + 4 * P.frameWords) ks ts := hrecs.2
  have hb' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length < 2 ^ 32 := by
    rw [addr_step]; simpa using hb
  have hc' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length ≤ cap := by
    rw [addr_step]; simpa using hc
  obtain ⟨fn, hfn⟩ := hw.fn
  have hstep : RewindsToS cap P fs.fid fn (a + 4 * P.frameWords) M
      (fun below => G ({ ft with locals := recOf P.frameWords k ft.locals } :: below)) := by
    rw [← hw.fid_eq]
    exact rewinds_stepS hP hw hA hR hrec (by omega) (by omega) fn (by rw [hw.fid_eq]; exact hfn)
  have h := ih hfn hstep hrecs' hb' hc' fnE hE
  rw [List.length_cons, ← addr_step]
  simpa [restore] using h

/-- The whole chain of waiting frames rewinds in bounds (`rewinds_chain`). -/
theorem rewinds_chainS {P : Prog} (hP : P.WF) {cap : Nat} {above e : Nat} {ks : List Nat}
    {sw tw : List Frame} (hch : Chain P above e ks sw tw) :
    ∀ {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame},
      P.fnAt above = some fnA → RewindsToS cap P above fnA a M G →
      RecsAt P.frameWords M a ks tw →
      a + 4 * P.frameWords * tw.length < 2 ^ 32 → a + 4 * P.frameWords * tw.length ≤ cap →
      ∀ fnE, P.fnAt e = some fnE → RewindsToS cap P e fnE (a + 4 * P.frameWords * tw.length) M
        (fun below => G (restore P.frameWords ks tw ++ below)) := by
  induction hch with
  | nil e =>
    intro fnA a M G hA hR _ _ _ fnE hE
    have hfn : fnA = fnE := Option.some.inj (hA.symm.trans hE)
    simpa [restore, ← hfn] using hR
  | cons hw _ ih => exact rewinds_consS hP hw ih

end Silmaril.Wasm.FX.Asyncify.Tool
