module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.SelSim.Basic

/-!
# The selective simulation: unwinding and rewinding under `SelOk`

Copies of the macro steps of `Silmaril/Proofs/Wasm/FX/Asyncify/Tool/{Unwind,Resume,ResumeChain,
SuspendSim}.lean` with `P.WF` weakened to `SelOk P C` (the proofs use only the facts of call
statements, the frame size and the bounds). The statements are unchanged otherwise.

New proofs (copies).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- One waiting frame unwinds: the frame above returns into its call-site check, which saves the
frame's record at `a` and reaches the frame's own `return`. -/
theorem unwind_wait_q {P : Prog} {C : Nat → Prop} (hP : SelOk P C) {fid : Nat} {fn : FnSrc} {sl tl : List W}
    {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    {fr : Frame} {K : List Instr} {ts : List Frame} {mem : Nat → W} {a : Nat}
    (hcode : fr.code = .return_ :: K) (ha : a + 4 * P.frameWords < 2 ^ 32) :
    Steps (asyncifyProg P)
      (1 + ((3 + 1) + (saveCode P.frameWords pre.length ++ dummies fn.nres).length))
      ⟨fr :: ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++ setsCode rs ++
          trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ (fr.ops.take fr.nres ++ []),
          .return_ :: (setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail),
          fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 (a + 4 * P.frameWords)],
        writeWords mem a (recOf P.frameWords pre.length tl)⟩ := by
  have hok : FnOkS P C fn := hP.fn hfn
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  have hk : pre.length < 2 ^ 32 := by have := hok.pre_lt hst; omega
  have hF : 1 ≤ P.frameWords := by have := hok.nloc; omega
  let K' := setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail
  let ops := fr.ops.take fr.nres ++ []
  let save := saveCode P.frameWords pre.length ++ dummies fn.nres
  have e1 : step (asyncifyProg P) ⟨fr :: ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++
      setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
      [1, BitVec.ofNat 32 a], mem⟩ = .next ⟨⟨fid, tl, ops, chk P.frameWords pre.length fn.nres ++
        setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 a], mem⟩ := by
    rw [step_return rfl hcode, ret_cons]
  have m2 : Steps (asyncifyProg P) (3 + 1)
      ⟨⟨fid, tl, ops, chk P.frameWords pre.length fn.nres ++ setsCode rs ++
        trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, ops, save ++ .return_ :: K', fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩ := by
    have e2 := steps_guard (E := asyncifyProg P) (fr := ⟨fid, tl, ops, [], fn.nres⟩) (rest := ts)
      (t := save ++ [.return_]) (K := K') (seg_chk_unwind tl ops (BitVec.ofNat 32 a) mem)
    simpa [chk, ifThen, save, K', List.append_assoc] using e2
  have m3 : Steps (asyncifyProg P) save.length
      ⟨⟨fid, tl, ops, save ++ .return_ :: K', fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ ops, .return_ :: K', fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 (a + 4 * P.frameWords)],
        writeWords mem a (recOf P.frameWords pre.length tl)⟩ := by
    have e3 := steps_seg (E := asyncifyProg P) (fr := ⟨fid, tl, ops, [], fn.nres⟩) (rest := ts)
      (code := .return_ :: K') (g := [1, BitVec.ofNat 32 a]) (m := mem)
      (show runSeg save _ = _ by
        rw [runSeg_append, saveCode_seg (a := a) htl hF ha hk, Option.bind_some, dummies_seg])
    simpa using e3
  exact (Steps.one e1).trans (m2.trans m3)

/-- Unwinding a chain of waiting frames from a frame about to `return`: the records are written
at `a, a + 4F, …` and the export returns with `state = 1`. -/
theorem unwind_q {P : Prog} {C : Nat → Prop} (hP : SelOk P C) {above e : Nat} {ks : List Nat} {sw tw : List Frame}
    (hch : Chain P above e ks sw tw) :
    ∀ (fr : Frame) (K : List Instr) (mem : Nat → W) (a : Nat), fr.code = .return_ :: K →
      fr.nres ≤ fr.ops.length → a + 4 * P.frameWords * tw.length < 2 ^ 32 →
      ∃ n c vs, Steps (asyncifyProg P) n ⟨fr :: tw, [1, BitVec.ofNat 32 a], mem⟩ c ∧
        step (asyncifyProg P) c = .done vs ⟨[], [1, BitVec.ofNat 32 (a + 4 * P.frameWords * tw.length)],
          writeRecs P.frameWords mem a (recs P.frameWords ks tw)⟩ := by
  induction hch with
  | nil e =>
    intro fr K mem a hcode _ _
    refine ⟨0, _, fr.ops.take fr.nres, .refl _, ?_⟩
    rw [step_return rfl hcode]
    simp [ret, recs, writeRecs]
  | @cons _ _ _ _ _ _ _ ts hw _ ih =>
    intro fr K mem a hcode _ hb
    cases hw with
    | @mk fid fn sl tl pre rest f as rs hfn hloc hst _ =>
      have hb' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length < 2 ^ 32 := by
        rw [addr_step]; simpa using hb
      have hw1 := unwind_wait_q hP hfn hloc hst (ts := ts) (mem := mem) (a := a) hcode (by omega)
      obtain ⟨n, c, vs, hs, hd⟩ := ih ⟨fid, tl, List.replicate fn.nres 0 ++ (fr.ops.take fr.nres ++ []),
        .return_ :: (setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail), fn.nres⟩ _ _
        (a + 4 * P.frameWords) rfl (by simp) hb'
      refine ⟨_, c, vs, hw1.trans hs, ?_⟩
      rw [hd, List.length_cons, ← addr_step]
      rfl

/-- The innermost frame: the import site it suspended at. -/
theorem rewinds_base_q {P : Prog} {C : Nat → Prop} (hP : SelOk P C) {fid : Nat} {fn : FnSrc} {pre rest : List Stmt}
    {f : FuncIdx} {as rs : List LocalIdx} {tl : List W} {M : Nat → W}
    (hfn : P.fnAt fid = some fn) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : f.value.val < P.imps.length) (htl : tl.length = P.frameWords)
    (hrec : readWords M P.sb P.frameWords = recOf P.frameWords pre.length tl) :
    RewindsTo P fid fn (P.sb + 4 * P.frameWords) M fun below =>
      ⟨fid, recOf P.frameWords pre.length tl, (readWords M 0 rs.length).reverse,
        setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: below := by
  intro below args hargs
  have hok := hP.fn hfn
  obtain ⟨hsig, -, -⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  obtain ⟨hb1, hb2⟩ := hP.bounds
  have hm : rs.length ≤ P.reqWords := (Prog.imp_le (List.mem_of_getElem (Prog.sig_imp hsig hf))).2
  have hF : 1 ≤ P.frameWords := by have := hok.nloc; omega
  have hk : pre.length < 2 ^ 32 := by
    have := hok.nstmts; rw [hst] at this; simp at this; omega
  have hsb : P.sb = 4 * P.reqWords := rfl
  let X := P.ctx fn
  let K' := trS X (pre.length + 1) rest ++ fn.tail
  let r := recOf P.frameWords pre.length tl
  let fr1 : Frame := { entry fid (tdef P fn) args with locals := r, code := [] }
  -- prologue
  obtain ⟨n1, e1⟩ := steps_prologue_rw (E := asyncifyProg P) (fr := { entry fid (tdef P fn) args with
    code := [] }) (rest := below) (K := trS X 0 fn.stmts ++ fn.tail) (M := M)
    (by simpa using entry_len (fid := fid) hargs hok.nloc) (a := P.sb) (by omega)
  rw [hrec] at e1
  -- skip the statements before the resume point
  have hsel := recOf_sel (k := pre.length) htl hF
  obtain ⟨n2, e2⟩ := steps_skip (P := P) (fn := fn)
    (fr := fr1) (rest := below)
    (K := trStmt X pre.length (Stmt.call f as rs) ++ K') (sp := BitVec.ofNat 32 P.sb) (M := M)
    (show r.length = _ from recOf_length htl hF) hF (by omega) hsel hk pre 0 (by omega)
  -- the import site resumes
  have e3 := steps_ite (E := asyncifyProg P) (fr := fr1) (rest := below)
    (t := [.localGet (lidx (P.frameWords - 1)), c32 pre.length, eqI,
      ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)])
    (e := reqCode f as ++ [c32 1, sState] ++ saveCode P.frameWords pre.length ++ dummies fn.nres ++
      [.return_]) (K := K') (seg_eq2_rw r [] (BitVec.ofNat 32 P.sb) M)
  have e4 := steps_ite (E := asyncifyProg P) (fr := fr1) (rest := below)
    (t := [c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs) (e := []) (K := K')
    (seg_sel (g := [2, BitVec.ofNat 32 P.sb]) (m := M) (ops := [])
      (show r.length = _ from recOf_length htl hF) hF (by omega) hsel hk (j := pre.length) hk)
  simp only [↓reduceIte] at e4
  have hseg : runSeg ([c32 0, sState] ++ pushAns 0 rs.length) ⟨r, [], [2, BitVec.ofNat 32 P.sb], M⟩ =
      some ⟨r, (readWords M 0 rs.length).reverse, [0, BitVec.ofNat 32 P.sb], M⟩ := by
    rw [runSeg_append]
    have : runSeg [c32 0, sState] ⟨r, [], [2, BitVec.ofNat 32 P.sb], M⟩ =
        some ⟨r, [], [0, BitVec.ofNat 32 P.sb], M⟩ := rfl
    rw [this, Option.bind_some, pushAns_seg (by omega)]
    simp
  have e5 := steps_seg (E := asyncifyProg P) (fr := fr1) (rest := below) (code := setsCode rs ++ K') hseg
  have hst' : trS X 0 fn.stmts = trS X 0 pre ++ (trStmt X pre.length (Stmt.call f as rs) ++
      trS X (pre.length + 1) rest) := by
    rw [hst, trS_append, Nat.zero_add]; rfl
  let T : List Instr := [c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs
  have m1 : Steps (asyncifyProg P) n1
      ⟨entry fid (tdef P fn) args :: below, [2, BitVec.ofNat 32 (P.sb + 4 * P.frameWords)], M⟩
      ⟨{ fr1 with code := trS X 0 fn.stmts ++ fn.tail } :: below, [2, BitVec.ofNat 32 P.sb], M⟩ := by
    simpa [entry, tdef, Prog.tBody, List.append_assoc, fr1] using e1
  have m2 : Steps (asyncifyProg P) n2
      ⟨{ fr1 with code := trS X 0 fn.stmts ++ fn.tail } :: below, [2, BitVec.ofNat 32 P.sb], M⟩
      ⟨{ fr1 with code := trStmt X pre.length (Stmt.call f as rs) ++ K' } :: below,
        [2, BitVec.ofNat 32 P.sb], M⟩ := by
    simpa [hst', List.append_assoc, K'] using e2
  have m3 : Steps (asyncifyProg P) (3 + 1)
      ⟨{ fr1 with code := trStmt X pre.length (Stmt.call f as rs) ++ K' } :: below,
        [2, BitVec.ofNat 32 P.sb], M⟩
      ⟨{ fr1 with code := [.localGet (lidx (P.frameWords - 1)), c32 pre.length, eqI, ifThen T] ++ K' } ::
        below, [2, BitVec.ofNat 32 P.sb], M⟩ := by
    simpa [trStmt, hf, Prog.ctx, X, T, List.append_assoc, fr1, entry] using e3
  have m4 : Steps (asyncifyProg P) (3 + 1)
      ⟨{ fr1 with code := [.localGet (lidx (P.frameWords - 1)), c32 pre.length, eqI, ifThen T] ++ K' } ::
        below, [2, BitVec.ofNat 32 P.sb], M⟩
      ⟨{ fr1 with code := ([c32 0, sState] ++ pushAns 0 rs.length) ++ (setsCode rs ++ K') } :: below,
        [2, BitVec.ofNat 32 P.sb], M⟩ := by
    simpa [ifThen, T, List.append_assoc, fr1, entry] using e4
  have m5 := e5
  refine ⟨n1 + (n2 + ((3 + 1) + ((3 + 1) + ([c32 0, sState] ++ pushAns 0 rs.length).length))),
    m1.trans (m2.trans (m3.trans (m4.trans ?_)))⟩
  simpa [fr1, entry, tdef, r, X, K', List.append_assoc] using m5

/-- One waiting frame re-enters its call site and calls the frame above it. -/
theorem rewinds_step_q {P : Prog} {C : Nat → Prop} (hP : SelOk P C) {above k : Nat} {fs ft : Frame} (hw : WaitR P above k fs ft)
    {fnA : FnSrc} (hfnA : P.fnAt above = some fnA) {a : Nat} {M : Nat → W}
    {G : List Frame → List Frame} (hRA : RewindsTo P above fnA a M G)
    (hrec : readWords M a P.frameWords = recOf P.frameWords k ft.locals)
    (ha : a + 4 * P.frameWords < 2 ^ 32) :
    ∀ fn, P.fnAt ft.fid = some fn → RewindsTo P ft.fid fn (a + 4 * P.frameWords) M
      (fun below => G ({ ft with locals := recOf P.frameWords k ft.locals } :: below)) := by
  cases hw with
  | mk hfn hloc hst hf =>
    rename_i fid fn sl tl pre rest f as rs
    intro fn' hfn' below args hargs
    simp only at hfn'
    rw [hfn] at hfn'; cases hfn'
    have hok := hP.fn hfn
    obtain ⟨hsig, has, -⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
    obtain ⟨fnA', hfnA', hnp, -⟩ := Prog.sig_fn hsig hf
    rw [hfnA] at hfnA'; cases hfnA'
    obtain ⟨hb1, hb2⟩ := hP.bounds
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
    obtain ⟨n1, e1⟩ := steps_prologue_rw (E := asyncifyProg P) (fr := { entry fid (tdef P fn) args with
      code := [] }) (rest := below) (K := trS X 0 fn.stmts ++ fn.tail) (M := M)
      (by simpa using entry_len (fid := fid) hargs hok.nloc) (a := a) ha
    rw [hrec] at e1
    have hsel := recOf_sel (k := pre.length) htl hF
    obtain ⟨n2, e2⟩ := steps_skip (P := P) (fn := fn) (fr := fr1) (rest := below)
      (K := trStmt X pre.length (Stmt.call f as rs) ++ K') (sp := BitVec.ofNat 32 a) (M := M)
      (show r.length = _ from hrl) hF (by omega) hsel hk pre 0 (by omega)
    have e3 := steps_ite (E := asyncifyProg P) (fr := fr1) (rest := below)
      (t := getsCode as ++ [.call f] ++ chk P.frameWords pre.length fn.nres ++ setsCode rs) (e := [])
      (K := K') (seg_site_rw (sp := BitVec.ofNat 32 a) (M := M) hrl hF (by omega) hsel hk)
    have hasl : ∀ x ∈ as, x.value.val < r.length := fun x hx => by
      have := has x hx; have := hok.nloc; omega
    have e4 := steps_seg (E := asyncifyProg P) (fr := fr1) (rest := below)
      (code := .call f :: (chk P.frameWords pre.length fn.nres ++ setsCode rs ++ K'))
      (getsCode_seg (gs := [2, BitVec.ofNat 32 a]) (mem := M) (ops := []) hasl)
    have e5 := step_call_def (E := asyncifyProg P)
      (c := ⟨⟨fid, r, (as.map (lv r)).reverse ++ [], .call f :: (chk P.frameWords pre.length fn.nres ++
        setsCode rs ++ K'), fn.nres⟩ :: below, [2, BitVec.ofNat 32 a], M⟩)
      (d := tdef P fnA) rfl rfl (by simpa [asyncifyProg] using himp)
      (by simpa [tdef] using Prog.tgt_fn hfnA) (by simp [tdef, hnp])
    have htk : ((as.map (lv r)).reverse ++ []).take (tdef P fnA).nparams = (as.map (lv r)).reverse :=
      by rw [List.append_nil]; exact List.take_of_length_le (by simp [tdef, hnp])
    have hdr : ((as.map (lv r)).reverse ++ []).drop (tdef P fnA).nparams = [] :=
      List.drop_eq_nil_of_le (by simp [tdef, hnp])
    rw [htk, hdr, List.reverse_reverse] at e5
    obtain ⟨n6, e6⟩ := hRA (⟨fid, r, [], chk P.frameWords pre.length fn.nres ++ setsCode rs ++ K',
      fn.nres⟩ :: below) (as.map (lv r)) (by simp [hnp])
    have hst' : trS X 0 fn.stmts = trS X 0 pre ++ (trStmt X pre.length (Stmt.call f as rs) ++
        trS X (pre.length + 1) rest) := by
      rw [hst, trS_append, Nat.zero_add]; rfl
    have m1 : Steps (asyncifyProg P) n1
        ⟨entry fid (tdef P fn) args :: below, [2, BitVec.ofNat 32 (a + 4 * P.frameWords)], M⟩
        ⟨{ fr1 with code := trS X 0 fn.stmts ++ fn.tail } :: below, [2, BitVec.ofNat 32 a], M⟩ := by
      simpa [entry, tdef, Prog.tBody, List.append_assoc, fr1] using e1
    have m2 : Steps (asyncifyProg P) n2
        ⟨{ fr1 with code := trS X 0 fn.stmts ++ fn.tail } :: below, [2, BitVec.ofNat 32 a], M⟩
        ⟨{ fr1 with code := trStmt X pre.length (Stmt.call f as rs) ++ K' } :: below,
          [2, BitVec.ofNat 32 a], M⟩ := by
      simpa [hst', List.append_assoc, K'] using e2
    have m3 : Steps (asyncifyProg P) (7 + 1)
        ⟨{ fr1 with code := trStmt X pre.length (Stmt.call f as rs) ++ K' } :: below,
          [2, BitVec.ofNat 32 a], M⟩
        ⟨{ fr1 with code := getsCode as ++ .call f :: (chk P.frameWords pre.length fn.nres ++
          setsCode rs ++ K') } :: below, [2, BitVec.ofNat 32 a], M⟩ := by
      simpa [trStmt, himp, Prog.ctx, X, ifThen, List.append_assoc, fr1, entry] using e3
    have m4 : Steps (asyncifyProg P) (getsCode as).length
        ⟨{ fr1 with code := getsCode as ++ .call f :: (chk P.frameWords pre.length fn.nres ++
          setsCode rs ++ K') } :: below, [2, BitVec.ofNat 32 a], M⟩
        ⟨⟨fid, r, (as.map (lv r)).reverse ++ [], .call f :: (chk P.frameWords pre.length fn.nres ++
          setsCode rs ++ K'), fn.nres⟩ :: below, [2, BitVec.ofNat 32 a], M⟩ := by
      simpa [fr1, entry, tdef] using e4
    refine ⟨n1 + (n2 + ((7 + 1) + ((getsCode as).length + (1 + n6)))),
      m1.trans (m2.trans (m3.trans (m4.trans ((Steps.one e5).trans ?_))))⟩
    simpa [tdef, X, K', r, List.append_assoc, chk] using e6

/-- One more waiting frame below a chain that rewinds. -/
theorem rewinds_cons_q {P : Prog} {C : Nat → Prop} (hP : SelOk P C) {above e k : Nat} {ks : List Nat} {fs ft : Frame}
    {ts : List Frame} (hw : WaitR P above k fs ft)
    (ih : ∀ {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame},
      P.fnAt fs.fid = some fnA → RewindsTo P fs.fid fnA a M G → RecsAt P.frameWords M a ks ts →
      a + 4 * P.frameWords * ts.length < 2 ^ 32 →
      ∀ fnE, P.fnAt e = some fnE → RewindsTo P e fnE (a + 4 * P.frameWords * ts.length) M
        (fun below => G (restore P.frameWords ks ts ++ below)))
    {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame}
    (hA : P.fnAt above = some fnA) (hR : RewindsTo P above fnA a M G)
    (hrecs : RecsAt P.frameWords M a (k :: ks) (ft :: ts))
    (hb : a + 4 * P.frameWords * (ft :: ts).length < 2 ^ 32) (fnE : FnSrc)
    (hE : P.fnAt e = some fnE) :
    RewindsTo P e fnE (a + 4 * P.frameWords * (ft :: ts).length) M
      (fun below => G (restore P.frameWords (k :: ks) (ft :: ts) ++ below)) := by
  have hrec : readWords M a P.frameWords = recOf P.frameWords k ft.locals := hrecs.1
  have hrecs' : RecsAt P.frameWords M (a + 4 * P.frameWords) ks ts := hrecs.2
  have hb' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length < 2 ^ 32 := by
    rw [addr_step]; simpa using hb
  obtain ⟨fn, hfn⟩ := hw.fn
  have hstep : RewindsTo P fs.fid fn (a + 4 * P.frameWords) M
      (fun below => G ({ ft with locals := recOf P.frameWords k ft.locals } :: below)) := by
    rw [← hw.fid_eq]
    exact rewinds_step_q hP hw hA hR hrec (by omega) fn (by rw [hw.fid_eq]; exact hfn)
  have h := ih hfn hstep hrecs' hb' fnE hE
  rw [List.length_cons, ← addr_step]
  simpa [restore] using h

/-- The whole chain of waiting frames, from the export call. -/
theorem rewinds_chain_q {P : Prog} {C : Nat → Prop} (hP : SelOk P C) {above e : Nat} {ks : List Nat} {sw tw : List Frame}
    (hch : Chain P above e ks sw tw) :
    ∀ {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame},
      P.fnAt above = some fnA → RewindsTo P above fnA a M G → RecsAt P.frameWords M a ks tw →
      a + 4 * P.frameWords * tw.length < 2 ^ 32 →
      ∀ fnE, P.fnAt e = some fnE → RewindsTo P e fnE (a + 4 * P.frameWords * tw.length) M
        (fun below => G (restore P.frameWords ks tw ++ below)) := by
  induction hch with
  | nil e =>
    intro fnA a M G hA hR _ _ fnE hE
    have hfn : fnA = fnE := Option.some.inj (hA.symm.trans hE)
    simpa [restore, ← hfn] using hR
  | cons hw _ ih => exact rewinds_cons_q hP hw ih

/-- The target at an import site in normal mode: it writes the request, sets `state := 1`, saves
the frame at `SB` and unwinds the waiting frames. -/
theorem tgt_imp_unwind_q {P : Prog} {C : Nat → Prop} (hP : SelOk P C) {fid e : Nat} {fn : FnSrc} {sl tl : List W}
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
  have hok : FnOkS P C fn := hP.fn hfn
  obtain ⟨hsig, has, -⟩ := Stmt.wf_call (hok.stmts (Stmt.call f as rs) (by rw [hst]; simp))
  have hreq : as.length + 1 ≤ P.reqWords :=
    (Prog.imp_le (List.mem_of_getElem (Prog.sig_imp hsig hf))).1
  have hb2 : 4 * P.frameWords + 4 * P.reqWords < 2 ^ 24 := (hP.bounds).2
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
  obtain ⟨nU, cU, vs, eU, hdone⟩ := unwind_q hP hch ⟨fid, tl, List.replicate fn.nres 0 ++ [],
    .return_ :: K', fn.nres⟩ K' mem2 (P.sb + 4 * P.frameWords) rfl (by simp)
    (by have := addr_step P.sb P.frameWords tw.length; omega)
  exact ⟨_, cU, vs, m1.trans (m2.trans eU), hdone⟩

/-- After the host's answer `ws`, the target rewinds the whole chain back to the import site. -/
theorem rewind_after_q {P : Prog} {C : Nat → Prop} (hP : SelOk P C) {fid e : Nat} {fn fnE : FnSrc} {pre rest : List Stmt}
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
  have hF : 1 ≤ P.frameWords := by have := (hP.fn hfn).nloc; omega
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
  have hchain := rewinds_chain_q hP hch hfn (rewinds_base_q hP hfn hst hf htl hrec0) hrecsM
    (by have := addr_step P.sb P.frameWords tw.length; omega) fnE hfnE
  obtain ⟨nR, eR⟩ := hchain [] ta hargsE
  exact ⟨nR, by simpa only [hans] using eR⟩

end Silmaril.Wasm.FX.Asyncify.Tool

