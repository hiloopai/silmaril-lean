module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Resume

/-!
# Rewinding a whole chain: the waiting frames

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/ResumeChain.lean`; `rewinds_chain`
restyled).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem WaitR.fid_eq {P : Prog} {above k : Nat} {fs ft : Frame} (h : WaitR P above k fs ft) :
    ft.fid = fs.fid := by
  cases h; rfl

theorem WaitR.fn {P : Prog} {above k : Nat} {fs ft : Frame} (h : WaitR P above k fs ft) :
    ∃ fn, P.fnAt fs.fid = some fn := by
  cases h with
  | mk hfn _ _ _ => exact ⟨_, hfn⟩

theorem seg_site_rw {ls : List W} {sp : W} {M : Nat → W} {F k : Nat}
    (hl : ls.length = F) (hF : 1 ≤ F) (hF2 : F < 2 ^ 32) (hsel : ls[F - 1]? = some (BitVec.ofNat 32 k))
    (hk : k < 2 ^ 32) :
    runSeg [gState, c32 2, neI, .localGet (lidx (F - 1)), c32 k, eqI, orI] ⟨ls, [], [2, sp], M⟩ =
      some ⟨ls, [1], [2, sp], M⟩ := by
  have h1 : [gState, c32 2, neI, .localGet (lidx (F - 1)), c32 k, eqI, orI] =
      [gState, c32 2, neI] ++ ([.localGet (lidx (F - 1)), c32 k, eqI] ++ [orI]) := rfl
  rw [h1, runSeg_append, seg_ne2_rw, Option.bind_some, runSeg_append,
    seg_sel (j := k) hl hF hF2 hsel hk hk, Option.bind_some]
  simp [runSeg, segStep, ctlOf, segCore, pexec, orI, Numerics.intBinOp]

/-- One waiting frame re-enters its call site and calls the frame above it. -/
theorem rewinds_step {P : Prog} (hP : P.WF) {above k : Nat} {fs ft : Frame} (hw : WaitR P above k fs ft)
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
theorem rewinds_cons {P : Prog} (hP : P.WF) {above e k : Nat} {ks : List Nat} {fs ft : Frame}
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
    exact rewinds_step hP hw hA hR hrec (by omega) fn (by rw [hw.fid_eq]; exact hfn)
  have h := ih hfn hstep hrecs' hb' fnE hE
  rw [List.length_cons, ← addr_step]
  simpa [restore] using h

/-- The whole chain of waiting frames, from the export call. -/
theorem rewinds_chain {P : Prog} (hP : P.WF) {above e : Nat} {ks : List Nat} {sw tw : List Frame}
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
  | cons hw _ ih => exact rewinds_cons hP hw ih

end Silmaril.Wasm.FX.Asyncify.Tool
