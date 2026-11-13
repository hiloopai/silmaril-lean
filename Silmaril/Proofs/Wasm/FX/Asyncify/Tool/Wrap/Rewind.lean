module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Wrap.Unwind

/-!
# Rewinding with a wrapping `sp`

`rewinds_stepW`, `rewinds_consW` and `rewinds_chainW` of `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits`
with the weaker bound of `Wrap/Unwind`: every record starts below `2 ^ 32`, so a chain of `d`
records at `a, a + 4F, …` rewinds in bounds when `a + 4 F · d < 2 ^ 32 + 4 F` (and ends at or
below `cap`). The `sp` of the export call, `a + 4 F · d`, may have wrapped.

New proofs (copies with the weaker bound).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- One waiting frame re-enters its call site in bounds (`rewinds_step`). -/
theorem rewinds_stepW {P : Prog} (hP : P.WF) {cap : Nat} {above k : Nat} {fs ft : Frame}
    (hw : WaitR P above k fs ft) {fnA : FnSrc} (hfnA : P.fnAt above = some fnA) {a : Nat}
    {M : Nat → W} {G : List Frame → List Frame} (hRA : RewindsToS cap P above fnA a M G)
    (hrec : readWords M a P.frameWords = recOf P.frameWords k ft.locals)
    (ha : a < 2 ^ 32) (hcap : a + 4 * P.frameWords ≤ cap) :
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
    obtain ⟨n1, e1⟩ := steps_prologue_rwW (cap := cap) (E := asyncifyProg P)
      (fr := { entry fid (tdef P fn) args with code := [] }) (rest := below)
      (K := trS X 0 fn.stmts ++ fn.tail) (M := M)
      (by simpa using entry_len (fid := fid) hargs hok.nloc) (a := a) (Prog.frame4_lt hP) ha hcap
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
theorem rewinds_consW {P : Prog} (hP : P.WF) {cap : Nat} {above e k : Nat} {ks : List Nat}
    {fs ft : Frame} {ts : List Frame} (hw : WaitR P above k fs ft)
    (ih : ∀ {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame},
      P.fnAt fs.fid = some fnA → RewindsToS cap P fs.fid fnA a M G →
      RecsAt P.frameWords M a ks ts →
      a + 4 * P.frameWords * ts.length < 2 ^ 32 + 4 * P.frameWords → a + 4 * P.frameWords * ts.length ≤ cap →
      ∀ fnE, P.fnAt e = some fnE → RewindsToS cap P e fnE (a + 4 * P.frameWords * ts.length) M
        (fun below => G (restore P.frameWords ks ts ++ below)))
    {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame}
    (hA : P.fnAt above = some fnA) (hR : RewindsToS cap P above fnA a M G)
    (hrecs : RecsAt P.frameWords M a (k :: ks) (ft :: ts))
    (hb : a + 4 * P.frameWords * (ft :: ts).length < 2 ^ 32 + 4 * P.frameWords)
    (hc : a + 4 * P.frameWords * (ft :: ts).length ≤ cap) (fnE : FnSrc)
    (hE : P.fnAt e = some fnE) :
    RewindsToS cap P e fnE (a + 4 * P.frameWords * (ft :: ts).length) M
      (fun below => G (restore P.frameWords (k :: ks) (ft :: ts) ++ below)) := by
  have hrec : readWords M a P.frameWords = recOf P.frameWords k ft.locals := hrecs.1
  have hrecs' : RecsAt P.frameWords M (a + 4 * P.frameWords) ks ts := hrecs.2
  have hb' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length < 2 ^ 32 + 4 * P.frameWords := by
    rw [addr_step]; simpa using hb
  have hc' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length ≤ cap := by
    rw [addr_step]; simpa using hc
  obtain ⟨fn, hfn⟩ := hw.fn
  have hstep : RewindsToS cap P fs.fid fn (a + 4 * P.frameWords) M
      (fun below => G ({ ft with locals := recOf P.frameWords k ft.locals } :: below)) := by
    rw [← hw.fid_eq]
    exact rewinds_stepW hP hw hA hR hrec (by omega) (by omega) fn (by rw [hw.fid_eq]; exact hfn)
  have h := ih hfn hstep hrecs' hb' hc' fnE hE
  rw [List.length_cons, ← addr_step]
  simpa [restore] using h

/-- The whole chain of waiting frames rewinds in bounds (`rewinds_chain`). -/
theorem rewinds_chainW {P : Prog} (hP : P.WF) {cap : Nat} {above e : Nat} {ks : List Nat}
    {sw tw : List Frame} (hch : Chain P above e ks sw tw) :
    ∀ {fnA : FnSrc} {a : Nat} {M : Nat → W} {G : List Frame → List Frame},
      P.fnAt above = some fnA → RewindsToS cap P above fnA a M G →
      RecsAt P.frameWords M a ks tw →
      a + 4 * P.frameWords * tw.length < 2 ^ 32 + 4 * P.frameWords → a + 4 * P.frameWords * tw.length ≤ cap →
      ∀ fnE, P.fnAt e = some fnE → RewindsToS cap P e fnE (a + 4 * P.frameWords * tw.length) M
        (fun below => G (restore P.frameWords ks tw ++ below)) := by
  induction hch with
  | nil e =>
    intro fnA a M G hA hR _ _ _ fnE hE
    have hfn : fnA = fnE := Option.some.inj (hA.symm.trans hE)
    simpa [restore, ← hfn] using hR
  | cons hw _ ih => exact rewinds_consW hP hw ih

end Silmaril.Wasm.FX.Asyncify.Tool
