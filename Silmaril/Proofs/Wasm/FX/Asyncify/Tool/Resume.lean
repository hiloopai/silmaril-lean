module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Skip

/-!
# Rewinding a whole chain: from the export call back to the suspension point
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- The machine function of an asyncified function. -/
def tdef (P : Prog) (fn : FnSrc) : FnDef := ⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩

/-- Calling function `fid` in rewind mode with `sp = a` re-creates the frames `G below` on top of
any frames `below`, ending in normal mode with `sp = SB`. -/
def RewindsTo (P : Prog) (fid : Nat) (fn : FnSrc) (a : Nat) (M : Nat → W)
    (G : List Frame → List Frame) : Prop :=
  ∀ below args, args.length = fn.nparams → ∃ n, Steps (asyncifyProg P) n
    ⟨entry fid (tdef P fn) args :: below, [2, BitVec.ofNat 32 a], M⟩
    ⟨G below, [0, BitVec.ofNat 32 P.sb], M⟩

/-- The waiting frames with their saved locals. -/
def restore (F : Nat) : List Nat → List Frame → List Frame
  | k :: ks, w :: ws => { w with locals := recOf F k w.locals } :: restore F ks ws
  | _, _ => []

theorem recOf_sel {F k : Nat} {tl : List W} (h : tl.length = F) (_hF : 1 ≤ F) :
    (recOf F k tl)[F - 1]? = some (BitVec.ofNat 32 k) := by
  have hlen : (tl.take (F - 1)).length = F - 1 := by simp [h]
  rw [recOf, List.getElem?_append_right (by omega), hlen, Nat.sub_self]; rfl

theorem entry_len {P : Prog} {fn : FnSrc} {fid : Nat} {args : List W} (hargs : args.length = fn.nparams)
    (hF : fn.nloc + 1 ≤ P.frameWords) : (entry fid (tdef P fn) args).locals.length = P.frameWords := by
  simp [entry, tdef, hargs, FnSrc.nloc] at *; omega

/-- The innermost frame: the import site it suspended at. -/
theorem rewinds_base {P : Prog} (hP : P.WF) {fid : Nat} {fn : FnSrc} {pre rest : List Stmt}
    {f : FuncIdx} {as rs : List LocalIdx} {tl : List W} {M : Nat → W}
    (hfn : P.fnAt fid = some fn) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    (hf : f.value.val < P.imps.length) (htl : tl.length = P.frameWords)
    (hrec : readWords M P.sb P.frameWords = recOf P.frameWords pre.length tl) :
    RewindsTo P fid fn (P.sb + 4 * P.frameWords) M fun below =>
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

end Silmaril.Wasm.FX.Asyncify.Tool
