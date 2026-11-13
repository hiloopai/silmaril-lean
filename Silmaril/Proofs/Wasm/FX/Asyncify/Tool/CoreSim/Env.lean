module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Body
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Step

/-!
# Every function of the asyncified program checks

`ck_trStmt`: the translation of a well-formed statement checks from and to the empty stack;
`tbody_ck`: the asyncified body checks to its result count; `envOk_asyncify`: `EnvOk` of
`asyncifyProg P` for a well-formed `P`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm
open Silmaril.Wasm.FX.Asyncify.Tool

variable {X : CkCtx} {P : Prog} {fn : FnSrc}

theorem ck_trImport (h : BodyCtx P fn X) (k : Nat) {f : FuncIdx} {as rs : List LocalIdx}
    (hlt : f.value.val < P.imps.length) (hsig : P.sig f.value.val = some (as.length, rs.length))
    (ha : ∀ x ∈ as, x.value.val < fn.nloc) (hr : ∀ r ∈ rs, r.value.val < fn.nloc) :
    Run X [gState, c32 2, eqI,
      .if_ .empty
        [.localGet (lidx ((P.ctx fn).F - 1)), c32 k, eqI,
          ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)]
        (reqCode f as ++ [c32 1, sState] ++ saveCode (P.ctx fn).F k ++ dummies (P.ctx fn).nres ++
          [.return_])] [] [] := by
  have hmem : (as.length, rs.length) ∈ P.imps := by
    rw [← Prog.sig_imp hsig hlt]; exact List.getElem_mem hlt
  have hb := Prog.imp_le hmem
  have hw := h.bound
  have hA : Ck X (· = []) [.localGet (lidx (P.frameWords - 1)), c32 k, eqI,
      ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)] [] :=
    ck_seq (ins1 (.get h.sel)) (ck_seq (run_c32 k _) (ck_seq (run_rel _ _ [])
      (.ifE (ck_resumeArm h hr (by omega)) (.nil rfl) (.nil rfl))))
  exact ck_seq (run_gState []) (ck_seq (run_c32 2 _) (ck_seq (run_rel _ _ [])
    (.ifE hA (ck_requestArm h k ha (by omega)) (.nil rfl))))

theorem ck_callArm (h : BodyCtx P fn X) (k : Nat) {f : FuncIdx} {as rs : List LocalIdx}
    (hge : P.imps.length ≤ f.value.val) (hsig : P.sig f.value.val = some (as.length, rs.length))
    (ha : ∀ x ∈ as, x.value.val < fn.nloc) (hr : ∀ r ∈ rs, r.value.val < fn.nloc) :
    Ck X (· = []) (getsCode as ++ [.call f] ++ chk P.frameWords k fn.nres ++ setsCode rs) [] := by
  obtain ⟨fn', hat, hn, hm⟩ := Prog.sig_fn hsig hge
  have hfd := Prog.tgt_fn hat
  have hg := run_getsCode (X := X) [] fun x hx => Nat.lt_of_lt_of_le (ha x hx) h.loc
  have hc : Run X [.call f] (List.replicate as.length false ++ [])
      (List.replicate fn'.nres false ++ (List.replicate as.length false ++ []).drop fn'.nparams) :=
    ins1 (InsOk.call (a := List.replicate as.length false ++ []) (by rw [h.env]; exact hge)
      (by rw [h.env]; exact hfd)
      (by simp [hn]))
  have he : List.replicate fn'.nres false ++ (List.replicate as.length false ++ []).drop
      fn'.nparams = List.replicate rs.length false ++ [] := by
    simp only [List.append_nil, hn, hm, List.drop_replicate, Nat.sub_self, List.replicate_zero]
  rw [he] at hc
  have hk := run_chk (X := X) k h.frame.symm h.hL h.hF1 (List.replicate rs.length false ++ [])
  rw [h.nres] at hk
  have hs := run_setsCode (X := X) (p := List.replicate rs.length false) (by have := h.hL; omega)
    [] (List.length_replicate ..) fun r hm => Nat.lt_of_lt_of_le (hr r hm) h.loc
  exact ck_seq (ck_seq (ck_seq hg hc) hk) hs

theorem ck_trStmt (h : BodyCtx P fn X) (k : Nat) :
    ∀ s : Stmt, s.wf P fn.nloc = true → Run X (trStmt (P.ctx fn) k s) [] []
  | .pure _, hw => ck_trPure h k hw
  | .call f as rs, hw => by
    obtain ⟨hsig, ha, hr⟩ := Stmt.wf_call hw
    by_cases hlt : f.value.val < P.imps.length
    · have e : trStmt (P.ctx fn) k (.call f as rs) = [gState, c32 2, eqI,
          .if_ .empty
            [.localGet (lidx ((P.ctx fn).F - 1)), c32 k, eqI,
              ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)]
            (reqCode f as ++ [c32 1, sState] ++ saveCode (P.ctx fn).F k ++
              dummies (P.ctx fn).nres ++ [.return_])] := by
        simp only [trStmt, Prog.ctx, hlt, ite_true]
      rw [e]; exact ck_trImport h k hlt hsig ha hr
    · have e : trStmt (P.ctx fn) k (.call f as rs) = [gState, c32 2, neI,
          .localGet (lidx (P.frameWords - 1)), c32 k, eqI, orI,
          ifThen (getsCode as ++ [.call f] ++ chk P.frameWords k fn.nres ++ setsCode rs)] := by
        simp only [trStmt, Prog.ctx, hlt, ite_false]
      rw [e]
      exact ck_seq (run_gState []) (ck_seq (run_c32 2 _) (ck_seq (run_rel _ _ [])
        (ck_seq (ins1 (.get h.sel)) (ck_seq (run_c32 k _) (ck_seq (run_rel _ _ _)
          (ck_seq (ins1 .bin) (.ifE (ck_callArm h k (by omega) hsig ha hr) (.nil rfl)
            (.nil rfl))))))))

theorem run_trS (h : BodyCtx P fn X) :
    ∀ (k : Nat) (ss : List Stmt), (∀ s ∈ ss, s.wf P fn.nloc = true) →
      Run X (trS (P.ctx fn) k ss) [] []
  | _, [], _ => .nil rfl
  | k, s :: ss, hw => ck_seq (ck_trStmt h k s (hw s (List.mem_cons_self ..)))
      (run_trS h (k + 1) ss fun s' hs => hw s' (List.mem_cons_of_mem _ hs))

/-- **An asyncified body checks** to its result count. -/
theorem tbody_ck (h : BodyCtx P fn X) :
    Ck X (fun a => a.length = fn.nres) (P.tBody fn) [] := by
  obtain ⟨a', hl, hr⟩ := pure_run h.loc fn.tail [] h.ok.tailPure h.ok.tailDepth
  exact ck_seq (ck_seq (run_prologue h.frame.symm h.hL []) (run_trS h 0 fn.stmts h.ok.stmts))
    (ck_mono hr fun b hb => hb ▸ hl)

/-- **Every function of the asyncified program checks.** -/
theorem envOk_asyncify (hP : P.WF) : EnvOk (asyncifyProg P) := by
  intro j fd hj
  have hj' : (P.fns.map fun fn => (⟨fn.nparams, P.frameWords - fn.nparams, fn.nres,
      P.tBody fn⟩ : FnDef))[j]? = some fd := hj
  rw [List.getElem?_map] at hj'
  obtain ⟨fn, hfn, hfd⟩ := Option.map_eq_some_iff.1 hj'
  have hat : P.fnAt (j + P.imps.length) = some fn := by
    simp only [Prog.fnAt, Nat.le_add_left, ite_true, Nat.add_sub_cancel, hfn]
  have hok := Prog.fnOk hP hat
  have hL : fn.nparams + (P.frameWords - fn.nparams) = P.frameWords := by
    have := hok.nloc; unfold FnSrc.nloc at this; omega
  rw [← hfd]
  show Ck ⟨asyncifyProg P, fn.nparams + (P.frameWords - fn.nparams), fn.nres⟩ _ (P.tBody fn) []
  rw [hL]
  exact tbody_ck ⟨rfl, rfl, rfl, hok, (Prog.wf_bounds hP).2⟩

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
