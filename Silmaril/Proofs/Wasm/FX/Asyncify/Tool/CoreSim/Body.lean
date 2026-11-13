module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Typed

/-!
# Asyncified bodies pass the checker

Pure source code checks with its stack depths (`pure_run`); the translation of each statement
checks from and to the empty stack (`ck_trPure`, `ck_trImport`, `ck_trCall`), hence the
statements (`run_trS`) and the whole body (`tbody_ck`); `envOk_asyncify`: every function of
`asyncifyProg P` checks, for a well-formed `P`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm
open Silmaril.Wasm.FX.Asyncify.Tool

variable {X : CkCtx}

/-! ## Pure code -/

/-- One pure instruction checks, with the stack effect `eff`. -/
theorem pure_ins {S : Nat} (hS : S ≤ X.L) :
    ∀ {i : Instr} (a : List Bool), PureShape S i → (eff i).1 ≤ a.length →
      ∃ a', a'.length = a.length - (eff i).1 + (eff i).2 ∧ InsOk X i a a'
  | _, a, .nop, _ => ⟨a, by simp [eff], .nop⟩
  | _, _ :: a, .drop, _ => ⟨a, by simp [eff], .drop⟩
  | _, [], .drop, hd => absurd hd (by simp [eff])
  | _, a, .get _ hx, _ => ⟨false :: a, by simp [eff], .get (by omega)⟩
  | _, _ :: a, .set _ hx, _ => ⟨a, by simp [eff], .set (by omega)⟩
  | _, [], .set _ _, hd => absurd hd (by simp [eff])
  | _, _ :: a, .tee _ hx, _ => ⟨false :: a, by simp [eff], .tee (by omega)⟩
  | _, [], .tee _ _, hd => absurd hd (by simp [eff])
  | _, a, .const _, _ => ⟨_ :: a, by simp [eff], .const⟩
  | _, _ :: a, .un _, _ => ⟨false :: a, by simp [eff], .un⟩
  | _, [], .un _, hd => absurd hd (by simp [eff])
  | _, _ :: _ :: a, .bin _, _ => ⟨_ :: a, by simp [eff], .bin⟩
  | _, [], .bin _, hd => absurd hd (by simp [eff])
  | _, [_], .bin _, hd => absurd hd (by simp [eff])
  | _, _ :: a, .test _, _ => ⟨false :: a, by simp [eff], .test⟩
  | _, [], .test _, hd => absurd hd (by simp [eff])
  | _, _ :: _ :: a, .rel _, _ => ⟨false :: a, by simp [eff], .rel⟩
  | _, [], .rel _, hd => absurd hd (by simp [eff])
  | _, [_], .rel _, hd => absurd hd (by simp [eff])

theorem depthAfter_cons {i : Instr} {is : List Instr} {d d' : Nat}
    (h : depthAfter (i :: is) d = some d') :
    (eff i).1 ≤ d ∧ depthAfter is (d - (eff i).1 + (eff i).2) = some d' := by
  unfold depthAfter at h
  by_cases hd : (eff i).1 ≤ d
  · rw [ite_eq_left_iff.2 (fun h' => absurd hd h')] at h; exact ⟨hd, h⟩
  · rw [ite_eq_right_iff.2 (fun h' => absurd h' hd)] at h; cases h

/-- Pure code checks, with the depths of `depthAfter`. -/
theorem pure_run {S : Nat} (hS : S ≤ X.L) :
    ∀ (is : List Instr) (a : List Bool) {d' : Nat}, (∀ i ∈ is, pureIns S i = true) →
      depthAfter is a.length = some d' → ∃ a', a'.length = d' ∧ Run X is a a'
  | [], a, _, _, hd => ⟨a, Option.some.inj hd, .nil rfl⟩
  | i :: is, a, _, hp, hd => by
    obtain ⟨hle, hd'⟩ := depthAfter_cons hd
    obtain ⟨a₁, hl₁, hI⟩ := pure_ins hS a (pureShape (hp i (List.mem_cons_self ..))) hle
    obtain ⟨a', hl', hr⟩ := pure_run hS is a₁ (fun j hj => hp j (List.mem_cons_of_mem _ hj))
      (by rw [hl₁]; exact hd')
    exact ⟨a', hl', .ins hI hr⟩

/-! ## Statements -/

/-- The facts about a function of a well-formed program that the checker needs. -/
structure BodyCtx (P : Prog) (fn : FnSrc) (X : CkCtx) : Prop where
  env : X.E = asyncifyProg P
  frame : X.L = P.frameWords
  nres : X.nres = fn.nres
  ok : FnOk P fn
  bound : 4 * P.frameWords + 4 * P.reqWords < 2 ^ 24

theorem BodyCtx.hL {P : Prog} {fn : FnSrc} (h : BodyCtx P fn X) : X.L < 2 ^ 26 := by
  have := h.bound; rw [h.frame]; omega

theorem BodyCtx.hF1 {P : Prog} {fn : FnSrc} (h : BodyCtx P fn X) : 1 ≤ P.frameWords := by
  have := h.ok.nloc; omega

theorem BodyCtx.loc {P : Prog} {fn : FnSrc} (h : BodyCtx P fn X) : fn.nloc ≤ X.L := by
  have := h.ok.nloc; rw [h.frame]; omega

theorem BodyCtx.sel {P : Prog} {fn : FnSrc} (h : BodyCtx P fn X) :
    (lidx (P.frameWords - 1)).value.val < X.L :=
  lidx_lt (by have := h.hF1; rw [h.frame]; omega) (by have := h.hL; omega)

theorem ck_trPure {P : Prog} {fn : FnSrc} (h : BodyCtx P fn X) (k : Nat) {is : List Instr}
    (hw : (Stmt.pure is).wf P fn.nloc = true) : Run X (trStmt (P.ctx fn) k (.pure is)) [] [] := by
  obtain ⟨-, hp, hd⟩ := Stmt.wf_pure hw
  obtain ⟨a', hl, hr⟩ := pure_run h.loc is [] hp hd
  have harm : Run X is [] [] := List.eq_nil_of_length_eq_zero hl ▸ hr
  exact ck_seq (run_gState []) (ck_seq (run_c32 2 _) (ck_seq (run_rel _ _ [])
    (.ifE harm (.nil rfl) (.nil rfl))))

/-- After a blocking call: set `state := 0`, push the answers, store them. -/
theorem ck_resumeArm {P : Prog} {fn : FnSrc} (h : BodyCtx P fn X) {rs : List LocalIdx}
    (hr : ∀ r ∈ rs, r.value.val < fn.nloc) (hm : rs.length < 2 ^ 59) :
    Run X ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs) [] [] := by
  have h1 : Run X [c32 0, sState] [] [] := ck_seq (run_c32_al (n := 0) rfl []) (run_sState true [])
  have h2 := run_pushAns (X := X) 0 rs.length [] (by omega)
  have h3 := run_setsCode (X := X) (p := List.replicate rs.length false) (by have := h.hL; omega)
    [] (List.length_replicate ..)
    fun r hm => Nat.lt_of_lt_of_le (hr r hm) h.loc
  exact ck_seq (ck_seq h1 h2) h3

/-- Before a blocking call: write the request, set `state := 1`, save the frame, return. -/
theorem ck_requestArm {P : Prog} {fn : FnSrc} (h : BodyCtx P fn X) (k : Nat) {f : FuncIdx}
    {as : List LocalIdx} (ha : ∀ x ∈ as, x.value.val < fn.nloc) (hn : as.length < 2 ^ 59) :
    Ck X (· = []) (reqCode f as ++ [c32 1, sState] ++ saveCode P.frameWords k ++
      dummies fn.nres ++ [.return_]) [] := by
  have hreq : Run X (reqCode f as) [] [] :=
    ck_seq (ck_seq (run_c32_al (n := 0) rfl []) (ck_seq (run_c32 _ _) (run_st (o := 0) rfl
      (by decide) _ []))) (run_reqArgs 1 as [] (by omega)
        fun x hx => Nat.lt_of_lt_of_le (ha x hx) h.loc)
  have hset : Run X [c32 1, sState] [] [] := ck_seq (run_c32 1 _) (run_sState _ [])
  have hsave := ck_saveRet (X := X) k h.frame.symm h.hL h.hF1
  rw [h.nres] at hsave
  simp only [List.append_assoc] at hsave ⊢
  exact ck_seq hreq (ck_seq hset hsave)

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
