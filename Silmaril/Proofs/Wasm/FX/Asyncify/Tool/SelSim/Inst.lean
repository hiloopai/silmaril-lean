module

public import Silmaril.Wasm.FX.Asyncify.Tool.SelSim.Defs
public import Silmaril.Wasm.FX.Asyncify.Tool.Selective.Thms
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.SelSim.Main
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Calm.Basic

/-!
# The selective program satisfies `SelOk`

`selProg_selOk`: for a well-formed `P`, the selective program `selProg P` is well formed up to
pure statements holding calls of the calm functions `SelCalm P` (`SelOk`): the reclassified
statements are call statements of `P` to calm functions, and the statements of a calm function
are all reclassified, because a calm function calls calm functions only (`calm_calls`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem selProg_imps (P : Prog) : (selProg P).imps = P.imps := rfl

theorem selProg_fns (P : Prog) : (selProg P).fns = P.fns.map (selFn P) := rfl

theorem selProg_fnAt {P : Prog} {fid : Nat} :
    (selProg P).fnAt fid = (P.fnAt fid).map (selFn P) := by
  unfold Prog.fnAt
  by_cases h : P.imps.length ≤ fid <;> simp [selProg_imps, selProg_fns, h]

theorem selProg_sig (P : Prog) (g : Nat) : (selProg P).sig g = P.sig g := by
  unfold Prog.sig
  by_cases h : g < P.imps.length <;> simp [selProg_imps, selProg_fns, h, Function.comp_def, selFn]

theorem selFn_nloc (P : Prog) (fn : FnSrc) : (selFn P fn).nloc = fn.nloc := rfl

theorem selFn_body (P : Prog) (fn : FnSrc) : (selFn P fn).body = fn.body := by
  simp [selFn, FnSrc.body, flatS_selStmt]

theorem wf_call_sel {P : Prog} {S : Nat} {f : FuncIdx} {as rs : List LocalIdx} :
    (Stmt.call f as rs).wf (selProg P) S = (Stmt.call f as rs).wf P S := by
  simp [Stmt.wf, selProg_sig]

/-- A statement of `P`, reclassified, satisfies `StmtOk` for the selective program. -/
theorem selStmt_ok {P : Prog} {S : Nat} {st : Stmt} (h : st.wf P S = true) :
    StmtOk (selProg P) (SelCalm P) S (selStmt P st) := by
  cases st with
  | pure is => exact Or.inl h
  | call f as rs =>
    obtain ⟨hsig, -, -⟩ := Stmt.wf_call h
    by_cases hc : P.imps.length ≤ f.value.val ∧ mayS P f.value.val = false
    · simp only [selStmt, hc, and_self, ↓reduceIte]
      have hlt : f.value.val < P.imps.length + P.fns.length := by
        unfold Prog.sig at hsig
        rw [dite_eq_right_of_eq_false (eq_false (by omega))] at hsig
        cases hg : P.fns[f.value.val - P.imps.length]? with
        | none => rw [hg] at hsig; cases hsig
        | some _ =>
          have := (List.getElem?_eq_some_iff.1 hg).1
          omega
      exact Or.inr ⟨f, as, rs, rfl, ⟨hc.1, hlt, hc.2⟩, by rw [wf_call_sel]; exact h⟩
    · simp only [selStmt, hc, ↓reduceIte]
      show (Stmt.call f as rs).wf (selProg P) S = true
      rw [wf_call_sel]; exact h

theorem selProg_frameWords' (P : Prog) : (selProg P).frameWords = P.frameWords :=
  selProg_frameWords P

/-- The functions of the selective program satisfy `FnOkS`. -/
theorem selProg_fnOkS {P : Prog} (hP : P.WF) {fid : Nat} {fn' : FnSrc}
    (hfn' : (selProg P).fnAt fid = some fn') : FnOkS (selProg P) (SelCalm P) fn' := by
  obtain ⟨fn, hfn, rfl⟩ : ∃ fn, P.fnAt fid = some fn ∧ selFn P fn = fn' :=
    Option.map_eq_some_iff.1 (by rw [← selProg_fnAt]; exact hfn')
  have hok : FnOk P fn := Prog.fnOk hP hfn
  have hst : ∀ s ∈ (selFn P fn).stmts, StmtOk (selProg P) (SelCalm P) fn.nloc s := by
    intro s hs
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hs
    exact selStmt_ok (hok.stmts st hst)
  have hn : (selFn P fn).stmts.length < 2 ^ 31 := by simpa [selFn] using hok.nstmts
  have hl : (selFn P fn).nloc + 1 ≤ (selProg P).frameWords := by
    rw [selFn_nloc, selProg_frameWords']; exact hok.nloc
  exact ⟨hst, hok.tailPure, hok.tailDepth, hn, hl⟩

/-- A calm function is a function of the selective program. -/
theorem selProg_calmFn {P : Prog} {g : Nat} (hg : SelCalm P g) :
    ∃ fn, (selProg P).fnAt g = some fn := by
  obtain ⟨hge, hlt, -⟩ := hg
  have hi : g - P.imps.length < P.fns.length := by omega
  refine ⟨selFn P P.fns[g - P.imps.length], ?_⟩
  rw [selProg_fnAt]
  simp [Prog.fnAt, hge, List.getElem?_eq_getElem hi]

/-- The statements of a calm function are pure in the selective program. -/
theorem selProg_calmPure {P : Prog} {g : Nat} {fn' : FnSrc} (hg : SelCalm P g)
    (hfn' : (selProg P).fnAt g = some fn') : ∀ s ∈ fn'.stmts, ∃ is, s = .pure is := by
  obtain ⟨hge, -, hcalm⟩ := hg
  obtain ⟨fn, hfn, rfl⟩ : ∃ fn, P.fnAt g = some fn ∧ selFn P fn = fn' :=
    Option.map_eq_some_iff.1 (by rw [← selProg_fnAt]; exact hfn')
  have hget : P.fns[g - P.imps.length]? = some fn := by
    unfold Prog.fnAt at hfn; simpa [hge] using hfn
  intro s hs
  obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hs
  cases st with
  | pure is => exact ⟨is, rfl⟩
  | call f as rs =>
    have hf : mayS P f.value.val = false := calm_calls hcalm hget hst
    exact ⟨(Stmt.call f as rs).code, by simp [selStmt, calm_defined hf, hf]⟩

/-- **The selective program is well formed up to calm calls.** -/
theorem selProg_selOk {P : Prog} (hP : P.WF) : SelOk (selProg P) (SelCalm P) where
  bounds := by
    have := Prog.wf_bounds hP
    simpa [selProg_imps, selProg_fns, selProg_frameWords', selProg_reqWords] using this
  fn := selProg_fnOkS hP
  calmFn := selProg_calmFn
  calmPure := selProg_calmPure

end Silmaril.Wasm.FX.Asyncify.Tool
