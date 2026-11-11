module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Rewind

/-!
# Rewinding: skipping the statements before the resume point, and the two call sites
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem frame_eta_code (fr : Frame) (c : List Instr) :
    { { fr with code := c } with locals := fr.locals, ops := fr.ops, code := c } = { fr with code := c } :=
  rfl

/-- One statement before the resume point is skipped when rewinding. -/
theorem steps_skip1 {P : Prog} {fn : FnSrc} {fr : Frame} {rest : List Frame} {K : List Instr}
    {sp : W} {M : Nat → W} {k j : Nat} (s : Stmt)
    (hl : fr.locals.length = P.frameWords) (hF : 1 ≤ P.frameWords) (hF2 : P.frameWords < 2 ^ 32)
    (hsel : fr.locals[P.frameWords - 1]? = some (BitVec.ofNat 32 k)) (hk : k < 2 ^ 32)
    (hjk : j < k) :
    ∃ n, Steps (asyncifyProg P) n ⟨{ fr with code := trStmt (P.ctx fn) j s ++ K } :: rest, [2, sp], M⟩
      ⟨{ fr with code := K } :: rest, [2, sp], M⟩ := by
  have hne : k ≠ j := by omega
  cases s with
  | pure is =>
    have e := steps_ite (E := asyncifyProg P) (fr := fr) (rest := rest) (t := is) (e := []) (K := K)
      (seg_ne2_rw fr.locals fr.ops sp M)
    exact ⟨_, by simpa [trStmt, ifThen] using e⟩
  | call f as rs =>
    by_cases hf : f.value.val < P.imps.length
    · have e1 := steps_ite (E := asyncifyProg P) (fr := fr) (rest := rest)
        (t := [.localGet (lidx (P.frameWords - 1)), c32 j, eqI,
          ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)])
        (e := reqCode f as ++ [c32 1, sState] ++ saveCode P.frameWords j ++ dummies fn.nres ++
          [.return_]) (K := K) (seg_eq2_rw fr.locals fr.ops sp M)
      have e2 := steps_ite (E := asyncifyProg P) (fr := fr) (rest := rest)
        (t := [c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs) (e := []) (K := K)
        (seg_sel (g := [2, sp]) (m := M) (ops := fr.ops) hl hF hF2 hsel hk (j := j) (by omega))
      simp only [hne, ↓reduceIte] at e2
      refine ⟨_, Steps.trans (by simpa [trStmt, hf, Prog.ctx] using e1) (by simpa [ifThen] using e2)⟩
    · have hseg : runSeg [gState, c32 2, neI, .localGet (lidx (P.frameWords - 1)), c32 j, eqI, orI]
          ⟨fr.locals, fr.ops, [2, sp], M⟩ = some ⟨fr.locals, 0 :: fr.ops, [2, sp], M⟩ := by
        have h1 : [gState, c32 2, neI, .localGet (lidx (P.frameWords - 1)), c32 j, eqI, orI] =
            [gState, c32 2, neI] ++ ([.localGet (lidx (P.frameWords - 1)), c32 j, eqI] ++ [orI]) := rfl
        rw [h1, runSeg_append, seg_ne2_rw, Option.bind_some, runSeg_append,
          seg_sel (j := j) hl hF hF2 hsel hk (by omega), Option.bind_some]
        simp [hne, runSeg, segStep, ctlOf, segCore, pexec, orI, Numerics.intBinOp]
      have e := steps_ite (E := asyncifyProg P) (fr := fr) (rest := rest)
        (t := getsCode as ++ [.call f] ++ chk P.frameWords j fn.nres ++ setsCode rs) (e := [])
        (K := K) hseg
      exact ⟨_, by simpa [trStmt, hf, Prog.ctx, ifThen] using e⟩

/-- The statements before the resume point are skipped when rewinding. -/
theorem steps_skip {P : Prog} {fn : FnSrc} {fr : Frame} {rest : List Frame} {K : List Instr}
    {sp : W} {M : Nat → W} {k : Nat}
    (hl : fr.locals.length = P.frameWords) (hF : 1 ≤ P.frameWords) (hF2 : P.frameWords < 2 ^ 32)
    (hsel : fr.locals[P.frameWords - 1]? = some (BitVec.ofNat 32 k)) (hk : k < 2 ^ 32) :
    ∀ (ss : List Stmt) (j : Nat), j + ss.length ≤ k →
      ∃ n, Steps (asyncifyProg P) n ⟨{ fr with code := trS (P.ctx fn) j ss ++ K } :: rest, [2, sp], M⟩
        ⟨{ fr with code := K } :: rest, [2, sp], M⟩
  | [], j, _ => ⟨0, by simpa [trS] using Steps.refl _⟩
  | s :: ss, j, h => by
    simp only [List.length_cons] at h
    obtain ⟨n1, e1⟩ := steps_skip1 (fn := fn) (fr := fr) (rest := rest)
      (K := trS (P.ctx fn) (j + 1) ss ++ K) (sp := sp) (M := M) (j := j) s hl hF hF2 hsel hk (by omega)
    obtain ⟨n2, e2⟩ := steps_skip (fn := fn) (fr := fr) (rest := rest) (K := K) (sp := sp) (M := M)
      hl hF hF2 hsel hk ss (j + 1) (by omega)
    exact ⟨n1 + n2, by simpa [trS, List.append_assoc] using e1.trans e2⟩

end Silmaril.Wasm.FX.Asyncify.Tool
