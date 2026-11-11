module

public import Silmaril.Wasm.FX.Asyncify.Tool.Thms
public import Silmaril.Wasm.FX.Asyncify.Tool.Elide.Defs

/-!
# Eliding re-entry checks: proofs

`elideS` keeps the flat code (`elideS_flat`) and well-formedness (`elideS_wf`), and its output
alternates (`elideS_alt`: every pure statement is followed by a call statement), so it has at most
as many pure statements as call statements (`Alt.checks_le`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem elideS_flat : ∀ (ss : List Stmt) (tl : List Instr),
    flatS (elideS ss tl).1 ++ (elideS ss tl).2 = flatS ss ++ tl
  | [], _ => rfl
  | .call f as rs :: r, tl => by
    simp only [elideS, flatS, List.append_assoc]
    rw [elideS_flat r tl]
  | .pure is :: r, tl => by
    have ih := elideS_flat r tl
    rcases h : elideS r tl with ⟨_ | ⟨_ | _, r'⟩, tl'⟩ <;>
      simp only [h, flatS, Stmt.code, List.append_assoc, List.nil_append] at ih ⊢ <;>
      simp only [elideS, h, flatS, Stmt.code, List.append_assoc, List.nil_append, ih]

/-- Pure statements alternate with call statements, and the last statement is a call. -/
inductive Alt : List Stmt → Prop
  | nil : Alt []
  | call {f : FuncIdx} {as rs : List LocalIdx} {r : List Stmt} : Alt r → Alt (.call f as rs :: r)
  | pc {is : List Instr} {f : FuncIdx} {as rs : List LocalIdx} {r : List Stmt} :
      Alt r → Alt (.pure is :: .call f as rs :: r)

theorem Alt.tail_call {f : FuncIdx} {as rs : List LocalIdx} {r : List Stmt}
    (h : Alt (.call f as rs :: r)) : Alt r := by
  cases h; assumption

theorem Alt.pure_inv {js : List Instr} {r : List Stmt} (h : Alt (.pure js :: r)) :
    ∃ f as rs r', r = .call f as rs :: r' ∧ Alt r' := by
  cases h with
  | pc h => exact ⟨_, _, _, _, rfl, h⟩

theorem elideS_alt : ∀ (ss : List Stmt) (tl : List Instr), Alt (elideS ss tl).1
  | [], _ => .nil
  | .call f as rs :: r, tl => .call (elideS_alt r tl)
  | .pure is :: r, tl => by
    have ih := elideS_alt r tl
    rcases h : elideS r tl with ⟨_ | ⟨_ | _, r'⟩, tl'⟩
    · simpa [elideS, h] using Alt.nil
    · rw [h] at ih
      obtain ⟨f, as, rs, r'', rfl, h''⟩ := ih.pure_inv
      simpa [elideS, h] using Alt.pc h''
    · rw [h] at ih
      simpa [elideS, h] using Alt.pc ih.tail_call

theorem Alt.checks_le : ∀ {ss : List Stmt}, Alt ss → pureChecks ss ≤ callStmts ss
  | _, .nil => le_refl _
  | _, .call h => by
    have := h.checks_le
    simp only [pureChecks, callStmts]; omega
  | _, .pc h => by
    have := h.checks_le
    simp only [pureChecks, callStmts]; omega

theorem elideS_checks : ∀ (ss : List Stmt) (tl : List Instr),
    pureChecks (elideS ss tl).1 ≤ pureChecks ss ∧ callStmts (elideS ss tl).1 = callStmts ss
  | [], _ => ⟨le_refl _, rfl⟩
  | .call f as rs :: r, tl => by
    have ih := elideS_checks r tl
    simp only [elideS, pureChecks, callStmts]; omega
  | .pure is :: r, tl => by
    have ih := elideS_checks r tl
    rcases h : elideS r tl with ⟨_ | ⟨_ | _, r'⟩, tl'⟩ <;> rw [h] at ih <;>
      simp only [elideS, h, pureChecks, callStmts] at ih ⊢ <;> omega

theorem Stmt.wf_pure_append {P : Prog} {S : Nat} {is js : List Instr}
    (hi : (Stmt.pure is).wf P S = true) (hj : (Stmt.pure js).wf P S = true) :
    (Stmt.pure (is ++ js)).wf P S = true := by
  obtain ⟨hne, hp, hd⟩ := Stmt.wf_pure hi
  obtain ⟨-, hp', hd'⟩ := Stmt.wf_pure hj
  have hne' : is ++ js ≠ [] := by simp [hne]
  have hd'' : depthAfter (is ++ js) 0 = some 0 := by rw [depthAfter_append, hd]; exact hd'
  simp only [Stmt.wf, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, beq_iff_eq, List.mem_append]
  exact ⟨⟨hne', fun i hi => hi.elim (hp i) (hp' i)⟩, hd''⟩

/-- The facts of a well-formed function body that `elideS` keeps. -/
structure BodyOk (P : Prog) (S n : Nat) (ss : List Stmt) (tl : List Instr) : Prop where
  stmts : ∀ s ∈ ss, s.wf P S = true
  tailPure : ∀ i ∈ tl, pureIns S i = true
  tailDepth : depthAfter tl 0 = some n

theorem BodyOk.sink {P : Prog} {S n : Nat} {is : List Instr} {tl : List Instr}
    (hi : (Stmt.pure is).wf P S = true) (h : BodyOk P S n [] tl) : BodyOk P S n [] (is ++ tl) := by
  obtain ⟨-, hp, hd⟩ := Stmt.wf_pure hi
  refine ⟨by simp, fun i hm => (List.mem_append.1 hm).elim (hp i) (h.tailPure i), ?_⟩
  rw [depthAfter_append, hd]; exact h.tailDepth

theorem elideS_wf {P : Prog} {S n : Nat} : ∀ (ss : List Stmt) (tl : List Instr),
    BodyOk P S n ss tl → BodyOk P S n (elideS ss tl).1 (elideS ss tl).2 ∧
      (elideS ss tl).1.length ≤ ss.length
  | [], _, h => ⟨h, le_refl _⟩
  | .call f as rs :: r, tl, h => by
    have ih := elideS_wf r tl ⟨fun s hs => h.stmts s (by simp [hs]), h.tailPure, h.tailDepth⟩
    have hc : (Stmt.call f as rs).wf P S = true := h.stmts _ (by simp)
    refine ⟨⟨fun s hs => ?_, ih.1.tailPure, ih.1.tailDepth⟩, by simpa [elideS] using ih.2⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact hc
    · exact ih.1.stmts s hs
  | .pure is :: r, tl, h => by
    have ih := elideS_wf r tl ⟨fun s hs => h.stmts s (by simp [hs]), h.tailPure, h.tailDepth⟩
    have hi : (Stmt.pure is).wf P S = true := h.stmts _ (by simp)
    rcases hr : elideS r tl with ⟨_ | ⟨_ | _, r'⟩, tl'⟩ <;> rw [hr] at ih <;> simp only [elideS, hr]
    · exact ⟨BodyOk.sink hi ih.1, by simp⟩
    · refine ⟨⟨fun s hs => ?_, ih.1.tailPure, ih.1.tailDepth⟩,
        Nat.succ_le_succ (Nat.le_of_succ_le ih.2)⟩
      rcases List.mem_cons.1 hs with rfl | hs
      · exact Stmt.wf_pure_append hi (ih.1.stmts _ (by simp))
      · exact ih.1.stmts s (by simp [hs])
    · refine ⟨⟨fun s hs => ?_, ih.1.tailPure, ih.1.tailDepth⟩, Nat.succ_le_succ ih.2⟩
      rcases List.mem_cons.1 hs with rfl | hs
      · exact hi
      · exact ih.1.stmts s hs

/-! ## Programs -/

theorem FnSrc.elide_body (fn : FnSrc) : fn.elide.body = fn.body := elideS_flat fn.stmts fn.tail

theorem Prog.elide_env (P : Prog) : P.elide.env = P.env := by
  unfold Prog.env Prog.elide
  simp only [List.map_map]
  congr 2
  funext fn
  show (⟨fn.nparams, fn.nlocals, fn.nres, fn.elide.body⟩ : FnDef) = _
  rw [FnSrc.elide_body]

theorem Prog.elide_frameWords (P : Prog) : P.elide.frameWords = P.frameWords := by
  simp only [Prog.frameWords, Prog.elide, List.map_map]
  rfl

theorem Prog.elide_sb (P : Prog) : P.elide.sb = P.sb := rfl

theorem Prog.elide_sig (P : Prog) : P.elide.sig = P.sig := by
  funext f
  unfold Prog.sig
  simp only [Prog.elide, List.getElem?_map, Option.map_map]
  rfl

theorem Stmt.wf_elide (P : Prog) (S : Nat) (s : Stmt) : s.wf P.elide S = s.wf P S := by
  cases s <;> simp [Stmt.wf, Prog.elide_sig]

theorem Prog.elide_fnAt {P : Prog} {e : Nat} {fn : FnSrc} (h : P.fnAt e = some fn) :
    P.elide.fnAt e = some fn.elide := by
  unfold Prog.fnAt at h ⊢
  have hge : P.imps.length ≤ e := by
    by_contra hlt; simp [hlt] at h
  simp only [Prog.elide, hge, ↓reduceIte, List.getElem?_map] at h ⊢
  simp [h]

theorem FnSrc.elide_wf {P : Prog} {fn : FnSrc} (h : fn.wf P = true) : fn.elide.wf P.elide = true := by
  simp only [FnSrc.wf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hb := elideS_wf (P := P) (S := fn.nloc) (n := fn.nres) fn.stmts fn.tail
    ⟨h.1.1.1, h.1.1.2, h.1.2⟩
  have hnl : fn.elide.nloc = fn.nloc := rfl
  simp only [FnSrc.wf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq, hnl,
    Stmt.wf_elide]
  exact ⟨⟨⟨hb.1.stmts, hb.1.tailPure⟩, hb.1.tailDepth⟩, by
    have := hb.2; have := h.2; simp only [FnSrc.elide]; omega⟩

theorem Prog.elide_wf {P : Prog} (hP : P.WF) : P.elide.WF := by
  simp only [Prog.WF, Prog.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hP ⊢
  refine ⟨⟨fun fn hm => ?_, by simpa [Prog.elide] using hP.1.2⟩, by
    rw [Prog.elide_frameWords]; exact hP.2⟩
  obtain ⟨fn0, hm0, rfl⟩ := List.mem_map.1 (show fn ∈ P.fns.map FnSrc.elide from hm)
  exact FnSrc.elide_wf (hP.1.1 fn0 hm0)

theorem DepthBound.elide_iff {σ : Type} (P : Prog) (H : Host σ) (x : Cfg × σ) :
    DepthBound P.elide H x ↔ DepthBound P H x := by
  simp only [DepthBound, Prog.elide_env, Prog.elide_sb, Prog.elide_frameWords]

theorem srcCfg_elide (e : Nat) (fn : FnSrc) (args : List W) :
    srcCfg e fn.elide args = srcCfg e fn args := by
  simp only [srcCfg, FnSrc.elide_body]; rfl

/-- The guards of pure statements after elision: at most one per call statement, and no more
than before. -/
theorem elide_guards (fn : FnSrc) :
    pureChecks fn.elide.stmts ≤ callStmts fn.stmts ∧
      pureChecks fn.elide.stmts ≤ pureChecks fn.stmts := by
  have h1 := (elideS_alt fn.stmts fn.tail).checks_le
  have h2 := elideS_checks fn.stmts fn.tail
  exact ⟨by simp only [FnSrc.elide]; omega, h2.1⟩

/-! ## Correctness and equivalence -/

/-- **The pass with elided checks is correct**: the asyncified `P.elide` has the behaviours of
the source `P`, under the same hypotheses as `asyncify_beh`. -/
theorem asyncify_elide_beh {σ : Type} (P : Prog) (hP : P.WF) (H : Host σ) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (s : σ)
    (hbound : DepthBound P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStep (asyncifyProg P.elide) H) (tgtSt P.elide e fn.elide args s) := by
  have hb : DepthBound P.elide H (srcCfg e fn.elide args, s) := by
    rw [DepthBound.elide_iff, srcCfg_elide]; exact hbound
  have h := asyncify_beh P.elide (Prog.elide_wf hP) H (Prog.elide_fnAt hfn) args hargs s hb
  rw [Prog.elide_env, srcCfg_elide] at h
  exact h

/-- **Eliding the checks is an equivalence of targets**: the guarded and the elided asyncified
programs have the same behaviours (both are the source's). -/
theorem elide_equiv {σ : Type} (P : Prog) (hP : P.WF) (H : Host σ) {e : Nat} {fn : FnSrc}
    (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams) (s : σ)
    (hbound : DepthBound P H (srcCfg e fn args, s)) :
    beh (tgtStep (asyncifyProg P) H) (tgtSt P e fn args s) =
      beh (tgtStep (asyncifyProg P.elide) H) (tgtSt P.elide e fn.elide args s) :=
  (asyncify_beh P hP H hfn args hargs s hbound).symm.trans
    (asyncify_elide_beh P hP H hfn args hargs s hbound)

/-! ## Modules and bytes -/

theorem asyncifyE_eq {m m' : Module} {pages : Nat} (h : asyncifyE m pages = .ok m') :
    ∃ P, recognize m = .ok P ∧ m' = asyncifyModule m P.elide pages := by
  unfold asyncifyE at h
  split at h
  · cases h
  · rename_i P hr
    refine ⟨P, hr, ?_⟩
    split at h
    · cases h
    · split at h
      · exact (Except.ok.inj h).symm
      · cases h

theorem asyncifyBytesE_inv {b b' : ByteArray} {pages : Nat} (h : asyncifyBytesE b pages = .ok b') :
    ∃ m m' bs, Binary.Core.decode? b = some m ∧ asyncifyE m pages = .ok m' ∧
      Binaryen.Exe.encodeModule? m' = .ok bs ∧ b' = ⟨bs.toArray⟩ := by
  unfold asyncifyBytesE at h
  split at h
  · cases h
  · rename_i m hd
    split at h
    · cases h
    · rename_i m' ha
      split at h
      · rename_i bs he
        exact ⟨m, m', bs, hd, ha, he, (Except.ok.inj h).symm⟩
      · cases h

/-- **The tool with elided checks, on bytes.** As `asyncifyBytes_spec`, for the elided program
`P0.elide` of the recognised `P0`; its pure statements have at most one check per call
statement. -/
theorem asyncifyBytesE_spec {b b' : ByteArray} {pages : Nat} (h : asyncifyBytesE b pages = .ok b') :
    ∃ m P0 m', Binary.Core.decode? b = some m ∧ Binary.Core.Encodes b.data.toList m ∧
      recognize m = .ok P0 ∧ P0.WF ∧ envOf m = some P0.elide.env ∧
      m' = asyncifyModule m P0.elide pages ∧ Binary.Core.Encodes b'.data.toList m' ∧
      envOfLax m' = some (asyncifyProg P0.elide) ∧ globalsOfLax m' = some P0.elide.tGlobals ∧
      (∀ name, exportFunc m' name = exportFunc m name) ∧
      (∀ fn ∈ P0.fns, pureChecks fn.elide.stmts ≤ callStmts fn.stmts) := by
  obtain ⟨m, m', bs, hd, ha, he, hb'⟩ := asyncifyBytesE_inv h
  obtain ⟨P0, hr, hm'⟩ := asyncifyE_eq ha
  obtain ⟨hwf, henv⟩ := recognize_sound hr
  have henv' : envOf m = some P0.elide.env := by rw [Prog.elide_env]; exact henv
  have henc : Binary.Core.Encodes b'.data.toList m' := by
    rw [hb']; simpa using Binaryen.Exe.encodeModule?_sound he
  refine ⟨m, P0, m', hd, Binary.Core.decode?_sound hd, hr, hwf, henv', hm', henc, ?_, ?_, ?_,
    fun fn _ => (elide_guards fn).1⟩
  · rw [hm']; exact envOfLax_asyncifyModule henv' pages
  · rw [hm']; exact globalsOfLax_asyncifyModule m P0.elide pages
  · rw [hm']; exact exportFunc_asyncifyModule m P0.elide pages

/-- **End to end, with elided checks.** When `asyncifyBytesE` turns `b` into `b'`, the input
decodes to `m` (source program `P0`), `b'` encodes a module read back as `asyncifyProg P0.elide`,
and every call has the same behaviours in `m` (suspending) and in `b'` (asyncify protocol); the
same calls in the guarded output (`asyncifyProg P0`) have the same behaviours as well. -/
theorem asyncifyBytesE_correct {b b' : ByteArray} {pages : Nat}
    (h : asyncifyBytesE b pages = .ok b') :
    ∃ m P0 m', Binary.Core.decode? b = some m ∧ Binary.Core.Encodes b'.data.toList m' ∧
      recognize m = .ok P0 ∧ envOf m = some P0.env ∧
      envOfLax m' = some (asyncifyProg P0.elide) ∧ globalsOfLax m' = some P0.elide.tGlobals ∧
      (∀ name, exportFunc m' name = exportFunc m name) ∧
      ∀ {σ : Type} (H : Host σ) {e : Nat} {fn : FnSrc} (args : List W) (s : σ),
        P0.fnAt e = some fn → args.length = fn.nparams → DepthBound P0 H (srcCfg e fn args, s) →
        beh (srcStep P0.env H) (srcCfg e fn args, s) =
          beh (tgtStep (asyncifyProg P0.elide) H) (tgtSt P0.elide e fn.elide args s) ∧
        beh (tgtStep (asyncifyProg P0) H) (tgtSt P0 e fn args s) =
          beh (tgtStep (asyncifyProg P0.elide) H) (tgtSt P0.elide e fn.elide args s) := by
  obtain ⟨m, P0, m', hd, -, hr, hwf, -, -, he, hlax, hgl, hex, -⟩ := asyncifyBytesE_spec h
  have henv : envOf m = some P0.env := (recognize_sound hr).2
  exact ⟨m, P0, m', hd, he, hr, henv, hlax, hgl, hex, fun {_} H {_} {_} args s hfn hargs hb =>
    ⟨asyncify_elide_beh P0 hwf H hfn args hargs s hb, elide_equiv P0 hwf H hfn args hargs s hb⟩⟩

end Silmaril.Wasm.FX.Asyncify.Tool
