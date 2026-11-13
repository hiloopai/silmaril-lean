module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.Wide

/-!
# The generated code's accesses stay within `4 · max F R` of their operand

Every load and store the pass generates has an offset `o` with `o + 4 ≤ 4 · max F R`
(`envOff_asyncify`): the records use offsets below `4F`, the request area offsets below `4R`.
With `Wide`, a memory of `2 ^ 32 + 4 · max F R` bytes or more is never overrun (`safe_wide`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- Every instruction of `l` satisfies `OffI B`. -/
abbrev OffL (B : Nat) (l : List Instr) : Prop := ∀ i ∈ l, OffI B i

theorem offL_append {B : Nat} {a b : List Instr} (ha : OffL B a) (hb : OffL B b) :
    OffL B (a ++ b) := fun i hi => (List.mem_append.1 hi).elim (ha i) (hb i)

theorem offL_cons {B : Nat} {i : Instr} {l : List Instr} (hi : OffI B i) (hl : OffL B l) :
    OffL B (i :: l) := fun j hj => (List.mem_cons.1 hj).elim (fun h => h ▸ hi) (hl j)

theorem offL_nil (B : Nat) : OffL B [] := fun _ h => by cases h

/-- An instruction without access that is not an `if`. -/
theorem offI_plain {B : Nat} {i : Instr} (hf : AccFree i) (hif : ∀ bt t e, i ≠ .if_ bt t e) :
    OffI B i := .free hf hif

theorem offI_pure {B S : Nat} {i : Instr} (h : pureIns S i = true) : OffI B i := by
  have hs := pureShape h
  refine .free (accFree_of_pure hs) fun bt t e he => ?_
  subst he
  cases hs

theorem offI_gget {B : Nat} (g : GlobalIdx) : OffI B (.globalGet g) :=
  offI_plain (accFree_gget g) fun _ _ _ h => by cases h
theorem offI_gset {B : Nat} (g : GlobalIdx) : OffI B (.globalSet g) :=
  offI_plain (accFree_gset g) fun _ _ _ h => by cases h
theorem offI_c32 {B : Nat} (n : Nat) : OffI B (c32 n) :=
  offI_plain (accFree_c32 n) fun _ _ _ h => by cases h
theorem offI_get {B : Nat} (a : LocalIdx) : OffI B (.localGet a) :=
  offI_plain (accFree_get a) fun _ _ _ h => by cases h
theorem offI_set {B : Nat} (a : LocalIdx) : OffI B (.localSet a) :=
  offI_plain (accFree_set a) fun _ _ _ h => by cases h
theorem offI_rel {B : Nat} (op : IntRelOp) : OffI B (.intRelOp .i32 op) :=
  offI_plain (accFree_rel op) fun _ _ _ h => by cases h
theorem offI_bin {B : Nat} (op : IntBinOp) : OffI B (.intBinOp .i32 op) :=
  offI_plain (accFree_bin op) fun _ _ _ h => by cases h
theorem offI_ret {B : Nat} : OffI B .return_ :=
  offI_plain accFree_ret fun _ _ _ h => by cases h
theorem offI_call {B : Nat} (f : FuncIdx) : OffI B (.call f) :=
  offI_plain (accFree_call f) fun _ _ _ h => by cases h

theorem offI_st {B o : Nat} (h : o + 4 ≤ B) (ho : o < 2 ^ 64) : OffI B (st o) :=
  .store (by rw [marg_off ho]; exact h)

theorem offI_ld {B o : Nat} (h : o + 4 ≤ B) (ho : o < 2 ^ 64) : OffI B (ld o) :=
  .load (by rw [marg_off ho]; exact h)

theorem offL_saveLocals {B : Nat} : ∀ (i n : Nat), 4 * (i + n) ≤ B → 4 * (i + n) < 2 ^ 64 →
    OffL B (saveLocals i n)
  | _, 0, _, _ => offL_nil B
  | i, n + 1, h, h' => by
    have hrest := offL_saveLocals (B := B) (i + 1) n (by omega) (by omega)
    exact offL_cons (offI_gget _) (offL_cons (offI_get _)
      (offL_cons (offI_st (by omega) (by omega)) hrest))

theorem offL_loadLocals {B : Nat} : ∀ (i n : Nat), 4 * (i + n) ≤ B → 4 * (i + n) < 2 ^ 64 →
    OffL B (loadLocals i n)
  | _, 0, _, _ => offL_nil B
  | i, n + 1, h, h' => by
    have hrest := offL_loadLocals (B := B) (i + 1) n (by omega) (by omega)
    exact offL_cons (offI_gget _) (offL_cons (offI_ld (by omega) (by omega))
      (offL_cons (offI_set _) hrest))

theorem offL_pushAns {B : Nat} : ∀ (j m : Nat), 4 * (j + m) ≤ B → 4 * (j + m) < 2 ^ 64 →
    OffL B (pushAns j m)
  | _, 0, _, _ => offL_nil B
  | j, m + 1, h, h' => by
    have hrest := offL_pushAns (B := B) (j + 1) m (by omega) (by omega)
    exact offL_cons (offI_c32 _) (offL_cons (offI_ld (by omega) (by omega)) hrest)

theorem offL_reqArgs {B : Nat} : ∀ (j : Nat) (as : List LocalIdx), 4 * (j + as.length) ≤ B →
    4 * (j + as.length) < 2 ^ 64 → OffL B (reqArgs j as)
  | _, [], _, _ => offL_nil B
  | j, a :: as, h, h' => by
    have hl : 4 * (j + 1 + as.length) ≤ B := by simp only [List.length_cons] at h; omega
    have hl' : 4 * (j + 1 + as.length) < 2 ^ 64 := by simp only [List.length_cons] at h'; omega
    have hj : 4 * j + 4 ≤ B := by omega
    have hrest := offL_reqArgs (B := B) (j + 1) as hl hl'
    exact offL_cons (offI_c32 _) (offL_cons (offI_get _)
      (offL_cons (offI_st hj (by omega)) hrest))

theorem offL_gets {B : Nat} (as : List LocalIdx) : OffL B (getsCode as) := by
  intro i hi
  obtain ⟨a, -, rfl⟩ : ∃ a ∈ as, .localGet a = i := by simpa [getsCode] using hi
  exact offI_get a

theorem offL_sets {B : Nat} (rs : List LocalIdx) : OffL B (setsCode rs) := by
  intro i hi
  obtain ⟨a, -, rfl⟩ : ∃ a ∈ rs, .localSet a = i := by simpa [setsCode] using hi
  exact offI_set a

theorem offL_dummies {B : Nat} (n : Nat) : OffL B (dummies n) := by
  intro i hi
  rw [List.eq_of_mem_replicate hi]
  exact offI_c32 0

/-- The sizes of the generated code against the bound `B`. -/
structure OffCtx (B F R : Nat) : Prop where
  hF : 1 ≤ F
  hR : 1 ≤ R
  fB : 4 * F ≤ B
  rB : 4 * R ≤ B
  small : B < 2 ^ 32

theorem offL_saveCode {B F R : Nat} (X : OffCtx B F R) (k : Nat) : OffL B (saveCode F k) := by
  have hF := X.hF
  have hB := X.fB
  have hs := X.small
  refine offL_append (offL_saveLocals 0 (F - 1) (by omega) (by omega)) ?_
  exact offL_cons (offI_gget _) (offL_cons (offI_c32 _) (offL_cons (offI_st (by omega) (by omega))
    (offL_cons (offI_gget _) (offL_cons (offI_c32 _) (offL_cons (offI_bin _)
      (offL_cons (offI_gset _) (offL_nil B)))))))

theorem offL_prologue {B F R : Nat} (X : OffCtx B F R) : OffL B (prologue F) := by
  have hB := X.fB
  have hs := X.small
  have hrest : OffL B (restoreCode F) :=
    offL_append (offL_cons (offI_gget _) (offL_cons (offI_c32 _) (offL_cons (offI_bin _)
      (offL_cons (offI_gset _) (offL_nil B))))) (offL_loadLocals 0 F (by omega) (by omega))
  exact offL_cons (offI_gget _) (offL_cons (offI_c32 _) (offL_cons (offI_rel _)
    (offL_cons (.ifE hrest (offL_nil B)) (offL_nil B))))

theorem offL_chk {B F R : Nat} (X : OffCtx B F R) (k n : Nat) : OffL B (chk F k n) := by
  have harm : OffL B (saveCode F k ++ dummies n ++ [.return_]) :=
    offL_append (offL_append (offL_saveCode X k) (offL_dummies n))
      (offL_cons offI_ret (offL_nil B))
  exact offL_cons (offI_gget _) (offL_cons (offI_c32 _) (offL_cons (offI_rel _)
    (offL_cons (.ifE harm (offL_nil B)) (offL_nil B))))

/-- The translation of a call statement to an import. -/
theorem offL_imp {B F R : Nat} (X : OffCtx B F R) (k nres : Nat) (f : FuncIdx)
    (as rs : List LocalIdx) (has : as.length + 1 ≤ R) (hrs : rs.length ≤ R) :
    OffL B [gState, c32 2, eqI,
      .if_ .empty
        [.localGet (lidx (F - 1)), c32 k, eqI,
          ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)]
        (reqCode f as ++ [c32 1, sState] ++ saveCode F k ++ dummies nres ++ [.return_])] := by
  have hB := X.rB
  have hs := X.small
  have hR := X.hR
  have hans : OffL B ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs) :=
    offL_append (offL_append (offL_cons (offI_c32 _) (offL_cons (offI_gset _) (offL_nil B)))
      (offL_pushAns 0 rs.length (by omega) (by omega))) (offL_sets rs)
  have hthen : OffL B [.localGet (lidx (F - 1)), c32 k, eqI,
      ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)] :=
    offL_cons (offI_get _) (offL_cons (offI_c32 _) (offL_cons (offI_rel _)
      (offL_cons (.ifE hans (offL_nil B)) (offL_nil B))))
  have hreq : OffL B (reqCode f as) :=
    offL_cons (offI_c32 _) (offL_cons (offI_c32 _) (offL_cons (offI_st (by omega) (by omega))
      (offL_reqArgs 1 as (by omega) (by omega))))
  have helse : OffL B (reqCode f as ++ [c32 1, sState] ++ saveCode F k ++ dummies nres ++
      [.return_]) :=
    offL_append (offL_append (offL_append (offL_append hreq
      (offL_cons (offI_c32 _) (offL_cons (offI_gset _) (offL_nil B)))) (offL_saveCode X k))
      (offL_dummies nres)) (offL_cons offI_ret (offL_nil B))
  exact offL_cons (offI_gget _) (offL_cons (offI_c32 _) (offL_cons (offI_rel _)
    (offL_cons (.ifE hthen helse) (offL_nil B))))

/-- The translation of a call statement to a defined function. -/
theorem offL_def {B F R : Nat} (X : OffCtx B F R) (k nres : Nat) (f : FuncIdx)
    (as rs : List LocalIdx) :
    OffL B [gState, c32 2, neI, .localGet (lidx (F - 1)), c32 k, eqI, orI,
      ifThen (getsCode as ++ [.call f] ++ chk F k nres ++ setsCode rs)] := by
  have harm : OffL B (getsCode as ++ [.call f] ++ chk F k nres ++ setsCode rs) :=
    offL_append (offL_append (offL_append (offL_gets as) (offL_cons (offI_call f)
      (offL_nil B))) (offL_chk X k nres)) (offL_sets rs)
  exact offL_cons (offI_gget _) (offL_cons (offI_c32 2) (offL_cons (offI_rel .ne)
    (offL_cons (offI_get _) (offL_cons (offI_c32 k) (offL_cons (offI_rel .eq)
      (offL_cons (offI_bin .or) (offL_cons (.ifE harm (offL_nil B)) (offL_nil B))))))))

theorem offL_trStmt {B : Nat} {P : Prog} {S : Nat} (X : OffCtx B P.frameWords P.reqWords)
    (nres k : Nat) {s : Stmt} (hs : s.wf P S = true) :
    OffL B (trStmt ⟨P.imps.length, P.frameWords, nres⟩ k s) := by
  cases s with
  | pure is =>
    obtain ⟨-, hp, -⟩ := Stmt.wf_pure hs
    exact offL_cons (offI_gget _) (offL_cons (offI_c32 _) (offL_cons (offI_rel _)
      (offL_cons (.ifE (fun i hi => offI_pure (hp i hi)) (offL_nil B)) (offL_nil B))))
  | call f as rs =>
    obtain ⟨hsig, -, -⟩ := Stmt.wf_call hs
    by_cases hf : f.value.val < P.imps.length
    · have himp := Prog.sig_imp hsig hf
      obtain ⟨h1, h2⟩ := Prog.imp_le (List.mem_of_getElem himp)
      have h := offL_imp X k nres f as rs h1 h2
      simpa [trStmt, hf] using h
    · have h := offL_def X k nres f as rs
      simpa [trStmt, hf] using h

theorem offL_trS {B : Nat} {P : Prog} {S : Nat} (X : OffCtx B P.frameWords P.reqWords)
    (nres : Nat) : ∀ (k : Nat) (ss : List Stmt), (∀ s ∈ ss, s.wf P S = true) →
    OffL B (trS ⟨P.imps.length, P.frameWords, nres⟩ k ss)
  | _, [], _ => offL_nil B
  | k, s :: ss, h =>
    offL_append (offL_trStmt X nres k (h s (by simp)))
      (offL_trS X nres (k + 1) ss fun s' hs' => h s' (by simp [hs']))

/-- The bound of the generated code's accesses: `4 · max F R`. -/
def Prog.offB (P : Prog) : Nat := 4 * max P.frameWords P.reqWords

theorem Prog.frameWords_pos (P : Prog) : 1 ≤ P.frameWords := by
  unfold Prog.frameWords; omega

theorem Prog.offCtx {P : Prog} (hP : P.WF) : OffCtx P.offB P.frameWords P.reqWords := by
  have hb := (Prog.wf_bounds hP).2
  have hR := Prog.reqWords_pos P
  have hF := Prog.frameWords_pos P
  refine ⟨hF, hR, ?_, ?_, ?_⟩ <;> simp only [Prog.offB] <;> omega

/-- **Every body of the asyncified program has its accesses within `4 · max F R`.** -/
theorem envOff_asyncify {P : Prog} (hP : P.WF) : EnvOff P.offB (asyncifyProg P) := by
  have X := Prog.offCtx hP
  intro d hd
  obtain ⟨fn, hfn, rfl⟩ : ∃ fn ∈ P.fns,
      (⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ : FnDef) = d := by
    simpa [asyncifyProg] using hd
  have hw := Prog.wf_fns hP hfn
  have hw' : (∀ s ∈ fn.stmts, s.wf P fn.nloc = true) ∧ ∀ i ∈ fn.tail, pureIns fn.nloc i = true := by
    simp only [FnSrc.wf, Bool.and_eq_true, List.all_eq_true] at hw
    exact ⟨hw.1.1.1, hw.1.1.2⟩
  have hbody : OffL P.offB (P.tBody fn) :=
    offL_append (offL_append (offL_prologue X) (offL_trS X fn.nres 0 fn.stmts hw'.1))
      fun i hi => offI_pure (hw'.2 i hi)
  exact hbody

/-- **A memory of at least `2 ^ 32 + 4 · max F R` bytes is never overrun**, by any target run of
the asyncified program from a call of a defined function. -/
theorem safe_wide (P : Prog) (hP : P.WF) (H : Host σ) {cap : Nat} (hcap : 2 ^ 32 + P.offB ≤ cap)
    {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W) (s : σ) :
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg) (tgtSt P e fn args s) := by
  have hE := envOff_asyncify hP
  have hmem : tdef P fn ∈ (asyncifyProg P).fns := by
    have := Prog.tgt_fn hfn
    exact List.mem_of_getElem? (by simpa [tdef] using this)
  have h0 : OffCfg P.offB (tgtSt P e fn args s).cfg := by
    intro fr hfr i hi
    have hfr' : fr = entry e (tdef P fn) args := by simpa [tgtSt] using hfr
    rw [hfr'] at hi
    exact hE _ hmem i (by simpa [entry] using hi)
  intro n y hy
  exact not_oob_off (offT_runN hE H n _ h0 y hy) hcap

end Silmaril.Wasm.FX.Asyncify.Tool
