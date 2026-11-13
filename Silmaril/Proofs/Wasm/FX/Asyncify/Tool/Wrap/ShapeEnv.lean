module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Wrap.Shape

/-!
# Every asyncified body has the request-access shape

`envOK_asyncify`: every body of `asyncifyProg P` is `CodeOK P.frameWords P.reqWords`. The record
code (`saveCode`, `restoreCode`) uses offsets below `4 F`; the request code writes the import
index at offset `0` and every argument as `c32 0, local.get a, st (4 j)`, and the answers are read
as `c32 0, ld (4 j)`, with `4 j + 4 ≤ 4 R`. With `Wrap/Shape`, `safe_shape`: a memory of `cap`
bytes with `2 ^ 32 + 4 F ≤ cap + 1` and `4 R ≤ cap` is never overrun.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- Every instruction of `l` has a small offset and is not an `if`. -/
def SmallL (F : Nat) (l : List Instr) : Prop :=
  ∀ i ∈ l, OffI (4 * F) i ∧ ∀ bt t e, i ≠ .if_ bt t e

theorem codeOK_of_small {F R : Nat} : ∀ {l : List Instr}, SmallL F l → CodeOK F R l
  | [], _ => .nil
  | i :: l, h =>
    have hi := h i (by simp)
    .small hi.1 hi.2 (codeOK_of_small fun j hj => h j (by simp [hj]))

theorem smallL_append {F : Nat} {a b : List Instr} (ha : SmallL F a) (hb : SmallL F b) :
    SmallL F (a ++ b) := fun i hi => (List.mem_append.1 hi).elim (ha i) (hb i)

theorem smallL_cons {F : Nat} {i : Instr} {l : List Instr} (hi : OffI (4 * F) i)
    (hif : ∀ bt t e, i ≠ .if_ bt t e) (hl : SmallL F l) : SmallL F (i :: l) :=
  fun j hj => (List.mem_cons.1 hj).elim (fun h => h ▸ ⟨hi, hif⟩) (hl j)

theorem smallL_nil (F : Nat) : SmallL F [] := fun _ h => by cases h

/-- One instruction with a small offset that is not an `if`. -/
abbrev SmallI (F : Nat) (i : Instr) : Prop := OffI (4 * F) i ∧ ∀ bt t e, i ≠ .if_ bt t e

theorem smallL_cons' {F : Nat} {i : Instr} {l : List Instr} (hi : SmallI F i) (hl : SmallL F l) :
    SmallL F (i :: l) := smallL_cons hi.1 hi.2 hl

theorem notIf_pure {S : Nat} {i : Instr} (h : pureIns S i = true) :
    ∀ bt t e, i ≠ .if_ bt t e := by
  intro bt t e he
  have hs := pureShape h
  rw [he] at hs
  cases hs

theorem smallL_pure {F S : Nat} {l : List Instr} (h : ∀ i ∈ l, pureIns S i = true) : SmallL F l :=
  fun i hi => ⟨offI_pure (h i hi), notIf_pure (h i hi)⟩

theorem smallI_gget {F : Nat} (g : GlobalIdx) : SmallI F (.globalGet g) :=
  ⟨offI_gget g, fun _ _ _ h => by cases h⟩
theorem smallI_gset {F : Nat} (g : GlobalIdx) : SmallI F (.globalSet g) :=
  ⟨offI_gset g, fun _ _ _ h => by cases h⟩
theorem smallI_c32 {F : Nat} (n : Nat) : SmallI F (c32 n) :=
  ⟨offI_c32 n, fun _ _ _ h => by cases h⟩
theorem smallI_get {F : Nat} (a : LocalIdx) : SmallI F (.localGet a) :=
  ⟨offI_get a, fun _ _ _ h => by cases h⟩
theorem smallI_set {F : Nat} (a : LocalIdx) : SmallI F (.localSet a) :=
  ⟨offI_set a, fun _ _ _ h => by cases h⟩
theorem smallI_rel {F : Nat} (op : IntRelOp) : SmallI F (.intRelOp .i32 op) :=
  ⟨offI_rel op, fun _ _ _ h => by cases h⟩
theorem smallI_bin {F : Nat} (op : IntBinOp) : SmallI F (.intBinOp .i32 op) :=
  ⟨offI_bin op, fun _ _ _ h => by cases h⟩
theorem smallI_ret {F : Nat} : SmallI F .return_ :=
  ⟨offI_ret, fun _ _ _ h => by cases h⟩
theorem smallI_call {F : Nat} (f : FuncIdx) : SmallI F (.call f) :=
  ⟨offI_call f, fun _ _ _ h => by cases h⟩
theorem smallI_st {F o : Nat} (h : o + 4 ≤ 4 * F) (ho : o < 2 ^ 64) : SmallI F (st o) :=
  ⟨offI_st h ho, fun _ _ _ h => by cases h⟩
theorem smallI_ld {F o : Nat} (h : o + 4 ≤ 4 * F) (ho : o < 2 ^ 64) : SmallI F (ld o) :=
  ⟨offI_ld h ho, fun _ _ _ h => by cases h⟩

theorem smallL_saveLocals {F : Nat} : ∀ (i n : Nat), i + n ≤ F → 4 * F < 2 ^ 32 →
    SmallL F (saveLocals i n)
  | _, 0, _, _ => smallL_nil F
  | i, n + 1, h, h' => by
    have hrest := smallL_saveLocals (F := F) (i + 1) n (by omega) h'
    exact smallL_cons' (smallI_gget _) (smallL_cons' (smallI_get _)
      (smallL_cons' (smallI_st (by omega) (by omega)) hrest))

theorem smallL_loadLocals {F : Nat} : ∀ (i n : Nat), i + n ≤ F → 4 * F < 2 ^ 32 →
    SmallL F (loadLocals i n)
  | _, 0, _, _ => smallL_nil F
  | i, n + 1, h, h' => by
    have hrest := smallL_loadLocals (F := F) (i + 1) n (by omega) h'
    exact smallL_cons' (smallI_gget _) (smallL_cons' (smallI_ld (by omega) (by omega))
      (smallL_cons' (smallI_set _) hrest))

theorem smallL_saveCode {F : Nat} (hF : 1 ≤ F) (hF4 : 4 * F < 2 ^ 32) (k : Nat) :
    SmallL F (saveCode F k) :=
  smallL_append (smallL_saveLocals 0 (F - 1) (by omega) hF4)
    (smallL_cons' (smallI_gget _) (smallL_cons' (smallI_c32 _)
      (smallL_cons' (smallI_st (by omega) (by omega)) (smallL_cons' (smallI_gget _)
        (smallL_cons' (smallI_c32 _) (smallL_cons' (smallI_bin _)
          (smallL_cons' (smallI_gset _) (smallL_nil F))))))))

theorem smallL_restoreCode {F : Nat} (hF4 : 4 * F < 2 ^ 32) : SmallL F (restoreCode F) :=
  smallL_cons' (smallI_gget _) (smallL_cons' (smallI_c32 _) (smallL_cons' (smallI_bin _)
    (smallL_cons' (smallI_gset _) (smallL_loadLocals 0 F (by omega) hF4))))

theorem smallL_gets {F : Nat} (as : List LocalIdx) : SmallL F (getsCode as) := by
  intro i hi
  obtain ⟨a, -, rfl⟩ : ∃ a ∈ as, .localGet a = i := by simpa [getsCode] using hi
  exact smallI_get a

theorem smallL_sets {F : Nat} (rs : List LocalIdx) : SmallL F (setsCode rs) := by
  intro i hi
  obtain ⟨a, -, rfl⟩ : ∃ a ∈ rs, .localSet a = i := by simpa [setsCode] using hi
  exact smallI_set a

theorem smallL_dummies {F : Nat} (n : Nat) : SmallL F (dummies n) := by
  intro i hi
  rw [List.eq_of_mem_replicate hi]
  exact smallI_c32 0

/-- A guard `global.get state, c32 v, rel`. -/
theorem smallL_guard {F : Nat} (v : Nat) (op : IntRelOp) :
    SmallL F [gState, c32 v, .intRelOp .i32 op] :=
  smallL_cons' (smallI_gget _) (smallL_cons' (smallI_c32 _) (smallL_cons' (smallI_rel _)
    (smallL_nil F)))

theorem codeOK_pushAns {F R : Nat} : ∀ (j m : Nat), j + m ≤ R → 4 * R < 2 ^ 32 →
    CodeOK F R (pushAns j m)
  | _, 0, _, _ => .nil
  | j, m + 1, h, h' => .ld0 (by omega) (by omega) (codeOK_pushAns (j + 1) m (by omega) h')

theorem codeOK_reqArgs {F R : Nat} : ∀ (j : Nat) (as : List LocalIdx), j + as.length ≤ R →
    4 * R < 2 ^ 32 → CodeOK F R (reqArgs j as)
  | _, [], _, _ => .nil
  | j, a :: as, h, h' => by
    have hl : j + 1 + as.length ≤ R := by simp only [List.length_cons] at h; omega
    exact .st0 (by omega) (by omega) (codeOK_reqArgs (j + 1) as hl h')

/-- The sizes the generated code relies on. -/
structure ShapeCtx (F R : Nat) : Prop where
  hF : 1 ≤ F
  hF4 : 4 * F < 2 ^ 32
  hR4 : 4 * R < 2 ^ 32

theorem Prog.shapeCtx {P : Prog} (hP : P.WF) : ShapeCtx P.frameWords P.reqWords := by
  have hb := (Prog.wf_bounds hP).2
  exact ⟨Prog.frameWords_pos P, by omega, by omega⟩

theorem codeOK_reqCode {F R : Nat} (X : ShapeCtx F R) (f : FuncIdx) (as : List LocalIdx)
    (has : as.length + 1 ≤ R) : CodeOK F R (reqCode f as) := by
  have hF := X.hF
  have hhead : SmallL F [c32 0, c32 f.value.val, st 0] :=
    smallL_cons' (smallI_c32 _) (smallL_cons' (smallI_c32 _)
      (smallL_cons' (smallI_st (by omega) (by omega)) (smallL_nil F)))
  exact (codeOK_of_small hhead).append (codeOK_reqArgs 1 as (by omega) X.hR4)

theorem codeOK_chk {F R : Nat} (X : ShapeCtx F R) (k n : Nat) : CodeOK F R (chk F k n) := by
  have harm : SmallL F (saveCode F k ++ dummies n ++ [.return_]) :=
    smallL_append (smallL_append (smallL_saveCode X.hF X.hF4 k) (smallL_dummies n))
      (smallL_cons' smallI_ret (smallL_nil F))
  have hhead : SmallL F [gState, c32 1, eqI] := smallL_guard 1 .eq
  exact (codeOK_of_small hhead).append (.ifE (codeOK_of_small harm) .nil .nil)

theorem codeOK_prologue {F R : Nat} (X : ShapeCtx F R) : CodeOK F R (prologue F) := by
  have hhead : SmallL F [gState, c32 2, eqI] := smallL_guard 2 .eq
  exact (codeOK_of_small hhead).append
    (.ifE (codeOK_of_small (smallL_restoreCode X.hF4)) .nil .nil)

/-- The translation of a call statement to an import. -/
theorem codeOK_imp {F R : Nat} (X : ShapeCtx F R) (k nres : Nat) (f : FuncIdx)
    (as rs : List LocalIdx) (has : as.length + 1 ≤ R) (hrs : rs.length ≤ R) :
    CodeOK F R [gState, c32 2, eqI,
      .if_ .empty
        [.localGet (lidx (F - 1)), c32 k, eqI,
          ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)]
        (reqCode f as ++ [c32 1, sState] ++ saveCode F k ++ dummies nres ++ [.return_])] := by
  have hans : CodeOK F R ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs) :=
    ((codeOK_of_small (smallL_cons' (smallI_c32 0) (smallL_cons' (smallI_gset _)
      (smallL_nil F)))).append
      (codeOK_pushAns 0 rs.length (by omega) X.hR4)).append (codeOK_of_small (smallL_sets rs))
  have hsel : SmallL F [.localGet (lidx (F - 1)), c32 k, eqI] :=
    smallL_cons' (smallI_get _) (smallL_cons' (smallI_c32 _) (smallL_cons' (smallI_rel _)
      (smallL_nil F)))
  have hthen : CodeOK F R [.localGet (lidx (F - 1)), c32 k, eqI,
      ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)] :=
    (codeOK_of_small hsel).append (.ifE hans .nil .nil)
  have hsave : SmallL F ([c32 1, sState] ++ saveCode F k ++ dummies nres ++ [.return_]) :=
    smallL_append (smallL_append (smallL_cons' (smallI_c32 1) (smallL_cons' (smallI_gset _)
      (smallL_saveCode X.hF X.hF4 k))) (smallL_dummies nres)) (smallL_cons' smallI_ret (smallL_nil F))
  have helse : CodeOK F R (reqCode f as ++ [c32 1, sState] ++ saveCode F k ++ dummies nres ++
      [.return_]) := by
    simpa only [List.append_assoc] using
      (codeOK_reqCode X f as has).append (by simpa only [List.append_assoc] using codeOK_of_small hsave)
  have hhead : SmallL F [gState, c32 2, eqI] := smallL_guard 2 .eq
  exact (codeOK_of_small hhead).append (.ifE hthen helse .nil)

/-- The translation of a call statement to a defined function. -/
theorem codeOK_def {F R : Nat} (X : ShapeCtx F R) (k nres : Nat) (f : FuncIdx)
    (as rs : List LocalIdx) :
    CodeOK F R [gState, c32 2, neI, .localGet (lidx (F - 1)), c32 k, eqI, orI,
      ifThen (getsCode as ++ [.call f] ++ chk F k nres ++ setsCode rs)] := by
  have harm : CodeOK F R (getsCode as ++ [.call f] ++ chk F k nres ++ setsCode rs) :=
    ((codeOK_of_small (smallL_append (smallL_gets as) (smallL_cons' (smallI_call f)
      (smallL_nil F)))).append
      (codeOK_chk X k nres)).append (codeOK_of_small (smallL_sets rs))
  have hhead : SmallL F [gState, c32 2, neI, .localGet (lidx (F - 1)), c32 k, eqI, orI] :=
    smallL_cons' (smallI_gget _) (smallL_cons' (smallI_c32 _) (smallL_cons' (smallI_rel _)
      (smallL_cons' (smallI_get _) (smallL_cons' (smallI_c32 _) (smallL_cons' (smallI_rel _)
        (smallL_cons' (smallI_bin _) (smallL_nil F)))))))
  exact (codeOK_of_small hhead).append (.ifE harm .nil .nil)

theorem codeOK_trStmt {P : Prog} {S : Nat} (X : ShapeCtx P.frameWords P.reqWords)
    (nres k : Nat) {s : Stmt} (hs : s.wf P S = true) :
    CodeOK P.frameWords P.reqWords (trStmt ⟨P.imps.length, P.frameWords, nres⟩ k s) := by
  cases s with
  | pure is =>
    obtain ⟨-, hp, -⟩ := Stmt.wf_pure hs
    have hhead : SmallL P.frameWords [gState, c32 2, neI] := smallL_guard 2 .ne
    exact (codeOK_of_small hhead).append (.ifE (codeOK_of_small (smallL_pure hp)) .nil .nil)
  | call f as rs =>
    obtain ⟨hsig, -, -⟩ := Stmt.wf_call hs
    by_cases hf : f.value.val < P.imps.length
    · have himp := Prog.sig_imp hsig hf
      obtain ⟨h1, h2⟩ := Prog.imp_le (List.mem_of_getElem himp)
      have h := codeOK_imp X k nres f as rs h1 h2
      simpa [trStmt, hf] using h
    · have h := codeOK_def X k nres f as rs
      simpa [trStmt, hf] using h

theorem codeOK_trS {P : Prog} {S : Nat} (X : ShapeCtx P.frameWords P.reqWords) (nres : Nat) :
    ∀ (k : Nat) (ss : List Stmt), (∀ s ∈ ss, s.wf P S = true) →
    CodeOK P.frameWords P.reqWords (trS ⟨P.imps.length, P.frameWords, nres⟩ k ss)
  | _, [], _ => .nil
  | k, s :: ss, h =>
    (codeOK_trStmt X nres k (h s (by simp))).append
      (codeOK_trS X nres (k + 1) ss fun s' hs' => h s' (by simp [hs']))

/-- **Every body of the asyncified program has the request-access shape.** -/
theorem envOK_asyncify {P : Prog} (hP : P.WF) :
    EnvOK P.frameWords P.reqWords (asyncifyProg P) := by
  have X := Prog.shapeCtx hP
  intro d hd
  obtain ⟨fn, hfn, rfl⟩ : ∃ fn ∈ P.fns,
      (⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ : FnDef) = d := by
    simpa [asyncifyProg] using hd
  have hw := Prog.wf_fns hP hfn
  have hw' : (∀ s ∈ fn.stmts, s.wf P fn.nloc = true) ∧ ∀ i ∈ fn.tail, pureIns fn.nloc i = true := by
    simp only [FnSrc.wf, Bool.and_eq_true, List.all_eq_true] at hw
    exact ⟨hw.1.1.1, hw.1.1.2⟩
  have hbody : CodeOK P.frameWords P.reqWords (P.tBody fn) :=
    ((codeOK_prologue X).append (codeOK_trS X fn.nres 0 fn.stmts hw'.1)).append
      (codeOK_of_small (smallL_pure hw'.2))
  exact hbody

/-- **A memory of `cap` bytes with `2 ^ 32 + 4 F ≤ cap + 1` and `4 R ≤ cap` is never overrun**,
by any target run of the asyncified program from a call of a defined function. -/
theorem safe_shape (P : Prog) (hP : P.WF) (H : Host σ) {cap : Nat}
    (hF : 2 ^ 32 + 4 * P.frameWords ≤ cap + 1) (hR : P.sb ≤ cap)
    {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W) (s : σ) :
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg) (tgtSt P e fn args s) := by
  have hE := envOK_asyncify hP
  have hmem : tdef P fn ∈ (asyncifyProg P).fns := by
    have := Prog.tgt_fn hfn
    exact List.mem_of_getElem? (by simpa [tdef] using this)
  have h0 : CfgOK P.frameWords P.reqWords (tgtSt P e fn args s).cfg :=
    cfgOK_of (Or.inl (hE _ hmem)) (by simp)
  intro n y hy
  exact not_oob_ok (cfgOK_runN hE H n _ h0 y hy) hF hR

end Silmaril.Wasm.FX.Asyncify.Tool
