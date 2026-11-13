module

public import Silmaril.Compiler.Core.Verified.ExitCall.Defs
public import Silmaril.Compiler.Core.Source.PureLocal.Defs

/-! # The statement `abort();`

Cerberus elaborates the statement `abort();` (with `abort` declared `void abort(void)`, no body) to

```
let strong _ = bound(
  let strong f = pure(<abort>) in
  let (r, ps, _, _) = cfunction(f) in
  if params_length(ps) = 0 then
    if are_compatible(void, r) then ccall(ty, f, []) else undef(UB041)
  else undef(UB038)) in
pure(unit)
```

`abortStmt file e`: `e` has this shape, `abort` is the C library call the dynamics implements
(`Dynamics.libraryCall`), and the checks hold for its declaration: the parameter list that
`cfunction` gives is empty, `params_length` of it folds to `0` (`Fold.eval` of the standard
library function on that list), and the return type is `void`. This is constant folding of the
type checks, not an execution of the program.

`abortStmt_reaches`: in every environment, over every continuation, from every memory, the
statement halts with `aborted` (`Dynamics.libraryCall`), the output unchanged.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.AbortCall

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Fold
open Silmaril.Cerberus.Core.PureEval (Reaches)
open ReturnConst (focusMemory)
open ExitCall (lift plain_effectExpr plain_pureExpr plain_value plain_apply ra_sseq ra_bound ra_val
  ra_sym ra_args_cons ra_args_nil ra_cfunction ra_functionInfo ra_effectBind ra_strongBind
  ra_diagnostic info info_inv rv_info scheduled_reaches end_reaches ra_raise)
open ReturnLit (Eff)

local notation "rv" => runtimeValue

/-- `abort` declared without a body: the C library call the dynamics implements. -/
def isAbort (file : Doc) (s : Sym) : Bool :=
  match file.funs.lookup s, s.description with
  | some (.procedureDecl ..), .id "abort" => true
  | _, _ => false

/-- `params_length` of the empty list `[]` of element type `t` folds to `0`. -/
def lengthZero (file : Doc) (pl : Sym) (t : BaseType) : Bool :=
  match funBody file (.sym pl) with
  | some ([prm], body) =>
    match eval file Return.fuel (extend [(prm, .list t [])] ∅) body with
    | some (.object (.integer 0)) => true
    | _ => false
  | _ => false

/-- The bindings of the `cfunction` pattern pass the checks: `ps` is an empty list whose
`params_length` folds to `0`, `r` is `void`, and `f` is not rebound. -/
def checks (file : Doc) (xs : List (Sym × WVal)) (f ps r pl : Sym) : Bool :=
  (match (extend xs ∅).lookup ps with
    | some (.list t []) => lengthZero file pl t
    | _ => false) &&
  (match (extend xs ∅).lookup r with
    | some (.ctype (.mk _ .void)) => true
    | _ => false) &&
  xs.all fun b => b.1.key != f.key

/-- The statement `abort();`. -/
def abortStmt (file : Doc) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (none, _))) (.mk _ (.bound (.mk _ (.sseq (.mk _ (.base (some f, _)))
      (.mk _ (.pure (.mk _ () (.val (.loaded (.specified (.pointer (.function s))))))))
      (.mk _ (.let_ pat (.mk _ () (.cfunction (.mk _ () (.sym f₁))))
        (.mk _ (.if_ (.mk _ () (.op .eq (.mk _ () (.call (.sym pl) [.mk _ () (.sym ps)]))
            (.mk _ () (.val (.object (.integer 0))))))
          (.mk _ (.if_ (.mk _ () (.areCompatible (.mk _ () (.val (.ctype (.mk _ .void))))
              (.mk _ () (.sym r))))
            (.mk _ (.ccall _ _ (.mk _ () (.sym f₂)) []))
            _))
          _)))))))) _) =>
      f₁.key == f.key && f₂.key == f.key && isAbort file s &&
        match info file s with
        | some i => match matchP pat i with
          | some xs => checks file xs f ps r pl
          | none => false
        | none => false
  | _ => false

/-! ## Inversion -/

theorem lookup_extend_of {xs : List (Sym × WVal)} {s : Sym} {w : WVal}
    (h : (extend xs ∅).lookup s = some w) (denv : Env) :
    (extendEnv (Fold.bmap xs) denv).lookup s = some (rv w) := by
  induction xs with
  | nil => simp [extend, Map.lookup] at h
  | cons x xs ih =>
    obtain ⟨y, v⟩ := x
    by_cases e : MapKey.key s = MapKey.key y
    · simp only [extend, List.foldr, Map.lookup, Map.insert] at h
      rw [e, Finmap.lookup_insert] at h
      cases h
      simp only [Fold.bmap, List.map_cons, extendEnv, List.foldr, Map.lookup, Map.insert]
      rw [e, Finmap.lookup_insert]
    · have h' : (extend xs ∅).lookup s = some w := by
        simpa [extend, Map.lookup_insert_of_key_ne _ _ e] using h
      have := ih h'
      simp only [Fold.bmap, List.map_cons, extendEnv, List.foldr] at this ⊢
      rw [Map.lookup_insert_of_key_ne _ _ e]
      exact this

theorem lookup_extend_other {xs : List (Sym × WVal)} {s : Sym}
    (h : (xs.all fun b => b.1.key != s.key) = true) (denv : Env) :
    (extendEnv (Fold.bmap xs) denv).lookup s = denv.lookup s := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have e : MapKey.key s ≠ MapKey.key x.1 := fun e => h.1 e.symm
    simp only [Fold.bmap, List.map_cons, extendEnv, List.foldr] at ih ⊢
    rw [Map.lookup_insert_of_key_ne _ _ e]
    exact ih (by simpa using h.2)

/-! ## Steps -/

variable {file : Program} {labels : Labels}

theorem ra_op {m : Mem.Concrete.State} {k : List Frame} {env : Env} (ann : List Annot) (b : BinOp)
    (p q : PE) :
    requestAux file labels m (.pureExpr (.mk ann () (.op b p q)) env) k =
      .next (.pureExpr p env) (.arguments (.bin b) [] [q] env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, arguments]

theorem ra_call {m : Mem.Concrete.State} {k : List Frame} {env : Env} (ann : List Annot) (n : Name Sym)
    (p : PE) (ps : List PE) :
    requestAux file labels m (.pureExpr (.mk ann () (.call n (p :: ps))) env) k =
      .next (.pureExpr p env) (.arguments (.call n) [] ps env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, arguments]

theorem ra_compatible {m : Mem.Concrete.State} {k : List Frame} {env : Env} (ann : List Annot)
    (p q : PE) :
    requestAux file labels m (.pureExpr (.mk ann () (.areCompatible p q)) env) k =
      .next (.pureExpr p env) (.arguments .compatible [] [q] env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, arguments]

theorem ra_apply_call {m : Mem.Concrete.State} {k : List Frame} {n : Name Sym} {vs : List Val}
    {body : PE} {env : Env} (h : functionBody file n vs = .ok (body, env)) :
    requestAux file labels m (.apply (.call n) vs) k = .next (.pureExpr body env) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, h]

theorem ra_apply_prim {m : Mem.Concrete.State} {k : List Frame} {op : Prim} {vs : List Val} {v : Val}
    (hp : PureEval.Plain op) (h : primitive op vs (PureEval.tagsOf file m) = .ok v) :
    requestAux file labels m (.apply op vs) k = .next (.value v) k := by
  rw [Silmaril.Cerberus.Core.PureLocal.requestAux_apply file hp vs k m false, h]

theorem ra_compat_void {m : Mem.Concrete.State} {k : List Frame} (c d : List Annot) :
    requestAux file labels m (.apply .compatible [.ctype (.mk c .void), .ctype (.mk d .void)]) k =
      .next (.value .true) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, Fold.compat_void]

theorem ra_if_true {m : Mem.Concrete.State} {k : List Frame} (yes no : EE) (benv : Env) :
    requestAux file labels m (.value .true) (.effectIf yes no benv :: k) =
      .next (.effectExpr yes benv) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem ra_abort {m : Mem.Concrete.State} {k : List Frame} {outer : Env} {s : Sym}
    (hs : libraryCall file s = some .abort) :
    requestAux file labels m (.apply (.procedure outer) [.loaded (.specified (.pointer (.function s)))]) k =
      .scheduled [(.raise .aborted, [])] := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, hs, scheduledRequest]

theorem isAbort_libraryCall {f : Doc} {s : Sym} (h : isAbort f s = true) : libraryCall f s = some .abort := by
  unfold isAbort at h
  unfold libraryCall
  split at h <;> simp_all

/-- `params_length(ps) = 0` with `ps` bound to an empty list on which it folds to `0`. -/
theorem lengthZero_reaches {pl ps : Sym} {t : BaseType} (h : lengthZero file pl t = true) {env : Env}
    (hps : env.lookup ps = some (.list t [])) (a0 a1 a2 a3 : List Annot) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr (.mk a0 () (.op .eq (.mk a1 () (.call (.sym pl) [.mk a2 () (.sym ps)]))
      (.mk a3 () (.val (.object (.integer 0)))))) env, k, m⟩ ⟨.value .true, k, m⟩ := by
  unfold lengthZero at h
  split at h
  · rename_i prm body hbody
    split at h
    · rename_i hev
      have hfb := Fold.funBody_sound (ws := [.list t []]) hbody rfl
      have hr : Fold.EnvRel (extend [(prm, .list t [])] ∅) (extendEnv ([prm].zip ([(Value.list t [] : WVal)].map rv)) ∅) := by
        simpa [Fold.bmap] using (Fold.EnvRel.empty).extend [(prm, .list t [])]
      let K₁ : List Frame := .arguments (.bin .eq) [] [.mk a3 () (.val (.object (.integer 0)))] env :: k
      refine (lift file labels (ra_op a0 .eq _ _) (plain_pureExpr _ _)).trans ?_
      refine (lift file labels (ra_call a1 _ _ []) (plain_pureExpr _ _)).trans ?_
      refine (lift file labels (ra_sym file labels a2 () hps) (plain_value _)).trans ?_
      refine (lift file labels (ra_args_nil file labels _ _ _) (plain_apply _ _)).trans ?_
      refine (lift file labels (ra_apply_call (k := K₁) (by simpa [runtimeValue, runtimeValues] using hfb)) (plain_pureExpr _ _)).trans ?_
      refine (Fold.eval_reaches file labels Return.fuel _ body _ hev _ hr K₁ m).trans ?_
      refine (lift file labels (ra_args_cons file labels _ _ _ _ _) (plain_pureExpr _ _)).trans ?_
      refine (lift file labels (ra_val file labels a3 () _) (plain_value _)).trans ?_
      refine (lift file labels (ra_args_nil file labels _ _ _) (plain_apply _ _)).trans ?_
      exact lift file labels (ra_apply_prim trivial (by simp [primitive, integerBin, Dynamics.boolean]; rfl))
        (plain_value _)
    · cases h
  · cases h

/-- **`abort();`** halts with `aborted`, in every environment, over every continuation. -/
theorem abortStmt_reaches {e : Eff} (h : abortStmt file e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    ∃ m', Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.halt .aborted, [], m'⟩ ∧
      m'.stdout = m.stdout := by
  unfold abortStmt at h
  split at h
  · rename_i a0 a1 bt0 a2 a3 a4 f bt1 a5 a6 s a7 pat a8 a9 f₁ a10 a11 a12 pl a13 ps a14 a15 a16 a17 vann
      a18 r a19 u1 u2 a20 f₂ undef2 undef1 unitE
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hf₁, hf₂⟩, habort⟩, hrest⟩ := h
    split at hrest
    · rename_i i hi
      split at hrest
      · rename_i xs hxs
        unfold checks at hrest
        simp only [Bool.and_eq_true] at hrest
        obtain ⟨⟨hps, hr⟩, hfx⟩ := hrest
        obtain ⟨l0, at0, ret, params, va, pr, hlook, rfl⟩ := info_inv hi
        let fv : Val := .loaded (.specified (.pointer (.function s)))
        let CCALL : EE := .mk a19 (.ccall u1 u2 (.mk a20 () (.sym f₂)) [])
        let IF2 : EE := .mk a15 (.if_ (.mk a16 () (.areCompatible (.mk a17 () (.val (.ctype
          (.mk vann .void)))) (.mk a18 () (.sym r)))) CCALL undef2)
        let IF1 : EE := .mk a10 (.if_ (.mk a11 () (.op .eq (.mk a12 () (.call (.sym pl) [.mk a13 () (.sym ps)]))
          (.mk a14 () (.val (.object (.integer 0)))))) IF2 undef1)
        let LET : EE := .mk a7 (.let_ pat (.mk a8 () (.cfunction (.mk a9 () (.sym f₁)))) IF1)
        let CALL : EE := .mk a3 (.sseq (.mk a4 (.base (some f, bt1)))
          (.mk a5 (.pure (.mk a6 () (.val (.loaded (.specified (.pointer (.function s)))))))) LET)
        let env₁ := extendEnv [(f, fv)] env
        let infoV : Val := .tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2),
          Dynamics.boolean va, Dynamics.boolean pr]
        have hm : matchPattern pat infoV = some (Fold.bmap xs) := by
          have := Fold.matchP_rv pat (.tuple [.ctype ret, .list .ctype (params.map fun p => .ctype p.2),
            Fold.boolean va, Fold.boolean pr])
          rw [rv_info, hxs] at this
          exact this
        let env₂ := extendEnv (Fold.bmap xs) env₁
        let K₀ : List Frame := .bound :: .strongBind (.mk a1 (.base (none, bt0))) unitE env :: k
        -- `let strong _ = bound(CALL)`, then `let strong f = pure(<abort>)`
        have s₁ : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (none, bt0)))
            (.mk a2 (.bound CALL)) unitE)) env, k, m⟩ ⟨.effectExpr CALL env, K₀, m⟩ :=
          (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans
            (lift file labels (ra_bound file labels _ _) (plain_effectExpr _ _))
        obtain ⟨l₁, s₂⟩ := ExitCall.pure_local file labels (wc := false) (env := env)
          (k := .strongBind (.mk a4 (.base (some f, bt1))) LET env :: K₀) (m := m) a5
          (.mk a6 () (.val (.loaded (.specified (.pointer (.function s))))))
        let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
        have s₃ : Reaches file labels ⟨.effectExpr CALL env, K₀, m⟩ ⟨.effectExpr LET env₁, K₀, m₁⟩ :=
          (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans
            ((Interleave.reaches_of_local file labels s₂).trans
              ((lift file labels (ra_val file labels a6 () _) (plain_value _)).trans
                ((lift file labels (ra_diagnostic file labels _ _) (plain_value _)).trans
                  (lift file labels (ra_strongBind file labels (xs := [(f, fv)]) (by rfl) _ _)
                    (plain_effectExpr _ _)))))
        -- `let pat = cfunction(f)`
        have hf₁' : env₁.lookup f₁ = some fv := ConvInt.lookup_one hf₁
        let m₂ := focusMemory a7 m₁
        have s₄ : Reaches file labels ⟨.effectExpr LET env₁, K₀, m₁⟩ ⟨.effectExpr IF1 env₂, K₀, m₂⟩ :=
          (Straight.focus_reaches (ExitCall.request_let file labels)).trans
            ((lift file labels (ra_cfunction file labels _ _ _) (plain_pureExpr _ _)).trans
              ((lift file labels (ra_sym file labels a9 () hf₁') (plain_value _)).trans
                ((lift file labels (ra_args_nil file labels _ _ _) (plain_apply _ _)).trans
                  ((lift file labels (ra_functionInfo file labels hlook) (plain_value _)).trans
                    (lift file labels (ra_effectBind file labels hm _ _) (plain_effectExpr _ _))))))
        -- `params_length(ps) = 0`
        obtain ⟨t, ht, hzero⟩ : ∃ t, (extend xs ∅).lookup ps = some (.list t []) ∧ lengthZero file pl t = true := by
          revert hps; split
          · rename_i t ht; exact fun h => ⟨t, ht, h⟩
          · intro h; cases h
        obtain ⟨ra, hra⟩ : ∃ a, (extend xs ∅).lookup r = some (.ctype (.mk a .void)) := by
          revert hr; split
          · rename_i a ha; exact fun _ => ⟨a, ha⟩
          · intro h; cases h
        have hps₂ : env₂.lookup ps = some (.list t []) := by
          simpa [runtimeValue, runtimeValues] using lookup_extend_of ht env₁
        have hr₂ : env₂.lookup r = some (.ctype (.mk ra .void)) := by
          simpa [runtimeValue] using lookup_extend_of hra env₁
        have hf₂' : env₂.lookup f₂ = some fv := by
          rw [ReturnLit.lookup_key hf₂, lookup_extend_other hfx env₁]
          exact ConvInt.lookup_one rfl
        let m₃ := focusMemory a10 m₂
        have s₅ : Reaches file labels ⟨.effectExpr IF1 env₂, K₀, m₂⟩ ⟨.effectExpr IF2 env₂, K₀, m₃⟩ :=
          (Straight.focus_reaches (ExitCall.request_if file labels)).trans
            ((lengthZero_reaches hzero hps₂ a11 a12 a13 a14 _ _).trans
              (lift file labels (ra_if_true _ _ _) (plain_effectExpr _ _)))
        -- `are_compatible(void, r)`
        let m₄ := focusMemory a15 m₃
        have s₆ : Reaches file labels ⟨.effectExpr IF2 env₂, K₀, m₃⟩ ⟨.effectExpr CCALL env₂, K₀, m₄⟩ :=
          (Straight.focus_reaches (ExitCall.request_if file labels)).trans
            ((lift file labels (ra_compatible a16 _ _) (plain_pureExpr _ _)).trans
              ((lift file labels (ra_val file labels a17 () _) (plain_value _)).trans
                ((lift file labels (ra_args_cons file labels _ _ _ _ _) (plain_pureExpr _ _)).trans
                  ((lift file labels (ra_sym file labels a18 () hr₂) (plain_value _)).trans
                    ((lift file labels (ra_args_nil file labels _ _ _) (plain_apply _ _)).trans
                      ((lift file labels (ra_compat_void _ _)
                        (plain_value _)).trans
                        (lift file labels (ra_if_true _ _ _) (plain_effectExpr _ _))))))))
        -- the call
        let m₅ := focusMemory a19 m₄
        have s₇ : Reaches file labels ⟨.effectExpr CCALL env₂, K₀, m₄⟩ ⟨.halt .aborted, [], m₅⟩ :=
          (Straight.focus_reaches (ExitCall.request_ccall file labels)).trans
            ((lift file labels (ra_sym file labels a20 () hf₂') (plain_value _)).trans
              ((lift file labels (ra_args_nil file labels _ _ _) (plain_apply _ _)).trans
                ((scheduled_reaches file labels (ra_abort (isAbort_libraryCall habort))
                  (fun _ h => nomatch h)).trans
                  (end_reaches file labels (ra_raise file labels _) (fun _ h => nomatch h)))))
        refine ⟨m₅, s₁.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans s₇)))), ?_⟩
        simp [m₅, m₄, m₃, m₂, m₁, ReturnConst.focusMemory_stdout]
      · cases hrest
    · cases hrest
  · cases h

end Silmaril.Compile.Core.Verified.AbortCall
