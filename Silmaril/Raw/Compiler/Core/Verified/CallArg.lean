module

public import Silmaril.Compiler.Core.Verified.Call.Defs
public import Silmaril.Compiler.Core.Verified.LocalExpr.Defs
public import Silmaril.Compiler.Core.Verified.LocalsDoc.Defs
public import Silmaril.Compiler.Core.Verified.ClosedEffSound.Defs

/-! # Calls with one `int` argument: the pieces

Cerberus elaborates a call `g(n)` of a procedure with one `int` parameter to

```
let strong ((p, (f, ps, v, _)), a) = unseq(let strong q = pure(<g>) in pure((q, cfunction(q))),
                                            <n>) in
if not (params_length(ps) = 1) then undef else
if v || not are_compatible(<return type>, f) then undef else
let strong x = (let t = params_nth(ps, 0) in
                if not are_compatible(int, t) then undef else
                let weak o = create(alignof(int), int) in
                store(int, o, conv_loaded_int(int, a)) ; pure(o)) in
let strong r = ccall(<type>, p, [x]) in kill(int, x) ; pure(r)
```

`<n>` is `pure(n)` for a literal, or Cerberus's glue around a C operator on literals
(`-1`), which `ClosedEff.lit` folds (`argLit`). The argument object `o` is created and initialised by the caller; the callee receives the
pointer `x` to it as its parameter and reads it with `load`; the caller kills it after the
return. This file proves the steps of that elaboration that do not involve the callee: the
function-pointer task of the arena as local steps (`fnTask_readTask`), the arity and
compatibility checks (`length_one_eval`, `nth_zero_eval`, `notCompatible_reaches`,
`variadicCheck_reaches`) and the binds over the arena's annotation frame.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CallArg

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns)
open ReturnLit (Eff)
open ConvInt (lookupFun)
open LoadTask (Touched ReadTask)
open Call (retKind)

/-! ## Recognisers of std.core's parameter-list functions -/

/-- std.core's `params_length_aux(acc, cs) =
case cs of [] => acc | _ :: xs => params_length_aux(acc + 1, xs)`. -/
def isLengthAux (aux : Sym) : ConvInt.Fun → Bool
  | .function _ [(acc, _), (cs, _)]
      (.mk _ () (.case_ (.mk _ () (.sym cs₁))
        [(.mk _ (.ctor (.nil _) []), .mk _ () (.sym acc₁)),
         (.mk _ (.ctor .cons [.mk _ (.base (none, _)), .mk _ (.base (some xs, _))]),
          .mk _ () (.call (.sym aux₁) [.mk _ () (.op .add (.mk _ () (.sym acc₂))
            (.mk _ () (.val (.object (.integer o))))), .mk _ () (.sym xs₁)]))])) =>
      decide (acc.key ≠ cs.key ∧ cs₁.key = cs.key ∧ acc₁.key = acc.key ∧ aux₁.key = aux.key ∧
        acc₂.key = acc.key ∧ o = 1 ∧ xs₁.key = xs.key ∧ acc.key ≠ xs.key)
  | _ => false

/-- std.core's `params_length(cs) = params_length_aux(0, cs)`. -/
def isLength (file : File Codec.wireModel Unit Unit) : ConvInt.Fun → Bool
  | .function _ [(cs, _)]
      (.mk _ () (.call (.sym aux) [.mk _ () (.val (.object (.integer z))), .mk _ () (.sym cs₁)])) =>
      decide (z = 0 ∧ cs₁.key = cs.key) &&
      (match lookupFun file aux with
       | some d => isLengthAux aux d
       | none => false)
  | _ => false

/-- The symbol `s` names std.core's `params_length`. -/
def isParamsLength (file : File Codec.wireModel Unit Unit) (s : Sym) : Bool :=
  match lookupFun file s with
  | some d => isLength file d
  | none => false

/-- std.core's `params_nth(cs, n) = case cs of [] => … | x :: xs => if n = 0 then x else …`. -/
def isNth : ConvInt.Fun → Bool
  | .function _ [(cs, _), (n, _)]
      (.mk _ () (.case_ (.mk _ () (.sym cs₁))
        [(.mk _ (.ctor (.nil _) []), _),
         (.mk _ (.ctor .cons [.mk _ (.base (some x, _)), .mk _ (.base (some xs, _))]),
          .mk _ () (.if_ (.mk _ () (.op .eq (.mk _ () (.sym n₁)) (.mk _ () (.val (.object (.integer z))))))
            (.mk _ () (.sym x₁)) _))])) =>
      decide (cs.key ≠ n.key ∧ cs₁.key = cs.key ∧ n₁.key = n.key ∧ z = 0 ∧ x₁.key = x.key ∧
        n.key ≠ x.key ∧ n.key ≠ xs.key)
  | _ => false

/-- The symbol `s` names std.core's `params_nth`. -/
def isParamsNth (file : File Codec.wireModel Unit Unit) (s : Sym) : Bool :=
  match lookupFun file s with
  | some d => isNth d
  | none => false

/-! ## Environments -/

variable {file : Program} {labels : Labels}

theorem lookup_cons {a s : Sym} {x : Val} {xs : Bindings} {env : Env} :
    (extendEnv ((a, x) :: xs) env).lookup s =
      if s.key = a.key then some x else (extendEnv xs env).lookup s := by
  by_cases h : s.key = a.key
  · have : MapKey.key s = MapKey.key a := h
    simp only [h, ↓reduceIte, extendEnv, List.foldr, Map.lookup, Map.insert]
    rw [this, Finmap.lookup_insert]
  · have : MapKey.key s ≠ MapKey.key a := h
    simp only [h, ↓reduceIte, extendEnv, List.foldr, Map.lookup, Map.insert]
    rw [Finmap.lookup_insert_of_ne _ this]

theorem lookup_nil {s : Sym} {env : Env} : (extendEnv [] env).lookup s = env.lookup s := rfl

theorem lookup_cons_eq {a s : Sym} {x : Val} {xs : Bindings} {env : Env} (h : s.key = a.key) :
    (extendEnv ((a, x) :: xs) env).lookup s = some x := by
  rw [lookup_cons]; simp [h]

theorem lookup_cons_ne {a s : Sym} {x : Val} {xs : Bindings} {env : Env} (h : s.key ≠ a.key) :
    (extendEnv ((a, x) :: xs) env).lookup s = (extendEnv xs env).lookup s := by
  rw [lookup_cons]; simp [h]

/-! ## Pure evaluations -/

/-- `params_length([c]) = 1`, and `not (params_length(ps) = 1)` is false. -/
theorem length_one_eval {len pty : Sym} {env : Env} {c : Ctype} {ann an a1 a2 a3 : List Annot}
    (hl : isParamsLength file len = true) (hp : env.lookup pty = some (.list .ctype [.ctype c]))
    (tags : Mem.Concrete.Tags) :
    Eval file tags env (.inl (.mk an () (.not (.mk ann () (.op .eq
      (.mk a1 () (.call (.sym len) [.mk a2 () (.sym pty)])) (.mk a3 () (.val (.object (.integer 1)))))))))
      (.inl .false) := by
  unfold isParamsLength at hl
  split at hl
  · rename_i d hd
    unfold isLength at hl
    split at hl
    · rename_i bt cs cbt pann cann aux vann z wann cs₁
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨⟨rfl, hcs⟩, hl⟩ := hl
      split at hl
      · rename_i d' hd'
        unfold isLengthAux at hl
        split at hl
        · rename_i bt' acc abt cs' cbt' pann' cann' cs'₁ nbt nann sann acc₁ cpa wa wbt xa xs xbt
            capann aux₁ oa1 opann acc₂ oa2 o xsa xs₁
          obtain ⟨hne, hcs', hacc, haux, hacc₂, rfl, hxs, hax⟩ := of_decide_eq_true hl
          have hd'' := (show lookupFun file aux₁ = lookupFun file aux by
              unfold lookupFun; rw [ReturnLit.lookup_key haux, ReturnLit.lookup_key haux]).trans hd'
          refine .not (vs := [.true]) (.cons (.op (vs := [.object (.integer 1), .object (.integer 1)])
            (.cons (.call (v := .object (.integer 1)) (.cons (.sym hp) .nil)
              (ConvInt.functionBody_eq hd rfl) ?_) (.cons .val .nil)) ?_) .nil) ?_
          · refine .call (v := .object (.integer 1))
              (.cons .val (.cons (.sym (ConvInt.lookup_one hcs)) .nil)) (ConvInt.functionBody_eq hd' rfl) ?_
            -- `params_length_aux(0, [c])`
            refine .case_ (xs := [(xs, .list .ctype [])])
              (body := .mk capann () (.call (.sym aux₁) [.mk oa1 () (.op .add (.mk opann () (.sym acc₂))
                (.mk oa2 () (.val (.object (.integer 1))))), .mk xsa () (.sym xs₁)]))
              (.sym (ConvInt.lookup_two_second hcs' (fun h => hne h.symm)))
              (by simp [selectCase, matchPattern, bind, Option.bind]) ?_
            refine .call (vs := [.object (.integer 1), .list .ctype []])
              (.cons (.op (vs := [.object (.integer 0), .object (.integer 1)])
                (.cons (.sym ?_) (.cons .val .nil)) ?_) (.cons (.sym ?_) .nil))
              (ConvInt.functionBody_eq hd'' rfl) ?_
            · rw [lookup_cons_ne (by rw [hacc₂]; exact hax), lookup_nil]
              exact ConvInt.lookup_two_first hacc₂
            · simp [primitive, integerBin, integer, pure, Except.pure]
            · exact lookup_cons_eq hxs
            -- `params_length_aux(1, [])`
            exact .case_ (xs := []) (body := .mk sann () (.sym acc₁))
              (.sym (ConvInt.lookup_two_second hcs' (fun h => hne h.symm)))
              (by simp [selectCase, matchPattern]) (.sym (ConvInt.lookup_two_first hacc))
          · simp [primitive, integerBin, boolean, pure, Except.pure]
          · simp [primitive, pure, Except.pure]
        · cases hl
      · cases hl
    · cases hl
  · cases hl

/-- `params_nth([c], 0) = c`. -/
theorem nth_zero_eval {nth pty : Sym} {env : Env} {c : Ctype} {ann a1 a2 : List Annot}
    (hn : isParamsNth file nth = true) (hp : env.lookup pty = some (.list .ctype [.ctype c]))
    (tags : Mem.Concrete.Tags) :
    Eval file tags env (.inl (.mk ann () (.call (.sym nth)
      [.mk a1 () (.sym pty), .mk a2 () (.val (.object (.integer 0)))]))) (.inl (.ctype c)) := by
  unfold isParamsNth at hn
  split at hn
  · rename_i d hd
    unfold isNth at hn
    split at hn
    · rename_i rbt cs cbt n nbt pann cann cs₁ nann na e0 ca xa x xbt xsa xs xsbt ia oa n1a n₁ za z
        x1a x₁ e1
      obtain ⟨hne, hcs, hn₁, rfl, hx, hnx, hnxs⟩ := of_decide_eq_true hn
      refine .call (vs := [.list .ctype [.ctype c], .object (.integer 0)])
        (.cons (.sym hp) (.cons .val .nil)) (ConvInt.functionBody_eq hd rfl) ?_
      refine .case_ (xs := [(x, .ctype c), (xs, .list .ctype [])])
        (body := .mk ia () (.if_ (.mk oa () (.op .eq (.mk n1a () (.sym n₁))
          (.mk za () (.val (.object (.integer 0)))))) (.mk x1a () (.sym x₁)) e1))
        (.sym (ConvInt.lookup_two_first hcs))
        (by simp [selectCase, matchPattern, bind, Option.bind]) ?_
      refine .ifTrue (.op (vs := [.object (.integer 0), .object (.integer 0)])
        (.cons (.sym ?_) (.cons .val .nil)) ?_) (.sym ?_)
      · rw [lookup_cons_ne (by rw [hn₁]; exact hnx), lookup_cons_ne (by rw [hn₁]; exact hnxs),
          lookup_nil]
        exact ConvInt.lookup_two_second hn₁ (fun h => hne h.symm)
      · simp [primitive, integerBin, boolean, pure, Except.pure]
      · exact lookup_cons_eq hx
    · cases hn
  · cases hn

/-- `not are_compatible(rty, f)` is false for return types of the same kind. -/
theorem notCompatible_reaches {an ann aann bann : List Annot} {rty fty : Ctype} {f : Sym}
    {env : Env} {isInt : Bool} (hr : retKind rty = some isInt) (hf : retKind fty = some isInt)
    (hl : env.lookup f = some (.ctype fty)) :
    SeqReach.PureEval file labels (.mk an () (.not
      (.mk ann () (.areCompatible (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))))) env
      .false := by
  intro k m
  refine (SeqReach.next_reaches
    (c' := .pureExpr (.mk ann () (.areCompatible (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))) env)
    (k' := .arguments .notBool [] [] env :: k) (by intro o h; cases h)
    (by simp [request, requestAux, awaitsScheduling, arguments])).trans ?_
  refine (Call.compatible_reaches hr hf hl _ _).trans ?_
  refine (CallReach.arguments_reaches .nil .notBool [] _ k m).trans ?_
  apply SeqReach.next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, primitive, pure, Except.pure]

/-- `v || not are_compatible(rty, f)` is false for a non-variadic procedure. -/
theorem variadicCheck_reaches {an a1 a2 ann aann bann : List Annot} {rty fty : Ctype} {b f : Sym}
    {env : Env} {isInt : Bool} (hr : retKind rty = some isInt) (hf : retKind fty = some isInt)
    (hb : env.lookup b = some .false) (hl : env.lookup f = some (.ctype fty)) :
    SeqReach.PureEval file labels (.mk an () (.op .or (.mk a1 () (.sym b)) (.mk a2 () (.not
      (.mk ann () (.areCompatible (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))))))) env
      .false := by
  intro k m
  refine (SeqReach.next_reaches (c' := .pureExpr (.mk a1 () (.sym b)) env)
    (k' := .arguments (.bin .or) [] [.mk a2 () (.not
      (.mk ann () (.areCompatible (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))))] env :: k)
    (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling, arguments])).trans ?_
  refine (SeqReach.pure_symbol a1 b env _ hb _ _).trans ?_
  refine (CallReach.arguments_reaches (.cons (notCompatible_reaches hr hf hl) .nil)
    (.bin .or) [] _ k m).trans ?_
  apply SeqReach.next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, primitive, pure, Except.pure]

/-! ## Binds over the arena's annotations -/

theorem annotations_sbind_reaches (xs : List Access) {pat : Pattern Sym} {v : Val} {bs : Bindings}
    (hm : matchPattern pat v = some bs) (b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .annotations xs :: .strongBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv bs env), .annotations xs :: k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, hm]

theorem annotations_wbind_reaches (xs : List Access) {pat : Pattern Sym} {v : Val} {bs : Bindings}
    (hm : matchPattern pat v = some bs) (b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .annotations xs :: .effectBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv bs env), .annotations xs :: k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, hm]

/-! ## The function-pointer task -/

theorem requestAux_sseq (m : Mem.Concrete.State) (ann : List Annot) (pat : Pattern Sym) (a b : EE)
    (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.effectExpr (.mk ann (.sseq pat a b)) env) k wc =
      .next (.effectExpr a env) (.strongBind pat b env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_sbind (m : Mem.Concrete.State) (ann : List Annot) (p : Sym) (ty : BaseType)
    (v : Val) (b : EE) (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value v) (.strongBind (.mk ann (.base (some p, ty))) b env :: k) wc =
      .next (.effectExpr b (extendEnv [(p, v)] env)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, matchPattern]

/-- The value of the function-pointer task: the pointer and the metadata of `g`. -/
def fnInfo (g : Sym) (rty : Ctype) (params : List (Option Sym × Ctype)) (variadic proto : Bool) :
    Val :=
  .tuple [.loaded (.specified (.pointer (.function g))),
    .tuple [.ctype rty, .list .ctype (params.map fun q => .ctype q.2), boolean variadic,
      boolean proto]]

/-- **The function-pointer task** `let strong q = pure(<g>) in pure((q, cfunction(q)))` runs to
the pointer and the metadata of `g` by local steps, changing only the current location. -/
theorem fnTask_local {wc : Bool} (a0 pa a1 a2 a3 a4 a5 a6 a7 : List Annot) (pt : BaseType)
    {q q₁ q₂ g : Sym} (h₁ : q₁.key = q.key) (h₂ : q₂.key = q.key) {loc : Loc} {attrs : Attributes}
    {rty : Ctype} {params : List (Option Sym × Ctype)} {variadic proto : Bool}
    (hg : file.funInfo.lookup g = some (loc, attrs, rty, params, variadic, proto))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ l', LocalReaches file labels wc
      ⟨.effectExpr (.mk a0 (.sseq (.mk pa (.base (some q, pt)))
        (.mk a1 (.pure (.mk a2 () (.val (.loaded (.specified (.pointer (.function g))))))))
        (.mk a3 (.pure (.mk a4 () (.ctor .tuple
          [.mk a5 () (.sym q₁), .mk a6 () (.cfunction (.mk a7 () (.sym q₂)))])))))) env, k, m⟩
      ⟨.value (fnInfo g rty params variadic proto), k, {m with currentLocation := l'}⟩ := by
  let fp : Val := .loaded (.specified (.pointer (.function g)))
  let env₁ := extendEnv [(q, fp)] env
  have l1 : env₁.lookup q₁ = some fp := ConvInt.lookup_one h₁
  have l2 : env₁.lookup q₂ = some fp := ConvInt.lookup_one h₂
  let B : EE := .mk a3 (.pure (.mk a4 () (.ctor .tuple
    [.mk a5 () (.sym q₁), .mk a6 () (.cfunction (.mk a7 () (.sym q₂)))])))
  have s0 : LocalReaches file labels wc ⟨.effectExpr (.mk a0 (.sseq (.mk pa (.base (some q, pt)))
        (.mk a1 (.pure (.mk a2 () (.val (.loaded (.specified (.pointer (.function g)))))))) B)) env, k, m⟩
      ⟨.effectExpr (.mk a1 (.pure (.mk a2 () (.val (.loaded (.specified (.pointer (.function g)))))))) env,
        .strongBind (.mk pa (.base (some q, pt))) B env :: k, m⟩ :=
    .single (.next (requestAux_sseq m a0 _ _ _ env k wc) (LoadTask.plain_effectExpr _ _))
  obtain ⟨l1', r1⟩ := LoadTask.pure_val_local (file := file) (labels := labels) (wc := wc) a1 a2
    (.loaded (.specified (.pointer (.function g)))) env
    (.strongBind (.mk pa (.base (some q, pt))) B env :: k) m
  let m₁ : Mem.Concrete.State := {m with currentLocation := l1'}
  have s2 : LocalReaches file labels wc ⟨.value fp, .strongBind (.mk pa (.base (some q, pt))) B env :: k, m₁⟩
      ⟨.effectExpr B env₁, k, m₁⟩ :=
    .single (.next (requestAux_sbind m₁ pa q pt fp B env k wc) (LoadTask.plain_effectExpr _ _))
  obtain ⟨l, hr⟩ := LoadTask.requestAux_pure (file := file) (labels := labels) m₁ a3
    (.mk a4 () (.ctor .tuple [.mk a5 () (.sym q₁), .mk a6 () (.cfunction (.mk a7 () (.sym q₂)))])) env₁ k wc
  obtain ⟨l2', r3⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr _ env₁) (by simpa using hr)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l2'}
  let K := Frame.diagnosticLocation m₁.currentLocation :: k
  let info : Val := .tuple [.ctype rty, .list .ctype (params.map fun q => .ctype q.2),
    boolean variadic, boolean proto]
  let S5 : PE := .mk a5 () (.sym q₁)
  let CF : PE := .mk a6 () (.cfunction (.mk a7 () (.sym q₂)))
  have tail : LocalReaches file labels wc
      ⟨.pureExpr (.mk a4 () (.ctor .tuple [S5, CF])) env₁, K, m₂⟩
      ⟨.value (fnInfo g rty params variadic proto), k, m₂⟩ := by
    refine .head (b := ⟨.pureExpr S5 env₁, .arguments (.ctor .tuple) [] [CF] env₁ :: K, m₂⟩)
      (.next (by rw [requestAux.eq_def]; simp [awaitsScheduling, arguments, S5, CF])
        (LoadTask.plain_pureExpr _ _)) ?_
    refine .head (.next (LoadTask.requestAux_sym m₂ a5 q₁ env₁ l1 _ wc) (LoadTask.plain_value _)) ?_
    refine .head (.next (LoadTask.requestAux_argument m₂ _ [] fp CF [] env₁ _ wc)
      (LoadTask.plain_pureExpr _ _)) ?_
    refine .head (b := ⟨.pureExpr (.mk a7 () (.sym q₂)) env₁,
        .arguments .functionInfo [] [] env₁ :: .arguments (.ctor .tuple) ([] ++ [fp]) [] env₁ :: K, m₂⟩)
      (.next (by rw [requestAux.eq_def]; simp [awaitsScheduling, arguments, CF])
        (LoadTask.plain_pureExpr _ _)) ?_
    refine .head (.next (LoadTask.requestAux_sym m₂ a7 q₂ env₁ l2 _ wc) (LoadTask.plain_value _)) ?_
    refine .head (.next (LoadTask.requestAux_last_argument m₂ _ [] fp env₁ _ wc)
      (LoadTask.plain_apply _ _)) ?_
    refine .head (b := ⟨.value info, .arguments (.ctor .tuple) ([] ++ [fp]) [] env₁ :: K, m₂⟩)
      (.next (by rw [requestAux.eq_def]; simp [awaitsScheduling, hg, info, fp])
        (LoadTask.plain_value _)) ?_
    refine .head (.next (LoadTask.requestAux_last_argument m₂ _ ([] ++ [fp]) info env₁ _ wc)
      (LoadTask.plain_apply _ _)) ?_
    refine (PureLocal.apply_local file (op := .ctor .tuple) trivial
      (v := fnInfo g rty params variadic proto) wc ?_).trans ?_
    · simp [primitive, fnInfo, info, fp, pure, Except.pure]
    · exact .single (.next (Interleave.requestAux_value_diagnostic file labels m₂ _ _ k wc)
        (LoadTask.plain_value _))
  exact ⟨l2', s0.trans (r1.trans (s2.trans (r3.trans tail)))⟩

/-- The function-pointer task only reads. -/
theorem fnTask_readTask (I : Mem.Concrete.State → Prop) (a0 pa a1 a2 a3 a4 a5 a6 a7 : List Annot)
    (pt : BaseType) {q q₁ q₂ g : Sym} (h₁ : q₁.key = q.key) (h₂ : q₂.key = q.key) {loc : Loc}
    {attrs : Attributes} {rty : Ctype} {params : List (Option Sym × Ctype)} {variadic proto : Bool}
    (hg : file.funInfo.lookup g = some (loc, attrs, rty, params, variadic, proto)) (env : Env) :
    ReadTask (file := file) (labels := labels) I env
      (.mk a0 (.sseq (.mk pa (.base (some q, pt)))
        (.mk a1 (.pure (.mk a2 () (.val (.loaded (.specified (.pointer (.function g))))))))
        (.mk a3 (.pure (.mk a4 () (.ctor .tuple
          [.mk a5 () (.sym q₁), .mk a6 () (.cfunction (.mk a7 () (.sym q₂)))]))))))
      (fnInfo g rty params variadic proto) := by
  refine ⟨by simp [hasCCall], fun m _ => ?_⟩
  obtain ⟨l', run⟩ := fnTask_local (file := file) (labels := labels) (wc := false) a0 pa a1 a2 a3 a4 a5
    a6 a7 pt h₁ h₂ hg env [] m
  exact ⟨[], _, by simp, ⟨l', m.lastUsed, rfl⟩, [], run, rfl⟩

/-! ## Memories -/

open Locals (Slot)
open Mem.Concrete (LiveInt IntRange nextIntAddress)
open IntExpr (Term)
open ReturnLit (NoBoundary ReturnLabel noBoundary_cons)

theorem touched_seq (ann : List Annot) (m : Mem.Concrete.State) :
    Touched m (SeqReach.focusMemory ann m) :=
  ⟨_, m.lastUsed, SeqReach.focusMemory_shape ann m⟩

theorem touched_nextIntAddress {m m' : Mem.Concrete.State} (h : Touched m m') :
    nextIntAddress m' = nextIntAddress m := by
  obtain ⟨l, u, rfl⟩ := h; rfl

theorem touched_nextId {m m' : Mem.Concrete.State} (h : Touched m m') : m'.nextId = m.nextId := by
  obtain ⟨l, u, rfl⟩ := h; rfl

theorem touched_dead {m m' : Mem.Concrete.State} (h : Touched m m') : m'.dead = m.dead := by
  obtain ⟨l, u, rfl⟩ := h; rfl

theorem touched_live {m m' : Mem.Concrete.State} (h : Touched m m') {id addr : Int}
    (l : LiveInt m id addr) : LiveInt m' id addr := by
  obtain ⟨_, _, rfl⟩ := h
  exact Locals.liveInt_with l rfl rfl

/-! ## The callee -/

/-- A statement sequence of a procedure with the parameter `x` that starts with `return e;`,
`e` an `int` expression of `IntExpr.term` (reads of `x` allowed). -/
def retTermArg (file : File Codec.wireModel Unit Unit) (ret x : Sym) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ ConvInt.isConvLoadedInt file s = true then IntExpr.term file x e
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retTermArg file ret x a
  | _ => none

/-- The body of a procedure with the parameter `x`: `return e;`, then the return label. -/
def argBody (file : File Codec.wireModel Unit Unit) (x : Sym) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ ReturnLit.saveFree a = true then retTermArg file ret x a else none
  | _ => none

/-- What a callee with one parameter returns: the value of `t` with the parameter's object
holding `n`, or undefined behaviour. -/
def Returns (s : State) (k : List Frame) (m : Mem.Concrete.State) (n : Int) (t : Term) : Prop :=
  (t.Ok n ∧ ∃ m', Touched m m' ∧ Reaches file labels s ⟨.value (IntExpr.spec (t.val n)), k, m'⟩) ∨
    ∃ s', Reaches file labels s s' ∧ s'.control = .halt IntExpr.overflow

theorem Returns.pre {s s' : State} {k : List Frame} {m : Mem.Concrete.State} {n : Int} {t : Term}
    (h : Reaches file labels s s') (o : Returns (file := file) (labels := labels) s' k m n t) :
    Returns (file := file) (labels := labels) s k m n t := by
  rcases o with ⟨ok, m', tch, r⟩ | ⟨s'', r, hs⟩
  · exact .inl ⟨ok, m', tch, h.trans r⟩
  · exact .inr ⟨s'', h.trans r, hs⟩

theorem jump_returns' {ret l : Sym} {L : Labels} (hl : l.key = ret.key) (hret : ReturnLabel L ret)
    (v : Val) (env : Env) {loc : List Frame} (hk : NoBoundary loc) (caller : List Frame)
    (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧ Reaches file labels
      ⟨.value v, .runLabel l [] [] env :: (loc ++ .procedureReturn L :: caller), m⟩
      ⟨.value v, .procedureReturn L :: caller, m'⟩ := by
  obtain ⟨r, bann, pann, r', hr, hlook⟩ := hret
  have hlook' : L.lookup l = some ([r], .mk bann (.pure (.mk pann () (.sym r')))) := by
    rw [ReturnLit.lookup_key hl]; exact hlook
  refine ⟨SeqReach.focusMemory bann m, touched_seq bann m, ?_⟩
  exact (LoopReach.run_arguments_reaches .nil [] v _ _ m L [r] _ (Call.context_local hk L caller)
    hlook' rfl).trans
    (SeqReach.effect_pure_reaches bann (SeqReach.pure_symbol pann r' _ v (ConvInt.lookup_one hr)) _ m)

/-- **`return e;` in a procedure with a parameter** returns the value of `e` to the caller, or
reaches undefined behaviour. -/
theorem retTermArg_returns {ret x : Sym} {L : Labels} (hret : ReturnLabel L ret) (e : EE)
    (t : Term) (h : retTermArg file ret x e = some t) (env : Env) {loc : List Frame}
    (hk : NoBoundary loc) (caller : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) :
    Returns (file := file) (labels := labels)
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
      (.procedureReturn L :: caller) m n t := by
  unfold retTermArg at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
        [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
      let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env ::
        (loc ++ .procedureReturn L :: caller)
      have pre : Reaches file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
            loc ++ .procedureReturn L :: caller, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
        (ReturnConst.sequence_reaches file labels ann _ _ _ env _ m).trans
          (ReturnLit.bound_reaches bann _ env _ m)
      refine Returns.pre pre ?_
      by_cases ok : t.Ok n
      · left
        refine ⟨ok, ?_⟩
        obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := IntExpr.term_runs (file := file)
          (labels := labels) t h (fun _ => hx) hn ok (.bound :: kR) m (fun _ => slot)
        let v : Val := IntExpr.spec (t.val n)
        have popped : Reaches file labels ⟨.value v, fr ++ .bound :: kR, m₁⟩
            ⟨.value v, kR, m₁⟩ := by
          rcases hfr with ⟨rfl, -⟩ | rfl
          · exact LocalExpr.value_bound_reaches v kR m₁
          · exact Locals.annotations_bound_reaches xs v kR m₁
        let env₁ := extendEnv [(u, v)] env
        have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m₁)) env₁
            (.inl (.mk cann () (.call (.sym s)
              [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                .mk a3 () (.sym u')])))
            (.inl v) :=
          ConvInt.convLoadedInt_eval (ann := tyann) hs (IntExpr.Term.ok_int hn t ok)
            (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
        obtain ⟨m', tch', back⟩ := jump_returns' (file := file) (labels := labels) hl hret v env₁ hk
          caller (ReturnConst.focusMemory rann m₁)
        refine ⟨m', tch.trans ((LoadTask.focusMemory_touched rann m₁).trans tch'), ?_⟩
        refine (Interleave.reaches_of_local file labels run).trans (popped.trans ?_)
        refine (ReturnLit.bind_reaches pann u ty v R env _ m₁).trans ?_
        refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
        exact ((Eval.sound file _ heval) labels _ _ rfl).trans back
      · right
        exact ArenaFail.fail_reaches file labels
          (IntExpr.term_fails (file := file) (labels := labels) t h (fun _ => hx) hn ok (.bound :: kR) m
            (fun _ => slot))
    · cases h
  · rename_i _ ann pann ty a b
    exact Returns.pre (ReturnConst.sequence_reaches file labels ann _ a b env _ m)
      (retTermArg_returns hret a t h env (loc := .strongBind (.mk pann (.base (none, ty))) b env :: loc)
        (noBoundary_cons hk trivial) caller m hx hn slot)
  · cases h
termination_by sizeOf e

/-- The body of a callee with a parameter, entered with its return frame, returns to the
caller. -/
theorem argBody_returns {x : Sym} {body : EE} {t : Term} (h : argBody file x body = some t)
    (env : Env) (caller : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) :
    Returns (file := file) (labels := labels)
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: caller, m⟩ caller m n t := by
  unfold argBody at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      refine Returns.pre (ReturnConst.sequence_reaches file labels ann _ a _ env _ m) ?_
      rcases retTermArg_returns (file := file) (labels := labels) (ReturnLit.returnLabel_body hr hfree) a t h env
          (loc := [.strongBind (.mk pann (.base (none, bt0))) _ env])
          (by simp [NoBoundary, hasBoundary]) caller m hx hn slot with ⟨ok, m', tch, r⟩ | ub
      · exact .inl ⟨ok, m', tch, r.trans (CallReach.return_reaches _ _ caller m')⟩
      · exact .inr ub
    · cases h
  · cases h

/-- The procedure `g` of the file with one `int` parameter `x`, returning `int`, whose body is
`return e;` (`e` recognised as `t`, reads of `x` allowed): `(x, t)`. -/
def calleeArg (file : File Codec.wireModel Unit Unit) (g : Sym) : Option (Sym × Term) :=
  if (file.stdlib.lookup g).isSome then none else
  match file.funInfo.lookup g with
  | some (_, _, rty, [(_, pty)], false, _) =>
    match file.funs.lookup g with
    | some (.procedure _ _ _ [(x, _)] body) =>
      if retKind rty = some true ∧ retKind pty = some true then
        (argBody file x body).map fun t => (x, t)
      else none
    | _ => none
  | _ => none

theorem calleeArg_spec {g x : Sym} {t : Term} (hc : calleeArg file g = some (x, t)) :
    ∃ loc attrs rty po pty proto dloc marker bt xbt body,
      file.stdlib.lookup g = none ∧
      file.funInfo.lookup g = some (loc, attrs, rty, [(po, pty)], false, proto) ∧
      file.funs.lookup g = some (.procedure dloc marker bt [(x, xbt)] body) ∧
      retKind rty = some true ∧ retKind pty = some true ∧ argBody file x body = some t := by
  unfold calleeArg at hc
  split at hc
  · cases hc
  rename_i hstd
  split at hc
  · rename_i loc attrs rty po pty proto hinfo
    split at hc
    · rename_i dloc marker bt x' xbt body hdecl
      split at hc
      · rename_i hk
        cases hb : argBody file x' body with
        | none => simp [hb] at hc
        | some t' =>
          simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact ⟨loc, attrs, rty, po, pty, proto, dloc, marker, bt, xbt, body, by simpa using hstd,
            hinfo, hdecl, hk.1, hk.2, hb⟩
      · cases hc
    · cases hc
  · cases hc

/-! ## The call site, layer by layer -/

/-- `kill(int, x) ; pure(r)`. -/
def killTail (x r : Sym) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (none, _))) kl (.mk _ (.pure (.mk _ () (.sym r₁))))) =>
      Locals.killInt x kl && decide (r₁.key = r.key)
  | _ => false

theorem killTail_reaches {x r : Sym} {e : EE} (h : killTail x r e = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {id addr : Int} {v : Val}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hr : env.lookup r = some v) (live : LiveInt m id addr) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value v, k, m'⟩ := by
  unfold killTail at h
  split at h
  · rename_i _ ann kann kt kl pann bann r₁
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hkl, hr₁⟩ := h
    obtain ⟨m₁, out₁, rk⟩ := Locals.killInt_reaches (file := file) (labels := labels) hkl env
      (.strongBind (.mk kann (.base (none, kt))) (.mk pann (.pure (.mk bann () (.sym r₁)))) env :: k) m hx
      live
    refine ⟨SeqReach.focusMemory pann m₁, by simp [out₁], ?_⟩
    refine (ReturnConst.sequence_reaches file labels ann _ kl _ env k m).trans (rk.trans ?_)
    refine (ReturnConst.wildcard_sequence_reaches file labels kann kt .unit _ env k m₁).trans ?_
    exact SeqReach.effect_pure_reaches pann
      (SeqReach.pure_symbol bann r₁ env v (by rw [ReturnLit.lookup_key hr₁]; exact hr)) k m₁
  · cases h

/-- `let strong r = ccall(_, p, [x]) in kill(int, x) ; pure(r)`. -/
def callTail (p x : Sym) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (some r, _)))
      (.mk _ (.ccall () _ (.mk _ () (.sym p₁)) [.mk _ () (.sym x₁)])) kt) =>
      decide (p₁.key = p.key ∧ x₁.key = x.key ∧ x.key ≠ r.key) && killTail x r kt
  | _ => false

theorem callTail_returns {p x : Sym} {e : EE} (h : callTail p x e = true) {g x0 : Sym} {t : Term}
    (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value (IntExpr.spec (t.val n)), k, m'⟩) ∨
    ∃ s', Reaches file labels ⟨.effectExpr e env, k, m⟩ s' ∧ s'.control = .halt IntExpr.overflow := by
  obtain ⟨loc, attrs, frt, po, fpt, proto, dloc, marker, bt, xbt, body, hstd, hinfo, hdecl, -, -,
    hbody⟩ := calleeArg_spec hc
  unfold callTail at h
  split at h
  · rename_i _ ann rann r rt cann mt pann p₁ xann x₁ kt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp₁, hx₁, hxr⟩, hkt⟩ := h
    let ptr : Val := .object (.pointer (.allocated id addr))
    let K := Frame.strongBind (.mk rann (.base (some r, rt))) kt env :: k
    have enter := (ReturnConst.sequence_reaches file labels ann _ _ kt env k m).trans
      (CallReach.ccall_reaches (file := file) (labels := labels) (args := [ptr]) cann mt
        (SeqReach.pure_symbol pann p₁ env _ (by rw [ReturnLit.lookup_key hp₁]; exact hp))
        (.cons (SeqReach.pure_symbol xann x₁ env _ (by rw [ReturnLit.lookup_key hx₁]; exact hx)) .nil)
        (CallReach.procedure_not_builtin hdecl)
        (CallReach.procedure_body (values := [ptr]) hstd hdecl rfl) K m)
    rcases argBody_returns (file := file) (labels := labels) hbody (extendEnv [(x0, ptr)] env) K
        (SeqReach.focusMemory cann m) (ConvInt.lookup_one rfl) hn ((touched_seq cann m).slot slot) with
      ⟨ok, m₁, tch, r₁⟩ | ⟨s', r₁, hs'⟩
    · left
      refine ⟨ok, ?_⟩
      let v := IntExpr.spec (t.val n)
      let env₁ := extendEnv [(r, v)] env
      have hx' : env₁.lookup x = some ptr := by
        rw [ConvInt.lookup_one_other hxr]; exact hx
      obtain ⟨m₂, out₂, rk⟩ := killTail_reaches (file := file) (labels := labels) hkt env₁ k m₁ hx'
        (ConvInt.lookup_one rfl) (touched_live tch (touched_live (touched_seq cann m) slot.live))
      refine ⟨m₂, by rw [out₂, tch.stdout]; simp, ?_⟩
      exact enter.trans (r₁.trans ((SeqReach.strong_bind_reaches rfl k m₁).trans rk))
    · exact .inr ⟨s', enter.trans r₁, hs'⟩
  · cases h

/-- The argument object: `let weak o = create(alignof(int), int) in
store(int, o, conv_loaded_int(int, a)) ; pure(o)`. -/
def mkArg (file : File Codec.wireModel Unit Unit) (a : Sym) : Eff → Bool
  | .mk _ (.wseq (.mk _ (.base (some o, _))) cr
      (.mk _ (.wseq (.mk _ (.base (none, _)))
        (.mk _ (.action (.mk .pos (.mk _ _ (.store false
          (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
          (.mk _ () (.sym o₁))
          (.mk _ () (.call (.sym cv) [.mk _ () (.val (.ctype (.mk _
            (.basic (.integer (.signed .int)))))), .mk _ () (.sym a₁)])) .na)))))
        (.mk _ (.pure (.mk _ () (.sym o₂))))))) =>
      Locals.createInt cr && decide (o₁.key = o.key ∧ o₂.key = o.key ∧ a₁.key = a.key ∧ a.key ≠ o.key) &&
        ConvInt.isConvLoadedInt file cv
  | _ => false

theorem mkArg_reaches {a : Sym} {e : EE} (h : mkArg file a e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {n : Int} (ha : env.lookup a = some (.loaded (.specified (.integer n))))
    (hn : IntRange n) (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m' ys, m'.stdout = m.stdout ∧ Slot m' m.nextId (nextIntAddress m) n ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), .annotations ys :: k, m'⟩ := by
  unfold mkArg at h
  split at h
  · rename_i _ ann oann o ot cr wann w2ann w2t stann stl stu a1 c1 a2 o₁ a3 cv a4 c3 a5 a₁ pann bann o₂
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hcr, ho₁, ho₂, ha₁, hao⟩, hcv⟩ := h
    let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
    let PURE : EE := .mk pann (.pure (.mk bann () (.sym o₂)))
    let ST : EE := .mk stann (.action (.mk .pos (.mk stl stu (.store false
          (.mk a1 () (.val (.ctype (.mk c1 (.basic (.integer (.signed .int)))))))
          (.mk a2 () (.sym o₁))
          (.mk a3 () (.call (.sym cv) [.mk a4 () (.val (.ctype (.mk c3
            (.basic (.integer (.signed .int)))))), .mk a5 () (.sym a₁)])) .na))))
    let W2 : EE := .mk wann (.wseq (.mk w2ann (.base (none, w2t))) ST PURE)
    obtain ⟨m₁, out₁, live₁, rc⟩ := Locals.createInt_reaches (file := file) (labels := labels) hcr env
      (.effectBind (.mk oann (.base (some o, ot))) W2 env :: k) m hpos hdead
    let env₁ := extendEnv [(o, ptr)] env
    have hx₁ : env₁.lookup o₁ = some ptr := ConvInt.lookup_one ho₁
    have ht₁ : env₁.lookup a₁ = some (.loaded (.specified (.integer n))) := by
      rw [ConvInt.lookup_one_other (by rw [ha₁]; exact hao), ReturnLit.lookup_key ha₁]; exact ha
    obtain ⟨ys, rst⟩ := Locals.store_reaches (file := file) (labels := labels) stann a1 a2 a3 a4 a5 c1 c3
      stl stu o₁ cv a₁ hcv env₁ (.effectBind (.mk w2ann (.base (none, w2t))) PURE env₁ :: k) m₁ hx₁ ht₁ hn
      live₁
    let m₂ := Locals.stored (ReturnConst.focusMemory stann m₁) m.nextId (nextIntAddress m) n
    have slot₂ : Slot m₂ m.nextId (nextIntAddress m) n :=
      Locals.stored_slot (Locals.liveInt_focus stann live₁) n
    refine ⟨SeqReach.focusMemory pann m₂, ys, ?_, (touched_seq pann m₂).slot slot₂, ?_⟩
    · simp [m₂, Locals.stored_stdout, out₁]
    refine (Locals.wseq_reaches (file := file) (labels := labels) ann _ cr W2 env k m).trans
      (rc.trans ?_)
    refine (Locals.wbind_reaches oann o ot ptr W2 env k m₁).trans ?_
    refine (Locals.wseq_reaches (file := file) (labels := labels) wann _ ST PURE env₁ k m₁).trans
      (rst.trans ?_)
    refine (annotations_wbind_reaches ys (bs := []) rfl PURE env₁ k m₂).trans ?_
    exact SeqReach.effect_pure_reaches pann
      (SeqReach.pure_symbol bann o₂ _ ptr (by rw [lookup_nil]; exact ConvInt.lookup_one ho₂))
      (.annotations ys :: k) m₂
  · cases h


/-- What a call with an argument shows: the callee's value with the argument object holding
`n`, above the arena's annotations, or undefined behaviour. -/
def ArgGives (s : State) (k : List Frame) (out : String) (n : Int) (t : Term) : Prop :=
  (t.Ok n ∧ ∃ m' zs, m'.stdout = out ∧
    Reaches file labels s ⟨.value (IntExpr.spec (t.val n)), .annotations zs :: k, m'⟩) ∨
  ∃ s', Reaches file labels s s' ∧ s'.control = .halt IntExpr.overflow

/-- `let t = params_nth(ps, 0) in if not are_compatible(int, t) then undef else <mkArg>`. -/
def letArg (file : File Codec.wireModel Unit Unit) (pty a : Sym) : Eff → Bool
  | .mk _ (.let_ (.mk _ (.base (some tt, _)))
      (.mk _ () (.call (.sym nth) [.mk _ () (.sym pty₂), .mk _ () (.val (.object (.integer zero)))]))
      (.mk _ (.if_ (.mk _ () (.not (.mk _ () (.areCompatible (.mk _ () (.val (.ctype ity)))
          (.mk _ () (.sym tt₁))))))
        _ mk))) =>
      decide (pty₂.key = pty.key ∧ tt₁.key = tt.key ∧ zero = 0 ∧ a.key ≠ tt.key) &&
        isParamsNth file nth && decide (retKind ity = some true) && mkArg file a mk
  | _ => false

theorem letArg_reaches {pty a : Sym} {e : EE} (h : letArg file pty a e = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {c : Ctype} {n : Int}
    (hp : env.lookup pty = some (.list .ctype [.ctype c])) (hc : retKind c = some true)
    (ha : env.lookup a = some (.loaded (.specified (.integer n)))) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m' ys, m'.stdout = m.stdout ∧ Slot m' m.nextId (nextIntAddress m) n ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), .annotations ys :: k, m'⟩ := by
  unfold letArg at h
  split at h
  · rename_i _ lann tann tt tbt nann nth a1 pty₂ a2 zero iann cann bann cvann ity cfann tt₁ u mk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpty, htt, rfl, hat⟩, hnth⟩, hity⟩, hmk⟩ := h
    let env₁ := extendEnv [(tt, .ctype c)] env
    let m₁ := SeqReach.focusMemory lann m
    let m₂ := SeqReach.focusMemory iann m₁
    have T : Touched m m₂ := (touched_seq lann m).trans (touched_seq iann m₁)
    have ha₁ : env₁.lookup a = some (.loaded (.specified (.integer n))) := by
      rw [ConvInt.lookup_one_other hat]; exact ha
    obtain ⟨m', ys, out, slot, r⟩ := mkArg_reaches (file := file) (labels := labels) hmk env₁ k m₂ ha₁ hn
      (by rw [touched_nextIntAddress T]; exact hpos) (by rw [touched_nextId T, touched_dead T]; exact hdead)
    rw [touched_nextId T, touched_nextIntAddress T] at slot r
    refine ⟨m', ys, by rw [out, T.stdout], slot, ?_⟩
    refine (SeqReach.effect_let_reaches lann (xs := [(tt, .ctype c)])
      (Call.pureEval_of (nth_zero_eval hnth ((ReturnLit.lookup_key hpty).trans hp))) rfl k m).trans ?_
    refine (SeqReach.effect_if_reaches iann false
      (notCompatible_reaches hity hc (ConvInt.lookup_one htt)) k m₁).trans ?_
    exact r
  · cases h

theorem ArgGives.pre {s s' : State} {k : List Frame} {out : String} {n : Int} {t : Term}
    (h : Reaches file labels s s') (o : ArgGives (file := file) (labels := labels) s' k out n t) :
    ArgGives (file := file) (labels := labels) s k out n t := by
  rcases o with ⟨ok, m', zs, hout, r⟩ | ⟨s'', r, hs⟩
  · exact .inl ⟨ok, m', zs, hout, h.trans r⟩
  · exact .inr ⟨s'', h.trans r, hs⟩

/-- `let strong x = <letArg> in <callTail>`. -/
def restArg (file : File Codec.wireModel Unit Unit) (pty a p : Sym) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (some x, _))) la ct) =>
      decide (p.key ≠ x.key) && letArg file pty a la && callTail p x ct
  | _ => false

theorem restArg_gives {pty a p : Sym} {e : EE} (h : restArg file pty a p e = true) {g x0 : Sym}
    {t : Term} (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {c : Ctype} {n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hpty : env.lookup pty = some (.list .ctype [.ctype c])) (hcint : retKind c = some true)
    (ha : env.lookup a = some (.loaded (.specified (.integer n)))) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ArgGives (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ k m.stdout n t := by
  unfold restArg at h
  split at h
  · rename_i _ ann xann x xbt la ct
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpx, hla⟩, hct⟩ := h
    obtain ⟨m₁, ys, out₁, slot₁, r₁⟩ := letArg_reaches (file := file) (labels := labels) hla env
      (.strongBind (.mk xann (.base (some x, xbt))) ct env :: k) m hpty hcint ha hn hpos hdead
    let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
    let env₁ := extendEnv [(x, ptr)] env
    have pre := (ReturnConst.sequence_reaches file labels ann _ la ct env k m).trans
      (r₁.trans (annotations_sbind_reaches ys (bs := [(x, ptr)]) rfl ct env k m₁))
    rcases callTail_returns (file := file) (labels := labels) hct hc env₁ (.annotations ys :: k) m₁
        (by rw [ConvInt.lookup_one_other hpx]; exact hp) (ConvInt.lookup_one rfl) hn slot₁ with
      ⟨ok, m₂, out₂, r₂⟩ | ⟨s', r₂, hs'⟩
    · exact .inl ⟨ok, m₂, ys, by rw [out₂, out₁], pre.trans r₂⟩
    · exact .inr ⟨s', pre.trans r₂, hs'⟩
  · cases h

/-- `if not (params_length(ps) = 1) then undef else
if v || not are_compatible(int, f) then undef else <restArg>`. -/
def guards (file : File Codec.wireModel Unit Unit) (fty pty vs a p : Sym) : Eff → Bool
  | .mk _ (.if_ (.mk _ () (.not (.mk _ () (.op .eq (.mk _ () (.call (.sym len) [.mk _ () (.sym pty₁)]))
        (.mk _ () (.val (.object (.integer one))))))))
      _ (.mk _ (.if_ (.mk _ () (.op .or (.mk _ () (.sym vs₁)) (.mk _ () (.not (.mk _ ()
          (.areCompatible (.mk _ () (.val (.ctype rty))) (.mk _ () (.sym fty₁))))))))
        _ rest))) =>
      decide (pty₁.key = pty.key ∧ vs₁.key = vs.key ∧ fty₁.key = fty.key ∧ one = 1) &&
        isParamsLength file len && decide (retKind rty = some true) && restArg file pty a p rest
  | _ => false

theorem guards_gives {fty pty vs a p : Sym} {e : EE} (h : guards file fty pty vs a p e = true)
    {g x0 : Sym} {t : Term} (hc : calleeArg file g = some (x0, t)) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {c frt : Ctype} {n : Int}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hpty : env.lookup pty = some (.list .ctype [.ctype c])) (hcint : retKind c = some true)
    (hvs : env.lookup vs = some .false) (hfty : env.lookup fty = some (.ctype frt))
    (hfrt : retKind frt = some true)
    (ha : env.lookup a = some (.loaded (.specified (.integer n)))) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ArgGives (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ k m.stdout n t := by
  unfold guards at h
  split at h
  · rename_i _ i1ann c1a c1b c1c len c1d pty₁ c1e one u1 i2ann c2a c2b vs₁ c2c c2d c2e rty c2f fty₁
      u2 rest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpty₁, hvs₁, hfty₁, rfl⟩, hlen⟩, hrty⟩, hrest⟩ := h
    let m₁ := SeqReach.focusMemory i1ann m
    let m₂ := SeqReach.focusMemory i2ann m₁
    have T : Touched m m₂ := (touched_seq i1ann m).trans (touched_seq i2ann m₁)
    have o := restArg_gives (file := file) (labels := labels) hrest hc env k m₂ hp hpty hcint ha hn
      (by rw [touched_nextIntAddress T]; exact hpos) (by rw [touched_nextId T, touched_dead T]; exact hdead)
    rw [T.stdout] at o
    refine ArgGives.pre ?_ o
    refine (SeqReach.effect_if_reaches i1ann false
      (Call.pureEval_of (length_one_eval hlen ((ReturnLit.lookup_key hpty₁).trans hpty))) k m).trans ?_
    exact SeqReach.effect_if_reaches i2ann false (variadicCheck_reaches hrty hfrt
      ((ReturnLit.lookup_key hvs₁).trans hvs) ((ReturnLit.lookup_key hfty₁).trans hfty)) k m₁
  · cases h

/-- The function-pointer task of the arena: the procedure it points to. -/
def fnTask : Eff → Option Sym
  | .mk _ (.sseq (.mk _ (.base (some q, _)))
      (.mk _ (.pure (.mk _ () (.val (.loaded (.specified (.pointer (.function g))))))))
      (.mk _ (.pure (.mk _ () (.ctor .tuple [.mk _ () (.sym q₁), .mk _ () (.cfunction (.mk _ () (.sym q₂)))]))))) =>
      if q₁.key = q.key ∧ q₂.key = q.key then some g else none
  | _ => none

/-- Tasks that are strong sequences, as the function-pointer task is. -/
def isSseq : Eff → Bool
  | .mk _ (.sseq ..) => true
  | _ => false

/-- Tasks other than the function-pointer task's form. -/
def isPure (e : Eff) : Bool := !isSseq e

/-- The argument task: a closed `int` expression (a literal, or the glue around a C operator on
literals) that is not a strong sequence. -/
def argLit (file : File Codec.wireModel Unit Unit) (e : Eff) : Option Int :=
  if isSseq e then none else ClosedEff.lit file e

/-- The argument task only reads, and runs to its folded literal. -/
theorem argLit_spec {e : EE} {n : Int} (h : argLit file e = some n)
    (I : Mem.Concrete.State → Prop) (env : Env) :
    isPure e = true ∧ Mem.Concrete.IntRange n ∧
      ReadTask (file := file) (labels := labels) I env e (.loaded (.specified (.integer n))) := by
  unfold argLit at h
  split at h
  · cases h
  · rename_i hs
    have hr := (ClosedEff.lit_inv file h).2
    refine ⟨by simp [isPure, hs], hr, ClosedEff.lit_noCall file h, fun m _ => ?_⟩
    obtain ⟨l, fr, hfr, r⟩ := ClosedEff.lit_local file labels h env [] m
    refine ⟨[], {m with currentLocation := l}, by simp, ⟨l, m.lastUsed, rfl⟩, fr ++ [], r, ?_⟩
    rcases hfr with ⟨rfl, -⟩ | rfl <;> rfl

theorem fnTask_spec {e : EE} {g : Sym} (h : fnTask e = some g) (I : Mem.Concrete.State → Prop)
    {loc : Loc} {attrs : Attributes} {rty : Ctype} {params : List (Option Sym × Ctype)}
    {variadic proto : Bool}
    (hg : file.funInfo.lookup g = some (loc, attrs, rty, params, variadic, proto)) (env : Env) :
    isPure e = false ∧
      ReadTask (file := file) (labels := labels) I env e (fnInfo g rty params variadic proto) := by
  unfold fnTask at h
  split at h
  · rename_i _ a0 pa q pt a1 a2 g' a3 a4 a5 q₁ a6 a7 q₂
    split at h
    · rename_i cond
      cases h
      exact ⟨rfl, fnTask_readTask I a0 pa a1 a2 a3 a4 a5 a6 a7 pt cond.1 cond.2 hg env⟩
    · cases h
  · cases h

/-- The elaboration of a call `g(n)` of a procedure with one `int` parameter, `n` a closed
`int` expression (`argLit`): the procedure `g` and the value of `n`. -/
def argSite (file : File Codec.wireModel Unit Unit) : Eff → Option (Sym × Int)
  | .mk _ (.sseq (.mk _ (.ctor .tuple [.mk _ (.ctor .tuple [.mk _ (.base (some p, _)),
        .mk _ (.ctor .tuple [.mk _ (.base (some fty, _)), .mk _ (.base (some pty, _)),
          .mk _ (.base (some vs, _)), .mk _ (.base (some pr, _))])]),
        .mk _ (.base (some a, _))]))
      (.mk _ (.unseq [t1, t2])) gd) =>
      match fnTask t1 with
      | some g => match argLit file t2 with
        | some n =>
          if decide (fty.key ≠ p.key ∧ pty.key ≠ p.key ∧ pty.key ≠ fty.key ∧ vs.key ≠ p.key ∧
                vs.key ≠ fty.key ∧ vs.key ≠ pty.key) &&
              decide (a.key ≠ p.key ∧ a.key ≠ fty.key ∧ a.key ≠ pty.key ∧ a.key ≠ vs.key ∧
                a.key ≠ pr.key) &&
              decide (-2147483648 ≤ n ∧ n ≤ 2147483647) && guards file fty pty vs a p gd
          then some (g, n) else none
        | none => none
      | none => none
  | _ => none

theorem argSite_range {e : EE} {g : Sym} {n : Int} (h : argSite file e = some (g, n)) :
    IntRange n := by
  unfold argSite at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i cond
          simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact cond.1.2
        · cases h
      · cases h
    · cases h
  · cases h

/-- **A call `g(n)`**: the caller creates and initialises the argument object, `g` reads it
through its parameter, the caller kills it after the return. -/
theorem argCall_gives {e : EE} {g x0 : Sym} {n : Int} {t : Term}
    (hs : argSite file e = some (g, n)) (hc : calleeArg file g = some (x0, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m)
    (hdead : m.nextId ∉ m.dead) :
    ArgGives (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ k m.stdout n t := by
  obtain ⟨loc, attrs, frt, po, fpt, proto, dloc, marker, bt, xbt, body, hstd, hinfo, hdecl, hfr, hfp,
    hbody⟩ := calleeArg_spec hc
  unfold argSite at hs
  split at hs
  · rename_i _ eA pA pA1 pA2 p pT pA3 fA fty fT psA pty psT vA vs vT prA pr prT aA a aT uA t1 T2 gd
    split at hs
    · rename_i g' hfn
      split at hs
      · rename_i n' hlit
        split at hs
        · rename_i cond
          simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
          obtain ⟨⟨⟨⟨nfp, npp, npf, nvp, nvf, nvpt⟩, nap, naf, napt, nav, napr⟩, lo, hi⟩, hgd⟩ := cond
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨hg, hnn⟩ := hs
          subst hg hnn
          have hn : IntRange n' := ⟨lo, hi⟩
          let fp : Val := .loaded (.specified (.pointer (.function g')))
          let lit : Val := .loaded (.specified (.integer n'))
          let info := fnInfo g' frt [(po, fpt)] false proto
          let val : EE → Val := fun e => if isPure e then lit else info
          obtain ⟨hpure, hread⟩ := fnTask_spec (file := file) (labels := labels) hfn (fun _ => True) hinfo env
          obtain ⟨hpure₂, -, hread₂⟩ := argLit_spec (file := file) (labels := labels) hlit (fun _ => True) env
          have tasks : ∀ e ∈ [t1, T2], ReadTask (file := file) (labels := labels) (fun _ => True) env e
              (val e) := by
            intro e he
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl
            · simpa [val, hpure] using hread
            · simpa [val, hpure₂] using hread₂
          have hvals : [t1, T2].map val = [info, lit] := by
            show [val t1, val T2] = [info, lit]
            simp only [val, hpure, hpure₂, Bool.false_eq_true, ↓reduceIte]
          let PAT : Pattern Sym := .mk pA (.ctor .tuple [.mk pA1 (.ctor .tuple [.mk pA2 (.base (some p, pT)),
            .mk pA3 (.ctor .tuple [.mk fA (.base (some fty, fT)), .mk psA (.base (some pty, psT)),
              .mk vA (.base (some vs, vT)), .mk prA (.base (some pr, prT))])]), .mk aA (.base (some a, aT))])
          obtain ⟨xs, m₁, -, tch₁, run⟩ := LoadTask.unseq_reads (file := file) (labels := labels)
            (k := .strongBind PAT gd env :: k) (annots := uA) (fun _ => True) (fun _ _ _ _ => trivial) val
            tasks m trivial
          rw [hvals] at run
          let bs : Bindings := [(p, fp), (fty, .ctype frt), (pty, .list .ctype [.ctype fpt]),
            (vs, boolean false), (pr, boolean proto), (a, lit)]
          let env₁ := extendEnv bs env
          have pre : Reaches file labels ⟨.effectExpr (.mk eA (.sseq PAT (.mk uA (.unseq [t1, T2])) gd)) env, k, m⟩
              ⟨.effectExpr gd env₁, .annotations xs :: k, m₁⟩ :=
            (ReturnConst.sequence_reaches file labels eA PAT _ gd env k m).trans
              ((Interleave.reaches_of_local file labels run).trans
                (annotations_sbind_reaches xs (bs := bs) rfl gd env k m₁))
          have lp : env₁.lookup p = some fp := lookup_cons_eq rfl
          have lfty : env₁.lookup fty = some (.ctype frt) := by
            rw [lookup_cons_ne nfp]; exact lookup_cons_eq rfl
          have lpty : env₁.lookup pty = some (.list .ctype [.ctype fpt]) := by
            rw [lookup_cons_ne npp, lookup_cons_ne npf]; exact lookup_cons_eq rfl
          have lvs : env₁.lookup vs = some .false := by
            rw [lookup_cons_ne nvp, lookup_cons_ne nvf, lookup_cons_ne nvpt]; exact lookup_cons_eq rfl
          have la : env₁.lookup a = some lit := by
            rw [lookup_cons_ne nap, lookup_cons_ne naf, lookup_cons_ne napt, lookup_cons_ne nav,
              lookup_cons_ne napr]
            exact lookup_cons_eq rfl
          have o := guards_gives (file := file) (labels := labels) hgd hc env₁ (.annotations xs :: k) m₁ lp lpty
            hfp lvs lfty hfr la hn (by rw [touched_nextIntAddress tch₁]; exact hpos)
            (by rw [touched_nextId tch₁, touched_dead tch₁]; exact hdead)
          rw [tch₁.stdout] at o
          rcases o with ⟨ok, m', zs, out, r⟩ | ⟨s', r, hs'⟩
          · exact .inl ⟨ok, m', zs ++ xs, out,
              pre.trans (r.trans (Locals.annotations_merge_reaches zs xs _ k m'))⟩
          · exact .inr ⟨s', pre.trans r, hs'⟩
        · cases hs
      · cases hs
    · cases hs
  · cases hs

/-! ## `main` -/

open LocalExpr (Shows)

/-- A statement sequence that starts with `return g(n);`: `n` and what `g` returns. -/
def retArg (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option (Int × Term)
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ ConvInt.isConvLoadedInt file s = true then
        match argSite file e with
        | some (g, n) => (calleeArg file g).map fun (_, t) => (n, t)
        | none => none
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retArg file ret a
  | _ => none

/-- **`return g(n);`** halts with what `g` returns for `n`, or reaches undefined behaviour. -/
theorem retArg_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) {n : Int} {t : Term}
    (h : retArg file ret e = some (n, t)) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ n t m.stdout := by
  unfold retArg at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      split at h
      · rename_i g n' hsite
        cases hca : calleeArg file g with
        | none => simp [hca] at h
        | some xt =>
          obtain ⟨x0, t'⟩ := xt
          simp only [hca, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hn', ht'⟩ := h
          subst hn' ht'
          have hn : IntRange n' := argSite_range hsite
          let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
          let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env :: k
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
                k, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          refine LocalExpr.Shows.pre pre ?_
          rcases argCall_gives (labels := labels) hsite hca env (.bound :: kR) m hpos hdead with
            ⟨ok, m₁, zs, out₁, r⟩ | ⟨s', r, hs'⟩
          · left
            refine ⟨ok, ?_⟩
            let v : Val := IntExpr.spec (t'.val n')
            let env₁ := extendEnv [(u, v)] env
            have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m₁)) env₁
                (.inl (.mk cann () (.call (.sym s)
                  [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                    .mk a3 () (.sym u')])))
                (.inl v) :=
              ConvInt.convLoadedInt_eval (ann := tyann) hs (IntExpr.Term.ok_int hn t' ok)
                (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
            obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk
              (ReturnConst.focusMemory rann m₁)
            refine ⟨m', by simp [out, out₁], ?_⟩
            refine r.trans ((Locals.annotations_bound_reaches zs v kR m₁).trans ?_)
            refine (ReturnLit.bind_reaches pann u ty v R env k m₁).trans ?_
            refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
            exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
          · exact .inr ⟨s', r, hs'⟩
      · cases h
    · cases h
  · rename_i _ ann pann ty a b
    exact LocalExpr.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env k m)
      (retArg_halts hret a h env (k := .strongBind (.mk pann (.base (none, ty))) b env :: k)
        (noBoundary_cons hk trivial) m hpos hdead)
  · cases h
termination_by sizeOf e

/-- The body of `main`: a statement sequence that returns `g(n)`, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option (Int × Term)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ ReturnLit.saveFree a = true then retArg file ret a else none
  | _ => none

/-- `main` returns `g(n)` for a procedure `g` of the file with one `int` parameter. -/
def recognize (doc : Codec.Document) : Option (Int × Term) := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (n : Int) (t : Term)
    (h : recognize doc = some (n, t)) (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s n t "" := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
  cases main : doc.file.main with
  | none => simp [main] at h
  | some sym =>
    cases decl : doc.file.funs.lookup sym with
    | none => simp [main, decl] at h
    | some entry =>
      cases entry <;> try { simp [main, decl] at h }
      case procedure loc marker ty ps body =>
        cases ps with
        | cons p ps => simp [main, decl] at h
        | nil =>
          have hbody : recognizeBody doc.file body = some (n, t) := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hlast, hdead, hentry⟩ :=
            StartupMem.initial_reaches_body_mem doc.file enums args hdefs main decl
          have hlabels : labels = Map.ofList (saves body).reverse := by
            simp [initial, main, decl] at hinit
            exact hinit.2.symm
          unfold recognizeBody at hbody
          split at hbody
          · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
            split at hbody
            · rename_i cond
              obtain ⟨hr, hfree⟩ := cond
              have hret : ReturnLabel labels ret := by
                rw [hlabels]; exact ReturnLit.returnLabel_body hr hfree
              let SAVE : EE :=
                .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
              have o := retArg_halts hret a hbody ∅
                (k := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs])
                (by simp [NoBoundary, hasBoundary]) m (Locals.errno_nextIntAddress hlast)
                (by simp [hdead])
              rw [hout] at o
              exact ⟨s, labels, hinit, LocalExpr.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) o⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with the value
the callee returns for `n`, mod 256, and no output. -/
theorem recognize_sound (doc : Codec.Document) (n : Int) (t : Term) (h : recognize doc = some (n, t))
    (args : List String) :
    Spec.CoreUB doc args ∨ t.Ok n ∧ Spec.CoreBeh doc args (.exit (t.val n % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc n t h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (t.val n % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.CallArg
