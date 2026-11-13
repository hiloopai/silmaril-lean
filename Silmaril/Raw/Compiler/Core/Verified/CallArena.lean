module

public import Silmaril.Compiler.Core.Verified.CallLocal.Defs

/-! # Arithmetic procedure calls as sole remaining operands

The call's metadata checks run locally, the procedure entry is scheduled, and the
callee's complete successful local trace is collected. This is a source theorem;
no execution of the Core program is used by a compiler recognizer.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CallArena

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnConst (focusMemory)
open CallLocal (focus sequence)
open LoadTask (plain_effectExpr plain_pureExpr plain_value plain_apply)

variable {file : Program} {labels : Labels}

/-- A pure evaluation with no effects or scheduling, over every continuation. -/
def LPure (p : PE) (env : Env) (v : Val) : Prop :=
  ∀ k m, LocalReaches file labels false ⟨.pureExpr p env, k, m⟩ ⟨.value v, k, m⟩

theorem of_eval {p : PE} {env : Env} {v : Val}
    (h : ∀ tags, Eval file tags env (.inl p) (.inl v)) :
    LPure (file := file) (labels := labels) p env v :=
  fun k m => PureLocal.eval_local file _ (h _) k m rfl

theorem function_info {ann pann : List Annot} {p g : Sym} {env : Env}
    {loc : Loc} {attrs : Attributes} {rty : Ctype} {params : List (Option Sym × Ctype)}
    {variadic proto : Bool}
    (hp : env.lookup p = some (.loaded (.specified (.pointer (.function g)))))
    (hg : file.funInfo.lookup g = some (loc, attrs, rty, params, variadic, proto)) :
    LPure (file := file) (labels := labels) (.mk ann () (.cfunction (.mk pann () (.sym p)))) env
      (.tuple [.ctype rty, .list .ctype (params.map fun q => .ctype q.2),
        boolean variadic, boolean proto]) := by
  intro k m
  refine .head (.next (c' := .pureExpr (.mk pann () (.sym p)) env)
    (k' := .arguments .functionInfo [] [] env :: k)
    (by simp [requestAux, awaitsScheduling, arguments]) (plain_pureExpr _ _)) ?_
  refine .head (.next (c' := .value (.loaded (.specified (.pointer (.function g)))))
    (k' := .arguments .functionInfo [] [] env :: k)
    (by simp [requestAux, awaitsScheduling, hp]) (plain_value _)) ?_
  refine .head (.next (c' := .apply .functionInfo [.loaded (.specified (.pointer (.function g)))])
    (k' := k) (by simp [requestAux, awaitsScheduling]) (plain_apply _ _)) ?_
  exact .single (.next (by simp [requestAux, awaitsScheduling, hg]) (plain_value _))

theorem compatible {ann aann bann : List Annot} {rty fty : Ctype} {f : Sym} {env : Env}
    {isInt : Bool} (hr : Call.retKind rty = some isInt) (hf : Call.retKind fty = some isInt)
    (hl : env.lookup f = some (.ctype fty)) :
    LPure (file := file) (labels := labels)
      (.mk ann () (.areCompatible (.mk aann () (.val (.ctype rty))) (.mk bann () (.sym f)))) env
      .true := by
  intro k m
  refine (PureLocal.arguments_local file .compatible
    [.mk aann () (.val (.ctype rty)), .mk bann () (.sym f)] env k m false
    (by simp [requestAux, awaitsScheduling])).trans ?_
  have ha : Eval file (tagsOf file m) env
      (.inr [.mk aann () (.val (.ctype rty)), .mk bann () (.sym f)])
      (.inr [.ctype rty, .ctype fty]) := .cons .val (.cons (.sym hl) .nil)
  refine (PureLocal.args_local file _ ha .compatible [] k m rfl).trans ?_
  exact .single (.next (by simp [requestAux, awaitsScheduling, primitive,
    Call.compatible_retKind hr hf, boolean, pure, Except.pure]) (plain_value _))

theorem effect_let (ann : List Annot) {pat : Pattern Sym} {p : PE} {body : EE}
    {env : Env} {v : Val} {xs : Bindings}
    (hp : LPure (file := file) (labels := labels) p env v)
    (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk ann (.let_ pat p body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory ann m⟩ := by
  refine (focus (c' := .pureExpr p env) (k' := .effectBind pat body env :: k)
    ann m (plain_pureExpr _ _) ?_).trans ((hp _ _).tail ?_)
  · simp [requestAux, awaitsScheduling, focusMemory] ; rfl
  · exact .next (by simp [requestAux, awaitsScheduling, hm]) (plain_effectExpr _ _)

theorem effect_if (ann : List Annot) {p : PE} {yes no : EE} {env : Env} (b : Bool)
    (hp : LPure (file := file) (labels := labels) p env (boolean b))
    (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk ann (.if_ p yes no)) env, k, m⟩
      ⟨.effectExpr (if b then yes else no) env, k, focusMemory ann m⟩ := by
  refine (focus (c' := .pureExpr p env) (k' := .effectIf yes no env :: k)
    ann m (plain_pureExpr _ _) ?_).trans ((hp _ _).tail ?_)
  · simp [requestAux, awaitsScheduling, focusMemory] ; rfl
  · cases b <;> exact .next (by simp [requestAux, awaitsScheduling, boolean]) (plain_effectExpr _ _)

theorem sseq_pure (ann firstAnn : List Annot) {pat : Pattern Sym} {p : PE} {body : EE}
    {env : Env} {v : Val} {xs : Bindings}
    (hp : ∀ tags, Eval file tags env (.inl p) (.inl v))
    (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk ann (.sseq pat (.mk firstAnn (.pure p)) body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory firstAnn m⟩ := by
  refine (sequence ann _ _ _ env k m).trans ((CallLocal.pure firstAnn hp _ m).tail ?_)
  exact .next (by simp [requestAux, awaitsScheduling, hm]) (plain_effectExpr _ _)

theorem ccall_start (ann : List Annot) (metadata : PE) {target : PE} {env : Env} {g : Sym}
    (hp : ∀ tags, Eval file tags env (.inl target)
      (.inl (.loaded (.specified (.pointer (.function g))))))
    (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.ccall () metadata target [])) env, k, m⟩
      ⟨.apply (.procedure env) [.loaded (.specified (.pointer (.function g)))], k, focusMemory ann m⟩ := by
  refine (focus (c' := .pureExpr target env) (k' := .arguments (.procedure env) [] [] env :: k)
    ann m (plain_pureExpr _ _) ?_).trans ?_
  · simp [requestAux, awaitsScheduling, arguments, focusMemory] ; rfl
  · simpa [PureEval.argState] using PureLocal.args_local file _
      (Eval.cons (hp _) Eval.nil) (.procedure env) [] k (focusMemory ann m) rfl

/-- A no-parameter int callee with a locally proved arithmetic return. -/
def callee (file : File Codec.wireModel Unit Unit) (g : Sym) : Option IntExpr.Term :=
  if (file.stdlib.lookup g).isSome then none else
  match file.funInfo.lookup g, file.funs.lookup g with
  | some (_, _, rty, [], _, _), some (.procedure _ _ _ [] body) =>
    if Call.retKind rty = some true then CallLocal.bodyTerm file body else none
  | _, _ => none

theorem callee_spec {g : Sym} {t : IntExpr.Term} (hc : callee file g = some t) :
    ∃ loc attrs rty variadic proto dloc marker bt body,
      file.stdlib.lookup g = none ∧
      file.funInfo.lookup g = some (loc, attrs, rty, [], variadic, proto) ∧
      file.funs.lookup g = some (.procedure dloc marker bt [] body) ∧ Call.retKind rty = some true ∧
      CallLocal.bodyTerm file body = some t := by
  unfold callee at hc
  split at hc
  · cases hc
  rename_i hstd
  split at hc
  · rename_i loc attrs rty variadic proto dloc marker bt body hinfo hdecl
    split at hc
    · exact ⟨loc, attrs, rty, variadic, proto, dloc, marker, bt, body,
        by simpa using hstd, hinfo, hdecl, by assumption, hc⟩
    · cases hc
  · cases hc

/-- A call's type checks are local steps, stopping just before its scheduled
procedure entry. The resulting environment, body and memory are explicit. -/
theorem call_prefix {e : EE} {g : Sym} {t : IntExpr.Term}
    (hs : Call.callSite file e = some (g, true)) (hc : callee file g = some t)
    (env : Env) (m : Mem.Concrete.State) :
    ∃ body env' m', CallLocal.bodyTerm file body = some t ∧ m'.stdout = m.stdout ∧
      libraryCall file g = none ∧ procedureBody file g [] = .ok (body, []) ∧
      LocalReaches file labels false ⟨.effectExpr e env, [], m⟩
        ⟨.apply (.procedure env') [.loaded (.specified (.pointer (.function g)))], [], m'⟩ := by
  obtain ⟨loc, attrs, fty, variadic, proto, dloc, marker, bt, body, hstd, hinfo, hdecl, hfk, hbody⟩ :=
    callee_spec hc
  unfold Call.callSite at hs
  split at hs
  · rename_i ann pann p pbt fann vann g' lann tann fa fty' fbt pa pty pbt' w1a w1 w2a w2 cann cpann
      p₁ iann oann lenann len lnann pty₁ zann z iann' cpa cva rty cfa fty₁ ccann mt pann₂ p₂ no1 no2
    split at hs
    · rename_i cond
      obtain ⟨hp₁, hp₂, hpty, hfty, hne, hpf, hpp, rfl, hlen⟩ := cond
      have hrk : Call.retKind rty = some true ∧ g' = g := by
        cases h : Call.retKind rty with
        | none => simp [h] at hs
        | some b =>
          simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          exact ⟨by rw [hs.2], hs.1⟩
      obtain ⟨hrk, rfl⟩ := hrk
      let fp : Val := .loaded (.specified (.pointer (.function g')))
      let env₁ := extendEnv [(p, fp)] env
      let env₂ := extendEnv [(fty', (.ctype fty : Val)), (pty, .list .ctype [])] env₁
      have l1 : env₁.lookup p₁ = some fp := ConvInt.lookup_one hp₁
      have l2 : env₂.lookup pty₁ = some (.list .ctype []) :=
        Call.lookup_ext2_second hpty (fun h => hne h.symm)
      have l3 : env₂.lookup fty₁ = some (.ctype fty) := Call.lookup_ext2_first hfty
      have l4 : env₂.lookup p₂ = some fp := by
        rw [Call.lookup_ext2_other (by rw [hp₂]; exact hpf) (by rw [hp₂]; exact hpp)]
        exact ConvInt.lookup_one hp₂
      have hmatch : matchPattern (.mk tann (.ctor .tuple [.mk fa (.base (some fty', fbt)),
          .mk pa (.base (some pty, pbt')), .mk w1a (.base (none, w1)), .mk w2a (.base (none, w2))]))
          (.tuple [.ctype fty, .list .ctype (([] : List (Option Sym × Ctype)).map fun q => .ctype q.2),
            boolean variadic, boolean proto]) =
          some [(fty', .ctype fty), (pty, .list .ctype [])] := rfl
      let m₁ := focusMemory fann m
      let m₂ := focusMemory lann m₁
      let m₃ := focusMemory iann m₂
      let m₄ := focusMemory iann' m₃
      refine ⟨body, env₂, focusMemory ccann m₄, hbody, by simp [m₄, m₃, m₂, m₁],
        CallReach.procedure_not_builtin hdecl, CallReach.procedure_body hstd hdecl rfl, ?_⟩
      refine (sseq_pure ann fann (pat := .mk pann (.base (some p, pbt))) (xs := [(p, fp)])
        (fun _ => .val) rfl [] m).trans ?_
      refine (effect_let lann (function_info l1 hinfo) hmatch [] m₁).trans ?_
      refine (effect_if iann true (of_eval (Call.length_eval hlen l2)) [] m₂).trans ?_
      refine (effect_if iann' true (compatible hrk hfk l3) [] m₃).trans ?_
      exact ccall_start ccann mt (fun _ => .sym l4) [] m₄
    · cases hs
  · cases hs

/-- A successful arithmetic call, including all metadata checks and scheduling,
finishes the sole remaining operand. Its caller supplies no step guards. -/
theorem call_in_arena {e : EE} {g : Sym} {t : IntExpr.Term}
    (hs : Call.callSite file e = some (g, true)) (hc : callee file g = some t)
    (ok : t.Ok 0) (env : Env) (m : Mem.Concrete.State)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    ∃ m', m'.stdout = m.stdout ∧ CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave ((i, IntExpr.spec (t.val 0), []) :: done) [], k, m'⟩ := by
  obtain ⟨body, env', m₁, hbody, out₁, ordinary, resolved, run⟩ := call_prefix (labels := labels) hs hc env m
  have pending : Pending [] i := ⟨by simp, by simp⟩
  have preRun : CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, [])], k, m⟩
      ⟨.interleave done [(i, .apply (.procedure env')
        [.loaded (.specified (.pointer (.function g)))], [])], k, m₁⟩ := by
    apply reaches_of_local file labels
    have localRun : LocalReaches file labels (taskFlag false k [])
        ⟨.effectExpr e env, [], m⟩
        ⟨.apply (.procedure env') [.loaded (.specified (.pointer (.function g)))], [], m₁⟩ := by
      simpa [taskFlag] using run
    exact ArenaFail.drive_run file labels pending (done := done) (k := k) (wc := false)
      localRun (fun v h => by cases h)
  have entry := ArenaCall.procedure_enter file labels m₁ done i g [] env' body [] [] k ordinary resolved
  obtain ⟨m', out, bodyrun⟩ := CallLocal.body_in_arena (labels := labels) hbody ok env' m₁ done i k
  exact ⟨m', out.trans out₁, preRun.trans (entry.trans (by simpa [extendEnv, CallReach.bodyLabels] using bodyrun))⟩

end Silmaril.Compile.Core.Verified.CallArena
