module

public import Silmaril.Compiler.Core.CallReturn.Defs
public import Silmaril.Compiler.Core.CalleeReturn.Thms
public import Silmaril.Compiler.Core.ElaborationTotal.Thms

/-! Actual zero-argument call metadata, runtime length, compatibility, indirect
Core procedure dispatch and literal-callee return, with arbitrary callers. -/
@[expose] public section
namespace Silmaril.Compiler.Core.CallReturn
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Silmaril.Compile.Core.Verified
open Silmaril.Compiler.Core.CalleeReturn
open Silmaril.Compiler.Core.ElaborationTotal (pureEvaluation_forced)
open SeqReach (focusMemory)
variable {file : Program} {labels : Labels}

private theorem located_next_forced (annotations : List Annot) {control next : Control}
    {frames following : List Frame} {memory : Mem.Concrete.State}
    (live : ∀ outcome, control ≠ .halt outcome)
    (requested : request file labels ⟨control, frames, memory⟩ =
      if (focusMemory annotations memory).currentLocation == memory.currentLocation then .next next following
      else .next (.setLocation (focusMemory annotations memory).currentLocation next) following) :
    Forced.Reaches file labels ⟨control, frames, memory⟩
      ⟨next, following, focusMemory annotations memory⟩ := by
  by_cases equal : (focusMemory annotations memory).currentLocation == memory.currentLocation
  · have current : (focusMemory annotations memory).currentLocation = memory.currentLocation := by
      simpa using equal
    have same : focusMemory annotations memory = memory := by
      rw [SeqReach.focusMemory_shape annotations memory, current]
    rw [same]
    exact Forced.next live (by rw [requested, same]; simp)
  · refine (Forced.next (c' := .setLocation (focusMemory annotations memory).currentLocation next)
      (k' := following) (by intro outcome impossible; exact live outcome impossible)
      (by rw [requested]; simp [equal])).trans ?_
    apply Forced.update (by intro outcome impossible; cases impossible)
    rw [SeqReach.focusMemory_shape annotations memory]
    simp [request, requestAux, awaitsScheduling]

private theorem pure_value (ann : List Annot) (v : Value Codec.wireModel) (env : Env) :
    PureForced (file := file) (labels := labels) (.mk ann () (.val v)) env (runtimeValue v) := by
  intro k m
  apply Forced.next <;> simp [request, requestAux, awaitsScheduling]


private theorem pure_symbol (ann : List Annot) (sym : Sym) (env : Env) (v : Val)
    (h : env.lookup sym = some v) :
    PureForced (file := file) (labels := labels) (.mk ann () (.sym sym)) env v := by
  intro k m
  apply Forced.next <;> simp [request, requestAux, awaitsScheduling, h]


private theorem effect_pure_enter (ann : List Annot) (p : PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk ann (.pure p)) env, k, m⟩
      ⟨.pureExpr p env, .diagnosticLocation m.currentLocation :: k, focusMemory ann m⟩ := by
  apply located_next_forced ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr p env) (.diagnosticLocation m.currentLocation :: k)
    else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
      (.diagnosticLocation m.currentLocation :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]


private theorem effect_pure_reaches (ann : List Annot) {p : PE} {env : Env} {v : Val}
    (hp : PureForced (file := file) (labels := labels) p env v) (k : List Frame) (m : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk ann (.pure p)) env, k, m⟩
      ⟨.value v, k, focusMemory ann m⟩ := by
  refine (effect_pure_enter ann p env k m).trans ((hp _ _).trans ?_)
  apply Forced.next <;> simp [request, requestAux, awaitsScheduling]


private theorem effect_bind_reaches {pat : Pattern Sym} {body : EE} {env : Env} {v : Val}
    {xs : Bindings} (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.value v, .effectBind pat body env :: k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, m⟩ := by
  apply Forced.next <;> simp [request, requestAux, awaitsScheduling, hm]


private theorem strong_bind_reaches {pat : Pattern Sym} {body : EE} {env : Env} {v : Val}
    {xs : Bindings} (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.value v, .strongBind pat body env :: k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, m⟩ := by
  apply Forced.next <;> simp [request, requestAux, awaitsScheduling, hm]


private theorem effect_let_reaches (ann : List Annot) {pat : Pattern Sym} {p : PE} {body : EE}
    {env : Env} {v : Val} {xs : Bindings} (hp : PureForced (file := file) (labels := labels) p env v)
    (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk ann (.let_ pat p body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory ann m⟩ := by
  refine Forced.Reaches.trans (middle :=
    ⟨.pureExpr p env, .effectBind pat body env :: k, focusMemory ann m⟩) ?_ ?_
  · apply located_next_forced ann (by intro o; simp)
    simp only [request, requestAux, awaitsScheduling]
    change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
      Request.next (.pureExpr p env) (.effectBind pat body env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectBind pat body env :: k)) with
      | .next (.jumping s vs env) k => jump labels s vs env k
      | r => r) = _
    by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]
  · exact (hp _ _).trans (effect_bind_reaches hm k _)


private theorem sseq_reaches (ann : List Annot) {pat : Pattern Sym} {a body : EE}
    {env : Env} {v : Val} {xs : Bindings} {k : List Frame} {m m' : Mem.Concrete.State}
    (ha : Forced.Reaches file labels ⟨.effectExpr a env, .strongBind pat body env :: k, m⟩
      ⟨.value v, .strongBind pat body env :: k, m'⟩)
    (hm : matchPattern pat v = some xs) :
    Forced.Reaches file labels ⟨.effectExpr (.mk ann (.sseq pat a body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, m'⟩ := by
  refine Forced.Reaches.trans (middle :=
    ⟨.effectExpr a env, .strongBind pat body env :: k, m⟩) ?_
      (ha.trans (strong_bind_reaches hm k m'))
  apply Forced.next <;> simp [request, requestAux, awaitsScheduling]


private theorem sseq_pure_reaches (ann firstAnn : List Annot) {pat : Pattern Sym} {p : PE} {body : EE}
    {env : Env} {v : Val} {xs : Bindings} (hp : PureForced (file := file) (labels := labels) p env v)
    (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk ann (.sseq pat (.mk firstAnn (.pure p)) body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory firstAnn m⟩ :=
  sseq_reaches ann (effect_pure_reaches firstAnn hp _ _) hm


private theorem effect_if_reaches (ann : List Annot) {p : PE} {yes no : EE} {env : Env} (b : Bool)
    (hp : PureForced (file := file) (labels := labels) p env (boolean b)) (k : List Frame) (m : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.effectExpr (.mk ann (.if_ p yes no)) env, k, m⟩
      ⟨.effectExpr (if b then yes else no) env, k, focusMemory ann m⟩ := by
  refine Forced.Reaches.trans (middle :=
    ⟨.pureExpr p env, .effectIf yes no env :: k, focusMemory ann m⟩) ?_ ?_
  · apply located_next_forced ann (by intro o; simp)
    simp only [request, requestAux, awaitsScheduling]
    change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
      Request.next (.pureExpr p env) (.effectIf yes no env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectIf yes no env :: k)) with
      | .next (.jumping s vs env) k => jump labels s vs env k
      | r => r) = _
    by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]
  · refine (hp _ _).trans ?_
    cases b <;> apply Forced.next <;> simp [request, requestAux, awaitsScheduling, boolean]

private theorem ccall_enter (ann : List Annot) (metadata target : PE) (ps : List PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Forced.Reaches file labels
      ⟨.effectExpr (.mk ann (.ccall () metadata target ps)) env, k, m⟩
      ⟨.pureExpr target env, .arguments (.procedure env) [] ps env :: k, focusMemory ann m⟩ := by
  apply located_next_forced ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr target env) (.arguments (.procedure env) [] ps env :: k)
    else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr target env))
      (.arguments (.procedure env) [] ps env :: k)) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]


private theorem eval_forced {expression : PE} {environment : Env} {value : Val}
    (evaluates : ∀ tags, Eval file tags environment (.inl expression) (.inl value)) :
    PureForced (file := file) (labels := labels) expression environment value :=
  fun frames memory => pureEvaluation_forced file _ (evaluates (tagsOf file memory)) labels frames memory rfl

private theorem arguments_nil_forced (op : Prim) (acc : List Val) (value : Val)
    (environment : Env) (frames : List Frame) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels ⟨.value value, .arguments op acc [] environment :: frames, memory⟩
      ⟨.apply op (acc ++ [value]), frames, memory⟩ := by
  apply Forced.next (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling]

theorem cfunction_forced {ann pann : List Annot} {pointer callee : Sym} {environment : Env}
    {location : Loc} {attributes : Attributes} {result : Ctype} {parameters : List (Option Sym × Ctype)}
    {variadic prototype : Bool}
    (pointsTo : environment.lookup pointer = some (.loaded (.specified (.pointer (.function callee)))))
    (metadata : file.funInfo.lookup callee = some (location, attributes, result, parameters, variadic, prototype)) :
    PureForced (file := file) (labels := labels) (.mk ann () (.cfunction (.mk pann () (.sym pointer))))
      environment (.tuple [.ctype result, .list .ctype (parameters.map fun pair => .ctype pair.2),
        boolean variadic, boolean prototype]) := by
  intro frames memory
  refine (Forced.next (c' := .pureExpr (.mk pann () (.sym pointer)) environment)
    (k' := .arguments .functionInfo [] [] environment :: frames)
    (by intro outcome impossible; cases impossible)
    (by simp [request, requestAux, awaitsScheduling, arguments])).trans ?_
  refine (pure_symbol pann pointer environment _ pointsTo _ _).trans ?_
  refine (arguments_nil_forced .functionInfo [] _ environment frames memory).trans ?_
  apply Forced.next (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling, metadata]

theorem compatible_forced {ann leftAnn rightAnn : List Annot} {expected actual : Ctype}
    {result : Sym} {environment : Env} {integer : Bool}
    (expectedKind : Call.retKind expected = some integer) (actualKind : Call.retKind actual = some integer)
    (found : environment.lookup result = some (.ctype actual)) :
    PureForced (file := file) (labels := labels)
      (.mk ann () (.areCompatible (.mk leftAnn () (.val (.ctype expected)))
        (.mk rightAnn () (.sym result)))) environment .true := by
  intro frames memory
  refine (Forced.next (c' := .pureExpr (.mk leftAnn () (.val (.ctype expected))) environment)
    (k' := .arguments .compatible [] [.mk rightAnn () (.sym result)] environment :: frames)
    (by intro outcome impossible; cases impossible)
    (by simp [request, requestAux, awaitsScheduling, arguments])).trans ?_
  have expectedValue : PureForced (file := file) (labels := labels)
      (.mk leftAnn () (.val (.ctype expected))) environment (.ctype expected) := by
    simpa only [runtimeValue] using pure_value (file := file) (labels := labels) leftAnn (.ctype expected) environment
  refine (expectedValue _ _).trans ?_
  refine (Forced.next (c' := .pureExpr (.mk rightAnn () (.sym result)) environment)
    (k' := .arguments .compatible [.ctype expected] [] environment :: frames)
    (by intro outcome impossible; cases impossible)
    (by simp [request, requestAux, awaitsScheduling])).trans ?_
  refine (pure_symbol rightAnn result environment _ found _ _).trans ?_
  refine (arguments_nil_forced .compatible [.ctype expected] _ environment frames memory).trans ?_
  apply Forced.next (by intro outcome impossible; cases impossible)
  simp [request, requestAux, awaitsScheduling, primitive, Call.compatible_retKind expectedKind actualKind,
    boolean, pure, Except.pure]

theorem ccall_forced_return (annotations : List Annot) (metadata : PE)
    {target : PE} {callee : Sym} {body : EE} {number : Int} {environment : Env}
    (pointsTo : PureForced (file := file) (labels := labels) target environment
      (.loaded (.specified (.pointer (.function callee)))))
    (ordinary : libraryCall file callee = none)
    (resolved : procedureBody file callee [] = .ok (body, []))
    (recognized : ReturnLit.recognizeBody file body = some number)
    (frames : List Frame) (memory : Mem.Concrete.State) :
    ∃ finish, LocationOnly memory finish ∧ Forced.Reaches file labels
      ⟨.effectExpr (.mk annotations (.ccall () metadata target [])) environment, frames, memory⟩
      ⟨.value (.loaded (.specified (.integer number))), frames, finish⟩ := by
  obtain ⟨finish, location, returned⟩ := procedure_forced_return callee body number ordinary resolved recognized
    environment frames (focusMemory annotations memory)
  refine ⟨finish, (CalleeReturn.focus_location annotations memory).trans location, ?_⟩
  exact (ccall_enter annotations metadata target [] environment frames memory).trans
    ((pointsTo _ _).trans ((arguments_nil_forced (.procedure environment) [] _ environment frames _).trans returned))

/-- Actual emitted zero-argument call syntax reaches the recognized callee's
literal value, including real metadata, runtime length and compatibility checks.
The call's pointer is the callee symbol recognized from the actual expression;
no alias map or expected translated body is supplied as proof evidence. -/
theorem callSite_forced_return {e : EE} {g : Sym} {number : Int}
    {loc : Loc} {attrs : Attributes} {fty : Ctype} {variadic proto : Bool} {body : EE}
    (hs : Call.callSite file e = some (g, true))
    (hinfo : file.funInfo.lookup g = some (loc, attrs, fty, [], variadic, proto))
    (hfk : Call.retKind fty = some true)
    (ordinary : libraryCall file g = none)
    (resolved : procedureBody file g [] = .ok (body, []))
    (hbody : ReturnLit.recognizeBody file body = some number)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ finish, LocationOnly m finish ∧ Forced.Reaches file labels
      ⟨.effectExpr e env, k, m⟩ ⟨.value (.loaded (.specified (.integer number))), k, finish⟩ := by
  unfold Call.callSite at hs
  split at hs
  next ann pann p pbt fann vann g' lann tann fa fty' fbt pa pty pbt' w1a w1 w2a w2 cann cpann
      p₁ iann oann lenann len lnann pty₁ zann z iann' cpa cva rty cfa fty₁ ccann mt pann₂ p₂ no1 no2 =>
    split at hs
    next cond =>
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
      let m₁ := SeqReach.focusMemory fann m
      let m₂ := SeqReach.focusMemory lann m₁
      let m₃ := SeqReach.focusMemory iann m₂
      let m₄ := SeqReach.focusMemory iann' m₃
      have callReturns : ∃ finish, LocationOnly m₄ finish ∧ Forced.Reaches file labels
          ⟨.effectExpr (.mk ccann (.ccall () mt (.mk pann₂ () (.sym p₂)) [])) env₂, k, m₄⟩
          ⟨.value (.loaded (.specified (.integer number))), k, finish⟩ :=
        ccall_forced_return ccann mt (pure_symbol pann₂ p₂ env₂ fp l4) ordinary resolved hbody k m₄
      obtain ⟨finish, location, returned⟩ := callReturns
      have beforeCall : LocationOnly m m₄ :=
        (CalleeReturn.focus_location fann m).trans
          ((CalleeReturn.focus_location lann m₁).trans
            ((CalleeReturn.focus_location iann m₂).trans (CalleeReturn.focus_location iann' m₃)))
      refine ⟨finish, beforeCall.trans location, ?_⟩
      refine (sseq_pure_reaches ann fann (pat := .mk pann (.base (some p, pbt))) (xs := [(p, fp)])
        (pure_value vann (.loaded (.specified (.pointer (.function g')))) env) rfl k m).trans ?_
      refine (effect_let_reaches lann (cfunction_forced l1 hinfo) hmatch k m₁).trans ?_
      refine (effect_if_reaches iann true (eval_forced (Call.length_eval hlen l2)) k m₂).trans ?_
      refine (effect_if_reaches iann' true (compatible_forced hrk hfk l3) k m₃).trans ?_
      exact returned
    next => cases hs
  next => cases hs

end Silmaril.Compiler.Core.CallReturn
