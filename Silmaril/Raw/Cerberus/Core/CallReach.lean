module

public import Silmaril.Cerberus.Core.LoopReach.Defs

/-! # Procedure calls in the canonical Core dynamics

Calls evaluate operands in the caller environment, bind the resulting values
simultaneously, and suspend the caller below a procedure-return frame. In C's
elaboration the values bound to parameters are pointers to argument objects;
dispatch itself neither allocates nor copies those objects. The rules here
preserve arbitrary caller frames and permit arbitrary memory effects in the body.
They do not change the compiler or its accepted fragment.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.CallReach

open Dynamics SeqReach

variable {file : Program} {labels : Labels}

/-- Calls are explicit scheduling points, even outside an operand arena. -/
theorem scheduled_reaches {c c' : Control} {k k' : List Frame}
    {choices : List (Control × List Frame)} {m : Mem.Concrete.State}
    (live : ∀ o, c ≠ .halt o)
    (h : request file labels ⟨c, k, m⟩ = .scheduled choices)
    (member : (c', k') ∈ choices) :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m⟩ :=
  .single ⟨.tau, Step.respond live (h ▸ Respond.scheduled member)⟩

/-- The label arena installed by procedure dispatch. -/
def bodyLabels (body : EE) : Labels := Map.ofList (saves body).reverse

/-- Ordinary file procedures are selected when std.core has no entry. -/
theorem procedure_body {s : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType}
    {params : List (Sym × BaseType)} {body : EE} {values : List Val}
    (stdlib : file.stdlib.lookup s = none)
    (decl : file.funs.lookup s = some (.procedure loc marker ty params body))
    (arity : params.length = values.length) :
    procedureBody file s values = .ok (body, (params.map Prod.fst).zip values) := by
  simp [procedureBody, stdlib, decl, arity, pure, Except.pure]

/-- A std.core procedure body shadows the ordinary function table. -/
theorem stdlib_procedure_body {s : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType}
    {params : List (Sym × BaseType)} {body : EE} {values : List Val}
    (decl : file.stdlib.lookup s = some (.procedure loc marker ty params body))
    (arity : params.length = values.length) :
    procedureBody file s values = .ok (body, (params.map Prod.fst).zip values) := by
  simp [procedureBody, decl, arity, pure, Except.pure]

/-- A defined procedure takes precedence over the library builtins. -/
theorem procedure_not_builtin {s : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType}
    {params : List (Sym × BaseType)} {body : EE}
    (decl : file.funs.lookup s = some (.procedure loc marker ty params body)) :
    libraryCall file s = none := by
  simp [libraryCall, decl]

/-- Finish a left-to-right operand list under its original environment. -/
theorem arguments_reaches {ps : List PE} {values : List Val} {env : Env}
    (evaluates : List.Forall₂ (fun p v => PureEval file labels p env v) ps values)
    (op : Prim) (acc : List Val) (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .arguments op acc ps env :: k, m⟩
      ⟨.apply op (acc ++ v :: values), k, m⟩ := by
  induction evaluates generalizing acc v with
  | nil => apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
  | @cons p w ps ws head tail ih =>
    refine Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr p env, .arguments op (acc ++ [v]) ps env :: k, m⟩) ?_ ?_
    · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
    · simpa [List.append_assoc] using (head _ _).trans (ih (acc ++ [v]) w)

/-- Both call forms enter the resolved body with parameter bindings over the
caller environment and a fresh callee label arena. -/
theorem dispatch_reaches (direct : Bool) {s : Sym} {args : List Val}
    {body : EE} {bindings : Bindings}
    (ordinary : libraryCall file s = none)
    (resolved : procedureBody file s args = .ok (body, bindings))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.apply (if direct then .directProcedure env else .procedure env)
        (.loaded (.specified (.pointer (.function s))) :: args), k, m⟩
      ⟨.effectExpr body (extendEnv bindings env), .procedureReturn (bodyLabels body) :: k, m⟩ := by
  cases direct with
  | false =>
    apply scheduled_reaches (choices :=
      [(.effectExpr body (extendEnv bindings env), .procedureReturn (bodyLabels body) :: k)])
      (by intro o; simp)
    · simp [request, requestAux, awaitsScheduling, scheduledRequest, ordinary, resolved, bodyLabels]
    · simp
  | true =>
    apply next_reaches <;>
      simp [request, requestAux, awaitsScheduling, ordinary, resolved, bodyLabels]

/-- Enter an indirect call, including its diagnostic source location.
The first Core operand is type metadata and is not evaluated by dispatch. -/
theorem ccall_enter (ann : List Annot) (metadata target : PE) (ps : List PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.ccall () metadata target ps)) env, k, m⟩
      ⟨.pureExpr target env, .arguments (.procedure env) [] ps env :: k, focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr target env) (.arguments (.procedure env) [] ps env :: k)
    else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr target env))
      (.arguments (.procedure env) [] ps env :: k)) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

/-- A `ccall` reaches the body after computing its function pointer and operands. -/
theorem ccall_reaches (ann : List Annot) (metadata : PE) {target : PE}
    {ps : List PE} {args : List Val} {s : Sym} {body : EE} {bindings : Bindings} {env : Env}
    (target_eval : PureEval file labels target env (.loaded (.specified (.pointer (.function s)))))
    (args_eval : List.Forall₂ (fun p v => PureEval file labels p env v) ps args)
    (ordinary : libraryCall file s = none)
    (resolved : procedureBody file s args = .ok (body, bindings))
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.ccall () metadata target ps)) env, k, m⟩
      ⟨.effectExpr body (extendEnv bindings env),
        .procedureReturn (bodyLabels body) :: k, focusMemory ann m⟩ := by
  exact (ccall_enter ann metadata target ps env k m).trans
    ((target_eval _ _).trans ((arguments_reaches args_eval (.procedure env) [] _ k _).trans
      (dispatch_reaches false ordinary resolved env k _)))

/-- Direct `proc` calls evaluate the same operands, using a literal function pointer. -/
theorem proc_reaches {s : Sym} {ps : List PE} {args : List Val}
    {body : EE} {bindings : Bindings} {env : Env}
    (args_eval : List.Forall₂ (fun p v => PureEval file labels p env v) ps args)
    (ordinary : libraryCall file s = none)
    (resolved : procedureBody file s args = .ok (body, bindings))
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk [] (.proc () (.sym s) ps)) env, k, m⟩
      ⟨.effectExpr body (extendEnv bindings env), .procedureReturn (bodyLabels body) :: k, m⟩ := by
  refine Relation.ReflTransGen.trans (b :=
    ⟨.pureExpr (.mk [] () (.val (.loaded (.specified (.pointer (.function s)))))) env,
      .arguments (.directProcedure env) [] ps env :: k, m⟩) ?_ ?_
  · apply next_reaches <;> simp [request, requestAux, awaitsScheduling, arguments]
  · exact (pure_value [] (.loaded (.specified (.pointer (.function s)))) env _ _).trans
      ((arguments_reaches args_eval (.directProcedure env) [] _ k m).trans
        (dispatch_reaches true ordinary resolved env k m))

/-- A procedure value pops exactly one frame and resumes the suspended caller. -/
theorem return_reaches (v : Val) (localLabels : Labels) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .procedureReturn localLabels :: k, m⟩ ⟨.value v, k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

/-- A `run ret(...)` drops local frames, enters the saved return body, and
returns its result to the caller. Body effects are retained in the final memory. -/
theorem run_return_reaches (ret : Sym) (env : Env) (ps : List PE) (values : List Val)
    (evaluates : List.Forall₂ (fun p v => PureEval file labels p env v) ps values)
    (localFrames caller : List Frame) (localLabels : Labels) (params : List Sym) (body : EE)
    (m m' : Mem.Concrete.State) (v : Val)
    (context : procedureContext labels (localFrames ++ .procedureReturn localLabels :: caller) =
      (localLabels, .procedureReturn localLabels :: caller))
    (lookup : localLabels.lookup ret = some (params, body))
    (arity : params.length = values.length)
    (body_reaches : Reaches file labels
      ⟨.effectExpr body (extendEnv (params.zip values) env), .procedureReturn localLabels :: caller, m⟩
      ⟨.value v, .procedureReturn localLabels :: caller, m'⟩) :
    Reaches file labels
      ⟨.effectExpr (.mk [] (.run () ret ps)) env, localFrames ++ .procedureReturn localLabels :: caller, m⟩
      ⟨.value v, caller, m'⟩ :=
  (LoopReach.run_reaches ret env ps values evaluates _ _ m localLabels params body context lookup arity).trans
    (body_reaches.trans (return_reaches v localLabels caller m'))

/-- The usual saved return label is `ret(result) = pure(result)`. This
specialization discharges the return body's execution rather than assuming it. -/
theorem run_saved_value (ret result : Sym) (env : Env) (p : PE) (v : Val)
    (evaluates : PureEval file labels p env v)
    (localFrames caller : List Frame) (localLabels : Labels) (m : Mem.Concrete.State)
    (context : procedureContext labels (localFrames ++ .procedureReturn localLabels :: caller) =
      (localLabels, .procedureReturn localLabels :: caller))
    (lookup : localLabels.lookup ret = some
      ([result], .mk [] (.pure (.mk [] () (.sym result))))) :
    Reaches file labels
      ⟨.effectExpr (.mk [] (.run () ret [p])) env,
        localFrames ++ .procedureReturn localLabels :: caller, m⟩
      ⟨.value v, caller, m⟩ := by
  apply run_return_reaches ret env [p] [v] (.cons evaluates .nil)
    localFrames caller localLabels [result] _ m m v context lookup rfl
  simpa [focusMemory] using (effect_pure_reaches []
    (pure_symbol [] result (extendEnv ([result].zip [v]) env) v (by simp [extendEnv])) _ m)

/-- Compose an indirect call with its body's execution and return. The
semantic body premise may change all memory, including allocations and stdout. -/
theorem ccall_returns (ann : List Annot) (metadata : PE) {target : PE}
    {ps : List PE} {args : List Val} {s : Sym} {body : EE} {bindings : Bindings} {env : Env}
    (target_eval : PureEval file labels target env (.loaded (.specified (.pointer (.function s)))))
    (args_eval : List.Forall₂ (fun p v => PureEval file labels p env v) ps args)
    (ordinary : libraryCall file s = none)
    (resolved : procedureBody file s args = .ok (body, bindings))
    (k : List Frame) (m m' : Mem.Concrete.State) (v : Val)
    (body_reaches : Reaches file labels
      ⟨.effectExpr body (extendEnv bindings env), .procedureReturn (bodyLabels body) :: k, focusMemory ann m⟩
      ⟨.value v, .procedureReturn (bodyLabels body) :: k, m'⟩) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.ccall () metadata target ps)) env, k, m⟩ ⟨.value v, k, m'⟩ :=
  (ccall_reaches ann metadata target_eval args_eval ordinary resolved k m).trans
    (body_reaches.trans (return_reaches v (bodyLabels body) k m'))

/-- Direct calls have the same compositional return rule. -/
theorem proc_returns {s : Sym} {ps : List PE} {args : List Val}
    {body : EE} {bindings : Bindings} {env : Env}
    (args_eval : List.Forall₂ (fun p v => PureEval file labels p env v) ps args)
    (ordinary : libraryCall file s = none)
    (resolved : procedureBody file s args = .ok (body, bindings))
    (k : List Frame) (m m' : Mem.Concrete.State) (v : Val)
    (body_reaches : Reaches file labels
      ⟨.effectExpr body (extendEnv bindings env), .procedureReturn (bodyLabels body) :: k, m⟩
      ⟨.value v, .procedureReturn (bodyLabels body) :: k, m'⟩) :
    Reaches file labels ⟨.effectExpr (.mk [] (.proc () (.sym s) ps)) env, k, m⟩ ⟨.value v, k, m'⟩ :=
  (proc_reaches args_eval ordinary resolved k m).trans
    (body_reaches.trans (return_reaches v (bodyLabels body) k m'))

/-- A failed resolution terminates with the dynamics' error; it is not UB. -/
theorem dispatch_error (direct : Bool) {s : Sym} {args : List Val} {o : Outcome}
    (ordinary : libraryCall file s = none) (failed : procedureBody file s args = .error o)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.apply (if direct then .directProcedure env else .procedure env)
        (.loaded (.specified (.pointer (.function s))) :: args), k, m⟩
      ⟨.halt o, [], m⟩ := by
  have raised : Reaches file labels ⟨.raise o, [], m⟩ ⟨.halt o, [], m⟩ := by
    apply Relation.ReflTransGen.single
    refine ⟨.terminal o, Step.respond (by intro o; simp) ?_⟩
    simpa [request, requestAux, awaitsScheduling] using (Respond.end_ (mem := m) (o := o))
  cases direct with
  | false =>
    refine Relation.ReflTransGen.trans (b := ⟨.raise o, [], m⟩) ?_ raised
    apply scheduled_reaches (choices := [(.raise o, [])]) (by intro o; simp)
    · simp [request, requestAux, awaitsScheduling, scheduledRequest, ordinary, failed]
    · simp
  | true =>
    apply Relation.ReflTransGen.single
    refine ⟨.terminal o, Step.respond (by intro o; simp) ?_⟩
    simpa [request, requestAux, awaitsScheduling, ordinary, failed] using
      (Respond.end_ (mem := m) (o := o))

/-- Failed resolution also propagates from a complete source call, after
operand evaluation and the call's scheduling point. -/
theorem ccall_error (ann : List Annot) (metadata : PE) {target : PE}
    {ps : List PE} {args : List Val} {s : Sym} {o : Outcome} {env : Env}
    (target_eval : PureEval file labels target env (.loaded (.specified (.pointer (.function s)))))
    (args_eval : List.Forall₂ (fun p v => PureEval file labels p env v) ps args)
    (ordinary : libraryCall file s = none)
    (failed : procedureBody file s args = .error o)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.ccall () metadata target ps)) env, k, m⟩
      ⟨.halt o, [], focusMemory ann m⟩ :=
  (ccall_enter ann metadata target ps env k m).trans
    ((target_eval _ _).trans ((arguments_reaches args_eval (.procedure env) [] _ k _).trans
      (dispatch_error false ordinary failed env k _)))

/-- Named symbols absent from both procedure tables have the canonical error. -/
theorem unknown_procedure (digest : Digest) (n : Nat) (name : String) (args : List Val)
    (stdlib : file.stdlib.lookup (.mk digest n (.id name)) = none)
    (funs : file.funs.lookup (.mk digest n (.id name)) = none) :
    procedureBody file (.mk digest n (.id name)) args = .error (.error
      s!"ill-formed program: `calling an unknown procedure: Symbol({n}, SD_Id(\"{batchEscape name}\"))'") := by
  simp [procedureBody, stdlib, funs]; rfl

end Silmaril.Cerberus.Core.CallReach
