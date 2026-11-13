module

public import Silmaril.Cerberus.Core.SeqReach.Defs
public import Silmaril.Foundations.InfiniteTrace

/-! # Saved-label transfers in the canonical Core dynamics

`run` is a nonlocal transfer: it discards local continuation frames and uses
the nearest procedure's labels. Arguments are evaluated before any parameter
is rebound. These rules preserve the entire memory, including stdout.

The `run` entry rules below use unannotated effect syntax; pure operands may
have arbitrary annotations. `save_enter` handles arbitrary source locations.
The divergence rule constructs an actual infinite LTS trace, without fuel.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.LoopReach

open Dynamics SeqReach

variable {file : Program} {labels : Labels}

/-- Resolving a label uses the selected procedure context and checks arity. -/
theorem jump_resolves {s : Sym} {vs : List Val} {env : Env}
    {k retained : List Frame} {localLabels : Labels} {params : List Sym} {body : EE}
    (context : procedureContext labels k = (localLabels, retained))
    (lookup : localLabels.lookup s = some (params, body))
    (arity : params.length = vs.length) :
    jump labels s vs env k =
      .next (.effectExpr body (extendEnv (params.zip vs) env)) retained := by
  simp [jump, jumpDestination, context, lookup, arity]

/-- The outer request normalizes a pending jump even without a boundary. -/
theorem normalize_jump {s : Sym} {vs : List Val} {env : Env}
    {k retained : List Frame} {localLabels : Labels} {params : List Sym} {body : EE}
    (context : procedureContext labels k = (localLabels, retained))
    (lookup : localLabels.lookup s = some (params, body))
    (arity : params.length = vs.length) :
    (match requestJump labels s vs env k with
      | .next (.jumping t ws e) frames => jump labels t ws e frames
      | r => r) =
        .next (.effectExpr body (extendEnv (params.zip vs) env)) retained := by
  have resolved := jump_resolves context lookup arity (env := env)
  by_cases boundary : hasBoundary k = true <;> simp [requestJump, boundary, resolved]

/-- A zero-argument transfer drops the intervening continuation frames. -/
theorem run_nil_step (s : Sym) (env : Env) (k retained : List Frame)
    (m : Mem.Concrete.State) (localLabels : Labels) (body : EE)
    (context : procedureContext labels k = (localLabels, retained))
    (lookup : localLabels.lookup s = some ([], body)) :
    ∃ a, Step file labels ⟨.effectExpr (.mk [] (.run () s [])) env, k, m⟩ a
      ⟨.effectExpr body env, retained, m⟩ := by
  refine ⟨.tau, Step.respond (by intro o; simp) ?_⟩
  have resolved := jump_resolves (vs := []) context lookup rfl (env := env)
  have req : request file labels
      ⟨.effectExpr (.mk [] (.run () s [])) env, k, m⟩ = .next (.effectExpr body env) retained := by
    by_cases boundary : hasBoundary k = true <;>
      simp [request, requestAux, awaitsScheduling, requestJump, boundary, resolved, extendEnv]
  rw [req]
  exact Respond.next

/-- Finish evaluating a run's operands, then bind parameters simultaneously. -/
theorem run_arguments_reaches {s : Sym} {env : Env} {ps : List PE} {values : List Val}
    (evaluates : List.Forall₂ (fun p v => PureEval file labels p env v) ps values)
    (acc : List Val) (v : Val) (k retained : List Frame) (m : Mem.Concrete.State)
    (localLabels : Labels) (params : List Sym) (body : EE)
    (context : procedureContext labels k = (localLabels, retained))
    (lookup : localLabels.lookup s = some (params, body))
    (arity : params.length = (acc ++ v :: values).length) :
    Reaches file labels ⟨.value v, .runLabel s acc ps env :: k, m⟩
      ⟨.effectExpr body (extendEnv (params.zip (acc ++ v :: values)) env), retained, m⟩ := by
  induction evaluates generalizing acc v with
  | nil =>
    apply next_reaches (by intro o; simp)
    have resolved := jump_resolves context lookup arity (env := env)
    by_cases boundary : hasBoundary k = true <;>
      simp [request, requestAux, awaitsScheduling, requestJump, boundary, resolved]
  | @cons p w ps ws head tail ih =>
    refine Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr p env, .runLabel s (acc ++ [v]) ps env :: k, m⟩) ?_ ?_
    · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
    · refine (head _ _).trans ?_
      simpa [List.append_assoc] using
        ih (acc ++ [v]) w (by simpa [List.append_assoc] using arity)

/-- Transfer with any number of pure operands. The semantic premises do not
evaluate the source at compile time and may describe runtime computations. -/
theorem run_reaches (s : Sym) (env : Env) (ps : List PE) (values : List Val)
    (evaluates : List.Forall₂ (fun p v => PureEval file labels p env v) ps values)
    (k retained : List Frame) (m : Mem.Concrete.State) (localLabels : Labels)
    (params : List Sym) (body : EE)
    (context : procedureContext labels k = (localLabels, retained))
    (lookup : localLabels.lookup s = some (params, body))
    (arity : params.length = values.length) :
    Reaches file labels ⟨.effectExpr (.mk [] (.run () s ps)) env, k, m⟩
      ⟨.effectExpr body (extendEnv (params.zip values) env), retained, m⟩ := by
  cases evaluates with
  | nil =>
    have hp : params = [] := List.eq_nil_of_length_eq_zero arity
    subst params
    simpa [extendEnv] using
      (Relation.ReflTransGen.single (run_nil_step s env k retained m localLabels body context lookup))
  | @cons p v ps vs head tail =>
    refine Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr p env, .runLabel s [] ps env :: k, m⟩) ?_ ?_
    · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
    · exact (head _ _).trans
        (run_arguments_reaches tail [] v k retained m localLabels params body context lookup arity)

/-- Entering a save with no parameters falls through to its body. Labels are
collected from the procedure syntax, rather than installed by this step. -/
theorem save_enter (ann : List Annot) (label : Sym × BaseType) (body : EE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.save label [] body)) env, k, m⟩
      ⟨.effectExpr body env, k, focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
      Request.next (.effectExpr body env) k
    else .next (.setLocation (focusMemory ann m).currentLocation (.effectExpr body env)) k) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

/-- Save initializers, like run operands, all use the original environment. -/
theorem save_arguments_reaches {env : Env} {ps : List PE} {values : List Val}
    (evaluates : List.Forall₂ (fun p v => PureEval file labels p env v) ps values)
    (syms : List Sym) (acc : List Val) (v : Val) (body : EE)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .saveArguments syms acc ps body env :: k, m⟩
      ⟨.effectExpr body (extendEnv (syms.zip (acc ++ v :: values)) env), k, m⟩ := by
  induction evaluates generalizing acc v with
  | nil => apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
  | @cons p w ps ws head tail ih =>
    refine Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr p env, .saveArguments syms (acc ++ [v]) ps body env :: k, m⟩) ?_ ?_
    · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
    · simpa [List.append_assoc] using (head _ _).trans (ih (acc ++ [v]) w)

/-- Enter the first initializer of a save, retaining its remaining operands. -/
theorem save_nonempty_enter (ann : List Annot) (label : Sym × BaseType)
    (sym : Sym) (info : BaseType × Option (Ctype × PassBy)) (p : PE)
    (rest : List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE)))
    (body : EE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.save label ((sym, (info, p)) :: rest) body)) env, k, m⟩
      ⟨.pureExpr p env,
        .saveArguments (sym :: rest.map Prod.fst) [] (rest.map (fun x => x.2.2)) body env :: k,
        focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling, List.map_cons]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
      Request.next (.pureExpr p env)
        (.saveArguments (sym :: rest.map Prod.fst) [] (rest.map (fun x => x.2.2)) body env :: k)
    else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.saveArguments (sym :: rest.map Prod.fst) [] (rest.map (fun x => x.2.2)) body env :: k)) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

/-- A save with any number of pure initializers binds its parameters and
falls through to its body, preserving memory apart from diagnostic location. -/
theorem save_reaches (ann : List Annot) (label : Sym × BaseType)
    (parameters : List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE)))
    (body : EE) (env : Env) (values : List Val)
    (evaluates : List.Forall₂ (fun p v => PureEval file labels p env v)
      (parameters.map (fun x => x.2.2)) values)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.save label parameters body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv ((parameters.map Prod.fst).zip values) env),
        k, focusMemory ann m⟩ := by
  cases parameters with
  | nil =>
    cases evaluates
    simpa [extendEnv] using save_enter ann label body env k m
  | cons param rest =>
    rcases param with ⟨sym, info, p⟩
    cases evaluates with
    | cons head tail =>
      exact (save_nonempty_enter ann label sym info p rest body env k m).trans
        ((head _ _).trans (save_arguments_reaches tail _ [] _ body k _))

/-- Productive iteration of a state invariant gives a genuine infinite
trace. Requiring a nonempty path rules out zero-step stuttering. -/
theorem iterations_diverge (invariant : State → Prop)
    (iteration : ∀ s, invariant s → ∃ t,
      Relation.TransGen (fun a b => ∃ l, Step file labels a l b) s t ∧ invariant t)
    {start : State} (initial : invariant start) :
    InfiniteTrace (fun a b => ∃ l, Step file labels a l b) start := by
  refine InfiniteTrace.coinduct (fun s => ∃ t, invariant t ∧ Reaches file labels s t)
    ?_ ⟨start, initial, .refl⟩
  rintro s ⟨t, valid, path⟩
  rcases Relation.ReflTransGen.cases_head path with rfl | ⟨u, step, rest⟩
  · obtain ⟨t', path', valid'⟩ := iteration s valid
    obtain ⟨u, step, rest⟩ := Relation.TransGen.head'_iff.mp path'
    exact ⟨u, step, t', valid', rest⟩
  · exact ⟨u, step, t, valid, rest⟩

/-- A saved zero-argument back edge has an infinite trace, provided its
procedure boundary and environment remain the same on reentry. -/
theorem self_run_diverges (s : Sym) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) (localLabels : Labels)
    (context : procedureContext labels k = (localLabels, k))
    (lookup : localLabels.lookup s = some ([], .mk [] (.run () s []))) :
    InfiniteTrace (fun a b => ∃ l, Step file labels a l b)
      ⟨.effectExpr (.mk [] (.run () s [])) env, k, m⟩ := by
  refine ⟨fun _ => ⟨.effectExpr (.mk [] (.run () s [])) env, k, m⟩, rfl, ?_⟩
  intro n
  exact run_nil_step s env k k m localLabels _ context lookup

end Silmaril.Cerberus.Core.LoopReach
