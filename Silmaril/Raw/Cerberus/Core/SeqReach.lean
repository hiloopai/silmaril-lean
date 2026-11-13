module

public import Silmaril.Cerberus.Core.Dynamics.Defs

/-! # Core reachability for binding, sequencing and branches

These rules use only the canonical dynamics, independently of the compiler specification.
They apply under every continuation and from every memory. `PureEval` is a semantic
premise, not a compile-time evaluator; literal values witness that it is inhabited.

Conditions are Core booleans (`true`/`false`), usually obtained by comparing the integer
inside `Specified`. `Unspecified` is a pattern constructor, not itself undefined
behaviour: only an explicit `undef` arm is shown to reach UB.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.SeqReach

open Dynamics

/-- Unlabelled reachability of the canonical Core LTS. Definitionally equal to the
reachability relations used by `StartupReach` and the verified compiler. -/
abbrev Reaches (file : Program) (labels : Labels) :=
  Relation.ReflTransGen (fun s t => ∃ a, Step file labels s a t)

/-- A pure expression computes `v`, preserving memory, under every continuation. -/
def PureEval (file : Program) (labels : Labels) (p : PE) (env : Env) (v : Val) : Prop :=
  ∀ k m, Reaches file labels ⟨.pureExpr p env, k, m⟩ ⟨.value v, k, m⟩

variable {file : Program} {labels : Labels}

theorem next_reaches {c c' : Control} {k k' : List Frame} {m : Mem.Concrete.State}
    (live : ∀ o, c ≠ .halt o)
    (h : request file labels ⟨c, k, m⟩ = .next c' k') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m⟩ := by
  exact .single ⟨.tau, Step.respond live (h ▸ Respond.next)⟩

/-- The only memory change on entry to a located expression is diagnostic location. -/
def focusMemory (ann : List Annot) (m : Mem.Concrete.State) : Mem.Concrete.State :=
  match ann.findSome? (fun a => match a with | .loc l => some l | _ => none) with
  | some l => if libraryLocation l then m else {m with currentLocation := l}
  | none => m

@[simp] theorem focusMemory_stdout (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).stdout = m.stdout := by
  unfold focusMemory
  split
  · split <;> rfl
  · rfl

theorem focusMemory_shape (ann : List Annot) (m : Mem.Concrete.State) :
    focusMemory ann m = {m with currentLocation := (focusMemory ann m).currentLocation} := by
  unfold focusMemory
  split
  · split <;> rfl
  · rfl

/-- Discharge the optional location-setting transition shared by located expressions. -/
theorem located_next_reaches (ann : List Annot) {c c' : Control}
    {k k' : List Frame} {m : Mem.Concrete.State} (live : ∀ o, c ≠ .halt o)
    (h : request file labels ⟨c, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then .next c' k'
      else .next (.setLocation (focusMemory ann m).currentLocation c') k') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', focusMemory ann m⟩ := by
  by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation
  · have heq : (focusMemory ann m).currentLocation = m.currentLocation := by simpa using eq
    have hm : focusMemory ann m = m := by rw [focusMemory_shape ann m, heq]
    rw [hm]
    exact next_reaches live (by simpa [eq] using h)
  · refine (next_reaches live (by simpa [eq] using h)).trans ?_
    apply Relation.ReflTransGen.single
    refine ⟨.tau, Step.respond (by intro o; simp) ?_⟩
    have shape := focusMemory_shape ann m
    rw [shape]
    exact (show Respond m
      (request file labels ⟨.setLocation (focusMemory ann m).currentLocation c', k', m⟩)
      .tau ⟨c', k', {m with currentLocation := (focusMemory ann m).currentLocation}⟩ from
        by simpa [request, requestAux, awaitsScheduling] using
          (Respond.update (mem := m) (c := c') (k := k')
            (m := {m with currentLocation := (focusMemory ann m).currentLocation})))

theorem pure_value (ann : List Annot) (v : Value Codec.wireModel) (env : Env) :
    PureEval file labels (.mk ann () (.val v)) env (runtimeValue v) := by
  intro k m
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

theorem pure_symbol (ann : List Annot) (sym : Sym) (env : Env) (v : Val)
    (h : env.lookup sym = some v) :
    PureEval file labels (.mk ann () (.sym sym)) env v := by
  intro k m
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling, h]

/-- Enter a pure expression under its diagnostic frame. -/
theorem effect_pure_enter (ann : List Annot) (p : PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.pure p)) env, k, m⟩
      ⟨.pureExpr p env, .diagnosticLocation m.currentLocation :: k, focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr p env) (.diagnosticLocation m.currentLocation :: k)
    else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
      (.diagnosticLocation m.currentLocation :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

/-- Lift a pure computation to an effectful expression, including its location frame. -/
theorem effect_pure_reaches (ann : List Annot) {p : PE} {env : Env} {v : Val}
    (hp : PureEval file labels p env v) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.pure p)) env, k, m⟩
      ⟨.value v, k, focusMemory ann m⟩ := by
  refine (effect_pure_enter ann p env k m).trans ((hp _ _).trans ?_)
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

theorem pure_let_reaches (ann : List Annot) {pat : Pattern Sym} {p body : PE}
    {env : Env} {v : Val} {xs : Bindings} (hp : PureEval file labels p env v)
    (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr (.mk ann () (.let_ pat p body)) env, k, m⟩
      ⟨.pureExpr body (extendEnv xs env), k, m⟩ := by
  refine Relation.ReflTransGen.trans (b := ⟨.pureExpr p env, .pureBind pat body env :: k, m⟩) ?_ ?_
  · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
  · refine (hp _ _).trans ?_
    apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hm]

theorem effect_bind_reaches {pat : Pattern Sym} {body : EE} {env : Env} {v : Val}
    {xs : Bindings} (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .effectBind pat body env :: k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hm]

theorem strong_bind_reaches {pat : Pattern Sym} {body : EE} {env : Env} {v : Val}
    {xs : Bindings} (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .strongBind pat body env :: k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hm]

theorem effect_let_reaches (ann : List Annot) {pat : Pattern Sym} {p : PE} {body : EE}
    {env : Env} {v : Val} {xs : Bindings} (hp : PureEval file labels p env v)
    (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.let_ pat p body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory ann m⟩ := by
  refine Relation.ReflTransGen.trans (b :=
    ⟨.pureExpr p env, .effectBind pat body env :: k, focusMemory ann m⟩) ?_ ?_
  · apply located_next_reaches ann (by intro o; simp)
    simp only [request, requestAux, awaitsScheduling]
    change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
      Request.next (.pureExpr p env) (.effectBind pat body env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectBind pat body env :: k)) with
      | .next (.jumping s vs env) k => jump labels s vs env k
      | r => r) = _
    by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]
  · exact (hp _ _).trans (effect_bind_reaches hm k _)

/-- Strong sequencing composes a first computation with the displayed continuation;
its resulting memory is passed to the body. -/
theorem sseq_reaches (ann : List Annot) {pat : Pattern Sym} {a body : EE}
    {env : Env} {v : Val} {xs : Bindings} {k : List Frame} {m m' : Mem.Concrete.State}
    (ha : Reaches file labels ⟨.effectExpr a env, .strongBind pat body env :: k, m⟩
      ⟨.value v, .strongBind pat body env :: k, m'⟩)
    (hm : matchPattern pat v = some xs) :
    Reaches file labels ⟨.effectExpr (.mk ann (.sseq pat a body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, m'⟩ := by
  refine Relation.ReflTransGen.trans (b :=
    ⟨.effectExpr a env, .strongBind pat body env :: k, m⟩) ?_
      (ha.trans (strong_bind_reaches hm k m'))
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

/-- Weak sequencing uses its own continuation and also passes on the resulting memory. -/
theorem wseq_reaches (ann : List Annot) {pat : Pattern Sym} {a body : EE}
    {env : Env} {v : Val} {xs : Bindings} {k : List Frame} {m m' : Mem.Concrete.State}
    (ha : Reaches file labels ⟨.effectExpr a env, .effectBind pat body env :: k, m⟩
      ⟨.value v, .effectBind pat body env :: k, m'⟩)
    (hm : matchPattern pat v = some xs) :
    Reaches file labels ⟨.effectExpr (.mk ann (.wseq pat a body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, m'⟩ := by
  refine Relation.ReflTransGen.trans (b :=
    ⟨.effectExpr a env, .effectBind pat body env :: k, m⟩) ?_
      (ha.trans (effect_bind_reaches hm k m'))
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

theorem sseq_pure_reaches (ann firstAnn : List Annot) {pat : Pattern Sym} {p : PE} {body : EE}
    {env : Env} {v : Val} {xs : Bindings} (hp : PureEval file labels p env v)
    (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.sseq pat (.mk firstAnn (.pure p)) body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory firstAnn m⟩ :=
  sseq_reaches ann (effect_pure_reaches firstAnn hp _ _) hm

theorem wseq_pure_reaches (ann firstAnn : List Annot) {pat : Pattern Sym} {p : PE} {body : EE}
    {env : Env} {v : Val} {xs : Bindings} (hp : PureEval file labels p env v)
    (hm : matchPattern pat v = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.wseq pat (.mk firstAnn (.pure p)) body)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory firstAnn m⟩ :=
  wseq_reaches ann (effect_pure_reaches firstAnn hp _ _) hm

theorem pure_if_reaches (ann : List Annot) {p yes no : PE} {env : Env} (b : Bool)
    (hp : PureEval file labels p env (boolean b)) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr (.mk ann () (.if_ p yes no)) env, k, m⟩
      ⟨.pureExpr (if b then yes else no) env, k, m⟩ := by
  refine Relation.ReflTransGen.trans (b := ⟨.pureExpr p env, .pureIf yes no env :: k, m⟩) ?_ ?_
  · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
  · refine (hp _ _).trans ?_
    cases b <;> apply next_reaches <;> simp [request, requestAux, awaitsScheduling, boolean]

theorem effect_if_reaches (ann : List Annot) {p : PE} {yes no : EE} {env : Env} (b : Bool)
    (hp : PureEval file labels p env (boolean b)) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.if_ p yes no)) env, k, m⟩
      ⟨.effectExpr (if b then yes else no) env, k, focusMemory ann m⟩ := by
  refine Relation.ReflTransGen.trans (b :=
    ⟨.pureExpr p env, .effectIf yes no env :: k, focusMemory ann m⟩) ?_ ?_
  · apply located_next_reaches ann (by intro o; simp)
    simp only [request, requestAux, awaitsScheduling]
    change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
      Request.next (.pureExpr p env) (.effectIf yes no env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectIf yes no env :: k)) with
      | .next (.jumping s vs env) k => jump labels s vs env k
      | r => r) = _
    by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]
  · refine (hp _ _).trans ?_
    cases b <;> apply next_reaches <;> simp [request, requestAux, awaitsScheduling, boolean]

theorem pure_case_reaches (ann : List Annot) {p body : PE} {bs : List (Pattern Sym × PE)}
    {env : Env} {v : Val} {xs : Bindings} (hp : PureEval file labels p env v)
    (hm : selectCase v bs = some (xs, body)) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr (.mk ann () (.case_ p bs)) env, k, m⟩
      ⟨.pureExpr body (extendEnv xs env), k, m⟩ := by
  refine Relation.ReflTransGen.trans (b := ⟨.pureExpr p env, .pureCase bs env :: k, m⟩) ?_ ?_
  · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
  · refine (hp _ _).trans ?_
    apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hm]

theorem effect_case_reaches (ann : List Annot) {p : PE} {body : EE} {bs : List (Pattern Sym × EE)}
    {env : Env} {v : Val} {xs : Bindings} (hp : PureEval file labels p env v)
    (hm : selectCase v bs = some (xs, body)) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.case_ p bs)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory ann m⟩ := by
  refine Relation.ReflTransGen.trans (b :=
    ⟨.pureExpr p env, .effectCase bs env :: k, focusMemory ann m⟩) ?_ ?_
  · apply located_next_reaches ann (by intro o; simp)
    simp only [request, requestAux, awaitsScheduling]
    change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
      Request.next (.pureExpr p env) (.effectCase bs env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.effectCase bs env :: k)) with
      | .next (.jumping s vs env) k => jump labels s vs env k
      | r => r) = _
    by_cases eq : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]
  · refine (hp _ _).trans ?_
    apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hm]

/-- The usual two-arm case selects `Specified` and binds its object value. -/
theorem select_specified {α : Type} (sa ua : List Annot) (sp up : Pattern Sym)
    (yes no : α) (v : ObjectValue Mem.Concrete.model) {xs : Bindings}
    (hm : matchPattern sp (.object v) = some xs) :
    selectCase (.loaded (.specified v))
      [(.mk sa (.ctor .specified [sp]), yes), (.mk ua (.ctor .unspecified [up]), no)] =
        some (xs, yes) := by
  simp [selectCase, matchPattern, hm]

/-- `Unspecified` skips the `Specified` arm and binds its C type. -/
theorem select_unspecified {α : Type} (sa ua : List Annot) (sp up : Pattern Sym)
    (yes no : α) (ty : Ctype) {xs : Bindings}
    (hm : matchPattern up (.ctype ty) = some xs) :
    selectCase (.loaded (.unspecified ty))
      [(.mk sa (.ctor .specified [sp]), yes), (.mk ua (.ctor .unspecified [up]), no)] =
        some (xs, no) := by
  simp [selectCase, matchPattern, hm]

theorem specified_case_reaches (ann sa ua : List Annot) (sp up : Pattern Sym)
    {p : PE} {yes no : EE} {env : Env} {v : ObjectValue Mem.Concrete.model} {xs : Bindings}
    (hp : PureEval file labels p env (.loaded (.specified v)))
    (hm : matchPattern sp (.object v) = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.case_ p
      [(.mk sa (.ctor .specified [sp]), yes), (.mk ua (.ctor .unspecified [up]), no)])) env, k, m⟩
      ⟨.effectExpr yes (extendEnv xs env), k, focusMemory ann m⟩ :=
  effect_case_reaches ann hp (select_specified sa ua sp up yes no v hm) k m

theorem unspecified_case_reaches (ann sa ua : List Annot) (sp up : Pattern Sym)
    {p : PE} {yes no : EE} {env : Env} {ty : Ctype} {xs : Bindings}
    (hp : PureEval file labels p env (.loaded (.unspecified ty)))
    (hm : matchPattern up (.ctype ty) = some xs) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.case_ p
      [(.mk sa (.ctor .specified [sp]), yes), (.mk ua (.ctor .unspecified [up]), no)])) env, k, m⟩
      ⟨.effectExpr no (extendEnv xs env), k, focusMemory ann m⟩ :=
  effect_case_reaches ann hp (select_unspecified sa ua sp up yes no ty hm) k m

/-- An explicit pure `undef` ends in UB, discarding the continuation. -/
theorem pure_undef_reaches (ann : List Annot) (loc : Loc) (ub : UndefinedBehaviour)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr (.mk ann () (.undef loc ub)) env, k, m⟩
      ⟨.halt (.ub loc ub), [], m⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.terminal (.ub loc ub), Step.respond (by intro o; simp) ?_⟩
  simpa [request, requestAux, awaitsScheduling] using
    (Respond.end_ (mem := m) (o := .ub loc ub))

theorem effect_undef_reaches (ann pann : List Annot) (loc : Loc) (ub : UndefinedBehaviour)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.pure (.mk pann () (.undef loc ub)))) env, k, m⟩
      ⟨.halt (.ub loc ub), [], focusMemory ann m⟩ :=
  (effect_pure_enter ann _ env k m).trans (pure_undef_reaches pann loc ub env _ _)

/-- The usual unspecified UB arm really reaches the canonical UB outcome. The arbitrary
behaviour allowance belongs to the compiler specification, not the Core step relation. -/
theorem unspecified_undef_reaches (ann sa ua armAnn pann : List Annot) (sp up : Pattern Sym)
    {p : PE} {yes : EE} {env : Env} {ty : Ctype} {xs : Bindings}
    (hp : PureEval file labels p env (.loaded (.unspecified ty)))
    (hm : matchPattern up (.ctype ty) = some xs) (loc : Loc) (ub : UndefinedBehaviour)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.case_ p
      [(.mk sa (.ctor .specified [sp]), yes),
       (.mk ua (.ctor .unspecified [up]), .mk armAnn (.pure (.mk pann () (.undef loc ub))))])) env, k, m⟩
      ⟨.halt (.ub loc ub), [], focusMemory armAnn (focusMemory ann m)⟩ :=
  (unspecified_case_reaches ann sa ua sp up hp hm k m).trans
    (effect_undef_reaches armAnn pann loc ub _ k _)

/-- Compositional pure evaluation rules, suitable for use by a proved folder. -/
theorem PureEval.let_ (ann : List Annot) {pat : Pattern Sym} {p body : PE} {env : Env}
    {v result : Val} {xs : Bindings} (hp : PureEval file labels p env v)
    (hm : matchPattern pat v = some xs) (hb : PureEval file labels body (extendEnv xs env) result) :
    PureEval file labels (.mk ann () (.let_ pat p body)) env result := by
  intro k m
  exact (pure_let_reaches ann hp hm k m).trans (hb k m)

theorem PureEval.if_ (ann : List Annot) {p yes no : PE} {env : Env} {result : Val} (b : Bool)
    (hp : PureEval file labels p env (boolean b))
    (hb : PureEval file labels (if b then yes else no) env result) :
    PureEval file labels (.mk ann () (.if_ p yes no)) env result := by
  intro k m
  exact (pure_if_reaches ann b hp k m).trans (hb k m)

theorem PureEval.case_ (ann : List Annot) {p body : PE} {bs : List (Pattern Sym × PE)}
    {env : Env} {v result : Val} {xs : Bindings} (hp : PureEval file labels p env v)
    (hm : selectCase v bs = some (xs, body))
    (hb : PureEval file labels body (extendEnv xs env) result) :
    PureEval file labels (.mk ann () (.case_ p bs)) env result := by
  intro k m
  exact (pure_case_reaches ann hp hm k m).trans (hb k m)

end Silmaril.Cerberus.Core.SeqReach
