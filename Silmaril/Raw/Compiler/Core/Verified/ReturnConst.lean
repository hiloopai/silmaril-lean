module

public import Silmaril.Compiler.Core.Source.StartupReach.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # Core side: `main` returning an integer literal

`recognize doc = some n` when `doc`'s `main` is a procedure without parameters whose body
is, syntactically, a sequence of unit expressions followed by `return n` for an integer
literal `n` (directly, or through the elaborated return label: `save ret(x := n) in x`), and
the file has no global definitions. The recogniser inspects syntax only; it runs nothing.

`recognize_sound`: the Core dynamics, from the document's initial state, reaches
`halt (defined (Specified n))` with empty stdout, so `CoreBeh doc (exit (n mod 256) [])`.
The body lemmas (`skip_reaches`, `recognizeBody_reaches`) are
proved for every environment, continuation and memory; the startup is
`StartupReach.initial_reaches_body`, for every argument list and enum registration.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ReturnConst

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Spec

abbrev Reaches (file : Program) (labels : Labels) :=
  Relation.ReflTransGen (coreStep file labels)

theorem next_reaches (file : Program) (labels : Labels) (c c' : Control)
    (k k' : List Frame) (m : Mem.Concrete.State)
    (live : ∀ o, c ≠ .halt o)
    (h : request file labels ⟨c, k, m⟩ = .next c' k') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.tau, Step.respond live ?_⟩
  rw [h]
  exact Respond.next

theorem update_reaches (file : Program) (labels : Labels) (c c' : Control)
    (k k' : List Frame) (m m' : Mem.Concrete.State)
    (live : ∀ o, c ≠ .halt o)
    (h : request file labels ⟨c, k, m⟩ = .update m' c' k') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m'⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.tau, Step.respond live ?_⟩
  rw [h]
  exact Respond.update

theorem value_halts (file : Program) (labels : Labels) (v : Val)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, [], m⟩ ⟨.halt (.defined v), [], m⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.terminal (.defined v), Step.respond (by intro o; simp) ?_⟩
  change Respond m (request file labels ⟨.value v, [], m⟩) _ _
  simpa [request, requestAux, awaitsScheduling] using (Respond.end_ (mem := m) (o := .defined v))

theorem pure_value_reaches (file : Program) (labels : Labels) (ann : List Annot)
    (v : Value Codec.wireModel) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr (.mk ann () (.val v)) env, k, m⟩
      ⟨.value (runtimeValue v), k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

/-- Source locations change diagnostics but never the program's output. -/
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

theorem request_effect_pure (file : Program) (labels : Labels) (ann : List Annot)
    (p : PE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    request file labels ⟨.effectExpr (.mk ann (.pure p)) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.diagnosticLocation m.currentLocation :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.diagnosticLocation m.currentLocation :: k) := by
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr p env) (.diagnosticLocation m.currentLocation :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.diagnosticLocation m.currentLocation :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

theorem effect_pure_reaches (file : Program) (labels : Labels) (ann : List Annot)
    (p : PE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.pure p)) env, k, m⟩
      ⟨.pureExpr p env, .diagnosticLocation m.currentLocation :: k, focusMemory ann m⟩ := by
  unfold focusMemory
  split
  · rename_i loc found
    split
    · rename_i lib
      apply next_reaches <;> simp_all [request_effect_pure, focusMemory]
    · rename_i lib
      by_cases equal : loc == m.currentLocation
      · have eq : loc = m.currentLocation := by simpa using equal
        subst loc
        apply next_reaches <;> simp_all [request_effect_pure, focusMemory]
      · apply Relation.ReflTransGen.trans (b :=
          ⟨.setLocation loc (.pureExpr p env), .diagnosticLocation m.currentLocation :: k, m⟩)
        · apply next_reaches <;> simp_all [request_effect_pure, focusMemory]
        · apply update_reaches <;> simp [request, requestAux, awaitsScheduling]
  · rename_i found
    have focus : focusMemory ann m = m := by
      unfold focusMemory
      rw [found]
    apply next_reaches
    · intro o; simp
    · rw [request_effect_pure]
      simp [focus]

theorem sequence_reaches (file : Program) (labels : Labels) (ann : List Annot)
    (pat : Pattern Sym) (a b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.sseq pat a b)) env, k, m⟩
      ⟨.effectExpr a env, .strongBind pat b env :: k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

theorem diagnostic_reaches (file : Program) (labels : Labels) (loc : Loc)
    (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .diagnosticLocation loc :: k, m⟩
      ⟨.value v, k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

theorem wildcard_sequence_reaches (file : Program) (labels : Labels)
    (ann : List Annot) (ty : BaseType) (v : Val) (b : EE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .strongBind (.mk ann (.base (none, ty))) b env :: k, m⟩
      ⟨.effectExpr b env, k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling, matchPattern, extendEnv]

/-- A sequence of literal unit expressions has no effect. No calls, memory,
branches or arithmetic are silently evaluated by this predicate. -/
def skip : Expr Codec.wireModel Unit Unit Sym → Bool
  | .mk _ (.pure (.mk _ _ (.val .unit))) => true
  | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => skip a && skip b
  | _ => false

/-- No-op syntax reduces to unit in any environment and continuation,
without changing stdout, including when source locations are annotated. -/
theorem skip_reaches (file : Program) (labels : Labels) (e : EE)
    (h : skip e = true) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  unfold skip at h
  split at h
  · rename_i ann pann u
    refine ⟨focusMemory ann m, focusMemory_stdout ann m, ?_⟩
    exact (effect_pure_reaches file labels ann _ env k m).trans
      ((pure_value_reaches file labels pann .unit env _ _).trans
        (diagnostic_reaches file labels m.currentLocation .unit k _))
  · rename_i ann patann ty a b
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨m₁, out₁, ra⟩ := skip_reaches file labels a ha env
      (.strongBind (.mk patann (.base (none, ty))) b env :: k) m
    obtain ⟨m₂, out₂, rb⟩ := skip_reaches file labels b hb env k m₁
    refine ⟨m₂, out₂.trans out₁, ?_⟩
    exact (sequence_reaches file labels ann _ a b env k m).trans
      (ra.trans ((wildcard_sequence_reaches file labels patann ty .unit b env k m₁).trans rb))
  · cases h
termination_by sizeOf e

/-- Integer syntax admitted in the saved return epilogue. -/
def intLiteral : Pexpr Codec.wireModel Unit Sym → Option Int
  | .mk _ _ (.val (.loaded (.specified (.integer n)))) => some n
  | .mk _ _ (.ctor .specified [.mk _ _ (.val (.object (.integer n)))]) => some n
  | _ => none

theorem intLiteral_reaches (file : Program) (labels : Labels) (p : PE) (n : Int)
    (h : intLiteral p = some n) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr p env, k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), k, m⟩ := by
  unfold intLiteral at h
  split at h
  · cases h
    exact pure_value_reaches file labels _ _ env k m
  · rename_i ann u pann u₂ val
    cases h
    apply Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr (.mk pann () (.val (.object (.integer n)))) env,
        .arguments (.ctor .specified) [] [] env :: k, m⟩)
    · apply next_reaches <;> simp [request, requestAux, awaitsScheduling, arguments]
    · apply Relation.ReflTransGen.trans
        (pure_value_reaches file labels pann (.object (.integer n)) env _ m)
      apply Relation.ReflTransGen.trans (b := ⟨.apply (.ctor .specified) [.object (.integer n)], k, m⟩)
      · apply next_reaches <;> simp [request, requestAux, awaitsScheduling, runtimeValue, runtimeObject]
      · apply next_reaches <;> simp [request, requestAux, awaitsScheduling, primitive]
        all_goals rfl
  · cases h

theorem request_save (file : Program) (labels : Labels) (ann : List Annot)
    (label : Sym × BaseType) (s : Sym) (paramInfo : BaseType × Option (Ctype × PassBy))
    (p : PE) (body : EE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    request file labels ⟨.effectExpr (.mk ann (.save label [(s, (paramInfo, p))] body)) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.saveArguments [s] [] [] body env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.saveArguments [s] [] [] body env :: k) := by
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr p env) (.saveArguments [s] [] [] body env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.saveArguments [s] [] [] body env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

theorem save_reaches (file : Program) (labels : Labels) (ann : List Annot)
    (label : Sym × BaseType) (s : Sym) (paramInfo : BaseType × Option (Ctype × PassBy))
    (p : PE) (body : EE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.save label [(s, (paramInfo, p))] body)) env, k, m⟩
      ⟨.pureExpr p env, .saveArguments [s] [] [] body env :: k, focusMemory ann m⟩ := by
  unfold focusMemory
  split
  · rename_i loc found
    split
    · rename_i lib
      apply next_reaches <;> simp_all [request_save, focusMemory]
    · rename_i lib
      by_cases equal : loc == m.currentLocation
      · have eq : loc = m.currentLocation := by simpa using equal
        subst loc
        apply next_reaches <;> simp_all [request_save, focusMemory]
      · apply Relation.ReflTransGen.trans (b :=
          ⟨.setLocation loc (.pureExpr p env), .saveArguments [s] [] [] body env :: k, m⟩)
        · apply next_reaches <;> simp_all [request_save, focusMemory]
        · apply update_reaches <;> simp [request, requestAux, awaitsScheduling]
  · rename_i found
    have focus : focusMemory ann m = m := by
      unfold focusMemory
      rw [found]
    apply next_reaches
    · intro o; simp
    · rw [request_save]
      simp [focus]

theorem saveArgument_reaches (file : Program) (labels : Labels) (s : Sym)
    (v : Val) (body : EE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .saveArguments [s] [] [] body env :: k, m⟩
      ⟨.effectExpr body (env.insert s v), k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling, extendEnv]

theorem pure_sym_reaches (file : Program) (labels : Labels) (ann : List Annot)
    (s t : Sym) (equal : MapKey.key s = MapKey.key t) (v : Val)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr (.mk ann () (.sym t)) (env.insert s v), k, m⟩
      ⟨.value v, k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling, Map.lookup, Map.insert, equal]

/-- Recognize a literal return or the saved default-return epilogue, preceded
only by syntactic unit expressions. Keys use the same equality as Core maps. -/
def recognizeBody : Expr Codec.wireModel Unit Unit Sym → Option Int
  | .mk _ (.pure (.mk _ _ (.val (.loaded (.specified (.integer n)))))) => some n
  | .mk _ (.sseq (.mk _ (.base (none, _))) a b) =>
      if skip a then recognizeBody b else none
  | .mk _ (.save _ [(s, (_, p))] (.mk _ (.pure (.mk _ _ (.sym t))))) =>
      if MapKey.key s = MapKey.key t then intLiteral p else none
  | _ => none

/-- A recognized body returns the literal at run time from every memory,
environment and continuation, preserving stdout. -/
theorem recognizeBody_reaches (file : Program) (labels : Labels) (e : EE) (n : Int)
    (h : recognizeBody e = some n) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), k, m'⟩ := by
  unfold recognizeBody at h
  split at h
  · rename_i ann pann u val
    cases h
    refine ⟨focusMemory ann m, focusMemory_stdout ann m, ?_⟩
    exact (effect_pure_reaches file labels ann _ env k m).trans
      ((pure_value_reaches file labels pann _ env _ _).trans
        (diagnostic_reaches file labels m.currentLocation _ k _))
  · rename_i ann patann ty a b
    split at h
    · rename_i ha
      obtain ⟨m₁, out₁, ra⟩ := skip_reaches file labels a ha env
        (.strongBind (.mk patann (.base (none, ty))) b env :: k) m
      obtain ⟨m₂, out₂, rb⟩ := recognizeBody_reaches file labels b n h env k m₁
      refine ⟨m₂, out₂.trans out₁, ?_⟩
      exact (sequence_reaches file labels ann _ a b env k m).trans
        (ra.trans ((wildcard_sequence_reaches file labels patann ty .unit b env k m₁).trans rb))
    · cases h
  · rename_i ann label s paramInfo p bann pann u t
    split at h
    · rename_i equal
      let v : Val := .loaded (.specified (.integer n))
      let m₁ := focusMemory ann m
      let m₂ := focusMemory bann m₁
      refine ⟨m₂, (focusMemory_stdout bann m₁).trans (focusMemory_stdout ann m), ?_⟩
      apply Relation.ReflTransGen.trans (save_reaches file labels ann label s paramInfo p _ env k m)
      apply Relation.ReflTransGen.trans (intLiteral_reaches file labels p n h env _ m₁)
      apply Relation.ReflTransGen.trans (saveArgument_reaches file labels s v _ env k m₁)
      apply Relation.ReflTransGen.trans (effect_pure_reaches file labels bann _ (env.insert s v) k m₁)
      exact (pure_sym_reaches file labels pann s t equal v env _ m₂).trans
        (diagnostic_reaches file labels m₁.currentLocation v k m₂)
    · cases h
  · cases h
termination_by sizeOf e

/-- `main` returns an integer literal: no global definitions (no initialiser is evaluated),
`main` a procedure without parameters, and its body recognised by `recognizeBody`. -/
def recognize (doc : Codec.Document) : Option Int := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody body

theorem value_halts_annotations (file : Program) (labels : Labels) (v : Val)
    (xs : List Access) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, [.annotations xs], m⟩ ⟨.halt (.defined v), [], m⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.terminal (.defined v), Step.respond (by intro o; simp) ?_⟩
  simpa [request, requestAux, awaitsScheduling] using
    (Respond.end_ (mem := m) (o := .defined v))

/-- The whole-document run: from the initial state of the document (any arguments, any
enum registrations), the dynamics halts with `Specified n` and empty stdout. -/
theorem recognize_reaches (doc : Codec.Document) (n : Int) (h : recognize doc = some n)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels t, initial doc.file enums args = .ok (s, labels) ∧ Reaches doc.file labels s t ∧
      t.control = .halt (.defined (.loaded (.specified (.integer n)))) ∧ t.memory.stdout = "" := by
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
          have hbody : recognizeBody body = some n := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hentry⟩ := StartupReach.initial_reaches_body
            doc.file enums args hdefs main decl
          obtain ⟨m', hout', hrun⟩ := recognizeBody_reaches doc.file labels body n hbody ∅
            [.annotations xs] m
          exact ⟨s, labels, _, hinit,
            hentry.trans (hrun.trans (value_halts_annotations _ _ _ xs m')), rfl, hout'.trans hout⟩

/-- **Core side.** A recognised document exits with `n mod 256` and no output. -/
theorem recognize_sound (doc : Codec.Document) (n : Int) (h : recognize doc = some n) (args : List String) :
    CoreBeh doc args (.exit (n % 256).toNat []) := by
  obtain ⟨s, labels, t, hinit, reach, halt, out⟩ :=
    recognize_reaches doc n h (Map.ofList (doc.enumBindings.getD [])) args
  have beh := CoreBeh.exit (k := (n % 256).toNat) ⟨s, labels, hinit, reach⟩ halt rfl
  simpa [coreBytes, out] using beh

end Silmaril.Compile.Core.Verified.ReturnConst
