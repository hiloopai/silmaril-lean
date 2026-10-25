module

public import Silmaril.Wasm.V1.Execution.Instantiation

/-!
# Reduction contexts and initializer evaluation

The executable constant-expression evaluator agrees with the independent
small-step relation. Finite and infinite executions lift through evaluation
contexts; in particular, a supplied divergent host outcome is an actual
infinite reduction, rather than a stuck configuration.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution.Runtime

/-- Evaluation-context closure for arbitrary finite executions. -/
theorem Steps.context {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Steps host a b) (vs : List Value) (tail : List Admin) :
    Steps host ⟨a.store, a.frame, values vs ++ a.code ++ tail⟩
      ⟨b.store, b.frame, values vs ++ b.code ++ tail⟩ :=
  Relation.ReflTransGen.lift (p := Step host) (fun c : Config H => ⟨c.store, c.frame, values vs ++ c.code ++ tail⟩)
    (fun _ _ h => Step.context h vs tail) a b h

theorem Steps.label {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Steps host a b) (n : Nat) (cont : Expr) :
    Steps host ⟨a.store, a.frame, [.label n cont a.code]⟩
      ⟨b.store, b.frame, [.label n cont b.code]⟩ :=
  Relation.ReflTransGen.lift (p := Step host) (fun c : Config H => ⟨c.store, c.frame, [.label n cont c.code]⟩)
    (fun _ _ h => Step.label h n cont) a b h

theorem Steps.frame {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Steps host a b) (n : Nat) (outer : Frame) :
    Steps host ⟨a.store, outer, [.frame n a.frame a.code]⟩
      ⟨b.store, outer, [.frame n b.frame b.code]⟩ :=
  Relation.ReflTransGen.lift (p := Step host) (fun c : Config H => ⟨c.store, outer, [.frame n c.frame c.code]⟩)
    (fun _ _ h => Step.frame h n outer) a b h

theorem Diverges.context {H : Type*} {host : HostSemantics H} {a : Config H}
    (h : Diverges host a) (vs : List Value) (tail : List Admin) :
    Diverges host ⟨a.store, a.frame, values vs ++ a.code ++ tail⟩ :=
  InfiniteTrace.map (S := Step host)
    (fun c : Config H => ⟨c.store, c.frame, values vs ++ c.code ++ tail⟩)
    (fun _ _ step => Step.context step vs tail) h

theorem constInstr?_sound {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    {i : Instr} {v : Value} (h : constInstr? s f.module i = some v) :
    Steps host ⟨s, f, [.source i]⟩ ⟨s, f, [value v]⟩ := by
  cases i <;> simp only [constInstr?] at h
  all_goals try contradiction
  case intConst t bits => cases h; exact .refl
  case floatConst t bits => cases h; exact .refl
  case globalGet i =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a, ha, g, hg, rfl⟩ := h
    exact (Step.globalGet s f i a g ha hg).steps

theorem constInstrs?_sound {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    {es : Expr} {vs : List Value} (h : es.mapM (constInstr? s f.module) = some vs) :
    Steps host ⟨s, f, expression es⟩ ⟨s, f, values vs⟩ := by
  induction es generalizing vs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    cases h
    exact .refl
  | cons e es ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    have first := (constInstr?_sound host s f hv).context [] (expression es)
    have rest := (ih hvs).context [v] []
    simp only [values, List.map_nil, List.nil_append, List.map_cons, List.append_nil] at first rest
    simpa only [expression, List.map_cons, values, List.cons_append, List.nil_append] using first.trans rest

theorem constExpr?_sound {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    {es : Expr} {v : Value} (h : constExpr? s f.module es = some v) :
    Steps host ⟨s, f, expression es⟩ ⟨s, f, [value v]⟩ := by
  simp only [constExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vs, hvs, hv⟩ := h
  split at hv <;> simp_all
  exact constInstrs?_sound host s f hvs

theorem host_diverges {H : Type*} {host : HostSemantics H} (s : Store H) (f : Frame)
    (a : FuncAddr) (ft : FuncType) (fn : H) (args : List Value)
    (found : s.funcs[a.value]? = some (.host ft fn)) (arity : args.length = ft.params.length)
    (behavior : host fn s args .diverged) :
    Diverges host ⟨s, f, values args ++ [.invoke a]⟩ :=
  ⟨fun _ => ⟨s, f, values args ++ [.invoke a]⟩, rfl,
    fun _ => Step.invokeHostDiverges s f a ft fn args found arity behavior⟩

end Silmaril.Wasm.V1.Execution
