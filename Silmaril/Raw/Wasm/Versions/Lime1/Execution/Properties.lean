module

public import Silmaril.Wasm.Lime1.Execution.Step

/-! # Lime1 evaluation contexts and divergence

Finite runs and infinite traces lift through administrative evaluation contexts.
Explicit cycle witnesses distinguish divergence from absence of a finite result.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Execution

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

/-- A finite first step preserves subsequent divergence. -/
theorem Step.diverges {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) (hd : Diverges host b) : Diverges host a :=
  InfiniteTrace.fold h hd

/-- A two-state reduction cycle is an actual infinite trace. -/
theorem Step.twoCycle_diverges {H : Type*} {host : HostSemantics H} {a b : Config H}
    (hab : Step host a b) (hba : Step host b a) : Diverges host a := by
  refine ⟨fun n => if n % 2 = 0 then a else b, by simp, ?_⟩
  intro n
  by_cases h : n % 2 = 0
  · have hn : (n + 1) % 2 ≠ 0 := by omega
    simpa [h, hn] using hab
  · have hn : (n + 1) % 2 = 0 := by omega
    simpa [h, hn] using hba

theorem host_diverges {H : Type*} {host : HostSemantics H} (s : Store H) (f : Frame)
    (a : FuncAddr) (ft : FuncType) (fn : H) (args : List Value)
    (found : s.funcs[a.value]? = some (.host ft fn)) (arity : args.length = ft.params.length)
    (behavior : host fn s args .diverged) :
    Diverges host ⟨s, f, values args ++ [.invoke a]⟩ :=
  ⟨fun _ => ⟨s, f, values args ++ [.invoke a]⟩, rfl,
    fun _ => Step.invokeHostDiverges s f a ft fn args found arity behavior⟩

end Silmaril.Wasm.Lime1.Execution
