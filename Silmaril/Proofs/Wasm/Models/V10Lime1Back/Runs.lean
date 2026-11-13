module

public import Silmaril.Proofs.Wasm.Models.V10Lime1Back.Step

/-!
# Backward simulation of runs, and the converse on `Store1` points

* `Step.ungate`: a step under the gated host is a step under the host;
* `HostKeepsV1 src`: the 1.0 host keeps the store's functions; from `HostKeepsL` of the
  transported host (`hostKeepsV1_of`), as the domain of `v10own` provides;
* `Step.funcs_eq`: so 1.0 steps keep functions, and `Store1` is invariant;
* `steps_back`, `diverges_back`: Lime1 runs and infinite traces from the image of a `Store1`
  1.0 configuration, under the transported host, are images of 1.0 runs and traces;
* **`behaviours_back`**: at a point of the domain of `v10own` whose store is `Store1`, the Lime1
  behaviours of `ptL p` are 1.0 behaviours of `p`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Lime1Back

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution (codeToLime)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V10Lime1Back
open Silmaril.Wasm.Models.V10 (LStore LHost HostKeepsL)

variable {H : Type}

/-- The constructors of a Lime1 step that do not consult the host: rebuild the step. -/
local macro "ungate_step" : tactic => `(tactic|
  first
    | (apply Silmaril.Wasm.Lime1.Execution.Step.pure ; assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.localGet ; assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.localSet <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.globalGet <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.globalSet <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.call ; assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.callIndirect <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.callIndirectBounds <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.callIndirectNull <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.callIndirectType <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.invokeWasm <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.intLoad <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.intLoadTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.floatLoad <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.floatLoadTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.intStore <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.intStoreTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.floatStore <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.floatStoreTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memorySize <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryGrow <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryCopy <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryCopyTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryFill <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryFillTrap <;> assumption))

/-- A step under the gated host is a step under the host. -/
theorem Step.ungate {src : LHost H} {a b : Silmaril.Wasm.Lime1.Execution.Config H}
    (h : Silmaril.Wasm.Lime1.Execution.Step (V10Lime1.gate src) a b) :
    Silmaril.Wasm.Lime1.Execution.Step src a b := by
  induction h with
  | context _ vs tail ih => exact .context ih vs tail
  | label _ n cont ih => exact .label ih n cont
  | frame _ n outer ih => exact .frame ih n outer
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact .invokeHost s s' f a ft fn args r found arity behavior.1
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact .invokeHostDiverges s f a ft fn args found arity behavior.1
  | _ => ungate_step

/-- The 1.0 host keeps the store's functions. -/
def HostKeepsV1 (src : V10.OHost H) : Prop :=
  ∀ h s vs s' r, src h s vs (.returned s' r) → s'.funcs = s.funcs

/-- `HostKeepsL` of the transported host gives `HostKeepsV1`. -/
theorem hostKeepsV1_of {src : V10.OHost H}
    (hk : HostKeepsL (src.mapCode Silmaril.Wasm.V1.Func.toLime)) : HostKeepsV1 src := by
  intro h s vs s' r hs
  have himg : (s'.mapCode Silmaril.Wasm.V1.Func.toLime).funcs =
      (s.mapCode Silmaril.Wasm.V1.Func.toLime).funcs :=
    hk h _ vs _ r (HostSemantics.compatible_mapCode _ src h s vs _ hs)
  exact List.map_injective_iff.mpr funcInst_injective himg

/-- 1.0 steps keep the store's functions. -/
theorem Step.funcs_eq {src : V10.OHost H} (hk : HostKeepsV1 src)
    {a b : Silmaril.Wasm.V1.Execution.Config H} (h : Silmaril.Wasm.V1.Execution.Step src a b) :
    b.store.funcs = a.store.funcs := by
  induction h with
  | context _ _ _ ih => exact ih
  | label _ _ _ ih => exact ih
  | frame _ _ _ ih => exact ih
  | invokeHost s s' f a ft fn args r found arity behavior => exact hk _ _ _ _ _ behavior
  | _ => rfl

/-- `Store1` is invariant along 1.0 steps. -/
theorem Step.store1 {src : V10.OHost H} (hk : HostKeepsV1 src)
    {a b : Silmaril.Wasm.V1.Execution.Config H} (h : Silmaril.Wasm.V1.Execution.Step src a b)
    (ha : Store1 a.store) : Store1 b.store := by
  intro ft m fn hmem
  rw [Step.funcs_eq hk h] at hmem
  exact ha ft m fn hmem

/-- **Lime1 runs from an image are images of 1.0 runs.** -/
theorem steps_back {src : V10.OHost H} (hk : HostKeepsV1 src)
    {a : Silmaril.Wasm.V1.Execution.Config H} (ha : Store1 a.store)
    {c' : Silmaril.Wasm.Lime1.Execution.Config H}
    (h : Silmaril.Wasm.Lime1.Execution.Steps (src.mapCode Silmaril.Wasm.V1.Func.toLime)
      a.toLime c') :
    ∃ b, Silmaril.Wasm.V1.Execution.Steps src a b ∧ Store1 b.store ∧ c' = b.toLime := by
  induction h with
  | refl => exact ⟨a, .refl, ha, rfl⟩
  | tail _ step ih =>
    obtain ⟨b, hrun, hb, rfl⟩ := ih
    obtain ⟨b₂, hstep, rfl⟩ := stepBack src b _ hb step
    exact ⟨b₂, hrun.tail hstep, Step.store1 hk hstep hb, rfl⟩

/-- **Lime1 infinite traces from an image are images of 1.0 traces.** -/
theorem diverges_back {src : V10.OHost H} (hk : HostKeepsV1 src)
    {a : Silmaril.Wasm.V1.Execution.Config H} (ha : Store1 a.store)
    (h : Silmaril.Wasm.Lime1.Execution.Diverges (src.mapCode Silmaril.Wasm.V1.Func.toLime)
      a.toLime) :
    Silmaril.Wasm.V1.Execution.Diverges src a := by
  refine InfiniteTrace.coinduct
    (fun x => Store1 x.store ∧ Silmaril.Wasm.Lime1.Execution.Diverges
      (src.mapCode Silmaril.Wasm.V1.Func.toLime) x.toLime) ?_ ⟨ha, h⟩
  rintro x ⟨hx, hdiv⟩
  obtain ⟨d, step, hd⟩ := hdiv.unfold
  obtain ⟨b, hstep, rfl⟩ := stepBack src x d hx step
  exact ⟨b, hstep, Step.store1 hk hstep hx, hd⟩

/-- A configuration whose image is a result is a result. -/
theorem result_back {A : List VAdmin} {r : Result}
    (h : codeToLime A = Silmaril.Wasm.Lime1.Execution.result r) :
    A = Silmaril.Wasm.V1.Execution.result r := by
  cases r with
  | values vs => exact code_values.mp h
  | trap =>
    obtain ⟨x, A', rfl, hx, hA'⟩ := code_cons.mp h
    rw [map_trap.mp hx, code_nil.mp hA']
    rfl

/-- Finite runs under the gated host are runs under the host. -/
theorem Steps.ungate {src : LHost H} {a b : Silmaril.Wasm.Lime1.Execution.Config H}
    (h : Silmaril.Wasm.Lime1.Execution.Steps (V10Lime1.gate src) a b) :
    Silmaril.Wasm.Lime1.Execution.Steps src a b := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Step.ungate step)

/-- Infinite traces under the gated host are traces under the host. -/
theorem Diverges.ungate {src : LHost H} {a : Silmaril.Wasm.Lime1.Execution.Config H}
    (h : Silmaril.Wasm.Lime1.Execution.Diverges (V10Lime1.gate src) a) :
    Silmaril.Wasm.Lime1.Execution.Diverges src a :=
  InfiniteTrace.map id (fun _ _ => Step.ungate) h

/-- **On `Store1` points of the domain, Lime1 behaviours of the image are 1.0 behaviours.** -/
theorem behaviours_back {p : V10.Pt H} (hp : V10.dom p) (h₁ : Store1 p.1) (a : FuncAddr)
    (vs : List Value) :
    Lime1Core.behavioursL (V10Lime1.ptL p).2 (V10Lime1.ptL p).1 a vs ⊆
      Silmaril.Wasm.V1.Execution.behaviours p.2 p.1 a vs := by
  have hk : HostKeepsV1 p.2 := hostKeepsV1_of hp.2.2.1
  have hinv : Lime1Core.invokeL (V10Lime1.ptL p).1 a vs =
      (Silmaril.Wasm.V1.Execution.invoke p.1 a vs).toLime :=
    (Silmaril.Proofs.Wasm.Models.V10Lime1.invoke_toLime p.1 a vs).symm
  rintro _ (⟨c', r, hrun, hres, rfl⟩ | ⟨rfl, hdiv⟩)
  · rw [hinv] at hrun
    obtain ⟨b, hb, -, rfl⟩ := steps_back hk h₁ (Steps.ungate hrun)
    exact Or.inl ⟨b, r, hb, result_back hres, rfl⟩
  · rw [hinv] at hdiv
    exact Or.inr ⟨rfl, diverges_back hk h₁ (Diverges.ungate hdiv)⟩

end Silmaril.Proofs.Wasm.Models.V10Lime1Back
