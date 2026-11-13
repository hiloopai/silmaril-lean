module

public import Silmaril.Wasm.Spec.Graph.Defs

@[expose] public section

/-!
# The logic graph of the specification institutions: proofs

* `SEdge.modelExpansive`: the edges marked `Expansive` (logic maps, wrapping, synchronous to
  asynchronous) are model-expansive comorphisms;
* `specGraphE_pathModelExpansive`: every path of `specGraphE` is model-expansive, hence
  `specGraphE_entails_lift_path_iff` (heterogeneous borrowing);
* `CoHom.lift_modelExpansive`, `liftGraph_pathModelExpansive`: lifting preserves this;
* `fullGraph₃_pathModelExpansive`: every path of the joined Wasm graph is model-expansive.
-/

namespace Silmaril.Wasm.Spec.Graph

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {M : Type} [Silmaril.Wasm.Component.CoreModule M]

/-- **The expansive edges are model-expansive comorphisms.** -/
theorem SEdge.modelExpansive (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) :
    ∀ {a b : SNode} (e : SEdge a b), e.Expansive → (e.coHom P C).ModelExpansive
  | _, _, .mod e s, _ => e.map.coHom_modelExpansive (s.sem P)
  | _, _, .comp e s, _ => e.map.coHom_modelExpansive (s.sem P C)
  | _, _, .async e s, _ => e.map.coHom_modelExpansive _
  | _, _, .wrap l, _ => pushCoHom_modelExpansive _ _ _ _ _
  | _, _, .sync l s, _ => pushCoHom_modelExpansive _ _ _ _ _
  | _, _, .env _, h => h.elim
  | _, _, .jointWrap _, h => h.elim
  | _, _, .jointIR _, h => h.elim

/-- **The environment edge is not model-expansive**: a program with a proper environment is not
the chaotic reading of a program. -/
theorem env_not_modelExpansive (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) (l : MLogic) :
    ¬ ((SEdge.env l).coHom P C).ModelExpansive := by
  intro h
  let X : WIface := ⟨[⟨[], []⟩], []⟩
  let Kb : EnvSpec (List Val) (Behaviour Val) X :=
    ⟨{[]}, ⟨rfl, fun ht hs => by rw [Set.mem_singleton_iff] at ht ⊢; subst ht; exact List.prefix_nil.1 hs⟩⟩
  let p : WasmProg X := ⟨[], {}⟩
  obtain ⟨N, hN⟩ := h X ⟨X, 𝟙 X, (p, Kb)⟩
  have heq := congrArg (fun N' : Model ((wasmSem P).withEnv) X => ∃ s ∈ N'.prog.2.1, s ≠ []) hN
  have h₁ : ∃ s ∈ (EnvSpec.top : EnvSpec (List Val) (Behaviour Val) N.iface).1, s ≠ [] :=
    ⟨[.ask (N.obs.imp ⟨0, Nat.zero_lt_one⟩) []], trivial, List.cons_ne_nil _ _⟩
  have h₂ : ∃ s ∈ Kb.1, s ≠ [] := heq.mp h₁
  obtain ⟨s, hs, hne⟩ := h₂
  exact hne hs

/-- **Every path of the expansive specification graph is model-expansive.** -/
theorem specGraphE_pathModelExpansive (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) :
    ∀ {a b : (specGraphE P C).Idx} (p : Quiver.Path a b), (specGraphE P C).PathModelExpansive p
  | _, _, .nil => trivial
  | _, _, .cons p e =>
    ⟨specGraphE_pathModelExpansive P C p, SEdge.modelExpansive P C e.1 e.2⟩

/-- **Heterogeneous borrowing in the specification graph**: consequence in the Grothendieck
institution of `specGraphE` is reflected along every path. -/
theorem specGraphE_entails_lift_path_iff (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M)
    {a b : (specGraphE P C).Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst (specGraphE P C).indexed ((specGraphE P C).pt a)).Sign)
    (Γ : Set ((IndexedCoInst.flat (specGraphE P C).indexed).obj
      (IndexedCoInst.mkSig (specGraphE P C).indexed ((specGraphE P C).pt a) S)).Sen)
    (φ : ((IndexedCoInst.flat (specGraphE P C).indexed).obj
      (IndexedCoInst.mkSig (specGraphE P C).indexed ((specGraphE P C).pt a) S)).Sen) :
    ((IndexedCoInst.flat (specGraphE P C).indexed).obj
        (IndexedCoInst.mkSig (specGraphE P C).indexed ((specGraphE P C).pt a) S)).Entails Γ φ ↔
      ((IndexedCoInst.flat (specGraphE P C).indexed).obj
          (IndexedCoInst.mkSig (specGraphE P C).indexed ((specGraphE P C).pt b)
            ((IndexedCoInst.coHom (specGraphE P C).indexed
              ((specGraphE P C).pathHom p)).Φ.obj S))).Entails
        (((IndexedCoInst.flat (specGraphE P C).indexed).map
            (IndexedCoInst.lift (specGraphE P C).indexed ((specGraphE P C).pathHom p) S)).sen '' Γ)
        (((IndexedCoInst.flat (specGraphE P C).indexed).map
            (IndexedCoInst.lift (specGraphE P C).indexed ((specGraphE P C).pathHom p) S)).sen φ) :=
  (specGraphE P C).entails_lift_path_iff p (specGraphE_pathModelExpansive P C p) S Γ φ

/-- A path of the graph: never-called sentences about Wasm programs, as action invariants, as
LTL over maximal behaviours. -/
noncomputable def ncToMax (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) :
    Quiver.Path (V := (specGraphE P C).Idx) (SNode.mod .neverCall .wasm) (SNode.mod .ltlMax .wasm) :=
  let e₁ : (specGraphE P C).Comor (SNode.mod .neverCall .wasm) (SNode.mod .act .wasm) :=
    ⟨.mod .ncAct .wasm, trivial⟩
  let e₂ : (specGraphE P C).Comor (SNode.mod .act .wasm) (SNode.mod .ltlMax .wasm) :=
    ⟨.mod .actMax .wasm, trivial⟩
  (Quiver.Path.nil.cons e₁).cons e₂

/-- Litmus: the composite comorphism along `ncToMax` is model-expansive. -/
theorem ncToMax_modelExpansive (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) :
    (IndexedCoInst.coHom (specGraphE P C).indexed
      ((specGraphE P C).pathHom (ncToMax P C))).ModelExpansive :=
  (specGraphE P C).modelExpansive_path _ (specGraphE_pathModelExpansive P C _)

/-- Lifting preserves model-expansiveness. -/
theorem _root_.Silmaril.Logic.Institution.Inst.CoHom.lift_modelExpansive
    {A B : Inst.{0, 0, 0, 0, 0}} {f : Inst.CoHom A B} (h : f.ModelExpansive) :
    f.lift.ModelExpansive :=
  fun S => h (ULift.down S)

/-- Paths of a lifted graph whose edges are model-expansive are model-expansive. -/
theorem liftGraph_pathModelExpansive (L : LogicGraph.{0, 0, 0, 0, 0, 0, 0})
    (hL : ∀ {a b} (e : L.Comor a b), (L.comor e).ModelExpansive) :
    ∀ {a b : (liftGraph L).Idx} (p : Quiver.Path a b), (liftGraph L).PathModelExpansive p
  | _, _, .nil => trivial
  | _, _, .cons p e => ⟨liftGraph_pathModelExpansive L hL p, Inst.CoHom.lift_modelExpansive (hL e)⟩

/-- **Every path of the joined Wasm graph is model-expansive**, so heterogeneous borrowing
applies across Core reduction semantics, games, components and the specification
institutions. -/
theorem fullGraph₃_pathModelExpansive {H : Type} (P : Profile) (host : HostSemantics H)
    (Env : Module → Store H → List ExternAddr → Prop) (C : Silmaril.Wasm.Component.CoreSem M)
    {a b : (fullGraph₃ P host Env C).Idx} (p : Quiver.Path a b) :
    (fullGraph₃ P host Env C).PathModelExpansive p :=
  Silmaril.Wasm.Institution.LogicGraph.sum_pathModelExpansive _ _ _ _
    (fun e => (Silmaril.Wasm.Institution.CompGraph.fullGraph₂_pathModelExpansive C P host Env
      (Quiver.Hom.toPath e)).2)
    (fun {a b} (e : (liftGraph (specGraphE P C)).Comor a b) =>
      Inst.CoHom.lift_modelExpansive (SEdge.modelExpansive P C e.1 e.2))
    (fun e => e.elim) p

end Silmaril.Wasm.Spec.Graph
