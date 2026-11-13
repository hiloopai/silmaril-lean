module

public import Silmaril.Wasm.Unified.Component.Core.Defs
public import Silmaril.Wasm.Institution.Games.Thms
public import Silmaril.Wasm.Institution.Components.Thms
public import Silmaril.Games.Handler.Thms

/-!
# Components over unified core modules: results

* Renaming modules and components is functorial (`UMod.map_id`, `UMod.map_comp`,
  `mapComp_id`, `mapComp_comp`, `CProg.map_id`, `CProg.map_comp`).
* **Renaming commutes with the denotation**: `denU_mapComp`: a renamed component in `C` is the
  component in the pulled-back core semantics `pullC C σ`. With `coreSem_reduct` (the core
  semantics of a reduct is the pulled-back core semantics) this gives `den_reduct` and
  `obs_reduct`: the component layer over the reduct `M|σ` is the component layer over `M` on
  renamed programs. This is the semantic half of the satisfaction condition of the component
  institution (`Silmaril.Wasm.Unified.Component.Inst`).
* `obs_core`: a core module answers a first call of export `j` exactly with the observations of
  the model on the code of `j` (two-move plays of a reduction strategy,
  `Silmaril.Wasm.Institution.Games.mem_ofReduction_ask_ans`). `obs_single`: the one-export module
  of `c` answers exactly the observations of `c`.
* `obs_core_subset_wrap`: **wrapping a module in the trivial component keeps its answers**
  (`wrapAdequate` and two-move plays through the boundary handlers). Only this direction is
  proved; the converse (the wrapper adds no answers) is open.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Wasm.Component Silmaril.Wasm.Unified
open Silmaril.Games (Strategy Handler Sig Move)

variable {S S' S'' : FSig}

/-! ## Functoriality of renaming -/

theorem UMod.map_id (m : UMod S) : m.map (𝟙 S) = m := by
  obtain ⟨I, X, c⟩ := m
  simp only [UMod.map, FSig.id_f, UInstr.mapCode_id]

theorem UMod.map_comp (σ : S ⟶ S') (τ : S' ⟶ S'') (m : UMod S) :
    m.map (σ ≫ τ) = (m.map σ).map τ := by
  obtain ⟨I, X, c⟩ := m
  simp only [UMod.map, FSig.comp_f, UInstr.mapCode_map]

mutual
theorem mapComp_id : ∀ c : Comp (UMod S), mapComp (𝟙 S) c = c
  | .mk I ns xs => by rw [mapComp, mapNodes_id ns]

theorem mapNodes_id : ∀ ns : List (Node (UMod S)), mapNodes (𝟙 S) ns = ns
  | [] => rfl
  | n :: ns => by rw [mapNodes, mapNode_id n, mapNodes_id ns]

theorem mapNode_id : ∀ n : Node (UMod S), mapNode (𝟙 S) n = n
  | .core m args => by rw [mapNode, UMod.map_id]
  | .inst c args => by rw [mapNode, mapComp_id c]
end

mutual
theorem mapComp_comp (σ : S ⟶ S') (τ : S' ⟶ S'') :
    ∀ c : Comp (UMod S), mapComp (σ ≫ τ) c = mapComp τ (mapComp σ c)
  | .mk I ns xs => by rw [mapComp, mapNodes_comp σ τ ns, mapComp, mapComp]

theorem mapNodes_comp (σ : S ⟶ S') (τ : S' ⟶ S'') :
    ∀ ns : List (Node (UMod S)), mapNodes (σ ≫ τ) ns = mapNodes τ (mapNodes σ ns)
  | [] => rfl
  | n :: ns => by rw [mapNodes, mapNode_comp σ τ n, mapNodes_comp σ τ ns, mapNodes, mapNodes]

theorem mapNode_comp (σ : S ⟶ S') (τ : S' ⟶ S'') :
    ∀ n : Node (UMod S), mapNode (σ ≫ τ) n = mapNode τ (mapNode σ n)
  | .core m args => by rw [mapNode, UMod.map_comp, mapNode, mapNode]
  | .inst c args => by rw [mapNode, mapComp_comp σ τ c, mapNode, mapNode]
end

theorem CProg.map_id (x : CProg S) : x.map (𝟙 S) = x := by
  cases x with
  | core m => exact congrArg CProg.core (UMod.map_id m)
  | comp c => exact congrArg CProg.comp (mapComp_id c)

theorem CProg.map_comp (σ : S ⟶ S') (τ : S' ⟶ S'') (x : CProg S) :
    x.map (σ ≫ τ) = (x.map σ).map τ := by
  cases x with
  | core m => exact congrArg CProg.core (UMod.map_comp σ τ m)
  | comp c => exact congrArg CProg.comp (mapComp_comp σ τ c)

/-! ## Renaming and the denotation -/

theorem width_mapNode (σ : S ⟶ S') : ∀ n : Node (UMod S), (mapNode σ n).width = n.width
  | .core _ _ => rfl
  | .inst (.mk _ _ _) _ => rfl

theorem envAfter_mapNodes (σ : S ⟶ S') :
    ∀ (e : Nat) (ns : List (Node (UMod S))), envAfter e (mapNodes σ ns) = envAfter e ns
  | _, [] => rfl
  | e, n :: ns => by rw [mapNodes, envAfter, envAfter, width_mapNode, envAfter_mapNodes σ _ ns]

mutual
/-- **A renamed component** is the component in the pulled-back core semantics. -/
theorem denU_mapComp (C : CoreSem (UMod S')) (σ : S ⟶ S') :
    ∀ c : Comp (UMod S), (mapComp σ c).denU C = c.denU (pullC C σ)
  | .mk I ns xs => by
    rw [mapComp, Comp.denU, Comp.denU, envAfter_mapNodes, denNodes_mapComp C σ I.length ns]

theorem denNodes_mapComp (C : CoreSem (UMod S')) (σ : S ⟶ S') {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (Node (UMod S))) (D : Strategy X sigU),
      denNodes C e (mapNodes σ ns) D = denNodes (pullC C σ) e ns D
  | _, [], _ => by rw [mapNodes, denNodes, denNodes]
  | e, n :: ns, D => by
    rw [mapNodes, denNodes, denNodes, width_mapNode, den_mapNode C σ e n,
      denNodes_mapComp C σ _ ns]

theorem den_mapNode (C : CoreSem (UMod S')) (σ : S ⟶ S') :
    ∀ (e : Nat) (n : Node (UMod S)), Node.den C e (mapNode σ n) = Node.den (pullC C σ) e n
  | _, .core _ _ => by rw [mapNode, Node.den, Node.den]; rfl
  | e, .inst c args => by rw [mapNode, Node.den, Node.den, denU_mapComp C σ c]
end

theorem coreRed_reduct (σ : S ⟶ S') (M : PModel S') (m : UMod S) :
    coreRed (M.reduct σ) m = coreRed M (m.map σ) := by
  have h : ∀ (j : Nat) (p : Payload),
      (M.reduct σ).obs (m.code j, p) = M.obs ((m.map σ).code j, p) :=
    fun j p => Model.obs_reduct σ M (m.code j) p
  unfold coreRed
  simp only [h]
  rfl

/-- **The core semantics of a reduct** is the pulled-back core semantics. -/
theorem coreSem_reduct (σ : S ⟶ S') (M : PModel S') :
    coreSem (M.reduct σ) = pullC (coreSem M) σ := by
  unfold coreSem pullC
  simp only [coreRed_reduct]
  rfl

/-- The strategy of a program in the reduct is that of the renamed program. -/
theorem den_reduct (σ : S ⟶ S') (M : PModel S') (x : CProg S) :
    den (M.reduct σ) x = den M (x.map σ) := by
  cases x with
  | core m => rw [den, coreSem_reduct]; rfl
  | comp c => rw [den, coreSem_reduct, CProg.map, den, denU_mapComp]

/-- **Answers in the reduct** are answers of the renamed program. -/
theorem obs_reduct (σ : S ⟶ S') (M : PModel S') (x : CProg S) (j : Nat) (p : Payload) :
    obs (M.reduct σ) (x, j, p) = obs M (x.map σ, j, p) := by
  cases x with
  | core m => rw [obs, coreSem_reduct]; rfl
  | comp c => rw [obs, coreSem_reduct, CProg.map, obs, denU_mapComp]

/-! ## Answers of core modules -/

/-- **A core module answers with the observations of the model.** -/
theorem obs_core (M : PModel S) (m : UMod S) (j : Nat) (p : Payload) :
    obs M (.core m, j, p) = {r | j < m.exports.length ∧ r ∈ M.obs (m.code j, p)} := by
  ext r
  constructor
  · rintro ⟨h, hr⟩
    obtain ⟨_, -, hd⟩ := (Silmaril.Wasm.Institution.Games.mem_ofReduction_ask_ans _).1 hr
    exact ⟨h, hd⟩
  · rintro ⟨h, hr⟩
    exact ⟨h, (Silmaril.Wasm.Institution.Games.mem_ofReduction_ask_ans _).2 ⟨(), .refl, hr⟩⟩

/-- The one-export module of `c` answers export `0` with the observations of `c`. -/
theorem obs_single (M : PModel S) (c : S.Code) (p : Payload) :
    obs M (.core (UMod.single c), 0, p) = M.obs (c, p) := by
  rw [obs_core]
  ext r
  exact ⟨fun h => h.2, fun h => ⟨Nat.zero_lt_one, h⟩⟩

/-! ## Wrapping keeps answers

Two-move plays through compositions and handlers; `two_comp`, `two_comp_upper` and the handler
case are copied from `Silmaril.Proofs.Wasm.Component.Reference.Games` (a `Proofs` module of
another topic, so not imported). -/

section TwoMove

variable {E F G : Sig.{0}}

private theorem two_comp {σ : Strategy E F} {τ : Strategy F G} {q : G.Op} {q' : F.Op}
    {a' : F.Ar q'} {a : G.Ar q} (hσ : [.inr (.ask q'), .inr (.ans q' a')] ∈ σ)
    (hτ : [.inr (.ask q), .inl (.ask q'), .inl (.ans q' a'), .inr (.ans q a)] ∈ τ) :
    ([.inr (.ask q), .inr (.ans q a)] : List (Move E G)) ∈ σ.comp τ :=
  ⟨_, hσ, _, hτ, .right _ (.sync _ (.sync _ (.right _ .nil)))⟩

private theorem two_comp_upper {σ : Strategy E F} {τ : Strategy F G} {q : G.Op} {a : G.Ar q}
    (hτ : ([.inr (.ask q), .inr (.ans q a)] : List (Move F G)) ∈ τ) :
    ([.inr (.ask q), .inr (.ans q a)] : List (Move E G)) ∈ σ.comp τ :=
  ⟨[], σ.nil_mem, _, hτ, .right _ (.right _ .nil)⟩

private theorem four_widen {n j : Nat} (h : j < n) (p : Payload) (r : Option Payload) :
    ([.inr (.ask (j, p)), .inl (.ask (⟨j, h⟩, p)), .inl (.ans (⟨j, h⟩, p) r),
      .inr (.ans (j, p) r)] : List (Move (sigN n) sigU)) ∈ Strategy.ofHandler (widenH n) := by
  have hq : widenH n (j, p) = .call (⟨j, h⟩, p) fun r => .pure r := dite_eq_left h
  exact Strategy.mem_ofHandler.mpr ⟨Silmaril.Games.Reduction.State.idle,
    .vis (.ask _) (.vis (.call hq)
      (.vis (Silmaril.Games.Reduction.Step.resume (R := (widenH n).toReduction) _ _ _ r)
        (.vis (.ret rfl) (.nil _))))⟩

end TwoMove

/-- **Wrapping a module keeps its answers**: every answer of the module `m` to a first call of
export `j` is an answer of the trivial component wrapping `m`. -/
theorem obs_core_subset_wrap (M : PModel S) (m : UMod S) (j : Nat) (p : Payload) :
    obs M (.core m, j, p) ⊆ obs M (.comp (Silmaril.Wasm.Institution.Components.wrap m), j, p) := by
  rintro r ⟨h, hr⟩
  show _ ∈ (Silmaril.Wasm.Institution.Components.wrap m).denU (coreSem M)
  rw [Silmaril.Wasm.Institution.Components.wrapAdequate (coreSem M) m]
  exact two_comp_upper (two_comp hr (four_widen h p r))

end Silmaril.Wasm.Unified.Component
