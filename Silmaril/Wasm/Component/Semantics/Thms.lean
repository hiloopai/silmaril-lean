module

public import Silmaril.Wasm.Component.Semantics.Defs
public import Silmaril.Wasm.Component.Adapter.Thms

/-!
# The component semantics: basic theorems

* `denNodes_comp`: the environment construction commutes with composition
  below it (associativity of `Strategy.comp`); so a component whose imports
  are served by a strategy `B` is `denNodes` started from `B`.
* `denU_mapImpls`: rewriting wiring programs into programs with the same
  meaning does not change the denotation (at any nesting depth). Adapter
  fusion is an instance.
* `Linked.denU_toComponent`: the flat IR is a sub-IR of the nested one.
* Monotonicity in the core semantics: `denU_mono`. If every core module's
  strategy is refined, so is every component.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

variable {M : Type} [CoreModule M]

/-- Composition below an environment construction. -/
theorem denNodes_comp (C : CoreSem M) {X Y : Sig.{0}} (B : Strategy X Y) :
    ∀ (e : Nat) (ns : List (Node M)) (D : Strategy Y sigU),
      B.comp (denNodes C e ns D) = denNodes C e ns (B.comp D)
  | _, [], _ => by simp only [denNodes]
  | e, n :: ns, D => by
    simp only [denNodes]
    rw [denNodes_comp C B _ ns, ext, ext, Strategy.comp_assoc]

/-- `implsH` only depends on the programs of the `Impl`s. -/
theorem implsH_map {f : Impl → Impl} (hf : ∀ e im, (f im).prog e = im.prog e) (e : Nat)
    (ims : List Impl) : implsH e (ims.map f) = implsH e ims := by
  funext q
  unfold implsH
  rw [List.getElem?_map]
  rcases ims[q.1]? with _ | im
  · rfl
  · exact congrFun (hf e im) q.2

theorem implsN_map {f : Impl → Impl} (hf : ∀ e im, (f im).prog e = im.prog e) (e : Nat)
    (ims : List Impl) (t : Nat) : implsN e (ims.map f) t = implsN e ims t := by
  funext q
  exact congrFun (implsH_map hf e ims) _

theorem exportsH_map {f : Impl → Impl} (hf : ∀ e im, (f im).prog e = im.prog e) (e : Nat)
    (xs : List Export) : exportsH e (xs.map fun x => { x with impl := f x.impl }) = exportsH e xs := by
  simp only [exportsH, List.map_map]
  exact implsH_map (f := f) hf e (xs.map Export.impl) ▸ by simp [Function.comp_def]

theorem width_mapImplsNode (f : Impl → Impl) :
    ∀ n : Node M, (Comp.mapImplsNode f n).width = n.width
  | .core _ _ => rfl
  | .inst (.mk _ _ xs) _ => by
    simp [Comp.mapImplsNode, Comp.mapImpls, Node.width]

theorem envAfter_mapImplsNodes (f : Impl → Impl) :
    ∀ (e : Nat) (ns : List (Node M)), envAfter e (Comp.mapImplsNodes f ns) = envAfter e ns
  | _, [] => by simp only [Comp.mapImplsNodes]
  | e, n :: ns => by
    simp only [Comp.mapImplsNodes, envAfter, width_mapImplsNode,
      envAfter_mapImplsNodes f _ ns]

mutual
/-- Rewriting wiring programs by programs with the same meaning preserves the
denotation. -/
theorem denU_mapImpls (C : CoreSem M) {f : Impl → Impl}
    (hf : ∀ e im, (f im).prog e = im.prog e) :
    ∀ c : Comp M, (Comp.mapImpls f c).denU C = c.denU C
  | .mk I ns xs => by
    simp only [Comp.mapImpls, Comp.denU, exportsH_map hf, envAfter_mapImplsNodes,
      denNodes_mapImpls C hf I.length ns]

theorem denNodes_mapImpls (C : CoreSem M) {f : Impl → Impl}
    (hf : ∀ e im, (f im).prog e = im.prog e)
    {X : Sig.{0}} : ∀ (e : Nat) (ns : List (Node M)) (D : Strategy X sigU),
      denNodes C e (Comp.mapImplsNodes f ns) D = denNodes C e ns D
  | _, [], _ => by simp only [Comp.mapImplsNodes, denNodes]
  | e, n :: ns, D => by
    simp only [Comp.mapImplsNodes, denNodes, width_mapImplsNode, den_mapImplsNode C hf e n,
      denNodes_mapImpls C hf _ ns]

theorem den_mapImplsNode (C : CoreSem M) {f : Impl → Impl}
    (hf : ∀ e im, (f im).prog e = im.prog e) :
    ∀ (e : Nat) (n : Node M), (Comp.mapImplsNode f n).den C e = n.den C e
  | e, .core m args => by
    simp only [Comp.mapImplsNode, Node.den, coreNode, implsN_map hf]
  | e, .inst c args => by
    simp only [Comp.mapImplsNode, Node.den, implsH_map hf, denU_mapImpls C hf c]
end

/-- The typed denotation of `mapImpls`, at the same interface sizes. -/
theorem den_mapImpls (C : CoreSem M) {f : Impl → Impl} (hf : ∀ e im, (f im).prog e = im.prog e)
    (c : Comp M) (n k : Nat) :
    atSizes n k ((Comp.mapImpls f c).denU C) = atSizes n k (c.denU C) := by
  rw [denU_mapImpls C hf]

theorem Linked.denNodes_map (C : CoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (M × List Impl)) (D : Strategy X sigU),
      denNodes C e (ns.map fun n => .core n.1 n.2) D = Linked.denU.go C e ns D
  | _, [], _ => by simp only [List.map_nil, denNodes, Linked.denU.go]
  | e, n :: ns, D => by
    simp only [List.map_cons, denNodes, Linked.denU.go, Node.width, Node.den]
    exact Linked.denNodes_map C _ ns _

theorem Linked.envAfter_map :
    ∀ (e : Nat) (ns : List (M × List Impl)),
      envAfter e (ns.map fun n => (.core n.1 n.2 : Node M)) = linkedEnv e ns
  | _, [] => rfl
  | _, _ :: ns => Linked.envAfter_map _ ns

/-- The flat IR denotes as its embedding into the nested IR. -/
theorem Linked.denU_toComponent (C : CoreSem M) (l : Linked M) :
    l.toComponent.denU C = l.denU C := by
  obtain ⟨I, ns, xs⟩ := l
  simp only [Linked.toComponent, Comp.denU, Linked.denU, Linked.denNodes_map,
    Linked.envAfter_map]

/-! ## Monotonicity in the core semantics -/

/-- Pointwise refinement of core semantics. -/
def CoreSem.Le (C C' : CoreSem M) : Prop := ∀ m, C.sem m ≤ C'.sem m

theorem ext_mono {X : Sig.{0}} (e : Nat) {D D' : Strategy X sigU} {N N' : Strategy sigU sigU}
    (hD : D ≤ D') (hN : N ≤ N') : ext e D N ≤ ext e D' N' :=
  Strategy.comp_mono hD (Strategy.comp_mono (Strategy.pair_mono le_rfl hN) le_rfl)

mutual
/-- Refining the core semantics refines every component. -/
theorem denU_mono {C C' : CoreSem M} (h : C.Le C') :
    ∀ c : Comp M, c.denU C ≤ c.denU C'
  | .mk I ns xs => by
    simp only [Comp.denU]
    exact Strategy.comp_mono (denNodes_mono h I.length ns le_rfl) le_rfl

theorem denNodes_mono {C C' : CoreSem M} (h : C.Le C') {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (Node M)) {D D' : Strategy X sigU}, D ≤ D' →
      denNodes C e ns D ≤ denNodes C' e ns D'
  | _, [], _, _, hD => by simpa only [denNodes] using hD
  | e, n :: ns, _, _, hD => by
    simp only [denNodes]
    exact denNodes_mono h _ ns (ext_mono e hD (den_mono h e n))

theorem den_mono {C C' : CoreSem M} (h : C.Le C') :
    ∀ (e : Nat) (n : Node M), n.den C e ≤ n.den C' e
  | e, .core m args => by
    simp only [Node.den, coreNode]
    exact Strategy.comp_mono le_rfl (Strategy.comp_mono (h m) le_rfl)
  | e, .inst c args => by
    simp only [Node.den]
    exact Strategy.comp_mono le_rfl (denU_mono h c)
end

end Silmaril.Wasm.Component
