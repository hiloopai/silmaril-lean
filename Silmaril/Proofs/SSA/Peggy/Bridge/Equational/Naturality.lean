module

public import Silmaril.SSA.Peggy.Bridge.Equational.Compiler

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Equational.Proofs

open CategoryTheory Silmaril.Logic.Algebraic
open RVSDG (Tuple)

set_option backward.isDefEq.respectTransparency false

variable {S : Type} {A B : ManySorted.Signature S} {k n : Nat} {Γ : Fin k → S}
variable {rows : Fin n → Occurrence A Γ} {i : Fin n} {s : S}

private def mapRow (f : A ⟶ B) (r : Occurrence A Γ) : Occurrence B Γ :=
  ⟨r.1, ManySorted.Term.map f r.2⟩

private def mapWiring (f : A ⟶ B) {t : ManySorted.Term A Γ s} (w : Wiring rows i t) :
    Wiring (mapRow f ∘ rows) i (ManySorted.Term.map f t) :=
  match t with
  | .var v => .var v
  | .app op args => .app (f.operations op) (fun j => ManySorted.Term.map f (args j)) fun j =>
    let c := w.children j
    ⟨c.id, c.after, congrArg (mapRow f) c.term_eq⟩

private def mapNumbered (f : A ⟶ B) {t : ManySorted.Term A Γ s} (code : Numbered t) :
    Numbered (ManySorted.Term.map f t) :=
  ⟨code.tailSize, mapRow f ∘ code.rows, congrArg (mapRow f) code.root, fun i => mapWiring f (code.wiring i)⟩

private def ids {t : ManySorted.Term A Γ s} (w : Wiring rows i t) : List (Fin n) :=
  match t with
  | .var _ => []
  | .app _ _ => List.ofFn (fun j => (w.children j).id)

private theorem ids_map (f : A ⟶ B) {t : ManySorted.Term A Γ s} (w : Wiring rows i t) :
    ids (mapWiring f w) = ids w := by cases t <;> rfl

private theorem ids_cast {a b : Occurrence A Γ} (h : a = b) (wire : Wiring rows i a.2) :
    ids (h ▸ wire : Wiring rows i b.2) = ids wire := by cases h; rfl

private theorem ids_lift {arity : Nat} {inputs : Fin arity → S}
    {args : ∀ j, ManySorted.Term A Γ (inputs j)} (head : Occurrence A Γ)
    (subs : ∀ j, Numbered (args j)) (j : Fin arity) {i : Fin ((subs j).tailSize + 1)}
    {t : ManySorted.Term A Γ s} (w : Wiring (subs j).rows i t) :
    ids (Numbered.liftWiring head subs j w) = (ids w).map (Numbered.embed subs j) := by
  cases t with
  | var => rfl
  | app => simp [ids, Numbered.liftWiring, Wiring.app, List.map_ofFn, Function.comp_def]

private theorem child_eq {t : Occurrence A Γ} (a b : Child rows i t) (h : a.id = b.id) : a = b := by
  cases a; cases b; cases h; rfl

private theorem wire_eq {t : ManySorted.Term A Γ s} (a b : Wiring rows i t)
    (h : ids a = ids b) : a = b := by
  cases t with
  | var =>
    rcases a with ⟨⟨⟩⟩
    rcases b with ⟨⟨⟩⟩
    rfl
  | app op args =>
    have same := List.ofFn_inj.mp h
    exact congrArg Wiring.mk (funext (fun j => child_eq _ _ (congrFun same j)))

private theorem wires_heq {rs rt : Fin n → Occurrence A Γ} (h : rs = rt)
    (ws : ∀ j, Wiring rs j (rs j).2) (wt : ∀ j, Wiring rt j (rt j).2)
    (hs : ∀ j, ids (ws j) = ids (wt j)) : HEq ws wt := by
  subst rt
  exact heq_of_eq (funext (fun j => wire_eq _ _ (hs j)))

private theorem numbered_ext {t : ManySorted.Term A Γ s} (a b : Numbered t)
    (hsize : a.tailSize = b.tailSize) (hrows : HEq a.rows b.rows)
    (hwires : HEq a.wiring b.wiring) : a = b := by
  cases a; cases b; cases hsize; cases hrows; cases hwires; rfl

private theorem map_app (f : A ⟶ B) {arity : Nat} {inputs : Fin arity → S}
    {args : ∀ j, ManySorted.Term A Γ (inputs j)} (op : A.operations arity inputs s)
    (subs : ∀ j, Numbered (args j)) :
    mapNumbered f (Numbered.app op subs) =
      Numbered.app (f.operations op) (fun j => mapNumbered f (subs j)) := by
  let a := mapNumbered f (Numbered.app op subs)
  let mapped := fun j => mapNumbered f (subs j)
  let b := Numbered.app (f.operations op) mapped
  have rows_eq : a.rows = b.rows := by
    funext i
    refine Numbered.casesRow subs (fun i => a.rows i = b.rows i) rfl (fun j i => ?_) i
    exact (congrArg (mapRow f) (Numbered.appRows_embed ⟨s, .app op args⟩ subs j i)).trans
      (Numbered.appRows_embed ⟨s, .app (f.operations op) (fun j => ManySorted.Term.map f (args j))⟩
        (fun j => mapNumbered f (subs j)) j i).symm
  refine numbered_ext a b rfl (heq_of_eq rows_eq) (wires_heq rows_eq _ _ (fun i => ?_))
  refine Numbered.casesRow subs (fun i => ids (a.wiring i) = ids (b.wiring i)) rfl (fun j i => ?_) i
  have left : ids (a.wiring (Numbered.embed subs j i)) =
      (ids ((subs j).wiring i)).map (Numbered.embed subs j) := by
    dsimp only [a, mapNumbered, Numbered.app]
    simp only [ids_map, Numbered.casesRow_embed, ids_cast, ids_lift]
  have right : ids (b.wiring (Numbered.embed mapped j i)) =
      (ids ((subs j).wiring i)).map (Numbered.embed subs j) := by
    dsimp only [b, Numbered.app]
    simp only [Numbered.casesRow_embed, ids_cast, ids_lift]
    exact congrArg (List.map (Numbered.embed subs j)) (ids_map f ((subs j).wiring i))
  exact left.trans right.symm

private theorem compile_map (f : A ⟶ B) (t : ManySorted.Term A Γ s) :
    Numbered.compile (ManySorted.Term.map f t) = mapNumbered f (Numbered.compile t) := by
  induction t with
  | var v => rfl
  | app op args ih =>
    change Numbered.app (f.operations op) (fun j => Numbered.compile (ManySorted.Term.map f (args j))) =
      mapNumbered f (Numbered.app op (fun j => Numbered.compile (args j)))
    rw [map_app f]
    exact congrArg (Numbered.app (f.operations op)) (funext ih)

private theorem ref_reindex_refl {out : PEG.Ty S} {sort : Fin n → PEG.Ty S}
    (r : PEG.Ref sort out) : r.reindex (Equiv.refl _) = r := by cases r; rfl

private theorem pack_reindex {arity : Nat} (w : Fin arity → S) {sort : Fin n → PEG.Ty S}
    (f : ∀ j, PEG.Ref sort (.data (w j))) :
    (pack w f).map (fun _ r => r.reindex (Equiv.refl _)) = pack w f := by
  induction arity with
  | zero => rfl
  | succ arity ih =>
    exact congrArg₂ (fun head tail => Tuple.cons head tail)
      (ref_reindex_refl (f 0)) (ih (w ∘ Fin.succ) (fun i => f i.succ))

private theorem node_map (f : A ⟶ B) {t : ManySorted.Term A Γ s} (w : Wiring rows i t) :
    (mapWiring f w).node = w.node.relabel (mapOpcode f) (Equiv.refl _) id := by
  cases t with
  | var v => rfl
  | @app arity inputs out op args =>
    exact congrArg (fun args => PEG.Node.ofLabel
      (PEG.Label.op (Opcode.app (f.operations op)) :
        PEG.Label (Opcode B) (profile Γ) (Fin 0) (profile inputs) (.data s)) args)
      (pack_reindex inputs (fun j => (w.children j).ref)).symm

theorem graph_map (f : A ⟶ B) (t : ManySorted.Term A Γ s) :
    HEq (Numbered.compile (ManySorted.Term.map f t)).graph
      ((Numbered.compile t).graph.mapOps (mapOpcode f)) := by
  rw [compile_map]
  apply heq_of_eq
  let code := Numbered.compile t
  have forest : (code.graph.mapOps (mapOpcode f)).forest = emptyForest :=
    congrArg PEG.Graph.forest code.graph.mapOps_id
  change PEG.Graph.mk emptyForest _ _ _ =
    PEG.Graph.mk (code.graph.mapOps (mapOpcode f)).forest _ _ _
  rw [forest]
  exact congrArg (fun nodes => PEG.Graph.mk emptyForest (rowSort code.rows) nodes
    ((code.graph.mapOps (mapOpcode f)).roots)) (funext fun i => node_map f (code.wiring i))

theorem size_map (f : A ⟶ B) (t : ManySorted.Term A Γ s) :
    (Numbered.compile (ManySorted.Term.map f t)).tailSize = (Numbered.compile t).tailSize := by
  rw [compile_map]; rfl

end Silmaril.SSA.Peggy.Bridge.Equational.Proofs
