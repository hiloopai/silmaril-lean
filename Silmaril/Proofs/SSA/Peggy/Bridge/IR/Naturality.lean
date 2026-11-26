module

public import Silmaril.SSA.Peggy.Bridge.IR.Defs
public import Silmaril.SSA.PEG.Bridge.MLIR.Thms
public import Silmaril.SSA.RVSDG.MLIR.Regionless.Thms

public section

namespace Silmaril.SSA.Peggy.Bridge.IR.Proofs

open CategoryTheory
open Dialect (FixedSortSignature)
open PEG.Bridge
open Silmaril.SSA.RVSDG (Port Tuple Wires)
open Silmaril.SSA.RVSDG.MLIR
open PEG.Bridge.Compiler

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {P Q : PEG.InstructionSet.{0,0} Data}
variable {params results ts : List (PEG.Ty Data)} {n k : Nat}
variable {past : List (List (ValuePort Data))}
variable {S T U : FixedSortSignature.{0,0} Data}

private def mapLowered (f : PEG.InstructionMap P Q) {out : PEG.Ty Data}
    (code : Σ ins, Operation P ins out × Wires (valuePorts params) past (valuePorts ins)) :
    Σ ins, Operation Q ins out × Wires (valuePorts params) past (valuePorts ins) :=
  ⟨code.1, mapOperation f code.2.1, code.2.2⟩

private theorem lowerLabel_map (f : PEG.InstructionMap P Q) {ins out}
    (label : PEG.Label P params (Fin 0) ins out)
    (wires : Wires (valuePorts params) past (valuePorts ins)) :
    lowerLabel (label.map f (fun l => l)) wires = mapLowered f (lowerLabel label wires) := by
  cases label with
  | param => rfl
  | op => rfl
  | phi => rfl
  | theta l | eval l | pass l => exact l.elim0

private theorem wireRefs_map (f : PEG.InstructionMap P Q) (g : PEG.Graph P params results n 0)
    (scope : Scope g k past) (rs : Tuple (PEG.Ref g.sort) ts)
    (left : ∀ i : Fin ts.length, ((rs.map (fun _ r => PEG.Ref.reindex (Equiv.refl (Fin n)) r)).get
      (PEG.portAt ts i)).id.val < k) (right : ∀ i : Fin ts.length,
      (rs.get (PEG.portAt ts i)).id.val < k) :
    wireRefs (g := g.mapOps f) scope (rs.map (fun _ r => PEG.Ref.reindex (Equiv.refl (Fin n)) r)) left =
      wireRefs scope rs right := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact congrArg (Tuple.cons (resolve scope r (right 0)))
      (ih (fun i => left i.succ) (fun i => right i.succ))

private abbrev Code (P : PEG.InstructionSet.{0,0} Data)
    (params results : List (PEG.Ty Data)) (past : List (List (ValuePort Data))) :=
  Σ sigs, RVSDG.Term (Opcode P) (valuePorts params) past sigs (valuePorts results)

private abbrev Table (P : PEG.InstructionSet.{0,0} Data) (params results : List (PEG.Ty Data)) :=
  Σ sigs, RVSDG.Graph (Opcode P) (valuePorts params) [] sigs (valuePorts results)

private def mapCode (f : PEG.InstructionMap P Q)
    (code : Σ sigs, RVSDG.Term (Opcode P) (valuePorts params) past sigs (valuePorts results)) :
    Σ sigs, RVSDG.Term (Opcode Q) (valuePorts params) past sigs (valuePorts results) :=
  ⟨code.1, RVSDG.Institution.mapTerm (mapOpcode f) code.2⟩

private theorem compileFrom_map (f : PEG.InstructionMap P Q) (g : PEG.Graph P params results n 0)
    (h : Ordered g) (remaining k : Nat) (size : k + remaining = n) (scope : Scope g k past) :
    compileFrom (g.mapOps f) (ordered_map f g h) remaining k size scope =
      mapCode f (compileFrom g h remaining k size scope) := by
  induction remaining generalizing k past with
  | zero =>
    simp only [compileFrom]
    exact congrArg (fun wires => (⟨[], RVSDG.Term.ret wires⟩ : Code Q params results past))
      (wireRefs_map f g scope g.roots _ _)
  | succ remaining ih =>
    simp only [compileFrom]
    let i : Fin n := ⟨k, by omega⟩
    let source := g.node i
    let op := lowerLabel source.label (wireRefs scope source.args (h i))
    have wires := wireRefs_map f g scope source.args
      (ordered_map f g h i) (h i)
    have translated :
        lowerLabel ((g.mapOps f).node i).label
          (wireRefs (g := g.mapOps f) scope ((g.mapOps f).node i).args (ordered_map f g h i)) =
        mapLowered f op := by
      change lowerLabel (source.label.map f (fun l => l)) _ = mapLowered f op
      exact (congrArg (lowerLabel (source.label.map f (fun l => l))) wires).trans
        (lowerLabel_map f source.label _)
    have tail := ih (k + 1) (by omega) (scope.push i rfl)
    rw [translated]
    let bind (rest : Code Q params results (past ++ [valuePorts [g.sort i]])) :
        Code Q params results past :=
      ⟨_, .bind (primitive (mapOperation f op.2.1) op.2.2) (fun j => j.elim0) rest.2⟩
    exact congrArg bind tail

theorem translate_map (f : PEG.InstructionMap P Q) (g : PEG.Graph P params results n 0)
    (h : Ordered g) :
    translate (g.mapOps f) (ordered_map f g h) =
      ⟨(translate g h).1, RVSDG.Institution.mapGraph (mapOpcode f) (translate g h).2⟩ := by
  let numbering : Scope g 0 [] := fun i hi => (Nat.not_lt_zero i.val hi).elim
  let code := compileFrom g h n 0 (Nat.zero_add n) (past := []) numbering
  have eq := compileFrom_map f g h n 0 (Nat.zero_add n) (past := []) numbering
  exact (congrArg (fun c : Code Q params results [] => (⟨c.1, c.2.toGraph⟩ : Table Q params results)) eq).trans
    (congrArg (fun graph => (⟨code.1, graph⟩ : Table Q params results))
      (RVSDG.Institution.mapGraph_toGraph (mapOpcode f) code.2).symm)

theorem mapPEG_id (e : PEG.Bridge.Equation S.ops) : mapPEG (𝟙 S) e = e := by
  cases e
  simp [mapPEG, PEG.Graph.mapOps_id]

theorem mapPEG_comp (f : S ⟶ T) (g : T ⟶ U) (e : PEG.Bridge.Equation S.ops) :
    mapPEG (f ≫ g) e = mapPEG g (mapPEG f e) := by
  cases e
  simp only [mapPEG, FixedSortSignature.opcodeMap_comp, PEG.Graph.mapOps_comp]

theorem translateEquation_map (f : S ⟶ T) (e : PEG.Bridge.Equation S.ops) :
    (mapPEG f e).toRVSDG = e.toRVSDG.map (mapOpcode (FixedSortSignature.opcodeMap f)) := by
  let op : PEG.InstructionMap S.ops T.ops := fun p => FixedSortSignature.opcodeMap f p
  exact congrArg₂ (fun l r => (⟨e.params, e.results, l.1, r.1, l.2, r.2⟩ :
    Regionless.ValueEquation (Opcode T.ops))) (translate_map op e.lhs e.leftOrdered)
      (translate_map op e.rhs e.rightOrdered)

theorem profile_natural (f : S ⟶ T) :
    (profileMap S.ops).map ((mlirSignature Data).map f) =
      (profileMap T.ops).precomp (mapOpcode (FixedSortSignature.opcodeMap f)) := by
  apply congrArg (Regionless.ProfileMap.mk (P := Opcode S.ops) (L := PEG.Bridge.signature T.ops) id)
  funext _ _ op
  cases op
  rfl

theorem translate_regionless_map (f : S ⟶ T) (e : Regionless.ValueEquation (Opcode S.ops)) :
    Regionless.translateEquation (profileMap T.ops) (e.map (mapOpcode (FixedSortSignature.opcodeMap f))) =
      (Regionless.translateEquation (profileMap S.ops) e).map ((mlirSignature Data).map f) := by
  let f' := profileMap T.ops
  let op : RVSDG.Institution.OpcodeMap (Opcode S.ops) (Opcode T.ops) :=
    mapOpcode (FixedSortSignature.opcodeMap f)
  exact (Regionless.translateEquation_precomp f' op e).symm.trans
    ((congrArg (fun p => Regionless.translateEquation p e) (profile_natural f).symm).trans
      (Regionless.translateEquation_map (profileMap S.ops) (mapSymbol f) e).symm)

end Silmaril.SSA.Peggy.Bridge.IR.Proofs
