module

import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Tests

private abbrev T := Ty Unit Unit
private abbrev datum : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev st : T := .state ()
private abbrev fn : Function Unit Unit := ⟨[st], [st]⟩
private abbrev callable : T := fn.port
private abbrev imports : Ports T := [datum, datum]
private abbrev exports : Ports T := [global, callable, callable, callable, datum]
private abbrev groupPorts : Ports T := [callable, callable]
private abbrev leftSigs : List (Ports T) := [[global], groupPorts, [callable]]
private abbrev rightSigs : List (Ports T) := [groupPorts, [global], [callable]]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | stamp (id : Nat) : Op [datum] [datum]
  | mix : Op [datum, st] [st]

private def exchange {n : Nat} : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 (fun j => j.succ.succ))

private theorem exchange_twice {n : Nat} (i : Fin (n + 2)) : exchange (exchange i) = i :=
  Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

private def swap (n : Nat) : Fin (n + 2) ≃ Fin (n + 2) :=
  ⟨exchange, exchange, exchange_twice, exchange_twice⟩

private theorem everyTwo {P : Fin 2 → Prop} (first : P 0) (second : P 1) : ∀ i, P i :=
  Fin.cases first (Fin.cases second (fun i => i.elim0))

private theorem everyThree {P : Fin 3 → Prop} (first : P 0) (second : P 1) (third : P 2) : ∀ i, P i :=
  Fin.cases first (Fin.cases second (Fin.cases third (fun i => i.elim0)))

private abbrev deltaNode {past : List (Ports T)} (id : Nat) (port : Port imports datum) :
    RVSDG.Node Op imports past [datum] :=
  ⟨[datum], .simple (.stamp id), .cons (.arg port) .nil, fun j => j.elim0⟩

private def initL : RVSDG.Term Op imports [] [[datum], [datum]] [datum] :=
  .bind (deltaNode 3 .head) (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
    .bind (deltaNode 4 (.tail .head)) (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
      .ret (.cons (.output (0 : Fin 2) .head) .nil)

private def initR : RVSDG.Term Op imports [] [[datum], [datum]] [datum] :=
  .bind (deltaNode 4 (.tail .head)) (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
    .bind (deltaNode 3 .head) (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
      .ret (.cons (.output (1 : Fin 2) .head) .nil)

private def capturesImport {past : List (Ports T)} : Wires imports past imports :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

private def deltaL : DeltaTerm Op imports [] (.data ()) :=
  ⟨imports, capturesImport, _, initL⟩

private def deltaR : DeltaTerm Op imports [groupPorts] (.data ()) :=
  ⟨imports, capturesImport, _, initR⟩

private theorem deltaIso (ids : Nat → Nat) : deltaL.Renumbered ids deltaR :=
  ⟨⟨rfl, rfl⟩, .intro rfl rfl (swap 0)
    (everyTwo (.intro rfl rfl (fun j => j.elim0)) (.intro rfl rfl (fun j => j.elim0))) rfl⟩

private abbrev lambdaContext : Ports T := [datum, callable]
private abbrev bodyArgs : Ports T := lambdaContext ++ fn.args

private abbrev stamp {past : List (Ports T)} :
    NestedTheta.Node (Instruction Op) bodyArgs past [datum] :=
  ⟨[datum], .base (.simple (.primitive (.stamp 5))), .cons (.arg .head) .nil, fun j => j.elim0⟩

private abbrev call {past : List (Ports T)} :
    NestedTheta.Node (Instruction Op) bodyArgs past [st] :=
  ⟨[callable, st], .base (.simple (.apply fn)),
    .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil), fun j => j.elim0⟩

private abbrev mix {past : List (Ports T)} (wires : Wires bodyArgs past [datum, st]) :
    NestedTheta.Node (Instruction Op) bodyArgs past [st] :=
  ⟨[datum, st], .base (.simple (.primitive .mix)), wires, fun j => j.elim0⟩

private def bodyL : NestedTheta.Term (Instruction Op) bodyArgs [] [[datum], [st], [st]] [st] :=
  .bind stamp (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
    .bind call (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
      .bind (mix (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)))
        (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
        .ret (.cons (.output (2 : Fin 3) .head) .nil)

private def bodyR : NestedTheta.Term (Instruction Op) bodyArgs [] [[st], [datum], [st]] [st] :=
  .bind call (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
    .bind stamp (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
      .bind (mix (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)))
        (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
        .ret (.cons (.output (2 : Fin 3) .head) .nil)

private theorem bodyIso : NestedTheta.Term.Isomorphic (Instruction Op) bodyL bodyR :=
  .intro rfl rfl (swap 1)
    (everyThree (.intro rfl rfl (fun j => j.elim0)) (.intro rfl rfl (fun j => j.elim0))
      (.intro rfl rfl (fun j => j.elim0))) rfl

private def memberL {entry : Ports T} {past : List (Ports T)}
    (dataSource : Origin entry past datum) (callSource : Origin entry past callable) :
    LambdaTerm Op entry past fn :=
  ⟨lambdaContext, .cons dataSource (.cons callSource .nil), _, bodyL⟩

private def memberR {entry : Ports T} {past : List (Ports T)}
    (dataSource : Origin entry past datum) (callSource : Origin entry past callable) :
    LambdaTerm Op entry past fn :=
  ⟨lambdaContext, .cons dataSource (.cons callSource .nil), _, bodyR⟩

private def groupL : PhiTerm Op imports [[global]] [fn, fn] :=
  ⟨imports, capturesImport, .cons
    (memberL (.arg .head) (.arg (.tail (.tail (.tail .head)))))
    (.cons (memberL (.arg (.tail .head)) (.output (0 : Fin 1) .head)) .nil)⟩

private def groupR : PhiTerm Op imports [] [fn, fn] :=
  ⟨imports, capturesImport, .cons
    (memberR (.arg .head) (.arg (.tail (.tail (.tail .head)))))
    (.cons (memberR (.arg (.tail .head)) (.output (0 : Fin 1) .head)) .nil)⟩

private theorem groupIso (ids : Nat → Nat) : groupL.Renumbered ids groupR :=
  ⟨⟨rfl, rfl⟩, everyTwo ⟨⟨rfl, rfl⟩, bodyIso⟩ ⟨⟨rfl, rfl⟩, bodyIso⟩⟩

private def wrapperL : LambdaTerm Op imports [[global], groupPorts] fn :=
  memberL (.arg .head) (.output (1 : Fin 2) (.tail .head))

private def wrapperR : LambdaTerm Op imports [groupPorts, [global]] fn :=
  memberR (.arg .head) (.output (0 : Fin 2) (.tail .head))

private def leftResults : Wires imports leftSigs exports :=
  .cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head)
    (.cons (.output (1 : Fin 3) (.tail .head)) (.cons (.output (2 : Fin 3) .head)
      (.cons (.arg (.tail .head)) .nil))))

private def rightResults : Wires imports rightSigs exports :=
  .cons (.output (1 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head)
    (.cons (.output (0 : Fin 3) (.tail .head)) (.cons (.output (2 : Fin 3) .head)
      (.cons (.arg (.tail .head)) .nil))))

private def leftTerm : OmegaTerm Op imports exports leftSigs :=
  ⟨.bind (.delta deltaL) (.bind (.phi groupL) (.bind (.lambda wrapperL) (.ret leftResults)))⟩

private def rightTerm : OmegaTerm Op imports exports rightSigs :=
  ⟨.bind (.phi groupR) (.bind (.delta deltaR) (.bind (.lambda wrapperR) (.ret rightResults)))⟩

private theorem termsRelated : leftTerm.RenumberedBy rightTerm (swap 1) :=
  ⟨everyThree (.delta (deltaIso _)) (.phi (groupIso _)) (.lambda ⟨⟨rfl, rfl⟩, bodyIso⟩), rfl⟩

private def rightGraph : Omega Op imports exports rightSigs :=
  ⟨⟨Fin.cases (.phi groupR.toGraph)
    (Fin.cases (.delta deltaR.toGraph) (Fin.cases (.lambda wrapperR.toGraph) (fun i => i.elim0))),
    rightResults⟩⟩

private theorem graphRelated : leftTerm.toGraph.RenumberedBy rightGraph (swap 1) :=
  (OmegaTerm.renumberedBy_toGraph_iff leftTerm rightTerm (swap 1)).2 termsRelated

example : leftTerm.toGraph.toTerm.RenumberedBy rightGraph.toTerm (swap 1) :=
  (leftTerm.toGraph.renumberedBy_toTerm_iff rightGraph (swap 1)).2 graphRelated

example : leftTerm.toGraph.Isomorphic rightGraph := ⟨swap 1, graphRelated⟩

-- Even though the two recursion arguments have the same type, they are distinct ports.
private def wrongMember : LambdaTerm Op (imports ++ memberPorts [fn, fn]) [] fn :=
  memberR (.arg .head) (.arg (.tail (.tail .head)))

example : ¬ (groupL.definitions.get (0 : Fin 2)).Renumbered id wrongMember := by
  intro related
  have wires := related.1.2
  change [Address.arg 0, Address.arg 3] = [Address.arg 0, Address.arg 2] at wires
  cases wires

private def swappedExports : Omega Op imports exports rightSigs :=
  ⟨⟨rightGraph.region.vertices,
    .cons (.output (1 : Fin 3) .head) (.cons (.output (0 : Fin 3) (.tail .head))
      (.cons (.output (0 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head)
        (.cons (.arg (.tail .head)) .nil))))⟩⟩

example : ¬ leftTerm.toGraph.RenumberedBy swappedExports (swap 1) := by
  intro related
  have wires := related.exports
  change [Address.output 1 0, Address.output 0 0, Address.output 0 1, Address.output 2 0, Address.arg 1] =
    [Address.output 1 0, Address.output 0 1, Address.output 0 0, Address.output 2 0, Address.arg 1] at wires
  cases wires

-- The physical φ numbering is tied to the boundary result slots.
example : ¬ (∀ i, Address.rename (renameVertex (swap 0)) (groupL.toGraph.resultOrigin i).address =
    (groupR.toGraph.resultOrigin i).address) := by
  intro preserves
  have fixed := groupL.toGraph.member_number_eq groupR.toGraph (swap 0) preserves (0 : Fin 2)
  have eq : (1 : Nat) = 0 := congrArg Fin.val fixed
  cases eq

end Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Tests
