module

import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Tests

private abbrev Ty := PortType Unit Unit
private abbrev nty : Ty := .value ()
private abbrev sty : Ty := .state ()
private abbrev np : Ports Ty := [nty]
private abbrev sp : Ports Ty := [sty]
private abbrev both : Ports Ty := [nty, sty]
private abbrev feedback : Ports Ty := [.control 2, sty]
private abbrev bodyResults : Ports Ty := Theta.BodyResults both
private abbrev entryPorts : Ports Ty := [.control 2, nty, sty]

private inductive Op : Ports Ty → Ports Ty → Type where
  | add (n : Nat) : Op np np
  | stamp (n : Nat) : Op sp sp
  | tick (bound : Nat) : Op sp feedback

private def model : Model Op where
  value _ := Nat
  state _ := List Nat
  run
    | .add n, .cons x .nil => .cons ((show Nat from x) + n) .nil
    | .stamp n, .cons trace .nil => .cons ((show List Nat from trace) ++ [n]) .nil
    | .tick bound, .cons trace .nil =>
      let next := (show List Nat from trace) ++ [bound]
      .cons ⟨if next.length < bound then 1 else 0⟩ (.cons next .nil)

private abbrev add {args : Ports Ty} {past : List (Ports Ty)} (n : Nat)
    (wire : Origin args past nty) : Node Op args past np :=
  ⟨np, .base (.simple (.add n)), .cons wire .nil, fun j => j.elim0⟩

private abbrev stamp {args : Ports Ty} {past : List (Ports Ty)} (n : Nat)
    (wire : Origin args past sty) : Node Op args past sp :=
  ⟨sp, .base (.simple (.stamp n)), .cons wire .nil, fun j => j.elim0⟩

private abbrev tick {past : List (Ports Ty)} (bound : Nat) : Node Op both past feedback :=
  ⟨sp, .base (.simple (.tick bound)), .cons (.arg (.tail .head)) .nil, fun j => j.elim0⟩

private def leftBody (arm : Fin 2) : Term Op both [] [np, feedback] bodyResults :=
  .bind (add (4 + arm.val) (.arg .head)) (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
    .bind (tick (2 + arm.val)) (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head)
        (.cons (.output (1 : Fin 2) (.tail .head)) .nil)))

private def rightBody (arm : Fin 2) : Term Op both [] [feedback, np] bodyResults :=
  .bind (tick (2 + arm.val)) (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
    .bind (add (4 + arm.val) (.arg .head)) (fun j => Fin.elim0 (by change Fin 0 at j; exact j)) <|
      .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head)
        (.cons (.output (0 : Fin 2) (.tail .head)) .nil)))

private def leftArmTerm (arm : Fin 2) : Term Op both [] [both] both :=
  .bind (thetaVertex [np, feedback]) (fun _ => leftBody arm) (.ret (thetaResults both))

private def rightArmTerm (arm : Fin 2) : Term Op both [] [both] both :=
  .bind (thetaVertex [feedback, np]) (fun _ => rightBody arm) (.ret (thetaResults both))

private abbrev leftGamma : Node Op entryPorts [np, sp] both :=
  ⟨entryPorts, .base (.gamma 0), .cons (.arg .head)
    (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)), fun _ => [both]⟩

private abbrev rightGamma : Node Op entryPorts [sp, np] both :=
  ⟨entryPorts, .base (.gamma 0), .cons (.arg .head)
    (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)), fun _ => [both]⟩

private def leftTerm : Term Op entryPorts [] [np, sp, both] both :=
  let first : Node Op entryPorts [] np := add 1 (.arg (.tail .head))
  let second : Node Op entryPorts [np] sp := stamp 3 (.arg (.tail (.tail .head)))
  .bind first (fun j => Fin.elim0 (show Fin 0 from j)) <|
    .bind second (fun j => Fin.elim0 (show Fin 0 from j)) <|
      .bind leftGamma leftArmTerm <|
        .ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil))

private def rightTerm : Term Op entryPorts [] [sp, np, both] both :=
  let first : Node Op entryPorts [] sp := stamp 3 (.arg (.tail (.tail .head)))
  let second : Node Op entryPorts [sp] np := add 1 (.arg (.tail .head))
  .bind first (fun j => Fin.elim0 (show Fin 0 from j)) <|
    .bind second (fun j => Fin.elim0 (show Fin 0 from j)) <|
      .bind rightGamma rightArmTerm <|
        .ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil))

private def left := leftTerm.toGraph
private def right := rightTerm.toGraph

private def exchange {n : Nat} : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 (fun rest => rest.succ.succ))

private theorem exchange_twice {n : Nat} (i : Fin (n + 2)) : exchange (exchange i) = i := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => ?_)) i <;> rfl

private def swapFirstTwo (n : Nat) : Fin (n + 2) ≃ Fin (n + 2) :=
  ⟨exchange, exchange, exchange_twice, exchange_twice⟩

private theorem bodyIso (arm : Fin 2) :
    Graph.Isomorphic Op (leftBody arm).toGraph (rightBody arm).toGraph := by
  refine .intro rfl rfl (swapFirstTwo 0) ?_ ?_ rfl ?_
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i
  · intro i
    exact Fin.cases (fun j => j.elim0) (Fin.cases (fun j => j.elim0) (fun j => j.elim0)) i

private theorem childIso (arm : Fin 2) :
    Graph.Isomorphic Op (leftArmTerm arm).toGraph (rightArmTerm arm).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) ?_ ?_ rfl ?_
  · intro i
    exact Fin.cases rfl (fun j => j.elim0) i
  · intro i
    exact Fin.cases rfl (fun j => j.elim0) i
  · intro i
    exact Fin.cases (fun _ => bodyIso arm) (fun j => j.elim0) i

private theorem renumbered : Graph.Isomorphic Op left right := by
  refine .intro rfl rfl (swapFirstTwo 1) ?_ ?_ rfl ?_
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => j.elim0))) i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => j.elim0))) i
  · intro i
    exact Fin.cases (fun j => j.elim0)
      (Fin.cases (fun j => j.elim0) (Fin.cases childIso (fun j => j.elim0))) i

example : Term.Isomorphic Op leftTerm rightTerm :=
  (leftTerm.isomorphic_toGraph_iff rightTerm).1 renumbered

example (m : Model Op) (fuel : Nat) (input : Tuple m.Val entryPorts) :
    left.run m fuel input = right.run m fuel input := renumbered.run_eq m fuel input

private def input : Tuple model.Val entryPorts := .cons ⟨(1 : Fin 2)⟩ (.cons (10 : Nat) (.cons [] .nil))

example : left.run model 1 input = none := rfl

private def result : Tuple model.Val both := .cons (21 : Nat) (.cons [3, 3, 3] .nil)

example : left.run model 2 input = some result := rfl

example : right.toTerm.Returns model input result :=
  (renumbered.term_returns_iff model input result).1
    ((left.returns_iff model input result).1 ⟨2, rfl⟩)

end Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Tests
