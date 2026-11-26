module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Defs

/-! # Recursively structured mixed prefixes

Mixed θ leaves, recursive feedback and homogeneous binary choices produce
a raw payload with one live token. The typed carrier conversion joins the resulting tree to
any admitted ordered recursive suffix. The same parser reads root and
child scopes and discovers the cut from the actual leading vertices.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured

open Sequential
open Flat.Serial (WirePorts)
open OrderedTheta (carried carriedData results resultData)
open NestedTheta.ExplicitRuntime.PurePrefix.Splice (appendOrdered)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open LinearChain.Wiring (newest)
open NestedTheta.ExplicitRuntime.PurePrefix (Code EntryChecked)
open PureGamma (Choice ValueOp)
open NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse (orderedSuffix boundary)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A X Z L E D : τ}
variable {ps qs rows : List (Ports (OrderedRuntime.Structured.Ty τ))}

abbrev ChoiceRows (A : τ) := [Threaded (results A), InputPorts A]

inductive Tree (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) :
    List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | theta (s : Loop Φ ε A) (pureFirst : Bool) : Tree Φ ε A [InputPorts A]
  | feedback {ps : List (Ports (OrderedRuntime.Structured.Ty τ))}
      (body : Tree Φ ε A ps) (decide : TwoBlock.Instruction Φ A (Choice A)) :
      Tree Φ ε A [InputPorts A]
  | choice {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))} (gate : TwoBlock.Instruction Φ A (Choice A)) :
      Tree Φ ε A ps → Tree Φ ε A qs → Tree Φ ε A (ChoiceRows A)

def Tree.fragment : {rows : List (Ports (OrderedRuntime.Structured.Ty τ))} → Tree Φ ε A rows → Flat.Fragment Φ A A A
  | _, .theta s _ => s.fragment
  | _, .feedback body decide => (Flat.link body.fragment (.classify decide)).feedback
  | _, .choice gate left right => Flat.forkCase left.fragment right.fragment gate

abbrev RawCode (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) (rows : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
    (carriedData A) (carriedData A) (.arg (runtimePort (carried A))) rows

def choiceCode (gate : TwoBlock.Instruction Φ A (Choice A)) (left : RawCode Φ ε A ps)
    (right : RawCode Φ ε A qs) : RawCode Φ ε A (ChoiceRows A) :=
  let arms : Fin 2 → Σ rows, RawCode Φ ε A rows :=
    Fin.cases ⟨_, left⟩ (fun _ => ⟨_, right⟩)
  let classified := results A
  let past := [Threaded classified]
  ⟨_, .primitive (.arg (runtimePort (carried A))) (carriedData A) (resultData A)
    (.effect (.classifyPayload gate)) (.cons (.arg .head) .nil) <|
      .gamma 0 (newest .head []) (nextRuntime [] classified) (carriedData A) (carriedData A)
        (.cons (newest (.tail .head) []) .nil) (fun j => (arms j).1)
        (children := fun j => (arms j).2.1) (fun j => (arms j).2.2)
        (.ret (nextRuntime past (carried A)) (.cons (newest .head past) .nil))⟩

/-- Route the body's returned value using one ordered classifier. Its data
and token are read from the same checked return of the body. -/
def decisionCode (decide : TwoBlock.Instruction Φ A (Choice A)) :
    Wires.Code Φ (carriedData A) (resultData A) (.arg (runtimePort (carried A)))
      (past := []) [Threaded (results A)] :=
  ⟨_, .primitive (.arg (runtimePort (carried A))) (carriedData A) (resultData A)
    (.effect (.classifyPayload decide)) (.cons (.arg .head) .nil) <|
      .ret (nextRuntime [] (results A))
        (.cons (newest .head []) (.cons (newest (.tail .head) []) .nil))⟩

def feedbackBody (body : RawCode Φ ε A ps) (decide : TwoBlock.Instruction Φ A (Choice A)) :
    Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
      (carriedData A) (resultData A) (.arg (runtimePort (carried A))) (ps ++ [Threaded (results A)]) :=
  appendOrdered (decisionCode decide).2 body.2

def feedbackCode (body : RawCode Φ ε A ps) (decide : TwoBlock.Instruction Φ A (Choice A)) :
    RawCode Φ ε A [InputPorts A] :=
  let child := feedbackBody body decide
  ⟨_, .theta (.arg (runtimePort (carried A))) (carriedData A) (.cons (.arg .head) .nil)
    _ (children := fun _ => child.1) (fun _ => child.2)
    (.ret (nextRuntime [] (carried A)) (.cons (newest .head []) .nil))⟩

def Tree.code : {rows : List (Ports (OrderedRuntime.Structured.Ty τ))} → Tree Φ ε A rows → RawCode Φ ε A rows
  | _, .theta s order => s.code order
  | _, .feedback body decide => feedbackCode body.code decide
  | _, .choice gate left right => choiceCode gate left.code right.code

def Tree.graph (tree : Tree Φ ε A rows) := tree.code.1.toGraph

def Tree.checked (tree : Tree Φ ε A rows) :
    EntryChecked (a := carriedData A) (b := carriedData A) tree.graph.toTerm :=
  (NestedTheta.Term.toTerm_toGraph tree.code.1).symm ▸ tree.code.2

abbrev Graph (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A L E D : τ) (rows : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε) (InputPorts A) [] rows (WirePorts L E D)

/-- The selected prefix feeds the same recursive continuation on either arm. -/
def compile (head : Tree Φ ε A ps) (tail : StructuredCFG.WithNestedFeedback.Syntax Φ A X Z L E D qs) :
    Graph Φ ε A L E D ((ps ++ [WirePorts A X Z]) ++ qs) :=
  MixedContinuation.compile (headGraph := enterGraph head.checked X Z)
    (enterGraphChecked head.checked X Z) (.mixed tail)

structure Cut (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ)
    (args : Ports (OrderedRuntime.Structured.Ty τ)) (past rows : List (Ports (OrderedRuntime.Structured.Ty τ))) (outs : Ports (OrderedRuntime.Structured.Ty τ)) where
  headRows : List (Ports (OrderedRuntime.Structured.Ty τ))
  suffix : List (Ports (OrderedRuntime.Structured.Ty τ))
  tree : Tree Φ ε A headRows
  remaining : NestedTheta.Term (PureGamma.Op (τ := τ) Φ ε) args (past ++ headRows) suffix outs
  layout : headRows ++ suffix = rows

def Cut.make {args outs : Ports (OrderedRuntime.Structured.Ty τ)} {past : List (Ports (OrderedRuntime.Structured.Ty τ))} (tree : Tree Φ ε A ps)
    (rest : NestedTheta.Term (PureGamma.Op (τ := τ) Φ ε) args (past ++ rows) qs outs)
    (types : rows = ps) : Cut Φ ε A args past (rows ++ qs) outs :=
  ⟨ps, qs, tree, types ▸ rest, congrArg (· ++ qs) types.symm⟩

variable [DecidableEq τ]

def readGate {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} (kind : NestedTheta.Kind (PureGamma.Op (τ := τ) Φ ε) ins outs) :
    Option (TwoBlock.Instruction Φ A (Choice A)) :=
  match kind with
  | .base (.simple (.ordered op)) =>
    match Flat.Numbered.Recognize.opcodeKey op with
    | .classifyPayload a label => if a = A then MixedRows.instruction A (Choice A) label else none
    | _ => none
  | _ => none

def readDecision {args outs : Ports (OrderedRuntime.Structured.Ty τ)} {past rows : List (Ports (OrderedRuntime.Structured.Ty τ))} :
    NestedTheta.Term (PureGamma.Op (τ := τ) Φ ε) args past rows outs →
      Option (TwoBlock.Instruction Φ A (Choice A))
  | .bind node _ (.ret _) => readGate node.kind
  | _ => none

/-- Read a tree from a scope. Child scopes must end at the tree's result.
A feedback child consists of a tree followed by one classifier. At the root,
return the remaining numbered rows for suffix recovery. -/
def read (A : τ) : {args outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {past rows : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (PureGamma.Op (τ := τ) Φ ε) args past rows outs → Option (Cut Φ ε A args past rows outs)
  | _, _, _, _, .ret _ => none
  | _, _, past, _, .bind (head := first) node _
      (.bind (head := second) ⟨_, .base (.gamma 0), _, _⟩ children tail) => do
    let gate ← readGate node.kind
    let left ← read A (children (0 : Fin 2))
    let right ← read A (children (1 : Fin 2))
    if left.suffix.isEmpty && right.suffix.isEmpty then
      if types : [first,second] = ChoiceRows A then
        some (Cut.make (.choice gate left.tree right.tree) (List.append_assoc past [first] [second] ▸ tail) types)
      else none
    else none
  | _, _, _, _, .bind (head := first) node children tail =>
    if types : [first] = [InputPorts A] then
      match (PureTheta.Reverse.readTheta node.kind children).bind PureTheta.Reverse.decode with
      | some (loop, order) => some (Cut.make (.theta loop order) tail types)
      | none =>
        match node with
        | ⟨_, .theta _, _, _⟩ => do
          let cut ← read A (children (0 : Fin 1))
          let decide ← readDecision cut.remaining
          some (Cut.make (.feedback cut.tree decide) tail types)
        | _ => none
    else none

structure Candidate (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A L E D : τ)
    (rows : List (Ports (OrderedRuntime.Structured.Ty τ))) where
  headRows : List (Ports (OrderedRuntime.Structured.Ty τ))
  suffix : List (Ports (OrderedRuntime.Structured.Ty τ))
  leftSort : τ
  rightSort : τ
  tree : Tree Φ ε A headRows
  tail : Flat.Serial.Graph Φ A leftSort rightSort L E D suffix
  continuation : Translation.Fibre .mixed tail
  layout : (headRows ++ [WirePorts A leftSort rightSort]) ++ suffix = rows

def Candidate.emit (s : Candidate Φ ε A L E D rows) : Graph Φ ε A L E D rows :=
  s.layout ▸ MixedContinuation.linkRecovered (enterGraphChecked s.tree.checked s.leftSort s.rightSort) s.continuation

def Candidate.fragment (s : Candidate Φ ε A L E D rows) : Flat.Fragment Φ A E D :=
  Flat.link s.tree.fragment s.continuation.fragment

variable [DecidableEq Φ]

def readSuffix (tree : Tree Φ ε A ps) :
    {suffix : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (PureGamma.Op (τ := τ) Φ ε) (InputPorts A) ps suffix (WirePorts L E D) →
    ps ++ suffix = rows → Option (Candidate Φ ε A L E D rows)
  | _, .ret _, _ => none
  | _, .bind (head := head) adapter _ rest, layout => do
    let (input, x, z) ← readAdapter adapter.kind
    if input = A then
      if types : head = WirePorts A x z then do
        let tail ← orderedSuffix (boundary ps (WirePorts A x z)) (types ▸ rest)
        let continuation ← Translation.recover .mixed tail.toGraph
        return ⟨ps, _, x, z, tree, tail.toGraph, continuation, by
          simpa only [List.append_assoc, List.cons_append, List.nil_append, types] using layout⟩
      else none
    else none

def candidate (g : Graph Φ ε A L E D rows) : Option (Candidate Φ ε A L E D rows) := do
  let cut ← read A g.toTerm
  readSuffix cut.tree cut.remaining cut.layout

structure Fibre (g : Graph Φ ε A L E D rows) where
  shape : Candidate Φ ε A L E D rows
  wiring : shape.emit = g

def Fibre.fragment {g : Graph Φ ε A L E D rows} (f : Fibre g) : Flat.Fragment Φ A E D :=
  f.shape.fragment

def certify (g : Graph Φ ε A L E D rows) (c : Candidate Φ ε A L E D rows) : Option (Fibre g) :=
  letI := MixedRows.decideGraph c.emit g
  if same : c.emit = g then some ⟨c, same⟩ else none

/-- Discover the mixed tree and its recursive continuation from one
numbered table, then certify every operand and result address, including
nested feedback tokens, against the canonical emission. -/
def recover (g : Graph Φ ε A L E D rows) : Option (Fibre g) :=
  candidate g >>= certify g

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured
