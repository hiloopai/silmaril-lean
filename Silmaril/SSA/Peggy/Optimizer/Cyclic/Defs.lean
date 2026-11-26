module

public import Silmaril.SSA.PEG.Rules.Defs
public import Silmaril.SSA.Peggy.EPEG.Saturation.Defs
public import Silmaril.SSA.Peggy.EPEG.Selection.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Fin

/-! # One-loop PEG self-feedback elimination -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Optimizer.Cyclic

open PEG
open RVSDG (Tuple)
open EPEG (Classes Selection)
open EPEG.Saturation (Obligation)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n : Nat}

def supported {ins : List (Ty Data)} {out : Ty Data} :
    Label P params (Fin 1) ins out → Bool
  | .param _ | .op _ | .phi | .theta _ => true
  | .eval _ | .pass _ => false

/-- The nonfeedback phase estimate is updated synchronously. Feedback is
handled by the loop counter, so it contributes no edge to the phase estimate. -/
def nextPhase (g : Graph P params results n 1) (phase : Fin n → Nat) (i : Fin n) : Nat :=
  let row := g.node i
  (List.finRange row.inputs.length).foldr
    (fun slot upper => if (row.label.kind slot).IsFeedback then upper
      else max (phase (row.arg slot).id + 1) upper) 0

def inferPhase (g : Graph P params results n 1) : Nat → Fin n → Nat
  | 0 => fun _ => 0
  | fuel + 1 => nextPhase g (inferPhase g fuel)

def demandRank (phase : Fin n → Nat) : DemandRank n 1 :=
  [.counter 0, .phase phase]

/-- Independent certificates for the structural profile and native demands. -/
structure Admission (g : Graph P params results n 1) where
  phase : Fin n → Nat
  noParent : g.forest.parent 0 = none
  labels : ∀ i, supported (g.node i).label = true
  nonfeedback : ∀ i slot, ¬((g.node i).label.kind slot).IsFeedback →
    phase ((g.node i).arg slot).id < phase i
  demands : (demandRank phase).check g = true

/-- Compute a phase estimate, then check the actual numbered table.
Phase inference is bounded by the number of rows. -/
def admit (g : Graph P params results n 1) : Option (Admission g) :=
  let phase := inferPhase g n
  if ok : g.forest.parent 0 = none ∧ (∀ i, supported (g.node i).label = true) ∧
      (∀ i slot, ¬((g.node i).label.kind slot).IsFeedback →
        phase ((g.node i).arg slot).id < phase i) ∧
      (demandRank phase).check g = true then
    some ⟨phase, ok.1, ok.2.1, ok.2.2.1, ok.2.2.2⟩
  else none

variable {g : Graph P params results (n + 1) 1} {site : Fin (n + 1)}

/-- The actual row is a θ with literal self feedback and a distinct,
zero-input initializer. A leaf initializer needs no stream-definedness premise. -/
structure Match (g : Graph P params results (n + 1) 1) (site : Fin (n + 1)) where
  loop : Fin 1
  init : Ref g.sort (g.sort site)
  feedback : Ref g.sort (g.sort site)
  self : feedback.id = site
  distinct : init.id ≠ site
  leaf : (g.node init.id).inputs = []
  shape : Rules.HasNode (Ref.ofId g.sort site) (.theta loop) (.cons init (.cons feedback .nil))

def matchRow (g : Graph P params results (n + 1) 1) (site : Fin (n + 1)) :
    (row : Node P params (Fin 1) g.sort (g.sort site)) → g.node site = row → Option (Match g site)
  | ⟨_, .theta loop, .cons init (.cons feedback .nil)⟩, bound =>
    if ok : feedback.id = site ∧ init.id ≠ site ∧ (g.node init.id).inputs = [] then
      some ⟨loop, init, feedback, ok.1, ok.2.1, ok.2.2, heq_of_eq bound⟩
    else none
  | _, _ => none

def matchAt (g : Graph P params results (n + 1) 1) (site : Fin (n + 1)) :
    Option (Match g site) :=
  matchRow g site (g.node site) rfl

namespace Match

def rule (found : Match g site) : EPEG.GuardedEquation g :=
  ⟨[⟨found.feedback.id, site, congrArg g.sort found.self⟩],
    ⟨site, found.init.id, found.init.typed.symm⟩⟩

def obligation (found : Match g site) : Obligation g := .guarded found.rule

def classes (found : Match g site) : Classes (n + 1) :=
  EPEG.Saturation.saturate [found.obligation] Classes.discrete

/-- Find the remaining address of a vertex different from the deleted one. -/
def survivor (hole v : Fin (n + 1)) (distinct : v ≠ hole) :
    {i : Fin n // hole.succAbove i = v} :=
  Fin.succAboveCases hole (fun h => (h rfl).elim) (fun i _ => ⟨i, rfl⟩) v distinct

/-- Redirect the eliminated row to the initializer and compact all other addresses. -/
def redirect (found : Match g site) {out : Ty Data} (ref : Ref g.sort out) :
    Ref (g.sort ∘ site.succAbove) out :=
  if same : ref.id = site then
    let i := survivor site found.init.id found.distinct
    ⟨i.val, (congrArg g.sort i.property).trans
      (found.init.typed.trans ((congrArg g.sort same.symm).trans ref.typed))⟩
  else
    let i := survivor site ref.id same
    ⟨i.val, (congrArg g.sort i.property).trans ref.typed⟩

def extract (found : Match g site) : Graph P params results n 1 where
  forest := g.forest
  sort := g.sort ∘ site.succAbove
  node i :=
    let old := g.node (site.succAbove i)
    Node.ofLabel old.label (old.args.map fun _ => found.redirect)
  roots := g.roots.map fun _ => found.redirect

def selection (found : Match g site) (phase : Fin n → Nat) : Selection g found.extract :=
  ⟨fun i => Ref.ofId g.sort (site.succAbove i), demandRank phase⟩

/-- Generate both sides of the certificate from the same retained source row.
Only the operand references are redirected. -/
def rows (found : Match g site) (phase : Fin n → Nat) (i : Fin n) :
    Selection.Row (found.selection phase) i :=
  let old := g.node (site.succAbove i)
  ⟨old.inputs, old.label, old.args, old.args.map (fun _ => found.redirect), HEq.rfl, rfl⟩

end Match

structure Result (g : Graph P params results (n + 1) 1) where
  source : Admission g
  site : Fin (n + 1)
  matched : Match g site
  target : Admission matched.extract
  boundary : (matched.selection target.phase).check matched.classes = true
  edges : Selection.checkRows (matched.rows target.phase) matched.classes = true

def trySite (g : Graph P params results (n + 1) 1) (source : Admission g)
    (site : Fin (n + 1)) : Option (Result g) := do
  let found ← matchAt g site
  let target ← admit found.extract
  if ok : (found.selection target.phase).check found.classes = true ∧
      Selection.checkRows (found.rows target.phase) found.classes = true then
    some ⟨source, site, found, target, ok.1, ok.2⟩
  else none

/-- Scan at most one pass over the source addresses. Return the first
candidate passing all the independent checks. -/
def optimize (g : Graph P params results (n + 1) 1) : Option (Result g) := do
  let source ← admit g
  (List.finRange (n + 1)).findSome? (trySite g source)

end Silmaril.SSA.Peggy.Optimizer.Cyclic
