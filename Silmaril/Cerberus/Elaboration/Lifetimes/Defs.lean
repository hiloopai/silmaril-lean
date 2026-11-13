module

public import Silmaril.Cerberus.Elaboration.State.Defs
public import Silmaril.Cerberus.Elaboration.MemoryActions.Defs

/-! Actual lifetime-transfer construction from `translation.lem:3463-3496`.
Symbol membership uses semantic keys. Kills and creates retain source order;
this syntax construction does not discharge backend lifetime correctness. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Lifetimes
open Silmaril.Cerberus
open Construction

abbrev Visible := Sym × Ctype

def sequenceUnits (expressions : List Effect) (continuation : Effect) : Effect :=
  expressions.foldr (fun expression rest => strongSequence (wildcard .unit) expression rest) continuation

def sequenceBindings (expressions : List (Pat × Effect)) (continuation : Effect) : Effect :=
  expressions.foldr (fun (pattern, expression) rest => strongSequence pattern expression rest) continuation

def contains (symbol : Sym) (visible : List Visible) : Bool :=
  visible.any fun entry => decide (symbol.key = entry.1.key)

def killed (before after : List Visible) : List Visible :=
  before.filter fun entry => !contains entry.1 after

def created (before after : List Visible) : List Visible :=
  after.filter fun entry => !contains entry.1 before

def transfer (location : Loc) (label : Sym) (before after : List Visible)
    (arguments : List Pure) : Effect :=
  let kills := (killed before after).map fun (symbol, type) =>
    MemoryActions.staticKill location type (symbolPure symbol)
  let creates := (created before after).map fun (symbol, type) =>
    let coreType := ailCtype type
    (symbolPattern symbol (.object .pointer),
      MemoryActions.create location (alignof coreType) coreType (.source location [symbol]))
  sequenceUnits kills (sequenceBindings creates
    (Construction.run label (after.map (fun entry => symbolPure entry.1) ++ arguments)))

/-- Return targets have no visible objects: kill each captured local, then run. -/
def returnRun (location : Loc) (label : Sym) (before : List Visible)
    (arguments : List Pure) : Effect := transfer location label before [] arguments

def captureVisible : State.ElabM (List Visible) := do
  let symbols ← State.getVisibleObjects
  symbols.mapM fun symbol => do
    let (_, type) ← State.resolveObjectType symbol
    return (symbol, type)

end Silmaril.Cerberus.Elaboration.Lifetimes
