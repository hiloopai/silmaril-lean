module

public import Silmaril.Cerberus.Elaboration.Globals.Defs
public import Silmaril.Cerberus.Codec.WellFormed.Defs

/-! The empty-dependency specialization of pinned `core_linking.lem:70-279`.
Free-symbol analysis covers actual selected global constructor forms and rejects
other forms. In the linked Lem2026-05-01 Pset, choose is min_elt; the topo prepend
and final reverse therefore select ascending semantic keys when all edges are
empty. Unique keys restrict the source map/set representative ambiguity. This
is not an implementation of general nonempty-dependency topological ordering. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.GlobalOrder
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

/-- Lists represent finite sets only up to semantic-key membership. Their order
is immaterial for the only client operation, testing whether the set is empty. -/
def insert (symbol : Sym) (symbols : List Sym) : List Sym :=
  if symbols.any (fun present => decide (present.key = symbol.key)) then symbols
  else symbol :: symbols

def union (left right : List Sym) : List Sym := right.foldl (fun acc symbol => insert symbol acc) left

def without (free bound : List Sym) : List Sym :=
  free.filter fun symbol => !(bound.any fun name => decide (name.key = symbol.key))

/-- Source PEcall ignores its name and inspects arguments; CType/value payloads
introduce no free expression symbols in the source dependency analysis. -/
def freePure : Pure → Except String (List Sym)
  | .mk _ _ node => match node with
    | .sym symbol => .ok [symbol]
    | .val _ | .impl _ | .undef _ _ => .ok []
    | .ctor _ arguments | .call _ arguments => do
        let sets ← arguments.attach.mapM fun argument => freePure argument.val
        return sets.foldl union []
    | .struct _ members => do
        let sets ← members.attach.mapM fun member => freePure member.val.2
        return sets.foldl union []
    | .union _ _ expression => freePure expression
    | _ => .error "unsupported: independent-global pure dependency form"
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem argument.property
      omega
    | have h := List.sizeOf_lt_of_mem member.property
      rcases member with ⟨⟨identifier, value⟩, membership⟩
      simp_all
      omega

def boundSymbols : Pat → Except String (List Sym)
  | .mk _ (.base (some symbol, _)) => .ok [symbol]
  | .mk _ (.base (none, _)) => .ok []
  | _ => .error "unsupported: independent-global binding pattern"

def freeAction : ActionNode Codec.wireModel Unit Sym → Except String (List Sym)
  | .create alignment type _ => return union (← freePure alignment) (← freePure type)
  | .store _ type pointer value _ => return union (union (← freePure type) (← freePure pointer)) (← freePure value)
  | _ => .error "unsupported: independent-global action dependency form"

def freeEffect : Effect → Except String (List Sym)
  | .mk _ node => match node with
    | .pure expression => freePure expression
    | .bound expression => freeEffect expression
    | .sseq pattern first rest => do
        let firstSymbols ← freeEffect first
        let restSymbols ← freeEffect rest
        let bound ← boundSymbols pattern
        return union firstSymbols (without restSymbols bound)
    | .action (.mk _ (.mk _ _ action)) => freeAction action
    | _ => .error "unsupported: independent-global effect dependency form"
termination_by expression => sizeOf expression

def freeGlobal : Global Codec.wireModel Unit Unit → Except String (List Sym)
  | .declaration _ => .ok []
  | .definition _ expression => freeEffect expression

def uniqueKeys {α : Type} : List (Sym × α) → Bool
  | [] => true
  | (symbol, _) :: rest =>
      !(rest.any fun entry => decide (entry.1.key = symbol.key)) && uniqueKeys rest

/-- Actual pinned merge_globs specialization on zero dependency edges, with no
redundant tentative pairs. Translation and all fresh effects have already run;
this only orders the completed global output. -/
def mergeIndependent (globals : List (Sym × Global Codec.wireModel Unit Unit)) :
    Except String (List (Sym × Global Codec.wireModel Unit Unit)) := do
  unless uniqueKeys globals do
    throw "unsupported: duplicate global semantic keys"
  for (_, global) in globals do
    unless (← freeGlobal global).isEmpty do
      throw "unsupported: nonempty global dependencies need actual topological ordering"
  return globals.mergeSort fun left right => Codec.WellFormed.compareSym left.1 right.1 != .gt

end Silmaril.Cerberus.Elaboration.GlobalOrder
