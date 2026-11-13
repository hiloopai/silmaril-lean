module

public import Silmaril.Compiler.Core.Semantics.Defs
public import Silmaril.Compiler.Core.Spec.Defs
@[expose] public section

/-!
# Core behaviours at any enum registry and any program arguments

`Core.beh` (`Silmaril/Compile/Core/Semantics.lean`) starts the Core dynamics with
`Dynamics.initial file`: the **empty** enum registry and Cerberus's default arguments
`Startup.execArguments` (`["cmdname"]`). core-comp's specification (`Core.Spec.coreStart`) starts
it with the document's enum registry (`Codec.Document.enumBindings`) and any arguments that
`Spec.ArgsOk` accepts. This file lifts both restrictions:

* `behWith file enums args`: `Core.behFrom` the start state of `Dynamics.initial file enums args`;
  `Core.beh file` is `behWith file ∅ Startup.execArguments` (`beh_eq_behWith`, by `rfl`).
* `Source`: a Core file with its enum registry, the program of `langAt args`, the Core language
  whose programs run with the arguments `args`. `Source.ofDoc doc` is a decoded document's file
  and registry; its behaviours are `behFrom` `Spec.coreStart doc args` (`ofDoc_beh`, by `rfl`),
  and on a document without enum registry, at the default arguments, they are
  `Core.beh doc.file` (`ofDoc_beh_of_enumFree`).
* `cAS S`: typed Ail to Core sources run with the default arguments, at the same observations
  (`cAC` for sources). C semantics (`C.Sem.Semantics`) have no command line, so a C → Core
  elaboration is stated at `Startup.execArguments`; `valid_cAS_iff` says that on the empty
  registry it is `cAC`.
-/

namespace Silmaril.Compile.Core

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics (Program State Labels initial)
open CategoryTheory Silmaril.Compile.Category
open Silmaril.Compile.C.Sem (Obs)

/-- **The behaviours of a closed Core program run with an enum registry and arguments**:
`behFrom` the start state of `Dynamics.initial file enums args` (global definitions, `main`'s
argument objects for `args`, `errno`; `driver.lem:1542-1872`). -/
def behWith (file : Program) (enums : Map Sym IntegerType) (args : List String) : Set Obs :=
  match initial file enums args with
  | .ok (s₀, labels) => behFrom file labels s₀
  | .error _ => ∅

/-- `Core.beh` is `behWith` the empty registry and Cerberus's default arguments. -/
theorem beh_eq_behWith (file : Program) :
    beh file = behWith file ∅ Cerberus.Core.Startup.execArguments := rfl

/-- `behWith` is `behFrom` the state `Dynamics.initial` starts in. -/
theorem behWith_eq {file : Program} {enums : Map Sym IntegerType} {args : List String}
    {s₀ : State} {labels : Labels} (h : initial file enums args = .ok (s₀, labels)) :
    behWith file enums args = behFrom file labels s₀ := by
  simp only [behWith, h]

/-- A closed Core program with the enum registry its dynamics starts with. -/
structure Source where
  file : Program
  enums : Map Sym IntegerType := ∅

/-- The behaviours of a Core source run with the arguments `args`. -/
def Source.beh (args : List String) (q : Source) : Set Obs :=
  behWith q.file q.enums args

/-- The Core source of a decoded document: its file and its enum registry. -/
def Source.ofDoc (doc : Codec.Document) : Source :=
  ⟨doc.file, Map.ofList (doc.enumBindings.getD [])⟩

/-- A document's behaviours run with `args` are `behFrom` core-comp's start state
`Spec.coreStart doc args`. -/
theorem ofDoc_beh (doc : Codec.Document) (args : List String) :
    (Source.ofDoc doc).beh args =
      match Spec.coreStart doc args with
      | .ok (s₀, labels) => behFrom doc.file labels s₀
      | .error _ => ∅ := rfl

/-- A document's behaviours run with `args` are `behFrom` the state `Spec.coreStart` starts in. -/
theorem ofDoc_beh_of_coreStart {doc : Codec.Document} {args : List String} {s₀ : State}
    {labels : Labels} (h : Spec.coreStart doc args = .ok (s₀, labels)) :
    (Source.ofDoc doc).beh args = behFrom doc.file labels s₀ := by
  rw [ofDoc_beh, h]

/-- Without enum registry, `Spec.coreStart` at the default arguments is the start of
`Core.beh`. -/
theorem coreStart_of_enumFree {doc : Codec.Document} (h : doc.enumBindings.getD [] = []) :
    Spec.coreStart doc Cerberus.Core.Startup.execArguments = initial doc.file := by
  simp only [Spec.coreStart, h]
  rfl

/-- Without enum registry, at the default arguments, a document's behaviours are `Core.beh` of
its file. -/
theorem ofDoc_beh_of_enumFree {doc : Codec.Document} (h : doc.enumBindings.getD [] = []) :
    (Source.ofDoc doc).beh Cerberus.Core.Startup.execArguments = beh doc.file := by
  rw [ofDoc_beh, coreStart_of_enumFree h]
  rfl

/-- Core sources: closed Core files with their enum registry, observed as processes. -/
abbrev syntaxAt : Syntax.{0} := ⟨PUnit, Source, fun _ => ⟨⟩, Obs⟩

/-- Core as a language of the zoo, its programs run with the arguments `args`. -/
abbrev langAt (args : List String) : Language.{0} := syntaxAt.lang (Source.beh args)

/-- Typed Ail to Core sources run with the default arguments, at the same observations. -/
def cAS (S : C.Sem.Semantics) : C.Sem.cSyntax.lang S ⟶ langAt Cerberus.Core.Startup.execArguments :=
  ⟨fun _ => PUnit.unit, fun (o o' : Obs) => o = o'⟩

/-- On the empty registry, `cAS` is `cAC`. -/
theorem valid_cAS_iff (S : C.Sem.Semantics) (p : C.Sem.cSyntax.Prog) (file : Program) :
    Valid (cAS S) p ⟨file, ∅⟩ ↔ Valid (cAC S) p file := Iff.rfl

end Silmaril.Compile.Core
