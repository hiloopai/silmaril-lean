module

public import Silmaril.Languages.Python.Compile.Closure.Link.Defs
public import Silmaril.Languages.Python.Core.Closure.Executor.Defs

/-! # Compile a Python closure program to the fixed-positional executor

Executor operands include the synthesized None result, integer literals,
Boolean assertion literals, name reads, and assertion tests comparing a name
to an integer literal. An assigned call makes its
destination explicit. A nested definition stores a closure using
its resolved code reference and ordered captures.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.Run

open Core.Closure (CodeRef Heap Layout Value)
open Core.Closure.Dispatch (Entry)
open Core.Closure.Executor (Operand NameRead State Event)

inductive NameReadTranslation {layout : Layout} : Body.Expr layout → NameRead layout → Prop where
  | slot (slot : Core.Closure.Slot layout) : NameReadTranslation (.read slot) (.slot slot)
  | global (name : Source.Name) : NameReadTranslation (.globalName name) (.global name)

def nameRead? {layout : Layout} : (source : Body.Expr layout) →
    Option {target // NameReadTranslation source target}
  | .read slot => some ⟨.slot slot, .slot slot⟩
  | .globalName name => some ⟨.global name, .global name⟩
  | _ => none

inductive OperandTranslation {layout : Layout} : Body.Expr layout → Operand layout → Prop where
  | none : OperandTranslation .none (.literal .none)
  | integer (value : Int) : OperandTranslation (.integer value) (.literal (.int value))
  | boolean (value : Bool) : OperandTranslation (.boolean value) (.literal (.bool value))
  | read (slot : Core.Closure.Slot layout) : OperandTranslation (.read slot) (.read slot)
  | tuple (items : List (Core.Closure.TupleItem layout)) : OperandTranslation (.tuple items) (.tuple items)
  | globalName (name : Source.Name) : OperandTranslation (.globalName name) (.readGlobal name)
  | eqIntSlot (slot : Core.Closure.Slot layout) (right : Int) :
      OperandTranslation (.eqInt (.read slot) right) (.eqInt (.slot slot) right)
  | eqIntGlobal (name : Source.Name) (right : Int) :
      OperandTranslation (.eqInt (.globalName name) right) (.eqInt (.global name) right)

  | addInt {left right lhs rhs} (first : OperandTranslation left lhs) (second : OperandTranslation right rhs) :
      OperandTranslation (.add left right) (.addInt lhs rhs)
  | mulInt {left right lhs rhs} (first : OperandTranslation left lhs) (second : OperandTranslation right rhs) :
      OperandTranslation (.mul left right) (.binaryInt .mul lhs rhs)

def operand? {layout : Layout} : (source : Body.Expr layout) →
    Option {target // OperandTranslation source target}
  | .tuple items => some ⟨.tuple items, .tuple items⟩
  | .none => some ⟨.literal .none, .none⟩
  | .integer value => some ⟨.literal (.int value), .integer value⟩
  | .boolean value => some ⟨.literal (.bool value), .boolean value⟩
  | .read slot => some ⟨.read slot, .read slot⟩
  | .globalName name => some ⟨.readGlobal name, .globalName name⟩
  | .eqInt (.read slot) right => some ⟨.eqInt (.slot slot) right, .eqIntSlot slot right⟩
  | .eqInt (.globalName name) right => some ⟨.eqInt (.global name) right, .eqIntGlobal name right⟩
  | .add left right => do
    let lhs ← operand? left
    let rhs ← operand? right
    return ⟨.addInt lhs.val rhs.val, .addInt lhs.property rhs.property⟩
  | .mul left right => do
    let lhs ← operand? left
    let rhs ← operand? right
    return ⟨.binaryInt .mul lhs.val rhs.val, .mulInt lhs.property rhs.property⟩
  | _ => none

inductive ArgumentsTranslation {layout : Layout} : List (Body.Expr layout) → List (Operand layout) → Prop where
  | nil : ArgumentsTranslation [] []
  | cons {source target sources targets}
      (first : OperandTranslation source target) (rest : ArgumentsTranslation sources targets) :
      ArgumentsTranslation (source :: sources) (target :: targets)

def arguments? {layout : Layout} : (sources : List (Body.Expr layout)) →
    Option {targets // ArgumentsTranslation sources targets}
  | [] => some ⟨[], .nil⟩
  | source :: rest => do
    let argument ← operand? source
    let tail ← arguments? rest
    return ⟨argument.val :: tail.val, .cons argument.property tail.property⟩

inductive Translation {layout : Layout} :
    Link.Code layout → Core.Closure.Executor.Body layout → Prop where
  | ret {source target} (value : OperandTranslation source target) :
      Translation (.ret source) (.ret target)
  /-- A final call through an ordinary local can reuse that local after
  the callee has finished. The local is outside the shared cell heap. -/
  | retLocalCall {slot arguments operands} (translated : ArgumentsTranslation arguments operands) :
      Translation (.ret (.call (.read (.local slot)) arguments))
        (.call (.local slot) (.read (.local slot)) operands (.ret (.read (.local slot))))
  | retGlobalCall {name arguments operands} (translated : ArgumentsTranslation arguments operands) :
      Translation (.ret (.call (.globalName name) arguments))
        (.returnCall (.readGlobal name) operands)
  | assert {source target rest next}
      (test : OperandTranslation source target) (tail : Translation rest next) :
      Translation (.assert source rest) (.assert target next)
  | assertFreeVars {source receiver needle expected rest next}
      (read : NameReadTranslation source receiver) (tail : Translation rest next) :
      Translation (.assertFreeVars source needle expected rest)
        (.assertFreevars ⟨receiver, needle, expected⟩ next)
  | assertCellVars {source receiver needle rest next}
      (read : NameReadTranslation source receiver) (tail : Translation rest next) :
      Translation (.assertCellVars source needle rest) (.assertCellvars ⟨receiver, needle⟩ next)
  | assertCodeNames {source receiver needle rest next}
      (read : NameReadTranslation source receiver) (tail : Translation rest next) :
      Translation (.assertCodeNames source needle rest) (.assertCodeNames ⟨receiver, needle⟩ next)
  | discardCall {callee function rest next}
      (calleeTranslation : OperandTranslation callee function) (tail : Translation rest next) :
      Translation (.discardCall callee rest) (.callTo .discard function [] next)
  | assign {slot source target rest next}
      (value : OperandTranslation source target) (tail : Translation rest next) :
      Translation (.assign slot source rest) (.store slot target next)
  | call {slot callee arguments function operands rest next}
      (calleeTranslation : OperandTranslation callee function)
      (argumentTranslation : ArgumentsTranslation arguments operands) (tail : Translation rest next) :
      Translation (.assign slot (.call callee arguments) rest) (.call slot function operands next)
  | closure {slot path ref captures rest next} (tail : Translation rest next) :
      Translation (.closure slot path ref captures rest) (.store slot (.closure ref captures) next)
  | returnClosure (path : Source.BlockPath) (ref : Core.Closure.CodeRef)
      (captures : Fin ref.layout.captures → Core.Closure.CaptureSlot layout) :
      Translation (.returnClosure path ref captures none) (.ret (.closure ref captures))
  | returnClosureCall {path ref captures arguments operands} (translated : ArgumentsTranslation arguments operands) :
      Translation (.returnClosure path ref captures (some arguments)) (.returnCall (.closure ref captures) operands)

def lowerCode {layout : Layout} : (code : Link.Code layout) →
    Option {target // Translation code target}
  | .returnClosure path ref captures none => some ⟨.ret (.closure ref captures), .returnClosure path ref captures⟩
  | .returnClosure _ ref captures (some arguments) => do
    let operands ← arguments? arguments
    return ⟨.returnCall (.closure ref captures) operands.val, .returnClosureCall operands.property⟩
  | .ret (.call (.read (.local slot)) arguments) => do
    let operands ← arguments? arguments
    return ⟨.call (.local slot) (.read (.local slot)) operands.val (.ret (.read (.local slot))),
      .retLocalCall operands.property⟩
  | .ret (.call (.globalName name) arguments) => do
    let operands ← arguments? arguments
    return ⟨.returnCall (.readGlobal name) operands.val, .retGlobalCall operands.property⟩
  | .ret expression => do
    let operand ← operand? expression
    return ⟨.ret operand.val, .ret operand.property⟩
  | .assert test rest => do
    let operand ← operand? test
    let tail ← lowerCode rest
    return ⟨.assert operand.val tail.val, .assert operand.property tail.property⟩
  | .assertFreeVars source needle expected rest => do
    let receiver ← nameRead? source
    let tail ← lowerCode rest
    return ⟨.assertFreevars ⟨receiver.val, needle, expected⟩ tail.val,
      .assertFreeVars receiver.property tail.property⟩
  | .assertCellVars source needle rest => do
    let receiver ← nameRead? source
    let tail ← lowerCode rest
    return ⟨.assertCellvars ⟨receiver.val, needle⟩ tail.val, .assertCellVars receiver.property tail.property⟩
  | .assertCodeNames source needle rest => do
    let receiver ← nameRead? source
    let tail ← lowerCode rest
    return ⟨.assertCodeNames ⟨receiver.val, needle⟩ tail.val, .assertCodeNames receiver.property tail.property⟩
  | .discardCall callee rest => do
    let function ← operand? callee
    let tail ← lowerCode rest
    return ⟨.callTo .discard function.val [] tail.val, .discardCall function.property tail.property⟩
  | .assign slot (.call callee arguments) rest => do
    let function ← operand? callee
    let operands ← arguments? arguments
    let tail ← lowerCode rest
    return ⟨.call slot function.val operands.val tail.val, .call function.property operands.property tail.property⟩
  | .assign slot expression rest => do
    let operand ← operand? expression
    let tail ← lowerCode rest
    return ⟨.store slot operand.val tail.val, .assign operand.property tail.property⟩
  | .closure slot _ ref captures rest => do
    let tail ← lowerCode rest
    return ⟨.store slot (.closure ref captures) tail.val, .closure tail.property⟩

inductive Error where
  | frontend (failure : Body.Error)
  | bodyProfile (path : Source.BlockPath)
  | entryCaptures
  deriving Repr

abbrev ExecutorEntry := Entry Core.Closure.Executor.Body

def executorEntry (block : Link.Block) (body : Core.Closure.Executor.Body block.entry.layout) : ExecutorEntry :=
  ⟨block.entry.layout,
    { parameters := block.entry.definition.parameters
      body := body
      freevars := block.entry.definition.freevars
      cellvars := block.entry.definition.cellvars
      codeNames := block.entry.definition.codeNames
      varnames := block.entry.definition.varnames
      variadic := block.entry.definition.variadic }⟩

inductive TableTranslation : List Link.Block → List ExecutorEntry → Prop where
  | nil : TableTranslation [] []
  | cons {block : Link.Block} {body : Core.Closure.Executor.Body block.entry.layout}
      {blocks entries} (head : Translation block.entry.definition.body body)
      (tail : TableTranslation blocks entries) :
      TableTranslation (block :: blocks) (executorEntry block body :: entries)

def lowerTable : (blocks : List Link.Block) → Except Error {entries // TableTranslation blocks entries}
  | [] => .ok ⟨[], .nil⟩
  | block :: rest => do
    let some body := lowerCode block.entry.definition.body | throw (.bodyProfile block.path)
    let tail ← lowerTable rest
    return ⟨executorEntry block body.val :: tail.val, .cons body.property tail.property⟩

structure Compiled (source : Source.Module) where
  sourceBody : Body.Compiled source
  entries : List ExecutorEntry
  lowered : TableTranslation (Link.link sourceBody).blocks entries
  entryCapturesEmpty : (Link.link sourceBody).entry.layout.captures = 0

def Compiled.entry {source : Source.Module} (compiled : Compiled source) : CodeRef :=
  (Link.link compiled.sourceBody).entry

def Compiled.table {source : Source.Module} (compiled : Compiled source) : Core.Closure.Executor.CodeTable :=
  fun key => compiled.entries[key]?

def compile (source : Source.Module) : Except Error (Compiled source) := do
  let body ← (Body.compile source).mapError .frontend
  let program := Link.link body
  if emptyCaptures : program.entry.layout.captures = 0 then
    let table ← lowerTable program.blocks
    return ⟨body, table.val, table.property, emptyCaptures⟩
  else throw .entryCaptures

inductive StartError where
  | resolve (failure : Core.Closure.Dispatch.Failure)
  | bind (failure : Core.Closure.Failure)
  deriving Repr

def start {source : Source.Module} (compiled : Compiled source) (arguments : List Value) :
    Except StartError State := do
  let definition ← (Core.Closure.Dispatch.resolve compiled.table compiled.entry).mapError .resolve
  let heap := Heap.empty
  let (heap, frame) := Core.Closure.Frame.fresh (layout := compiled.entry.layout) heap
    (fun index => Fin.elim0 (Fin.cast compiled.entryCapturesEmpty index))
  let environment ← (Core.Closure.Call.bindPositional definition.parameters arguments (heap, frame)).mapError .bind
  return .running environment.1 environment.2 definition.body []

def run {source : Source.Module} (compiled : Compiled source) (arguments : List Value) (fuel : Nat) :
    Except StartError (List Event × State) := do
  let state ← start compiled arguments
  return Core.Closure.Executor.runPrefix compiled.table fuel state

end Silmaril.Languages.Python.Compile.Closure.Run
