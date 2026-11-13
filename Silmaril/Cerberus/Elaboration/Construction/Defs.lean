module

public import Silmaril.Cerberus.Core.Syntax.Defs
public import Silmaril.Cerberus.Codec.Mem.Defs

/-! Constructor and annotation equations from `frontend/model/core_aux.lem` at
Cerberus `b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. These operate on the actual
Core syntax before type inference. Scalar values use the existing wire memory
model; they do not implement the concrete PNVI memory backend. Empty tuples
reject explicitly.
-/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Construction
open Silmaril.Cerberus
open Silmaril.Cerberus.Core

abbrev Pure := Pexpr Codec.wireModel Unit Sym
abbrev Effect := Expr Codec.wireModel Unit Unit Sym
abbrev Pat := Pattern Sym
abbrev SaveArgument := Sym × ((BaseType × Option (Ctype × PassBy)) × Pure)

def wildcard (type : BaseType) : Pat := .mk [] (.base (none, type))

def symbolPatternWith (annotations : List Annot) (symbol : Option Sym)
    (type : BaseType) : Pat := .mk annotations (.base (symbol, type))

def symbolPattern (symbol : Sym) (type : BaseType) : Pat :=
  symbolPatternWith [] (some symbol) type

def tuplePattern : List Pat → Except String Pat
  | [] => .error "[Core_aux.mk_tuple_pat] called with |pats| = 0"
  | [pattern] => .ok pattern
  | patterns => .ok (.mk [] (.ctor .tuple patterns))

def specifiedPatternWith (annotations : List Annot) (pattern : Pat) : Pat :=
  .mk annotations (.ctor .specified [pattern])

def unspecifiedPatternWith (annotations : List Annot) (pattern : Pat) : Pat :=
  .mk annotations (.ctor .unspecified [pattern])

def specifiedPattern (pattern : Pat) : Pat := specifiedPatternWith [] pattern
def unspecifiedPattern (pattern : Pat) : Pat := unspecifiedPatternWith [] pattern

def listPattern (type : BaseType) : List Pat → Pat
  | [] => .mk [] (.ctor (.nil type) [])
  | pattern :: rest => .mk [] (.ctor .cons [pattern, listPattern type rest])

def annotateInteger (type : IntegerType) : Pure → Pure
  | .mk annotations () node => .mk (.value (.integer type) :: annotations) () node

/-- Only a direct integer type matches; an atomic wrapper is not removed. -/
def maybeAnnotateInteger : Ctype → Pure → Pure
  | .mk _ (.basic (.integer type)), expression => annotateInteger type expression
  | _, expression => expression

def symbolPureWith {bty : Type} (annotations : List Annot) (type : bty) (symbol : Sym) :
    Pexpr Codec.wireModel bty Sym := .mk annotations type (.sym symbol)
def symbolPure (symbol : Sym) : Pure := symbolPureWith [] () symbol
def valuePure (value : Value Codec.wireModel) : Pure := .mk [] () (.val value)

/-- Upstream's object integer, before `specified` wrapping. -/
def integer (value : Int) : Pure := valuePure (.object (.integer value))
def floating (value : Codec.wireModel.FloatingValue) : Pure :=
  valuePure (.object (.floating value))
def nullptr (referencedType : Ctype) : Pure := valuePure (.object (.pointer (.null referencedType)))
def specified (expression : Pure) : Pure := .mk [] () (.ctor .specified [expression])
def unspecified (type : Ctype) : Pure := valuePure (.loaded (.unspecified type))
def array (expressions : List Pure) : Pure := .mk [] () (.ctor .array expressions)
def unit : Pure := valuePure .unit
def boolean (value : Bool) : Pure := valuePure (if value then .true else .false)
def ctype (type : Ctype) : Pure := valuePure (.ctype type)
def ailCtype (type : Ctype) : Pure := ctype type

def listPure (type : BaseType) : List Pure → Pure
  | [] => .mk [] () (.ctor (.nil type) [])
  | expression :: rest => .mk [] () (.ctor .cons [expression, listPure type rest])

def tuplePure : List Pure → Except String Pure
  | [] => .error "Core_aux.mk_tuple_pe []"
  | [expression] => .ok expression
  | expressions => .ok (.mk [] () (.ctor .tuple expressions))

def ivmax (expression : Pure) : Pure := .mk [] () (.ctor .ivMax [expression])
def ivmin (expression : Pure) : Pure := .mk [] () (.ctor .ivMin [expression])
def sizeof (expression : Pure) : Pure := .mk [] () (.ctor .ivSizeof [expression])
def alignof (expression : Pure) : Pure := .mk [] () (.ctor .ivAlignof [expression])
def nullcap (signed : Bool) : Pure := .mk [] () (.ctor (.ivNullCap signed) [])
def undefined (location : Loc) (behavior : UndefinedBehaviour) : Pure :=
  .mk [] () (.undef location behavior)
def errorPure (message : String) (expression : Pure) : Pure := .mk [] () (.error message expression)
def notPure (expression : Pure) : Pure := .mk [] () (.not expression)
def operation (operator : BinOp) (left right : Pure) : Pure := .mk [] () (.op operator left right)
def convertInteger (type : IntegerType) (expression : Pure) : Pure :=
  .mk [] () (.convInt type expression)
def wrapInteger (type : IntegerType) (operator : IntOp) (left right : Pure) : Pure :=
  .mk [] () (.wrapI type operator left right)
def catchExceptionalCondition (type : IntegerType) (operator : IntOp) (left right : Pure) : Pure :=
  .mk [] () (.catchExceptionalCondition type operator left right)
def letPure (pattern : Pat) (value body : Pure) : Pure := .mk [] () (.let_ pattern value body)
def ifPureWith (annotations : List Annot) (condition yes no : Pure) : Pure :=
  .mk annotations () (.if_ condition yes no)
def ifPure (condition yes no : Pure) : Pure := ifPureWith [] condition yes no
def arrayShift (pointer : Pure) (type : Ctype) (index : Pure) : Pure :=
  .mk [] () (.arrayShift pointer type index)
def memberShift (pointer : Pure) (tag : Sym) (member : Identifier) : Pure :=
  .mk [] () (.memberShift pointer tag member)
def pureMemoryOperation (operator : PureMemOp) (arguments : List Pure) : Pure :=
  .mk [] () (.memop operator arguments)
def casePure (expression : Pure) (branches : List (Pat × Pure)) : Pure :=
  .mk [] () (.case_ expression branches)
def negate (type : IntegerType) (expression : Pure) : Pure :=
  operation .sub (annotateInteger type (integer 0)) expression
def structPure (tag : Sym) (members : List (Identifier × Pure)) : Pure := .mk [] () (.struct tag members)
def unionPure (tag : Sym) (member : Identifier) (value : Pure) : Pure := .mk [] () (.union tag member value)
def memberOf (tag : Sym) (member : Identifier) (value : Pure) : Pure := .mk [] () (.memberof tag member value)
def cfunction (expression : Pure) : Pure := .mk [] () (.cfunction expression)
def standardPure (standard : String) : Pure → Pure
  | .mk annotations type node => .mk (.std standard :: annotations) type node
def standardUndefined (location : Loc) (standard : String) (behavior : UndefinedBehaviour) : Pure :=
  standardPure standard (undefined location behavior)
def standardPair (standard : String) (expressions : Pure × Pure) : Pure × Pure :=
  (standardPure standard expressions.1, standardPure standard expressions.2)
def call (name : Name Sym) (arguments : List Pure) : Pure := .mk [] () (.call name arguments)
def compatible (left right : Pure) : Pure := .mk [] () (.areCompatible left right)

def pureEffect (expression : Pure) : Effect := .mk [] (.pure expression)
def valueEffect (value : Value Codec.wireModel) : Effect := pureEffect (valuePure value)
def skip : Effect := pureEffect unit

/-- `mk_unseq_e` always retains the constructor, even for zero/one operands. -/
def unseqEffect (expressions : List Effect) : Effect := .mk [] (.unseq expressions)

/-- The distinct earlier `mk_unseq` smart constructor. -/
def unseq : List Effect → Effect
  | [] => skip
  | [expression] => expression
  | expressions => unseqEffect expressions

def caseEffect (expression : Pure) (branches : List (Pat × Effect)) : Effect :=
  .mk [] (.case_ expression branches)
def weakSequence (pattern : Pat) (first second : Effect) : Effect := .mk [] (.wseq pattern first second)
def strongSequence (pattern : Pat) (first second : Effect) : Effect := .mk [] (.sseq pattern first second)
def saveWith (annotations : List Annot) (label : Sym × BaseType)
    (arguments : List SaveArgument) (body : Effect) : Effect := .mk annotations (.save label arguments body)
def save (label : Sym × BaseType) (arguments : List SaveArgument) (body : Effect) : Effect :=
  saveWith [] label arguments body
def run (label : Sym) (arguments : List Pure) : Effect := .mk [] (.run () label arguments)
def nondeterministic (expressions : List Effect) : Effect := .mk [] (.nd expressions)
def ifEffectWith (annotations : List Annot) (condition : Pure) (yes no : Effect) : Effect :=
  .mk annotations (.if_ condition yes no)
def ifEffect (condition : Pure) (yes no : Effect) : Effect := ifEffectWith [] condition yes no
def letEffect (pattern : Pat) (value : Pure) (body : Effect) : Effect := .mk [] (.let_ pattern value body)
def ccallWith (annotations : List Annot) (type function : Pure) (arguments : List Pure) : Effect :=
  .mk annotations (.ccall () type function arguments)
def memoryOperation (operator : MemOp Sym) (arguments : List Pure) : Effect :=
  .mk [] (.memop operator arguments)
def wait (thread : ThreadId) : Effect := .mk [] (.wait thread)

/-- Delete only the first matching annotation, preserving all later entries. -/
def deleteFirst (predicate : Annot → Bool) : List Annot → List Annot
  | [] => []
  | annotation :: rest => if predicate annotation then rest else annotation :: deleteFirst predicate rest

def addLocation (location : Loc) : Effect → Effect
  | .mk annotations node =>
      .mk (.loc location :: deleteFirst (fun a => match a with | .loc _ => true | _ => false) annotations) node
def addAnnotation (annotation : Annot) : Effect → Effect
  | .mk annotations node => .mk (annotation :: annotations) node
def addAnnotations (newAnnotations : List Annot) : Effect → Effect
  | .mk annotations node => .mk (newAnnotations ++ annotations) node
def addStatement (expression : Effect) : Effect := addAnnotation .stmt expression
def addExpression (expression : Effect) : Effect := addAnnotation .expr expression
def addStandard (standard : String) (expression : Effect) : Effect := addAnnotation (.std standard) expression
def addStandards (standards : List String) (expression : Effect) : Effect :=
  addAnnotations (standards.map Annot.std) expression
def addAttributes : Attributes → Effect → Effect
  | .mk [], expression => expression
  | attributes, expression => addAnnotation (.attrs attributes) expression

end Silmaril.Cerberus.Elaboration.Construction
