module

public import Silmaril.Cerberus.Elaboration.LocalObjects.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.LocalObjects
open Silmaril.Cerberus
open Construction

theorem default_alignment (type : Ctype) : alignment type none = alignof (ailCtype type) := rfl

theorem explicit_alignment (type : Ctype) (value : Int) :
    alignment type (some (.integer value)) = integer value := rfl

/-- The source function and local symbol both reach the allocation prefix. -/
theorem singleton_create (functionSymbol symbol : Sym) (actionLocation identifierLocation : Loc)
    (duration : Ail.StorageDuration) (register : Bool) (alignmentOption : Option Alignment)
    (qualifiers : Qualifiers) (type : Ctype) :
    blockCreates functionSymbol actionLocation
      [(symbol, ((identifierLocation, duration, register), alignmentOption, qualifiers, type))] =
    [(symbolPattern symbol (.object .pointer), MemoryActions.create actionLocation
      (alignment type alignmentOption) (ailCtype type) (.source identifierLocation [functionSymbol, symbol]))] := rfl

theorem concatStrong_unit (continuation : Effect) : concatStrong skip continuation = continuation := rfl

end Silmaril.Cerberus.Elaboration.LocalObjects
