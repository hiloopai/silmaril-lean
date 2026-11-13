module

public import Silmaril.Cerberus.Elaboration.Construction.Defs

/-! Positive-action aliases from pinned `core_aux.lem:510-523`, using actual
Core action syntax and the wire memory model. These construct actions; they do
not implement or certify a memory backend. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.MemoryActions
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

def positive (location : Loc) (action : ActionNode Codec.wireModel Unit Sym) : Effect :=
  .mk [] (.action (.mk .pos (.mk location () action)))

def create (location : Loc) (alignment type : Pure) (allocationPrefix : Prefix) : Effect :=
  positive location (.create alignment type allocationPrefix)

def staticKill (location : Loc) (type : Ctype) (pointer : Pure) : Effect :=
  positive location (.kill (.static type) pointer)

def store (location : Loc) (locking : Bool) (type pointer value : Pure)
    (order : MemoryOrder) : Effect := positive location (.store locking type pointer value order)

def load (location : Loc) (type pointer : Pure) (order : MemoryOrder) : Effect :=
  positive location (.load type pointer order)

end Silmaril.Cerberus.Elaboration.MemoryActions
