module

public import Silmaril.Cerberus.Elaboration.State.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.State
open Silmaril.Cerberus
open Silmaril.Cerberus.Core

theorem initial_visibleObjects (freshness : Freshness.Context) (convention : CallingConvention)
    (backend : String) : (initial freshness convention backend).effects.visibleObjects = [[]] := rfl

theorem initial_callingConvention (freshness : Freshness.Context) (convention : CallingConvention)
    (backend : String) : (initial freshness convention backend).effects.callingConvention = convention := rfl

end Silmaril.Cerberus.Elaboration.State
