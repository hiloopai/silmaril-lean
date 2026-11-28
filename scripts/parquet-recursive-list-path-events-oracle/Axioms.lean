module

import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Thms

open Silmaril.Formats.Parquet.Reader.Recursive

#print axioms Groups.events_wire
#print axioms Groups.events_eq_of_complete
#print axioms Prefix.failure
#print axioms Prefix.groups
#print axioms Prefix.complete

open Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events

#print axioms read_open_error
#print axioms readProjected_open_error
#print axioms readSource_wire
#print axioms read_wire
#print axioms read_failure
#print axioms readSource_complete
#print axioms readProjected_preserves
#print axioms readSource_eq_of_complete
#print axioms readProjected_reframe
