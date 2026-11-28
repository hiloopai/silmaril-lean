module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct

#print axioms Rows.mergeRows_typed
#print axioms Reader.readGroup_typed
#print axioms Reader.Events.read_open_error
#print axioms Reader.Events.readProjected_open_error
#print axioms Reader.Events.readSource_wire
#print axioms Reader.Events.read_wire
#print axioms Reader.Events.read_failure
#print axioms Reader.Events.readSource_complete
#print axioms Reader.Events.readProjected_wire
#print axioms Reader.Events.readSource_eq_of_complete
#print axioms Reader.Events.readProjected_reframe
