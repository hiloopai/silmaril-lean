module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc.Thms

open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct

#print axioms Rows.projectRows_demand
#print axioms Writer.GroupWire.slots_exact
#print axioms Writer.GroupWire.footer_exact
#print axioms Writer.serialize_construction
#print axioms Writer.certify_readback
#print axioms Writer.emit_wire
#print axioms Reader.readGroup_wire
#print axioms Reader.ToIpc.convert_optional_error
#print axioms Writer.FromIpc.convert_declaration_error
#print axioms Writer.FromIpc.round_trip
