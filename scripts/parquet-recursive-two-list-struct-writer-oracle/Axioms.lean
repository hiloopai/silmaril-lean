module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Thms

open Silmaril.Formats.Parquet.RecursiveSchema

#print axioms ListPath.Writer.GroupWire.footer_exact
#print axioms TwoListStruct.Reader.readGroup_wire
#print axioms TwoListStruct.Reader.readAll_wire
#print axioms TwoListStruct.Writer.GroupWire.footer_exact
#print axioms TwoListStruct.Writer.serialize_construction
#print axioms TwoListStruct.Writer.certify_readback
#print axioms TwoListStruct.Writer.emit_wire
