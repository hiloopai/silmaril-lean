module

public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs

/-! The two-BinaryView profile of the ordered V5 writer. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews

export OrderedWriter (Column BatchInput RecordError Error PhysicalColumn Record compile descriptorGroups
  pack bindings checkSizes)

namespace Column
export OrderedWriter.Column (int32 binary field observe length compile)
end Column

namespace BatchInput
export OrderedWriter.BatchInput (mk rowCount columns fields observe)
end BatchInput

namespace PhysicalColumn
export OrderedWriter.PhysicalColumn (mk node count parts)
end PhysicalColumn

namespace Record
export OrderedWriter.Record (mk output columns compiled packed metadataRead plan bound assigned)
end Record

namespace RecordError
export OrderedWriter.RecordError (ipc field unsupportedSchema schemaMismatch metadata metadataMismatch
  binding bindingMismatch)
end RecordError

namespace Error
export OrderedWriter.Error (ipc unsupportedSchema record readback readbackMismatch)
end Error

namespace Wire
export OrderedWriter.Wire (fieldBytes schema schemaSize)
end Wire

/-- Two view ordinals, with an optional INT32 in any position. -/
def supported (fields : List Field) : Bool :=
  fields.length ≤ 3 && fields.countP (·.kind == .view .binary) == 2 &&
    fields.all (fun field => field.kind == .view .binary || field.kind == .primitive .int32)

def checkRecord (limits : MixedFlat.Limits) (rows : Nat) (fields : List Field) :
    Except RecordError Unit :=
  OrderedWriter.checkRecord limits rows fields supported

def emitRecord (limits : MixedFlat.Limits) (input : BatchInput) :
    Except RecordError (Record limits input) :=
  OrderedWriter.emitRecord limits input supported

def emitSchema (ipc : Arrow.Limits) (fields : List Field) : Except Error KBytes :=
  OrderedWriter.emitSchema ipc fields supported

def serialize (limits : MixedFlat.Limits) (fields : List Field) (batches : List BatchInput) :
    Except Error KBytes :=
  OrderedWriter.serialize limits fields batches supported

def emit (limits : MixedFlat.Limits) (fields : List Field) (batches : List BatchInput) :
    Except Error KBytes :=
  OrderedWriter.emit limits fields batches supported

end Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews
