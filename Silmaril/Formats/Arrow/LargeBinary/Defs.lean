module

public import Silmaril.Formats.Arrow.Binary.Defs

/-! Checked signed i64 offsets for Arrow LargeBinary. Bitmap, descriptor
geometry and the opaque observation carrier are shared with plain Binary. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeBinary

abbrev Buffers := Binary.Buffers
abbrev Column := Binary.Column
abbrev Error := Binary.Error

def readOffset := Binary.Offsets.readOffset .i64
def readSlot := Binary.Offsets.readSlot .i64
def readColumn := Binary.Offsets.readColumn .i64

def OffsetWire := Binary.Offsets.OffsetWire .i64
def SlotWire := Binary.Offsets.SlotWire .i64
def ColumnWire := Binary.Offsets.ColumnWire .i64

end Silmaril.Formats.Arrow.LargeBinary
