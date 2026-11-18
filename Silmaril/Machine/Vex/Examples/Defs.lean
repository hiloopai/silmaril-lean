module

public import Silmaril.Machine.Vex.Scalar.Defs

@[expose] public section

namespace Silmaril.Machine.Vex.Fixtures

def movBytes : List UInt8 := [0x48, 0x89, 0xf8, 0xeb, 0x00]

def movLift : Raw.Block where
  address := 0x1000
  types := [64, 64]
  statements := [
    .mark 0x1000 3 0,
    .wrTmp 0 (.get 72 64),
    .put 16 (.tmp 0),
    .mark 0x1003 2 0
  ]
  next := .const 64 0x1005
  jumpKind := "Ijk_Boring"
  ipOffset := 184

def addBytes : List UInt8 := [0x48, 0x89, 0xf8, 0x48, 0x01, 0xf0, 0xeb, 0x00]

def addLift : Raw.Block where
  address := 0x1000
  types := [64, 64, 64, 64, 64]
  statements := [
    .mark 0x1000 3 0,
    .wrTmp 3 (.get 72 64),
    .mark 0x1003 3 0,
    .wrTmp 1 (.get 64 64),
    .wrTmp 0 (.op "Iop_Add64" [.tmp 3, .tmp 1]),
    .put 144 (.const 64 0x4),
    .put 152 (.tmp 3),
    .put 160 (.tmp 1),
    .put 16 (.tmp 0),
    .mark 0x1006 2 0
  ]
  next := .const 64 0x1008
  jumpKind := "Ijk_Boring"
  ipOffset := 184

def jeBytes : List UInt8 := [0x48, 0x39, 0xf7, 0x74, 0x04]

def jeLift : Raw.Block where
  address := 0x1000
  types := [64, 64, 64, 1, 64, 64, 64, 64, 64, 64, 64, 1, 1]
  statements := [
    .mark 0x1000 3 0,
    .wrTmp 2 (.get 72 64),
    .wrTmp 1 (.get 64 64),
    .put 144 (.const 64 0x8),
    .put 152 (.tmp 2),
    .put 160 (.tmp 1),
    .put 184 (.const 64 0x1003),
    .mark 0x1003 2 0,
    .wrTmp 11 (.op "Iop_CmpEQ64" [.tmp 2, .tmp 1]),
    .wrTmp 10 (.op "Iop_1Uto64" [.tmp 11]),
    .wrTmp 8 (.tmp 10),
    .wrTmp 12 (.op "Iop_64to1" [.tmp 8]),
    .wrTmp 3 (.tmp 12),
    .exit (.tmp 3) 0x1009 "Ijk_Boring" 184
  ]
  next := .const 64 0x1005
  jumpKind := "Ijk_Boring"
  ipOffset := 184

def jneBytes : List UInt8 := [0x48, 0x39, 0xf7, 0x75, 0x04]

def jneLift : Raw.Block where
  address := 0x1000
  types := [64, 64, 64, 1, 64, 64, 64, 64, 64, 64, 64, 1, 1]
  statements := [
    .mark 0x1000 3 0,
    .wrTmp 2 (.get 72 64),
    .wrTmp 1 (.get 64 64),
    .put 144 (.const 64 0x8),
    .put 152 (.tmp 2),
    .put 160 (.tmp 1),
    .put 184 (.const 64 0x1003),
    .mark 0x1003 2 0,
    .wrTmp 11 (.op "Iop_CmpEQ64" [.tmp 2, .tmp 1]),
    .wrTmp 10 (.op "Iop_1Uto64" [.tmp 11]),
    .wrTmp 8 (.tmp 10),
    .wrTmp 12 (.op "Iop_64to1" [.tmp 8]),
    .wrTmp 3 (.tmp 12),
    .exit (.tmp 3) 0x1005 "Ijk_Boring" 184
  ]
  next := .const 64 0x1009
  jumpKind := "Ijk_Boring"
  ipOffset := 184

end Silmaril.Machine.Vex.Fixtures
