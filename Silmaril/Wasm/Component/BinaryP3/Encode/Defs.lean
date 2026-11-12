module

public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
# Component binaries with async built-ins: an encoder

`Encode.ast c` writes `c` with minimal LEB128 numbers, failing (`none`) only on
numbers, lengths or sizes of `2 ^ 32` or more. Productions other than `canon`,
sections and components are `Silmaril.Wasm.Component.Binary.Encode`'s. The round trip
`parse (encode c) = ok c` is `Silmaril.Wasm.Component.BinaryP3.parse_encode`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3.Encode

open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Parse.ByteParse.Enc (u32 sized)
open Silmaril.Wasm.Component.Binary (preambleBytes)
open Silmaril.Wasm.Component.Binary.Encode (vec canonOpt resultList coreValType name)

/-- `async?`/`sh?`. -/
def flag (b : Bool) : Bytes := if b then [0x01] else [0x00]

def opts (os : List Binary.CanonOpt) : Option Bytes := vec canonOpt os

/-- A tag and one `u32`. -/
def tagU32 (tag : UInt8) (n : Nat) : Option Bytes := (tag :: ·) <$> u32 n

/-- A tag, a type index and options. -/
def tagU32Opts (tag : UInt8) (n : Nat) (os : List Binary.CanonOpt) : Option Bytes := do
  let a ← u32 n
  let b ← opts os
  pure (tag :: (a ++ b))

/-- A tag, a type index and a flag. -/
def tagU32Flag (tag : UInt8) (n : Nat) (f : Bool) : Option Bytes :=
  (fun a => tag :: (a ++ flag f)) <$> u32 n

def canon : Canon → Option Bytes
  | .lift f os t => do
    let a ← u32 f
    let b ← opts os
    let c ← u32 t
    pure (0x00 :: ([0x00] ++ ((a ++ b) ++ c)))
  | .lower f os => do
    let a ← u32 f
    let b ← opts os
    pure (0x01 :: ([0x00] ++ (a ++ b)))
  | .resourceNew t => tagU32 0x02 t
  | .resourceDrop t => tagU32 0x03 t
  | .resourceRep t => tagU32 0x04 t
  | .backpressureInc => some [0x24]
  | .backpressureDec => some [0x25]
  | .taskReturn r os => do
    let a ← resultList r
    let b ← opts os
    pure (0x09 :: (a ++ b))
  | .taskCancel => some [0x05]
  | .contextGet t i => (fun a => 0x0a :: (coreValType t ++ a)) <$> u32 i
  | .contextSet t i => (fun a => 0x0b :: (coreValType t ++ a)) <$> u32 i
  | .subtaskCancel f => some (0x06 :: flag f)
  | .subtaskDrop => some [0x0d]
  | .streamNew t => tagU32 0x0e t
  | .streamRead t os => tagU32Opts 0x0f t os
  | .streamWrite t os => tagU32Opts 0x10 t os
  | .streamCancelRead t f => tagU32Flag 0x11 t f
  | .streamCancelWrite t f => tagU32Flag 0x12 t f
  | .streamDropReadable t => tagU32 0x13 t
  | .streamDropWritable t => tagU32 0x14 t
  | .streamForward t => tagU32 0x2e t
  | .futureNew t => tagU32 0x15 t
  | .futureRead t os => tagU32Opts 0x16 t os
  | .futureWrite t os => tagU32Opts 0x17 t os
  | .futureCancelRead t f => tagU32Flag 0x18 t f
  | .futureCancelWrite t f => tagU32Flag 0x19 t f
  | .futureDropReadable t => tagU32 0x1a t
  | .futureDropWritable t => tagU32 0x1b t
  | .futureForward t => tagU32 0x2f t
  | .errorContextNew os => (0x1c :: ·) <$> opts os
  | .errorContextDebugMessage os => (0x1d :: ·) <$> opts os
  | .errorContextDrop => some [0x1e]
  | .waitableSetNew => some [0x1f]
  | .waitableSetWait m => (fun a => 0x20 :: ([0x00] ++ a)) <$> u32 m
  | .waitableSetPoll m => (fun a => 0x21 :: ([0x00] ++ a)) <$> u32 m
  | .waitableSetDrop => some [0x22]
  | .waitableJoin => some [0x23]
  | .threadIndex => some [0x26]
  | .threadNewIndirect ft tbl => do
    let a ← u32 ft
    let b ← u32 tbl
    pure (0x27 :: (a ++ b))
  | .threadResumeLater => some [0x28]
  | .threadSuspend => some [0x29, 0x00]
  | .threadYield => some [0x0c, 0x00]
  | .threadSuspendThenResume => some [0x2a, 0x00]
  | .threadYieldThenResume => some [0x2b, 0x00]
  | .threadSuspendThenPromote => some [0x2c, 0x00]
  | .threadYieldThenPromote => some [0x2d, 0x00]
  | .threadSpawnRef sh ft => (fun a => 0x40 :: (flag sh ++ a)) <$> u32 ft
  | .threadSpawnIndirect sh ft tbl => do
    let a ← u32 ft
    let b ← u32 tbl
    pure (0x41 :: ((flag sh ++ a) ++ b))
  | .threadAvailableParallelism sh => some (0x42 :: flag sh)

mutual
def section_ : Section → Option Bytes
  | .custom n d => do
    let a ← name n
    let s ← sized (a ++ d.data.toList)
    pure (0x00 :: s)
  | .coreModule m => do
    let s ← sized m.data.toList
    pure (0x01 :: s)
  | .coreInstances xs => Binary.Encode.vecSection 0x02 Binary.Encode.coreInstanceExpr xs
  | .coreTypes xs => Binary.Encode.vecSection 0x03 Binary.Encode.coreType xs
  | .component c => do
    let b ← ast c
    let s ← sized b
    pure (0x04 :: s)
  | .instances xs => Binary.Encode.vecSection 0x05 Binary.Encode.instanceExpr xs
  | .aliases xs => Binary.Encode.vecSection 0x06 Binary.Encode.alias_ xs
  | .types xs => Binary.Encode.vecSection 0x07 Binary.Encode.defType xs
  | .canons xs => Binary.Encode.vecSection 0x08 canon xs
  | .start st => do
    let b ← Binary.Encode.start st
    let s ← sized b
    pure (0x09 :: s)
  | .imports xs => Binary.Encode.vecSection 0x0a Binary.Encode.import_ xs
  | .exports xs => Binary.Encode.vecSection 0x0b Binary.Encode.export_ xs
  | .values xs => Binary.Encode.vecSection 0x0c Binary.Encode.value xs

def sections : List Section → Option Bytes
  | [] => some []
  | s :: ss => do
    let a ← section_ s
    let b ← sections ss
    pure (a ++ b)

def ast : Ast → Option Bytes
  | .mk ss => do
    let b ← sections ss
    pure (preambleBytes ++ b)
end

end Encode

/-- Encode a component binary. -/
def encode (c : Ast) : Option ByteArray := (Encode.ast c).map fun l => ⟨l.toArray⟩

end Silmaril.Wasm.Component.BinaryP3
