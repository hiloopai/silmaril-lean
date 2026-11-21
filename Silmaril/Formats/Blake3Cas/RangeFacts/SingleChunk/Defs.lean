module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Defs

@[expose] public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk

open Silmaril.Crypto.Blake3 (Bytes)

inductive Profile where
  | combined
  | outboard
  | slice

def Profile.encoding (profile : Profile) (request : Request) (size : Nat) : Bao.Encoding :=
  match profile with
  | .combined => .combined
  | .outboard => .outboard
  | .slice => .slice (request.window size)

/-- Feed the official Bao encoder its single data field, if one is requested.
Outboard stores no data field and no pairs in this profile. -/
def encode? (profile : Profile) (request : Request) (original : Bytes) : Option Bytes :=
  Bao.encode (profile.encoding request original.length) original.length fun
    | .pair _ => none
    | .data .. => some original

def decode? (profile : Profile) (cap : Nat) (digest : Bytes) (request : Request)
    (wire original : Bytes) : Option (Response digest request) :=
  match profile with
  | .combined => decodeCombined? cap digest request wire
  | .outboard => decodeOutboard? cap digest request wire original
  | .slice => decodeSlice? cap digest request wire

end Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk
