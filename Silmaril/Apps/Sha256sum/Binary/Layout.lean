module

public import Silmaril.Crypto.X86.Sha256O2.Image

/-! # Where `sha256sum-min` puts the pilot `sha256_compress`

The binary target `sha256sum-min` (research note `binary.md`; SHA-256 `elfSha256`) links
the 459 clang 18.1.3 `-O2` bytes of the pilot `sha256_compress` unchanged apart from its
one PC32 displacement, at `textBase`, with the K table at `rodataBase`. So the bytes it
loads there should be `Sha256O2.image textBase rodataBase`; the lifted transcription
`Binary.Compress` checks exactly that equation in the kernel (`bytes_eq_linkedImage`). -/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary

open Silmaril.X86 (Word)
open Silmaril.Process (Byte)

/-- SHA-256 of the ELF file `sha256sum-min`. -/
def elfSha256 : String := "22fa6345cc5bed08f07d4d5a0836885118259a73402470e4d7f7a7a81ad42817"

/-- The address of `sha256_compress` in `sha256sum-min`. -/
def textBase : Word := 0x405200#64

/-- The address of `sha256_compress_K` in `sha256sum-min`. -/
def rodataBase : Word := 0x407f10#64

/-- The pilot image relocated to this layout. -/
def linkedImage : List Byte := Silmaril.Crypto.X86.Sha256O2.image textBase rodataBase

end Silmaril.Apps.Sha256sum.Binary
