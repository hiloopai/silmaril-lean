module

public import Silmaril.X86.Link.Blob.Defs
public import Silmaril.Project.Shapes.Elf.Defs
public meta import Lean.Elab.Term

/-!
# Pinned executables as `Blob`s, without their bytes in a source file

The executables the dynamic-linking proofs read (gcc and clang outputs that contain crt start-up
code) are committed under `examples/dyn/pinned/` (`examples/dyn/pin.sh` rebuilds them and checks
their sha256 against `examples/dyn/pins.txt`); `Silmaril.Elf.Link.Dyn.Pin.Bytes` holds each file
as `include_bytes`.

`blob_of% n` elaborates, for such an `include_bytes` constant `n := ⟨decode c len cs⟩`, to the
`Blob` `⟨chunksVal c len cs, chunksLen c len cs⟩` (silmaril's value of the included file:
`Silmaril.Project.Shapes.ofBytes_decode` proves it is `Blob.ofBytes` of the file). The chunk
literals enter the elaborated term and the `.olean`, never a source file. A kernel read of the
`Blob` costs a few big-number operations per 4 KiB chunk, so `decide +kernel` over it works as
over a `Blob` literal.

Trusted: the `include_bytes` elaborator (its chunk literals are the file, which silmaril checks by
example), and the sha256 check of the fetched file. A different file at the path cannot make a
false theorem about the pinned one; it makes statements about the other file, and in practice
makes the `decide +kernel` checks fail.
-/

open Lean Elab Term Meta in
/-- `blob_of% n`: the `Blob` of the `include_bytes` constant `n` (`n := ⟨IncludeBytes.decode c len
cs⟩`), as `⟨chunksVal c len cs, chunksLen c len cs⟩`. -/
elab "blob_of% " n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let some v := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "blob_of%: {name} has no value"
  match v.getAppFnArgs with
  | (``Silmaril.Formats.Bytes.mk, #[d]) =>
    match d.getAppFnArgs with
    | (``Silmaril.IncludeBytes.decode, #[c, len, cs]) =>
      return mkApp2 (mkConst ``Silmaril.X86.Link.Blob.mk)
        (mkApp3 (mkConst ``Silmaril.Project.Shapes.chunksVal) c len cs)
        (mkApp3 (mkConst ``Silmaril.Project.Shapes.chunksLen) c len cs)
    | _ => throwError "blob_of%: {name} is not `⟨include_bytes …⟩`"
  | _ => throwError "blob_of%: {name} is not `⟨include_bytes …⟩`"
