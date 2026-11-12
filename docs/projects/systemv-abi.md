# System V AMD64: the ABI, C type classification and native contracts

The x86-64 System V calling convention as executable data and as contracts, beyond the INTEGER
boundary of `Silmaril.X86.SystemV` that the [translation-validation shapes](sysv-tv.md) use:
argument classification and call planning for C types, native layouts of the Cerberus type
vocabulary, typed FFI contracts, and two real compiled functions with their contracts.

It is the second wave of the C and translation-validation release, after the
[Cerberus port](cerberus.md). Layout as there: thin headers over `Silmaril.Raw.*`, with the
Raw declarations keeping their `Silmaril.*` namespaces (`Silmaril.C.Api`, `Silmaril.Machine.*`).

## Module map

| Module | What it holds |
| --- | --- |
| [`Silmaril.Machine.SystemV`](../../Silmaril/Machine/SystemV/Defs.lean) | `Realizes`, `Result`: a native implementation of a scalar C operation, over `Silmaril.C.Api` (signatures, scalar encodings, stack arguments, frames) |
| [`Silmaril.Machine.SystemV.Abi`](../../Silmaril/Machine/SystemV/Abi/Defs.lean) | AMD64 LP64 argument classification (`Class`, `merge`), call planning (`CallPlan`), `va_list` (`VaList`), specified against the psABI (x86-psABIs/x86-64-ABI@e1ce0983) |
| `….Abi.Ctypes`, `….Abi.Native`, `….Abi.DataLayout` | native layouts of the Cerberus C types (floating fields at their native sizes, not Cerberus's eight-byte shortcut); the richer native type vocabulary; agreement with `Silmaril.Data.Layout`'s psABI layout |
| `….Abi.Representation`, `….Abi.Chunks` | concrete native object representations of typed C values (`NativeValues.TypedValue`), byte chunks |
| `….Abi.Ffi`, `….Abi.Ffi.Bytes` | typed native FFI contracts over the integer machine state extended with vector, x87 and control state (observations only; an implementation proves its execution against them) |
| `….Abi.Int32Add`, `….Abi.Int32Identity` | real gcc 13.3 / clang 18.1 bytes for `int add(int, int)` and `int id(int)`, with their contracts (no compiler-emission correctness claimed) |
| `Silmaril.Machine.SystemV.VC` | the verification-condition form of the native contracts |
| `Silmaril.Machine.C.Api`, `Silmaril.Machine.CSupport` | the C API vocabulary (`Silmaril.C.Api.{Scalar,Signature,Arguments}`, `SysV.Entry/Return/Frame`) |
| `Silmaril.Machine.X86.Decompile.{SemLift,Features,Lea32,Returns}` | the byte-summary checker and the feature machine used by checked decompilation, a LEA32 check, `ret` completion |
| `Silmaril.Machine.X86.Spec.{Ensures,EnsuresSysV}` | headers re-exporting the public `Silmaril.X86.Spec.{Ensures,EnsuresSysV}` |
| [`Silmaril.Data.Layout.Cerberus`](../../Silmaril/Data/Layout/Cerberus/Defs.lean) | declarations as Cerberus C types; where `Silmaril.Data.Layout`'s System V layout and Cerberus's concrete layout agree, and where they do not (`floatDisagreement`) |
| `Silmaril.Semantics.CPort.Logic.Institution.Bridges.Contracts` | the bridge from these contracts to the institution layer |

`Silmaril.C.Api` and the public `Silmaril.X86.SystemV.CApi` are two presentations of the same
INTEGER profile (the second was promoted earlier, with its own names); they coexist.

## Main results

* `Abi.merge_comm`, `Abi.alignUp_mod`, `VaList.start_valid`, `VaList.next_valid`: the
  classification lattice and the `va_list` walk.
* `SystemV.convention_wellFormed`, `Result.readBytes`, `VC.Post.readBytes`,
  `Ffi.TotalCorrect.realizes`: contracts and their frame facts; a total FFI contract gives a
  `Realizes` certificate.
* `DataLayout.malloc_agree`, `test_agree`, `float_agree`; `Data.Layout.Cerberus.malloc_agree`,
  `floatDisagreement`: the native layout and `Silmaril.Data.Layout` agree on the test
  declarations (glibc's malloc chunk among them); Cerberus's concrete layout agrees except on
  floating types.

## Status

| | |
| --- | --- |
| **Proved** | the theorems above (kernel-checked; only `propext`, `Classical.choice`, `Quot.sound`) |
| **Trusted** | the classification and layout rules as transcribed from the psABI; the bytes of the two compiled examples (pinned compiler versions in their docstrings) |
| **Open / not claimed** | native code-generation correctness; the vector, x87 and control state have no execution semantics here; complex, vector and bit-field types are outside the native type metadata |

## Build

```sh
lake build --wfail Silmaril.Machine.SystemV.Thms Silmaril.Machine.SystemV.Abi.Thms \
  Silmaril.Machine.SystemV.Abi.Ffi.Thms Silmaril.Machine.SystemV.VC.Thms \
  Silmaril.Data.Layout.Cerberus.Thms
```

## Provenance

Original Silmaril work over the psABI specification cited in `Silmaril.Machine.SystemV.Abi`
(x86-psABIs/x86-64-ABI, commit e1ce098331da5dbd66e1ffc74162380bcc213236; specification text is
cited, not bundled). The Cerberus types are the [Cerberus port](cerberus.md)'s.
