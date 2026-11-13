module

public import Silmaril.Wasm.Jco.Styles.EncExact.Thms
public import Silmaril.Wasm.Jco.Styles.Lime.Thms
public import Silmaril.Wasm.Jco.Styles.Wide.Thms
public import Silmaril.Wasm.Jco.Example.Defs

/-!
# FFI styles: litmus checks

Closed evaluations of the codecs and layouts of `Silmaril.Wasm.Jco.Styles`, checked by `decide`
(kernel evaluation):

* UTF-16 of `"aé😀"`: four code units; the astral character is a surrogate pair. Decoding gives
  the string back. An unpaired surrogate is rejected.
* `NoShrink`: an ASCII string is stored by one exact allocation in every encoding; `"é"` is not
  (UTF-16 shrinks from 4 to 2 bytes).
* The layout of `(u8, u32, u16)`: offsets 0, 4, 8, size 12, alignment 4.
* The Lime1 adaptor of the litmus world `Example.exMeta` has one function per world function plus
  `cabi_realloc`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

example : (utf16Bytes "aé😀").length = 8 := by decide
example : decodeUtf16 (utf16Bytes "aé😀") = some "aé😀" := by decide
example : decodeUtf16 [0x00, 0xD8] = none := by decide
example : NoShrink .utf16 "abc" = true ∧ NoShrink .latin1Utf16 "abc" = true := by decide
example : NoShrink .utf16 "é" = false ∧ NoShrink .latin1Utf16 "é" = false := by decide
example : fieldOffs 0 [1, 4, 2] = [0, 4, 8] ∧ tupleSize [1, 4, 2] = 12 ∧
    tupleAlign [1, 4, 2] = 4 := by decide
example : (adaptorLime Example.exMeta).funcs.length = Example.exMeta.world.length + 1 := by decide

end Silmaril.Wasm.Jco
