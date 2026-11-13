module

public import Init.Data.String.Basic
public import Init.Data.ByteArray.Bootstrap

@[expose] public section

/-!
# Strings the kernel compares fast

`String.ofList l` stores the UTF-8 bytes of `l` as `List.utf8Encode l`, which builds its byte
array by `Array.push`, one byte at a time: the kernel takes time quadratic in the length to
reduce it (comparing two equal 1040-character `String.ofList` strings took about 4.6 s with
`decide +kernel`). `fastStr l` is the same string with its bytes given as the list
`l.flatMap String.utf8EncodeChar` (reduced in linear time; the comparison above takes about
0.05 s), and `fastStr_eq : fastStr = String.ofList`.

Quoted data (`Silmaril.Wasi.Versions.WitImport.KQuote`) is a function of the string
constructor: instantiated with `String.ofList` it is compared with the importer's output
character by character, and instantiated with `fastStr` the kernel computes on it.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- A byte list as a byte array, by its data. -/
theorem bytes_eq_toByteArray (bs : List UInt8) : (⟨⟨bs⟩⟩ : ByteArray) = bs.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

/-- `String.ofList`, with the bytes as a list the kernel reduces in linear time. -/
def fastStr (l : List Char) : String :=
  String.ofByteArray ⟨⟨l.flatMap String.utf8EncodeChar⟩⟩
    (.intro l rfl)

/-- `fastStr` is `String.ofList`. -/
theorem fastStr_eq : fastStr = String.ofList := by
  funext l
  unfold fastStr String.ofList
  congr 1

end Silmaril.Wasi.Versions.WitImport
