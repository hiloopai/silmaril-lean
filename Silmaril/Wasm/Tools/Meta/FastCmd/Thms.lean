module

public import Silmaril.Wasm.Tools.Meta.Fast.Defs
public import Silmaril.Wasm.Tools.Meta.FastCmd.Defs
public import Silmaril.Wasm.Tools.Meta.Leb.Thms
public import Silmaril.Wasm.Tools.Meta.Frame.Thms
import Silmaril.Proofs.Wasm.Tools.Meta.FastMeta

/-!
# The array walk and the array commands compute their specifications

## The walk

* `toList_eq`: `ByteArray.toList` lists the data; `sl_eq`: a slice is the corresponding part of
  that list; `sl_cons`, `sl_nil`, `sl_drop`, `sl_take`, `sl_length`: the slice algebra.
* `rdU32_spec`: **the array reader `rdU32` agrees with the list reader `readU32`**: when it
  reads `n` and stops at `p`, `readU32` reads `n` from the slice and leaves the slice from `p`
  (and `i < p ≤ j`); when it fails, `readU32` fails.
* `parseBinaryB_spec`: **the whole array walk `parseBinaryB` succeeds exactly when the list walk
  `parseBinary` does on the array's bytes, with the same items under `ItemB.toItem`** (proofs
  in `Silmaril/Proofs/Wasm/Tools/Meta/FastWalk.lean`, by induction on the fuel: the header, section framing, every section
  check, the function bodies read past the section end and checked after, the 1 GiB limit, and
  nested units with a declared end, including truncated ones, which never succeed).

## The commands

* `demangleB_spec`: **`wasm-tools demangle` as run (`demangleB`, over a `ByteArray`, copying
  sections from the input) succeeds exactly when the list specification `demangle` does, with
  the same output bytes.** The proof (`Silmaril/Proofs/Wasm/Tools/Meta/FastCmd.lean`) uses the
  walk theorem `parseBinaryB_spec`, that every section the walk reports lies inside the input,
  and that copying a section (`pushRawSec`) appends exactly `rawSec id body`.

* `payloadOfB_spec`: **`metadata show` as run (`payloadOfB`) succeeds exactly when the list
  specification `payloadOf` does, with the same payload tree** (names, producers, OCI fields,
  dependencies and byte ranges of every module and component, nested ones included).
* `addMetadataB_spec`: **`metadata add` as run (`addMetadataB`) succeeds exactly when the list
  specification `addMetadata` does, with the same output bytes.**

Both proofs (`Silmaril/Proofs/Wasm/Tools/Meta/FastMeta.lean`) add to the walk theorem a layout
lemma (`secs_lay`: the items of a successful array walk lie one after the other, so the
positions the parser records are the offsets the list walk computes from item lengths), the
custom-section name filters (`readCustom_other`, `addSec_other`: a section outside `metaNames`
or `addNames` leaves the metadata unchanged or is copied raw), and the agreement of the copy
of nested units (`pushRawItems_data`) and of the appended OCI fields (`forIn_rel`).
Error messages are not part of the statements (they are tested against upstream).

The proofs are in `Silmaril/Proofs/Wasm/Tools/Meta/{Fast,FastWalk,FastCmd,FastMeta}.lean`; this
header imports them with a plain import and restates the theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

theorem toList_eq (ba : ByteArray) : ba.toList = ba.data.toList :=
  Silmaril.Proofs.Wasm.Tools.Meta.toList_eq ba

theorem sl_eq (ba : ByteArray) (i j : Nat) : sl ba i j = (ba.data.toList.drop i).take (j - i) :=
  Silmaril.Proofs.Wasm.Tools.Meta.sl_eq ba i j

theorem sl_cons (ba : ByteArray) (i j : Nat) (h : i < j) (hj : j ≤ ba.size) :
    sl ba i j = byteAt ba i :: sl ba (i + 1) j :=
  Silmaril.Proofs.Wasm.Tools.Meta.sl_cons ba i j h hj

theorem sl_nil (ba : ByteArray) (i j : Nat) (h : j ≤ i) : sl ba i j = [] :=
  Silmaril.Proofs.Wasm.Tools.Meta.sl_nil ba i j h

theorem sl_drop (ba : ByteArray) (i j n : Nat) : (sl ba i j).drop n = sl ba (i + n) j :=
  Silmaril.Proofs.Wasm.Tools.Meta.sl_drop ba i j n

theorem sl_take (ba : ByteArray) (i j n : Nat) : (sl ba i j).take n = sl ba i (min j (i + n)) :=
  Silmaril.Proofs.Wasm.Tools.Meta.sl_take ba i j n

theorem sl_length (ba : ByteArray) (i j : Nat) (hj : j ≤ ba.size) : (sl ba i j).length = j - i :=
  Silmaril.Proofs.Wasm.Tools.Meta.sl_length ba i j hj

/-- **The array reader agrees with the list reader.** -/
theorem rdU32_spec (ba : ByteArray) (j i : Nat) (hj : j ≤ ba.size) :
    match rdU32 ba j i with
    | .ok (n, p) => readU32 (sl ba i j) = .ok (n, sl ba p j) ∧ i < p ∧ p ≤ j
    | .error _ => ∃ e, readU32 (sl ba i j) = .error e :=
  Silmaril.Proofs.Wasm.Tools.Meta.rdU32_spec ba j i hj

/-- The items of the array walk, as the list walk reports them. -/
def itemsOf (ba : ByteArray) (r : Enc × List ItemB) : Enc × List Item :=
  (r.1, r.2.map (ItemB.toItem ba))

/-- **The array walk agrees with the list walk**: `parseBinaryB` succeeds exactly when
`parseBinary` does on the array's bytes, and then with the same items (`ItemB.toItem`). The
array walk reads like wasmparser (the count and bodies of a code section past the section's
end, nested units with a declared end) and reports other errors; the proof shows these
differences never change which inputs are accepted or what is read. -/
theorem parseBinaryB_spec (ba : ByteArray) :
    (parseBinaryB ba).toOption.map (itemsOf ba) = (parseBinary ba.data.toList).toOption :=
  (Silmaril.Proofs.Wasm.Tools.Meta.parseBinaryB_spec_raw ba).symm

end Silmaril.Wasm.Tools.Meta

namespace Silmaril.Wasm.Tools.Meta.Demangle

/-- **`demangleB` computes `demangle`.** -/
theorem demangleB_spec (ba : ByteArray) :
    (demangleB ba).toOption.map (·.data.toList) = (demangle ba.data.toList).toOption :=
  (Silmaril.Proofs.Wasm.Tools.Meta.demangleB_spec_raw ba).symm

end Silmaril.Wasm.Tools.Meta.Demangle

namespace Silmaril.Wasm.Tools.Meta.Metadata

/-- **`payloadOfB` computes `payloadOf`.** -/
theorem payloadOfB_spec (ba : ByteArray) :
    (payloadOfB ba).toOption = (payloadOf ba.data.toList).toOption :=
  Silmaril.Proofs.Wasm.Tools.Meta.payloadOfB_spec_raw ba

/-- **`addMetadataB` computes `addMetadata`.** -/
theorem addMetadataB_spec (a : Add) (ba : ByteArray) :
    (addMetadataB a ba).toOption.map (·.data.toList) = (addMetadata a ba.data.toList).toOption :=
  Silmaril.Proofs.Wasm.Tools.Meta.addMetadataB_spec_raw a ba

end Silmaril.Wasm.Tools.Meta.Metadata

end
