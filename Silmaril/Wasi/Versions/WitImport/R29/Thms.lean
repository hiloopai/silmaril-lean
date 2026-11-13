module

public import Silmaril.Wasi.Versions.WitImport.RTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables29.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RP3.Thms

@[expose] public section

/-!
# WASI 0.2.9 against 0.2.12, as imported

The hand-written 0.2 modules were written against the 0.2.9 WIT (`P2/Io`, `P2/World`), the
imported tables were read from 0.2.12. This module compares the 0.2.9 tables of
`Silmaril.Wasi.Versions.WitImport.RTables29` / `RNetTables29` with the 0.2.12 ones, by kernel
evaluation.

* **Same functions and signatures** (`strip`, names unversioned): `io29_strip`,
  `clocks29_strip`, `fs29_strip`, `rand29_strip`, `sock29_strip`, `http29_strip`.
* `cli29_strip`: the same **except `exit-with-code`**, which 0.2.9 gates `@unstable` (the
  importer drops unstable items) and 0.2.12 marks `@since(version = 0.2.12)`.
* `wasi:random` and `wasi:cli` have no named types (`rand29P_free`, `cli29P_free`), so their
  resolved typing is the unresolved one (`witROk_free`); for `wasi:random` the two versions
  type every event alike (`witROk_rand29`), and the hand-written 0.2 random typing is the
  0.2.9 WIT typing plus the length condition (`ok2R29_eq`, from `ok2R_eq`).

Not shown: equality of the resolved typings for the packages with named types (`io`,
`clocks`, `filesystem`, `sockets`, `http`). Their environments differ in the package version
of every interface name (`@0.2.9` against `@0.2.12`), so the comparison needs a renaming
lemma for `tyOkR`; it is open.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi

theorem io29_strip : strip io29P.1 = strip io2P.1 := by decide +kernel
theorem clocks29_strip : strip clocks29P.1 = strip clocks2P.1 := by decide +kernel
theorem fs29_strip : strip fs29P.1 = strip fs2P.1 := by decide +kernel
theorem rand29_strip : strip rand29P.1 = strip rand2P.1 := by decide +kernel
theorem sock29_strip : strip sock29P.1 = strip sock2P.1 := by decide +kernel
theorem http29_strip : strip http29P.1 = strip http2P.1 := by decide +kernel

/-- **`wasi:cli` 0.2.9 is 0.2.12 without `exit-with-code`.** -/
theorem cli29_strip :
    strip cli29P.1 = (strip cli2P.1).filter (·.1.fn != "exit-with-code") := by decide +kernel

/-- `exit-with-code` is in the 0.2.12 table. -/
theorem exitWithCode_mem12 : (names (strip cli2P.1)).any (·.fn == "exit-with-code") := by
  decide +kernel

theorem rand29P_free : PkgFree rand29P = true := by decide +kernel
theorem cli29P_free : PkgFree cli29P = true := by decide +kernel

/-- **`wasi:random` 0.2.9 and 0.2.12 type every event alike.** -/
theorem witROk_rand29 (e : WEv) : witROk rand29P e = witROk rand2P e := by
  rw [witROk_free rand29P_free, witROk_free rand2P_free, rand29_strip]

/-- **The hand-written 0.2 random typing is the 0.2.9 WIT typing plus the length condition.** -/
theorem ok2R29_eq (e : WEv) : Random.ok2 e = (witROk rand29P e && len2 e) := by
  rw [witROk_rand29, ok2R_eq]

end Silmaril.Wasi.Versions.WitImport
