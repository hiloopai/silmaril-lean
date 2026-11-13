module

public import Silmaril.Wasi.Versions.WitImport.R29.Thms
public import Silmaril.Wasi.Versions.WitImport.Rename.Thms
public import Silmaril.Wasi.Versions.WitImport.RIo2.Thms
public import Silmaril.Wasi.Versions.WitImport.RCli2.Thms
public import Silmaril.Wasi.Versions.WitImport.RNet.Thms

@[expose] public section

/-!
# The resolved typing of WASI 0.2.9 is that of 0.2.12

`Silmaril.Wasi.Versions.WitImport.R29` compared the 0.2.9 and 0.2.12 tables without their type
environments. Here the whole packages are compared: exchanging the versions `0.2.9` and
`0.2.12` in every interface name (`rn29 = swapVer "0.2.9" "0.2.12"`, `Rename`) maps each 0.2.9
package onto the 0.2.12 one (`io29_rn`, `clocks29_rn`, `fs29_rn`, `sock29_rn`, `http29_rn`,
`rand29_rn`, kernel evaluation), and `wasi:cli` onto the 0.2.12 package without
`exit-with-code` (`cli29_rn`). Renaming does not change the resolved typing (`witROk_rn`), so:

* **`witROk_29`**, **`witRTrapOk_29`**: on every restriction, the typing of a 0.2.9 package is
  the typing of the 0.2.12 package it renames to.
* The 0.2.12 typing results hold for 0.2.9 as stated:
  **`ioTh_witR29`** (every trace of `P2.ioTh r` is resolved-typed against 0.2.9 `wasi:io`, traps
  admitted) and **`p2Ok_witR29`** (`P2.p2Ok` answers of the `cli`/`clocks` functions are
  resolved-typed against 0.2.9). Any other result about `witROk (rrestrict P L)` for one of
  these packages moves the same way, by `witROk_29`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit

/-- Exchange the versions `0.2.9` and `0.2.12`. -/
abbrev rn29 : Binary.IfaceName → Binary.IfaceName := swapVer "0.2.9" "0.2.12"

theorem io29_rn : rnPkg rn29 io29P = io2P := by decide +kernel
theorem clocks29_rn : rnPkg rn29 clocks29P = clocks2P := by decide +kernel
theorem fs29_rn : rnPkg rn29 fs29P = fs2P := by decide +kernel
theorem sock29_rn : rnPkg rn29 sock29P = sock2P := by decide +kernel
theorem http29_rn : rnPkg rn29 http29P = http2P := by decide +kernel
theorem rand29_rn : rnPkg rn29 rand29P = rand2P := by decide +kernel

/-- **`wasi:cli` 0.2.9 renames to 0.2.12 without `exit-with-code`.** -/
theorem cli29_rn :
    rnPkg rn29 cli29P = (cli2P.1.filter (·.1.fn != "exit-with-code"), cli2P.2) := by
  decide +kernel

/-- Restricting commutes with renaming. -/
theorem rnPkg_rrestrict (ρ : Binary.IfaceName → Binary.IfaceName) (P : RPkg) (L : List FnName) :
    rnPkg ρ (rrestrict P L) = rrestrict (rnPkg ρ P) L := by
  simp [rnPkg, rrestrict, List.filter_map, Function.comp_def]

/-- **The typing of a 0.2.9 package is that of the 0.2.12 package it renames to.** -/
theorem witROk_29 {P Q : RPkg} (h : rnPkg rn29 P = Q) (L : List FnName) (e : WEv) :
    witROk (rrestrict P L) e = witROk (rrestrict Q L) e := by
  rw [← h, ← rnPkg_rrestrict, witROk_rn (swapVer_injective _ _)]

/-- The same, traps admitted. -/
theorem witRTrapOk_29 {P Q : RPkg} (h : rnPkg rn29 P = Q) (L : List FnName) (e : WEv) :
    witRTrapOk (rrestrict P L) e = witRTrapOk (rrestrict Q L) e := by
  rw [← h, ← rnPkg_rrestrict, witRTrapOk_rn (swapVer_injective _ _)]

/-- **`P2.ioTh` is resolved-typed against 0.2.9 `wasi:io`** (traps admitted). -/
theorem ioTh_witR29 (r : P2.Reading) {t : List WEv} (h : (P2.ioTh r).Accepts t) :
    (witRTrapTh (rrestrict io29P io2L)).Accepts t := by
  have he : witRTrapTh (rrestrict io29P io2L) = witRTrapTh (rrestrict io2P io2L) := by
    unfold witRTrapTh
    rw [funext (witRTrapOk_29 io29_rn io2L)]
  rw [he]
  exact ioTh_witR r h

/-- The `cli`/`clocks`/`filesystem` slice of 0.2.9. -/
def p29P : RPkg := rappend cli29P (rappend clocks29P fs29P)

/-- On the functions of `cli2S`, the 0.2.9 slice renames to the 0.2.12 one. -/
theorem p29_rn_cli2S : rrestrict (rnPkg rn29 p29P) cli2S = rrestrict p2P cli2S := by
  decide +kernel

/-- **`P2.p2Ok` answers are resolved-typed against 0.2.9** (traps admitted), for the functions of
`cli2S`. -/
theorem p2Ok_witR29 (e : WEv) (h : P2.p2Ok e = true) :
    witRTrapOk (rrestrict p29P cli2S) e = true := by
  rw [← witRTrapOk_rn (swapVer_injective "0.2.9" "0.2.12"), rnPkg_rrestrict, p29_rn_cli2S]
  exact p2Ok_witR e h

end Silmaril.Wasi.Versions.WitImport
