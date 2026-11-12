module

public import Silmaril.Proofs.Elf.Lookup.GnuHash

/-! # Lookup semantics: theorems

PROVED (standard axioms only):

* `gnuLookup_eq_scanLookup`: on a well-formed GNU hash table (`GnuHashOk`, decidable, checked
  in one linear pass by `GnuHash.wf`), ld.so's hash walk `gnuLookup` computes the declarative
  lookup `scanLookup` (`Silmaril.Proofs.Elf.Lookup.GnuHash`);
* `firstMatch_cons`, `firstMatch_allFalse`, `firstMatch_append_false`, `checkMatch_of_ne`:
  the scan rejects every symbol with another name.
-/

@[expose] public section

namespace Silmaril.Elf

/-- **ld.so's hash walk is the declarative lookup** on a well-formed hash table. -/
theorem File.gnuLookup_eq_scan {A : File} (hok : A.GnuHashOk) (r : Ref) (plt : Bool) :
    A.gnuLookup r plt = A.scanLookup r plt :=
  gnuLookup_eq_scanLookup hok r plt

end Silmaril.Elf
