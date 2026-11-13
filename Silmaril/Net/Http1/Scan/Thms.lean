module

public import Silmaril.Proofs.Net.Http1.Scan

/-!
# Scanning runs of bytes: laws

Proofs in `Silmaril/Proofs/Net/Http1/Scan.lean`:

* `scanWhile_ge`, `scanWhile_le`: the scan stays in its window;
* `scanWhile_run`, `scanWhile_stop`: it stops after a run of `pred` bytes, at a byte outside
  `pred`; `scanWhile_of_run`: on such input it stops exactly there;
* `sound_runThen`, `complete_runThen`: `runThen pred` is sound and complete for
  `Spec.runThen pred`, bundled as `Grammar.runThen`;
* `Grammar.delim`: a run ended by a given byte (`delim_G_iff` characterises its grammar);
  `Grammar.lit_G_eq`: a literal's grammar relates only its bytes.
-/
