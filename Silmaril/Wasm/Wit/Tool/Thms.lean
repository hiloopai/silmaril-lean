module

public import Silmaril.Wasm.Wit.Tool.Defs
public import Silmaril.Proofs.Wasm.Wit.Tool
public import Silmaril.Proofs.Wasm.Wit.Tool.Complete

/-!
# The core of `wasm-wit`: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.Tool`; every theorem is proved, with no axiom
beyond Lean's.

Component WAT (`print`, `parse`):

* `printWat_eq_ok`, `parseWat_eq_ok`: the subcommands are the verified printer
  and reader composed with the verified binary parser and encoder;
* `parse_parseWat_printWat`: bytes printed and parsed back parse to the normal
  form `Wat.norm c` of the component (`Wat.read_print`, `Binary.parse_encode`);
* `printWat_parseWat_printWat`: `print ∘ parse ∘ print = print` on bytes.

WIT packages (`decode`, `encode`, `check`):

* `decode_eq_ok`, `check_eq_ok`: what the fields of a `check` report mean
  (`valid ↔ Package.Valid`, `unique ↔ NamesUnique`, `canonical ↔ p.canon = p`,
  `reencoded` is `encodePackage` in the environment the binary shows, `fixpoint`
  compares with the input);
* `reencode_sound`: if `check` finds the package valid with distinct names, the
  bytes `encode` writes decode to `p.canon` (`decodePackage_encodePackage_canon`);
* `canonical_of_fixpoint`: a fixed point of `encode` is canonical;
* `check_ok_sound`: bytes passing every check are `encodePackage env p` for a
  valid, canonical `p` with distinct names, decode to `p`, and `encode` gives
  them back (`reencode b = .ok b`).

Projection (`project`):

* `projectWat_printWat`: a binary and its WAT project to the same world
  (`Project.project_read_print`).

Completeness of `check` (`Silmaril.Proofs.Wasm.Wit.Tool.Complete`):

* `check_ok_iff`: `check` passes iff the bytes decode to a valid canonical package
  with distinct names whose encoding in the environment the bytes show
  (`decodeEnv`) is the bytes: sound, and complete relative to `decodeEnv`;
* `check_complete_of_env`: `check` passes on `encodePackage deps p` (valid,
  canonical, distinct names) when `decodeEnv` of the bytes validates `p` and
  re-encodes it to the same bytes;
* `Task.check_complete` (open, frozen): without those two conditions. No
  counterexample is known; `#guard`s check the elaboration goldens.

The WIT text path (`encode PKG.wit`), `embed` and the `projectX` commands are in
`Silmaril.Wasm.Wit.Tool.Source.Thms`.
-/
