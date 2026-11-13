module

public import Silmaril.Wasm.Wit.Project.Inv.Defs
public import Silmaril.Proofs.Wasm.Wit.ProjectInv

/-!
# Invariance of the extended projection: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.ProjectInv`:

* `projectX_norm : projectX (norm c) = projectX c` and
  `projectX_read_print : (read (print c)).bind projectX = projectX c`: like `project`,
  `projectX` is well defined on component WAT. The look-ahead for resource exports
  sees normalised names, which `normName` maps back (`resExport_map_nfSec`);
* `projectX_stripCode : ascribed c = true → projectX (stripCode c) = projectX c`: code
  does not change the extended projection of a component whose function and
  component exports carry type ascriptions;
* `projectX_stripCode_resComponent`: the hypothesis is needed. `resComponent` exports
  its lifted constructor without ascription; `projectX` reads the type from the
  `canon lift`, which `stripCode` drops, so `projectX (stripCode resComponent) = none`
  while `projectX resComponent` is defined. (`project` has no such case: it rejects
  every unascribed non-type export.)
-/
