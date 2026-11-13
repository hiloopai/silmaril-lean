module

public import Silmaril.Wasm.Tools.Gen.WitSmith.Defs
public import Silmaril.Wasm.Tools.Gen.Wit.Thms

/-!
# `wasm-tools wit-smith`: specification

* `witSmith_valid`: **every generated universe is a valid WIT universe** (`Silmaril.Wasm.Wit.Valid`)
  that uses only the flags of the command line;
* `witSmith_lift`: it is valid at every larger set of flags.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.WitSmith

open Silmaril.Wasm.Wit Silmaril.Wasm.Tools.Gen.Wit

/-- **Every generated universe is valid at the flags.** -/
theorem witSmith_valid (cfg : Config) (seed : ByteArray) :
    WitValidIn cfg.feat (witSmith cfg seed) :=
  (witGen cfg.feat).valid _ _

/-- Valid at every larger set of flags. -/
theorem witSmith_lift (cfg : Config) {G : WitFeat} (h : cfg.feat.le G) (seed : ByteArray) :
    WitValidIn G (witSmith cfg seed) :=
  witValid_mono h (witSmith_valid cfg seed)

end Silmaril.Wasm.Tools.Gen.WitSmith
