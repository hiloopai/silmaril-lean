module

public import Silmaril.Wasm.Tools.Gen.Wit.Defs
public import Silmaril.Wasm.Tools.Component.WitPkg.Defs

/-!
# `wasm-tools wit-smith`: the WIT instance of the generator API at the flags of the CLI

`witSmith cfg seed` is the WIT generator `Silmaril.Wasm.Tools.Gen.Wit.witGenRun cfg.feat` (every
output valid at the flags: `Wit.Valid` and inside `cfg.feat`) run on the seed bytes, read as
a SplitMix64 state (`rngOfBytes`), with a size from the seed length and `--max-pkg-items`.
`witSmithBytes` encodes its package as a WIT package component, exactly as
`wasm-tools component wit --wasm` does on WIT text (`Silmaril.Wasm.Wit.Tool.encodeDocs`, then
the async renaming and producers retagging of `Silmaril.Wasm.Tools.Component.Cmd.witWasmOfSrc`).

Upstream generates with `wit-smith`'s own decision tree: the same seed gives another package
(by design: only the CLI contract and the validity of the output are shared).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.WitSmith

open Silmaril.Wasm.Wit Silmaril.Wasm.Tools.Gen.Wit

/-- The options of `wasm-tools wit-smith` this generator reads. -/
structure Config where
  /-- The feature flags (`--async`, `--futures`, `--streams`, `--error-context`,
  `--fixed-length-lists`). -/
  feat : WitFeat := {}
  /-- `--max-pkg-items`: bounds the size. -/
  maxPkgItems : Nat := 10
  deriving Repr, Inhabited

/-- A SplitMix64 state from seed bytes (every byte mixed in). -/
def rngOfBytes (b : ByteArray) : Rng :=
  ⟨b.foldl (fun h x => mix64 (h ^^^ x.toUInt64 ^^^ golden)) (UInt64.ofNat b.size)⟩

/-- The size of a run: grows with the seed, bounded by `--max-pkg-items`. -/
def sizeOf (cfg : Config) (seed : ByteArray) : Nat := min (4 * cfg.maxPkgItems) (4 + seed.size / 4)

/-- **`wit-smith`'s universe**: the checked WIT generator at the flags. -/
def witSmith (cfg : Config) (seed : ByteArray) : Universe :=
  witGenRun cfg.feat (rngOfBytes seed) (sizeOf cfg seed)

/-- The text of the generated package (`wit-smith` prints it with `-v`). -/
def witText (cfg : Config) (seed : ByteArray) : String :=
  match witSmith cfg seed with
  | P :: _ => Silmaril.Wasm.Wit.Text.print ⟨P, []⟩
  | [] => ""

/-- **The bytes `wasm-tools wit-smith` writes**: the WIT package component of the generated
package, as `component wit --wasm` encodes WIT text. -/
def witSmithBytes (cfg : Config) (seed : ByteArray) : Except String ByteArray :=
  match witSmith cfg seed with
  | [P] => (fun b => Silmaril.Wasm.Tools.Component.Cmd.retag (Silmaril.Wasm.Wac.AsyncNames.fixBytes b)) <$>
      Silmaril.Wasm.Wit.Tool.encodeDocs ⟨P, []⟩ [] []
  | _ => .error "wit-smith: expected one package"

end Silmaril.Wasm.Tools.Gen.WitSmith
