module

public import Silmaril.Wasm.Tools.Framing.Defs

/-!
# `wasm-tools strip`

`wasm-tools strip` (wasm-tools 1.262.0, `src/bin/wasm-tools/strip.rs`) copies a binary section
by section through wasmparser's `Parser`, dropping the custom sections a predicate selects and
re-encoding every kept section with a minimal size field (`wasm_encoder::RawSection`); nested
modules and components of a component are stripped recursively and re-encoded the same way.

* `Mode`: `--all`, `--delete REGEX…` or the default (keep `name`, `component-type:*` and
  `dylink.0`); `Mode.removes isMatch m n`: the custom section `n` is removed. The regex matcher
  is a parameter (`isMatch pattern name`), so this topic does not depend on a regex engine;
* `stripF`: the section list of one encoding, recursively; `strip rm b`: the whole file.

`Thms`: on a module, the output's sections are exactly the kept input sections in order with
minimal sizes (`strip_module`), the output frames back to them (`strip_module_frames`), and
only custom sections are removed (`strip_module_noncustom`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Strip

open Silmaril.Wasm.Binary (Bytes)
open Silmaril.Wasm.Tools.Framing

/-- Which custom sections `strip` removes. -/
inductive Mode where
  | all
  | delete (patterns : List String)
  | dflt
  deriving Repr, DecidableEq

/-- The command line's mode: `--all` wins, then `--delete` (if any pattern), then the default. -/
def Mode.ofArgs (all : Bool) (patterns : List String) : Mode :=
  if all then .all else if patterns.isEmpty then .dflt else .delete patterns

/-- **Is the custom section `n` removed?** (`strip_custom_section`). -/
def Mode.removes (isMatch : String → String → Bool) : Mode → String → Bool
  | .all, _ => true
  | .delete ps, n => ps.any fun p => isMatch p n
  | .dflt, n => n != "name" && !n.startsWith "component-type:" && n != "dylink.0"

/-- Is the section kept? (Not a custom section, or a custom section whose name is kept; a custom
section without a readable name is kept, but `frame` has already refused those.) -/
def keepSec (rm : String → Bool) (s : RawSec) : Bool :=
  if s.id = 0 then
    match customName s.content with
    | .ok (n, _) => !rm n
    | .error _ => true
  else true

/-- **Strip a section list** of encoding `e`, recursing into nested modules and components
(`fuel` bounds the nesting). -/
def stripF (rm : String → Bool) : Nat → Enc → List RawSec → Except String (List RawSec)
  | _, _, [] => .ok []
  | fuel, e, s :: ss => do
    let rest ← stripF rm fuel e ss
    if !keepSec rm s then return rest
    match nestedEnc e s, fuel with
    | some e', fuel' + 1 =>
      let (_, inner) ← frame (some e') s.content
      let inner' ← stripF rm fuel' e' inner
      let c := e'.header ++ join inner'
      return { s with content := c }.canon :: rest
    | some _, 0 => .error "nesting too deep"
    | none, _ => return s.canon :: rest
termination_by fuel _ ss => (fuel, ss.length)

/-- **`wasm-tools strip`** on the bytes of a binary. -/
def strip (rm : String → Bool) (b : Bytes) : Except String Bytes := do
  let (e, ss) ← frame none b
  let ss' ← stripF rm b.length e ss
  return e.header ++ join ss'

end Silmaril.Wasm.Tools.Strip
