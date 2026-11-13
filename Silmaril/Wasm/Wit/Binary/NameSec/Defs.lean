module

public import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
# The `component-name` custom section

The name section of components (`Binary.md`, "Name Section", component-model
`8505ba7`): subsections, each `id size contents`,

```
componentnamesubsec ::= 0x00 size name
sortnamesubsec      ::= 0x01 size sort namemap     namemap ::= vec(idx name)
```

with a verified grammar (`nameSecG`) and an encoder. wit-component writes no
name section for a WIT package; components built from WIT (and the
`component-type` payload's builder) may carry one.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary
open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes)

/-- A subsection of the `component-name` section. -/
inductive NameSub where
  /-- `0x00`: the component's own name. -/
  | component (n : String)
  /-- `0x01`: names of the indices of one sort. -/
  | sort (s : ItemSort) (names : List (Nat × String))
  deriving Repr, DecidableEq, Inhabited

section
open Silmaril.Parse.ByteParse.Grammar

def nameAssocG : Grammar (Nat × String) := u32.seq name

def nameMapG : Grammar (List (Nat × String)) := vec nameAssocG (seq_nonEmpty u32_nonEmpty)

def nameSubG : Grammar NameSub := tagged "name subsection" fun b => match b.toNat with
  | 0x00 => some ((sizedBy name).map .component)
  | 0x01 => some ((sizedBy (sortG.seq nameMapG)).map fun p => .sort p.1 p.2)
  | _ => none

/-- The contents of a `component-name` section: subsections to the end. -/
def nameSecG : GrammarE (List NameSub) := GrammarE.items nameSubG (tagged_nonEmpty _ _)
end

def nameAssocEnc (p : Nat × String) : Option Bytes := do
  let a ← Silmaril.Parse.ByteParse.Enc.u32 p.1
  let b ← Silmaril.Parse.ByteParse.Enc.name p.2
  pure (a ++ b)

def NameSub.encode : NameSub → Option Bytes
  | .component n => do
    let b ← Silmaril.Parse.ByteParse.Enc.name n
    let s ← Silmaril.Parse.ByteParse.Enc.sized b
    pure (0x00 :: s)
  | .sort srt ns => do
    let m ← Silmaril.Parse.ByteParse.Enc.vec nameAssocEnc ns
    let s ← Silmaril.Parse.ByteParse.Enc.sized (Encode.sort srt ++ m)
    pure (0x01 :: s)

def encodeNameSubs : List NameSub → Option Bytes
  | [] => some []
  | s :: ss => do
    let a ← s.encode
    let b ← encodeNameSubs ss
    pure (a ++ b)

/-- Read the contents of a `component-name` section. -/
def parseNameSec (b : ByteArray) : Except Silmaril.Parse.ByteParse.Error (List NameSub) :=
  Silmaril.Parse.ByteParse.runAll nameSecG.parse b

end Silmaril.Wasm.Wit.Binary
