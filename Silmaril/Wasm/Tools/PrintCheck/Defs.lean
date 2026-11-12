module

public import Silmaril.Wasm.Tools.Text.Defs

/-!
# Fast paths of the `print` check and of `parse`, equal to the specification functions

`print` checks its text by reading it back with silmaril-lean's certified elaborator
(`Print.check`), and `parse` reads its input with the same elaborator; on multi-megabyte
modules almost all the time is spent in that elaborator (`Wat.Source.module?`), which
elaborates every module field twice (a first pass under a provisional identifier context, a
second under the refined one).

`moduleFast? k x` is `module? x` without its certificate, with each of the two passes run in
parallel over chunks of `k` fields (`parMapM`: one `Task` per chunk; a task is a pure value,
`(Task.spawn f).get = f ()`). `Silmaril.Wasm.Tools.PrintCheck.Thms.moduleFast?_eq` proves it equal
to `(module? x).map Subtype.val`, so everything built on it is equal to its specification:

* `checkFast k m t = Print.check m t` (`checkFast_eq`); it also encodes `m` in a task while
  the text is read;
* `printModuleFast k cfg b = Print.printModule cfg b` (`printModuleFast_eq`);
* `binaryToWatWithFast k cfg b = Text.binaryToWatWith cfg b` (`binaryToWatWithFast_eq`);
* `textToBinaryFast k s = Text.textToBinary s` and `watToBinaryFast k i = Text.watToBinary i`
  (`textToBinaryFast_eq`, `watToBinaryFast_eq`), through `parseSupportedFast?`, equal to
  silmaril-lean's `Wat.parseSupported?`.

The soundness theorems of `Silmaril.Wasm.Tools.Text.Thms` therefore hold for the fast functions
unchanged (`Thms`: `binaryToWatWithFast_sound`, `watToBinaryFast_sound`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.PrintCheck

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text Silmaril.Wasm.Text.Core
open Silmaril.Wasm.Binaryen.Toolkit.Wat.Source
open Silmaril.Wasm.Tools.Annot (stripTrivia)

/-- Chunks of at most `k` elements (with fuel; the chunks always concatenate to the list,
`Thms.flatten_chunksF`). -/
def chunksF {α : Type} (k : Nat) : Nat → List α → List (List α)
  | 0, xs => [xs]
  | _ + 1, [] => []
  | f + 1, xs => xs.take k :: chunksF k f (xs.drop k)

/-- `xs.mapM f`, one task per chunk of `k` elements. -/
def parMapM {α β : Type} (k : Nat) (f : α → Option β) (xs : List α) : Option (List β) :=
  let ts := (chunksF k xs.length xs).map fun c => Task.spawn fun _ => c.mapM f
  (ts.mapM Task.get).map List.flatten

/-- `Wat.Source.module?` without its certificate, the two field passes in parallel. -/
def moduleFast? (k : Nat) (x : SExp) : Option Wasm.Module := do
  let source ← moduleFields? x
  let fields := source.1
  let names : IdCtx := { types := fields.flatMap rawTypeNames }
  let hints := fields.map (fieldHintAt names)
  let J := IdCtx.concat (hints.map Prod.fst)
  let implicit := implicitTypes J.typedefs (hints.flatMap Prod.snd)
  let provisional := J ++ implicitCtx implicit
  let first ← parMapM k (fun y => (field? provisional y).map Subtype.val) fields
  let refined := IdCtx.concat (first.map (·.2.1))
  let actualUses := first.flatMap (·.2.2)
  let I := refined ++ implicitCtx (implicitTypes refined.typedefs actualUses)
  let outs ← parMapM k (fun y => (field? I y).map Subtype.val) fields
  let J' := IdCtx.concat (outs.map (·.2.1))
  let ds := outs.flatMap (·.1)
  let implicit' := implicitTypes J'.typedefs (outs.flatMap (·.2.2))
  if I = J' ++ implicitCtx implicit' then
    if I.Ok then
      if orderedAfter false ds = true then
        if startCount ds ≤ 1 then some (build (resolve ds) implicit')
        else none
      else none
    else none
  else none

/-- The default chunk size: 8 fields per task (`pp-bench.sh`: on pulldown-cmark 1 chunk 6.5 s,
4: 3.1 s, 8: 3.6 s, 16: 3.4 s, 256: 4.8 s, on a loaded 12-thread host). -/
def defaultChunk : Nat := 8

/-- `Print.readBack` with `moduleFast?`. -/
def readBackFast (k : Nat) (s : String) : Option Wasm.Module :=
  match Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 s with
  | none => none
  | some x =>
    match moduleFast? k x with
    | some m => some m
    | none => Binaryen.Toolkit.Wat.parseCanonical? x

/-- `Print.check`, with `moduleFast?` and the encoding of `m` in a task. -/
def checkFast (k : Nat) (m : Wasm.Module) (t : String) : Bool :=
  let ta := Task.spawn fun _ => Binaryen.Exe.encodeModule? m
  match readBackFast k (stripTrivia t) with
  | some m' =>
    match ta.get, Binaryen.Exe.encodeModule? m' with
    | .ok a, .ok a' => a == a'
    | _, _ => false
  | none => false

/-- `Print.printModule` with `checkFast`. -/
def printModuleFast (k : Nat) (cfg : Print.Config) (b : ByteArray) :
    Except Print.Error Print.Printed := do
  let (m, t) ← Print.printText cfg b
  pure ⟨m, t, if cfg.skeleton then false else checkFast k m t⟩

/-- `Text.binaryToWatWith` with `printModuleFast` and `checkFast`. -/
def binaryToWatWithFast (k : Nat) (cfg : Print.Config) (input : ByteArray) :
    Except String String :=
  match printModuleFast k cfg input with
  | .error e => .error e.message
  | .ok r =>
    if r.certified then .ok r.text
    else
      match Binaryen.Toolkit.disassembleBytes input with
      | .error e => .error e
      | .ok a =>
        if checkFast k r.module a.text then .ok a.text
        else .error "the printed text could not be checked against the module"

/-! ## Colours

`print --color always` writes the text with termcolor's escapes (`Print.Config.color`). The
coloured text is not WAT; it is printed separately and kept only when removing its escapes
(`stripAnsi`) gives the certified plain text (`Thms.colorText_spec`). -/

/-- Remove the SGR escapes `ESC [ … m` (with fuel, the length of the text). -/
def stripAnsiGo : Nat → List Char → List Char → List Char
  | 0, cs, acc => acc.reverse ++ cs
  | _ + 1, [], acc => acc.reverse
  | f + 1, '\x1b' :: '[' :: cs, acc =>
    match cs.dropWhile (· != 'm') with
    | _ :: rest => stripAnsiGo f rest acc
    | [] => acc.reverse
  | f + 1, c :: cs, acc => stripAnsiGo f cs (c :: acc)

def stripAnsi (t : String) : String := String.ofList (stripAnsiGo t.length t.toList [])

/-- The coloured text of `b` when its escapes removed give `plain`, else `plain`. -/
def colorText (cfg : Print.Config) (b : ByteArray) (plain : String) : String :=
  match Print.printText { cfg with color := true } b with
  | .ok (_, t) => if stripAnsi t == plain then t else plain
  | .error _ => plain

/-! ## `parse` -/

/-- `Wat.parseSupported?` with `moduleFast?`. -/
def parseSupportedFast? (k : Nat) (x : SExp) : Option Wasm.Module :=
  match Binaryen.Toolkit.Wat.parseCanonical? x with
  | some m => some m
  | none => moduleFast? k x

def textTreeFast? (k : Nat) (input : String) : Except String (SExp × Wasm.Module) :=
  match Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 (Annot.stripTrivia input) with
  | none => .error "malformed WAT lexical or bracket syntax"
  | some tree =>
    match parseSupportedFast? k tree with
    | none => .error "unsupported WAT syntax (outside silmaril's certified text fragment)"
    | some m => .ok (tree, m)

/-- `Text.textToBinary` with `textTreeFast?`. -/
def textToBinaryFast (k : Nat) (input : String) : Except String ByteArray := do
  let (tree, m) ← textTreeFast? k input
  let dc := Binaryen.Exe.usesDataIdx m
  let bytes ← Binaryen.Exe.encodeModuleWith? dc m
  let names ← ((Names.ofTree tree m (input.length + 1)).rename (Annot.nameAnnots input)).section
  let cs := (Annot.customs input).getD []
  -- the `wast` crate writes its `name` section only when no custom section is named `name`
  let names := Text.namesFor cs names
  let vals := Annot.branchHints input
  let branch := if vals.isEmpty then #[] else
    match textTreeFast? k (Annot.markerText input) with
    | .ok (_, m') => Layout.hintPositions m' vals
    | .error _ => #[]
  let h := { Layout.hints tree (input.length + 1) with branch }
  pure ⟨(Layout.relayout h cs names dc m bytes).toArray⟩

/-- `Text.watToBinary` with `textToBinaryFast`. -/
def watToBinaryFast (k : Nat) (input : ByteArray) : Except String ByteArray :=
  if Text.isBinary input then
    match Binary.Core.Decode.decodeModule input with
    | .ok _ => .ok input
    | .error e => .error e
  else
    match String.fromUTF8? input with
    | none => .error "input is not valid UTF-8"
    | some s => textToBinaryFast k s

/-- `Text.watToWat` with the fast functions. -/
def watToWatFast (k : Nat) (input : ByteArray) : Except String String := do
  binaryToWatWithFast k {} (← watToBinaryFast k input)

end Silmaril.Wasm.Tools.PrintCheck
