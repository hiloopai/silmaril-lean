module

public import Silmaril.Wasm.Tools.Gen.Core.Defs
public import Silmaril.Wasm.Component.BinaryP3.Encode.Defs
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Tools.Component.Validate.Defs

/-!
# A component-level instance of the generator API

Components are the abstract syntax of the component binary at component-model `d095e2f`
(`Silmaril.Wasm.Component.BinaryP3.Ast`). Validity is **`wasm-tools validate` of the compval
track** on the encoded bytes, plus valid core modules at the feature set:

* `CompValid F S c`: `c` encodes (`BinaryP3.encode c = some bs`), the component validator
  `Silmaril.Wasm.Tools.Component.Validate.check F bs` accepts the bytes (so, by `check_sound`,
  they decode in the component binary grammar to a component that is `ValidComponentCore3` at
  the flags `F`, with no extra or gate problem: component type checking of instances, aliases,
  canonical built-ins and types), and every top-level `core:module` section decodes
  (silmaril's `decodeModule`) to a module valid in the feature set `S` (`ValidIn S`);
  `compCheck F S` decides it (`Thms`: `compCheck_iff`), and decoded modules are
  `Encodes`-related to their bytes (`Thms`, from `decodeModule_sound`);
* `Raw.component S size`: one to three generated core modules (`Core.Raw.module`, encoded with
  silmaril's certified encoder `encodeModule?`) and custom sections;
* `Raw.mutate`: mutate an embedded core module (decode, `Core.Raw.mutate`, encode), add,
  drop or rotate sections; `Raw.cands`/`Raw.size`: drop a section, shrink an embedded module
  (`Core.Raw.cands`, the first eight);
* `compGenRun S`, `compMutRun S`, `compShrink S p`: what the checked objects compute (the raw
  output when `compCheck` accepts it, else the empty component or the input).

This module holds only what runs. `Thms` builds the verified objects over it: the language
`compLang F S`, `compGen S` and `compMut S` (computing `compGenRun S` and `compMutRun S`:
`compGen_run_eq`, `compMut_run_eq`); their fallback, the empty component, is `CompValid`
(`empty_compValid`, from `check_emptyBytes`: `Validate.check` accepts the preamble under every
flag set).

The component validator is sound, not proved complete (`docs/projects/wasm-components.md`), so the
checked objects may fall back where `wasm-tools` would accept; the rate is measured by
`tools/wasm-tools-gen-check`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Comp

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Tools.Gen.Core
open Silmaril.Wasm.Component.BinaryP3 (Ast Section)

/-- The top-level core module sections. -/
def coreModules (c : Ast) : List ByteArray :=
  c.sections.filterMap fun
    | .coreModule b => some b
    | _ => none

/-- Core module bytes that decode to a module valid in `S`. -/
def CoreBytesValid (S : FeatureSet) (b : ByteArray) : Prop :=
  ∃ m, Binary.Core.Decode.decodeModule b = .ok m ∧ ValidIn S m

/-- The checker of `CoreBytesValid`. -/
def coreBytesCheck (S : FeatureSet) (b : ByteArray) : Bool :=
  match Binary.Core.Decode.decodeModule b with
  | .ok m => featCheck S m
  | .error _ => false

open Silmaril.Wasm.Tools.Component.Validate (CFlags) in
/-- Component bytes that `wasm-tools validate` (the compval track's `Validate.check`) accepts
under the flags `F`. -/
def BytesAccepted (F : CFlags) (bs : ByteArray) : Prop :=
  ∃ ct, Silmaril.Wasm.Tools.Component.Validate.check F bs = .ok ct

open Silmaril.Wasm.Tools.Component.Validate (CFlags) in
/-- Its checker. -/
def bytesCheck (F : CFlags) (bs : ByteArray) : Bool :=
  match Silmaril.Wasm.Tools.Component.Validate.check F bs with
  | .ok _ => true
  | .error _ => false

open Silmaril.Wasm.Tools.Component.Validate (CFlags) in
/-- **Component validity** under the component flags `F` at the core feature set `S`: the
encoding is accepted by the component validator, and the top-level core modules are valid in
`S`. -/
def CompValid (F : CFlags) (S : FeatureSet) (c : Ast) : Prop :=
  (∃ bs, Silmaril.Wasm.Component.BinaryP3.encode c = some bs ∧ BytesAccepted F bs) ∧
    ∀ b ∈ coreModules c, CoreBytesValid S b

open Silmaril.Wasm.Tools.Component.Validate (CFlags) in
/-- Its checker. -/
def compCheck (F : CFlags) (S : FeatureSet) (c : Ast) : Bool :=
  (match Silmaril.Wasm.Component.BinaryP3.encode c with
    | some bs => bytesCheck F bs
    | none => false) && (coreModules c).all (coreBytesCheck S)

/-- The bytes of the empty component (the preamble). -/
def emptyBytes : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00]⟩

namespace Raw

/-- Encode a core module. -/
def encodeCore (m : Module) : Option ByteArray :=
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
  | .ok bs => some ⟨bs.toArray⟩
  | .error _ => none

/-- A custom section. -/
def custom : Rand Section := do
  let n ← Rand.nat 4
  let bytes ← Rand.list (← Rand.nat 12) (Rand.nat 256)
  return .custom s!"silmaril-gen-{n}" ⟨(bytes.map UInt8.ofNat).toArray⟩

/-- **A raw component**: core modules and custom sections. -/
def component (S : FeatureSet) (size : Nat) : Rand Ast := do
  let k ← Rand.range 1 3
  let mods ← Rand.list k (Core.Raw.module S (size / k + 1))
  let secs := mods.filterMap fun m => (encodeCore m).map Section.coreModule
  let cs ← Rand.list (← Rand.nat 2) custom
  return .mk (secs ++ cs)

/-- **Raw mutation** of a component. -/
def mutate (S : FeatureSet) (r : Rng) (c : Ast) : Ast := Rand.run (do
  let ss := c.sections
  match ← Rand.nat 4 with
  | 0 =>
    let is := (List.range ss.length).filter fun i =>
      match ss.getD i (.custom "" .empty) with | .coreModule _ => true | _ => false
    if is.isEmpty then return c
    let i ← Rand.pick is 0
    match ss.getD i (.custom "" .empty) with
    | .coreModule b =>
      match Binary.Core.Decode.decodeModule b with
      | .ok m =>
        let r' ← fun r => r.split
        match encodeCore (Core.Raw.mutate S r' m) with
        | some b' => return .mk (ss.set i (.coreModule b'))
        | none => return c
      | .error _ => return c
    | _ => return c
  | 1 => return .mk (ss ++ [← custom])
  | 2 =>
    if ss.isEmpty then return c
    return .mk (ss.eraseIdx (← Rand.nat ss.length))
  | _ =>
    match ss with
    | [] => return c
    | s :: rest => return .mk (rest ++ [s])) r

/-- The size: sections plus the sizes of embedded core modules. -/
def size (c : Ast) : Nat :=
  c.sections.length + (c.sections.map fun
    | .coreModule b =>
      match Binary.Core.Decode.decodeModule b with
      | .ok m => Core.Raw.size m
      | .error _ => b.size
    | .custom _ d => d.size
    | _ => 1).sum

/-- **Shrink candidates**: drop a section; shrink an embedded core module. -/
def cands (c : Ast) : List Ast :=
  let ss := c.sections
  ((List.range ss.length).map fun i => .mk (ss.eraseIdx i)) ++
  (List.range ss.length).flatMap fun i =>
    match ss.getD i (.custom "" .empty) with
    | .coreModule b =>
      match Binary.Core.Decode.decodeModule b with
      | .ok m => ((Core.Raw.cands m).take 8).filterMap fun m' =>
          (encodeCore m').map fun b' => .mk (ss.set i (.coreModule b'))
      | .error _ => []
    | _ => []

end Raw

/-- The default component flags (wasmparser's defaults at 1.262.0). -/
abbrev dflt : Silmaril.Wasm.Tools.Component.Validate.CFlags :=
  Silmaril.Wasm.Tools.Component.Validate.CFlags.default

/-- **The component generator** of a feature set (default component flags): the raw component
when `compCheck` accepts it, else the empty component (`Thms`: `compGen`, `compGen_run_eq`). -/
def compGenRun (S : FeatureSet) : Rng → Nat → Ast :=
  Generator.guardedRun (compCheck dflt S) (fun r n => Rand.run (Raw.component S n) r) (.mk [])

/-- **The component mutator**: the raw mutation when `compCheck` accepts it, else the input
(`Thms`: `compMut`, `compMut_run_eq`). -/
def compMutRun (S : FeatureSet) : Rng → Ast → Ast :=
  Mutator.guardedRun (compCheck dflt S) (Raw.mutate S)

/-- The component shrinker. -/
def compShrinker : Shrinker Ast := ⟨Raw.size, Raw.cands⟩

/-- **Checked component shrinking**. -/
def compShrink (S : FeatureSet) (p : Ast → Bool) (c : Ast) : Ast :=
  compShrinker.shrink (fun x => compCheck dflt S x && p x) c

end Silmaril.Wasm.Tools.Gen.Comp
