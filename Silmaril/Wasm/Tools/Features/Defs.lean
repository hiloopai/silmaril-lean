module

public import Silmaril.Wasm.Models.Features.Defs

/-!
# wasmparser feature flags and the `--features` argument of `wasm-tools`

`wasm-tools validate --features …` (wasm-tools 1.262.0, `src/bin/wasm-tools/validate.rs`) reads
a comma-separated list of wasmparser feature names (`crates/wasmparser/src/features.rs`), each
optionally prefixed by `-`, plus the groups `mvp`, `wasm1`, `wasm2`, `wasm3`, `lime1` and the
placeholder `all`. This topic transcribes that machinery and maps it to the capability lattice
of `Silmaril.Wasm.Models` (`FeatureSet`).

* `WFeatures`: a wasmparser feature set, as the 64-bit mask wasmparser uses (`Nat`, so the kernel
  evaluates it); `Flag`, `flags`: the 44 named flags with their bits, in declaration order
  (`reference-types` and `bulk-memory` are two bits each, as upstream);
* `WFeatures.dflt`, `.all`, `.mvp`, `.wasm1`, `.wasm2`, `.wasm3`, `.lime1`: upstream's constants;
* `Action`, `parsePart`, `parseFeatures`: one `--features` argument (errors are upstream's
  messages); `applyActions`: the fold of `CliFeatures::features`, starting from the default;
* `WFeatures.raw`, `WFeatures.toFS`: the capabilities a wasmparser feature set grants. `raw` is
  the direct reading of the flags (the MVP pieces wasmparser cannot disable are always present,
  and so is `mutGlobal`: the `mutable-global` flag only gates importing and exporting mutable
  globals, checked separately by `Validate.mutGlobalIOB`);
  `toFS` keeps a capability only together with all its prerequisites (the largest closed subset
  of `raw`), so a flag whose prerequisite is disabled grants nothing, as in wasmparser, where for
  example relaxed SIMD instructions are unusable without the `v128` type of `simd`.

Flags with no capability in `Cap` (threads, shared-everything threads, memory control, legacy
exceptions, custom descriptors, compact imports, `gc-types`, the component-model flags) are not
read by `toFS`; `tools/wasm-tools/README.md` lists how each is treated.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Features

open Silmaril.Wasm.Models

/-- A wasmparser feature set: its 64-bit mask. -/
abbrev WFeatures : Type := Nat

/-- A named wasmparser flag: its name as `wasm-tools` spells it, and its bits. -/
structure Flag where
  name : String
  bits : Nat
  deriving Repr, DecidableEq

/-- Bit `i`. -/
def bit (i : Nat) : Nat := 2 ^ i

/-- The flags of `crates/wasmparser/src/features.rs`, in declaration order (the order of
`WasmFeatures::FLAGS`, hence of upstream's list of valid names), with their defaults. -/
def flagTable : List (Flag × Bool) :=
  [ (⟨"mutable-global", bit 0⟩, true)
  , (⟨"saturating-float-to-int", bit 1⟩, true)
  , (⟨"sign-extension", bit 2⟩, true)
  , (⟨"reference-types", bit 3 ||| bit 34⟩, true)
  , (⟨"multi-value", bit 4⟩, true)
  , (⟨"bulk-memory", bit 5 ||| bit 35⟩, true)
  , (⟨"simd", bit 6⟩, true)
  , (⟨"relaxed-simd", bit 7⟩, true)
  , (⟨"threads", bit 8⟩, true)
  , (⟨"shared-everything-threads", bit 9⟩, false)
  , (⟨"tail-call", bit 10⟩, true)
  , (⟨"floats", bit 11⟩, true)
  , (⟨"multi-memory", bit 12⟩, true)
  , (⟨"exceptions", bit 13⟩, true)
  , (⟨"memory64", bit 14⟩, true)
  , (⟨"extended-const", bit 15⟩, true)
  , (⟨"component-model", bit 16⟩, true)
  , (⟨"function-references", bit 17⟩, true)
  , (⟨"memory-control", bit 18⟩, false)
  , (⟨"gc", bit 19⟩, true)
  , (⟨"custom-page-sizes", bit 20⟩, false)
  , (⟨"legacy-exceptions", bit 23⟩, false)
  , (⟨"gc-types", bit 24⟩, true)
  , (⟨"stack-switching", bit 25⟩, false)
  , (⟨"wide-arithmetic", bit 26⟩, true)
  , (⟨"cm-values", bit 21⟩, false)
  , (⟨"cm-nested-names", bit 22⟩, false)
  , (⟨"cm-async", bit 27⟩, true)
  , (⟨"cm-async-stackful", bit 28⟩, false)
  , (⟨"cm-more-async-builtins", bit 29⟩, false)
  , (⟨"cm-threading", bit 30⟩, false)
  , (⟨"cm-error-context", bit 31⟩, false)
  , (⟨"cm-fixed-length-lists", bit 32⟩, false)
  , (⟨"cm-gc", bit 33⟩, false)
  , (⟨"call-indirect-overlong", bit 34⟩, true)
  , (⟨"bulk-memory-opt", bit 35⟩, true)
  , (⟨"custom-descriptors", bit 36⟩, false)
  , (⟨"compact-imports", bit 37⟩, true)
  , (⟨"cm-map", bit 38⟩, true)
  , (⟨"cm64", bit 39⟩, false)
  , (⟨"cm-implements", bit 40⟩, true)
  , (⟨"cm-canon-names", bit 41⟩, false)
  , (⟨"cm-forward", bit 42⟩, false)
  , (⟨"cm-accessors", bit 43⟩, false) ]

/-- The named flags. -/
def flags : List Flag := flagTable.map (·.1)

/-- The bits of a flag, by name (`0` for an unknown name). -/
def bitsOf (name : String) : Nat := ((flags.find? (·.name == name)).map (·.bits)).getD 0

namespace WFeatures

/-- Union of masks. -/
def union (a b : WFeatures) : WFeatures := a ||| b

/-- The mask of every named flag (`WasmFeatures::all()`). -/
def all : WFeatures := flags.foldl (fun acc f => acc ||| f.bits) 0

/-- Remove the bits of `b` (`a &= !b` on 64 bits). -/
def diff (a b : WFeatures) : WFeatures := a &&& ((2 ^ 64 - 1) ^^^ b)

/-- The default set (`WasmFeatures::default()`): the flags whose default is `true`. -/
def dflt : WFeatures := flagTable.foldl (fun acc p => if p.2 then acc ||| p.1.bits else acc) 0

/-- `WasmFeatures::MVP`: floats and the GC type gate. -/
def mvp : WFeatures := bitsOf "floats" ||| bitsOf "gc-types"

/-- `WasmFeatures::WASM1`. -/
def wasm1 : WFeatures := mvp ||| bitsOf "mutable-global"

/-- `WasmFeatures::WASM2`. -/
def wasm2 : WFeatures :=
  wasm1 ||| bitsOf "bulk-memory" ||| bitsOf "reference-types" ||| bitsOf "sign-extension" |||
    bitsOf "saturating-float-to-int" ||| bitsOf "multi-value" ||| bitsOf "simd"

/-- `WasmFeatures::WASM3`. -/
def wasm3 : WFeatures :=
  wasm2 ||| bitsOf "gc" ||| bitsOf "tail-call" ||| bitsOf "extended-const" |||
    bitsOf "function-references" ||| bitsOf "multi-memory" ||| bitsOf "relaxed-simd" |||
    bitsOf "threads" ||| bitsOf "exceptions" ||| bitsOf "memory64"

/-- `WasmFeatures::LIME1`. -/
def lime1 : WFeatures :=
  wasm1 ||| bitsOf "multi-value" ||| bitsOf "sign-extension" |||
    bitsOf "saturating-float-to-int" ||| bitsOf "bulk-memory-opt" ||| bitsOf "extended-const" |||
    bitsOf "call-indirect-overlong"

/-- Is every bit of the flag `name` set? -/
def hasFlag (F : WFeatures) (name : String) : Bool :=
  let b := bitsOf name
  b != 0 && (F &&& b) == b

/-- Is the single bit `i` set? -/
def hasBit (F : WFeatures) (i : Nat) : Bool := (F &&& bit i) != 0

/-- **The capabilities wasmparser's flags grant, read directly.** The MVP pieces wasmparser has
no flag for (integers, control, calls, memories, tables, globals) are always granted.
`reference-types` is its own bit 3, `bulk-memory` its bit 5; their second bits are
`call-indirect-overlong` and `bulk-memory-opt`. -/
def raw (F : WFeatures) : Cap → Bool
  | .intNum | .control | .directCall | .memory | .table | .callIndirect | .globals => true
  | .floatNum => F.hasBit 11
  -- the mutable-global flag gates imports and exports of mutable globals only (a separate check,
  -- `Validate.mutGlobalIOB`); defined mutable globals and `global.set` are MVP
  | .mutGlobal => true
  | .signExt => F.hasBit 2
  | .satConv => F.hasBit 1
  | .multiValue => F.hasBit 4
  | .refTypes => F.hasBit 3
  | .bulkMemory => F.hasBit 5
  | .bulkMemoryOpt => F.hasBit 35
  | .simd => F.hasBit 6
  | .callIndirectOverlong => F.hasBit 34
  | .tailCall => F.hasBit 10
  | .extConst => F.hasBit 15
  | .typedFuncRef => F.hasBit 17
  | .gcImm | .gcMut => F.hasBit 19
  | .exn => F.hasBit 13
  | .memory64 => F.hasBit 14
  | .multiMemory => F.hasBit 12
  | .relaxedSimd => F.hasBit 7
  | .stackSwitching => F.hasBit 25
  | .wideArith => F.hasBit 26
  | .customPageSizes => F.hasBit 20

/-- The interior of a set of capabilities: the capabilities whose prerequisites are all in it. -/
def interior (S : Cap → Bool) (c : Cap) : Bool := S c && (Cap.pre c).all S

theorem interior_closed (S : Cap → Bool) : Closed (interior S) := by
  intro c hc d hd
  simp only [interior, Bool.and_eq_true, List.all_eq_true] at hc ⊢
  exact ⟨hc.2 d hd, fun e he => hc.2 e (Cap.pre_trans hd he)⟩

/-- **The capability set of a wasmparser feature set**: the largest closed subset of `raw F`. -/
def toFS (F : WFeatures) : FeatureSet := ⟨interior (raw F), interior_closed _⟩

end WFeatures

/-! ## The `--features` argument -/

/-- One action of a `--features` argument (`FeatureAction`). -/
inductive Action where
  | reset (F : WFeatures)
  | enable (F : WFeatures)
  | disable (F : WFeatures)
  deriving Repr, DecidableEq

/-- The groups, which can only be enabled; each resets the set. -/
def groups : List (String × WFeatures) :=
  [("mvp", WFeatures.mvp), ("wasm1", WFeatures.wasm1), ("wasm2", WFeatures.wasm2),
    ("wasm3", WFeatures.wasm3), ("lime1", WFeatures.lime1)]

/-- Every name `--features` accepts, in upstream's order (flags, groups, `all`). -/
def validNames : List String := flags.map (·.name) ++ groups.map (·.1) ++ ["all"]

/-- Upstream's message for an unknown name. -/
def unknownMsg (part : String) : String :=
  s!"unknown feature `{part}`\nValid features: " ++ ", ".intercalate validNames

/-- One comma-separated part (already trimmed and non-empty). -/
def parsePart (part : String) : Except String Action :=
  let (enable, name) :=
    if part.startsWith "-" then (false, (part.drop 1).toString) else (true, part)
  match flags.find? (·.name == name) with
  | some f => .ok (if enable then .enable f.bits else .disable f.bits)
  | none =>
    match groups.find? (·.1 == name) with
    | some (_, g) =>
      if enable then .ok (.reset g)
      else .error s!"cannot disable `{part}`, it can only be enabled"
    | none =>
      if name == "all" then .ok (if enable then .enable WFeatures.all else .disable WFeatures.all)
      else .error (unknownMsg part)

/-- The parts of one argument: split at `,`, trimmed, empty parts dropped. -/
def parts (arg : String) : List String :=
  ((arg.splitOn ",").map fun s => s.trimAscii.toString).filter (· ≠ "")

/-- **One `--features` argument** (`parse_features`): the first bad part is the error. -/
def parseFeatures (arg : String) : Except String (List Action) :=
  (parts arg).mapM parsePart

/-- One action applied to a set. -/
def Action.apply (F : WFeatures) : Action → WFeatures
  | .reset G => G
  | .enable G => F ||| G
  | .disable G => WFeatures.diff F G

/-- **The features of the command line** (`CliFeatures::features`): the actions of every
`--features` argument, in order, from the default set. -/
def applyActions (acts : List Action) : WFeatures := acts.foldl Action.apply WFeatures.dflt

end Silmaril.Wasm.Tools.Features
