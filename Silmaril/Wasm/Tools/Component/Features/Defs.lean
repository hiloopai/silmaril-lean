module

public import Silmaril.Wasm.Tools.Component.Validate.Defs

/-!
# The `--features` argument of `wasm-tools validate`, for components

wasmparser's `WasmFeatures` at 1.262.0 (`crates/wasmparser/src/features.rs`) is a 64-bit set
of flags; here it is a natural number used as a bit set (`Feat`). `flags` lists every named
flag with its bits and its default, transcribed from `features.rs` (`reference_types` and
`bulk_memory` are two bits each, as upstream); `groups` the version groups `mvp`, `wasm1`,
`wasm2`, `wasm3`, `lime1`.

`parseFeatures arg` follows `parse_features` of `src/bin/wasm-tools/validate.rs`: split at
`,`, trim, drop empty parts; a leading `-` disables; a flag name (lower case, `_` as `-`)
enables or disables its bits, a group resets the set to the group (a disabled group is an
error), `all` enables or disables every flag; an unknown name is an error listing the valid
names. `applyAll` folds the actions of every `--features` occurrence over the default
(`CliFeatures::features`).

`toCFlags f` projects the set to the component validator's flags (`Validate.CFlags`); it is
`none` when the `component-model` flag is off (wasmparser then rejects every component).
`Thms` proves `toCFlags default = some CFlags.default` and `toCFlags all = some CFlags.all`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Features

open Silmaril.Wasm.Tools.Component.Validate (CFlags)

/-- A feature set: bit `i` is flag `1 << i` of wasmparser's `WasmFeatures`. -/
abbrev Feat := Nat

/-- `1 <<< i`. -/
def bit (i : Nat) : Nat := 2 ^ i

/-- Every named flag of `WasmFeatures` at 1.262.0: name (as in `features.rs`), bits, default,
in the order of `WasmFeatures::FLAGS`. -/
def flags : List (String × Nat × Bool) :=
  [ ("mutable_global", bit 0, true), ("saturating_float_to_int", bit 1, true),
    ("sign_extension", bit 2, true), ("reference_types", bit 3 + bit 34, true),
    ("multi_value", bit 4, true), ("bulk_memory", bit 5 + bit 35, true),
    ("simd", bit 6, true), ("relaxed_simd", bit 7, true), ("threads", bit 8, true),
    ("shared_everything_threads", bit 9, false), ("tail_call", bit 10, true),
    ("floats", bit 11, true), ("multi_memory", bit 12, true), ("exceptions", bit 13, true),
    ("memory64", bit 14, true), ("extended_const", bit 15, true),
    ("component_model", bit 16, true), ("function_references", bit 17, true),
    ("memory_control", bit 18, false), ("gc", bit 19, true),
    ("custom_page_sizes", bit 20, false), ("legacy_exceptions", bit 23, false),
    ("gc_types", bit 24, true), ("stack_switching", bit 25, false),
    ("wide_arithmetic", bit 26, true), ("cm_values", bit 21, false),
    ("cm_nested_names", bit 22, false), ("cm_async", bit 27, true),
    ("cm_async_stackful", bit 28, false), ("cm_more_async_builtins", bit 29, false),
    ("cm_threading", bit 30, false), ("cm_error_context", bit 31, false),
    ("cm_fixed_length_lists", bit 32, false), ("cm_gc", bit 33, false),
    ("call_indirect_overlong", bit 34, true), ("bulk_memory_opt", bit 35, true),
    ("custom_descriptors", bit 36, false), ("compact_imports", bit 37, true),
    ("cm_map", bit 38, true), ("cm64", bit 39, false), ("cm_implements", bit 40, true),
    ("cm_canon_names", bit 41, false), ("cm_forward", bit 42, false),
    ("cm_accessors", bit 43, false) ]

/-- The bits of a flag (0 when unknown). -/
def bitsOf (n : String) : Nat := ((flags.find? (·.1 == n)).map (·.2.1)).getD 0

/-- Bitwise union of a list of masks. -/
def unionAll (ms : List Nat) : Nat := ms.foldl (· ||| ·) 0

/-- `WasmFeatures::default()`. -/
def default : Feat := unionAll (flags.filterMap fun (_, b, d) => if d then some b else none)

/-- `WasmFeatures::all()`. -/
def all : Feat := unionAll (flags.map (·.2.1))

/-- `MVP`, `WASM1`, `WASM2`, `WASM3`, `LIME1`. -/
def mvp : Feat := bitsOf "floats" ||| bitsOf "gc_types"
def wasm1 : Feat := mvp ||| bitsOf "mutable_global"
def wasm2 : Feat := unionAll (wasm1 :: ["bulk_memory", "reference_types", "sign_extension",
  "saturating_float_to_int", "multi_value", "simd"].map bitsOf)
def wasm3 : Feat := unionAll (wasm2 :: ["gc", "tail_call", "extended_const",
  "function_references", "multi_memory", "relaxed_simd", "threads", "exceptions",
  "memory64"].map bitsOf)
def lime1 : Feat := unionAll (wasm1 :: ["multi_value", "sign_extension",
  "saturating_float_to_int", "bulk_memory_opt", "extended_const",
  "call_indirect_overlong"].map bitsOf)

def groups : List (String × Feat) :=
  [("mvp", mvp), ("wasm1", wasm1), ("wasm2", wasm2), ("wasm3", wasm3), ("lime1", lime1)]

/-- One action of a `--features` argument. -/
inductive Action where
  | reset (f : Feat)
  | enable (f : Feat)
  | disable (f : Feat)
  deriving Repr, DecidableEq

/-- Apply an action. -/
def Action.apply (f : Feat) : Action → Feat
  | .reset g => g
  | .enable g => f ||| g
  | .disable g => f &&& (all ^^^ g)

/-- `flag_name`: lower case, `_` as `-`. -/
def flagName (n : String) : String := (n.map fun c => if c == '_' then '-' else c).toLower

/-- The names `parse_features` accepts, in the order it lists them. -/
def validNames : List String :=
  flags.map (flagName ·.1) ++ groups.map (·.1) ++ ["all"]

/-- One part (already trimmed and non-empty). -/
def parsePart (part : String) : Except String Action :=
  let (enable, p) := if part.startsWith "-" then (false, part.drop 1 |>.toString) else (true, part)
  match flags.find? (flagName ·.1 == p) with
  | some (_, b, _) => .ok (if enable then .enable b else .disable b)
  | none =>
    match groups.find? (·.1 == p) with
    | some (_, g) =>
      if enable then .ok (.reset g) else .error s!"cannot disable `{p}`, it can only be enabled"
    | none =>
      if p == "all" then .ok (if enable then .enable all else .disable all)
      else .error s!"unknown feature `{p}`\nValid features: {", ".intercalate validNames}"

/-- **`parse_features`**: one `--features` value. -/
def parseFeatures (arg : String) : Except String (List Action) :=
  ((arg.splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")).mapM parsePart

/-- **`CliFeatures::features`**: the actions of every occurrence, in order, from the
default. -/
def applyAll (acts : List (List Action)) : Feat := acts.flatten.foldl Action.apply default

/-- Is a flag set? -/
def has (f : Feat) (n : String) : Bool := f &&& bitsOf n == bitsOf n

/-- **Projection to the component validator's flags**; `none` when `component-model` is
off. -/
def toCFlags (f : Feat) : Option CFlags :=
  if !has f "component_model" then none
  else some
    ⟨{ async_ := has f "cm_async", map := has f "cm_map", implements := has f "cm_implements",
       fixedLists := has f "cm_fixed_length_lists", errorContext := has f "cm_error_context",
       moreAsyncBuiltins := has f "cm_more_async_builtins",
       stackful := has f "cm_async_stackful", threads := has f "cm_threading",
       forward := has f "cm_forward", memory64 := has f "cm64",
       getters := has f "cm_accessors", canonicalNames := has f "cm_canon_names",
       values := has f "cm_values", nestedNames := has f "cm_nested_names" },
     has f "cm_gc"⟩

end Silmaril.Wasm.Tools.Component.Features
