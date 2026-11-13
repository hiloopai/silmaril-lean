module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiff

/-!
# The rules each `theory-diff` row drops, as keys

The keys (relation name, rule name) that `spectec-gen theory-diff --list` reports dropped,
in the order of `ruleList` (for the main rows the tool lists `Export_ok` first). The
`VersionDiff*` chunk modules check them against the scripts.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.SpecTec

/-- The rule the wasm-1.0 errata drop (erratum 680 replaces the one rule of `Module_ok`). -/
def keysWasm10Fixed : List (IL.Id × IL.Id) := [("Module_ok", "")]

/-- The rules erratum M1 drops from the meta-IL script. -/
def keysMetaFixed : List (IL.Id × IL.Id) :=
  [("Step_exp", "BIN-ctx2"), ("Step_exp", "CMP-ctx2"), ("Step_exp", "CMP-EQ-true"),
   ("Step_exp", "CMP-NE-false")]

/-- The rules wasm-1.0 main `e7a9df7c` drops from the pinned wasm-1.0 (`Export_ok` and
`Module_ok` are redeclared). -/
def keysWasm10Main : List (IL.Id × IL.Id) := [("Module_ok", ""), ("Export_ok", "")]

/-- The rules wasm-2.0 main `e7a9df7c` drops from the pinned wasm-2.0 (`Export_ok` and
`Module_ok` are redeclared). -/
def keysWasm20Main : List (IL.Id × IL.Id) := [("Module_ok", ""), ("Export_ok", "")]

/-- The rules wasm-3.0 main `e7a9df7c` drops from the pinned wasm-3.0: one `Instrs_ok2` rule,
7 `Step` rules and 15 `Step_read` rules. -/
def keysWasm30Main : List (IL.Id × IL.Id) :=
  [("Instrs_ok2", "seq"), ("Step", "call_ref-func"), ("Step", "call_ref-hostfunc-res"),
   ("Step", "call_ref-hostfunc-div"), ("Step", "throw"), ("Step", "struct.new"),
   ("Step", "array.new_fixed"), ("Step", "array.set-oob"), ("Step_read", "call"),
   ("Step_read", "return_call"), ("Step_read", "return_call_ref-frame-addr"),
   ("Step_read", "throw_ref-handler-catch"), ("Step_read", "throw_ref-handler-catch_ref"),
   ("Step_read", "ref.func"), ("Step_read", "struct.get-struct"), ("Step_read", "array.get-oob"),
   ("Step_read", "array.get-array"), ("Step_read", "array.len-array"),
   ("Step_read", "array.fill-oob"), ("Step_read", "array.copy-oob1"),
   ("Step_read", "array.copy-oob2"), ("Step_read", "array.init_elem-oob1"),
   ("Step_read", "array.init_data-oob1")]

end Silmaril.Wasm.SpecTec.Institution.Versions
