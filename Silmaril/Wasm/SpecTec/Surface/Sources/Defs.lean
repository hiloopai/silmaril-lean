module

public meta import Lean.Elab.Command

/-!
# SpecTec surface syntax: source excerpts

Exact line ranges of the vendored SpecTec sources under `specs/spectec/src/`
(`WebAssembly/spec@608711107b7f1edb13efd57b7d79b49477462d36`), as string
literals, each line followed by its newline. `spectec_source` re-reads
the file at elaboration time and fails the build unless the literal equals
that line range byte for byte, so the literals cannot drift from the vendored
files. (Track GEN plans to emit these from `tools/spectec-gen`; until then they
are written here.)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Sources

/-- Lines `first` to `last` (1-based, inclusive) of a text, each with its
newline. -/
meta def lineRange (s : String) (first last : Nat) : String :=
  String.join (((s.splitOn "\n").drop (first - 1)).take (last + 1 - first) |>.map (· ++ "\n"))

open Lean Elab Command in
/-- `spectec_source name "path" first last "literal"` defines `name` as the
literal, after checking that it is exactly lines `first`-`last` of the file at
`path` (relative to the repository root); the build fails otherwise. -/
elab doc:(docComment)? "spectec_source " name:ident path:str first:num last:num lit:str : command => do
  let contents ← IO.FS.readFile path.getString
  let expected := lineRange contents first.getNat last.getNat
  unless expected == lit.getString do
    throwError "spectec_source: {path.getString} lines {first.getNat}-{last.getNat} \
      differ from the literal"
  elabCommand (← `($[$doc]? def $name : String := $lit))

/-- `specification/wasm-3.0/0.1-aux.vars.spectec`, line 5. -/
spectec_source wasm30_vars_line5
  "specs/spectec/src/specification/wasm-3.0/0.1-aux.vars.spectec" 5 5
  "syntax N hint(macro none) = nat\n"

/-- `specification/wasm-3.0/0.1-aux.vars.spectec`, lines 5-8. -/
spectec_source wasm30_vars_lines5_8
  "specs/spectec/src/specification/wasm-3.0/0.1-aux.vars.spectec" 5 8
  "syntax N hint(macro none) = nat\n\
   syntax K hint(macro none) = nat\n\
   syntax n hint(macro none) = nat  ;; hack\n\
   syntax m hint(macro none) = nat  ;; hack\n"

/-- `specification/wasm-3.0/0.2-aux.num.spectec`, lines 5-7: `$min`. -/
spectec_source wasm30_num_lines5_7
  "specs/spectec/src/specification/wasm-3.0/0.2-aux.num.spectec" 5 7
  "def $min(nat, nat) : nat\n\
   def $min(i, j) = i  -- if $(i <= j)\n\
   def $min(i, j) = j  -- otherwise\n"

/-- `specification/wasm-3.0/5.1-binary.values.spectec`, line 31: `Bi32`,
the declaration erratum #654 corrects. -/
spectec_source wasm30_binary_line31
  "specs/spectec/src/specification/wasm-3.0/5.1-binary.values.spectec" 31 31
  "grammar Bi32 : i32 = BuN(32)\n"

/-- Line 31 of `5.1-binary.values.spectec` with the source fix of erratum #654
(`BuN` to `BiN`); not a vendored file. -/
def wasm30_binary_line31_fixed : String := "grammar Bi32 : i32 = BiN(32)\n"

end Silmaril.Wasm.SpecTec.Surface.Sources
