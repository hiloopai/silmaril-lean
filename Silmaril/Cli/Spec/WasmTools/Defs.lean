module

public import Silmaril.Cli.Clap.Defs
public import Silmaril.Cli.Spec.WasmTools.Doc.Defs
public import Silmaril.Cli.Clap.Exact.Defs

/-!
# The command line of `wasm-tools` 1.262.0

The full command line of [wasm-tools](https://github.com/bytecodealliance/wasm-tools) 1.262.0
(`e22db44da`, 2026-10-13), the reference binary of `tools/wasm-tools/README.md`
(SHA-256 `fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211`), as an args
grammar (`root : Silmaril.Cli.Command`) in the clap dialect (`tool : Clap.Tool`): every
subcommand (19 top-level, 7 under `component`, 2 under `metadata`), every option with its
short and long names, value name, default and possible values, every positional argument,
the `-h` texts, the exit codes (the `after_help` texts and the long texts of `--help` are
data in `Silmaril.Cli.Spec.WasmTools.Doc`); the value checks of clap's value
parsers (`checks`, `checksAt`) and the `requires`/`conflicts_with` relations (`rules`), folded
into the grammar (`Command.checks`, `Command.rules`) by `grammar`.

**Provenance.** The grammar was extracted on 2026-11-10 from the `-h` output of every command
path by a one-off script (not kept); whether an option may repeat was probed by giving it
twice and reading clap's `cannot be used multiple times`. The value checks and rules were read
off the 1.262.0 sources (`src/bin/wasm-tools/*.rs`, `crates/wasm-metadata/src/clap.rs`,
`crates/wasm-smith/src/{{config,core}}.rs`, `crates/wit-component/src/lib.rs`,
`crates/wit-parser/src/lib.rs`): the Rust type of each numeric field (`usize`/`u64`: 64 bits,
`u32`, `u8`, `u128`), `parse_features`, `InstructionKind::from_str`, `MemoryOffsetChoices`,
`parse_key_value`, `parse_import_name`, `StringEncoding`, `Mangling`, `ColorChoice`. The
extraction is checked, not trusted: `tools/cli-spec/tests/wasm-tools-surface.sh` compares the
help of every path rendered in clap's layout (`Silmaril.Cli.Clap.Help`: `-h` and `--help`)
with upstream's byte for byte, and the exit class of `Clap.Tool.read` with the binary on the derived corpus.

**Left to the program** (`ValueCheck.external`, `absUrl`): whether a `[NAME=]MODULE` file is
readable (clap's value parser reads it), whether a `--licenses` value is an SPDX expression,
and whether a URL with a scheme parses. **Not recorded:** hidden options (`component new
--skip-validation`).
-/

@[expose] public section

namespace Silmaril.Cli.Spec.WasmTools

open Silmaril.Cli

/-- `--help` (3 commands). -/
def oHelpGroup : Opt :=
  { id := "help", short := ["h"], help := "Print help" }

/-- `--generate-dwarf` (8 commands). -/
def oGenerateDwarf : Opt :=
  { id := "generate-dwarf", arg := some .str, metavar := "lines|full", help := "Optionally generate DWARF debugging information from WebAssembly text files" }

/-- `-g` (8 commands). -/
def oG : Opt :=
  { id := "-g", long := [], short := ["g"], help := "Shorthand for `--generate-dwarf full`" }

/-- `--output` (21 commands). -/
def oOutput : Opt :=
  { id := "output", short := ["o"], arg := some .str, metavar := "OUTPUT", help := "Where to place output" }

/-- `--verbose` (26 commands). -/
def oVerbose : Opt :=
  { id := "verbose", short := ["v"], repeated := true, help := "Use verbose output (-v info, -vv debug, -vvv trace)" }

/-- `--color` (26 commands). -/
def oColor : Opt :=
  { id := "color", arg := some .str, metavar := "COLOR", help := "Configuration over whether terminal colors are used in output", default := some "auto" }

/-- `--wat` (9 commands). -/
def oWat : Opt :=
  { id := "wat", short := ["t"], help := "Output the text format of WebAssembly instead of the binary format" }

/-- `--help` (26 commands). -/
def oHelp : Opt :=
  { id := "help", short := ["h"], help := "Print help (see more with '--help')" }

/-- `--emit-canonical-names` (5 commands). -/
def oEmitCanonicalNames : Opt :=
  { id := "emit-canonical-names", help := "Emits canonical interface names with version suffixes" }

/-- `--wat` (4 commands). -/
def oWat2 : Opt :=
  { id := "wat", short := ["t"], help := "Print the output in the WebAssembly text format instead of binary" }

/-- `--features` (5 commands). -/
def oFeatures : Opt :=
  { id := "features", arg := some .str, metavar := "FEATURES", help := "Features to enable when parsing the `wit` option", repeated := true }

/-- `--all-features` (5 commands). -/
def oAllFeatures : Opt :=
  { id := "all-features", help := "Enable all features when parsing the `wit` option" }

/-- `wasm-tools wast`. -/
def wast : Command where
  name := "wast"
  about := "A subcommand to test `*.wast` files short of executing WebAssembly code"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oVerbose,
    oColor,
    { id := "ignore-error-messages", help := "Whether to ignore the error message expectation in `(assert_invalid ..)` directives" },
    { id := "features", short := ["f"], arg := some .str, metavar := "FEATURES", help := "Comma-separated list of WebAssembly features to enable during validation", repeated := true },
    { id := "allow-confusing-unicode", help := "Whether or not \"confusing unicode characters\" are allowed to be present in `*.wast` files" },
    { id := "assert", short := ["a"], arg := some .str, metavar := "ASSERT", help := "Perform extra internal assertions in `wasm-tools` itself over the provided test", repeated := true },
    { id := "snapshot", arg := some .str, metavar := "SNAPSHOT", help := "Directory to place snapshots in with `--assert snapshot-*` flags" },
    oHelp]

/-- `wasm-tools json-from-wast`. -/
def jsonFromWast : Command where
  name := "json-from-wast"
  aliases := ["wast2json"]
  about := "Convert a `*.wast` WebAssembly spec test into a `*.json` file and `*.wasm` files"
  pos := [
    { id := "wast", help := "Input `*.wast` file that will be parsed and converted to JSON" }]
  opts := [
    oVerbose,
    oColor,
    oOutput,
    { id := "wasm-dir", arg := some .str, metavar := "WASM_DIR", help := "Where to place binary and text WebAssembly files referenced by tests" },
    { id := "pretty", help := "Output pretty-printed JSON instead of compact json" },
    { id := "allow-confusing-unicode", arg := some (.enum ["true", "false"]), metavar := "true|false", help := "Controls the \"allow confusing unicode\" option which will reject parsing files that have unusual characters" },
    oHelp]

/-- `wasm-tools completion`. -/
def completion : Command where
  name := "completion"
  about := "Generate shell completion scripts for this CLI"
  pos := [
    { id := "shell", type := .enum ["bash", "elvish", "fish", "powershell", "zsh"], help := "The shell to generate completions for" }]
  opts := [
    oVerbose,
    oColor,
    oHelp]

/-- `wasm-tools addr2line`. -/
def addr2line : Command where
  name := "addr2line"
  about := "Translate a WebAssembly address to a filename and line number using DWARF debugging information"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" },
    { id := "addresses", arity := .many, help := "Addresses to convert to filenames and line numbers" }]
  opts := [
    oGenerateDwarf,
    oG,
    oOutput,
    oVerbose,
    oColor,
    { id := "code-section-relative", help := "Indicates that addresses are code-section-relative instead of offsets from the beginning of the module" },
    oHelp]

/-- `wasm-tools wit-dylib`. -/
def witDylib : Command where
  name := "wit-dylib"
  about := "Generate a wasm dynamic library from the input WIT world"
  pos := [
    { id := "wit", help := "Path to WIT files to load" },
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oFeatures,
    oAllFeatures,
    oOutput,
    oVerbose,
    oColor,
    { id := "encoding", arg := some .str, metavar := "ENCODING", help := "The string encoding to use for imports/exports, defaults to utf-8" },
    { id := "world", short := ["w"], arg := some .str, metavar := "WORLD", help := "The WIT world to use, if the WIT input has more than one" },
    { id := "validate", help := "Whether or not to validate the generated dynamic library" },
    oWat2,
    { id := "interpreter", arg := some .str, metavar := "name", help := "The interpreter name to insert into the `WASM_DYLINK_NEEDED` section encoded as `dylink.0`" },
    { id := "async", arg := some .str, metavar := "FILTER", help := "Determines which functions to lift or lower `async`, if any", repeated := true },
    { id := "stack-pointer", arg := some (.enum ["global", "task-context"]), metavar := "loc", help := "Where the stack pointer is located in the ABI of the generated dylib", default := some "global" },
    oEmitCanonicalNames,
    oHelp]

/-- `wasm-tools wit-smith`. -/
def witSmith : Command where
  name := "wit-smith"
  about := "A WIT test case generator"
  pos := [
    { id := "input", arity := .optional, help := "The arbitrary input seed" }]
  opts := [
    oOutput,
    oWat,
    { id := "max-packages", arg := some .str, metavar := "MAX_PACKAGES", default := some "10" },
    { id := "max-type-size", arg := some .str, metavar := "MAX_TYPE_SIZE", default := some "100" },
    { id := "max-interface-items", arg := some .str, metavar := "MAX_INTERFACE_ITEMS", default := some "10" },
    { id := "max-world-items", arg := some .str, metavar := "MAX_WORLD_ITEMS", default := some "10" },
    { id := "max-pkg-items", arg := some .str, metavar := "MAX_PKG_ITEMS", default := some "10" },
    { id := "max-type-parts", arg := some .str, metavar := "MAX_TYPE_PARTS", default := some "10" },
    { id := "max-files-per-package", arg := some .str, metavar := "MAX_FILES_PER_PACKAGE", default := some "10" },
    { id := "max-resource-items", arg := some .str, metavar := "MAX_RESOURCE_ITEMS", default := some "10" },
    { id := "async" },
    { id := "futures" },
    { id := "streams" },
    { id := "error-context" },
    { id := "fixed-length-lists" },
    { id := "world-include" },
    { id := "implements" },
    { id := "canonical-names" },
    { id := "arbitrary-config", help := "Indicates that \"arbitrary configuration\" should be used meaning that the input seed is first used to generate the configuration and then afterwards the rest of the seed is used to generate the document" },
    oVerbose,
    oColor,
    oHelp]

/-- `wasm-tools metadata add`. -/
def metadataAdd : Command where
  name := "add"
  about := "Add metadata (module name, producers) to a WebAssembly file"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oGenerateDwarf,
    oG,
    oOutput,
    oVerbose,
    oColor,
    { id := "name", arg := some .str, metavar := "NAME", help := "Add a module or component name to the names section" },
    { id := "clear-name", help := "Remove a module or component name from the names section" },
    { id := "language", arg := some .str, metavar := "NAME=VERSION", help := "Add a programming language to the producers section", repeated := true },
    { id := "processed-by", arg := some .str, metavar := "NAME=VERSION", help := "Add a tool and its version to the producers section", repeated := true },
    { id := "sdk", arg := some .str, metavar := "NAME=VERSION", help := "Add an SDK and its version to the producers section", repeated := true },
    { id := "authors", arg := some .str, metavar := "NAME", help := "Contact details of the people or organization responsible, encoded as a freeform string" },
    { id := "clear-authors", help := "Remove authors from the metadata" },
    { id := "description", arg := some .str, metavar := "NAME", help := "A human-readable description of the binary" },
    { id := "clear-description", help := "Remove description from the metadata" },
    { id := "licenses", arg := some .str, metavar := "NAME", help := "License(s) under which contained software is distributed as an SPDX License Expression" },
    { id := "clear-licenses", help := "Remove licenses from the metadata" },
    { id := "source", arg := some .str, metavar := "NAME", help := "URL to get source code for building the image" },
    { id := "clear-source", help := "Remove source from the metadata" },
    { id := "homepage", arg := some .str, metavar := "NAME", help := "URL to find more information on the binary" },
    { id := "clear-homepage", help := "Remove homepage from the metadata" },
    { id := "revision", arg := some .str, metavar := "NAME", help := "Source control revision identifier for the packaged software" },
    { id := "clear-revision", help := "Remove revision from the metadata" },
    { id := "version", arg := some .str, metavar := "NAME", help := "Version of the packaged software" },
    { id := "clear-version", help := "Remove version from the metadata" },
    oWat,
    oHelp]

/-- `wasm-tools metadata show`. -/
def metadataShow : Command where
  name := "show"
  about := "Read metadata (module name, producers) from a WebAssembly file"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oOutput,
    oVerbose,
    oColor,
    { id := "json", help := "Output in JSON encoding" },
    oHelp]

/-- `wasm-tools metadata`. -/
def metadata : Command where
  name := "metadata"
  about := "Manipulate metadata (module name, producers) to a WebAssembly file"
  opts := [
    oHelpGroup]
  subs := [metadataShow, metadataAdd]

/-- `wasm-tools component unbundle`. -/
def componentUnbundle : Command where
  name := "unbundle"
  about := "Unbundled core wasm modules from a component, switching them from being embedded to being imported"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oGenerateDwarf,
    oG,
    oOutput,
    oVerbose,
    oColor,
    { id := "module-dir", arg := some .str, metavar := "PATH", help := "Where to place unbundled core wasm modules", required := true },
    { id := "threshold", arg := some .str, metavar := "SIZE", help := "The size threshold for core wasm modules to unbundled", default := some "10240" },
    oWat,
    oHelp]

/-- `wasm-tools component semver-check`. -/
def componentSemverCheck : Command where
  name := "semver-check"
  about := "Tool for verifying whether one world is a semver compatible evolution of another"
  pos := [
    { id := "wit", help := "Path to WIT files to load" }]
  opts := [
    oVerbose,
    oColor,
    oFeatures,
    oAllFeatures,
    { id := "prev", arg := some .str, metavar := "PREV", help := "The \"previous\" world, or older version, of what's being tested", required := true },
    { id := "new", arg := some .str, metavar := "NEW", help := "The \"new\" world which is the \"prev\" world but modified", required := true },
    oHelp]

/-- `wasm-tools component link`. -/
def componentLink : Command where
  name := "link"
  about := "Link one or more dynamic library modules, producing a component"
  pos := [
    { id := "module", metavar := "[NAME=]MODULE", arity := .many, help := "Input libraries to link" }]
  opts := [
    { id := "dl-openable", arg := some .str, metavar := "[NAME=]MODULE", help := "Input library to link and make available for dynamic resolution via `dlopen` (may be repeated)", repeated := true },
    { id := "stack-size", arg := some .str, metavar := "STACK_SIZE", help := "Size of stack (in bytes) to allocate in the synthesized main module" },
    oOutput,
    oVerbose,
    oColor,
    oWat2,
    { id := "stub-missing-functions", help := "Generate trapping stubs for any missing functions" },
    { id := "use-built-in-libdl", help := "Use built-in implementations of `dlopen`/`dlsym`" },
    { id := "adapt", arg := some .str, metavar := "[NAME=]MODULE", help := "The path to an adapter module to satisfy imports not otherwise bound to WIT interfaces", repeated := true },
    { id := "validate", arg := some (.enum ["true", "false"]), valueOptional := true, missing := some "true", metavar := "true|false", help := "Whether or not to validate the output component" },
    { id := "realloc-via-memory-grow", help := "Use memory.grow to realloc memory and stack allocation in adapters" },
    { id := "merge-imports-based-on-semver", arg := some (.enum ["true", "false"]), valueOptional := true, missing := some "true", metavar := "true|false", help := "Indicates whether imports into the final component are merged based on semver ranges" },
    oEmitCanonicalNames,
    { id := "reject-legacy-names", help := "Reject usage of the \"legacy\" naming scheme of `wit-component` and require the new naming scheme to be used" },
    { id := "debug-names", arg := some (.enum ["true", "false"]), valueOptional := true, missing := some "true", metavar := "true|false", help := "Whether or not to add debug names to the generated binary" },
    { id := "return-call-ref", arg := some (.enum ["true", "false"]), valueOptional := true, missing := some "true", metavar := "true|false", help := "Whether or not to use `return_call_ref` for shims" },
    oHelp]

/-- `wasm-tools component targets`. -/
def componentTargets : Command where
  name := "targets"
  about := "Tool for verifying whether a component conforms to a world"
  pos := [
    { id := "wit", help := "Path to WIT files to load" },
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oVerbose,
    oColor,
    oFeatures,
    oAllFeatures,
    { id := "world", short := ["w"], arg := some .str, metavar := "WORLD", help := "The world used to test whether a component conforms to its signature. If the `WIT` source provided contains multiple packages, this option must be set, and must be of the fully-qualified form (ex: \"wasi:http/proxy\")" },
    { id := "semver-compatible", help := "Matches interfaces by their canonical names, so semver-compatible versions (e.g. `wasi:cli@0.2.3` and `wasi:cli@0.2.0`) are type-checked against each other" },
    oHelp]

/-- `wasm-tools component embed`. -/
def componentEmbed : Command where
  name := "embed"
  about := "Embeds metadata for a component inside of a core wasm module"
  pos := [
    { id := "wit", help := "Path to WIT files to load" },
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oFeatures,
    oAllFeatures,
    oGenerateDwarf,
    oG,
    oOutput,
    oVerbose,
    oColor,
    { id := "encoding", arg := some .str, metavar := "ENCODING", help := "The expected string encoding format for the component" },
    { id := "world", short := ["w"], arg := some .str, metavar := "WORLD", help := "The world that the component uses" },
    oEmitCanonicalNames,
    { id := "dummy", help := "Don't read a core wasm module as input, instead generating a \"dummy\" module as a placeholder" },
    { id := "dummy-names", arg := some .str, metavar := "DUMMY_NAMES", help := "Same as `--dummy`, but the style of core wasm names is specified" },
    { id := "async-callback", help := "With `--dummy-names legacy`, this will generate a core module such that all the imports are lowered using the async ABI and the exports are lifted using the async-with-callback ABI" },
    { id := "async-stackful", help := "With `--dummy-names legacy`, this will generate a core module such that all the imports are lowered using the async ABI and the exports are lifted using the async-without-callback (i.e. stackful) ABI" },
    oWat2,
    { id := "only-custom", help := "Print the wasm custom section only" },
    oHelp]

/-- `wasm-tools component wit`. -/
def componentWit : Command where
  name := "wit"
  about := "Tool for working with the WIT text format for components"
  pos := [
    { id := "input", arity := .optional, help := "Input file or directory to process" }]
  opts := [
    oVerbose,
    oColor,
    oOutput,
    { id := "wasm", short := ["w"], help := "Emit a WebAssembly binary representation instead of the WIT text format" },
    { id := "wat", short := ["t"], help := "Emit a WebAssembly textual representation instead of the WIT text format" },
    { id := "no-docs", help := "Do not include doc comments when emitting WIT text" },
    { id := "out-dir", arg := some .str, metavar := "OUT_DIR", help := "Emit the entire WIT resolution graph instead of just the \"top level\" package to the output directory specified" },
    { id := "skip-validation", help := "Skips the validation performed when using the `--wasm` and `--wat` options" },
    { id := "json", short := ["j"], help := "Emit the WIT document as JSON instead of text" },
    { id := "importize", help := "Generates WIT to import the component specified to this command" },
    { id := "importize-out-world-name", arg := some .str, metavar := "IMPORTIZE_OUT_WORLD_NAME", help := "The name of the world to generate when using `--importize` or `--importize-world`" },
    { id := "importize-world", arg := some .str, metavar := "WORLD", help := "Generates a WIT world to import a component which corresponds to the selected world" },
    { id := "exportize", help := "Generates WIT to export the component specified to this command" },
    { id := "exportize-out-world-name", arg := some .str, metavar := "EXPORTIZE_OUT_WORLD_NAME", help := "The name of the world to generate when using `--exportize` or `--exportize-world`" },
    { id := "exportize-import", arg := some .str, metavar := "IMPORT", help := "When used with `--exportize` or `--exportize-world`, only move the specified imports to exports. Can be specified multiple times. If not provided, all imports are moved", repeated := true },
    { id := "exportize-world", arg := some .str, metavar := "WORLD", help := "Generates a WIT world to export a component which corresponds to the selected world" },
    { id := "merge-world-imports-based-on-semver", arg := some .str, metavar := "WORLD", help := "Updates the world specified to deduplicate all of its imports based on semver versions" },
    { id := "generate-nominal-type-ids", arg := some .str, metavar := "WORLD", help := "Generates unique type IDs for nominal types in the world provided" },
    oFeatures,
    oAllFeatures,
    oEmitCanonicalNames,
    oHelp]

/-- `wasm-tools component new`. -/
def componentNew : Command where
  name := "new"
  about := "WebAssembly component encoder from an input core wasm binary"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    { id := "import-name", arg := some .str, metavar := "OLD=NEW", help := "Rename an instance import in the output component", repeated := true },
    oGenerateDwarf,
    oG,
    oOutput,
    oVerbose,
    oColor,
    { id := "adapt", arg := some .str, metavar := "[NAME=]MODULE", help := "The path to an adapter module to satisfy imports not otherwise bound to WIT interfaces", repeated := true },
    { id := "validate", arg := some (.enum ["true", "false"]), valueOptional := true, missing := some "true", metavar := "true|false", help := "Whether or not to validate the output component" },
    { id := "realloc-via-memory-grow", help := "Use memory.grow to realloc memory and stack allocation in adapters" },
    { id := "merge-imports-based-on-semver", arg := some (.enum ["true", "false"]), valueOptional := true, missing := some "true", metavar := "true|false", help := "Indicates whether imports into the final component are merged based on semver ranges" },
    oEmitCanonicalNames,
    { id := "reject-legacy-names", help := "Reject usage of the \"legacy\" naming scheme of `wit-component` and require the new naming scheme to be used" },
    { id := "debug-names", arg := some (.enum ["true", "false"]), valueOptional := true, missing := some "true", metavar := "true|false", help := "Whether or not to add debug names to the generated binary" },
    { id := "return-call-ref", arg := some (.enum ["true", "false"]), valueOptional := true, missing := some "true", metavar := "true|false", help := "Whether or not to use `return_call_ref` for shims" },
    oWat2,
    oHelp]

/-- `wasm-tools component`. -/
def component : Command where
  name := "component"
  about := "WebAssembly wit-based component tooling"
  opts := [
    oHelpGroup]
  subs := [componentNew, componentWit, componentEmbed, componentTargets, componentLink, componentSemverCheck, componentUnbundle]

/-- `wasm-tools demangle`. -/
def demangle : Command where
  name := "demangle"
  about := "Demangle Rust and C++ symbol names in the `name` section"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oOutput,
    oVerbose,
    oColor,
    oWat,
    oHelp]

/-- `wasm-tools compose`. -/
def compose : Command where
  name := "compose"
  about := "WebAssembly component composer"
  pos := [
    { id := "component", help := "The path to the root component to compose" }]
  opts := [
    oVerbose,
    oColor,
    oOutput,
    { id := "config", short := ["c"], arg := some .str, metavar := "CONFIG", help := "The path to the configuration file to use" },
    { id := "definitions", short := ["d"], arg := some .str, metavar := "DEFS", help := "Definition components whose exports define import dependencies to fulfill from", repeated := true },
    { id := "search-path", short := ["p"], arg := some .str, metavar := "PATH", help := "A path to search for imports", repeated := true },
    { id := "skip-validation", help := "Skip validation of the composed output component" },
    { id := "no-imports", help := "Do not allow instance imports in the composed output component" },
    oWat,
    { id := "quiet", short := ["q"], help := "Don't print warnings" },
    oHelp,
    versionOpt]

/-- `wasm-tools strip`. -/
def strip : Command where
  name := "strip"
  about := "Removes custom sections from an input WebAssembly file"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oOutput,
    oVerbose,
    oColor,
    { id := "all", short := ["a"], help := "Remove all custom sections, regardless of name" },
    { id := "delete", short := ["d"], arg := some .str, metavar := "REGEX", help := "Remove custom sections matching the specified regex", repeated := true },
    oWat,
    oHelp]

/-- `wasm-tools objdump`. -/
def objdump : Command where
  name := "objdump"
  about := "Dumps information about sections in a WebAssembly file"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oOutput,
    oVerbose,
    oColor,
    oHelp]

/-- `wasm-tools dump`. -/
def dump : Command where
  name := "dump"
  about := "Debugging utility to dump information about a wasm binary"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oOutput,
    oVerbose,
    oColor,
    oHelp]

/-- `wasm-tools mutate`. -/
def mutate : Command where
  name := "mutate"
  about := "A WebAssembly test case mutator"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oOutput,
    oVerbose,
    oColor,
    oWat,
    { id := "seed", short := ["s"], arg := some .str, metavar := "SEED", help := "The RNG seed used to choose which transformation to apply. Given the same input Wasm and same seed, `wasm-mutate` will always generate the same output Wasm", default := some "42" },
    { id := "preserve-semantics", help := "Only perform semantics-preserving transformations on the Wasm module" },
    { id := "fuel", short := ["f"], arg := some .str, metavar := "FUEL", help := "Fuel to control the time of the mutation", default := some "18446744073709551615" },
    { id := "reduce", help := "Only perform size-reducing transformations on the Wasm module. This allows `wasm-mutate` to be used as a test case reducer" },
    oHelp]

/-- `wasm-tools shrink`. -/
def shrink : Command where
  name := "shrink"
  about := "Shrink a Wasm file while maintaining a property of interest (such as triggering a compiler bug)"
  pos := [
    { id := "predicate", help := "The interestingness predicate script" },
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    { id := "attempts", short := ["a"], arg := some .str, metavar := "ATTEMPTS", help := "The number of shrink attempts to try before considering a Wasm module as small as it will ever get", default := some "1000" },
    { id := "allow-empty", help := "Allow shrinking the input down to an empty Wasm module" },
    { id := "seed", short := ["s"], arg := some .str, metavar := "SEED", help := "The RNG seed for choosing which size-reducing mutation to attempt next", default := some "42" },
    oOutput,
    oVerbose,
    oColor,
    oHelp]

/-- `wasm-tools smith`. -/
def smith : Command where
  name := "smith"
  about := "A WebAssembly test case generator"
  pos := [
    { id := "input", arity := .optional, help := "The arbitrary input seed" }]
  opts := [
    oOutput,
    oWat,
    { id := "ensure-termination", help := "Ensure that execution of generated Wasm modules will always terminate" },
    { id := "fuel", short := ["f"], arg := some .str, metavar := "FUEL", help := "The default amount of fuel used with `--ensure-termination`" },
    { id := "config", short := ["c"], arg := some .str, metavar := "CONFIG", help := "JSON configuration file with settings to control the wasm output" },
    { id := "available-imports", arg := some .str, metavar := "AVAILABLE_IMPORTS", help := "The imports that may be used when generating the module" },
    { id := "exports", arg := some .str, metavar := "EXPORTS", help := "If provided, the generated module will have exports with exactly the same names and types as those in the provided WebAssembly module. The implementation (e.g. function bodies, global initializers) of each export in the generated module will be random and unrelated to the implementation in the provided module" },
    { id := "module-shape", arg := some .str, metavar := "MODULE_SHAPE", help := "If provided, the generated module will have imports and exports with exactly the same names and types as those in the provided WebAssembly module" },
    { id := "allow-start-export", arg := some (.enum ["true", "false"]), metavar := "ALLOW_START_EXPORT", help := "Determines whether a `start` export may be included. Defaults to `true`" },
    { id := "allowed-instructions", arg := some .str, metavar := "ALLOWED_INSTRUCTIONS", help := "The kinds of instructions allowed in the generated wasm programs. Defaults to all" },
    { id := "allow-floats", arg := some (.enum ["true", "false"]), metavar := "ALLOW_FLOATS", help := "Determines whether we generate floating point instructions and types" },
    { id := "bulk-memory-enabled", arg := some (.enum ["true", "false"]), metavar := "BULK_MEMORY_ENABLED", help := "Determines whether the bulk memory proposal is enabled for generating instructions" },
    { id := "canonicalize-nans", arg := some (.enum ["true", "false"]), metavar := "CANONICALIZE_NANS", help := "Returns whether NaN values are canonicalized after all f32/f64 operation. Defaults to false" },
    { id := "disallow-traps", arg := some (.enum ["true", "false"]), metavar := "DISALLOW_TRAPS", help := "Returns whether we should avoid generating code that will possibly trap" },
    { id := "exceptions-enabled", arg := some (.enum ["true", "false"]), metavar := "EXCEPTIONS_ENABLED", help := "Determines whether the exception-handling proposal is enabled for generating instructions" },
    { id := "export-everything", arg := some (.enum ["true", "false"]), metavar := "EXPORT_EVERYTHING", help := "Export all WebAssembly objects in the module. Defaults to false" },
    { id := "gc-enabled", arg := some (.enum ["true", "false"]), metavar := "GC_ENABLED", help := "Determines whether the GC proposal is enabled when generating a Wasm module" },
    { id := "compact-imports-enabled", arg := some (.enum ["true", "false"]), metavar := "COMPACT_IMPORTS_ENABLED", help := "Determines whether compact import section proposal is enabled" },
    { id := "custom-descriptors-enabled", arg := some (.enum ["true", "false"]), metavar := "CUSTOM_DESCRIPTORS_ENABLED", help := "Determines whether the custom descriptors proposal is enabled when generating a Wasm module" },
    { id := "custom-page-sizes-enabled", arg := some (.enum ["true", "false"]), metavar := "CUSTOM_PAGE_SIZES_ENABLED", help := "Determines whether the custom-page-sizes proposal is enabled when generating a Wasm module" },
    { id := "generate-custom-sections", arg := some (.enum ["true", "false"]), metavar := "GENERATE_CUSTOM_SECTIONS", help := "Returns whether we should generate custom sections or not. Defaults to false" },
    { id := "max-aliases", arg := some .str, metavar := "MAX_ALIASES", help := "Returns the maximal size of the `alias` section. Defaults to 1000" },
    { id := "max-components", arg := some .str, metavar := "MAX_COMPONENTS", help := "The maximum number of components to use. Defaults to 10" },
    { id := "max-data-segments", arg := some .str, metavar := "MAX_DATA_SEGMENTS", help := "The maximum number of data segments to generate. Defaults to 100" },
    { id := "max-element-segments", arg := some .str, metavar := "MAX_ELEMENT_SEGMENTS", help := "The maximum number of element segments to generate. Defaults to 100" },
    { id := "max-elements", arg := some .str, metavar := "MAX_ELEMENTS", help := "The maximum number of elements within a segment to generate. Defaults to 100" },
    { id := "max-exports", arg := some .str, metavar := "MAX_EXPORTS", help := "The maximum number of exports to generate. Defaults to 100" },
    { id := "max-funcs", arg := some .str, metavar := "MAX_FUNCS", help := "The maximum number of functions to generate. Defaults to 100.  This includes imported functions" },
    { id := "max-globals", arg := some .str, metavar := "MAX_GLOBALS", help := "The maximum number of globals to generate. Defaults to 100.  This includes imported globals" },
    { id := "max-imports", arg := some .str, metavar := "MAX_IMPORTS", help := "The maximum number of imports to generate. Defaults to 100" },
    { id := "max-instances", arg := some .str, metavar := "MAX_INSTANCES", help := "The maximum number of instances to use. Defaults to 10" },
    { id := "max-instructions", arg := some .str, metavar := "MAX_INSTRUCTIONS", help := "The maximum number of instructions to generate in a function body. Defaults to 100" },
    { id := "max-memories", arg := some .str, metavar := "MAX_MEMORIES", help := "The maximum number of memories to use. Defaults to 1" },
    { id := "max-memory32-bytes", arg := some .str, metavar := "MAX_MEMORY32_BYTES", help := "The maximum, in bytes, of any 32-bit memory's initial or maximum size" },
    { id := "max-memory64-bytes", arg := some .str, metavar := "MAX_MEMORY64_BYTES", help := "The maximum, in bytes, of any 64-bit memory's initial or maximum size" },
    { id := "max-modules", arg := some .str, metavar := "MAX_MODULES", help := "The maximum number of modules to use. Defaults to 10" },
    { id := "max-nesting-depth", arg := some .str, metavar := "MAX_NESTING_DEPTH", help := "Returns the maximal nesting depth of modules with the component model proposal. Defaults to 10" },
    { id := "max-table-elements", arg := some .str, metavar := "MAX_TABLE_ELEMENTS", help := "The maximum, elements, of any table's initial or maximum size. Defaults to 1 million" },
    { id := "max-tables", arg := some .str, metavar := "MAX_TABLES", help := "The maximum number of tables to use. Defaults to 1" },
    { id := "max-tags", arg := some .str, metavar := "MAX_TAGS", help := "The maximum number of tags to generate. Defaults to 100" },
    { id := "max-type-size", arg := some .str, metavar := "MAX_TYPE_SIZE", help := "Returns the maximal effective size of any type generated by wasm-smith" },
    { id := "max-types", arg := some .str, metavar := "MAX_TYPES", help := "The maximum number of types to generate. Defaults to 100" },
    { id := "max-values", arg := some .str, metavar := "MAX_VALUES", help := "The maximum number of values to use. Defaults to 10" },
    { id := "memory64-enabled", arg := some (.enum ["true", "false"]), metavar := "MEMORY64_ENABLED", help := "Returns whether 64-bit memories are allowed. Defaults to true" },
    { id := "memory-max-size-required", arg := some (.enum ["true", "false"]), metavar := "MEMORY_MAX_SIZE_REQUIRED", help := "Whether every Wasm memory must have a maximum size specified. Defaults to `false`" },
    { id := "memory-offset-choices", arg := some .str, metavar := "MEMORY_OFFSET_CHOICES", help := "Control the probability of generating memory offsets that are in bounds vs. potentially out of bounds" },
    { id := "min-data-segments", arg := some .str, metavar := "MIN_DATA_SEGMENTS", help := "The minimum number of data segments to generate. Defaults to 0" },
    { id := "min-element-segments", arg := some .str, metavar := "MIN_ELEMENT_SEGMENTS", help := "The minimum number of element segments to generate. Defaults to 0" },
    { id := "min-elements", arg := some .str, metavar := "MIN_ELEMENTS", help := "The minimum number of elements within a segment to generate. Defaults to 0" },
    { id := "min-exports", arg := some .str, metavar := "MIN_EXPORTS", help := "The minimum number of exports to generate. Defaults to 0" },
    { id := "min-funcs", arg := some .str, metavar := "MIN_FUNCS", help := "The minimum number of functions to generate. Defaults to 0" },
    { id := "min-globals", arg := some .str, metavar := "MIN_GLOBALS", help := "The minimum number of globals to generate. Defaults to 0" },
    { id := "min-imports", arg := some .str, metavar := "MIN_IMPORTS", help := "The minimum number of imports to generate. Defaults to 0" },
    { id := "min-memories", arg := some .str, metavar := "MIN_MEMORIES", help := "The minimum number of memories to use. Defaults to 0" },
    { id := "min-tables", arg := some .str, metavar := "MIN_TABLES", help := "The minimum number of tables to use. Defaults to 0" },
    { id := "min-tags", arg := some .str, metavar := "MIN_TAGS", help := "The minimum number of tags to generate. Defaults to 0" },
    { id := "min-types", arg := some .str, metavar := "MIN_TYPES", help := "The minimum number of types to generate. Defaults to 0" },
    { id := "min-uleb-size", arg := some .str, metavar := "MIN_ULEB_SIZE", help := "The minimum size, in bytes, of all leb-encoded integers. Defaults to 1" },
    { id := "multi-value-enabled", arg := some (.enum ["true", "false"]), metavar := "MULTI_VALUE_ENABLED", help := "Determines whether the multi-value results are enabled" },
    { id := "reference-types-enabled", arg := some (.enum ["true", "false"]), metavar := "REFERENCE_TYPES_ENABLED", help := "Determines whether the reference types proposal is enabled for generating instructions" },
    { id := "relaxed-simd-enabled", arg := some (.enum ["true", "false"]), metavar := "RELAXED_SIMD_ENABLED", help := "Determines whether the Relaxed SIMD proposal is enabled for generating instructions" },
    { id := "saturating-float-to-int-enabled", arg := some (.enum ["true", "false"]), metavar := "SATURATING_FLOAT_TO_INT_ENABLED", help := "Determines whether the non-trapping float-to-int conversions proposal is enabled" },
    { id := "sign-extension-ops-enabled", arg := some (.enum ["true", "false"]), metavar := "SIGN_EXTENSION_OPS_ENABLED", help := "Determines whether the sign-extension-ops proposal is enabled" },
    { id := "shared-everything-threads-enabled", arg := some (.enum ["true", "false"]), metavar := "SHARED_EVERYTHING_THREADS_ENABLED", help := "Determines whether the shared-everything-threads proposal is enabled" },
    { id := "simd-enabled", arg := some (.enum ["true", "false"]), metavar := "SIMD_ENABLED", help := "Determines whether the SIMD proposal is enabled for generating instructions" },
    { id := "tail-call-enabled", arg := some (.enum ["true", "false"]), metavar := "TAIL_CALL_ENABLED", help := "Determines whether the tail calls proposal is enabled for generating instructions" },
    { id := "table-max-size-required", arg := some (.enum ["true", "false"]), metavar := "TABLE_MAX_SIZE_REQUIRED", help := "Whether every Wasm table must have a maximum size specified. Defaults to `false`" },
    { id := "threads-enabled", arg := some (.enum ["true", "false"]), metavar := "THREADS_ENABLED", help := "Determines whether the threads proposal is enabled" },
    { id := "allow-invalid-funcs", arg := some (.enum ["true", "false"]), metavar := "ALLOW_INVALID_FUNCS", help := "Indicates whether wasm-smith is allowed to generate invalid function bodies" },
    { id := "wide-arithmetic-enabled", arg := some (.enum ["true", "false"]), metavar := "WIDE_ARITHMETIC_ENABLED", help := "Determines whether the [wide-arithmetic proposal] is enabled" },
    { id := "extended-const-enabled", arg := some (.enum ["true", "false"]), metavar := "EXTENDED_CONST_ENABLED", help := "Determines whether the [extended-const proposal] is enabled" },
    { id := "const-expr-fuel", arg := some .str, metavar := "CONST_EXPR_FUEL", help := "Fuel limiting factor used when generating constant expressions" },
    { id := "limit-arrays-in-const-exprs", arg := some (.enum ["true", "false"]), metavar := "LIMIT_ARRAYS_IN_CONST_EXPRS", help := "Whether or not to limit the size of arrays generated in constant expressions" },
    oVerbose,
    oColor,
    oHelp]

/-- `wasm-tools print`. -/
def printCmd : Command where
  name := "print"
  aliases := ["wasm2wat"]
  about := "Print the textual form of a WebAssembly binary"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oGenerateDwarf,
    oG,
    oOutput,
    oVerbose,
    oColor,
    { id := "print-offsets", short := ["p"], help := "Whether or not to print binary offsets intermingled in the text format as comments for debugging" },
    { id := "skeleton", help := "Indicates that the \"skeleton\" of a module should be printed" },
    { id := "name-unnamed", help := "Ensure all wasm items have `$`-based names, even if they don't have an entry in the `name` section" },
    { id := "fold-instructions", short := ["f"], help := "Print instructions in the folded format. (See https://webassembly.github.io/spec/core/text/instructions.html#folded-instructions)" },
    { id := "print-operand-stack", help := "Print the contents of the operand stack within function bodies" },
    { id := "indent-text", arg := some .str, metavar := "INDENT_TEXT", help := "The string to use when indenting" },
    { id := "indent", arg := some .str, metavar := "INDENT", help := "Number of spaces used for indentation, has lower priority than `--indent-text`" },
    oHelp]

/-- `wasm-tools validate`. -/
def validate : Command where
  name := "validate"
  about := "Validate a WebAssembly binary"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oGenerateDwarf,
    oG,
    { id := "features", short := ["f"], arg := some .str, metavar := "FEATURES", help := "Comma-separated list of WebAssembly features to enable during validation", repeated := true },
    oVerbose,
    oColor,
    { id := "validate-custom", help := "Opt-in to validating the contents of custom sections" },
    oHelp]

/-- `wasm-tools parse`. -/
def parse : Command where
  name := "parse"
  aliases := ["wat2wasm"]
  about := "Parse the WebAssembly text format"
  pos := [
    { id := "input", arity := .optional, help := "Input file to process" }]
  opts := [
    oGenerateDwarf,
    oG,
    oOutput,
    oVerbose,
    oColor,
    oWat,
    oHelp]

/-- The exit codes of `wasm-tools` (clap's conventions and the commands' `Exit status`
notes). -/
def exits : List (Nat × String) :=
  [(0, "success; also -h/--help, help, -V/--version"),
   (1, "the command failed (e.g. an unreadable or invalid input; `validate` of an invalid module)"),
   (2, "a usage error (unknown option or subcommand, missing or invalid value, repeated option, missing required argument), or no subcommand (help on stderr)")]

/-- `wasm-tools`. -/
def root : Command where
  name := "wasm-tools"
  exits := exits
  version := some "1.262.0"
  opts := [
    oHelpGroup,
    versionOpt]
  subs := [parse, validate, printCmd, smith, shrink, mutate, dump, objdump, strip, compose, demangle, component, metadata, witSmith, witDylib, addr2line, completion, jsonFromWast, wast]

/-- The commands with `--generate-dwarf` and `-g` (they conflict). -/
def dwarfPaths : List (List String) :=
  [["parse"], ["validate"], ["print"], ["component", "new"], ["component", "embed"],
   ["component", "unbundle"], ["metadata", "add"], ["addr2line"]]


/-- The values of `wast --assert` (clap's `value_delimiter = ','` with possible values: each
part is checked, `checksAt`; the help lists them, `Clap.Tool.choices`). -/
def assertValues : List String :=
  ["default", "pretty-whitespace", "snapshot-print", "snapshot-json", "snapshot-folded",
    "test-folded", "no-test-folded", "permissive"]

/-- The Wasm features `validate` and `wast` accept (`wasmparser::WasmFeatures::FLAGS`, the
groups and `all`, as upstream's `invalid value` message lists them). -/
def wasmFeatures : List String :=
  ["mutable-global", "saturating-float-to-int", "sign-extension", "reference-types",
    "multi-value", "bulk-memory", "simd", "relaxed-simd", "threads",
    "shared-everything-threads", "tail-call", "floats", "multi-memory", "exceptions",
    "memory64", "extended-const", "component-model", "function-references",
    "memory-control", "gc", "custom-page-sizes", "legacy-exceptions", "gc-types",
    "stack-switching", "wide-arithmetic", "cm-values", "cm-nested-names", "cm-async",
    "cm-async-stackful", "cm-more-async-builtins", "cm-threading", "cm-error-context",
    "cm-fixed-length-lists", "cm-gc", "call-indirect-overlong", "bulk-memory-opt",
    "custom-descriptors", "compact-imports", "cm-map", "cm64", "cm-implements",
    "cm-canon-names", "cm-forward", "cm-accessors", "mvp", "wasm1", "wasm2", "wasm3",
    "lime1", "all"]

/-- The instruction kinds of `smith --allowed-instructions` (`InstructionKind::from_str`,
case-insensitive). -/
def instructionKinds : List String :=
  ["numeric_non_float", "numeric", "vector_non_float", "vector", "reference",
    "parametric", "variable", "table", "memory_non_float", "memory", "control",
    "aggregate"]

/-- Options read as `usize` or `u64` (wasm-smith's `Config`, wit-smith's, shrink and mutate). -/
def u64Options : List String :=
  ["max-aliases", "max-components", "max-data-segments", "max-elements",
    "max-element-segments", "max-exports", "max-files-per-package", "max-funcs",
    "max-globals", "max-imports", "max-instances", "max-instructions",
    "max-interface-items", "max-memories", "max-memory32-bytes", "max-modules",
    "max-nesting-depth", "max-packages", "max-pkg-items", "max-resource-items",
    "max-table-elements", "max-tables", "max-tags", "max-type-parts", "max-types",
    "max-type-size", "max-values", "max-world-items", "min-data-segments", "min-elements",
    "min-element-segments", "min-exports", "min-funcs", "min-globals", "min-imports",
    "min-tags", "min-types", "threshold", "indent", "seed", "fuel"]

/-- Options read as `u32`. -/
def u32Options : List String :=
  ["const-expr-fuel", "min-memories", "min-tables", "stack-size", "attempts"]

/-- The value checks of clap's value parsers (from the 1.262.0 sources; see the module doc). -/
def checks : List (String × ValueCheck) :=
  [("color", .oneOf ["always", "always-ansi", "never", "auto"]),
   ("generate-dwarf", .oneOf ["lines", "full"]),
   ("encoding", .oneOf ["utf8", "utf16", "compact-utf16"]),
   ("dummy-names", .oneOf ["legacy", "standard32"]),
   ("allowed-instructions", .listOf ',' false (.oneOf instructionKinds (ci := true))),
   ("memory-offset-choices", .tuple 3 ',' (.fromStr 32)),
   ("min-uleb-size", .uint 8),
   ("max-memory64-bytes", .uint 128),
   ("import-name", .keyValue), ("language", .keyValue), ("processed-by", .keyValue),
   ("sdk", .keyValue),
   ("source", .absUrl), ("homepage", .absUrl),
   ("licenses", .external "an SPDX license expression"),
   ("adapt", .external "a readable Wasm or WAT file"),
   ("dl-openable", .external "a readable Wasm or WAT file"),
   ("module", .external "a readable Wasm or WAT file")] ++
  u64Options.map (·, .uint 64) ++ u32Options.map (·, .uint 32)

/-- Checks of one command: the Wasm feature lists, and wasm-smith's `u32` widths. -/
def checksAt : List (List String × String × ValueCheck) :=
  [(["validate"], "features", .listOf ',' true (.negatable (.oneOf wasmFeatures))),
   (["wast"], "features", .listOf ',' true (.negatable (.oneOf wasmFeatures))),
   (["wast"], "assert", .listOf ',' false (.oneOf assertValues)),
   (["smith"], "fuel", .uint 32), (["smith"], "max-type-size", .uint 32)]

/-- The `conflicts_with` pairs of `component wit` (`WitOpts` of `component.rs`, each pair once,
in source order). -/
def witConflicts : List (String × String) :=
  [("wasm", "wat"), ("wasm", "out-dir"), ("wat", "out-dir"), ("out-dir", "output"),
   ("json", "wasm"), ("json", "out-dir"), ("json", "wat")] ++
  (let xs := ["importize", "importize-world", "exportize", "exportize-world",
      "merge-world-imports-based-on-semver", "generate-nominal-type-ids"]
   -- every pair of these six excludes each other
   xs.zipIdx.flatMap fun (a, i) => (xs.drop (i + 1)).map fun b => (a, b))

/-- `requires` and `conflicts_with` (from the 1.262.0 sources). -/
def rules : List (List String × Rule) :=
  [(["component", "embed"], .requires "async-callback" "dummy-names"),
   (["component", "embed"], .requires "async-stackful" "dummy-names"),
   (["component", "embed"], .conflicts "async-callback" "async-stackful"),
   (["component", "embed"], .conflicts "dummy" "dummy-names"),
   (["component", "embed"], .conflicts "only-custom" "wat"),
   (["component", "embed"], .conflicts "only-custom" "dummy"),
   (["component", "embed"], .conflicts "only-custom" "dummy-names")] ++
  (["name", "authors", "description", "licenses", "source", "homepage", "revision",
    "version"].map fun f => (["metadata", "add"], .conflicts f ("clear-" ++ f))) ++
  (dwarfPaths.map fun p => (p, .conflicts "generate-dwarf" "-g")) ++
  (witConflicts.map fun (a, b) => (["component", "wit"], .conflicts a b))

/-- The grammar with its value checks and rules: `checks` in force everywhere, `checksAt` at
their commands, `rules` at theirs. -/
def grammar : Command :=
  ((checksAt.foldl (fun c e => c.withChecksAt e.1 [e.2]) (root.withChecks checks)).withRules rules)

/-- Rust's `ParseIntError` message for a refused unsigned integer (`uN::from_str`). -/
def intReason (v : String) : String :=
  let ds := match v.toList with
    | '+' :: r => r
    | r => r
  if v.isEmpty then "cannot parse integer from empty string"
  else if !ds.isEmpty && ds.all Char.isDigit then "number too large to fit in target type"
  else "invalid digit found in string"

/-- The parts of a comma-separated list as `parse_features` reads them (trimmed, empty ones
skipped). -/
def listParts (v : String) : List String :=
  ((v.splitOn ",").map fun p => String.ofList (ValueCheck.trim p.toList)).filter (!·.isEmpty)

/-- **The reasons of upstream's value parsers** (1.262.0 sources, see the module doc), printed
after `invalid value 'V' for 'NAME'`: by argument id, for a refused value. The integer
parsers' reasons are clap's own (`Silmaril.Cli.Clap.Exact.checkReason`). -/
def reason (id v : String) : Option String :=
  match id with
  | "generate-dwarf" => some ("unknown `--generate-dwarf` setting: " ++ v)
  | "color" => some ("unrecognized color choice '" ++ v ++
      "': valid choices are: always, always-ansi, never, auto")
  | "features" =>
    let bad := (listParts v).find? fun p =>
      !wasmFeatures.contains (match p.toList with | '-' :: r => String.ofList r | _ => p)
    bad.map fun p =>
      let f := match p.toList with | '-' :: r => String.ofList r | _ => p
      "unknown feature `" ++ f ++ "`\nValid features: " ++ ", ".intercalate wasmFeatures
  | "allowed-instructions" =>
    ((v.splitOn ",").find? fun p => !instructionKinds.contains (p.map Char.toLower)).map
      ("unknown instruction kind: " ++ ·)
  | "memory-offset-choices" =>
    let parts := v.splitOn ","
    if parts.length != 3 then some "need 3 comma separated values"
    else (parts.find? fun p => ValueCheck.eval (.fromStr 32) p.toList != some true).map intReason
  | "import-name" => some "expected `--import-name` option to be of the form `OLD=NEW`"
  | "encoding" => some ("unknown string encoding `" ++ v ++ "`")
  | "dummy-names" => some ("unknown name mangling `" ++ v ++
      "`, supported values are `legacy` or `standard32`")
  | "language" | "processed-by" | "sdk" => some "expected KEY=VALUE"
  | "source" | "homepage" => some "relative URL without a base"
  | _ => none

/-- `wasm-tools` 1.262.0, in the clap dialect, without its presentation function. -/
def toolBase : Clap.Tool where
  grammar := grammar
  after := Doc.after
  long := Doc.long
  choices := [(["wast"], "assert", assertValues)]

/-- `wasm-tools` 1.262.0, in the clap dialect: help, version and usage errors in clap's exact
texts (`Clap.Tool.exact`). -/
def tool : Clap.Tool := { toolBase with present := some (toolBase.exact reason) }

/-- The clap view of `wasm-tools` (help, usage, corpus). -/
def wasmTools : Surface.Tool := tool.surface

/-- The clap view of the root command. -/
def surface : Surface.Command := wasmTools.root

end Silmaril.Cli.Spec.WasmTools
