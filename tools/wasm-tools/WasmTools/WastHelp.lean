/-! Help texts of `wasm-tools json-from-wast` and `wasm-tools wast` 1.262.0, as clap prints
them when stdout is not a terminal (captured from the pinned binary; see
`tools/wasm-tools/tests/wast/help/`). Generated: do not edit. -/

namespace WasmTools.WastHelp

def jsonShort : String := r##"Convert a `*.wast` WebAssembly spec test into a `*.json` file and `*.wasm` files

Usage: wasm-tools json-from-wast [OPTIONS] <WAST>

Arguments:
  <WAST>  Input `*.wast` file that will be parsed and converted to JSON

Options:
  -v, --verbose...
          Use verbose output (-v info, -vv debug, -vvv trace)
      --color <COLOR>
          Configuration over whether terminal colors are used in output [default: auto]
  -o, --output <OUTPUT>
          Where to place output
      --wasm-dir <WASM_DIR>
          Where to place binary and text WebAssembly files referenced by tests
      --pretty
          Output pretty-printed JSON instead of compact json
      --allow-confusing-unicode <true|false>
          Controls the "allow confusing unicode" option which will reject parsing files that have
          unusual characters [possible values: true, false]
  -h, --help
          Print help (see more with '--help')
"##

def jsonLong : String := r##"Convert a `*.wast` WebAssembly spec test into a `*.json` file and `*.wasm` files.

This subcommand will parse a wasm spec test, in the `*.wast` format, and then emit both a JSON file
and a number of auxiliary modules. This can perform all the parsing for various implementations of
the wasm text format while deferring the actual processing of all commands.

This subcommand is modelled after WABT's `wast2json` tool, found at
<https://github.com/WebAssembly/wabt>. More documentation of the format can be found at
<https://github.com/WebAssembly/wabt/blob/main/docs/wast2json.md>.

Note that this subcommand does not output precisely the same output as `wast2json`, but there should
be no major discrepancies.

This will also emit a number of `*.wasm` and `*.wat` files in the current directory (or in
`--wasm-dir`) which the JSON will reference. This command will print the JSON to stdout unless the
`-o` flag is given.

Usage: wasm-tools json-from-wast [OPTIONS] <WAST>

Arguments:
  <WAST>
          Input `*.wast` file that will be parsed and converted to JSON

Options:
  -v, --verbose...
          Use verbose output (-v info, -vv debug, -vvv trace)

      --color <COLOR>
          Configuration over whether terminal colors are used in output.
          
          Supports one of `auto|never|always|always-ansi`. The default is to detect what to do based
          on the terminal environment, for example by using `isatty`.
          
          [default: auto]

  -o, --output <OUTPUT>
          Where to place output.
          
          Required when printing WebAssembly binary output.
          
          If not provided, then stdout is used.

      --wasm-dir <WASM_DIR>
          Where to place binary and text WebAssembly files referenced by tests.
          
          Defaults to the current directory.

      --pretty
          Output pretty-printed JSON instead of compact json

      --allow-confusing-unicode <true|false>
          Controls the "allow confusing unicode" option which will reject parsing files that have
          unusual characters.
          
          This is defaulted to `true` to enable parsing all upstream spec tests but can be disabled
          if desired too.
          
          [possible values: true, false]

  -h, --help
          Print help (see a summary with '-h')
"##

def wastShort : String := r##"A subcommand to test `*.wast` files short of executing WebAssembly code

Usage: wasm-tools wast [OPTIONS] [INPUT]

Arguments:
  [INPUT]  Input file to process

Options:
  -v, --verbose...               Use verbose output (-v info, -vv debug, -vvv trace)
      --color <COLOR>            Configuration over whether terminal colors are used in output
                                 [default: auto]
      --ignore-error-messages    Whether to ignore the error message expectation in `(assert_invalid
                                 ..)` directives
  -f, --features <FEATURES>      Comma-separated list of WebAssembly features to enable during
                                 validation
      --allow-confusing-unicode  Whether or not "confusing unicode characters" are allowed to be
                                 present in `*.wast` files
  -a, --assert <ASSERT>          Perform extra internal assertions in `wasm-tools` itself over the
                                 provided test [possible values: default, pretty-whitespace,
                                 snapshot-print, snapshot-json, snapshot-folded, test-folded,
                                 no-test-folded, permissive]
      --snapshot <SNAPSHOT>      Directory to place snapshots in with `--assert snapshot-*` flags
  -h, --help                     Print help (see more with '--help')
"##

def wastLong : String := r##"A subcommand to test `*.wast` files short of executing WebAssembly code.

This subcommand can be used to validate the `*.wast` test format used by the WebAssembly spec
interpreter. This command takes a single test case as input and it will validate as much as it can
about it including:

* The syntax of the test is valid. * Modules that are declared to be valid are indeed valid. *
Modules that are declared to be invalid are indeed invalid.

This subcommand does not actually execute any WebAssembly code, so the `*.wast` test is not
guaranteed to pass in a real runtime if passed to a runtime. This can be used as a quick check to
double-check that a file is almost all valid, however.

The `wasm-tools` project itself also heavily relies on this subcommand for internal testing, so many
tests for `wasm-tools` use this subcommand as a way to write tests.

Usage: wasm-tools wast [OPTIONS] [INPUT]

Arguments:
  [INPUT]
          Input file to process.
          
          If not provided or if this is `-` then stdin is read entirely and processed.

Options:
  -v, --verbose...
          Use verbose output (-v info, -vv debug, -vvv trace)

      --color <COLOR>
          Configuration over whether terminal colors are used in output.
          
          Supports one of `auto|never|always|always-ansi`. The default is to detect what to do based
          on the terminal environment, for example by using `isatty`.
          
          [default: auto]

      --ignore-error-messages
          Whether to ignore the error message expectation in `(assert_invalid ..)` directives.
          
          When enabled this will only assert that modules produce an error, not that the error
          produced by wasm-tools matches that written in the test itself.

  -f, --features <FEATURES>
          Comma-separated list of WebAssembly features to enable during validation.
          
          If a "-" character is present in front of a feature it will disable that feature. For
          example "-simd" will disable the simd proposal.
          
          The placeholder "all" can be used to enable all wasm features and the term "-all" can be
          used to disable all features.
          
          The default set of features enabled are all WebAssembly proposals that are at phase 4 or
          after. This means that the default set of features accepted are relatively bleeding edge.
          Versions of the WebAssembly specification can also be selected. The "wasm1" or "mvp"
          feature can select the original WebAssembly specification and "wasm2" can be used to
          select the 2.0 version.
          
          Available feature options can be found in the wasmparser crate:
          <https://github.com/bytecodealliance/wasm-tools/blob/main/crates/wasmparser/src/features.rs>

      --allow-confusing-unicode
          Whether or not "confusing unicode characters" are allowed to be present in `*.wast` files.
          
          The default for this is `false`.

  -a, --assert <ASSERT>
          Perform extra internal assertions in `wasm-tools` itself over the provided test.
          
          This is used within the testing of `wasm-tools` itself to perform more tests by default
          such as asserting that the text format round-trips where possible. Asserts can be listed
          here to perform extra checks when validating the `*.wast` input.
          
          [possible values: default, pretty-whitespace, snapshot-print, snapshot-json,
          snapshot-folded, test-folded, no-test-folded, permissive]

      --snapshot <SNAPSHOT>
          Directory to place snapshots in with `--assert snapshot-*` flags

  -h, --help
          Print help (see a summary with '-h')
"##

end WasmTools.WastHelp
