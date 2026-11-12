/-!
# Help texts of `validate`, `strip`, `objdump` and `dump`

clap's `-h` and `--help` output of wasm-tools 1.262.0 (binary SHA-256
`fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211`), captured verbatim from the
pinned binary (`wasm-tools <cmd> -h`, `wasm-tools <cmd> --help`). The text is upstream's
documentation (Apache-2.0 WITH LLVM-exception / MIT). Regenerate with the script in
`tools/wasm-tools/tests/README.md`.
-/

namespace WasmTools.HelpV

/-- `wasm-tools validate -h`. -/
def validate_short : String :=
  "Validate a WebAssembly binary

Usage: wasm-tools validate [OPTIONS] [INPUT]

Arguments:
  [INPUT]  Input file to process

Options:
      --generate-dwarf <lines|full>  Optionally generate DWARF debugging information from
                                     WebAssembly text files
  -g                                 Shorthand for `--generate-dwarf full`
  -f, --features <FEATURES>          Comma-separated list of WebAssembly features to enable during
                                     validation
  -v, --verbose...                   Use verbose output (-v info, -vv debug, -vvv trace)
      --color <COLOR>                Configuration over whether terminal colors are used in output
                                     [default: auto]
      --validate-custom              Opt-in to validating the contents of custom sections
  -h, --help                         Print help (see more with '--help')

Examples:

    # Validate `foo.wasm` with the default Wasm feature proposals.
    $ wasm-tools validate foo.wasm

    # Validate `foo.wasm` with more verbose output
    $ wasm-tools validate -vv foo.wasm

    # Validate `fancy.wasm` with all Wasm feature proposals enabled.
    $ wasm-tools validate --features all fancy.wasm

    # Validate `mvp.wasm` with the original wasm feature set enabled.
    $ wasm-tools validate --features=wasm1 mvp.wasm
    $ wasm-tools validate --features=mvp mvp.wasm

Exit status:
    0 if the binary is valid,
    nonzero if the binary is not valid.
"

/-- `wasm-tools validate --help`. -/
def validate_long : String :=
  "Validate a WebAssembly binary

This subcommand will validate a WebAssembly binary to determine if it's valid or not. This
implements the validation algorithm of the WebAssembly specification
<https://webassembly.github.io/spec/core/valid/index.html>. No output is printed if the binary is
valid; an error message is printed to stderr if the binary is not valid. A WebAssembly text file can
also be used.

Extra information will be included in the error message if the input WebAssembly binary contains
DWARF debugging information.

Usage: wasm-tools validate [OPTIONS] [INPUT]

Arguments:
  [INPUT]
          Input file to process.
          
          If not provided or if this is `-` then stdin is read entirely and processed. Note that for
          most subcommands this input can either be a binary `*.wasm` file or a textual format
          `*.wat` file.

Options:
      --generate-dwarf <lines|full>
          Optionally generate DWARF debugging information from WebAssembly text files.
          
          When the input to this command is a WebAssembly text file, such as `*.wat`, then this
          option will instruct the text parser to insert DWARF debugging information to map binary
          locations back to the original source locations in the input `*.wat` file. This option has
          no effect if the `INPUT` argument is already a WebAssembly binary or if the text format
          uses `(module binary ...)`.

  -g
          Shorthand for `--generate-dwarf full`

  -f, --features <FEATURES>
          Comma-separated list of WebAssembly features to enable during validation.
          
          If a \"-\" character is present in front of a feature it will disable that feature. For
          example \"-simd\" will disable the simd proposal.
          
          The placeholder \"all\" can be used to enable all wasm features and the term \"-all\" can be
          used to disable all features.
          
          The default set of features enabled are all WebAssembly proposals that are at phase 4 or
          after. This means that the default set of features accepted are relatively bleeding edge.
          Versions of the WebAssembly specification can also be selected. The \"wasm1\" or \"mvp\"
          feature can select the original WebAssembly specification and \"wasm2\" can be used to
          select the 2.0 version.
          
          Available feature options can be found in the wasmparser crate:
          <https://github.com/bytecodealliance/wasm-tools/blob/main/crates/wasmparser/src/features.rs>

  -v, --verbose...
          Use verbose output (-v info, -vv debug, -vvv trace)

      --color <COLOR>
          Configuration over whether terminal colors are used in output.
          
          Supports one of `auto|never|always|always-ansi`. The default is to detect what to do based
          on the terminal environment, for example by using `isatty`.
          
          [default: auto]

      --validate-custom
          Opt-in to validating the contents of custom sections

  -h, --help
          Print help (see a summary with '-h')

Examples:

    # Validate `foo.wasm` with the default Wasm feature proposals.
    $ wasm-tools validate foo.wasm

    # Validate `foo.wasm` with more verbose output
    $ wasm-tools validate -vv foo.wasm

    # Validate `fancy.wasm` with all Wasm feature proposals enabled.
    $ wasm-tools validate --features all fancy.wasm

    # Validate `mvp.wasm` with the original wasm feature set enabled.
    $ wasm-tools validate --features=wasm1 mvp.wasm
    $ wasm-tools validate --features=mvp mvp.wasm

Exit status:
    0 if the binary is valid,
    nonzero if the binary is not valid.
"

/-- `wasm-tools strip -h`. -/
def strip_short : String :=
  "Removes custom sections from an input WebAssembly file

Usage: wasm-tools strip [OPTIONS] [INPUT]

Arguments:
  [INPUT]  Input file to process

Options:
  -o, --output <OUTPUT>  Where to place output
  -v, --verbose...       Use verbose output (-v info, -vv debug, -vvv trace)
      --color <COLOR>    Configuration over whether terminal colors are used in output [default:
                         auto]
  -a, --all              Remove all custom sections, regardless of name
  -d, --delete <REGEX>   Remove custom sections matching the specified regex
  -t, --wat              Output the text format of WebAssembly instead of the binary format
  -h, --help             Print help (see more with '--help')

Examples:

Suppose foo.wasm has the following textual representation:

(module
  (type (;0;) (func))
  (func (;2;) (type 0)
    (local i32)
    global.get 0
  )
  (@custom \"linking\" (after code) \"\")
  (@custom \"reloc.CODE\" (after code) \"\")
  (@custom \"target_features\" (after code) \"\")
)

    # Remove all custom sections from foo.wasm and print the textual form of
    # the output to stdout.
    $ wasm-tools strip -a -t foo.wasm
(module
  (type (;0;) (func))
  (func (;0;) (type 0)
    (local i32)
    global.get 0
  )
)
    # Remove only the custom sections whose names match the regexp `linking`
    # and print the textual form of the output to stdout.
    $ wasm-tools strip -d linking foo.wasm -t
(module
  (type (;0;) (func))
  (func (;0;) (type 0)
    (local i32)
    global.get 0
  )
  (@custom \"reloc.CODE\" (after code) \"\")
  (@custom \"target_features\" (after code) \"\")
)

   # Remove all custom sections from foo.wasm and save the binary output to
   # the file out.wasm.
   $ wasm-tools strip -a foo.wasm -o out.wasm

Exit status:
    0 on success,
    nonzero if the input file fails to parse.
"

/-- `wasm-tools strip --help`. -/
def strip_long : String :=
  "Removes custom sections from an input WebAssembly file.

This command will by default strip all custom sections such as DWARF debugging information from a
wasm file. It will not strip the `name`, `component-type`, or `dylink.0` sections by default unless
the `--all` flag is passed.

Usage: wasm-tools strip [OPTIONS] [INPUT]

Arguments:
  [INPUT]
          Input file to process.
          
          If not provided or if this is `-` then stdin is read entirely and processed. Note that for
          most subcommands this input can either be a binary `*.wasm` file or a textual format
          `*.wat` file.

Options:
  -o, --output <OUTPUT>
          Where to place output.
          
          Required when printing WebAssembly binary output.
          
          If not provided, then stdout is used.

  -v, --verbose...
          Use verbose output (-v info, -vv debug, -vvv trace)

      --color <COLOR>
          Configuration over whether terminal colors are used in output.
          
          Supports one of `auto|never|always|always-ansi`. The default is to detect what to do based
          on the terminal environment, for example by using `isatty`.
          
          [default: auto]

  -a, --all
          Remove all custom sections, regardless of name

  -d, --delete <REGEX>
          Remove custom sections matching the specified regex

  -t, --wat
          Output the text format of WebAssembly instead of the binary format

  -h, --help
          Print help (see a summary with '-h')

Examples:

Suppose foo.wasm has the following textual representation:

(module
  (type (;0;) (func))
  (func (;2;) (type 0)
    (local i32)
    global.get 0
  )
  (@custom \"linking\" (after code) \"\")
  (@custom \"reloc.CODE\" (after code) \"\")
  (@custom \"target_features\" (after code) \"\")
)

    # Remove all custom sections from foo.wasm and print the textual form of
    # the output to stdout.
    $ wasm-tools strip -a -t foo.wasm
(module
  (type (;0;) (func))
  (func (;0;) (type 0)
    (local i32)
    global.get 0
  )
)
    # Remove only the custom sections whose names match the regexp `linking`
    # and print the textual form of the output to stdout.
    $ wasm-tools strip -d linking foo.wasm -t
(module
  (type (;0;) (func))
  (func (;0;) (type 0)
    (local i32)
    global.get 0
  )
  (@custom \"reloc.CODE\" (after code) \"\")
  (@custom \"target_features\" (after code) \"\")
)

   # Remove all custom sections from foo.wasm and save the binary output to
   # the file out.wasm.
   $ wasm-tools strip -a foo.wasm -o out.wasm

Exit status:
    0 on success,
    nonzero if the input file fails to parse.
"

/-- `wasm-tools objdump -h`. -/
def objdump_short : String :=
  "Dumps information about sections in a WebAssembly file

Usage: wasm-tools objdump [OPTIONS] [INPUT]

Arguments:
  [INPUT]  Input file to process

Options:
  -o, --output <OUTPUT>  Where to place output
  -v, --verbose...       Use verbose output (-v info, -vv debug, -vvv trace)
      --color <COLOR>    Configuration over whether terminal colors are used in output [default:
                         auto]
  -h, --help             Print help (see more with '--help')


Examples:

       # Dump the contents of the file `add.wasm`:
       $ wasm-tools objdump add.wasm
       types                                  |        0xa -       0x11 |         7 bytes | 1 count
       functions                              |       0x13 -       0x15 |         2 bytes | 1 count
       exports                                |       0x17 -       0x33 |        28 bytes | 1 count
       code                                   |       0x35 -       0x3e |         9 bytes | 1 count
       custom \"name\"                          |       0x45 -       0x5c |        23 bytes | 1 count

   One line is printed per section. The columns indicate:
       * The name of the section (for example, \"types\")
       * The offsets within the file for the start and end of the section (for example, \"0xa -
       0x11\")
       * The size of the section (for example, \"7 bytes\")
       * The number of items within the section (for example, \"1 count\")

       # Dump the contents of the file `add.wasm` and store the text-based output in a file
       # named `add.txt`:
       $ wasm-tools objdump add.wasm -o add.txt

Exit status:
    0 if OK,
    nonzero to indicate a parse error.
"

/-- `wasm-tools objdump --help`. -/
def objdump_long : String :=
  "Dumps information about sections in a WebAssembly file.

This is a relatively incomplete subcommand and is generally intended to just help poke around an
object file.

Usage: wasm-tools objdump [OPTIONS] [INPUT]

Arguments:
  [INPUT]
          Input file to process.
          
          If not provided or if this is `-` then stdin is read entirely and processed. Note that for
          most subcommands this input can either be a binary `*.wasm` file or a textual format
          `*.wat` file.

Options:
  -o, --output <OUTPUT>
          Where to place output.
          
          Required when printing WebAssembly binary output.
          
          If not provided, then stdout is used.

  -v, --verbose...
          Use verbose output (-v info, -vv debug, -vvv trace)

      --color <COLOR>
          Configuration over whether terminal colors are used in output.
          
          Supports one of `auto|never|always|always-ansi`. The default is to detect what to do based
          on the terminal environment, for example by using `isatty`.
          
          [default: auto]

  -h, --help
          Print help (see a summary with '-h')


Examples:

       # Dump the contents of the file `add.wasm`:
       $ wasm-tools objdump add.wasm
       types                                  |        0xa -       0x11 |         7 bytes | 1 count
       functions                              |       0x13 -       0x15 |         2 bytes | 1 count
       exports                                |       0x17 -       0x33 |        28 bytes | 1 count
       code                                   |       0x35 -       0x3e |         9 bytes | 1 count
       custom \"name\"                          |       0x45 -       0x5c |        23 bytes | 1 count

   One line is printed per section. The columns indicate:
       * The name of the section (for example, \"types\")
       * The offsets within the file for the start and end of the section (for example, \"0xa -
       0x11\")
       * The size of the section (for example, \"7 bytes\")
       * The number of items within the section (for example, \"1 count\")

       # Dump the contents of the file `add.wasm` and store the text-based output in a file
       # named `add.txt`:
       $ wasm-tools objdump add.wasm -o add.txt

Exit status:
    0 if OK,
    nonzero to indicate a parse error.
"

/-- `wasm-tools dump -h`. -/
def dump_short : String :=
  "Debugging utility to dump information about a wasm binary

Usage: wasm-tools dump [OPTIONS] [INPUT]

Arguments:
  [INPUT]  Input file to process

Options:
  -o, --output <OUTPUT>  Where to place output
  -v, --verbose...       Use verbose output (-v info, -vv debug, -vvv trace)
      --color <COLOR>    Configuration over whether terminal colors are used in output [default:
                         auto]
  -h, --help             Print help (see more with '--help')
"

/-- `wasm-tools dump --help`. -/
def dump_long : String :=
  "Debugging utility to dump information about a wasm binary.

This can be useful to figure out precisely how each byte of a wasm binary is classified or where
particular constructs are at particular offsets.

Usage: wasm-tools dump [OPTIONS] [INPUT]

Arguments:
  [INPUT]
          Input file to process.
          
          If not provided or if this is `-` then stdin is read entirely and processed. Note that for
          most subcommands this input can either be a binary `*.wasm` file or a textual format
          `*.wat` file.

Options:
  -o, --output <OUTPUT>
          Where to place output.
          
          Required when printing WebAssembly binary output.
          
          If not provided, then stdout is used.

  -v, --verbose...
          Use verbose output (-v info, -vv debug, -vvv trace)

      --color <COLOR>
          Configuration over whether terminal colors are used in output.
          
          Supports one of `auto|never|always|always-ansi`. The default is to detect what to do based
          on the terminal environment, for example by using `isatty`.
          
          [default: auto]

  -h, --help
          Print help (see a summary with '-h')
"

end WasmTools.HelpV
