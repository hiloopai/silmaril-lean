# c-tv: compiler-explorer correspondences as Lean goals

`c-tv gen` compiles a C file with a pinned compiler, reads what a compiler explorer shows (the
DWARF line table: source line ↔ address ranges) and the frame slots of its objects, and writes a
Lean module whose goals relate the C code, its Cerberus Core and the x86-64 bytes. Rust; the
instruction decoder is `lift-x86` from [`../x86-lift`](../x86-lift/README.md) (a path
dependency).

```text
c-tv gen --src FILE.c --name NAME [--opt O0]… [--flags "…"] [--image IMAGE]
         [--core-probe CMD | --core FILE] [--root DIR] [--base ADDR]
```

* `--opt` (repeatable; default `O0` and `O2`): one build per level,
  `gcc -OPT -g -c -fdebug-prefix-map=/src=. FLAGS`.
* `--flags`: the other flags (default: freestanding, no stack protector or CET, general
  registers only, non-PIC, no unwind tables, no ident).
* `--image`: the container the compiler runs in (default
  `gcc:13.3.0@sha256:1d71f0f3450214bef38fe09e6f610fb6cca90cf97b43f4ce845bfc32a4168818`). Docker
  runs with `--network host` and the caller's uid, with the example's directory mounted at
  `/src`, the compiler's working directory.
* `--core-probe CMD`: how to run the Lean probe (`Silmaril.Project.CompilesTo.Probe.docText`)
  on a temporary module, `Silmaril/Project/CompilesTo/ProbeRun/CNAME.lean`, that c-tv writes
  under `--root` and removes afterwards. `CMD` runs in `--root`, with `{module}` and `{file}`
  (relative to `--root`) substituted: `lake env lean {file}`. Only the probe's part of the
  output is kept.
* `--core FILE`: reuse a saved probe output (`examples/compiles-to/NAME/core-probe.txt`).
* `--root`: where the outputs go (default `.`).
* `--base`: where `.text` is placed in the goals (default `0x401000`).

Builds are path-neutral. With `-fdebug-prefix-map=/src=.` the objects' DWARF holds `.` as the
compilation directory and the source's file name (`NAME.c`), never a host path. The receipts
and reports record paths relative to the example's directory (`OPT/NAME.o`, `NAME.c`) or to
`--root` (`examples/compiles-to/NAME/…`). The only absolute paths they hold are the container's:
`/src` (the receipt's `workdir` and the prefix map) and the image's `cc1` and `as`
(`tools_sha256`).

Outputs, all under `--root` (`CNAME` is `NAME` in CamelCase; the Lean modules belong to the
library `CompilesToExamples` of `lakefile.toml`, source directory `examples/compiles-to`, and
`docs/projects/compiles-to.md` explains their statements):

| path | what |
|---|---|
| `examples/compiles-to/NAME/NAME.c` | the source (copied) |
| `examples/compiles-to/NAME/OPT/NAME.o`, `OPT/RECEIPT.json` | the object (committed: gcc output for the example's own source, a few KB) and its receipt: image digest, working directory, command, `gcc`/`as` versions, `cc1`/`as` SHA-256, object and source SHA-256 |
| `examples/compiles-to/NAME/correspondence.{md,json}` | the compiler-explorer view: per function, each line's address range and instructions, the Lean point or the reason it is unsupported |
| `examples/compiles-to/NAME/core-probe.txt` | the probe output: typed Ail and Core document (for `--core`) |
| `examples/compiles-to/CompilesToExamples/CNAME/Defs.lean` | the header: the C text, its quoted typed Ail (`#guard`-checked against the frontend) and Core; per function its Core (`CFn`) and the goals `Task.elaborates_F`, `Task.F_safe`, `Task.F_canonical_safe`, `Task.F_builds`; per build and function the bytes (`SysV.objectCodeN`, by the kernel), the listing (`decodesAs`), the `FnData`, the point locators (`PointOf`, proved), the build, and the goals `Task.F_seg_K`, `Task.F_seg_K_from_c`, `Task.F_compiles_to`, `Task.F_canonical` |
| `examples/compiles-to/CompilesToExamples/CNAME/Proofs/*.lean` | the generated proofs (`Elaborates`, the `-O0` return-label segments); proof modules written next to them by hand or by a prover are kept and collected |
| `examples/compiles-to/CompilesToExamples/CNAME/Thms.lean` | imports every proof module that proves a goal and lists the goals each proves |
| `silmaril/compiles-to/NAME.toml`, `examples/compiles-to/CompilesToExamples/CNAME/Rows.lean` | the rows: the source and objects as values, per function `c.elaborates_to` and `c.compiles_to.builds`, per build `elf.object_fn`, a `c.compiles_to.segment` row per point, `c.compiles_to` and `c.compiles_to.canonical_entry` (`expect = "THM"` where a proof module proves the `Task`, else `"OPN"`), and the group of the file; the module loads them and solves the proved rows |
| `silmaril/compiles-to.toml`, `examples/compiles-to/CompilesToExamples.lean` | the group `silmaril.compiles_to.all` over every file with rows (a child of the root group in `silmaril/selftest.toml`) and the module that loads them all |

What the tool decides, and what Lean checks:

* **Granularity.** `statement` only for gcc `-O0`-shaped leaves (frame-pointer prologue, one
  address range per line, `pop %rbp; ret` epilogue, objects in `DW_OP_fbreg` slots of 4 bytes
  inside the red zone, one Core statement per line, one return label); else `function`. Every
  line range that is not a point is reported with the first reason (`correspondence.md`).
* **No goals** for a function the Lean decoder cannot read (an instruction outside `X86.Ext`),
  whose code a relocation patches (calls, globals), with a non-integer signature, or whose C the
  elaborator rejects; the reason is recorded.
* Lean re-checks the bytes, the decoder, and each point's Core fragment; the goals themselves
  are open (`def Task.… : Prop`) until proved.
* A probe module and the C file's quoted Core are data: `Task.elaborates_F` states that the
  elaborator's output is the quoted Core, and its proof (`cbv`) is checked by the kernel.

`regen.sh` regenerates the examples under `examples/compiles-to/` (`straight`, `branch`, `loop`)
from their saved probe outputs, or with `--probe` by running the probe (`lake env lean {file}`).
The rows read the sources and objects through the artifact registry `silmaril/artifacts.toml`;
register a new one with `scripts/sil project artifacts add PATH --name NAME` (built by
`make project-tool`).

Build and test (Rust 1.98 or later; `gen` needs Docker with the pinned image):

```sh
cd tools/c-tv
cargo build --release --locked
cargo test --locked
cargo clippy --locked --all-targets -- -D warnings
```
