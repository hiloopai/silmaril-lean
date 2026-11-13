# Genuine Cerberus oracle fixtures

Output of the upstream Cerberus C semantics at
[`rems-project/cerberus@b3e11ea334e95359907d4abf9194f0e7fedc6c6a`](https://github.com/rems-project/cerberus/tree/b3e11ea334e95359907d4abf9194f0e7fedc6c6a)
on 18 small C programs, used as oracles by the replay tests of the
[Cerberus port](../../../docs/projects/cerberus.md). Cerberus is BSD 2-Clause (with exceptions);
see [`NOTICES/Cerberus`](../../../NOTICES/Cerberus/README.md).

Each directory is one program:

| File | What |
| --- | --- |
| `input.c` | the C source |
| `core.sexp.gz` | the complete Core file Cerberus elaborates it to, in the tagged S-expression wire format, with its runtime maps |
| `core.pp.txt`, `oracle.core.pp.txt` | Cerberus's own Core listings (from the exporter and from the `cerberus` CLI) |
| `oracle.json` | the CLI's execution observation (for example `Defined`, `Specified(42)`) |
| `tail.sexp.gz` | the typed Ail before elaboration, with its fresh symbols |
| `fresh-context.json` | the fresh-symbol counter and digest at each pipeline boundary |
| `fields/` | each field of the Core file separately |

`shared/runtime/` holds the runtime maps shared by every document (`stdlib.sexp`, `impl.sexp`)
and the string-to-symbol map of the Core standard library (`ailnames.sexp`).

## How they were produced

- **Configuration:** a Core exporter linked against that Cerberus revision. It runs the concrete memory model, `PNVI_ae_udi`, the normal calling convention, no libc, and no Core typechecking, rewriting or sequentialization passes. The Core runtime is `gcc_4.9.0_x86_64-apple-darwin10.8.0`.
- **`tail.sexp.gz` and `fresh-context.json`:** these come from a separately built copy of the same exporter, instrumented to serialize the typed Ail before translation. Its complete Core output equals the unmodified export byte for byte on every fixture.
- **Path normalization (the only change):** the captured documents named the build machine's installation prefix in their runtime-library locations. In every file, compressed or not, that prefix is replaced by `/root/.opam/default`, the default opam prefix. The Core semantics of the port treats locations under that prefix as library locations (`Silmaril.Cerberus.Core.TypePrint.libraryLocation`). The `.gz` files were recompressed with `gzip -n -9`. No other byte changes.
- **Replays:** all four replay tests below give the same verdicts on the normalized and on the original documents.

## The replay tests

```sh
lake build ci_cerberus_genuine_oracle ci_cerberus_elaboration_oracle \
  ci_cerberus_integer_cast ci_cerberus_parameter_call
O=benchmarks/cerberus-elaboration/oracle
.lake/build/bin/ci_cerberus_genuine_oracle $O        # every Core document runs, through the Core LTS, to the CLI's observation
.lake/build/bin/ci_cerberus_elaboration_oracle $O    # the Lean elaborator on each typed Ail gives the genuine Core file, byte for byte
.lake/build/bin/ci_cerberus_integer_cast $O          # the captured loaded-integer runtime conversions
.lake/build/bin/ci_cerberus_parameter_call $O/call-id/core.sexp.gz
```

`make cerberus-oracle` runs all four. Exact agreement on these fixtures is evidence about the
port on these programs, not a general correctness theorem.
