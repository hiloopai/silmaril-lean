module

public import Silmaril.Wasi.Versions.WitImport.KCert.Io2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Io29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Cli29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Fs29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Rand29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Sock29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Http29.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Tokens.V2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Tokens.V3.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Tokens.V29.Thms

@[expose] public section

/-!
# Kernel-checked WIT imports (without doc comments)

For every signature table, drop list and resolved package that the WIT importer quotes
(`wit_table%`, `wit_drops%`, `wit_iface_table%`, `wit_rpkg%`) for WASI 0.2.12, 0.3.2 and
0.2.9, a theorem that the importer evaluated **in the kernel** (`kTable`, `kDrops`, `kRPkg`:
the verified parser through the fuelled lexer, `mergeDocs`, `Elab.elaborate`, `table`, `drops`,
`rtable`, `envOf`) on the same files gives it:

| package | certificate | theorems |
|---|---|---|
| `wasi:io@0.2.12` | `KC.io2` | `io2T_kernel_nodoc`, `io2D_kernel_nodoc`, `io2P_kernel_nodoc` |
| `wasi:clocks@0.2.12` | `KC.clocks2` | `clocks2T_kernel_nodoc`, `clocks2P_kernel_nodoc` |
| `wasi:cli@0.2.12` | `KC.cli2` | `cli2T_kernel_nodoc`, `cli2P_kernel_nodoc` |
| `wasi:filesystem@0.2.12` | `KC.fs2` | `fs2T_kernel_nodoc`, `fs2D_kernel_nodoc`, `fs2P_kernel_nodoc` |
| `wasi:sockets@0.2.12` | `KC.sock2` | `sock2T_kernel_nodoc`, `sock2P_kernel_nodoc` |
| `wasi:http@0.2.12` | `KC.http2` | `http2T_kernel_nodoc`, `http2P_kernel_nodoc` |
| `wasi:random@0.2.12` | `KC.rand2` | `rand2T_kernel_nodoc`, `rand2P_kernel_nodoc` |
| `wasi:random@0.3.2` | `KC.rand3` | `rand3T_kernel_nodoc`, `rand3P_kernel_nodoc` |
| `wasi:clocks@0.3.2` | `KC.clocks3` | `clocks3T_kernel_nodoc`, `clocks3P_kernel_nodoc` |
| `wasi:cli@0.3.2` | `KC.cli3` | `cli3T_kernel_nodoc`, `cli3P_kernel_nodoc` |
| `wasi:filesystem@0.3.2` | `KC.fs3` | `fs3T_kernel_nodoc`, `fs3D_kernel_nodoc`, `fs3P_kernel_nodoc` |
| `wasi:sockets@0.3.2` | `KC.sock3` | `sock3T_kernel_nodoc`, `sock3P_kernel_nodoc` |
| `wasi:http@0.3.2` | `KC.http3` | `http3T_kernel_nodoc`, `http3P_kernel_nodoc` |
| `wasi:io@0.2.9` | `KC.io29` | `io29P_kernel_nodoc` |
| `wasi:clocks@0.2.9` | `KC.clocks29` | `clocks29P_kernel_nodoc` |
| `wasi:cli@0.2.9` | `KC.cli29` | `cli29P_kernel_nodoc` |
| `wasi:filesystem@0.2.9` | `KC.fs29` | `fs29P_kernel_nodoc` |
| `wasi:random@0.2.9` | `KC.rand29` | `rand29P_kernel_nodoc` |
| `wasi:sockets@0.2.9` | `KC.sock29` | `sock29P_kernel_nodoc` |
| `wasi:http@0.2.9` | `KC.http29` | `http29P_kernel_nodoc` |

**On the vendored files' tokens** (`KCert/Tokens/*`): `<x>_kernel_tokens : kTableTok … = some <x>`
(and `kDropsTok`, `kRPkgTok`), the same importer on the glued texts with their doc comments
(`wit_src%`), whose doc-comment tokens are dropped after lexing (`parseTokK`,
`Silmaril.Wasi.Versions.WitImport.KTokens`). They follow from the `<x>_kernel_nodoc` theorems and,
per file, `KF.….parseNd` (`KCert/Lex/*`, `wit_klex`): the demoted text lexes to the full
text's tokens without doc comments, checked by the kernel, so `demoteDocs` is not trusted.

The certificates read the files without doc comments (`wit_srcnd%`, `Silmaril.Wasi.Versions.WitImport.KSrcNd`):
doc comments only fill `docs` fields, which no table and no resolved package contains, and
the kernel evaluates their text through UTF-8 decoding in time quadratic in the line length.
With the docs, `rand2T`, `rand3T`, `cli3T` and `clocks3T` are kernel-checked by
`Silmaril.Wasi.Versions.WitImport.KTables`.

Each evaluation is split into steps checked in separate modules (`wit_kfile`, `wit_kcert`,
`Silmaril.Wasi.Versions.WitImport.KQuote`; the composition theorems are
`Silmaril.Wasi.Versions.WitImport.KSplit`): one parse per file (`KCert/Files/*`), then per
package the gated universe and validity check with one `Elab.elabBody` equation per interface
(`KCert/<package>/Univ`), and the environment, worlds, package and binary checks
(`KCert/<package>`).

**With the doc comments parsed** (`KCert/Docs/*`): `<x>_kernel : kTable … = some <x>` (and
`kDrops`, `kRPkg`), the importer on the glued texts with their doc comments, every token parsed.
They follow from the `<x>_kernel_nodoc` theorems, the per-file kernel checks `KF.….parseEr`
(`KCert/Erase/*`, `KCert/EraseLex/*`: the parse with doc comments, erased, is the parse without
them) and the theorem that doc comments cannot change a table, a drop list or a resolved package
(`kTable_of_erase`, `kDrops_of_erase`, `kRPkg_of_erase`, `Silmaril.Wasi.Versions.WitImport.KErase`).
The `_kernel_tokens` theorems are kept as the earlier variant.

Still trusted: the text glue inside `wit_src%` (`withHeader`, `demoteParamDocs`), which runs in
the evaluator, and the elaborator reading the files.

A Silmaril addition.
-/
