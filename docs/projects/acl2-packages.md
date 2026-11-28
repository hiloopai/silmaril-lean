# ACL2 package resolution and nonrecursive source admission

This layer uses the home-package `Name` from [#4377](https://github.com/hiloopai/silmaril-lean/pull/4377).
In ACL2 8.7, a package's imports determine which foreign symbols its names
denote. For example, `ACL2::CAR` reads as `COMMON-LISP::CAR`. A user package
that imports an already imported symbol also sees the original home symbol.
ACL2's `defpkg` allows repeated references to the same import and rejects
distinct imports that share a symbol name. ACL2 supports no user export
operation. [DEFPKG](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____DEFPKG) ·
[Package admission source](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/other-events.lisp#L1375) ·
[Raw package imports](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L12761)

## APIs and scope

| API | Supported operations |
| --- | --- |
| [`PackageEnv`](../../Silmaril/Logic/ACL2/Packages/Defs.lean) | Admit evaluated lists of canonical imports using `defpkg`, select a known package, and resolve `SymbolRef` to `Name`. Equivalent redeclarations compare import sets and leave the snapshot unchanged. Rejected imports include unknown homes, aliases supplied as home names, conflicting symbol names and the reserved `ACL2-PKG-WITNESS`. |
| [`PackageReader`](../../Silmaril/ProofFormats/ACL2/Packages/Defs.lean) | Resolve the existing Common Lisp reader's symbol, keyword and qualified atoms. `readSetup` processes `in-package` and `defpkg` forms in order, resolving each form before applying it. Import syntax is literal `NIL` or a quoted proper list of symbols. `read` reads a single datum without executing it, preserves escaped symbol spelling and treats apostrophe as `COMMON-LISP::QUOTE`. Empty lists and the resolved `COMMON-LISP::NIL` have the same representation. |
| [`admitPackageBook`](../../Silmaril/ProofFormats/ACL2/Packages/Defs.lean) | Read a leading `in-package` in the ACL2 package, then a single bare `defun` in the selected user package. The logical caller supplies the prior `World`. The result carries the fresh `Name`, arity, typed body, and an `Event` whose extension updates the existing world. `PackageReader.admitDefinition` accepts a single bare `defun` with the current package already selected. |
| [`admitSource`](../../Silmaril/ProofFormats/ACL2/Defs.lean) | The existing ACL2-package source matcher still compares forms and include paths against a supplied checked book. Both paths use the same reader grammar and checked logical event types. |

The bootstrap table lists the supported `COMMON-LISP` symbols explicitly and
uses the same home identities for their imports into `ACL2`. It also covers
`ACL2::DEFPKG` and keyword syntax. Unknown bootstrap names fail closed.
Unqualified and double-colon names in a user package follow its import table
and otherwise denote a new home symbol in that package. Single-colon names
require an external symbol: the listed Common Lisp exports work, and ACL2/user
package names fail that check. `KEYWORD:NAME` depends on prior interning and is
unsupported. The profile excludes host package nicknames. Package selector
strings are matched exactly. [Bootstrap imports](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/acl2.lisp#L1201) ·
[IN-PACKAGE](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____IN-PACKAGE) ·
[Book header check](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/other-events.lisp#L10578) ·
[Common Lisp token and package syntax](https://www.lispworks.com/documentation/HyperSpec/Body/02_ce.htm)

The source profile uses ASCII symbols and strings, lists and dotted pairs.
The term subset is formals, `T` and `NIL` (including quoted forms),
`CONS`, `CAR`, `CDR`, `CONSP`, `EQUAL`, `IF`, and arity-checked calls from
the prior signature. Primitive dispatch and variable lookup use home
identities. The fresh definition name must belong to the active user
package, and definition and formal names are restricted to letter-led names
with letters, digits and hyphens. ACL2 mode, guard, package availability in
the host, and checks around ACL2's generated package event names are outside
this Lean adapter. It admits a typed fragment event, with native admission
checked independently for the fixture. No object carrier is needed for this
name and term check.

## Regression and native replay

The [fixtures](../../tests/acl2/packages/) define `SILMARIL-C2-HOME::|takeFirst|`
and import it into `SILMARIL-C2-USE`. The consumer book calls the imported
symbol unqualified. Lean checks the resulting call's arity, canonical name
and formal binding and composes the two checked events. It also rejects a
same-spelled symbol from `SILMARIL-C2-OTHER` and a call with two arguments.
The native replay certifies the same books source-only, then includes the
consumer in a fresh ACL2 process and checks the two translated
`unnormalized-body` properties, symbol identities and evaluation on
`(cons t nil)`. ACL2's translator rejects the two invalid calls in a separate
process. [Pinned fixture inputs](../../tests/acl2/packages/SHA256SUMS) ·
[Native observations](../../tests/acl2/packages/observe.lsp)

```sh
make acl2-package-source-check
make check CHECK_TARGETS='+Silmaril.ProofFormats.ACL2.Packages.Defs +Silmaril.ProofFormats.ACL2.Defs +Silmaril.Logic.ACL2.Books.Examples'

work=$(mktemp -d)
git clone --depth 1 --branch 8.7 https://github.com/acl2/acl2.git "$work/acl2"
test "$(git -C "$work/acl2" rev-parse HEAD)" = bc6f4f49e81a0711214a8d91f0d06e0e084d2204
make -C "$work/acl2" LISP=sbcl
tests/acl2/packages/check-native.sh "$work/acl2" "$work/results"
```

The recorded host was SBCL 2.5.2 and ACL2 8.7 at the commit above, Git tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`. The source-only run emits guard
and compiled-file warnings. Certificate bytes and logs can depend on the
host and paths. Native certification and the differential sample are
observations of this fixture.

## Open reader and package rules for x86isa

- Import expressions need ordered evaluation or a pinned native export.
  X86ISA's portcullis includes other books and builds its import set with
  `union-eq`, `*acl2-exports*`, `*common-lisp-symbols-from-main-lisp-package*`,
  and package-specific export constants. Those constants supply imports,
  while single-colon visibility is a separate reader operation.
  [X86ISA portcullis](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/portcullis/package.lsp)
- Replay needs package and book snapshots for local and hidden events,
  reincarnation, and certification portcullises. The monotone table here
  handles visible package introductions and redundant imports only.
  [Hidden packages](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____HIDDEN-DEFPKG)
- The ACL2 reader's `#.` constants, `#ux` and other dispatch literals,
  feature tests, backquote/comma expansion, and object literals still need
  versioned treatment. Macro expansion, translated lambdas, `make-event`,
  and recursion have their own inputs and checking obligations.
  [ACL2 readtable](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/acl2.lisp#L2026) ·
  [x86isa closure inventory](acl2-x86isa.md)
