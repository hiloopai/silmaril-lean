# Metamath data

These two databases are evidence for the Lean data correspondence tests.
They are not papers and introduce no Lean axioms.

| File | Origin | License | SHA-256 |
| --- | --- | --- | --- |
| `set-axioms.mm` | Axiom and syntax fragment extracted from [metamath/set.mm](https://github.com/metamath/set.mm/blob/0bbe48280664bc0d584bb2c4b4ed90dfe4f07b7b/set.mm), commit `0bbe48280664bc0d584bb2c4b4ed90dfe4f07b7b` | CC0-1.0 | `3eb214c1f099f11bf1b8fe51c97c9c73a2b18fa175c4cff47ba25de6a8e05968` |
| `z2.mm` | Second-order arithmetic database written for this formalization | CC0-1.0 | `120b727d802667a078fdeba59f95ffb62634835d5c3f42420bdea90e2971df2c` |

The files retain their source comments and public-domain dedication. Generator
paths in the source headers record provenance; those extraction scripts are
not needed to build or check this release.
[CC0-1.0](https://creativecommons.org/publicdomain/zero/1.0/legalcode)
is a waiver of copyright and related rights, with a fallback license.

From the repository root:

```sh
lake build Silmaril.Logic.Metamath.SetMM.Regression \
  Silmaril.Logic.Metamath.SecondOrder.Tests
```

The checks parse and verify the committed files, then compare labels,
assertion kinds, disjoint-variable pairs, hypotheses and conclusions with
the Lean data. `set-axioms.mm` contains more fragments than the ZFC fragment
checked here. The second-order check compares every database entry in order.

These are executable regression tests at elaboration time. Their success is
not a Lean proof that the full text checker accepted these particular files.
`Silmaril.Logic.Metamath.Verify.Kernel` separately proves acceptance of a
small proof-machine example by kernel reduction.

The public release does not distribute `peano.mm`. The Peano modules contain
Lean mathematical syntax and axiom statements, with their source labels.
