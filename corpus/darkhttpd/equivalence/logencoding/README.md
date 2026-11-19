# darkhttpd byte-predicate O0/Og problem

`Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence.Task.optimization` is an
**UNPROVED** contextual binary-equivalence problem over the existing ordinary-Git
1.17/default/x86_64 images. No software-under-test source or ELF was rebuilt.

| Endpoint | Symbol | Address | Size | Private stack |
| --- | --- | --- | --- | --- |
| O0 | `needs_logencoding` | `0x503e` | 41 bytes | 12 bytes |
| Og | `needs_logencoding` | `0x2816` | 21 bytes | 0 bytes |

The manifest binds exact whole-file and function hashes, executable PT_LOAD
spans, unchanged upstream source span, GCC flags, configuration, image identity
and actual build receipts. Kernel CodeAt and symbol facts establish byte identity,
not equivalence. This does not change the structural-decomposition census.

Every unsigned byte is admitted. Caller registers/flags/memory and upper56 RDI
bits are arbitrary and common between sides. DIL carries the low8 argument;
EAX carries the low32 result. Both excerpts inhabit one common caller memory.
Joint entry existence for every input, both first returns, actual EAX equality,
callee-saved ABI, memory preservation outside exact12/0 frames and complete
mapping preservation are obligations. Entry assumes no expected return, safety,
termination or source refinement. There are no globals, callees, heap or I/O
operations. O0 branches and spills; Og uses real LEA/byte comparisons/SETA/SETE/OR/
MOVZX. O2/O3 omit the standalone symbol and are not given an invented function.

The existing O0 C/Core/ELF problem remains separate. The exact included upstream
source is provenance here; this binary problem does not claim Og C refinement,
historical preprocessing/build adequacy, whole-ELF loading, full HTTP-server
correctness, universal nondeterministic termination or hardware refinement.
Whole-corpus semantic coverage is unfinished; no corpus semantic proof exists.

Reproduce from this checkout:

```sh
hiloop prove build Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence.Thms
hiloop prove run --build Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence.Thms -- \
  lake env lean -DwarningAsError=true --run tests/cerberus/DarkhttpdLogEncodingEquivalence.lean
python3 -I tools/corpus/check_darkhttpd_logencoding_equivalence_native.py
python3 -m unittest discover -s scripts/corpus -p 'test_*equivalence*.py'
```

With the pinned Lean/dependencies installed, the equivalent local commands are
`lake build --wfail` for that root and the shown `lake env lean` invocation.
`make check` includes both new execution checks.

The saved machine observations cover all256 bytes with four upper-register,
flag and stack patterns (1024 pairs), preserving actual callee-saved registers,
RSP, unrelated bytes and mapping metadata. The native check covers1024 pairs
with upper RDI/RSI/RDX patterns. Because these are PIE executables with static
symbols, the native check copies only the exact call-free, position-independent
function bytes into anonymous RX mappings. It does not dlopen or fully load the
ELFs, nor claim to validate arbitrary native ABI/memory effects. Finite model and
native observations are not semantic proofs. The measured registry build is a
warm remote build and may reuse compiled outputs; its timing is client wall time,
not fresh compilation time or CI-budget evidence.

The viewer exposes exact source/ELF/build/context identities and rejects altered
context text. All existing FIPS, configuration, jemalloc, cJSON and security
limits remain in force; this tranche changes no CI timing/security policy.
