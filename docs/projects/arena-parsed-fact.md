# Parsed residency and checked CAS admission

Import `Silmaril.Semantics.Arena.Traits.Parsed.Thms`. The default is the
existing `Traits.CasArena`: its slot lane holds native parsed values, and its
authoritative CAS lane holds bytes. `Trusted` states precisely what a backend
is trusted to implement: refinement to the authoritative snapshot, plus
profile validity on the states it exposes as ready. It does not grant Lean
trust in arbitrary I/O. `trusted_model` is the functional instance. The
existing step laws preserve validity on successful plain edits, raw puts and
verified attachments when it holds initially.

`insert_model` requires a vacant key, not an encoder result or a name. It
reads the exact object back, leaves it unnamed, and does not touch the byte
snapshot. The DASL fixture inserts an existing Prolly leaf and branch with a
local handle and reads both back, using a profile with no encoder or name
coverage. This is parsed residency, not a claim about tree invariants or
publishing a Prolly root. Reservations, holes, native residents and published
bytes have separate observations.

## Optional gate

- `Fact` is proposition-indexed by the exact source observation, selected
  profile, name and bytes. The verifier compares the source's exact bytes
  and recomputes the profile's abstract name choice. A digest alone cannot
  construct a witness. The Rust byte-claim abstraction packages immutable
  bytes and a checked claim; a CID digest check by itself says nothing about
  codec validity or which source returned the bytes. The Lean witness adds
  the source observation and checks the full selected name. It does not
  authenticate the source; claiming agreement with an external reference
  requires `Source.Agrees` separately.
- `AttachmentFact` also pins the exact resident object's encoding at the
  transaction's input state and key. No decidable equality on parsed values
  or injectivity is required. If users need decoding/semantic recovery, that
  is a codec law outside the raw byte fact. A raw put does not check object
  syntax. Named typed admission uses the profile's encoder, whose claimed
  canonicality has to be established for the chosen format separately.
- The optional `put` and `attach` verify before calling the same trusted
  operations. On validated facts they return the same result and successor,
  apart from embedding errors in the gate's error type. A valid upstream
  fact does not authorize overwriting different bytes in the target. On
  success the exact bytes are in the target's authoritative snapshot. On any
  error the pure commit keeps the original state; a real synchronous backend
  must make the commit atomic and keep the source/profile/input stable for
  validation. This reference gate may repeat encoder/selector work and does
  not yet establish a skip-verification fast path.
- `CasArena.probe` is a view of a trusted authoritative `get`, with
  `probe_agrees` justifying `absent` in the observed snapshot. A failed read
  maps to `unavailable`; it is neither absence nor evidence of malformed
  bytes. `verify` also distinguishes source absence, unequal bytes, an
  unavailable selector and a wrong selected name. None becomes a permanent
  negative cache entry here. A local vacant or unresident key is not a CAS
  read result. The verification stage has no writes.

## Initial backend and next contracts

Start with ordinary parsed slots plus a separate authoritative byte table.
Use a profiled encoder only at explicit name derivation/publication; the
selector is already available through `CasArena.profile.select?`. Exercise
fresh, hole, reservation, replacement, collision and source-unavailable
traces before adding interning or cache reuse. Count serialization, name
selection and byte comparisons separately so later optimizations can be
tested against identical observations. Do not turn a cache miss into an
authoritative `None` or use a parsed object as evidence for existing bytes.

This slice adds probe and gated raw put/attachment. It does not add named
reservation to the trait, atomic insert-and-publish for a new typed object,
eviction, authoritative deletion, or handle-lifetime rules. Follow-on
contracts should check separate typed spaces against a tagged space, reuse
the rooted Prolly and Git/FS APIs for consumers, and then refine a layered
backend with rooted retention and stale-handle protection. Owned vs scoped
reads and Rust/Python/JS synchronous error mappings follow that boundary.

```sh
lake build --wfail +Silmaril.Semantics.Arena.Traits.Parsed.Examples +Silmaril.Formats.Dasl.Arena.Prolly.Parsed.Examples
make check CHECK_TARGETS='+Silmaril.Semantics.Arena.Traits.Parsed.Examples +Silmaril.Formats.Dasl.Arena.Prolly.Parsed.Examples'
```
