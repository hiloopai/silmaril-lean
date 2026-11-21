# Checked named-logic sidecar

The Lean exporter reads the existing HOL Light and extensional MLTT fixture
terms and calls their grammar encoders. Its judgment and step entries reference
checked declarations in `Database.Examples.Thms`. This is not extraction of a
kernel proof object or a checker for arbitrary proof certificates. The row and
step labels are display metadata, not an expanded Lean proof tree. The logical
name relations in Lean remain abstract.

From the repository root, with the pinned Lean, Python 3.10+, and `b3sum` on a
controlled `PATH` (tested with 1.8.3):

```sh
bash tools/verification-projects/named-logic/check.sh <example-commit> /tmp/named-logic
python3 -BEs tools/verification-projects/named-logic/manifest.py verify \
  /tmp/named-logic/named-logic-plan.json /tmp/named-logic/named-logic.json
```

Pass the public full revision of the example source (an ancestor is acceptable
if the checked syntax and proofs are unchanged). The plan and sidecar are
deterministic for a fixed revision. The external script renders the inline
text/list fragment of DRISL; it rejects tags, including links. It recomputes
the two object CID envelopes/digests, strictly decodes the original bytes, and
validates all row references and their decoded syntax against the checked
export plan. The verifier is not a general BDASL validator, proof replay tool,
or verifier of the authenticity of a Git commit. Its dependencies are the
exact exporter output, Python, and `b3sum`. It uses no Lean hashing and does
not put digest verification into kernel evidence.

## Explorer input

`named-logic.json` has format `silmaril.named-logic.v1`, pinned `source`
(`repo`, `revision`), `profiles`, `blocks`, and ordered `rows`. Each profile
identifies layout, atom codec, inline placement, wire, codec, and multihash.
Blocks are indexed by profile and canonical CID text, and have `hex` and
`decoded`. Row `roots` (by role) and `assumptions` refer to `{profile, cid,
alternates}`; `alternates` maps another profile to its CID. Inhabitation has no
term coordinate. Each row has `scope` and `evidence` with a declaration,
source path, and ordered declared steps. A step has an `id`, `rule`,
`judgment`, `declaration`, and prior step IDs in `premises`. The two
presentations name the same inline syntax with separate external algorithms;
they are not the boxed-atom profile or a maximally linked graph.
