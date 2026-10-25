# Raw

Agent-generated proofs that are valid but not yet refined. Mirrors the header tree.

- **Not an API:** only the same topic's `Proofs` and `Thms` modules may import
  these, and they may change or disappear at any time.
- Refinement moves proofs from here to `Proofs/`. The raw version is deleted, or
  kept as a reference when it is still useful.
- Exploratory work stays outside this repository. Raw proofs land here only
  when they back a header in this repository.
