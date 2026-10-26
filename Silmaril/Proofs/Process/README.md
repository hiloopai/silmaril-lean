# Process proof ownership

Process-level proof roots are published through the topic headers under
`Silmaril/Process/**`.  The detailed LPS proofs are currently retained in
their pinned upstream namespaces so existing imports and generated declarations
remain stable.  New proof-only additions belong under this directory and must
be re-exported by a topic `Thms.lean` header.
