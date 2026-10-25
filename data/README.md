# Data

Small "world data" used by the formalization (for example physical constants).

- **Layout:** `data/<domain>/<name>.v<N>.json`, plus CSV where tabular.
  Checked-in dumps are the source of truth for Lean generation. SQLite and Parquet
  are build outputs and are not committed.
- **Sources:** each dataset has a manifest entry with the source URL, licence,
  retrieval date, the SHA-256 of the raw bytes, and BLAKE3 links. Raw source files
  are committed only when their licence allows redistribution.
- **Pipeline:** raw → JSON → SQLite → generated Lean, in Rust on covalence. There
  are no new Python generators.
