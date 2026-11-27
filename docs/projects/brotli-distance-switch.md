# Bounded Brotli distance switching within a command

`Execute.DistanceSwitch.read` is an opt-in command executor for an already
checked compressed meta-block header. It threads independent L, I and D run
state and the output and recent-distance ring. It shares command preflight,
literal insertion and the overlap-copy executor with the earlier profiles.

A pending explicit distance selects and debits the D run before reading the
value. The selected row is `4 * activeDistanceType + min (copyLength - 2) 3`
in the checked distance context map. The selected tree supplies the code and
RFC 7932 §4 determines the extra width and distance value. An implicit zero
distance bypasses D selection and preserves the recent-distance ring. An
insertion that reaches MLEN finishes before any distance operation.

Only bounded backward references reach the copy executor. Static dictionary
addresses return the typed distance, base length and word ID. The decoder
checks total output and MLEN before appending matched bytes. The existing
single-distance command and stream profiles retain their admission guards.
This PR adds a command entry point. Payload and whole-stream dispatch and
Parquet activation are separate.

## Checked laws

The command theorem names are in
`Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch`.

- `read_sound` proves ordered original bits and exact suffix and cursor under
  the shared bit cap. Its wire witness orders I selection, command, switched
  literals, D selection, distance code and extra bits, and the bytewise copy.
  It gives positive output progress without exceeding MLEN or the caller cap.
- `Wire.output_count` proves the exact regenerated command extent.
  `SelectionWire.other_runs` preserves L and I during D selection.
  `Wire.no_distance_symbol` preserves the D run and recent-distance ring
  for implicit distance and a literal-only ending.
- `read_error` and `Failure.offset` witness the earlier successful operations
  and the exact source prefix up to the first failure's operation. A control
  failure identifies its type-symbol or length field. A distance-value error
  points to the start of its code, including when its extra bits fail. Copy
  guards and dictionary rejection point immediately after distance resolution.
  No partial successor is returned on failure.

## Independent replay

The fixture is an independently assembled RFC 7932 stream, with one literal
and command type and two distance types. Pinned libbrotli v1.2.0
(`028fb5a23661f123017c060daa546b55cf4bde29`) decodes the entire specimen.
The trace compares all five commands, two D switches, selected contexts and
trees, code and extra values, cursor boundaries, run counts, resolved
distances, output and ring. An exhausted D run survives an implicit copy and
the terminal insertion. The prior stream decoders still reject the D header.

The controls cover caps at the D type, count, symbol and extra fields, a
post-resolution output cap, and truncation. A separately labeled,
native-produced stream exercises typed static dictionary rejection.

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Tests +Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Tests +Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Tests
python3 -B -I -u scripts/brotli-distance-switch/check.py
```

The replay accepts `--brotli-source` for an existing exact checkout.
[RFC 7932](https://www.rfc-editor.org/rfc/rfc7932)
· [libbrotli pin](https://github.com/google/brotli/tree/028fb5a23661f123017c060daa546b55cf4bde29)
