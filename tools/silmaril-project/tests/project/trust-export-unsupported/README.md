# trust-export-unsupported: real producer output, refused as missing metadata

`trust.json` is a real, unchanged `silmaril.trust-core.v1` export from core #125 at `cbcd896c`
(`#trust_export` over the bytes example modules).

That export is an **optional** input of the project database, and it is unsupported until it is
complete. The root policy names the set `standard`, which comes from the policy file itself, and
the export does not carry it. The converter refuses the document as **missing metadata**. It
does not read the set from anywhere else and does not assume its contents.

The primary input is the trust lines that `sil project trust-dump` writes; see `trust-core-bytes`.
