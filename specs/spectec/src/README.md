# Vendored SpecTec sources

Exact upstream bytes from `WebAssembly/spec` at revision
`608711107b7f1edb13efd57b7d79b49477462d36`, kept under their upstream paths:

* `specification/wasm-{1.0,2.0,3.0}/*.spectec`: the 57 source files listed in
  `../manifest.json` (10 + 10 + 37), from which the vendored `--ast` streams
  were elaborated;
* `spectec/src/frontend/{lexer.mll,parser.mly,elab.ml}`: the SpecTec frontend's
  lexer, parser and elaborator, kept as references for the Lean transcription
  in `Silmaril/Wasm/SpecTec/Surface/` (line numbers cited there refer to these
  files);
* `LICENSE`: the repository's top-level license notice. It assigns the
  Apache License 2.0 to `spectec/` (and `interpreter/`, `test/`) and the W3C
  Software and Document License to `document/`. It names no license for
  `specification/`. There is no `spectec/LICENSE` at this revision, so
  `spectec/LICENSE-Apache-2.0` is a copy of `interpreter/LICENSE` (the
  Apache 2.0 text the notice refers to).

Nothing here is edited. `.gitattributes` marks the tree `-whitespace`.

## How the files were fetched and checked

```sh
R=https://raw.githubusercontent.com/WebAssembly/spec/608711107b7f1edb13efd57b7d79b49477462d36
# every source path in ../manifest.json, plus the references:
for p in <manifest source paths> spectec/src/frontend/lexer.mll \
         spectec/src/frontend/parser.mly spectec/src/frontend/elab.ml LICENSE; do
  mkdir -p specs/spectec/src/$(dirname $p)
  curl -sfL $R/$p -o specs/spectec/src/$p
done
curl -sfL $R/interpreter/LICENSE -o specs/spectec/src/spectec/LICENSE-Apache-2.0

# check the 57 sources against the manifest (all 57 report OK):
python3 -c "import json;m=json.load(open('specs/spectec/manifest.json'))
for s in m['specs']:
  for f in s['sources']: print(f['sha256']+'  specs/spectec/src/'+f['path'])" \
  | sha256sum -c
```

The reference files are not in the manifest; their SHA-256s at fetch time:

```
f9b8edf89ebc989cacc509ea0427bb27d8644df94d42907352e2d9f1c45411bf  spectec/src/frontend/lexer.mll
b85440b187c179922f3637632857dce46475dd78aad8eca55fac4d430bd3a4de  spectec/src/frontend/parser.mly
cc1bfa4b988138a358af08530eb04e7773a704b652c1ce03358ffb93bb37d0e3  spectec/src/frontend/elab.ml
7f9c68bf8b4ed4acd32eb8b290b889a5149a734266838bf8be62c2819650af71  LICENSE
c6596eb7be8581c18be736c846fb9173b69eccf6ef94c5135893ec56bd92ba08  spectec/LICENSE-Apache-2.0
```
