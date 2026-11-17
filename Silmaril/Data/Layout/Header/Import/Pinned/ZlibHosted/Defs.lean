module

public import Silmaril.Data.Layout.Header.Import.Defs

/-! # `zlib-hosted.json`: the pinned artifact and its import (generated: do not edit)

Written by `examples/headers/emit.lean` and compared byte for byte by
`examples/headers/recipe.sh --check`. `zlibHostedJson` and `zlibHostedProv` are the committed
`examples/headers/clang/zlib-hosted.json` and `.prov`; `zlibHosted` is their import, and `ZlibHosted.entries`
the entries that import gives, as a literal. `import_zlibHosted` (`Pinned.ZlibHosted.Thms`) proves in the
kernel that they are equal; other theorems compute on the literal, never on the JSON.

The provenance, verbatim. It changes whenever the JSON does, so this module changes with it
and is rebuilt: Lake does not track the files `include_str` reads.

```text
artifact: zlib-hosted.json
image: silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9
clang: Debian clang version 18.1.8 (++20240731024826+3b5b5c1ec4a3-1~exp1~20240731144843.145)
target: x86_64-unknown-linux-gnu
std: gnu11
cwd: zlib-1.3.1
command: clang -target x86_64-unknown-linux-gnu -x c -std=gnu11 zlib.h -Xclang -ast-dump=json -fsyntax-only
filter: python3 -I filter.py zlib.h ./zconf.h
filter-sha256: f7234d7a7bbf7792b9482c54edfb2d2a4ee1cb9f1c192a769e8cf0f34613241f
source: zlib-1.3.1.tar.gz 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23 https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz
input: zlib.h 8a5579af72ea4f427ff00a4150f0ccb3fc5c1e4379f726e101133b1ab9fc600c
input: ./zconf.h f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae
json-sha256: c312a7c3c0ddd5c78b52e6c465f3e49ef5c5c05525016efc5868e8adfefe90b6
json-bytes: 38247
```
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

/-- `examples/headers/clang/zlib-hosted.json`. -/
def zlibHostedJson : String :=
  include_str "../../../../../../../examples/headers/clang/zlib-hosted.json"
/-- `examples/headers/clang/zlib-hosted.prov`. -/
def zlibHostedProv : String :=
  include_str "../../../../../../../examples/headers/clang/zlib-hosted.prov"
/-- zlib 1.3.1's `zlib.h`, hosted, as clang reads it: the import of `zlibHostedJson`. -/
def zlibHosted : Imported := .ofJson (.parse zlibHostedProv) zlibHostedJson

/-- The entries of `zlibHosted`, as a literal. -/
def ZlibHosted.entries : List Entry := [
  ⟨"z_size_t", .typedef, (some ⟨"./zconf.h", 255⟩), false,
    (.typedef (.ok (.typedef "size_t" (.int .long .unsigned))))⟩,
  ⟨"Byte", .typedef, (some ⟨"./zconf.h", 393⟩), false,
    (.typedef (.ok (.int .char .unsigned)))⟩,
  ⟨"uInt", .typedef, (some ⟨"./zconf.h", 395⟩), false,
    (.typedef (.ok (.int .int .unsigned)))⟩,
  ⟨"uLong", .typedef, (some ⟨"./zconf.h", 396⟩), false,
    (.typedef (.ok (.int .long .unsigned)))⟩,
  ⟨"Bytef", .typedef, (some ⟨"./zconf.h", 402⟩), false,
    (.typedef (.ok (.typedef "Byte" (.int .char .unsigned))))⟩,
  ⟨"charf", .typedef, (some ⟨"./zconf.h", 404⟩), false,
    (.typedef (.ok (.int .char .plain)))⟩,
  ⟨"intf", .typedef, (some ⟨"./zconf.h", 405⟩), false,
    (.typedef (.ok (.int .int .signed)))⟩,
  ⟨"uIntf", .typedef, (some ⟨"./zconf.h", 406⟩), false,
    (.typedef (.ok (.typedef "uInt" (.int .int .unsigned))))⟩,
  ⟨"uLongf", .typedef, (some ⟨"./zconf.h", 407⟩), false,
    (.typedef (.ok (.typedef "uLong" (.int .long .unsigned))))⟩,
  ⟨"voidpc", .typedef, (some ⟨"./zconf.h", 410⟩), false,
    (.typedef (.ok (.ptr .void)))⟩,
  ⟨"voidpf", .typedef, (some ⟨"./zconf.h", 411⟩), false,
    (.typedef (.ok (.ptr .void)))⟩,
  ⟨"voidp", .typedef, (some ⟨"./zconf.h", 412⟩), false,
    (.typedef (.ok (.ptr .void)))⟩,
  ⟨"z_crc_t", .typedef, (some ⟨"./zconf.h", 431⟩), false,
    (.typedef (.ok (.int .int .unsigned)))⟩,
  ⟨"alloc_func", .typedef, (some ⟨"zlib.h", 81⟩), false,
    (.typedef (.unsupported "function or function-pointer type: outside CProto"))⟩,
  ⟨"free_func", .typedef, (some ⟨"zlib.h", 82⟩), false,
    (.typedef (.unsupported "function or function-pointer type: outside CProto"))⟩,
  ⟨"internal_state", .struct, (some ⟨"zlib.h", 84⟩), false,
    (.tag false)⟩,
  ⟨"z_stream_s", .struct, (some ⟨"zlib.h", 86⟩), false,
    (.tag true)⟩,
  ⟨"z_stream", .typedef, (some ⟨"zlib.h", 106⟩), false,
    (.typedef (.ok (.struct "z_stream_s")))⟩,
  ⟨"z_streamp", .typedef, (some ⟨"zlib.h", 108⟩), false,
    (.typedef (.ok (.ptr (.typedef "z_stream" (.struct "z_stream_s")))))⟩,
  ⟨"gz_header_s", .struct, (some ⟨"zlib.h", 114⟩), false,
    (.tag true)⟩,
  ⟨"gz_header", .typedef, (some ⟨"zlib.h", 129⟩), false,
    (.typedef (.ok (.struct "gz_header_s")))⟩,
  ⟨"gz_headerp", .typedef, (some ⟨"zlib.h", 131⟩), false,
    (.typedef (.ok (.ptr (.typedef "gz_header" (.struct "gz_header_s")))))⟩,
  ⟨"zlibVersion", .function, (some ⟨"zlib.h", 220⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [], false⟩), (some ⟨[["const"], []], []⟩),
       false, .c, [], "zlibVersion", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflate", .function, (some ⟨"zlib.h", 250⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "deflate", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateEnd", .function, (some ⟨"zlib.h", 363⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "deflateEnd", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflate", .function, (some ⟨"zlib.h", 401⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "inflate", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateEnd", .function, (some ⟨"zlib.h", 521⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inflateEnd", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateSetDictionary", .function, (some ⟨"zlib.h", 611⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "uInt" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[]]]⟩),
       false, .c, [], "deflateSetDictionary", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateGetDictionary", .function, (some ⟨"zlib.h", 655⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.ptr (.typedef "uInt" (.int .int .unsigned)))], false⟩), (some ⟨[[]], [[[]], [[], []], [[], []]]⟩),
       false, .c, [], "deflateGetDictionary", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateCopy", .function, (some ⟨"zlib.h", 677⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "deflateCopy", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateReset", .function, (some ⟨"zlib.h", 695⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "deflateReset", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateParams", .function, (some ⟨"zlib.h", 706⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "deflateParams", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateTune", .function, (some ⟨"zlib.h", 744⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed), (.int .int .signed), (.int .int .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]], [[]], [[]]]⟩),
       false, .c, [], "deflateTune", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateBound", .function, (some ⟨"zlib.h", 761⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.typedef "uLong" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "deflateBound", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflatePending", .function, (some ⟨"zlib.h", 776⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.ptr (.int .int .unsigned)), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []], [[], []]]⟩),
       false, .c, [], "deflatePending", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflatePrime", .function, (some ⟨"zlib.h", 791⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "deflatePrime", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateSetHeader", .function, (some ⟨"zlib.h", 808⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.typedef "gz_headerp" (.ptr (.typedef "gz_header" (.struct "gz_header_s"))))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "deflateSetHeader", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateSetDictionary", .function, (some ⟨"zlib.h", 888⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "uInt" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[]]]⟩),
       false, .c, [], "inflateSetDictionary", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateGetDictionary", .function, (some ⟨"zlib.h", 911⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.ptr (.typedef "uInt" (.int .int .unsigned)))], false⟩), (some ⟨[[]], [[[]], [[], []], [[], []]]⟩),
       false, .c, [], "inflateGetDictionary", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateSync", .function, (some ⟨"zlib.h", 926⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inflateSync", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateCopy", .function, (some ⟨"zlib.h", 945⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "inflateCopy", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateReset", .function, (some ⟨"zlib.h", 961⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inflateReset", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateReset2", .function, (some ⟨"zlib.h", 972⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "inflateReset2", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflatePrime", .function, (some ⟨"zlib.h", 986⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "inflatePrime", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateMark", .function, (some ⟨"zlib.h", 1007⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inflateMark", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateGetHeader", .function, (some ⟨"zlib.h", 1035⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.typedef "gz_headerp" (.ptr (.typedef "gz_header" (.struct "gz_header_s"))))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "inflateGetHeader", none, (some "extern"), false, false⟩)⟩,
  ⟨"in_func", .typedef, (some ⟨"zlib.h", 1097⟩), false,
    (.typedef (.unsupported "function or function-pointer type: outside CProto"))⟩,
  ⟨"out_func", .typedef, (some ⟨"zlib.h", 1099⟩), false,
    (.typedef (.unsupported "function or function-pointer type: outside CProto"))⟩,
  ⟨"inflateBack", .function, (some ⟨"zlib.h", 1101⟩), false,
    (.function
      ⟨(.unsupported "parameter 2: typedef in_func: function or function-pointer type: outside CProto"), (some ⟨[[]], [[[]], [[]], [[], []], [[]], [[], []]]⟩),
       false, .c, [], "inflateBack", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateBackEnd", .function, (some ⟨"zlib.h", 1171⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inflateBackEnd", none, (some "extern"), false, false⟩)⟩,
  ⟨"zlibCompileFlags", .function, (some ⟨"zlib.h", 1179⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [], "zlibCompileFlags", none, (some "extern"), false, false⟩)⟩,
  ⟨"compress", .function, (some ⟨"zlib.h", 1232⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.ptr (.typedef "uLongf" (.typedef "uLong" (.int .long .unsigned)))), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "uLong" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[], []], [[], []], [["const"], []], [[]]]⟩),
       false, .c, [], "compress", none, (some "extern"), false, false⟩)⟩,
  ⟨"compress2", .function, (some ⟨"zlib.h", 1247⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.ptr (.typedef "uLongf" (.typedef "uLong" (.int .long .unsigned)))), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "uLong" (.int .long .unsigned)), (.int .int .signed)], false⟩), (some ⟨[[]], [[[], []], [[], []], [["const"], []], [[]], [[]]]⟩),
       false, .c, [], "compress2", none, (some "extern"), false, false⟩)⟩,
  ⟨"compressBound", .function, (some ⟨"zlib.h", 1263⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "uLong" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "compressBound", none, (some "extern"), false, false⟩)⟩,
  ⟨"uncompress", .function, (some ⟨"zlib.h", 1270⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.ptr (.typedef "uLongf" (.typedef "uLong" (.int .long .unsigned)))), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "uLong" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[], []], [[], []], [["const"], []], [[]]]⟩),
       false, .c, [], "uncompress", none, (some "extern"), false, false⟩)⟩,
  ⟨"uncompress2", .function, (some ⟨"zlib.h", 1288⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.ptr (.typedef "uLongf" (.typedef "uLong" (.int .long .unsigned)))), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.ptr (.typedef "uLong" (.int .long .unsigned)))], false⟩), (some ⟨[[]], [[[], []], [[], []], [["const"], []], [[], []]]⟩),
       false, .c, [], "uncompress2", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzFile_s", .struct, (some ⟨"zlib.h", 1305⟩), false,
    (.tag false)⟩,
  ⟨"gzFile", .typedef, (some ⟨"zlib.h", 1305⟩), false,
    (.typedef (.ok (.ptr (.struct "gzFile_s"))))⟩,
  ⟨"gzdopen", .function, (some ⟨"zlib.h", 1345⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), [(.int .int .signed), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[[]], [["const"], []]]⟩),
       false, .c, [], "gzdopen", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzbuffer", .function, (some ⟨"zlib.h", 1368⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.int .int .unsigned)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "gzbuffer", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzsetparams", .function, (some ⟨"zlib.h", 1384⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.int .int .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "gzsetparams", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzread", .function, (some ⟨"zlib.h", 1395⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.typedef "voidp" (.ptr .void)), (.int .int .unsigned)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "gzread", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzfread", .function, (some ⟨"zlib.h", 1425⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "z_size_t" (.typedef "size_t" (.int .long .unsigned))), [(.typedef "voidp" (.ptr .void)), (.typedef "z_size_t" (.typedef "size_t" (.int .long .unsigned))), (.typedef "z_size_t" (.typedef "size_t" (.int .long .unsigned))), (.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]], [[]], [[]], [[]]]⟩),
       false, .c, [], "gzfread", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzwrite", .function, (some ⟨"zlib.h", 1451⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.typedef "voidpc" (.ptr .void)), (.int .int .unsigned)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "gzwrite", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzfwrite", .function, (some ⟨"zlib.h", 1457⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "z_size_t" (.typedef "size_t" (.int .long .unsigned))), [(.typedef "voidpc" (.ptr .void)), (.typedef "z_size_t" (.typedef "size_t" (.int .long .unsigned))), (.typedef "z_size_t" (.typedef "size_t" (.int .long .unsigned))), (.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]], [[]], [[]], [[]]]⟩),
       false, .c, [], "gzfwrite", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzprintf", .function, (some ⟨"zlib.h", 1471⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.ptr (.int .char .plain))], true⟩), (some ⟨[[]], [[[]], [["const"], []]]⟩),
       true, .c, [], "gzprintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzputs", .function, (some ⟨"zlib.h", 1486⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[[]], [["const"], []]]⟩),
       false, .c, [], "gzputs", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzgets", .function, (some ⟨"zlib.h", 1494⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[], []], [[[]], [[], []], [[]]]⟩),
       false, .c, [], "gzgets", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzputc", .function, (some ⟨"zlib.h", 1508⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "gzputc", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzgetc", .function, (some ⟨"zlib.h", 1514⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzgetc", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzungetc", .function, (some ⟨"zlib.h", 1523⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed), (.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "gzungetc", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzflush", .function, (some ⟨"zlib.h", 1535⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "gzflush", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzrewind", .function, (some ⟨"zlib.h", 1570⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzrewind", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzeof", .function, (some ⟨"zlib.h", 1598⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzeof", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzdirect", .function, (some ⟨"zlib.h", 1613⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzdirect", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzclose", .function, (some ⟨"zlib.h", 1634⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzclose", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzclose_r", .function, (some ⟨"zlib.h", 1647⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzclose_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzclose_w", .function, (some ⟨"zlib.h", 1648⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzclose_w", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzerror", .function, (some ⟨"zlib.h", 1659⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.ptr (.int .int .signed))], false⟩), (some ⟨[["const"], []], [[[]], [[], []]]⟩),
       false, .c, [], "gzerror", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzclearerr", .function, (some ⟨"zlib.h", 1675⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzclearerr", none, (some "extern"), false, false⟩)⟩,
  ⟨"adler32", .function, (some ⟨"zlib.h", 1692⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "uLong" (.int .long .unsigned)), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "uInt" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[]]]⟩),
       false, .c, [], "adler32", none, (some "extern"), false, false⟩)⟩,
  ⟨"adler32_z", .function, (some ⟨"zlib.h", 1712⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "uLong" (.int .long .unsigned)), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "z_size_t" (.typedef "size_t" (.int .long .unsigned)))], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[]]]⟩),
       false, .c, [], "adler32_z", none, (some "extern"), false, false⟩)⟩,
  ⟨"crc32", .function, (some ⟨"zlib.h", 1730⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "uLong" (.int .long .unsigned)), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "uInt" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[]]]⟩),
       false, .c, [], "crc32", none, (some "extern"), false, false⟩)⟩,
  ⟨"crc32_z", .function, (some ⟨"zlib.h", 1748⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "uLong" (.int .long .unsigned)), (.ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))), (.typedef "z_size_t" (.typedef "size_t" (.int .long .unsigned)))], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[]]]⟩),
       false, .c, [], "crc32_z", none, (some "extern"), false, false⟩)⟩,
  ⟨"crc32_combine_op", .function, (some ⟨"zlib.h", 1771⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "uLong" (.int .long .unsigned)), (.typedef "uLong" (.int .long .unsigned)), (.typedef "uLong" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "crc32_combine_op", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateInit_", .function, (some ⟨"zlib.h", 1784⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed), (.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [["const"], []], [[]]]⟩),
       false, .c, [], "deflateInit_", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateInit_", .function, (some ⟨"zlib.h", 1786⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[]]]⟩),
       false, .c, [], "inflateInit_", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateInit2_", .function, (some ⟨"zlib.h", 1788⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed), (.int .int .signed), (.int .int .signed), (.int .int .signed), (.int .int .signed), (.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]], [[]], [[]], [[]], [["const"], []], [[]]]⟩),
       false, .c, [], "deflateInit2_", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateInit2_", .function, (some ⟨"zlib.h", 1792⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed), (.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [["const"], []], [[]]]⟩),
       false, .c, [], "inflateInit2_", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateBackInit_", .function, (some ⟨"zlib.h", 1794⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed), (.ptr (.int .char .unsigned)), (.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[], []], [["const"], []], [[]]]⟩),
       false, .c, [], "inflateBackInit_", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzFile_s", .struct, (some ⟨"zlib.h", 1837⟩), false,
    (.tag true)⟩,
  ⟨"gzgetc_", .function, (some ⟨"zlib.h", 1842⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzgetc_", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzopen", .function, (some ⟨"zlib.h", 1896⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []]]⟩),
       false, .c, [], "gzopen", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzseek", .function, (some ⟨"zlib.h", 1897⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.int .long .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "gzseek", none, (some "extern"), false, false⟩)⟩,
  ⟨"gztell", .function, (some ⟨"zlib.h", 1898⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gztell", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzoffset", .function, (some ⟨"zlib.h", 1899⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s")))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "gzoffset", none, (some "extern"), false, false⟩)⟩,
  ⟨"adler32_combine", .function, (some ⟨"zlib.h", 1900⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "uLong" (.int .long .unsigned)), (.typedef "uLong" (.int .long .unsigned)), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "adler32_combine", none, (some "extern"), false, false⟩)⟩,
  ⟨"crc32_combine", .function, (some ⟨"zlib.h", 1901⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.typedef "uLong" (.int .long .unsigned)), (.typedef "uLong" (.int .long .unsigned)), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "crc32_combine", none, (some "extern"), false, false⟩)⟩,
  ⟨"crc32_combine_gen", .function, (some ⟨"zlib.h", 1902⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "uLong" (.int .long .unsigned)), [(.int .long .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "crc32_combine_gen", none, (some "extern"), false, false⟩)⟩,
  ⟨"zError", .function, (some ⟨"zlib.h", 1914⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.int .int .signed)], false⟩), (some ⟨[["const"], []], [[[]]]⟩),
       false, .c, [], "zError", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateSyncPoint", .function, (some ⟨"zlib.h", 1915⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inflateSyncPoint", none, (some "extern"), false, false⟩)⟩,
  ⟨"get_crc_table", .function, (some ⟨"zlib.h", 1916⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.typedef "z_crc_t" (.int .int .unsigned))), [], false⟩), (some ⟨[["const"], []], []⟩),
       false, .c, [], "get_crc_table", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateUndermine", .function, (some ⟨"zlib.h", 1917⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "inflateUndermine", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateValidate", .function, (some ⟨"zlib.h", 1918⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s")))), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "inflateValidate", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateCodesUsed", .function, (some ⟨"zlib.h", 1919⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inflateCodesUsed", none, (some "extern"), false, false⟩)⟩,
  ⟨"inflateResetKeep", .function, (some ⟨"zlib.h", 1920⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inflateResetKeep", none, (some "extern"), false, false⟩)⟩,
  ⟨"deflateResetKeep", .function, (some ⟨"zlib.h", 1921⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "z_streamp" (.ptr (.typedef "z_stream" (.struct "z_stream_s"))))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "deflateResetKeep", none, (some "extern"), false, false⟩)⟩,
  ⟨"gzvprintf", .function, (some ⟨"zlib.h", 1928⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "gzFile" (.ptr (.struct "gzFile_s"))), (.ptr (.int .char .plain)), (.ptr (.struct "__va_list_tag"))], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[], []]]⟩),
       false, .c, [], "gzvprintf", none, (some "extern"), false, false⟩)⟩]

end Silmaril.Data.Layout.Header.Import.Pinned

end
