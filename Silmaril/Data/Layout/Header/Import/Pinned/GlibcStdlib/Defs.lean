module

public import Silmaril.Data.Layout.Header.Import.Defs

/-! # `glibc-stdlib.json`: the pinned artifact and its import (generated: do not edit)

Written by `examples/headers/emit.lean` and compared byte for byte by
`examples/headers/recipe.sh --check`. `glibcStdlibJson` and `glibcStdlibProv` are the committed
`examples/headers/clang/glibc-stdlib.json` and `.prov`; `glibcStdlib` is their import, and `GlibcStdlib.entries`
the entries that import gives, as a literal. `import_glibcStdlib` (`Pinned.GlibcStdlib.Thms`) proves in the
kernel that they are equal; other theorems compute on the literal, never on the JSON.

The provenance, verbatim. It changes whenever the JSON does, so this module changes with it
and is rebuilt: Lake does not track the files `include_str` reads.

```text
artifact: glibc-stdlib.json
image: silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9
clang: Debian clang version 18.1.8 (++20240731024826+3b5b5c1ec4a3-1~exp1~20240731144843.145)
target: x86_64-unknown-linux-gnu
std: gnu11
cwd: .
command: clang -target x86_64-unknown-linux-gnu -x c -std=gnu11 /usr/include/stdlib.h -Xclang -ast-dump=json -fsyntax-only
filter: python3 -I filter.py /usr/include/stdlib.h /usr/include/alloca.h
filter-sha256: f7234d7a7bbf7792b9482c54edfb2d2a4ee1cb9f1c192a769e8cf0f34613241f
input: /usr/include/stdlib.h 2b535c0953b3441ef72729d09e83d98d22f87ca68f8b0e8f85d2fd2285afbc91 (in the image)
input: /usr/include/alloca.h 3f2699e77f222953411a2c276513fbe8d4b04aa410a50d5d5b762a019fad391c (in the image)
json-sha256: 70fb104eec20492aee2c0f0f62282b68d947ed0ed94a4f7d2a1a39a6b5055488
json-bytes: 57171
```
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

/-- `examples/headers/clang/glibc-stdlib.json`. -/
def glibcStdlibJson : String :=
  include_str "../../../../../../../examples/headers/clang/glibc-stdlib.json"
/-- `examples/headers/clang/glibc-stdlib.prov`. -/
def glibcStdlibProv : String :=
  include_str "../../../../../../../examples/headers/clang/glibc-stdlib.prov"
/-- glibc's `stdlib.h` (with `alloca.h`), hosted, as clang reads it: the import of `glibcStdlibJson`. Noncomputable: the kernel computes it (in
`import_glibcStdlib`), and compiled code uses the literal `GlibcStdlib.entries`. Compiling it would parse the
JSON when a program that imports this module starts, with recursion as deep as the JSON is long. -/
noncomputable def glibcStdlib : Imported := .ofJson (.parse glibcStdlibProv) glibcStdlibJson

/-- The entries of `glibcStdlib`, as a literal. -/
def GlibcStdlib.entries : List Entry := [
  ⟨"", .struct, (some ⟨"/usr/include/stdlib.h", 59⟩), false,
    (.tag true)⟩,
  ⟨"div_t", .typedef, (some ⟨"/usr/include/stdlib.h", 63⟩), false,
    (.typedef (.ok (.struct "div_t")))⟩,
  ⟨"", .struct, (some ⟨"/usr/include/stdlib.h", 67⟩), false,
    (.tag true)⟩,
  ⟨"ldiv_t", .typedef, (some ⟨"/usr/include/stdlib.h", 71⟩), false,
    (.typedef (.ok (.struct "ldiv_t")))⟩,
  ⟨"", .struct, (some ⟨"/usr/include/stdlib.h", 77⟩), false,
    (.tag true)⟩,
  ⟨"lldiv_t", .typedef, (some ⟨"/usr/include/stdlib.h", 81⟩), false,
    (.typedef (.ok (.struct "lldiv_t")))⟩,
  ⟨"__ctype_get_mb_cur_max", .function, (some ⟨"/usr/include/stdlib.h", 98⟩), false,
    (.function
      ⟨(.unsupported "result: unknown type name size_t"), (some ⟨[[]], []⟩),
       false, .c, [.nothrow], "__ctype_get_mb_cur_max", none, (some "extern"), false, false⟩)⟩,
  ⟨"atof", .function, (some ⟨"/usr/include/stdlib.h", 102⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "atof", none, (some "extern"), false, false⟩)⟩,
  ⟨"atoi", .function, (some ⟨"/usr/include/stdlib.h", 105⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "atoi", none, (some "extern"), false, false⟩)⟩,
  ⟨"atol", .function, (some ⟨"/usr/include/stdlib.h", 108⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "atol", none, (some "extern"), false, false⟩)⟩,
  ⟨"atoll", .function, (some ⟨"/usr/include/stdlib.h", 113⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "atoll", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtod", .function, (some ⟨"/usr/include/stdlib.h", 118⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[]], [[["const"], []], [[], [], []]]⟩),
       false, .c, [.builtin], "strtod", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtod", .function, (some ⟨"/usr/include/stdlib.h", 118⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strtod", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtof", .function, (some ⟨"/usr/include/stdlib.h", 124⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[]], [[["const"], []], [[], [], []]]⟩),
       false, .c, [.builtin], "strtof", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtof", .function, (some ⟨"/usr/include/stdlib.h", 124⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strtof", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtold", .function, (some ⟨"/usr/include/stdlib.h", 127⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[]], [[["const"], []], [[], [], []]]⟩),
       false, .c, [.builtin], "strtold", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtold", .function, (some ⟨"/usr/include/stdlib.h", 127⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strtold", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtol", .function, (some ⟨"/usr/include/stdlib.h", 177⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], []], [[], [], []], [[]]]⟩),
       false, .c, [.builtin], "strtol", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtol", .function, (some ⟨"/usr/include/stdlib.h", 177⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strtol", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtoul", .function, (some ⟨"/usr/include/stdlib.h", 181⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], []], [[], [], []], [[]]]⟩),
       false, .c, [.builtin], "strtoul", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtoul", .function, (some ⟨"/usr/include/stdlib.h", 181⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strtoul", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtoq", .function, (some ⟨"/usr/include/stdlib.h", 188⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "strtoq", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtouq", .function, (some ⟨"/usr/include/stdlib.h", 193⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .unsigned), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "strtouq", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtoll", .function, (some ⟨"/usr/include/stdlib.h", 201⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], []], [[], [], []], [[]]]⟩),
       false, .c, [.builtin], "strtoll", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtoll", .function, (some ⟨"/usr/include/stdlib.h", 201⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strtoll", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtoull", .function, (some ⟨"/usr/include/stdlib.h", 206⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .unsigned), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], []], [[], [], []], [[]]]⟩),
       false, .c, [.builtin], "strtoull", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtoull", .function, (some ⟨"/usr/include/stdlib.h", 206⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .unsigned), [(.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain))), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], ["restrict"]], [[], [], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strtoull", none, (some "extern"), false, false⟩)⟩,
  ⟨"l64a", .function, (some ⟨"/usr/include/stdlib.h", 386⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.int .long .signed)], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.nothrow], "l64a", none, (some "extern"), false, false⟩)⟩,
  ⟨"a64l", .function, (some ⟨"/usr/include/stdlib.h", 389⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "a64l", none, (some "extern"), false, false⟩)⟩,
  ⟨"random", .function, (some ⟨"/usr/include/stdlib.h", 402⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.nothrow], "random", none, (some "extern"), false, false⟩)⟩,
  ⟨"srandom", .function, (some ⟨"/usr/include/stdlib.h", 405⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.int .int .unsigned)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "srandom", none, (some "extern"), false, false⟩)⟩,
  ⟨"initstate", .function, (some ⟨"/usr/include/stdlib.h", 411⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.int .int .unsigned), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[]], [[], []], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "initstate", none, (some "extern"), false, false⟩)⟩,
  ⟨"setstate", .function, (some ⟨"/usr/include/stdlib.h", 416⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "setstate", none, (some "extern"), false, false⟩)⟩,
  ⟨"random_data", .struct, (some ⟨"/usr/include/stdlib.h", 424⟩), false,
    (.tag true)⟩,
  ⟨"random_r", .function, (some ⟨"/usr/include/stdlib.h", 435⟩), false,
    (.function
      ⟨(.unsupported "parameter 2: unknown type name int32_t"), (some ⟨[[]], [[[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "random_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"srandom_r", .function, (some ⟨"/usr/include/stdlib.h", 438⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .unsigned), (.ptr (.struct "random_data"))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "srandom_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"initstate_r", .function, (some ⟨"/usr/include/stdlib.h", 441⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .unsigned), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned)), (.ptr (.struct "random_data"))], false⟩), (some ⟨[[]], [[[]], [[], ["restrict"]], [[]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "initstate_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"setstate_r", .function, (some ⟨"/usr/include/stdlib.h", 446⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.ptr (.struct "random_data"))], false⟩), (some ⟨[[]], [[[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "setstate_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"rand", .function, (some ⟨"/usr/include/stdlib.h", 454⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.nothrow], "rand", none, (some "extern"), false, false⟩)⟩,
  ⟨"srand", .function, (some ⟨"/usr/include/stdlib.h", 456⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.int .int .unsigned)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "srand", none, (some "extern"), false, false⟩)⟩,
  ⟨"rand_r", .function, (some ⟨"/usr/include/stdlib.h", 460⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nothrow], "rand_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"drand48", .function, (some ⟨"/usr/include/stdlib.h", 468⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.nothrow], "drand48", none, (some "extern"), false, false⟩)⟩,
  ⟨"erand48", .function, (some ⟨"/usr/include/stdlib.h", 469⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.ptr (.int .short .unsigned))], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "erand48", none, (some "extern"), false, false⟩)⟩,
  ⟨"lrand48", .function, (some ⟨"/usr/include/stdlib.h", 472⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.nothrow], "lrand48", none, (some "extern"), false, false⟩)⟩,
  ⟨"nrand48", .function, (some ⟨"/usr/include/stdlib.h", 473⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.ptr (.int .short .unsigned))], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "nrand48", none, (some "extern"), false, false⟩)⟩,
  ⟨"mrand48", .function, (some ⟨"/usr/include/stdlib.h", 477⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.nothrow], "mrand48", none, (some "extern"), false, false⟩)⟩,
  ⟨"jrand48", .function, (some ⟨"/usr/include/stdlib.h", 478⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.ptr (.int .short .unsigned))], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "jrand48", none, (some "extern"), false, false⟩)⟩,
  ⟨"srand48", .function, (some ⟨"/usr/include/stdlib.h", 482⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.int .long .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "srand48", none, (some "extern"), false, false⟩)⟩,
  ⟨"seed48", .function, (some ⟨"/usr/include/stdlib.h", 483⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .short .unsigned)), [(.ptr (.int .short .unsigned))], false⟩), (some ⟨[[], []], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "seed48", none, (some "extern"), false, false⟩)⟩,
  ⟨"lcong48", .function, (some ⟨"/usr/include/stdlib.h", 485⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.ptr (.int .short .unsigned))], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "lcong48", none, (some "extern"), false, false⟩)⟩,
  ⟨"drand48_data", .struct, (some ⟨"/usr/include/stdlib.h", 491⟩), false,
    (.tag true)⟩,
  ⟨"drand48_r", .function, (some ⟨"/usr/include/stdlib.h", 502⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.struct "drand48_data")), (.ptr (.float .double))], false⟩), (some ⟨[[]], [[[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "drand48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"erand48_r", .function, (some ⟨"/usr/include/stdlib.h", 504⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .short .unsigned)), (.ptr (.struct "drand48_data")), (.ptr (.float .double))], false⟩), (some ⟨[[]], [[[], []], [[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "erand48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"lrand48_r", .function, (some ⟨"/usr/include/stdlib.h", 509⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.struct "drand48_data")), (.ptr (.int .long .signed))], false⟩), (some ⟨[[]], [[[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "lrand48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"nrand48_r", .function, (some ⟨"/usr/include/stdlib.h", 512⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .short .unsigned)), (.ptr (.struct "drand48_data")), (.ptr (.int .long .signed))], false⟩), (some ⟨[[]], [[[], []], [[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "nrand48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"mrand48_r", .function, (some ⟨"/usr/include/stdlib.h", 518⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.struct "drand48_data")), (.ptr (.int .long .signed))], false⟩), (some ⟨[[]], [[[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "mrand48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"jrand48_r", .function, (some ⟨"/usr/include/stdlib.h", 521⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .short .unsigned)), (.ptr (.struct "drand48_data")), (.ptr (.int .long .signed))], false⟩), (some ⟨[[]], [[[], []], [[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "jrand48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"srand48_r", .function, (some ⟨"/usr/include/stdlib.h", 527⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .long .signed), (.ptr (.struct "drand48_data"))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "srand48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"seed48_r", .function, (some ⟨"/usr/include/stdlib.h", 530⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .short .unsigned)), (.ptr (.struct "drand48_data"))], false⟩), (some ⟨[[]], [[[], []], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "seed48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"lcong48_r", .function, (some ⟨"/usr/include/stdlib.h", 533⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .short .unsigned)), (.ptr (.struct "drand48_data"))], false⟩), (some ⟨[[]], [[[], []], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "lcong48_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"arc4random", .function, (some ⟨"/usr/include/stdlib.h", 538⟩), false,
    (.function
      ⟨(.unsupported "result: unknown type name __uint32_t"), (some ⟨[[]], []⟩),
       false, .c, [.nothrow], "arc4random", none, (some "extern"), false, false⟩)⟩,
  ⟨"arc4random_buf", .function, (some ⟨"/usr/include/stdlib.h", 542⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.ptr .void), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[], []], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "arc4random_buf", none, (some "extern"), false, false⟩)⟩,
  ⟨"arc4random_uniform", .function, (some ⟨"/usr/include/stdlib.h", 547⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "__uint32_t" (.int .int .unsigned)), [(.typedef "__uint32_t" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "arc4random_uniform", none, (some "extern"), false, false⟩)⟩,
  ⟨"malloc", .function, (some ⟨"/usr/include/stdlib.h", 553⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.builtin, .allocSize], "malloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"malloc", .function, (some ⟨"/usr/include/stdlib.h", 553⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.builtin, .allocSize, .nothrow, .restrict, .allocSize], "malloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"calloc", .function, (some ⟨"/usr/include/stdlib.h", 556⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.int .long .unsigned), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[]], [[]]]⟩),
       false, .c, [.builtin, .allocSize], "calloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"calloc", .function, (some ⟨"/usr/include/stdlib.h", 556⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.typedef "size_t" (.int .long .unsigned)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[]], [[]]]⟩),
       false, .c, [.builtin, .allocSize, .nothrow, .restrict, .allocSize], "calloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"realloc", .function, (some ⟨"/usr/include/stdlib.h", 564⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[], []], [[]]]⟩),
       false, .c, [.builtin, .allocSize], "realloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"realloc", .function, (some ⟨"/usr/include/stdlib.h", 564⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], []], [[]]]⟩),
       false, .c, [.builtin, .allocSize, .nothrow, .warnUnusedResult, .allocSize], "realloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"free", .function, (some ⟨"/usr/include/stdlib.h", 568⟩), true,
    (.function
      ⟨(.ok ⟨.void, [(.ptr .void)], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.builtin], "free", none, (some "extern"), false, false⟩)⟩,
  ⟨"free", .function, (some ⟨"/usr/include/stdlib.h", 568⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.ptr .void)], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.builtin, .nothrow], "free", none, (some "extern"), false, false⟩)⟩,
  ⟨"reallocarray", .function, (some ⟨"/usr/include/stdlib.h", 576⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.typedef "size_t" (.int .long .unsigned)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], []], [[]], [[]]]⟩),
       false, .c, [.nothrow, .warnUnusedResult], "reallocarray", none, (some "extern"), false, false⟩)⟩,
  ⟨"reallocarray", .function, (some ⟨"/usr/include/stdlib.h", 582⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.typedef "size_t" (.int .long .unsigned)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], []], [[]], [[]]]⟩),
       false, .c, [.warnUnusedResult, .nothrow], "reallocarray", none, (some "extern"), false, false⟩)⟩,
  ⟨"alloca", .function, (some ⟨"/usr/include/alloca.h", 32⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.builtin], "alloca", none, (some "extern"), false, false⟩)⟩,
  ⟨"alloca", .function, (some ⟨"/usr/include/alloca.h", 32⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "alloca", none, (some "extern"), false, false⟩)⟩,
  ⟨"valloc", .function, (some ⟨"/usr/include/stdlib.h", 593⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.nothrow, .restrict], "valloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"posix_memalign", .function, (some ⟨"/usr/include/stdlib.h", 599⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.ptr .void)), (.typedef "size_t" (.int .long .unsigned)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[], [], []], [[]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "posix_memalign", none, (some "extern"), false, false⟩)⟩,
  ⟨"aligned_alloc", .function, (some ⟨"/usr/include/stdlib.h", 605⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.int .long .unsigned), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[]], [[]]]⟩),
       false, .c, [.builtin, (.other "AllocAlignAttr"), .allocSize], "aligned_alloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"aligned_alloc", .function, (some ⟨"/usr/include/stdlib.h", 605⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.typedef "size_t" (.int .long .unsigned)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[]], [[]]]⟩),
       false, .c, [.builtin, .allocSize, .nothrow, .restrict, (.other "AllocAlignAttr"), .allocSize], "aligned_alloc", none, (some "extern"), false, false⟩)⟩,
  ⟨"abort", .function, (some ⟨"/usr/include/stdlib.h", 611⟩), true,
    (.function
      ⟨(.ok ⟨.void, [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.noreturn, .builtin], "abort", none, (some "extern"), false, false⟩)⟩,
  ⟨"abort", .function, (some ⟨"/usr/include/stdlib.h", 611⟩), false,
    (.function
      ⟨(.ok ⟨.void, [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.noreturn, .builtin, .nothrow], "abort", none, (some "extern"), false, false⟩)⟩,
  ⟨"atexit", .function, (some ⟨"/usr/include/stdlib.h", 615⟩), false,
    (.function
      ⟨(.unsupported "parameter 1: function or function-pointer type: outside CProto"), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "atexit", none, (some "extern"), false, false⟩)⟩,
  ⟨"at_quick_exit", .function, (some ⟨"/usr/include/stdlib.h", 623⟩), false,
    (.function
      ⟨(.unsupported "parameter 1: function or function-pointer type: outside CProto"), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "at_quick_exit", none, (some "extern"), false, false⟩)⟩,
  ⟨"on_exit", .function, (some ⟨"/usr/include/stdlib.h", 630⟩), false,
    (.function
      ⟨(.unsupported "parameter 1: function or function-pointer type: outside CProto"), (some ⟨[[]], [[[], [], []], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "on_exit", none, (some "extern"), false, false⟩)⟩,
  ⟨"exit", .function, (some ⟨"/usr/include/stdlib.h", 637⟩), true,
    (.function
      ⟨(.ok ⟨.void, [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.noreturn, .builtin], "exit", none, (some "extern"), false, false⟩)⟩,
  ⟨"exit", .function, (some ⟨"/usr/include/stdlib.h", 637⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.noreturn, .builtin, .nothrow], "exit", none, (some "extern"), false, false⟩)⟩,
  ⟨"quick_exit", .function, (some ⟨"/usr/include/stdlib.h", 643⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.noreturn, .nothrow], "quick_exit", none, (some "extern"), false, false⟩)⟩,
  ⟨"_Exit", .function, (some ⟨"/usr/include/stdlib.h", 649⟩), true,
    (.function
      ⟨(.ok ⟨.void, [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.noreturn, .builtin], "_Exit", none, (some "extern"), false, false⟩)⟩,
  ⟨"_Exit", .function, (some ⟨"/usr/include/stdlib.h", 649⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.noreturn, .builtin, .nothrow], "_Exit", none, (some "extern"), false, false⟩)⟩,
  ⟨"getenv", .function, (some ⟨"/usr/include/stdlib.h", 654⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[["const"], []]]⟩),
       false, .c, [.nothrow, .nonnull], "getenv", none, (some "extern"), false, false⟩)⟩,
  ⟨"putenv", .function, (some ⟨"/usr/include/stdlib.h", 667⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "putenv", none, (some "extern"), false, false⟩)⟩,
  ⟨"setenv", .function, (some ⟨"/usr/include/stdlib.h", 673⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "setenv", none, (some "extern"), false, false⟩)⟩,
  ⟨"unsetenv", .function, (some ⟨"/usr/include/stdlib.h", 677⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow, .nonnull], "unsetenv", none, (some "extern"), false, false⟩)⟩,
  ⟨"clearenv", .function, (some ⟨"/usr/include/stdlib.h", 684⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.nothrow], "clearenv", none, (some "extern"), false, false⟩)⟩,
  ⟨"mktemp", .function, (some ⟨"/usr/include/stdlib.h", 695⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "mktemp", none, (some "extern"), false, false⟩)⟩,
  ⟨"mkstemp", .function, (some ⟨"/usr/include/stdlib.h", 708⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[[], []]]⟩),
       false, .c, [.nonnull], "mkstemp", none, (some "extern"), false, false⟩)⟩,
  ⟨"mkstemps", .function, (some ⟨"/usr/include/stdlib.h", 730⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[]], [[[], []], [[]]]⟩),
       false, .c, [.nonnull], "mkstemps", none, (some "extern"), false, false⟩)⟩,
  ⟨"mkdtemp", .function, (some ⟨"/usr/include/stdlib.h", 751⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "mkdtemp", none, (some "extern"), false, false⟩)⟩,
  ⟨"system", .function, (some ⟨"/usr/include/stdlib.h", 804⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [], "system", none, (some "extern"), false, false⟩)⟩,
  ⟨"realpath", .function, (some ⟨"/usr/include/stdlib.h", 821⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[["const"], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow], "realpath", none, (some "extern"), false, false⟩)⟩,
  ⟨"__compar_fn_t", .typedef, (some ⟨"/usr/include/stdlib.h", 829⟩), false,
    (.typedef (.unsupported "function or function-pointer type: outside CProto"))⟩,
  ⟨"bsearch", .function, (some ⟨"/usr/include/stdlib.h", 841⟩), false,
    (.function
      ⟨(.unsupported "parameter 5: typedef __compar_fn_t: function or function-pointer type: outside CProto"), (some ⟨[[], []], [[["const"], []], [["const"], []], [[]], [[]], [[]]]⟩),
       false, .c, [.nonnull], "bsearch", none, (some "extern"), false, false⟩)⟩,
  ⟨"qsort", .function, (some ⟨"/usr/include/stdlib.h", 851⟩), false,
    (.function
      ⟨(.unsupported "parameter 4: typedef __compar_fn_t: function or function-pointer type: outside CProto"), (some ⟨[[]], [[[], []], [[]], [[]], [[]]]⟩),
       false, .c, [.nonnull], "qsort", none, (some "extern"), false, false⟩)⟩,
  ⟨"abs", .function, (some ⟨"/usr/include/stdlib.h", 861⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "abs", none, (some "extern"), false, false⟩)⟩,
  ⟨"abs", .function, (some ⟨"/usr/include/stdlib.h", 861⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "abs", none, (some "extern"), false, false⟩)⟩,
  ⟨"labs", .function, (some ⟨"/usr/include/stdlib.h", 862⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.int .long .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "labs", none, (some "extern"), false, false⟩)⟩,
  ⟨"labs", .function, (some ⟨"/usr/include/stdlib.h", 862⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.int .long .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "labs", none, (some "extern"), false, false⟩)⟩,
  ⟨"llabs", .function, (some ⟨"/usr/include/stdlib.h", 865⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.int .longLong .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "llabs", none, (some "extern"), false, false⟩)⟩,
  ⟨"llabs", .function, (some ⟨"/usr/include/stdlib.h", 865⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.int .longLong .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "llabs", none, (some "extern"), false, false⟩)⟩,
  ⟨"div", .function, (some ⟨"/usr/include/stdlib.h", 873⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "div_t" (.struct "div_t")), [(.int .int .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "div", none, (some "extern"), false, false⟩)⟩,
  ⟨"ldiv", .function, (some ⟨"/usr/include/stdlib.h", 875⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "ldiv_t" (.struct "ldiv_t")), [(.int .long .signed), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "ldiv", none, (some "extern"), false, false⟩)⟩,
  ⟨"lldiv", .function, (some ⟨"/usr/include/stdlib.h", 879⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "lldiv_t" (.struct "lldiv_t")), [(.int .longLong .signed), (.int .longLong .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "lldiv", none, (some "extern"), false, false⟩)⟩,
  ⟨"ecvt", .function, (some ⟨"/usr/include/stdlib.h", 893⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.float .double), (.int .int .signed), (.ptr (.int .int .signed)), (.ptr (.int .int .signed))], false⟩), (some ⟨[[], []], [[[]], [[]], [[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "ecvt", none, (some "extern"), false, false⟩)⟩,
  ⟨"fcvt", .function, (some ⟨"/usr/include/stdlib.h", 899⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.float .double), (.int .int .signed), (.ptr (.int .int .signed)), (.ptr (.int .int .signed))], false⟩), (some ⟨[[], []], [[[]], [[]], [[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "fcvt", none, (some "extern"), false, false⟩)⟩,
  ⟨"gcvt", .function, (some ⟨"/usr/include/stdlib.h", 905⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.float .double), (.int .int .signed), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[]], [[]], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "gcvt", none, (some "extern"), false, false⟩)⟩,
  ⟨"qecvt", .function, (some ⟨"/usr/include/stdlib.h", 911⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.float .longDouble), (.int .int .signed), (.ptr (.int .int .signed)), (.ptr (.int .int .signed))], false⟩), (some ⟨[[], []], [[[]], [[]], [[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "qecvt", none, (some "extern"), false, false⟩)⟩,
  ⟨"qfcvt", .function, (some ⟨"/usr/include/stdlib.h", 914⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.float .longDouble), (.int .int .signed), (.ptr (.int .int .signed)), (.ptr (.int .int .signed))], false⟩), (some ⟨[[], []], [[[]], [[]], [[], ["restrict"]], [[], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "qfcvt", none, (some "extern"), false, false⟩)⟩,
  ⟨"qgcvt", .function, (some ⟨"/usr/include/stdlib.h", 917⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.float .longDouble), (.int .int .signed), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[]], [[]], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "qgcvt", none, (some "extern"), false, false⟩)⟩,
  ⟨"ecvt_r", .function, (some ⟨"/usr/include/stdlib.h", 923⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double), (.int .int .signed), (.ptr (.int .int .signed)), (.ptr (.int .int .signed)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]], [[], ["restrict"]], [[], ["restrict"]], [[], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "ecvt_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"fcvt_r", .function, (some ⟨"/usr/include/stdlib.h", 926⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double), (.int .int .signed), (.ptr (.int .int .signed)), (.ptr (.int .int .signed)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]], [[], ["restrict"]], [[], ["restrict"]], [[], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "fcvt_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"qecvt_r", .function, (some ⟨"/usr/include/stdlib.h", 930⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble), (.int .int .signed), (.ptr (.int .int .signed)), (.ptr (.int .int .signed)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]], [[], ["restrict"]], [[], ["restrict"]], [[], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "qecvt_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"qfcvt_r", .function, (some ⟨"/usr/include/stdlib.h", 934⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble), (.int .int .signed), (.ptr (.int .int .signed)), (.ptr (.int .int .signed)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]], [[], ["restrict"]], [[], ["restrict"]], [[], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "qfcvt_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"mblen", .function, (some ⟨"/usr/include/stdlib.h", 943⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[["const"], []], [[]]]⟩),
       false, .c, [.nothrow], "mblen", none, (some "extern"), false, false⟩)⟩,
  ⟨"mbtowc", .function, (some ⟨"/usr/include/stdlib.h", 946⟩), false,
    (.function
      ⟨(.unsupported "parameter 1: unknown type name wchar_t"), (some ⟨[[]], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow], "mbtowc", none, (some "extern"), false, false⟩)⟩,
  ⟨"wctomb", .function, (some ⟨"/usr/include/stdlib.h", 950⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.typedef "wchar_t" (.int .int .signed))], false⟩), (some ⟨[[]], [[[], []], [[]]]⟩),
       false, .c, [.nothrow], "wctomb", none, (some "extern"), false, false⟩)⟩,
  ⟨"mbstowcs", .function, (some ⟨"/usr/include/stdlib.h", 954⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "size_t" (.int .long .unsigned)), [(.ptr (.typedef "wchar_t" (.int .int .signed))), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow], "mbstowcs", none, (some "extern"), false, false⟩)⟩,
  ⟨"wcstombs", .function, (some ⟨"/usr/include/stdlib.h", 958⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "size_t" (.int .long .unsigned)), [(.ptr (.int .char .plain)), (.ptr (.typedef "wchar_t" (.int .int .signed))), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow], "wcstombs", none, (some "extern"), false, false⟩)⟩,
  ⟨"rpmatch", .function, (some ⟨"/usr/include/stdlib.h", 969⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow, .nonnull], "rpmatch", none, (some "extern"), false, false⟩)⟩,
  ⟨"getsubopt", .function, (some ⟨"/usr/include/stdlib.h", 980⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.ptr (.int .char .plain))), (.ptr (.ptr (.int .char .plain))), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[]], [[[], [], ["restrict"]], [[], ["const"], ["restrict"]], [[], [], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "getsubopt", none, (some "extern"), false, false⟩)⟩,
  ⟨"getloadavg", .function, (some ⟨"/usr/include/stdlib.h", 1026⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.float .double)), (.int .int .signed)], false⟩), (some ⟨[[]], [[[], []], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "getloadavg", none, (some "extern"), false, false⟩)⟩]

end Silmaril.Data.Layout.Header.Import.Pinned

end
