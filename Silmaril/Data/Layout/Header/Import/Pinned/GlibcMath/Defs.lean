module

public import Silmaril.Data.Layout.Header.Import.Defs

/-! # `glibc-math.json`: the pinned artifact and its import (generated: do not edit)

Written by `examples/headers/emit.lean` and compared byte for byte by
`examples/headers/recipe.sh --check`. `glibcMathJson` and `glibcMathProv` are the committed
`examples/headers/clang/glibc-math.json` and `.prov`; `glibcMath` is their import, and `GlibcMath.entries`
the entries that import gives, as a literal. `import_glibcMath` (`Pinned.GlibcMath.Thms`) proves in the
kernel that they are equal; other theorems compute on the literal, never on the JSON.

The provenance, verbatim. It changes whenever the JSON does, so this module changes with it
and is rebuilt: Lake does not track the files `include_str` reads.

```text
artifact: glibc-math.json
image: silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9
clang: Debian clang version 18.1.8 (++20240731024826+3b5b5c1ec4a3-1~exp1~20240731144843.145)
target: x86_64-unknown-linux-gnu
std: gnu11
cwd: .
command: clang -target x86_64-unknown-linux-gnu -x c -std=gnu11 /usr/include/math.h -Xclang -ast-dump=json -fsyntax-only
filter: python3 -I filter.py /usr/include/math.h /usr/include/x86_64-linux-gnu/bits/mathcalls.h /usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h /usr/include/x86_64-linux-gnu/bits/floatn-common.h
filter-sha256: f7234d7a7bbf7792b9482c54edfb2d2a4ee1cb9f1c192a769e8cf0f34613241f
input: /usr/include/math.h 4a0b7f8fe8b7d97eab417c8c295a6aecaba8b7d49bc240e40c35fd01b87ffad2 (in the image)
input: /usr/include/x86_64-linux-gnu/bits/mathcalls.h bb2f279f45b98be7fadcb1b6df9c6eeb121d77fd1a256b0a4fa91180d16d0ac3 (in the image)
input: /usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h c5f7141d7c6c3ac2a132528c56d2a712bd0304dfc205a0f0f0fd8fa59021f757 (in the image)
input: /usr/include/x86_64-linux-gnu/bits/floatn-common.h 34470310bc42f4ed4a8790ca3f33d1a11878a583561d51ad324ef5fb925d5493 (in the image)
json-sha256: db61bb75bdeca38285face86a1962ee1ea37a6f9b9b82c0e37c5b37e82f25e3d
json-bytes: 294120
```
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

/-- `examples/headers/clang/glibc-math.json`. -/
def glibcMathJson : String :=
  include_str "../../../../../../../examples/headers/clang/glibc-math.json"
/-- `examples/headers/clang/glibc-math.prov`. -/
def glibcMathProv : String :=
  include_str "../../../../../../../examples/headers/clang/glibc-math.prov"
/-- glibc's `math.h` (libm), hosted, as clang reads it: the import of `glibcMathJson`. Noncomputable: the kernel computes it (in
`import_glibcMath`), and compiled code uses the literal `GlibcMath.entries`. Compiling it would parse the
JSON when a program that imports this module starts, with recursion as deep as the JSON is long. -/
noncomputable def glibcMath : Imported := .ofJson (.parse glibcMathProv) glibcMathJson

/-- The entries of `glibcMath`, as a literal. -/
def GlibcMath.entries : List Entry := [
  ⟨"_Float32", .typedef, (some ⟨"/usr/include/x86_64-linux-gnu/bits/floatn-common.h", 214⟩), false,
    (.typedef (.ok (.float .float)))⟩,
  ⟨"_Float64", .typedef, (some ⟨"/usr/include/x86_64-linux-gnu/bits/floatn-common.h", 251⟩), false,
    (.typedef (.ok (.float .double)))⟩,
  ⟨"_Float32x", .typedef, (some ⟨"/usr/include/x86_64-linux-gnu/bits/floatn-common.h", 268⟩), false,
    (.typedef (.ok (.float .double)))⟩,
  ⟨"_Float64x", .typedef, (some ⟨"/usr/include/x86_64-linux-gnu/bits/floatn-common.h", 285⟩), false,
    (.typedef (.ok (.float .longDouble)))⟩,
  ⟨"float_t", .typedef, (some ⟨"/usr/include/math.h", 163⟩), false,
    (.typedef (.ok (.float .float)))⟩,
  ⟨"double_t", .typedef, (some ⟨"/usr/include/math.h", 164⟩), false,
    (.typedef (.ok (.float .double)))⟩,
  ⟨"__fpclassify", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 20⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__fpclassify", none, (some "extern"), false, false⟩)⟩,
  ⟨"__signbit", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 24⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__signbit", none, (some "extern"), false, false⟩)⟩,
  ⟨"__isinf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 29⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__isinf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__finite", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 33⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "__finite", none, (some "extern"), false, false⟩)⟩,
  ⟨"__finite", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 33⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "__finite", none, (some "extern"), false, false⟩)⟩,
  ⟨"__isnan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 37⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__isnan", none, (some "extern"), false, false⟩)⟩,
  ⟨"__iseqsig", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 41⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__iseqsig", none, (some "extern"), false, false⟩)⟩,
  ⟨"__issignaling", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 44⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__issignaling", none, (some "extern"), false, false⟩)⟩,
  ⟨"acos", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acos", none, (some "extern"), false, false⟩)⟩,
  ⟨"acos", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acos", none, (some "extern"), false, false⟩)⟩,
  ⟨"__acos", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__acos", none, (some "extern"), false, false⟩)⟩,
  ⟨"asin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asin", none, (some "extern"), false, false⟩)⟩,
  ⟨"asin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asin", none, (some "extern"), false, false⟩)⟩,
  ⟨"__asin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__asin", none, (some "extern"), false, false⟩)⟩,
  ⟨"atan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atan", none, (some "extern"), false, false⟩)⟩,
  ⟨"atan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atan", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__atan", none, (some "extern"), false, false⟩)⟩,
  ⟨"atan2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "atan2", none, (some "extern"), false, false⟩)⟩,
  ⟨"atan2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "atan2", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atan2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__atan2", none, (some "extern"), false, false⟩)⟩,
  ⟨"cos", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "cos", none, (some "extern"), false, false⟩)⟩,
  ⟨"cos", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "cos", none, (some "extern"), false, false⟩)⟩,
  ⟨"__cos", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__cos", none, (some "extern"), false, false⟩)⟩,
  ⟨"sin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sin", none, (some "extern"), false, false⟩)⟩,
  ⟨"sin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sin", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sin", none, (some "extern"), false, false⟩)⟩,
  ⟨"tan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tan", none, (some "extern"), false, false⟩)⟩,
  ⟨"tan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tan", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tan", none, (some "extern"), false, false⟩)⟩,
  ⟨"cosh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "cosh", none, (some "extern"), false, false⟩)⟩,
  ⟨"cosh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "cosh", none, (some "extern"), false, false⟩)⟩,
  ⟨"__cosh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__cosh", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinh", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinh", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sinh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sinh", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanh", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanh", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tanh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tanh", none, (some "extern"), false, false⟩)⟩,
  ⟨"acosh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acosh", none, (some "extern"), false, false⟩)⟩,
  ⟨"acosh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acosh", none, (some "extern"), false, false⟩)⟩,
  ⟨"__acosh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__acosh", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinh", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinh", none, (some "extern"), false, false⟩)⟩,
  ⟨"__asinh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__asinh", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanh", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanh", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atanh", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__atanh", none, (some "extern"), false, false⟩)⟩,
  ⟨"exp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "exp", none, (some "extern"), false, false⟩)⟩,
  ⟨"exp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "exp", none, (some "extern"), false, false⟩)⟩,
  ⟨"__exp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__exp", none, (some "extern"), false, false⟩)⟩,
  ⟨"frexp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "frexp", none, (some "extern"), false, false⟩)⟩,
  ⟨"frexp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "frexp", none, (some "extern"), false, false⟩)⟩,
  ⟨"__frexp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "__frexp", none, (some "extern"), false, false⟩)⟩,
  ⟨"ldexp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "ldexp", none, (some "extern"), false, false⟩)⟩,
  ⟨"ldexp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "ldexp", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ldexp", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__ldexp", none, (some "extern"), false, false⟩)⟩,
  ⟨"log", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log", none, (some "extern"), false, false⟩)⟩,
  ⟨"log", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log", none, (some "extern"), false, false⟩)⟩,
  ⟨"log10", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log10", none, (some "extern"), false, false⟩)⟩,
  ⟨"log10", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log10", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log10", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log10", none, (some "extern"), false, false⟩)⟩,
  ⟨"modf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.ptr (.float .double))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "modf", none, (some "extern"), false, false⟩)⟩,
  ⟨"modf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.ptr (.float .double))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "modf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__modf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.ptr (.float .double))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "__modf", none, (some "extern"), false, false⟩)⟩,
  ⟨"expm1", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expm1", none, (some "extern"), false, false⟩)⟩,
  ⟨"expm1", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expm1", none, (some "extern"), false, false⟩)⟩,
  ⟨"__expm1", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__expm1", none, (some "extern"), false, false⟩)⟩,
  ⟨"log1p", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log1p", none, (some "extern"), false, false⟩)⟩,
  ⟨"log1p", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log1p", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log1p", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log1p", none, (some "extern"), false, false⟩)⟩,
  ⟨"logb", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logb", none, (some "extern"), false, false⟩)⟩,
  ⟨"logb", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logb", none, (some "extern"), false, false⟩)⟩,
  ⟨"__logb", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__logb", none, (some "extern"), false, false⟩)⟩,
  ⟨"exp2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "exp2", none, (some "extern"), false, false⟩)⟩,
  ⟨"exp2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "exp2", none, (some "extern"), false, false⟩)⟩,
  ⟨"__exp2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__exp2", none, (some "extern"), false, false⟩)⟩,
  ⟨"log2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log2", none, (some "extern"), false, false⟩)⟩,
  ⟨"log2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log2", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log2", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log2", none, (some "extern"), false, false⟩)⟩,
  ⟨"pow", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "pow", none, (some "extern"), false, false⟩)⟩,
  ⟨"pow", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "pow", none, (some "extern"), false, false⟩)⟩,
  ⟨"__pow", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__pow", none, (some "extern"), false, false⟩)⟩,
  ⟨"sqrt", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sqrt", none, (some "extern"), false, false⟩)⟩,
  ⟨"sqrt", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sqrt", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sqrt", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sqrt", none, (some "extern"), false, false⟩)⟩,
  ⟨"hypot", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "hypot", none, (some "extern"), false, false⟩)⟩,
  ⟨"hypot", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "hypot", none, (some "extern"), false, false⟩)⟩,
  ⟨"__hypot", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__hypot", none, (some "extern"), false, false⟩)⟩,
  ⟨"cbrt", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "cbrt", none, (some "extern"), false, false⟩)⟩,
  ⟨"cbrt", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "cbrt", none, (some "extern"), false, false⟩)⟩,
  ⟨"__cbrt", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__cbrt", none, (some "extern"), false, false⟩)⟩,
  ⟨"ceil", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "ceil", none, (some "extern"), false, false⟩)⟩,
  ⟨"ceil", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "ceil", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ceil", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__ceil", none, (some "extern"), false, false⟩)⟩,
  ⟨"fabs", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fabs", none, (some "extern"), false, false⟩)⟩,
  ⟨"fabs", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fabs", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fabs", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__fabs", none, (some "extern"), false, false⟩)⟩,
  ⟨"floor", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "floor", none, (some "extern"), false, false⟩)⟩,
  ⟨"floor", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "floor", none, (some "extern"), false, false⟩)⟩,
  ⟨"__floor", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__floor", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmod", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fmod", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmod", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fmod", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmod", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__fmod", none, (some "extern"), false, false⟩)⟩,
  ⟨"isinf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 177⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "isinf", none, (some "extern"), false, false⟩)⟩,
  ⟨"finite", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 183⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "finite", none, (some "extern"), false, false⟩)⟩,
  ⟨"finite", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 183⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "finite", none, (some "extern"), false, false⟩)⟩,
  ⟨"drem", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 187⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "drem", none, (some "extern"), false, false⟩)⟩,
  ⟨"__drem", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 187⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__drem", none, (some "extern"), false, false⟩)⟩,
  ⟨"significand", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 191⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "significand", none, (some "extern"), false, false⟩)⟩,
  ⟨"__significand", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 191⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__significand", none, (some "extern"), false, false⟩)⟩,
  ⟨"copysign", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "copysign", none, (some "extern"), false, false⟩)⟩,
  ⟨"copysign", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "copysign", none, (some "extern"), false, false⟩)⟩,
  ⟨"__copysign", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__copysign", none, (some "extern"), false, false⟩)⟩,
  ⟨"nan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure], "nan", none, (some "extern"), false, false⟩)⟩,
  ⟨"nan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.builtin, .pure, .nothrow], "nan", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow], "__nan", none, (some "extern"), false, false⟩)⟩,
  ⟨"isnan", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 213⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "isnan", none, (some "extern"), false, false⟩)⟩,
  ⟨"j0", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 220⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "j0", none, (some "extern"), false, false⟩)⟩,
  ⟨"__j0", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 220⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__j0", none, (some "extern"), false, false⟩)⟩,
  ⟨"j1", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 221⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "j1", none, (some "extern"), false, false⟩)⟩,
  ⟨"__j1", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 221⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__j1", none, (some "extern"), false, false⟩)⟩,
  ⟨"jn", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 222⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.int .int .signed), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "jn", none, (some "extern"), false, false⟩)⟩,
  ⟨"__jn", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 222⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.int .int .signed), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__jn", none, (some "extern"), false, false⟩)⟩,
  ⟨"y0", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 223⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "y0", none, (some "extern"), false, false⟩)⟩,
  ⟨"__y0", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 223⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__y0", none, (some "extern"), false, false⟩)⟩,
  ⟨"y1", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 224⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "y1", none, (some "extern"), false, false⟩)⟩,
  ⟨"__y1", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 224⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__y1", none, (some "extern"), false, false⟩)⟩,
  ⟨"yn", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 225⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.int .int .signed), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "yn", none, (some "extern"), false, false⟩)⟩,
  ⟨"__yn", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 225⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.int .int .signed), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__yn", none, (some "extern"), false, false⟩)⟩,
  ⟨"erf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erf", none, (some "extern"), false, false⟩)⟩,
  ⟨"erf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__erf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__erf", none, (some "extern"), false, false⟩)⟩,
  ⟨"erfc", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erfc", none, (some "extern"), false, false⟩)⟩,
  ⟨"erfc", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erfc", none, (some "extern"), false, false⟩)⟩,
  ⟨"__erfc", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__erfc", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgamma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lgamma", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgamma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lgamma", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lgamma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lgamma", none, (some "extern"), false, false⟩)⟩,
  ⟨"tgamma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tgamma", none, (some "extern"), false, false⟩)⟩,
  ⟨"tgamma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tgamma", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tgamma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tgamma", none, (some "extern"), false, false⟩)⟩,
  ⟨"gamma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 244⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "gamma", none, (some "extern"), false, false⟩)⟩,
  ⟨"__gamma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 244⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__gamma", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgamma_r", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 252⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "lgamma_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lgamma_r", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 252⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "__lgamma_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"rint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "rint", none, (some "extern"), false, false⟩)⟩,
  ⟨"rint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "rint", none, (some "extern"), false, false⟩)⟩,
  ⟨"__rint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__rint", none, (some "extern"), false, false⟩)⟩,
  ⟨"nextafter", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nextafter", none, (some "extern"), false, false⟩)⟩,
  ⟨"nextafter", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nextafter", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nextafter", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__nextafter", none, (some "extern"), false, false⟩)⟩,
  ⟨"nexttoward", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nexttoward", none, (some "extern"), false, false⟩)⟩,
  ⟨"nexttoward", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nexttoward", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nexttoward", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__nexttoward", none, (some "extern"), false, false⟩)⟩,
  ⟨"remainder", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "remainder", none, (some "extern"), false, false⟩)⟩,
  ⟨"remainder", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "remainder", none, (some "extern"), false, false⟩)⟩,
  ⟨"__remainder", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__remainder", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbn", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalbn", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbn", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalbn", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalbn", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalbn", none, (some "extern"), false, false⟩)⟩,
  ⟨"ilogb", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "ilogb", none, (some "extern"), false, false⟩)⟩,
  ⟨"ilogb", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "ilogb", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ilogb", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__ilogb", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbln", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalbln", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbln", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalbln", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalbln", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalbln", none, (some "extern"), false, false⟩)⟩,
  ⟨"nearbyint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "nearbyint", none, (some "extern"), false, false⟩)⟩,
  ⟨"nearbyint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "nearbyint", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nearbyint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__nearbyint", none, (some "extern"), false, false⟩)⟩,
  ⟨"round", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "round", none, (some "extern"), false, false⟩)⟩,
  ⟨"round", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "round", none, (some "extern"), false, false⟩)⟩,
  ⟨"__round", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__round", none, (some "extern"), false, false⟩)⟩,
  ⟨"trunc", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "trunc", none, (some "extern"), false, false⟩)⟩,
  ⟨"trunc", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "trunc", none, (some "extern"), false, false⟩)⟩,
  ⟨"__trunc", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__trunc", none, (some "extern"), false, false⟩)⟩,
  ⟨"remquo", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "remquo", none, (some "extern"), false, false⟩)⟩,
  ⟨"remquo", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "remquo", none, (some "extern"), false, false⟩)⟩,
  ⟨"__remquo", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.nothrow], "__remquo", none, (some "extern"), false, false⟩)⟩,
  ⟨"lrint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lrint", none, (some "extern"), false, false⟩)⟩,
  ⟨"lrint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lrint", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lrint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lrint", none, (some "extern"), false, false⟩)⟩,
  ⟨"llrint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llrint", none, (some "extern"), false, false⟩)⟩,
  ⟨"llrint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llrint", none, (some "extern"), false, false⟩)⟩,
  ⟨"__llrint", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__llrint", none, (some "extern"), false, false⟩)⟩,
  ⟨"lround", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lround", none, (some "extern"), false, false⟩)⟩,
  ⟨"lround", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lround", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lround", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lround", none, (some "extern"), false, false⟩)⟩,
  ⟨"llround", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llround", none, (some "extern"), false, false⟩)⟩,
  ⟨"llround", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llround", none, (some "extern"), false, false⟩)⟩,
  ⟨"__llround", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .double)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__llround", none, (some "extern"), false, false⟩)⟩,
  ⟨"fdim", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fdim", none, (some "extern"), false, false⟩)⟩,
  ⟨"fdim", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fdim", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fdim", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__fdim", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmax", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fmax", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmax", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fmax", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmax", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__fmax", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fmin", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fmin", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmin", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__fmin", none, (some "extern"), false, false⟩)⟩,
  ⟨"fma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), true,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "fma", none, (some "extern"), false, false⟩)⟩,
  ⟨"fma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "fma", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fma", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.nothrow], "__fma", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalb", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 435⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "scalb", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalb", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 435⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .double), (.float .double)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalb", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fpclassifyf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 20⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__fpclassifyf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__signbitf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 24⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__signbitf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__isinff", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 29⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__isinff", none, (some "extern"), false, false⟩)⟩,
  ⟨"__finitef", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 33⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "__finitef", none, (some "extern"), false, false⟩)⟩,
  ⟨"__finitef", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 33⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "__finitef", none, (some "extern"), false, false⟩)⟩,
  ⟨"__isnanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 37⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__isnanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__iseqsigf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 41⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__iseqsigf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__issignalingf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 44⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__issignalingf", none, (some "extern"), false, false⟩)⟩,
  ⟨"acosf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acosf", none, (some "extern"), false, false⟩)⟩,
  ⟨"acosf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acosf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__acosf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__acosf", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinf", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__asinf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__asinf", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__atanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"atan2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "atan2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"atan2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "atan2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atan2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__atan2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"cosf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "cosf", none, (some "extern"), false, false⟩)⟩,
  ⟨"cosf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "cosf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__cosf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__cosf", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinf", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sinf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sinf", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"coshf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "coshf", none, (some "extern"), false, false⟩)⟩,
  ⟨"coshf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "coshf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__coshf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__coshf", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sinhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sinhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tanhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tanhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"acoshf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acoshf", none, (some "extern"), false, false⟩)⟩,
  ⟨"acoshf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acoshf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__acoshf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__acoshf", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__asinhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__asinhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atanhf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__atanhf", none, (some "extern"), false, false⟩)⟩,
  ⟨"expf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expf", none, (some "extern"), false, false⟩)⟩,
  ⟨"expf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__expf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__expf", none, (some "extern"), false, false⟩)⟩,
  ⟨"frexpf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "frexpf", none, (some "extern"), false, false⟩)⟩,
  ⟨"frexpf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "frexpf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__frexpf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "__frexpf", none, (some "extern"), false, false⟩)⟩,
  ⟨"ldexpf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "ldexpf", none, (some "extern"), false, false⟩)⟩,
  ⟨"ldexpf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "ldexpf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ldexpf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__ldexpf", none, (some "extern"), false, false⟩)⟩,
  ⟨"logf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logf", none, (some "extern"), false, false⟩)⟩,
  ⟨"logf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__logf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__logf", none, (some "extern"), false, false⟩)⟩,
  ⟨"log10f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log10f", none, (some "extern"), false, false⟩)⟩,
  ⟨"log10f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log10f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log10f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log10f", none, (some "extern"), false, false⟩)⟩,
  ⟨"modff", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.ptr (.float .float))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "modff", none, (some "extern"), false, false⟩)⟩,
  ⟨"modff", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.ptr (.float .float))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "modff", none, (some "extern"), false, false⟩)⟩,
  ⟨"__modff", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.ptr (.float .float))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "__modff", none, (some "extern"), false, false⟩)⟩,
  ⟨"expm1f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expm1f", none, (some "extern"), false, false⟩)⟩,
  ⟨"expm1f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expm1f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__expm1f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__expm1f", none, (some "extern"), false, false⟩)⟩,
  ⟨"log1pf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log1pf", none, (some "extern"), false, false⟩)⟩,
  ⟨"log1pf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log1pf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log1pf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log1pf", none, (some "extern"), false, false⟩)⟩,
  ⟨"logbf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logbf", none, (some "extern"), false, false⟩)⟩,
  ⟨"logbf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logbf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__logbf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__logbf", none, (some "extern"), false, false⟩)⟩,
  ⟨"exp2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "exp2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"exp2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "exp2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__exp2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__exp2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"log2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"log2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log2f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log2f", none, (some "extern"), false, false⟩)⟩,
  ⟨"powf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "powf", none, (some "extern"), false, false⟩)⟩,
  ⟨"powf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "powf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__powf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__powf", none, (some "extern"), false, false⟩)⟩,
  ⟨"sqrtf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sqrtf", none, (some "extern"), false, false⟩)⟩,
  ⟨"sqrtf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sqrtf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sqrtf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sqrtf", none, (some "extern"), false, false⟩)⟩,
  ⟨"hypotf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "hypotf", none, (some "extern"), false, false⟩)⟩,
  ⟨"hypotf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "hypotf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__hypotf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__hypotf", none, (some "extern"), false, false⟩)⟩,
  ⟨"cbrtf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "cbrtf", none, (some "extern"), false, false⟩)⟩,
  ⟨"cbrtf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "cbrtf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__cbrtf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__cbrtf", none, (some "extern"), false, false⟩)⟩,
  ⟨"ceilf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "ceilf", none, (some "extern"), false, false⟩)⟩,
  ⟨"ceilf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "ceilf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ceilf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__ceilf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fabsf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fabsf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fabsf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fabsf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fabsf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__fabsf", none, (some "extern"), false, false⟩)⟩,
  ⟨"floorf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "floorf", none, (some "extern"), false, false⟩)⟩,
  ⟨"floorf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "floorf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__floorf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__floorf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmodf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fmodf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmodf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fmodf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmodf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__fmodf", none, (some "extern"), false, false⟩)⟩,
  ⟨"isinff", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 177⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "isinff", none, (some "extern"), false, false⟩)⟩,
  ⟨"finitef", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 183⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "finitef", none, (some "extern"), false, false⟩)⟩,
  ⟨"finitef", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 183⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "finitef", none, (some "extern"), false, false⟩)⟩,
  ⟨"dremf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 187⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "dremf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__dremf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 187⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__dremf", none, (some "extern"), false, false⟩)⟩,
  ⟨"significandf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 191⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "significandf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__significandf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 191⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__significandf", none, (some "extern"), false, false⟩)⟩,
  ⟨"copysignf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "copysignf", none, (some "extern"), false, false⟩)⟩,
  ⟨"copysignf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "copysignf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__copysignf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__copysignf", none, (some "extern"), false, false⟩)⟩,
  ⟨"nanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure], "nanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"nanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.builtin, .pure, .nothrow], "nanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow], "__nanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"isnanf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 213⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "isnanf", none, (some "extern"), false, false⟩)⟩,
  ⟨"j0f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 220⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "j0f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__j0f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 220⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__j0f", none, (some "extern"), false, false⟩)⟩,
  ⟨"j1f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 221⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "j1f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__j1f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 221⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__j1f", none, (some "extern"), false, false⟩)⟩,
  ⟨"jnf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 222⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.int .int .signed), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "jnf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__jnf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 222⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.int .int .signed), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__jnf", none, (some "extern"), false, false⟩)⟩,
  ⟨"y0f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 223⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "y0f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__y0f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 223⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__y0f", none, (some "extern"), false, false⟩)⟩,
  ⟨"y1f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 224⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "y1f", none, (some "extern"), false, false⟩)⟩,
  ⟨"__y1f", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 224⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__y1f", none, (some "extern"), false, false⟩)⟩,
  ⟨"ynf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 225⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.int .int .signed), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "ynf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ynf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 225⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.int .int .signed), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__ynf", none, (some "extern"), false, false⟩)⟩,
  ⟨"erff", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erff", none, (some "extern"), false, false⟩)⟩,
  ⟨"erff", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erff", none, (some "extern"), false, false⟩)⟩,
  ⟨"__erff", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__erff", none, (some "extern"), false, false⟩)⟩,
  ⟨"erfcf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erfcf", none, (some "extern"), false, false⟩)⟩,
  ⟨"erfcf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erfcf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__erfcf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__erfcf", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgammaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lgammaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgammaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lgammaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lgammaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lgammaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"tgammaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tgammaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"tgammaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tgammaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tgammaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tgammaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"gammaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 244⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "gammaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__gammaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 244⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__gammaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgammaf_r", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 252⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "lgammaf_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lgammaf_r", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 252⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "__lgammaf_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"rintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "rintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"rintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "rintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__rintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__rintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"nextafterf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nextafterf", none, (some "extern"), false, false⟩)⟩,
  ⟨"nextafterf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nextafterf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nextafterf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__nextafterf", none, (some "extern"), false, false⟩)⟩,
  ⟨"nexttowardf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nexttowardf", none, (some "extern"), false, false⟩)⟩,
  ⟨"nexttowardf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nexttowardf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nexttowardf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__nexttowardf", none, (some "extern"), false, false⟩)⟩,
  ⟨"remainderf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "remainderf", none, (some "extern"), false, false⟩)⟩,
  ⟨"remainderf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "remainderf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__remainderf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__remainderf", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbnf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalbnf", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbnf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalbnf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalbnf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalbnf", none, (some "extern"), false, false⟩)⟩,
  ⟨"ilogbf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "ilogbf", none, (some "extern"), false, false⟩)⟩,
  ⟨"ilogbf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "ilogbf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ilogbf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__ilogbf", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalblnf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalblnf", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalblnf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalblnf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalblnf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalblnf", none, (some "extern"), false, false⟩)⟩,
  ⟨"nearbyintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "nearbyintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"nearbyintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "nearbyintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nearbyintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__nearbyintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"roundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "roundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"roundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "roundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__roundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__roundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"truncf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "truncf", none, (some "extern"), false, false⟩)⟩,
  ⟨"truncf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "truncf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__truncf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__truncf", none, (some "extern"), false, false⟩)⟩,
  ⟨"remquof", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "remquof", none, (some "extern"), false, false⟩)⟩,
  ⟨"remquof", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "remquof", none, (some "extern"), false, false⟩)⟩,
  ⟨"__remquof", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.nothrow], "__remquof", none, (some "extern"), false, false⟩)⟩,
  ⟨"lrintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lrintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"lrintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lrintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lrintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lrintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"llrintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llrintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"llrintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llrintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__llrintf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__llrintf", none, (some "extern"), false, false⟩)⟩,
  ⟨"lroundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lroundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"lroundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lroundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lroundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lroundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"llroundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llroundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"llroundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llroundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__llroundf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .float)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__llroundf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fdimf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fdimf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fdimf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fdimf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fdimf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__fdimf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmaxf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fmaxf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmaxf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fmaxf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmaxf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__fmaxf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fminf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fminf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fminf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fminf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fminf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__fminf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), true,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "fmaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "fmaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmaf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.nothrow], "__fmaf", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 435⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "scalbf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalbf", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 435⟩), false,
    (.function
      ⟨(.ok ⟨(.float .float), [(.float .float), (.float .float)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalbf", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fpclassifyl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 20⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__fpclassifyl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__signbitl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 24⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__signbitl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__isinfl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 29⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__isinfl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__finitel", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 33⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "__finitel", none, (some "extern"), false, false⟩)⟩,
  ⟨"__finitel", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 33⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "__finitel", none, (some "extern"), false, false⟩)⟩,
  ⟨"__isnanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 37⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__isnanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__iseqsigl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 41⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__iseqsigl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__issignalingl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h", 44⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__issignalingl", none, (some "extern"), false, false⟩)⟩,
  ⟨"acosl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acosl", none, (some "extern"), false, false⟩)⟩,
  ⟨"acosl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acosl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__acosl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 53⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__acosl", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinl", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__asinl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 55⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__asinl", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 57⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__atanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"atan2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "atan2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"atan2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "atan2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atan2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 59⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__atan2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"cosl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "cosl", none, (some "extern"), false, false⟩)⟩,
  ⟨"cosl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "cosl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__cosl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 62⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__cosl", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinl", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sinl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 64⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sinl", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 66⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"coshl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "coshl", none, (some "extern"), false, false⟩)⟩,
  ⟨"coshl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "coshl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__coshl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 71⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__coshl", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"sinhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sinhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sinhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 73⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sinhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"tanhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tanhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tanhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 75⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tanhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"acoshl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acoshl", none, (some "extern"), false, false⟩)⟩,
  ⟨"acoshl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "acoshl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__acoshl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 85⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__acoshl", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"asinhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "asinhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__asinhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 87⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__asinhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"atanhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "atanhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__atanhl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 89⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__atanhl", none, (some "extern"), false, false⟩)⟩,
  ⟨"expl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expl", none, (some "extern"), false, false⟩)⟩,
  ⟨"expl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__expl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 95⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__expl", none, (some "extern"), false, false⟩)⟩,
  ⟨"frexpl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "frexpl", none, (some "extern"), false, false⟩)⟩,
  ⟨"frexpl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "frexpl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__frexpl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 98⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "__frexpl", none, (some "extern"), false, false⟩)⟩,
  ⟨"ldexpl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "ldexpl", none, (some "extern"), false, false⟩)⟩,
  ⟨"ldexpl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "ldexpl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ldexpl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 101⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__ldexpl", none, (some "extern"), false, false⟩)⟩,
  ⟨"logl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logl", none, (some "extern"), false, false⟩)⟩,
  ⟨"logl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__logl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 104⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__logl", none, (some "extern"), false, false⟩)⟩,
  ⟨"log10l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log10l", none, (some "extern"), false, false⟩)⟩,
  ⟨"log10l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log10l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log10l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 107⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log10l", none, (some "extern"), false, false⟩)⟩,
  ⟨"modfl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.ptr (.float .longDouble))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "modfl", none, (some "extern"), false, false⟩)⟩,
  ⟨"modfl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.ptr (.float .longDouble))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "modfl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__modfl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 110⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.ptr (.float .longDouble))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow, .nonnull], "__modfl", none, (some "extern"), false, false⟩)⟩,
  ⟨"expm1l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expm1l", none, (some "extern"), false, false⟩)⟩,
  ⟨"expm1l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "expm1l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__expm1l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 119⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__expm1l", none, (some "extern"), false, false⟩)⟩,
  ⟨"log1pl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log1pl", none, (some "extern"), false, false⟩)⟩,
  ⟨"log1pl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log1pl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log1pl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 122⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log1pl", none, (some "extern"), false, false⟩)⟩,
  ⟨"logbl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logbl", none, (some "extern"), false, false⟩)⟩,
  ⟨"logbl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "logbl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__logbl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 125⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__logbl", none, (some "extern"), false, false⟩)⟩,
  ⟨"exp2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "exp2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"exp2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "exp2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__exp2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 130⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__exp2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"log2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"log2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "log2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__log2l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 133⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__log2l", none, (some "extern"), false, false⟩)⟩,
  ⟨"powl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "powl", none, (some "extern"), false, false⟩)⟩,
  ⟨"powl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "powl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__powl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 140⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__powl", none, (some "extern"), false, false⟩)⟩,
  ⟨"sqrtl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sqrtl", none, (some "extern"), false, false⟩)⟩,
  ⟨"sqrtl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "sqrtl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__sqrtl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 143⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__sqrtl", none, (some "extern"), false, false⟩)⟩,
  ⟨"hypotl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "hypotl", none, (some "extern"), false, false⟩)⟩,
  ⟨"hypotl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "hypotl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__hypotl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 147⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__hypotl", none, (some "extern"), false, false⟩)⟩,
  ⟨"cbrtl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "cbrtl", none, (some "extern"), false, false⟩)⟩,
  ⟨"cbrtl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "cbrtl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__cbrtl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 152⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__cbrtl", none, (some "extern"), false, false⟩)⟩,
  ⟨"ceill", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "ceill", none, (some "extern"), false, false⟩)⟩,
  ⟨"ceill", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "ceill", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ceill", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 159⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__ceill", none, (some "extern"), false, false⟩)⟩,
  ⟨"fabsl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fabsl", none, (some "extern"), false, false⟩)⟩,
  ⟨"fabsl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fabsl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fabsl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 162⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__fabsl", none, (some "extern"), false, false⟩)⟩,
  ⟨"floorl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "floorl", none, (some "extern"), false, false⟩)⟩,
  ⟨"floorl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "floorl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__floorl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 165⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__floorl", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmodl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fmodl", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmodl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fmodl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmodl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 168⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__fmodl", none, (some "extern"), false, false⟩)⟩,
  ⟨"isinfl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 177⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "isinfl", none, (some "extern"), false, false⟩)⟩,
  ⟨"finitel", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 183⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "finitel", none, (some "extern"), false, false⟩)⟩,
  ⟨"finitel", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 183⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "finitel", none, (some "extern"), false, false⟩)⟩,
  ⟨"dreml", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 187⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "dreml", none, (some "extern"), false, false⟩)⟩,
  ⟨"__dreml", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 187⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__dreml", none, (some "extern"), false, false⟩)⟩,
  ⟨"significandl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 191⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "significandl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__significandl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 191⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__significandl", none, (some "extern"), false, false⟩)⟩,
  ⟨"copysignl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "copysignl", none, (some "extern"), false, false⟩)⟩,
  ⟨"copysignl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "copysignl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__copysignl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 198⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__copysignl", none, (some "extern"), false, false⟩)⟩,
  ⟨"nanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure], "nanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"nanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.builtin, .pure, .nothrow], "nanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 203⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.nothrow], "__nanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"isnanl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 213⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "isnanl", none, (some "extern"), false, false⟩)⟩,
  ⟨"j0l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 220⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "j0l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__j0l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 220⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__j0l", none, (some "extern"), false, false⟩)⟩,
  ⟨"j1l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 221⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "j1l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__j1l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 221⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__j1l", none, (some "extern"), false, false⟩)⟩,
  ⟨"jnl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 222⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.int .int .signed), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "jnl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__jnl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 222⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.int .int .signed), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__jnl", none, (some "extern"), false, false⟩)⟩,
  ⟨"y0l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 223⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "y0l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__y0l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 223⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__y0l", none, (some "extern"), false, false⟩)⟩,
  ⟨"y1l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 224⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "y1l", none, (some "extern"), false, false⟩)⟩,
  ⟨"__y1l", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 224⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__y1l", none, (some "extern"), false, false⟩)⟩,
  ⟨"ynl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 225⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.int .int .signed), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "ynl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ynl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 225⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.int .int .signed), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__ynl", none, (some "extern"), false, false⟩)⟩,
  ⟨"erfl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erfl", none, (some "extern"), false, false⟩)⟩,
  ⟨"erfl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erfl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__erfl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 231⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__erfl", none, (some "extern"), false, false⟩)⟩,
  ⟨"erfcl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erfcl", none, (some "extern"), false, false⟩)⟩,
  ⟨"erfcl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "erfcl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__erfcl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 232⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__erfcl", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgammal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lgammal", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgammal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lgammal", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lgammal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 233⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lgammal", none, (some "extern"), false, false⟩)⟩,
  ⟨"tgammal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tgammal", none, (some "extern"), false, false⟩)⟩,
  ⟨"tgammal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "tgammal", none, (some "extern"), false, false⟩)⟩,
  ⟨"__tgammal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 238⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__tgammal", none, (some "extern"), false, false⟩)⟩,
  ⟨"gammal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 244⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "gammal", none, (some "extern"), false, false⟩)⟩,
  ⟨"__gammal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 244⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__gammal", none, (some "extern"), false, false⟩)⟩,
  ⟨"lgammal_r", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 252⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "lgammal_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lgammal_r", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 252⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[], []]]⟩),
       false, .c, [.nothrow], "__lgammal_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"rintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "rintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"rintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "rintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__rintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 259⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__rintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"nextafterl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nextafterl", none, (some "extern"), false, false⟩)⟩,
  ⟨"nextafterl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nextafterl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nextafterl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 262⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__nextafterl", none, (some "extern"), false, false⟩)⟩,
  ⟨"nexttowardl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nexttowardl", none, (some "extern"), false, false⟩)⟩,
  ⟨"nexttowardl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "nexttowardl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nexttowardl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 264⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__nexttowardl", none, (some "extern"), false, false⟩)⟩,
  ⟨"remainderl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "remainderl", none, (some "extern"), false, false⟩)⟩,
  ⟨"remainderl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "remainderl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__remainderl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 275⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__remainderl", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbnl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalbnl", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbnl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalbnl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalbnl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 279⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalbnl", none, (some "extern"), false, false⟩)⟩,
  ⟨"ilogbl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "ilogbl", none, (some "extern"), false, false⟩)⟩,
  ⟨"ilogbl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "ilogbl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__ilogbl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 283⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__ilogbl", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalblnl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalblnl", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalblnl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "scalblnl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalblnl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 293⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalblnl", none, (some "extern"), false, false⟩)⟩,
  ⟨"nearbyintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "nearbyintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"nearbyintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "nearbyintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__nearbyintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 297⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__nearbyintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"roundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "roundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"roundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "roundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__roundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 301⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__roundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"truncl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "truncl", none, (some "extern"), false, false⟩)⟩,
  ⟨"truncl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "truncl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__truncl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 305⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow, .const], "__truncl", none, (some "extern"), false, false⟩)⟩,
  ⟨"remquol", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "remquol", none, (some "extern"), false, false⟩)⟩,
  ⟨"remquol", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.builtin, .nothrow], "remquol", none, (some "extern"), false, false⟩)⟩,
  ⟨"__remquol", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 310⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[]], [[]], [[], []]]⟩),
       false, .c, [.nothrow], "__remquol", none, (some "extern"), false, false⟩)⟩,
  ⟨"lrintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lrintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"lrintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lrintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lrintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 317⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lrintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"llrintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llrintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"llrintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llrintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__llrintl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 319⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__llrintl", none, (some "extern"), false, false⟩)⟩,
  ⟨"lroundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lroundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"lroundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "lroundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__lroundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 323⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__lroundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"llroundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), true,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llroundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"llroundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "llroundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__llroundl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 325⟩), false,
    (.function
      ⟨(.ok ⟨(.int .longLong .signed), [(.float .longDouble)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.nothrow], "__llroundl", none, (some "extern"), false, false⟩)⟩,
  ⟨"fdiml", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fdiml", none, (some "extern"), false, false⟩)⟩,
  ⟨"fdiml", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow], "fdiml", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fdiml", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 329⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__fdiml", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmaxl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fmaxl", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmaxl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fmaxl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmaxl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 333⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__fmaxl", none, (some "extern"), false, false⟩)⟩,
  ⟨"fminl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fminl", none, (some "extern"), false, false⟩)⟩,
  ⟨"fminl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .const], "fminl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fminl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 336⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow, .const], "__fminl", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), true,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "fmal", none, (some "extern"), false, false⟩)⟩,
  ⟨"fmal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.builtin, .const, .nothrow], "fmal", none, (some "extern"), false, false⟩)⟩,
  ⟨"__fmal", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 340⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [.nothrow], "__fmal", none, (some "extern"), false, false⟩)⟩,
  ⟨"scalbl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 435⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "scalbl", none, (some "extern"), false, false⟩)⟩,
  ⟨"__scalbl", .function, (some ⟨"/usr/include/x86_64-linux-gnu/bits/mathcalls.h", 435⟩), false,
    (.function
      ⟨(.ok ⟨(.float .longDouble), [(.float .longDouble), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "__scalbl", none, (some "extern"), false, false⟩)⟩,
  ⟨"signgam", .variable, (some ⟨"/usr/include/math.h", 854⟩), false,
    (.variable (.ok (.int .int .signed)) (some "extern"))⟩,
  ⟨"", .enum, (some ⟨"/usr/include/math.h", 934⟩), false,
    (.tag true)⟩]

end Silmaril.Data.Layout.Header.Import.Pinned

end
