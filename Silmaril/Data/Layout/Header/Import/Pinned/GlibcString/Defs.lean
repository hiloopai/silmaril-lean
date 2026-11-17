module

public import Silmaril.Data.Layout.Header.Import.Defs

/-! # `glibc-string.json`: the pinned artifact and its import (generated: do not edit)

Written by `examples/headers/emit.lean` and compared byte for byte by
`examples/headers/recipe.sh --check`. `glibcStringJson` and `glibcStringProv` are the committed
`examples/headers/clang/glibc-string.json` and `.prov`; `glibcString` is their import, and `GlibcString.entries`
the entries that import gives, as a literal. `import_glibcString` (`Pinned.GlibcString.Thms`) proves in the
kernel that they are equal; other theorems compute on the literal, never on the JSON.

The provenance, verbatim. It changes whenever the JSON does, so this module changes with it
and is rebuilt: Lake does not track the files `include_str` reads.

```text
artifact: glibc-string.json
image: silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9
clang: Debian clang version 18.1.8 (++20240731024826+3b5b5c1ec4a3-1~exp1~20240731144843.145)
target: x86_64-unknown-linux-gnu
std: gnu11
cwd: .
command: clang -target x86_64-unknown-linux-gnu -x c -std=gnu11 /usr/include/string.h -Xclang -ast-dump=json -fsyntax-only
filter: python3 -I filter.py /usr/include/string.h
filter-sha256: f7234d7a7bbf7792b9482c54edfb2d2a4ee1cb9f1c192a769e8cf0f34613241f
input: /usr/include/string.h aa84f9ec0e15576219ff099be4ed2bd8ec5e23122a89f1d223bfbc3335f851fa (in the image)
json-sha256: ffdce3a8b55ada683a2bdd3ebbf80b4ec273cff034a4f27a741895eafea8622d
json-bytes: 33403
```
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

/-- `examples/headers/clang/glibc-string.json`. -/
def glibcStringJson : String :=
  include_str "../../../../../../../examples/headers/clang/glibc-string.json"
/-- `examples/headers/clang/glibc-string.prov`. -/
def glibcStringProv : String :=
  include_str "../../../../../../../examples/headers/clang/glibc-string.prov"
/-- glibc's `string.h`, hosted, as clang reads it: the import of `glibcStringJson`. Noncomputable: the kernel computes it (in
`import_glibcString`), and compiled code uses the literal `GlibcString.entries`. Compiling it would parse the
JSON when a program that imports this module starts, with recursion as deep as the JSON is long. -/
noncomputable def glibcString : Imported := .ofJson (.parse glibcStringProv) glibcStringJson

/-- The entries of `glibcString`, as a literal. -/
def GlibcString.entries : List Entry := [
  ⟨"memcpy", .function, (some ⟨"/usr/include/string.h", 43⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin], "memcpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"memcpy", .function, (some ⟨"/usr/include/string.h", 43⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "memcpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"memmove", .function, (some ⟨"/usr/include/string.h", 47⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin], "memmove", none, (some "extern"), false, false⟩)⟩,
  ⟨"memmove", .function, (some ⟨"/usr/include/string.h", 47⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "memmove", none, (some "extern"), false, false⟩)⟩,
  ⟨"memccpy", .function, (some ⟨"/usr/include/string.h", 54⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void), (.int .int .signed), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[], []], [["const"], []], [[]], [[]]]⟩),
       false, .c, [.builtin], "memccpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"memccpy", .function, (some ⟨"/usr/include/string.h", 54⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void), (.int .int .signed), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "memccpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"memset", .function, (some ⟨"/usr/include/string.h", 61⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.int .int .signed), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[], []], [[]], [[]]]⟩),
       false, .c, [.builtin], "memset", none, (some "extern"), false, false⟩)⟩,
  ⟨"memset", .function, (some ⟨"/usr/include/string.h", 61⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.int .int .signed), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], []], [[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "memset", none, (some "extern"), false, false⟩)⟩,
  ⟨"memcmp", .function, (some ⟨"/usr/include/string.h", 64⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr .void), (.ptr .void), (.int .long .unsigned)], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin], "memcmp", none, (some "extern"), false, false⟩)⟩,
  ⟨"memcmp", .function, (some ⟨"/usr/include/string.h", 64⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr .void), (.ptr .void), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "memcmp", none, (some "extern"), false, false⟩)⟩,
  ⟨"__memcmpeq", .function, (some ⟨"/usr/include/string.h", 80⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr .void), (.ptr .void), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []], [[]]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "__memcmpeq", none, (some "extern"), false, false⟩)⟩,
  ⟨"memchr", .function, (some ⟨"/usr/include/string.h", 107⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.int .int .signed), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[["const"], []], [[]], [[]]]⟩),
       false, .c, [.builtin], "memchr", none, (some "extern"), false, false⟩)⟩,
  ⟨"memchr", .function, (some ⟨"/usr/include/string.h", 107⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.int .int .signed), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[["const"], []], [[]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "memchr", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcpy", .function, (some ⟨"/usr/include/string.h", 141⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], []], [["const"], []]]⟩),
       false, .c, [.builtin], "strcpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcpy", .function, (some ⟨"/usr/include/string.h", 141⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strcpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"strncpy", .function, (some ⟨"/usr/include/string.h", 144⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin], "strncpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"strncpy", .function, (some ⟨"/usr/include/string.h", 144⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strncpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcat", .function, (some ⟨"/usr/include/string.h", 149⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], []], [["const"], []]]⟩),
       false, .c, [.builtin], "strcat", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcat", .function, (some ⟨"/usr/include/string.h", 149⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strcat", none, (some "extern"), false, false⟩)⟩,
  ⟨"strncat", .function, (some ⟨"/usr/include/string.h", 152⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin], "strncat", none, (some "extern"), false, false⟩)⟩,
  ⟨"strncat", .function, (some ⟨"/usr/include/string.h", 152⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strncat", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcmp", .function, (some ⟨"/usr/include/string.h", 156⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin], "strcmp", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcmp", .function, (some ⟨"/usr/include/string.h", 156⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strcmp", none, (some "extern"), false, false⟩)⟩,
  ⟨"strncmp", .function, (some ⟨"/usr/include/string.h", 159⟩), true,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.int .long .unsigned)], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin], "strncmp", none, (some "extern"), false, false⟩)⟩,
  ⟨"strncmp", .function, (some ⟨"/usr/include/string.h", 159⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strncmp", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcoll", .function, (some ⟨"/usr/include/string.h", 163⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "strcoll", none, (some "extern"), false, false⟩)⟩,
  ⟨"strxfrm", .function, (some ⟨"/usr/include/string.h", 166⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.int .long .unsigned)], false⟩), (some ⟨[[]], [[[], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin], "strxfrm", none, (some "extern"), false, false⟩)⟩,
  ⟨"strxfrm", .function, (some ⟨"/usr/include/string.h", 166⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strxfrm", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcoll_l", .function, (some ⟨"/usr/include/string.h", 175⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.typedef "locale_t" (.ptr (.struct "__locale_struct")))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []], [[]]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "strcoll_l", none, (some "extern"), false, false⟩)⟩,
  ⟨"strxfrm_l", .function, (some ⟨"/usr/include/string.h", 179⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "size_t" (.int .long .unsigned)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned)), (.typedef "locale_t" (.ptr (.struct "__locale_struct")))], false⟩), (some ⟨[[]], [[[], []], [["const"], []], [[]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "strxfrm_l", none, (some "extern"), false, false⟩)⟩,
  ⟨"strdup", .function, (some ⟨"/usr/include/string.h", 187⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[["const"], []]]⟩),
       false, .c, [.builtin], "strdup", none, (some "extern"), false, false⟩)⟩,
  ⟨"strdup", .function, (some ⟨"/usr/include/string.h", 187⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .restrict, .nonnull], "strdup", none, (some "extern"), false, false⟩)⟩,
  ⟨"strndup", .function, (some ⟨"/usr/include/string.h", 195⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[["const"], []], [[]]]⟩),
       false, .c, [.builtin], "strndup", none, (some "extern"), false, false⟩)⟩,
  ⟨"strndup", .function, (some ⟨"/usr/include/string.h", 195⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[["const"], []], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .restrict, .nonnull], "strndup", none, (some "extern"), false, false⟩)⟩,
  ⟨"strchr", .function, (some ⟨"/usr/include/string.h", 246⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[], []], [[["const"], []], [[]]]⟩),
       false, .c, [.builtin], "strchr", none, (some "extern"), false, false⟩)⟩,
  ⟨"strchr", .function, (some ⟨"/usr/include/string.h", 246⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[], []], [[["const"], []], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strchr", none, (some "extern"), false, false⟩)⟩,
  ⟨"strrchr", .function, (some ⟨"/usr/include/string.h", 273⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[], []], [[["const"], []], [[]]]⟩),
       false, .c, [.builtin], "strrchr", none, (some "extern"), false, false⟩)⟩,
  ⟨"strrchr", .function, (some ⟨"/usr/include/string.h", 273⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.int .int .signed)], false⟩), (some ⟨[[], []], [[["const"], []], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strrchr", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcspn", .function, (some ⟨"/usr/include/string.h", 293⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin], "strcspn", none, (some "extern"), false, false⟩)⟩,
  ⟨"strcspn", .function, (some ⟨"/usr/include/string.h", 293⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strcspn", none, (some "extern"), false, false⟩)⟩,
  ⟨"strspn", .function, (some ⟨"/usr/include/string.h", 297⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin], "strspn", none, (some "extern"), false, false⟩)⟩,
  ⟨"strspn", .function, (some ⟨"/usr/include/string.h", 297⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strspn", none, (some "extern"), false, false⟩)⟩,
  ⟨"strpbrk", .function, (some ⟨"/usr/include/string.h", 323⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin], "strpbrk", none, (some "extern"), false, false⟩)⟩,
  ⟨"strpbrk", .function, (some ⟨"/usr/include/string.h", 323⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strpbrk", none, (some "extern"), false, false⟩)⟩,
  ⟨"strstr", .function, (some ⟨"/usr/include/string.h", 350⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin], "strstr", none, (some "extern"), false, false⟩)⟩,
  ⟨"strstr", .function, (some ⟨"/usr/include/string.h", 350⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[["const"], []], [["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strstr", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtok", .function, (some ⟨"/usr/include/string.h", 356⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], []], [["const"], []]]⟩),
       false, .c, [.builtin], "strtok", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtok", .function, (some ⟨"/usr/include/string.h", 356⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "strtok", none, (some "extern"), false, false⟩)⟩,
  ⟨"__strtok_r", .function, (some ⟨"/usr/include/string.h", 361⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[], [], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "__strtok_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"strtok_r", .function, (some ⟨"/usr/include/string.h", 366⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.ptr (.ptr (.int .char .plain)))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[], [], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "strtok_r", none, (some "extern"), false, false⟩)⟩,
  ⟨"strlen", .function, (some ⟨"/usr/include/string.h", 407⟩), true,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.builtin], "strlen", none, (some "extern"), false, false⟩)⟩,
  ⟨"strlen", .function, (some ⟨"/usr/include/string.h", 407⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .unsigned), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.builtin, .nothrow, .pure, .nonnull], "strlen", none, (some "extern"), false, false⟩)⟩,
  ⟨"strnlen", .function, (some ⟨"/usr/include/string.h", 413⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "size_t" (.int .long .unsigned)), [(.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[["const"], []], [[]]]⟩),
       false, .c, [.nothrow, .pure, .nonnull], "strnlen", none, (some "extern"), false, false⟩)⟩,
  ⟨"strerror", .function, (some ⟨"/usr/include/string.h", 419⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.int .int .signed)], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.builtin], "strerror", none, (some "extern"), false, false⟩)⟩,
  ⟨"strerror", .function, (some ⟨"/usr/include/string.h", 419⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.int .int .signed)], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.builtin, .nothrow], "strerror", none, (some "extern"), false, false⟩)⟩,
  ⟨"strerror_r", .function, (some ⟨"/usr/include/string.h", 432⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [[], []], [[]]]⟩),
       false, .c, [.asmLabel, .nothrow, .nonnull], "__xpg_strerror_r", (some "__xpg_strerror_r"), (some "extern"), false, false⟩)⟩,
  ⟨"strerror_l", .function, (some ⟨"/usr/include/string.h", 458⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.int .int .signed), (.typedef "locale_t" (.ptr (.struct "__locale_struct")))], false⟩), (some ⟨[[], []], [[[]], [[]]]⟩),
       false, .c, [.nothrow], "strerror_l", none, (some "extern"), false, false⟩)⟩,
  ⟨"explicit_bzero", .function, (some ⟨"/usr/include/string.h", 466⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.ptr .void), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[], []], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "explicit_bzero", none, (some "extern"), false, false⟩)⟩,
  ⟨"strsep", .function, (some ⟨"/usr/include/string.h", 471⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.ptr (.int .char .plain))), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], [], ["restrict"]], [["const"], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "strsep", none, (some "extern"), false, false⟩)⟩,
  ⟨"strsignal", .function, (some ⟨"/usr/include/string.h", 478⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.int .int .signed)], false⟩), (some ⟨[[], []], [[[]]]⟩),
       false, .c, [.nothrow], "strsignal", none, (some "extern"), false, false⟩)⟩,
  ⟨"__stpcpy", .function, (some ⟨"/usr/include/string.h", 489⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]]]⟩),
       false, .c, [.nothrow, .nonnull], "__stpcpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"stpcpy", .function, (some ⟨"/usr/include/string.h", 491⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], []], [["const"], []]]⟩),
       false, .c, [.builtin], "stpcpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"stpcpy", .function, (some ⟨"/usr/include/string.h", 491⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "stpcpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"__stpncpy", .function, (some ⟨"/usr/include/string.h", 496⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.nothrow, .nonnull], "__stpncpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"stpncpy", .function, (some ⟨"/usr/include/string.h", 499⟩), true,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.int .long .unsigned)], false⟩), (some ⟨[[], []], [[[], []], [["const"], []], [[]]]⟩),
       false, .c, [.builtin], "stpncpy", none, (some "extern"), false, false⟩)⟩,
  ⟨"stpncpy", .function, (some ⟨"/usr/include/string.h", 499⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.int .char .plain)), [(.ptr (.int .char .plain)), (.ptr (.int .char .plain)), (.typedef "size_t" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [.builtin, .nothrow, .nonnull], "stpncpy", none, (some "extern"), false, false⟩)⟩]

end Silmaril.Data.Layout.Header.Import.Pinned

end
