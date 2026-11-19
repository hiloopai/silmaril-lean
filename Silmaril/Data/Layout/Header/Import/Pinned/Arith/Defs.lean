module

public import Silmaril.Data.Layout.Header.Import.Defs

/-! # `arith.json`: the pinned artifact and its import (generated: do not edit)

Written by `examples/headers/emit.lean` and compared byte for byte by
`examples/headers/recipe.sh --check`. `arithJson` and `arithProv` are the committed
`examples/headers/clang/arith.json` and `.prov`; `arith` is their import, and `Arith.entries`
the entries that import gives, as a literal. `import_arith` (`Pinned.Arith.Thms`) proves in the
kernel that they are equal; other theorems compute on the literal, never on the JSON.

The provenance, verbatim. It changes whenever the JSON does, so this module changes with it
and is rebuilt: Lake does not track the files `include_str` reads.

```text
artifact: arith.json
image: silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9
clang: Debian clang version 18.1.8 (++20240731024826+3b5b5c1ec4a3-1~exp1~20240731144843.145)
target: x86_64-unknown-linux-gnu
std: gnu11
cwd: 01-leaf-arith
command: clang -target x86_64-unknown-linux-gnu -x c -std=gnu11 -ffreestanding -fno-builtin -I../common arith.h -Xclang -ast-dump=json -fsyntax-only
include: ../common
filter: python3 -I filter.py arith.h ../common/rt.h
filter-sha256: f7234d7a7bbf7792b9482c54edfb2d2a4ee1cb9f1c192a769e8cf0f34613241f
input: arith.h 61eb45a5756b10db4d130c18d9e34130d1ad06ef359cdeb31527b1983f55ebd0
input: ../common/rt.h bad2f2ad76bea06a400ad4ecfa9571627468a16077aabffe497468254b8a2174
json-sha256: 29504cc856844187f9e8135636df614e1cda8246dcac26a431e3b5a3f2f3907d
json-bytes: 7748
```
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

/-- `examples/headers/clang/arith.json`. -/
def arithJson : String :=
  include_str "../../../../../../../examples/headers/clang/arith.json"
/-- `examples/headers/clang/arith.prov`. -/
def arithProv : String :=
  include_str "../../../../../../../examples/headers/clang/arith.prov"
/-- `arith.h` and the `rt.h` it includes, as clang reads it: the import of `arithJson`. Noncomputable: the kernel computes it (in
`import_arith`), and compiled code uses the literal `Arith.entries`. Compiling it would parse the
JSON when a program that imports this module starts, with recursion as deep as the JSON is long. -/
noncomputable def arith : Imported := .ofJson (.parse arithProv) arithJson

/-- The entries of `arith`, as a literal. -/
def Arith.entries : List Entry := [
  ⟨"u8", .typedef, (some ⟨"../common/rt.h", 12⟩), false,
    (.typedef (.ok (.int .char .unsigned)))⟩,
  ⟨"u16", .typedef, (some ⟨"../common/rt.h", 13⟩), false,
    (.typedef (.ok (.int .short .unsigned)))⟩,
  ⟨"u32", .typedef, (some ⟨"../common/rt.h", 14⟩), false,
    (.typedef (.ok (.int .int .unsigned)))⟩,
  ⟨"u64", .typedef, (some ⟨"../common/rt.h", 15⟩), false,
    (.typedef (.ok (.int .longLong .unsigned)))⟩,
  ⟨"usize", .typedef, (some ⟨"../common/rt.h", 16⟩), false,
    (.typedef (.ok (.int .long .unsigned)))⟩,
  ⟨"isize", .typedef, (some ⟨"../common/rt.h", 17⟩), false,
    (.typedef (.ok (.int .long .signed)))⟩,
  ⟨"sc3", .function, (some ⟨"../common/rt.h", 19⟩), false,
    (.function
      ⟨(.ok ⟨(.int .long .signed), [(.int .long .signed), (.int .long .signed), (.int .long .signed), (.int .long .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]], [[]]]⟩),
       false, .c, [], "sc3", none, none, false, false⟩)⟩,
  ⟨"rt_write", .function, (some ⟨"../common/rt.h", 20⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "isize" (.int .long .signed)), [(.int .int .signed), (.ptr .void), (.typedef "usize" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [["const"], []], [[]]]⟩),
       false, .c, [], "rt_write", none, none, false, false⟩)⟩,
  ⟨"rt_read", .function, (some ⟨"../common/rt.h", 21⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "isize" (.int .long .signed)), [(.int .int .signed), (.ptr .void), (.typedef "usize" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[[]], [[], []], [[]]]⟩),
       false, .c, [], "rt_read", none, none, false, false⟩)⟩,
  ⟨"rt_puts", .function, (some ⟨"../common/rt.h", 22⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [], "rt_puts", none, none, false, false⟩)⟩,
  ⟨"rt_put_hex", .function, (some ⟨"../common/rt.h", 23⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "rt_put_hex", none, none, false, false⟩)⟩,
  ⟨"rt_check", .function, (some ⟨"../common/rt.h", 24⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.int .int .signed), (.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[[]], [["const"], []]]⟩),
       false, .c, [], "rt_check", none, none, false, false⟩)⟩,
  ⟨"rt_failures", .function, (some ⟨"../common/rt.h", 25⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [], "rt_failures", none, none, false, false⟩)⟩,
  ⟨"rt_finish", .function, (some ⟨"../common/rt.h", 26⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [], "rt_finish", none, none, false, false⟩)⟩,
  ⟨"memcpy", .function, (some ⟨"../common/rt.h", 28⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void), (.typedef "usize" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], ["restrict"]], [["const"], ["restrict"]], [[]]]⟩),
       false, .c, [], "memcpy", none, none, false, false⟩)⟩,
  ⟨"memset", .function, (some ⟨"../common/rt.h", 29⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.int .int .signed), (.typedef "usize" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], []], [[]], [[]]]⟩),
       false, .c, [], "memset", none, none, false, false⟩)⟩,
  ⟨"memmove", .function, (some ⟨"../common/rt.h", 30⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void), (.typedef "usize" (.int .long .unsigned))], false⟩), (some ⟨[[], []], [[[], []], [["const"], []], [[]]]⟩),
       false, .c, [], "memmove", none, none, false, false⟩)⟩,
  ⟨"memcmp", .function, (some ⟨"../common/rt.h", 31⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr .void), (.ptr .void), (.typedef "usize" (.int .long .unsigned))], false⟩), (some ⟨[[]], [[["const"], []], [["const"], []], [[]]]⟩),
       false, .c, [], "memcmp", none, none, false, false⟩)⟩,
  ⟨"strlen", .function, (some ⟨"../common/rt.h", 32⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "usize" (.int .long .unsigned)), [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [], "strlen", none, none, false, false⟩)⟩,
  ⟨"popcount32", .function, (some ⟨"arith.h", 6⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "u32" (.int .int .unsigned)), [(.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "popcount32", none, none, false, false⟩)⟩,
  ⟨"gcd_u32", .function, (some ⟨"arith.h", 7⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "u32" (.int .int .unsigned)), [(.typedef "u32" (.int .int .unsigned)), (.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "gcd_u32", none, none, false, false⟩)⟩,
  ⟨"clamp_i32", .function, (some ⟨"arith.h", 8⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed), (.int .int .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]], [[]]]⟩),
       false, .c, [], "clamp_i32", none, none, false, false⟩)⟩,
  ⟨"isqrt_u32", .function, (some ⟨"arith.h", 9⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "u32" (.int .int .unsigned)), [(.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "isqrt_u32", none, none, false, false⟩)⟩,
  ⟨"sat_add_u32", .function, (some ⟨"arith.h", 10⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "u32" (.int .int .unsigned)), [(.typedef "u32" (.int .int .unsigned)), (.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "sat_add_u32", none, none, false, false⟩)⟩,
  ⟨"bswap32_manual", .function, (some ⟨"arith.h", 11⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "u32" (.int .int .unsigned)), [(.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "bswap32_manual", none, none, false, false⟩)⟩,
  ⟨"ilog2_u32", .function, (some ⟨"arith.h", 12⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "ilog2_u32", none, none, false, false⟩)⟩]

end Silmaril.Data.Layout.Header.Import.Pinned

end
