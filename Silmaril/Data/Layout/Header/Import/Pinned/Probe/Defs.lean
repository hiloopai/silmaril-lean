module

public import Silmaril.Data.Layout.Header.Import.Defs

/-! # `probe.json`: the pinned artifact and its import (generated: do not edit)

Written by `examples/headers/emit.lean` and compared byte for byte by
`examples/headers/recipe.sh --check`. `probeJson` and `probeProv` are the committed
`examples/headers/clang/probe.json` and `.prov`; `probe` is their import, and `Probe.entries`
the entries that import gives, as a literal. `import_probe` (`Pinned.Probe.Thms`) proves in the
kernel that they are equal; other theorems compute on the literal, never on the JSON.

The provenance, verbatim. It changes whenever the JSON does, so this module changes with it
and is rebuilt: Lake does not track the files `include_str` reads.

```text
artifact: probe.json
image: silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9
clang: Debian clang version 18.1.8 (++20240731024826+3b5b5c1ec4a3-1~exp1~20240731144843.145)
target: x86_64-unknown-linux-gnu
std: gnu11
cwd: .
command: clang -target x86_64-unknown-linux-gnu -x c -std=gnu11 -ffreestanding -fno-builtin probe.h -Xclang -ast-dump=json -fsyntax-only
filter: python3 -I filter.py probe.h
filter-sha256: f7234d7a7bbf7792b9482c54edfb2d2a4ee1cb9f1c192a769e8cf0f34613241f
input: probe.h d69db957a83d0583a2307778114ed337a67bdfdc925e7941aa4c3297882b14a3
json-sha256: 6c6325672964fb9ee3cb2f635f306c7ac47d3c38119103923ed0d9437bed9d2a
json-bytes: 7113
```
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

/-- `examples/headers/clang/probe.json`. -/
def probeJson : String :=
  include_str "../../../../../../../examples/headers/clang/probe.json"
/-- `examples/headers/clang/probe.prov`. -/
def probeProv : String :=
  include_str "../../../../../../../examples/headers/clang/probe.prov"
/-- The probe header `examples/headers/probe/probe.h`, as clang reads it: the import of `probeJson`. Noncomputable: the kernel computes it (in
`import_probe`), and compiled code uses the literal `Probe.entries`. Compiling it would parse the
JSON when a program that imports this module starts, with recursion as deep as the JSON is long. -/
noncomputable def probe : Imported := .ofJson (.parse probeProv) probeJson

/-- The entries of `probe`, as a literal. -/
def Probe.entries : List Entry := [
  ⟨"u32", .typedef, (some ⟨"probe.h", 6⟩), false,
    (.typedef (.ok (.int .int .unsigned)))⟩,
  ⟨"pair", .struct, (some ⟨"probe.h", 7⟩), false,
    (.tag true)⟩,
  ⟨"pair_t", .typedef, (some ⟨"probe.h", 7⟩), false,
    (.typedef (.ok (.struct "pair")))⟩,
  ⟨"fwd", .struct, (some ⟨"probe.h", 8⟩), false,
    (.tag false)⟩,
  ⟨"u", .union, (some ⟨"probe.h", 9⟩), false,
    (.tag true)⟩,
  ⟨"color", .enum, (some ⟨"probe.h", 10⟩), false,
    (.tag true)⟩,
  ⟨"cmp_fn", .typedef, (some ⟨"probe.h", 11⟩), false,
    (.typedef (.unsupported "function or function-pointer type: outside CProto"))⟩,
  ⟨"vec4", .typedef, (some ⟨"probe.h", 12⟩), false,
    (.typedef (.ok (.array (.typedef "u32" (.int .int .unsigned)) 4)))⟩,
  ⟨"counter", .variable, (some ⟨"probe.h", 13⟩), false,
    (.variable (.ok (.int .int .signed)) (some "extern"))⟩,
  ⟨"names", .variable, (some ⟨"probe.h", 14⟩), false,
    (.variable (.unsupported "incomplete array type") (some "extern"))⟩,
  ⟨"plain", .function, (some ⟨"probe.h", 15⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed), (.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "plain", none, none, false, false⟩)⟩,
  ⟨"knr", .function, (some ⟨"probe.h", 16⟩), false,
    (.function
      ⟨(.unsupported "no prototype (K&R f()): outside CProto"), none,
       false, .c, [], "knr", none, none, false, false⟩)⟩,
  ⟨"vf", .function, (some ⟨"probe.h", 17⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.ptr (.int .char .plain))], true⟩), (some ⟨[[]], [[["const"], []]]⟩),
       true, .c, [.format], "vf", none, none, false, false⟩)⟩,
  ⟨"die", .function, (some ⟨"probe.h", 18⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.ptr (.int .char .plain))], false⟩), (some ⟨[[]], [[["const"], []]]⟩),
       false, .c, [.noreturn], "die", none, none, false, false⟩)⟩,
  ⟨"die2", .function, (some ⟨"probe.h", 19⟩), false,
    (.function
      ⟨(.ok ⟨.void, [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [.noreturn], "die2", none, none, false, false⟩)⟩,
  ⟨"nn", .function, (some ⟨"probe.h", 20⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr .void), [(.ptr .void), (.ptr .void)], false⟩), (some ⟨[[], []], [[[], []], [[], []]]⟩),
       false, .c, [.nonnull], "nn", none, none, false, false⟩)⟩,
  ⟨"old", .function, (some ⟨"probe.h", 21⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.deprecated], "old", none, none, false, false⟩)⟩,
  ⟨"hidden", .function, (some ⟨"probe.h", 22⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [(.visibility "hidden")], "hidden", none, none, false, false⟩)⟩,
  ⟨"renamed", .function, (some ⟨"probe.h", 23⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [.asmLabel], "renamed_v2", (some "renamed_v2"), none, false, false⟩)⟩,
  ⟨"win", .function, (some ⟨"probe.h", 24⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed), (.int .int .signed)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .msAbi, [], "win", none, none, false, false⟩)⟩,
  ⟨"sysv", .function, (some ⟨"probe.h", 25⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .sysvAbi, [], "sysv", none, none, false, false⟩)⟩,
  ⟨"rc", .function, (some ⟨"probe.h", 26⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .regcall, [], "rc", none, none, false, false⟩)⟩,
  ⟨"by_value", .function, (some ⟨"probe.h", 27⟩), false,
    (.function
      ⟨(.ok ⟨(.typedef "pair_t" (.struct "pair")), [(.typedef "pair_t" (.struct "pair"))], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "by_value", none, none, false, false⟩)⟩,
  ⟨"fp", .function, (some ⟨"probe.h", 28⟩), false,
    (.function
      ⟨(.ok ⟨(.float .double), [(.float .float), (.float .longDouble)], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "fp", none, none, false, false⟩)⟩,
  ⟨"flag", .function, (some ⟨"probe.h", 29⟩), false,
    (.function
      ⟨(.ok ⟨.bool, [], false⟩), (some ⟨[[]], []⟩),
       false, .c, [], "flag", none, none, false, false⟩)⟩,
  ⟨"sort", .function, (some ⟨"probe.h", 30⟩), false,
    (.function
      ⟨(.unsupported "parameter 3: typedef cmp_fn: function or function-pointer type: outside CProto"), (some ⟨[[]], [[[], []], [[]], [[]]]⟩),
       false, .c, [], "sort", none, none, false, false⟩)⟩,
  ⟨"arr", .function, (some ⟨"probe.h", 31⟩), false,
    (.function
      ⟨(.ok ⟨.void, [(.ptr (.int .int .signed)), (.ptr (.int .int .signed))], false⟩), (some ⟨[[]], [[[], []], [[], []]]⟩),
       false, .c, [], "arr", none, none, false, false⟩)⟩,
  ⟨"mk", .function, (some ⟨"probe.h", 32⟩), false,
    (.function
      ⟨(.ok ⟨(.ptr (.struct "fwd")), [], false⟩), (some ⟨[[], []], []⟩),
       false, .c, [], "mk", none, none, false, false⟩)⟩,
  ⟨"paint", .function, (some ⟨"probe.h", 33⟩), false,
    (.function
      ⟨(.ok ⟨(.enum "color" none), [(.enum "color" none)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "paint", none, none, false, false⟩)⟩,
  ⟨"inl", .function, (some ⟨"probe.h", 34⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed)], false⟩), (some ⟨[[]], [[[]]]⟩),
       false, .c, [], "inl", none, (some "static"), true, true⟩)⟩,
  ⟨"plain", .function, (some ⟨"probe.h", 35⟩), false,
    (.function
      ⟨(.ok ⟨(.int .int .signed), [(.int .int .signed), (.typedef "u32" (.int .int .unsigned))], false⟩), (some ⟨[[]], [[[]], [[]]]⟩),
       false, .c, [], "plain", none, none, false, false⟩)⟩]

end Silmaril.Data.Layout.Header.Import.Pinned

end
