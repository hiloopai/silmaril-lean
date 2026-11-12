module

public import Silmaril.Data.Layout.Command.Defs

/-!
# Worked example: one C source, five targets, five Clang cross-checks

`clang/message.c` is laid out under every data model of `Silmaril.Data.Layout`, and each
layout is compared with a Clang 19 record-layout dump for the matching triple, normalized by
`tools/c-layout/clang_record_layouts.py` into `clang/message.<target>.json`. See
docs/projects/c-record-layout.md for the walkthrough and the trust boundary.

The interesting differences: `union Value` holds a `long double`, which is 16 bytes aligned
to 16 on x86-64, AArch64, RISC-V and wasm32 but 12 bytes aligned to 4 on i386, where `double`
and `long long` are also only 4-aligned inside records.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Examples

open Silmaril.Data.Layout.Record

c_layout Demo for Target.x86_64 Target.i386 Target.aarch64 Target.riscv64 Target.wasm32 :=
  include_str "clang/message.c"

c_layout_import Demo.x86_64 from "clang/message.x86_64.json"
c_layout_import Demo.i386 from "clang/message.i386.json"
c_layout_import Demo.aarch64 from "clang/message.aarch64.json"
c_layout_import Demo.riscv64 from "clang/message.riscv64.json"
c_layout_import Demo.wasm32 from "clang/message.wasm32.json"

/-! ## What the declarations say

`Demo.source` is the C text, `Demo.Header.decl` the source description of `struct Header`,
`Demo.ast` all four, `Demo.parses` the parse certificate; `Demo.i386.Header` is the i386
layout of `struct Header`, `Demo.i386.resolves` and `Demo.i386.wf` its certificates, and
`Demo.i386.observed.matches` the comparison with Clang. -/

/-- `offsetof(struct Message, value)` is 48 on x86-64 and 36 on i386. -/
example : Demo.x86_64.Message.entries.map (·.offset) = [0, 48, 64] := by decide
example : Demo.i386.Message.entries.map (·.offset) = [0, 36, 48] := by decide

/-- The union is as large as its largest member, rounded up to its alignment. -/
example : (Demo.x86_64.Value.size, Demo.x86_64.Value.align) = (16, 16) := rfl
example : (Demo.i386.Value.size, Demo.i386.Value.align) = (12, 4) := rfl

/-- The resolved layouts keep the source's kinds, names and member names. -/
example : Demo.wasm32.layout.map layoutNames = Demo.ast.map declNames :=
  resolveEnv_names Demo.wasm32.resolves

/-- The chain, for one target. -/
example : Interchange.CrossChecked Demo.source Demo.i386.target
    Demo.i386.observed.report :=
  Demo.i386.observed.crossChecked

end Silmaril.Data.Layout.Examples
