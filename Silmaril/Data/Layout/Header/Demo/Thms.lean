module

public import Silmaril.Data.Layout.Header.Demo.Defs

/-!
# The layout demo header's aggregates under System V x86-64 and Microsoft x64

`demo.h` (`demoH`) reads to seven tag definitions (`demoEnv_tags`). For each, and for each data
model (System V x86-64: policy `.sysv`, `sysvX86_64`; Microsoft x64, clang's MSVC-compatible
record layout: policy `.ms`, `msX64`), one theorem states its bit-level layout
(`layoutOf … = some (slots, shape)`) and one the library's padding counts
(`paddingOf … = some (paddingBytes, paddingBits)`). Each is one kernel evaluation
(`decide +kernel`) of the reader on the header text and of `bitLayout`; none is refused under
either model.

These are the theorems the explorer's Headers tab links from `demo.h`'s layout tables
(`tools/header-pages`), after checking that each statement is exactly about `demoEnv`, the tag
and the data model of the table it is linked from, and that its right-hand side is the value
the tab shows.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Demo

open Silmaril.Data.Layout

/-- The tags `demo.h` defines, in the order the reader completes them. -/
theorem demoEnv_tags :
    demoEnv.map (fun d => (d.kind, d.tag)) =
      [(.struct, "rec"), (.struct, "pt"), (.union, "word"), (.struct, "node"),
        (.struct, "pair"), (.struct, "vec2"), (.struct, "mixed")] := by decide +kernel

/-! ## `struct rec { char c; unsigned flags : 3; unsigned mode : 5; long n; int x; double d; }` -/

/-- System V: the bit-fields share `c`'s `unsigned` unit (bits 8 and 11); `long` is 8 bytes. -/
theorem rec_sysv :
    layoutOf .sysv sysvX86_64 demoEnv .struct "rec" =
      some ([⟨"c", 0, 8⟩, ⟨"flags", 8, 3⟩, ⟨"mode", 11, 5⟩, ⟨"n", 64, 64⟩, ⟨"x", 128, 32⟩,
        ⟨"d", 192, 64⟩], ⟨32, 8⟩) := by decide +kernel

theorem rec_sysv_padding : paddingOf .sysv sysvX86_64 demoEnv .struct "rec" = some (10, 80) := by
  decide +kernel

/-- Microsoft x64: the bit-fields open a new `unsigned` unit at byte 4; `long` is 4 bytes. -/
theorem rec_ms :
    layoutOf .ms msX64 demoEnv .struct "rec" =
      some ([⟨"c", 0, 8⟩, ⟨"flags", 32, 3⟩, ⟨"mode", 35, 5⟩, ⟨"n", 64, 32⟩, ⟨"x", 96, 32⟩,
        ⟨"d", 128, 64⟩], ⟨24, 8⟩) := by decide +kernel

theorem rec_ms_padding : paddingOf .ms msX64 demoEnv .struct "rec" = some (6, 48) := by
  decide +kernel

/-! ## `struct pt { char tag; long v; short s; }` -/

theorem pt_sysv :
    layoutOf .sysv sysvX86_64 demoEnv .struct "pt" =
      some ([⟨"tag", 0, 8⟩, ⟨"v", 64, 64⟩, ⟨"s", 128, 16⟩], ⟨24, 8⟩) := by decide +kernel

theorem pt_sysv_padding : paddingOf .sysv sysvX86_64 demoEnv .struct "pt" = some (13, 104) := by
  decide +kernel

theorem pt_ms :
    layoutOf .ms msX64 demoEnv .struct "pt" =
      some ([⟨"tag", 0, 8⟩, ⟨"v", 32, 32⟩, ⟨"s", 64, 16⟩], ⟨12, 4⟩) := by decide +kernel

theorem pt_ms_padding : paddingOf .ms msX64 demoEnv .struct "pt" = some (5, 40) := by
  decide +kernel

/-! ## `union word { u32 u; float f; unsigned char b[4]; }` -/

theorem word_sysv :
    layoutOf .sysv sysvX86_64 demoEnv .union "word" =
      some ([⟨"u", 0, 32⟩, ⟨"f", 0, 32⟩, ⟨"b", 0, 32⟩], ⟨4, 4⟩) := by decide +kernel

theorem word_sysv_padding : paddingOf .sysv sysvX86_64 demoEnv .union "word" = some (0, 0) := by
  decide +kernel

theorem word_ms :
    layoutOf .ms msX64 demoEnv .union "word" =
      some ([⟨"u", 0, 32⟩, ⟨"f", 0, 32⟩, ⟨"b", 0, 32⟩], ⟨4, 4⟩) := by decide +kernel

theorem word_ms_padding : paddingOf .ms msX64 demoEnv .union "word" = some (0, 0) := by
  decide +kernel

/-! ## `struct node { struct pt where; struct node *next; u32 count; }` -/

theorem node_sysv :
    layoutOf .sysv sysvX86_64 demoEnv .struct "node" =
      some ([⟨"where", 0, 192⟩, ⟨"next", 192, 64⟩, ⟨"count", 256, 32⟩], ⟨40, 8⟩) := by
  decide +kernel

theorem node_sysv_padding : paddingOf .sysv sysvX86_64 demoEnv .struct "node" = some (4, 32) := by
  decide +kernel

theorem node_ms :
    layoutOf .ms msX64 demoEnv .struct "node" =
      some ([⟨"where", 0, 96⟩, ⟨"next", 128, 64⟩, ⟨"count", 192, 32⟩], ⟨32, 8⟩) := by
  decide +kernel

theorem node_ms_padding : paddingOf .ms msX64 demoEnv .struct "node" = some (8, 64) := by
  decide +kernel

/-! ## `struct pair { long a; long b; }` -/

theorem pair_sysv :
    layoutOf .sysv sysvX86_64 demoEnv .struct "pair" =
      some ([⟨"a", 0, 64⟩, ⟨"b", 64, 64⟩], ⟨16, 8⟩) := by decide +kernel

theorem pair_sysv_padding : paddingOf .sysv sysvX86_64 demoEnv .struct "pair" = some (0, 0) := by
  decide +kernel

theorem pair_ms :
    layoutOf .ms msX64 demoEnv .struct "pair" =
      some ([⟨"a", 0, 32⟩, ⟨"b", 32, 32⟩], ⟨8, 4⟩) := by decide +kernel

theorem pair_ms_padding : paddingOf .ms msX64 demoEnv .struct "pair" = some (0, 0) := by
  decide +kernel

/-! ## `struct vec2 { double x; double y; }` -/

theorem vec2_sysv :
    layoutOf .sysv sysvX86_64 demoEnv .struct "vec2" =
      some ([⟨"x", 0, 64⟩, ⟨"y", 64, 64⟩], ⟨16, 8⟩) := by decide +kernel

theorem vec2_sysv_padding : paddingOf .sysv sysvX86_64 demoEnv .struct "vec2" = some (0, 0) := by
  decide +kernel

theorem vec2_ms :
    layoutOf .ms msX64 demoEnv .struct "vec2" =
      some ([⟨"x", 0, 64⟩, ⟨"y", 64, 64⟩], ⟨16, 8⟩) := by decide +kernel

theorem vec2_ms_padding : paddingOf .ms msX64 demoEnv .struct "vec2" = some (0, 0) := by
  decide +kernel

/-! ## `struct mixed { long a; double b; }` -/

theorem mixed_sysv :
    layoutOf .sysv sysvX86_64 demoEnv .struct "mixed" =
      some ([⟨"a", 0, 64⟩, ⟨"b", 64, 64⟩], ⟨16, 8⟩) := by decide +kernel

theorem mixed_sysv_padding :
    paddingOf .sysv sysvX86_64 demoEnv .struct "mixed" = some (0, 0) := by decide +kernel

/-- Microsoft x64: the 4-byte `long` leaves bytes 4–7 as padding before the `double`. -/
theorem mixed_ms :
    layoutOf .ms msX64 demoEnv .struct "mixed" =
      some ([⟨"a", 0, 32⟩, ⟨"b", 64, 64⟩], ⟨16, 8⟩) := by decide +kernel

theorem mixed_ms_padding : paddingOf .ms msX64 demoEnv .struct "mixed" = some (4, 32) := by
  decide +kernel

end Silmaril.Data.Layout.Header.Demo

end
