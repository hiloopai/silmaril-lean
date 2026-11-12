# Data layouts and separation-logic fragments

Reusable, ISA-independent representations of low-level data under `Silmaril/Data/`.
The definitions are executable. The library states its goals as `def Task.x : Prop`
and proves them in the `Thms` headers. The one goal left open is `Task.bitfieldLayout`.

## C object layout (`Silmaril.Data.Layout`)

| Module | Contents |
| --- | --- |
| `Layout.Defs` | C types (`CTy`, `Field`, `Decl`, `Env`) with structs and unions by tag, arrays, pointers, typedefs, enums, `_Alignas`; data models `sysvX86_64`, `aapcs64`, `rv64Lp64`, `i386Ilp32`, `wasm32`; `layoutTy`, `declLayout`, `resolve` |
| `Layout.Thms`, `Layout.Resolve.Thms` | well-formed placements (members disjoint, in bounds, aligned); nested designators lie inside the object and are aligned |
| `Layout.Bytes.Defs`, `.Thms` | `ByteMem` memories, integer codecs, field lenses (`readField`/`writeField`), padding specifications and frame lemmas |
| `Layout.Bytes.Process.Defs`, `Layout.Bytes.Wasm.Defs` | `ByteMem` instances for `Silmaril.Process.ByteMemory` and Wasm linear memories (`ByteArray`) |
| `Layout.Bits.Defs`, `.Thms` | bit-level specifications of integer members (`WordSpec`: zero, reserved, flag and value items) |
| `Layout.Render.Defs` | rendering declarations as C source and as `gdb ptype` output |
| `Layout.Glibc.Malloc.Defs`, `.Thms` | glibc 2.39 `malloc_chunk`, `malloc_state`, `malloc_par` and tcache structures; their computed layouts equal transcribed DWARF tables on x86-64, AArch64, RISC-V 64 and i386, and render as `gdb ptype` prints them |

Bit-fields are rejected by `layoutTy` for now (`Task.bitfieldLayout`).

[C record layouts from source text](c-record-layout.md) adds a parser for C `struct`/`union`
text with a soundness proof, type-free resolved layouts (`Layout.Record`), a versioned JSON
schema for observed compiler layouts with a Clang adapter (`Layout.Interchange`), and the
`c_layout` command that produces named declarations and certificates.

## Fragments (`Silmaril.Data.Cells`, `SepList`, `Bitmap`, `BoundaryTag`)

`Cells` is a small separation-logic kernel over an abstract byte memory: cells,
fragments, a decidable holds relation and a one-lemma frame rule. On top of it:

* `SepList`: list segments, sentinel doubly linked lists, rings, singly linked lists
  with a pointer encoding (identity or glibc safe-linking), skip lists; insertion and
  removal lemmas.
* `Bitmap`: bitmaps of words as fragments (glibc's `binmap`), with set and clear.
* `BoundaryTag`: heaps tiled by blocks with size headers and boundary tags
  (dlmalloc/ptmalloc style), with split and merge steps.

## Build

```sh
lake build --wfail Silmaril.Data.Layout.Glibc.Malloc.Thms Silmaril.Data.SepList.Thms \
  Silmaril.Data.Bitmap.Thms Silmaril.Data.BoundaryTag.Thms Silmaril.Data.Layout.Resolve.Thms \
  Silmaril.Data.Layout.Bytes.Process.Defs Silmaril.Data.Layout.Bytes.Wasm.Defs
```
