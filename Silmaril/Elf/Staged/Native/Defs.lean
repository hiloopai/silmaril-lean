module

public import Silmaril.Elf.Staged.Leaf.Thms
public import Silmaril.Prelude.Trust.Policy.Defs
-- Native runs interpret these functions while elaborating, so their code is loaded as `meta`.
public meta import Silmaril.Elf.Staged.Leaf.Thms

/-! # ELF leaves under the trust policy

Each leaf (`Silmaril.Elf.Staged.Leaf`) has **two checkers** for **one proposition**:

* the **native side** `Native.<leaf> b c` runs the leaf on the `ByteArray` of a file
  (`fastRead`), registered as `elf.<leaf>` with no kernel fallback (the kernel would decode the
  `ByteArray` one byte at a time);
* the **kernel side** `Kernel.<leaf> x c` runs the same leaf on core's kernel bytes `x`
  (`Silmaril.KBytes.readLE`), registered as `elf.<leaf>.kernel` with a kernel fallback.

`Native.<leaf>_sound` and `Kernel.<leaf>_sound x.wf x.toByteArray_eq` conclude the same
`P (blobOf ⟨raw⟩) c`; the kernel bytes are tied to the raw bytes by `x.toByteArray = raw`
(`kbytes_def … of_include`). A leaf theorem pairs them with the trust framework's `edge_pair`:

```
theorem layout : LayoutIs F L := by
  edge_pair (native := Native.layout_sound (raw := helloRaw) (L := L))
    (kernel := Kernel.layout_sound hello.wf hello.toByteArray_eq (L := L))
```

The native side runs when the policy allows `elf.<leaf>` in the module; otherwise the kernel
checks the kernel side, which never runs natively. Errors and `false` propagate. The `default`
set holds `elf.layout`; the other leaves run natively under `local`.
-/

@[expose] public section

namespace Silmaril.Elf.Staged

open Silmaril.Formats.ELF (SectionHeader Rela)

namespace Native

/-- `elf.layout` on a `ByteArray`. -/
def layout (b : Silmaril.Formats.Bytes) (L : Layout) : Bool := Leaf.layout.native b L
/-- `elf.body` on a `ByteArray`. -/
def body (b : Silmaril.Formats.Bytes) (c : Layout × SectionHeader × Body) : Bool :=
  Leaf.body.native b c
/-- `elf.loader` on a `ByteArray`. -/
def loader (b : Silmaril.Formats.Bytes) (c : Layout × Loader) : Bool := Leaf.loader.native b c
/-- `elf.rela` on a `ByteArray`. -/
def rela (b : Silmaril.Formats.Bytes) (c : Nat × Nat × List Rela) : Bool := Leaf.rela.native b c
/-- `elf.tiles` on a `ByteArray`. -/
def tiles (b : Silmaril.Formats.Bytes) (c : Nat × List Nat) : Bool := Leaf.tiles.native b c
/-- `elf.tiles.x86` on a `ByteArray`. -/
def tilesX86 (b : Silmaril.Formats.Bytes) (c : Nat × List Nat) : Bool := Leaf.tilesX86.native b c
/-- `elf.symbols.byName` on a `ByteArray`. -/
def byName (b : Silmaril.Formats.Bytes) (x : Symbols.ByName) : Bool := Leaf.byName.native b x
/-- `elf.symbols.byAddr` on a `ByteArray`. -/
def byAddr (b : Silmaril.Formats.Bytes) (x : Symbols.ByAddr) : Bool := Leaf.byAddr.native b x

variable {raw : ByteArray}

theorem layout_sound {L : Layout} (h : layout ⟨raw⟩ L = true) : LayoutIs (blobOf ⟨raw⟩) L :=
  Leaf.layout.of_native h
theorem body_sound {c : Layout × SectionHeader × Body} (h : body ⟨raw⟩ c = true) :
    BodyIs (blobOf ⟨raw⟩) c.1 c.2.1 c.2.2 :=
  Leaf.body.of_native h
theorem loader_sound {c : Layout × Loader} (h : loader ⟨raw⟩ c = true) :
    LoaderIs (blobOf ⟨raw⟩) c.1 c.2 :=
  Leaf.loader.of_native h
theorem rela_sound {c : Nat × Nat × List Rela} (h : rela ⟨raw⟩ c = true) :
    EntriesAt (blobOf ⟨raw⟩) Parse.rela c.1 24 c.2.1 c.2.2 :=
  Leaf.rela.of_native h
theorem tiles_sound {c : Nat × List Nat} (h : tiles ⟨raw⟩ c = true) :
    TilesAt (blobOf ⟨raw⟩) (fun _ _ => true) c.1 c.2 :=
  Leaf.tiles.of_native h
theorem tilesX86_sound {c : Nat × List Nat} (h : tilesX86 ⟨raw⟩ c = true) :
    TilesAt (blobOf ⟨raw⟩) x86Ok c.1 c.2 :=
  Leaf.tilesX86.of_native h
theorem byName_sound {x : Symbols.ByName} (h : byName ⟨raw⟩ x = true) :
    x.sorted = true ∧ x.Sound (blobOf ⟨raw⟩) :=
  Leaf.byName.of_native h
theorem byAddr_sound {x : Symbols.ByAddr} (h : byAddr ⟨raw⟩ x = true) :
    x.sorted = true ∧ x.Sound (blobOf ⟨raw⟩) :=
  Leaf.byAddr.of_native h

end Native

namespace Kernel

/-- `elf.layout` on kernel bytes. -/
def layout (x : Silmaril.KBytes) (L : Layout) : Bool := Leaf.layout.kbytes x L
/-- `elf.body` on kernel bytes. -/
def body (x : Silmaril.KBytes) (c : Layout × SectionHeader × Body) : Bool := Leaf.body.kbytes x c
/-- `elf.loader` on kernel bytes. -/
def loader (x : Silmaril.KBytes) (c : Layout × Loader) : Bool := Leaf.loader.kbytes x c
/-- `elf.rela` on kernel bytes. -/
def rela (x : Silmaril.KBytes) (c : Nat × Nat × List Rela) : Bool := Leaf.rela.kbytes x c
/-- `elf.tiles` on kernel bytes. -/
def tiles (x : Silmaril.KBytes) (c : Nat × List Nat) : Bool := Leaf.tiles.kbytes x c
/-- `elf.tiles.x86` on kernel bytes. -/
def tilesX86 (x : Silmaril.KBytes) (c : Nat × List Nat) : Bool := Leaf.tilesX86.kbytes x c
/-- `elf.symbols.byName` on kernel bytes. -/
def byName (x : Silmaril.KBytes) (s : Symbols.ByName) : Bool := Leaf.byName.kbytes x s
/-- `elf.symbols.byAddr` on kernel bytes. -/
def byAddr (x : Silmaril.KBytes) (s : Symbols.ByAddr) : Bool := Leaf.byAddr.kbytes x s

variable {x : Silmaril.KBytes} {raw : ByteArray}

theorem layout_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {L : Layout}
    (h : layout x L = true) : LayoutIs (blobOf ⟨raw⟩) L :=
  Leaf.layout.of_kbytes hx hr h
theorem body_sound (hx : x.wf = true) (hr : x.toByteArray = raw)
    {c : Layout × SectionHeader × Body} (h : body x c = true) :
    BodyIs (blobOf ⟨raw⟩) c.1 c.2.1 c.2.2 :=
  Leaf.body.of_kbytes hx hr h
theorem loader_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {c : Layout × Loader}
    (h : loader x c = true) : LoaderIs (blobOf ⟨raw⟩) c.1 c.2 :=
  Leaf.loader.of_kbytes hx hr h
theorem rela_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {c : Nat × Nat × List Rela}
    (h : rela x c = true) : EntriesAt (blobOf ⟨raw⟩) Parse.rela c.1 24 c.2.1 c.2.2 :=
  Leaf.rela.of_kbytes hx hr h
theorem tiles_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {c : Nat × List Nat}
    (h : tiles x c = true) : TilesAt (blobOf ⟨raw⟩) (fun _ _ => true) c.1 c.2 :=
  Leaf.tiles.of_kbytes hx hr h
theorem tilesX86_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {c : Nat × List Nat}
    (h : tilesX86 x c = true) : TilesAt (blobOf ⟨raw⟩) x86Ok c.1 c.2 :=
  Leaf.tilesX86.of_kbytes hx hr h
theorem byName_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {s : Symbols.ByName}
    (h : byName x s = true) : s.sorted = true ∧ s.Sound (blobOf ⟨raw⟩) :=
  Leaf.byName.of_kbytes hx hr h
theorem byAddr_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {s : Symbols.ByAddr}
    (h : byAddr x s = true) : s.sorted = true ∧ s.Sound (blobOf ⟨raw⟩) :=
  Leaf.byAddr.of_kbytes hx hr h

end Kernel

end Silmaril.Elf.Staged

/-! ## Registrations -/

/-- The stage-1 layout of an ELF file, read natively from its `ByteArray` (`fastRead`). Trusts
the compiled reader and `Nat` arithmetic. No kernel fallback: the kernel checker reads
`Silmaril.KBytes` instead (`elf.layout.kernel`, paired by `edge_pair`). -/
native_decider elf.layout := Silmaril.Elf.Staged.Native.layout

/-- One section body, read natively. Trusts the compiled reader. No kernel fallback. -/
native_decider elf.body := Silmaril.Elf.Staged.Native.body

/-- The loader view, read natively. Trusts the compiled reader. No kernel fallback. -/
native_decider elf.loader := Silmaril.Elf.Staged.Native.loader

/-- A window of `RELA` entries, read natively. Trusts the compiled reader. No kernel fallback. -/
native_decider elf.rela := Silmaril.Elf.Staged.Native.rela

/-- Instruction tiles lie in the file, read natively. No kernel fallback. -/
native_decider elf.tiles := Silmaril.Elf.Staged.Native.tiles

/-- Instruction tiles each decode as one instruction of the local x86 model, natively. Trusts
the compiled decoder. No kernel fallback. -/
native_decider elf.tiles.x86 := Silmaril.Elf.Staged.Native.tilesX86

/-- A forward symbol index, checked natively. No kernel fallback. -/
native_decider elf.symbols.byName := Silmaril.Elf.Staged.Native.byName

/-- A reverse symbol map, checked natively. No kernel fallback. -/
native_decider elf.symbols.byAddr := Silmaril.Elf.Staged.Native.byAddr

/-! ## Kernel sides

Registered so that `edge_pair` can check them and record their uses. `edge_pair` runs a kernel
side only in the kernel (`decideEdge … (kernelOnly := true)`), whatever the policy allows. -/

/-- The stage-1 layout on kernel bytes (`KBytes.readLE`): a few big-number operations per read. -/
native_decider elf.layout.kernel := Silmaril.Elf.Staged.Kernel.layout with_kernel_fallback
/-- One section body on kernel bytes. -/
native_decider elf.body.kernel := Silmaril.Elf.Staged.Kernel.body with_kernel_fallback
/-- The loader view on kernel bytes. -/
native_decider elf.loader.kernel := Silmaril.Elf.Staged.Kernel.loader with_kernel_fallback
/-- A window of `RELA` entries on kernel bytes. -/
native_decider elf.rela.kernel := Silmaril.Elf.Staged.Kernel.rela with_kernel_fallback
/-- Instruction tiles in the file, on kernel bytes. -/
native_decider elf.tiles.kernel := Silmaril.Elf.Staged.Kernel.tiles with_kernel_fallback
/-- Instruction tiles through the local x86 model, on kernel bytes. -/
native_decider elf.tiles.x86.kernel := Silmaril.Elf.Staged.Kernel.tilesX86 with_kernel_fallback
/-- A forward symbol index on kernel bytes. -/
native_decider elf.symbols.byName.kernel := Silmaril.Elf.Staged.Kernel.byName with_kernel_fallback
/-- A reverse symbol map on kernel bytes. -/
native_decider elf.symbols.byAddr.kernel := Silmaril.Elf.Staged.Kernel.byAddr with_kernel_fallback
