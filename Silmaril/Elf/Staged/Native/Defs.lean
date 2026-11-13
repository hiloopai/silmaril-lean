module

public import Silmaril.Elf.Staged.Leaf.Thms
public import Silmaril.Prelude.Trust.Policy.Defs
-- Native runs interpret these functions while elaborating, so their code is loaded as `meta`.
public meta import Silmaril.Elf.Staged.Leaf.Thms

/-! # ELF leaves under the trust policy

Each leaf (`Silmaril.Elf.Staged.Leaf`) is one declared procedure (`Silmaril.Procedures.elf.*`,
a `Silmaril.Trust.ProcDecl`) with **two backends** for **one proposition**:

* **native**: `Native.<leaf> b c` runs the leaf on the `ByteArray` of a file (`fastRead`);
* **kernel**: `Kernel.<leaf> x c` runs the same leaf on core's kernel bytes `x`
  (`Silmaril.KBytes.readLE`), and is only ever checked by the kernel.

`Native.<leaf>_sound` and `Kernel.<leaf>_sound x.wf_true x.toByteArray_eq` conclude the same
`P (blobOf ⟨raw⟩) c`; the kernel bytes are tied to the raw bytes by `x.toByteArray = raw`
(`kbytes_def … of_include`). A leaf theorem is

```
theorem layout : LayoutIs F L := by
  sil_check elf.layout (native := Native.layout_sound (raw := helloRaw) (L := L))
    (kernel := Kernel.layout_sound hello.wf_true hello.toByteArray_eq (L := L))
```

The native backend runs when the policy allows `elf.layout` in the module; otherwise the kernel
checks the kernel backend. Errors and `false` propagate. Both modes record their use under the
one name. The `default` set holds `elf.layout`; the other leaves run natively under `local`.
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

/-! ## Procedure declarations

One semantic name per leaf (`Silmaril.Trust.ProcDecl`): the native backend reads the
`ByteArray` (compiled `fastRead`; trusts the Lean compiler and runtime), the kernel backend reads
kernel bytes and is only ever checked by the kernel. `sil_check` picks one by the policy. -/

/-- The stage-1 layout (`LayoutIs`): `elf.layout`. -/
def Silmaril.Procedures.elf.layout : Silmaril.Trust.ProcDecl where
  doc := "The stage-1 layout (LayoutIs). Native: compiled fastRead over the file's ByteArray (trusts the \
    compiler and runtime). Kernel: KBytes.readLE, checked by the kernel."
  native := some ⟨``Silmaril.Elf.Staged.Native.layout, ``Silmaril.Elf.Staged.Native.layout_sound⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Kernel.layout, ``Silmaril.Elf.Staged.Kernel.layout_sound⟩
  format := some `elf

/-- One section body (`BodyIs`): `elf.body`. -/
def Silmaril.Procedures.elf.body : Silmaril.Trust.ProcDecl where
  doc := "One section body (BodyIs). Native: compiled fastRead over the file's ByteArray (trusts the \
    compiler and runtime). Kernel: KBytes.readLE, checked by the kernel."
  native := some ⟨``Silmaril.Elf.Staged.Native.body, ``Silmaril.Elf.Staged.Native.body_sound⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Kernel.body, ``Silmaril.Elf.Staged.Kernel.body_sound⟩
  format := some `elf

/-- The loader view (`LoaderIs`): `elf.loader`. -/
def Silmaril.Procedures.elf.loader : Silmaril.Trust.ProcDecl where
  doc := "The loader view (LoaderIs). Native: compiled fastRead over the file's ByteArray (trusts the \
    compiler and runtime). Kernel: KBytes.readLE, checked by the kernel."
  native := some ⟨``Silmaril.Elf.Staged.Native.loader, ``Silmaril.Elf.Staged.Native.loader_sound⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Kernel.loader, ``Silmaril.Elf.Staged.Kernel.loader_sound⟩
  format := some `elf

/-- A window of `RELA` entries (`EntriesAt`): `elf.rela`. -/
def Silmaril.Procedures.elf.rela : Silmaril.Trust.ProcDecl where
  doc := "A window of RELA entries (EntriesAt). Native: compiled fastRead over the file's ByteArray (trusts the \
    compiler and runtime). Kernel: KBytes.readLE, checked by the kernel."
  native := some ⟨``Silmaril.Elf.Staged.Native.rela, ``Silmaril.Elf.Staged.Native.rela_sound⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Kernel.rela, ``Silmaril.Elf.Staged.Kernel.rela_sound⟩
  format := some `elf

/-- Instruction tiles lie in the file (`TilesAt`): `elf.tiles`. -/
def Silmaril.Procedures.elf.tiles : Silmaril.Trust.ProcDecl where
  doc := "Instruction tiles lie in the file (TilesAt). Native: compiled fastRead over the file's ByteArray (trusts the \
    compiler and runtime). Kernel: KBytes.readLE, checked by the kernel."
  native := some ⟨``Silmaril.Elf.Staged.Native.tiles, ``Silmaril.Elf.Staged.Native.tiles_sound⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Kernel.tiles, ``Silmaril.Elf.Staged.Kernel.tiles_sound⟩
  format := some `elf

/-- Instruction tiles each decode as one instruction of the local x86 model (`TilesAt … x86Ok`): `elf.tiles.x86`. -/
def Silmaril.Procedures.elf.tiles.x86 : Silmaril.Trust.ProcDecl where
  doc := "Instruction tiles each decode as one instruction of the local x86 model (TilesAt … x86Ok). Native: compiled fastRead over the file's ByteArray (trusts the \
    compiler and runtime). Kernel: KBytes.readLE, checked by the kernel."
  native := some ⟨``Silmaril.Elf.Staged.Native.tilesX86, ``Silmaril.Elf.Staged.Native.tilesX86_sound⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Kernel.tilesX86, ``Silmaril.Elf.Staged.Kernel.tilesX86_sound⟩
  format := some `elf

/-- A forward symbol index (`ByName.Sound`): `elf.symbols.byName`. -/
def Silmaril.Procedures.elf.symbols.byName : Silmaril.Trust.ProcDecl where
  doc := "A forward symbol index (ByName.Sound). Native: compiled fastRead over the file's ByteArray (trusts the \
    compiler and runtime). Kernel: KBytes.readLE, checked by the kernel."
  native := some ⟨``Silmaril.Elf.Staged.Native.byName, ``Silmaril.Elf.Staged.Native.byName_sound⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Kernel.byName, ``Silmaril.Elf.Staged.Kernel.byName_sound⟩
  format := some `elf

/-- A reverse symbol map (`ByAddr.Sound`): `elf.symbols.byAddr`. -/
def Silmaril.Procedures.elf.symbols.byAddr : Silmaril.Trust.ProcDecl where
  doc := "A reverse symbol map (ByAddr.Sound). Native: compiled fastRead over the file's ByteArray (trusts the \
    compiler and runtime). Kernel: KBytes.readLE, checked by the kernel."
  native := some ⟨``Silmaril.Elf.Staged.Native.byAddr, ``Silmaril.Elf.Staged.Native.byAddr_sound⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Kernel.byAddr, ``Silmaril.Elf.Staged.Kernel.byAddr_sound⟩
  format := some `elf
