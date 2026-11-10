module

public import Silmaril.Project.Shapes.X86.Defs
public import Silmaril.Project.Shapes.Elf.Thms
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.BlockCert9.Defs
import Silmaril.Proofs.Project.Shapes.X86
import Silmaril.X86.BlockCert9.Examples

/-! # Standard problem shapes: x86-64 functions (transfer lemmas)

* Along the model order `Open ⊑ Open9 ⊑ Str9` (each machine runs every run of the previous):
  `Contract.open9_of_open`, `Contract.str9_of_open9`, `Contract.str9_of_open`. A row solved on
  `contract.open` gives the rows on `contract.open9` and `contract.str9`.
* `ContractStrict.contract`: first-return correctness implies total correctness.
* `Nonvacuous.of_entered`: a spec whose entry is "code loaded, `rip` at a word" is not vacuous
  on `Open.isa` when the code fits below the top of the address space (a concrete witness
  state, `Silmaril.Proofs.Project.Shapes.X86`); `Nonvacuous.open9_of_open`,
  `Nonvacuous.str9_of_open9`.
* `AbiFn.contract`; `AbiFn.of_spec`: a contract for the spec `p.spec fp post` (entry exactly
  `p.Entered`) on `Open.isa` / `Open9.isa` / `Str9.isa` is a row of `abi_function` when the
  placed region fits; `AbiFn.open9_of_open`, `AbiFn.str9_of_open9` along the model order.
* `EntersCode.of_entersAt`, `AbiFn.elfFn`: a row of `x86.abi_function` and the loader fact for
  its region give the row of `elf.fn_contract`.
* `ElfFn.of_segment`: the segment theorem, the loader fact and the two conditions give the ELF
  theorem; `ElfFn.x86_of_blob` with the `Blob` certificate of the executable;
  `ElfFn.of_leafSpec` for a `BlockCert9.leafSpec` contract (both conditions proved here).
* `ElfFnWeak.of_vacuous`, `ElfFn.not_vacuous`, `AbiFn.not_vacuous`: the weak form is filled by
  the vacuous spec `vacuousSpec` (`entry := False`) for any code the executable loads; `ElfFn`
  and `AbiFn` are not.
* `correct_iff`, `correctLoose_iff`: the class shapes are `Silmaril.Problems.FnCorrect`.
* Example: the leaf `ilog2_u32` (`Silmaril.X86.BlockCert9.Examples`) is a row of
  `abi_function.open9` (`ilog2_abi`), and a row of `fn_contract.x86_open9` for any executable
  that loads its code.
-/

@[expose] public section

namespace Silmaril.Project.Shapes

open Silmaril.X86 (MState Word Byte FnContract)

variable {S : FnContract.Spec MState}

theorem Contract.open9_of_open (h : Contract Silmaril.X86.Open.isa S) : Contract Silmaril.X86.Open9.isa S :=
  FnContract.Spec.Total.toOpen9 h

theorem Contract.str9_of_open9 (h : Contract Silmaril.X86.Open9.isa S) : Contract Silmaril.X86.Str9.isa S :=
  FnContract.Spec.Total.toStr9 h

theorem Contract.str9_of_open (h : Contract Silmaril.X86.Open.isa S) : Contract Silmaril.X86.Str9.isa S :=
  h.open9_of_open.str9_of_open9

theorem ContractStrict.contract {M : Model} (h : ContractStrict M S) : Contract M S :=
  FnContract.Spec.Strict.total h

/-! ## Non-vacuity -/

/-- **A spec entered at loaded code is not vacuous** on `Silmaril.X86.Open.isa`: if every state with `code`
loaded at `base` and `rip = rip` meets `S.entry`, and the code leaves 32 bytes below the top of
the address space, some System V entry state meets `S.entry`. -/
theorem Nonvacuous.of_entered {base : Word} {code : List Byte} {rip : Word}
    (fits : base.toNat + code.length + 32 ≤ 2 ^ 64)
    (he : ∀ s : MState, Silmaril.X86.Ext.Loaded s.memory base code → s.core.rip = rip →
      S.entry s) :
    Nonvacuous Silmaril.X86.Open.isa S :=
  let ⟨s, hl, hr, ha⟩ := Silmaril.Proofs.Project.Shapes.X86.exists_entry base code rip fits
  ⟨s, trivial, ha, he s hl hr⟩

/-- The non-vacuity of a spec carries from `Silmaril.X86.Open.isa` to `Silmaril.X86.Open9.isa` and `Silmaril.X86.Str9.isa`: the three
models share the state, its liveness and its views. -/
theorem Nonvacuous.open9_of_open (h : Nonvacuous Silmaril.X86.Open.isa S) : Nonvacuous Silmaril.X86.Open9.isa S :=
  let ⟨s, _, ha, he⟩ := h; ⟨s, trivial, ha, he⟩

theorem Nonvacuous.str9_of_open9 (h : Nonvacuous Silmaril.X86.Open9.isa S) : Nonvacuous Silmaril.X86.Str9.isa S :=
  let ⟨s, _, ha, he⟩ := h; ⟨s, trivial, ha, he⟩

/-! ## Placed functions -/

variable {p : Placement} {fp : MState → Nat → Prop} {post : MState → MState → Prop}

theorem AbiFn.contract {M : Model} (h : AbiFn M p S) : Contract M S := h.2.2

/-- The spec `p.spec fp post` is not vacuous when the placed region fits. -/
theorem Placement.spec_nonvacuous (fits : p.base.toNat + p.code.length + 32 ≤ 2 ^ 64) :
    Nonvacuous Silmaril.X86.Open.isa (p.spec fp post) :=
  Nonvacuous.of_entered (rip := p.entry) fits fun _ hl hr => ⟨hl, hr⟩

/-- **A contract for `p.spec fp post` on `Silmaril.X86.Open.isa` is a row** of `abi_function.open` when the
placed region fits. -/
theorem AbiFn.of_spec (hc : Contract Silmaril.X86.Open.isa (p.spec fp post))
    (fits : p.base.toNat + p.code.length + 32 ≤ 2 ^ 64) :
    AbiFn Silmaril.X86.Open.isa p (p.spec fp post) :=
  ⟨fun _ he => he, Placement.spec_nonvacuous fits, hc⟩

/-- The same on `Silmaril.X86.Open9.isa`. -/
theorem AbiFn.of_spec9 (hc : Contract Silmaril.X86.Open9.isa (p.spec fp post))
    (fits : p.base.toNat + p.code.length + 32 ≤ 2 ^ 64) :
    AbiFn Silmaril.X86.Open9.isa p (p.spec fp post) :=
  ⟨fun _ he => he, (Placement.spec_nonvacuous fits).open9_of_open, hc⟩

/-- A row on `Open` is a row on `Open9`. -/
theorem AbiFn.open9_of_open (h : AbiFn Silmaril.X86.Open.isa p S) : AbiFn Silmaril.X86.Open9.isa p S :=
  let ⟨he, hn, hc⟩ := h; ⟨he, hn.open9_of_open, hc.open9_of_open⟩

/-- A row on `Open9` is a row on `Str9`. -/
theorem AbiFn.str9_of_open9 (h : AbiFn Silmaril.X86.Open9.isa p S) : AbiFn Silmaril.X86.Str9.isa p S :=
  let ⟨he, hn, hc⟩ := h; ⟨he, hn.str9_of_open9, hc.str9_of_open9⟩

/-- A spec entered at the function placed by `p` is about the region of `p`, if the function's
offset is inside it. -/
theorem EntersCode.of_entersAt {M : Model} (hoff : p.off < p.code.length)
    (h : EntersAt M p S) : EntersCode M p.base.toNat p.code S := fun s hs =>
  let ⟨hl, hr⟩ := h s hs; Silmaril.Proofs.Project.Shapes.X86.rip_inside hoff hl hr

/-! ## Functions of an executable -/

/-- **Segment theorem ⇒ ELF theorem.** -/
theorem ElfFn.of_segment {L : Loader} {M : Model} {V : Type} {exe : Value V} {addr : Nat}
    {code : List Byte} (hl : Loads L exe "rx" addr code) (he : EntersCode M addr code S)
    (hn : Nonvacuous M S) (hc : Contract M S) : ElfFn L M exe addr code S :=
  ⟨hl, he, hn, hc⟩

/-- **A placed function's row and the loader fact give the ELF row**: if `exe` loads the region
of `p` (`rx`) and the function's offset is inside it, a row of `x86.abi_function` on `M` is a
row of `elf.fn_contract` on `M` for the region. -/
theorem AbiFn.elfFn {L : Loader} {M : Model} {V : Type} {exe : Value V}
    (hl : Loads L exe "rx" p.base.toNat p.code) (hoff : p.off < p.code.length)
    (h : AbiFn M p S) : ElfFn L M exe p.base.toNat p.code S :=
  ⟨hl, EntersCode.of_entersAt hoff h.1, h.2.1, h.2.2⟩

/-- A row of `fn_contract.x86_open` (or any model) from the executable's `Blob` certificate,
the kernel-fast loader check and the segment theorem. -/
theorem ElfFn.x86_of_blob {M : Model} {V : Type} {exe : Value V} {addr : Nat}
    {code : List Byte} {B : Silmaril.X86.Link.Blob}
    (hB : Silmaril.X86.Link.Blob.ofBytes (Silmaril.Project.Formats.elfBytes exe.bytes) = B)
    (h : Silmaril.X86.Ladder.Pinned.check B "rx" addr code = true)
    (he : EntersCode M addr code S) (hn : Nonvacuous M S) (hc : Contract M S) :
    ElfFn Loader.x86 M exe addr code S :=
  ⟨Loads.x86_of_blob hB h, he, hn, hc⟩

/-- `ElfFn` forgets to its weak form. -/
theorem ElfFn.weak {L : Loader} {M : Model} {V : Type} {exe : Value V} {addr : Nat}
    {code : List Byte} (h : ElfFn L M exe addr code S) : ElfFnWeak L M exe addr code S :=
  ⟨h.1, h.2.2.2⟩

/-- A leaf contract (`BlockCert9.leafSpec base code off post`) is about `code` at `base` on
each standard model (`M` reads the open state: `hmem`, `hcore`), if the function's offset is
inside the code. -/
theorem EntersCode.leafSpec {M : Model} (hmem : ∀ s, M.mem s = s.memory)
    (hcore : ∀ s, M.core s = s.core) {base : Word} {code : List Byte} {off : Nat}
    (hoff : off < code.length) :
    EntersCode M base.toNat code (Silmaril.X86.BlockCert9.leafSpec base code off post) :=
  fun s ⟨hl, hr⟩ => Silmaril.Proofs.Project.Shapes.X86.rip_inside (M := M) hoff
    (by rw [hmem]; exact hl) (by rw [hcore]; exact hr)

/-- **A row for a leaf contract** on `Silmaril.X86.Open.isa`: the loader fact, the contract, and two
decidable side conditions (the offset inside the code, the code below the top of the address
space). -/
theorem ElfFn.of_leafSpec {L : Loader} {V : Type} {exe : Value V} {base : Word}
    {code : List Byte} {off : Nat} (hl : Loads L exe "rx" base.toNat code)
    (hoff : off < code.length) (fits : base.toNat + code.length + 32 ≤ 2 ^ 64)
    (hc : Contract Silmaril.X86.Open.isa (Silmaril.X86.BlockCert9.leafSpec base code off post)) :
    ElfFn L Silmaril.X86.Open.isa exe base.toNat code (Silmaril.X86.BlockCert9.leafSpec base code off post) :=
  ⟨hl, EntersCode.leafSpec (fun _ => rfl) (fun _ => rfl) hoff,
    Nonvacuous.of_entered (rip := base + BitVec.ofNat 64 off) fits fun _ hl hr => ⟨hl, hr⟩, hc⟩

/-- The same on `Silmaril.X86.Open9.isa`. -/
theorem ElfFn.of_leafSpec9 {L : Loader} {V : Type} {exe : Value V} {base : Word}
    {code : List Byte} {off : Nat} (hl : Loads L exe "rx" base.toNat code)
    (hoff : off < code.length) (fits : base.toNat + code.length + 32 ≤ 2 ^ 64)
    (hc : Contract Silmaril.X86.Open9.isa (Silmaril.X86.BlockCert9.leafSpec base code off post)) :
    ElfFn L Silmaril.X86.Open9.isa exe base.toNat code
      (Silmaril.X86.BlockCert9.leafSpec base code off post) :=
  ⟨hl, EntersCode.leafSpec (fun _ => rfl) (fun _ => rfl) hoff,
    (Nonvacuous.of_entered (S := Silmaril.X86.BlockCert9.leafSpec base code off post)
      (rip := base + BitVec.ofNat 64 off) fits fun _ hl hr => ⟨hl, hr⟩).open9_of_open, hc⟩

/-! ## The vacuous spec: the weak form is filled, `ElfFn` and `AbiFn` are not -/

/-- A spec no state enters. Its contract holds on every model. -/
def vacuousSpec : FnContract.Spec MState where
  entry _ := False
  footprint _ _ := False
  post _ _ := False

theorem Contract.vacuous {M : Model} : Contract M vacuousSpec :=
  fun _ _ _ h => h.elim

/-- **The weak form says nothing about the code**: for any code an executable loads, the
vacuous spec fills it. -/
theorem ElfFnWeak.of_vacuous {L : Loader} {M : Model} {V : Type} {exe : Value V} {addr : Nat}
    {code : List Byte} (hl : Loads L exe "rx" addr code) :
    ElfFnWeak L M exe addr code vacuousSpec :=
  ⟨hl, Contract.vacuous⟩

/-- **`ElfFn` rejects the vacuous spec.** -/
theorem ElfFn.not_vacuous {L : Loader} {M : Model} {V : Type} {exe : Value V} {addr : Nat}
    {code : List Byte} : ¬ ElfFn L M exe addr code vacuousSpec :=
  fun ⟨_, _, ⟨_, _, _, h⟩, _⟩ => h

/-- **`AbiFn` rejects the vacuous spec.** -/
theorem AbiFn.not_vacuous {M : Model} : ¬ AbiFn M p vacuousSpec :=
  fun ⟨_, ⟨_, _, _, h⟩, _⟩ => h

/-! ## The class shapes -/

theorem correct_iff (𝓜 : Silmaril.Problems.Class MState) (S : Word → FnContract.Spec MState) :
    Correct 𝓜 S ↔ Silmaril.Problems.FnCorrect 𝓜 S := Iff.rfl

theorem correctLoose_iff (D : Silmaril.X86.Loose.DTable Silmaril.X86.Loose.Listing.LForm)
    (S : Word → FnContract.Spec MState) :
    CorrectLoose D S ↔ Silmaril.Problems.FnCorrect
      (Silmaril.Problems.Class.below (Silmaril.Problems.Models.X86.looseSv1 D)) S := Iff.rfl

end Silmaril.Project.Shapes

end

/-! ## Example: the leaf `ilog2_u32`

Outside the public section: it uses the privately imported example proofs. -/

namespace Silmaril.Project.Shapes

open Silmaril.X86.BlockCert9.Examples

/-- The placement of `ilog2_u32`: its code at `0x401430`, entered at offset 0. -/
def ilogPlacement : Placement := ⟨ilogBase, ilogCode, 0⟩

/-- **`ilog2_u32` is a row of `abi_function.open9`.** -/
theorem ilog2_abi : AbiFn Silmaril.X86.Open9.isa ilogPlacement ilogSpec :=
  ⟨fun _ he => he,
    (Nonvacuous.of_entered (S := ilogSpec) (base := ilogBase) (code := ilogCode)
      (rip := ilogPlacement.entry) (by decide) fun _ hl hr => ⟨hl, hr⟩).open9_of_open,
    ilog2_total⟩

example {V : Type} {exe : Value V} (hl : Loads Loader.x86 exe "rx" ilogBase.toNat ilogCode) :
    ElfFn Loader.x86 Silmaril.X86.Open9.isa exe ilogBase.toNat ilogCode ilogSpec :=
  ilog2_abi.elfFn hl (by decide)

end Silmaril.Project.Shapes
