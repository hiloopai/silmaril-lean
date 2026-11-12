module

public import Silmaril.X86.Institution.Defs
public import Silmaril.X86.Exact.Defs
public import Silmaril.Project.Shapes.X86.Defs

/-!
# The x86 institution over arbitrary binaries

silmaril's x86 institution (`Silmaril.X86.Institution`) is *per binary*: a signature carries
the decode table of one image, so its sentences can only speak about that image. This module
lifts it to the level of an **instruction set**: a signature is an ISA fragment, and a
sentence names the binary it is about.

**Signatures.** `ISig Φ = ⟨dec, forms, sys⟩` over a form index `Φ`:

* `dec : Decoder Φ`, the decode *relation* `Set (DEntry Φ)`: "these bytes are this form".
  A decoder function (`Decoder.ofFn I.decode`, the graph at full length) and a per-binary
  table (`Decoder.ofTable D`) are both decoders, so the per-binary signatures are exactly the
  ISA signatures with a finite decoder;
* `forms : Loose.Sigma Φ`, the form specifications (silmaril's);
* `sys : SysIface`, the syscall slot (silmaril's, trivial for now).

A bundled signature `Sign` packs the form index with the signature, so that a morphism can
change it. A **morphism** `A ⟶ B` (`Sign.Hom`) is a renaming `ρ : A.Φ → B.Φ` along which `B`
decodes every entry `A` decodes (`ρ` maps entries to entries) and specifies every form `A`
specifies, more tightly. It covers ISA inclusion (`Ext8 ⊆ Ext9 ⊆ Str9`: new forms, the old
ones renamed into a bigger index), tightening (`Σ v1 ⟶ Σexact`) and growing a per-binary
table, in one category.

**Models.** The *top* of a signature is the loose machine `loose G.dec G.forms V`: at a state
whose `rip` holds the bytes of an entry of the decoder, a step does what every specification
of that entry allows, elsewhere anything. It reads the code from the state's memory, so one
machine serves every image: a model `Model V A = {C // Le C (top) ∧ Progress C}` refines,
for every image at once, the loose machine that decodes that image with the signature's
decoder (`Thms.le_table`: a model of `A` is below the per-binary top of any table that `A`
decodes). The reduct along a morphism keeps the machine.

**Sentences** are data and name the binary. `Sen Φ σ` has two forms:

* `fn p L S`: **the function placed by `p`** (`Placement`: a code region `p.code` at `p.base`
  and the function's offset `p.off`, silmaril's `x86.abi_function` placement) **meets the
  System V contract `S`**. Its meaning is `S.at V p`: `S` entered with the region loaded as
  code and `rip` at the function, demonically totally correct. `L : Listing Φ` is the
  function's disassembly in the signature's vocabulary (offset, length, form). It is part of
  the data that is translated, compared and checked (`Sen.WF`: the decoder reads each listed
  slice as its form), but satisfaction does not depend on it; it is a certificate, not a
  hypothesis;
* `family φ`: a contract family `Word → Spec σ`, silmaril's per-binary sentence, which names
  its code inside the precondition.

**Translation** along `ρ` renames the listing's forms (`Sen.map`): a sentence of `Ext9`
becomes one of `Str9` with every form wrapped in `.ext9`. The bytes, the placement and the
contract are unchanged, so the satisfaction condition still holds by unfolding: what a
binary does is fixed by its bytes, not by the vocabulary used to list them.

**Satisfaction** `Sat V C φ` is `MustTotal` of the placed contract on `C` (for `fn`), or
silmaril's `Institution.Sat` (for `family`).

The institution is `inst V : Sign ⥤ Room`, with `classic V` and `bundled V` as in silmaril.
The per-binary institution embeds: `embed Φ : Institution.Sig Φ ⥤ Sign` (a table is a finite
decoder) and the comorphism `embedCoHom V : (Institution.bundled Φ V).CoHom (bundled V)`
(sentences become `family` sentences, models are the same machines). `pin` composes it with
a morphism `⟨D, forms⟩ ⟶ A` into the corridor from the per-binary room of a table `D` that
`A` decodes (the code of one image) to the room of `A`.

**Where other levels attach** (sketch, nothing below is built).

* *Other instruction sets* (32-bit x86, AArch64, RISC-V). Everything here is parametric in
  the form index, the decoder and the state type `σ` with its views `V`, but silmaril's
  `Views`, `FormSpec` and `Spec` are about the x86-64 core `Silmaril.X86.State` (registers,
  flags, `rip`, `fsBase`) and the System V contract. An ISA family attaches by abstracting
  the core: `Views κ σ` over a core type `κ` with a program counter, `FormSpec κ`, and a
  contract with the family's calling convention (AAPCS64, the RISC-V psABI, i386 cdecl).
  Then `Sign` becomes a signature over a fixed family, and a cross-family translation
  (x86-32 as a mode of x86-64; a binary translator) is a comorphism that changes the state
  type and pulls contracts back along the state view (`Spec.comap`).
* *ELF level* (built). `elf Ld exe p L S`: the loader `Ld` (an explicit, trusted
  `ELoader`; `ELoader.x86` is silmaril's LPS loader) places the function `p` from the
  executable `exe` in an `rx` segment (`Places`, silmaril's `Loads`/`Pinned.LoadedAt`), and
  the `fn` sentence holds of `p`. `Places` is a fact about the bytes, not the model. Trusted:
  the loader, and that a process started from `exe` has the loader's image in memory.
* *Dynamic linking* (interface, `DynSen`, `dyn`). A function of an executable loaded with its
  `DT_NEEDED` closure: for **every** outcome `r` of an explicit `DynLoader` that binds every
  import (`r.resolve`), the function is loaded at its object's base and its contract (which
  may read `r`: the GOT, the bases) holds on the model **with the imports' contracts linked
  in** (`withImports`: one atomic contract step at each binding). The dynamic-loader model
  (`Silmaril.Elf.Link.Dyn`) fills `DynLoader`.
* *Whole runs* (`ProcSen`, `proc`). Every process of an executable with its closure, started
  by an explicit `ProcLoader` from the documented initial state (`ProcEnv`: argv, envp, auxv)
  terminates, and its exit status and `stdout` (an explicit `ProcObs`) satisfy `post`, on the
  model with the imports' contracts linked in. Contracts may change the state beyond core and
  memory (`XSpec`: the bytes handed to `stdout`, the exit status). **Trusted** in a `proc`
  sentence: the `ProcLoader` (`execve`, the initial stack, `ld.so`'s relocation), the
  `ProcObs` (what "exited with status `e`, wrote `out`" means), the model (its instruction
  semantics, and the kernel: system calls are steps of the model), and the imports'
  contracts unless discharged (`must_of_withImports`). The open question for the
  signature: a `SysIface` listing the system calls a process may issue, and morphisms that
  extend it.

Lean reserves `Σ`, so signatures are named `G`, `A`, `B` in the code.
-/

@[expose] public section

namespace Silmaril.X86.BinInstitution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.X86 (Word Byte RelIsa)
open Silmaril.X86.RelIsa (Views Le Progress)
open Silmaril.X86.Loose (DEntry DTable FormSpec AtEntry MatchRes)
open Silmaril.X86.FnContract (Spec)
open Silmaril.X86.Institution (SysIface)
open Silmaril.Project.Shapes (Placement)

variable {Φ Ψ σ : Type}

/-! ## Decoders -/

/-- **A decoder**: the byte strings an ISA reads as each form, as a relation. -/
abbrev Decoder (Φ : Type) : Type := Set (DEntry Φ)

/-- The decoder of a decoding function: the entries it reads at their full length. -/
def Decoder.ofFn (dec : List Byte → Option (Φ × Nat)) : Decoder Φ :=
  {e | dec e.bytes = some (e.form, e.bytes.length)}

/-- The decoder of a per-binary table. -/
def Decoder.ofTable (D : DTable Φ) : Decoder Φ := {e | e ∈ D}

/-- An entry with its form renamed. -/
def mapEntry (ρ : Φ → Ψ) (e : DEntry Φ) : DEntry Ψ := ⟨e.bytes, ρ e.form⟩

/-! ## The loose machine of a decoder

`Silmaril.X86.Loose.X86Loose.rel` over a decoder instead of a list; on `Decoder.ofTable D`
it is `X86Loose.rel D` (`Thms.loose_ofTable`). Proposed upstream: let `X86Loose.step` take a
`Set (DEntry Φ)`. -/

/-- The loose step relation of a decoder: at every decoder entry fetched at `rip`, a step is
allowed by every specification of its form; the successor is live. -/
def looseStep (dec : Decoder Φ) (S : Silmaril.X86.Loose.Sigma Φ) (V : Views σ) (s : σ)
    (r : RelIsa.Res σ) : Prop :=
  (∀ e ∈ dec, AtEntry e (V.core s) (V.mem s) → ∀ F, S e.form = some F →
    ∃ res, F.sem (V.core s) (V.mem s) e.bytes.length res ∧ MatchRes V s r res) ∧
  ∀ t, r = .ok t → V.live t

/-- **The loose machine of a decoder** and form specifications. -/
def loose (dec : Decoder Φ) (S : Silmaril.X86.Loose.Sigma Φ) (V : Views σ) : RelIsa σ where
  toViews := V
  step := looseStep dec S V
  live_step {_ t} _ h := h.2 t rfl

/-! ## Signatures -/

/-- **An ISA signature**: a decoder, form specifications and a syscall interface. -/
structure ISig (Φ : Type) : Type where
  /-- What the ISA decodes: byte strings with their forms. -/
  dec : Decoder Φ
  /-- What each form may do; `none` is unspecified (anything goes). -/
  forms : Silmaril.X86.Loose.Sigma Φ
  /-- The syscall interface (trivial for now). -/
  sys : SysIface := {}

/-- **The top of a signature**: the loose machine of its decoder. -/
def ISig.top (V : Views σ) (G : ISig Φ) : RelIsa σ := loose G.dec G.forms V

/-- The ISA signature of a per-binary signature: its table as a (finite) decoder. -/
def ISig.ofSig (G : Silmaril.X86.Institution.Sig Φ) : ISig Φ :=
  ⟨Decoder.ofTable G.table, G.forms, G.sys⟩

/-- **The exact ISA signature of a machine**: its decoder and its exact forms
(`Silmaril.X86.Exact.FormSpec.exact`). -/
def ISig.ofIsa (I : Silmaril.X86.SegVC.Isa σ) : ISig I.Instr :=
  ⟨Decoder.ofFn I.decode, Silmaril.X86.Exact.exactForms I, {}⟩

/-- **A bundled signature**: a form index and an ISA signature over it. -/
structure Sign : Type 1 where
  /-- The form index. -/
  Φ : Type
  /-- The signature. -/
  sig : ISig Φ

/-- **A signature morphism** `A ⟶ B`: a renaming of the forms along which `B` decodes every
entry of `A`, and specifies every form `A` specifies, more tightly. -/
@[ext]
structure Sign.Hom (A B : Sign) : Type where
  /-- The renaming of the forms. -/
  ρ : A.Φ → B.Φ
  /-- Every entry `A` decodes, `B` decodes as the renamed form. -/
  dec : ∀ e ∈ A.sig.dec, mapEntry ρ e ∈ B.sig.dec
  /-- Every form `A` specifies, `B` specifies more tightly. -/
  forms : ∀ i F, A.sig.forms i = some F → ∃ F', B.sig.forms (ρ i) = some F' ∧ F.Tightens F'

/-- The identity morphism. -/
def Sign.Hom.id (A : Sign) : Sign.Hom A A :=
  ⟨_root_.id, fun _ h => h, fun _ F h => ⟨F, h, FormSpec.Tightens.refl F⟩⟩

/-- Composition of morphisms. -/
def Sign.Hom.comp {A B C : Sign} (f : Sign.Hom A B) (g : Sign.Hom B C) : Sign.Hom A C where
  ρ := g.ρ ∘ f.ρ
  dec e he := g.dec _ (f.dec e he)
  forms i F hF := by
    obtain ⟨F₁, h₁, t₁⟩ := f.forms i F hF
    obtain ⟨F₂, h₂, t₂⟩ := g.forms _ F₁ h₁
    exact ⟨F₂, h₂, t₁.trans t₂⟩

/-- **The category of ISA signatures.** -/
instance : Category.{0} Sign where
  Hom := Sign.Hom
  id := Sign.Hom.id
  comp := Sign.Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ## Models -/

/-- **A model of `A`**: a machine below the top of `A` with an outcome from every live
state. -/
def Model (V : Views σ) (A : Sign) : Type :=
  {C : RelIsa σ // Le C (A.sig.top V) ∧ Progress C}

/-- Models ordered by refinement. -/
instance (V : Views σ) (A : Sign) : Preorder (Model V A) where
  le M M' := Le M.1 M'.1
  le_refl M := Le.refl M.1
  le_trans _ _ _ h₁ h₂ := Le.trans h₁ h₂

/-! ## Sentences -/

/-- One instruction of a listing: its offset in the code, its length and its form. -/
structure Item (Φ : Type) : Type where
  off : Nat
  len : Nat
  form : Φ
  deriving DecidableEq, Repr

/-- **A listing**: a function's disassembly in a signature's vocabulary. -/
abbrev Listing (Φ : Type) : Type := List (Item Φ)

/-- A listing with its forms renamed. -/
def Listing.map (ρ : Φ → Ψ) (L : Listing Φ) : Listing Ψ :=
  List.map (fun it => ⟨it.off, it.len, ρ it.form⟩) L

/-- **The linear sweep** of a decoding function over `code` from offset `0`: decode, step
over the instruction, repeat, until the end of the code or a byte string it does not read. -/
def Listing.linear (dec : List Byte → Option (Φ × Nat)) (code : List Byte) : Listing Φ :=
  go code.length 0
where
  /-- The sweep from offset `o`, with fuel. -/
  go : Nat → Nat → Listing Φ
    | 0, _ => []
    | fuel + 1, o =>
      if o < code.length then
        match dec (code.drop o) with
        | some (f, n) => if 0 < n then ⟨o, n, f⟩ :: go fuel (o + n) else []
        | none => []
      else []

/-- The listing a decoding function reads at the given offsets of `code` (the offsets it
cannot read are dropped). -/
def Listing.ofFn (dec : List Byte → Option (Φ × Nat)) (code : List Byte) (offs : List Nat) :
    Listing Φ :=
  offs.filterMap fun o => (dec (code.drop o)).map fun (f, n) => ⟨o, n, f⟩

/-- **The placed contract**: `S` entered with the code of `p` loaded (`Ext.Loaded`) and `rip`
at the function (read through the views `V`). -/
def Spec.at (V : Views σ) (p : Placement) (S : Spec σ) : Spec σ where
  entry s := Silmaril.X86.Ext.Loaded (V.mem s) p.base p.code ∧ (V.core s).rip = p.entry ∧
    S.entry s
  footprint := S.footprint
  post := S.post

/-! ## Loaders (trusted, explicit) -/

/-- **A static ELF loader**: the memory image (segments with permissions) a file loads to, if
the loader accepts it. A loader is *data in the sentence*: an `elf` sentence says what holds
under the loader it names, so the loader is an explicit, trusted parameter, never a hidden
assumption. -/
abbrev ELoader : Type := Silmaril.X86.Link.Blob → Option Silmaril.Process.LPS.Image

/-- The LPS loader with policy `P` (silmaril's `Project.Shapes.Loader.lps` on a `Blob`). -/
def ELoader.lps (P : Silmaril.Process.LPS.ELFImage.Policy) : ELoader := fun b =>
  (Silmaril.Process.LPS.ELFImage.parse P b.bytes).map (·.image b.bytes)

/-- **The standard x86-64 loader** (`ELFImage.x86Policy`, as `Pinned.LoadedAt`). -/
def ELoader.x86 : ELoader := ELoader.lps Silmaril.Process.LPS.ELFImage.x86Policy

/-- **The loader places `p`**: it accepts `exe`, and one `rx` segment of the image holds
exactly `p.code` at `p.base` (silmaril's `Loads` with `perms = "rx"`). -/
def Places (Ld : ELoader) (exe : Silmaril.X86.Link.Blob) (p : Placement) : Prop :=
  ∃ img, Ld exe = some img ∧ ∃ seg ∈ img.segments, seg.perms = "rx" ∧
    Silmaril.X86.Ladder.Pinned.sliceAt seg p.base.toNat p.code.length = some p.code

/-! ## Contracts with effects

silmaril's `Spec.ResultV` asks that a call changes only the core and the memory (`silent`).
A library call such as `puts` also changes the state beyond them (the bytes handed to
`stdout`, the exit status, kept in a ghost extension of the state). `XSpec` is a `Spec` with
an **effect** relation on whole states that replaces `silent`; `XSpec.ofSpec V S` is `S` with
`silent` as its effect, so `ResultX` of it is exactly `ResultV` (`Thms.resultX_ofSpec_iff`).
Proposed upstream: give `Spec` (or `Spec.ResultV`) an effect field defaulting to `silent`. -/

/-- **A contract with an effect**: a function spec whose call may change the state beyond the
core and the memory, as `effect` allows. -/
structure XSpec (σ : Type) extends Spec σ where
  /-- What the call may do to the whole state (`silent`: nothing beyond core and memory). -/
  effect : σ → σ → Prop

/-- A plain spec as a contract whose effect is `silent`. -/
def XSpec.ofSpec (V : Views σ) (S : Spec σ) : XSpec σ :=
  { S with effect := fun s t => V.upd s (V.core t) (V.mem t) = t }

/-- **What a call with contract `X` guarantees** from `s` to `t`: `Spec.ResultV` with `silent`
replaced by the effect. -/
structure XSpec.ResultX (V : Views σ) (X : XSpec σ) (s t : σ) : Prop where
  effect : X.effect s t
  abi : Silmaril.X86.FnContract.AbiReturn (V.core s) (V.mem s) (V.core t)
  frame : (V.mem s).WritesWithin (V.mem t) (X.footprint s)
  post : X.post s t

/-- **Demonic total correctness of a contract with an effect.** -/
def XSpec.MustTotal (A : RelIsa σ) (X : XSpec σ) : Prop :=
  ∀ s, A.live s → Silmaril.X86.FnContract.AbiEntry (A.core s) (A.mem s) → X.entry s →
    RelIsa.Must A (fun _ => True) (X.ResultX A.toViews s) s

/-! ## Dynamic linking and processes

A dynamically linked executable is loaded with the objects of its `DT_NEEDED` closure. A run
of the dynamic loader decides where each object goes (ASLR) and how each imported symbol is
bound; a sentence about such an executable is relative to **every** outcome of the loader and
to the contracts it **assumes** of the imported symbols. Nothing here models `ld.so`:
`DynLoader` and `ProcLoader` are the slots the dynamic loader model (`Silmaril.Elf.Link.Dyn`)
fills.

**The rely is linked in.** The assumed contracts are not hypotheses about the model (that would
make satisfaction fail to be closed under refinement: a smaller machine may meet the assumption
while the conclusion only followed for a bigger one). Instead the conclusion is judged on
`withImports C r Γ`: the model `C` with each bound import replaced by **one atomic step of its
contract** (where the contract's precondition holds; elsewhere at that address anything goes),
as a summary. This is monotone in `C` (`Thms.le_withImports`), so satisfaction is closed under
refinement for every sentence, and when `C` itself meets the import contracts the conclusion
transfers to `C` (`Thms.must_of_withImports`). -/

/-- An imported symbol: its name and the version it requests (`DT_VERNEED`), if any. -/
structure SymRef : Type where
  name : String
  version : Option String := none
  deriving DecidableEq, Repr

/-- **One outcome of a dynamic load**. -/
structure DynLoad : Type where
  /-- The load base of each object, by name (`""`: the executable). -/
  base : String → Option Word
  /-- **The resolution** (`Resolve`): the address each imported symbol is bound to. -/
  resolve : SymRef → Option Word

/-- **A dynamic loader**: the outcomes it may produce for an executable and the objects of its
`DT_NEEDED` closure, by name. Trusted, explicit: it is part of the sentence. -/
structure DynLoader : Type where
  Loads : Silmaril.X86.Link.Blob → List (String × Silmaril.X86.Link.Blob) → DynLoad → Prop

/-- The contracts assumed of imported symbols, as contract families over the address the
symbol is bound to. -/
abbrev Imports (σ : Type) : Type := List (SymRef × (Word → XSpec σ))

/-- Every import is bound in `r`. -/
def DynLoad.Resolves (r : DynLoad) (Γ : Imports σ) : Prop := ∀ im ∈ Γ, (r.resolve im.1).isSome

/-- The assumed contract at address `a` in `r`: that of the first import bound to `a`. -/
def importAt (r : DynLoad) (Γ : Imports σ) (a : Word) : Option (XSpec σ) :=
  (Γ.find? fun im => r.resolve im.1 == some a).map fun im => im.2 a

/-- **The model with the imports' contracts linked in**: at an address an import is bound to, one
step to a result of its contract (from a live System V entry meeting its precondition; anything
otherwise); elsewhere, `C`. Successors are live. -/
def withImports (C : RelIsa σ) (r : DynLoad) (Γ : Imports σ) : RelIsa σ where
  toViews := C.toViews
  step s o :=
    (match importAt r Γ (C.core s).rip with
      | some X => C.live s → Silmaril.X86.FnContract.AbiEntry (C.core s) (C.mem s) →
          X.entry s → ∃ t, o = .ok t ∧ X.ResultX C.toViews s t
      | none => C.step s o) ∧
    ∀ t, o = .ok t → C.live t
  live_step _ h := h.2 _ rfl

/-- **A sentence about a function of a dynamically linked executable.** -/
structure DynSen (Φ σ : Type) : Type where
  /-- The dynamic loader the sentence is relative to. -/
  loader : DynLoader
  /-- The executable. -/
  exe : Silmaril.X86.Link.Blob
  /-- Its `DT_NEEDED` closure, by `DT_SONAME` (e.g. `libc.so.6`). -/
  libs : List (String × Silmaril.X86.Link.Blob)
  /-- The object holding the function (`""`: the executable), and its offset from that
  object's load base. -/
  obj : String
  off : Nat
  /-- The function's code. -/
  code : List Byte
  /-- The contracts assumed of the imported symbols. -/
  imports : Imports σ
  /-- The function's listing. -/
  listing : Listing Φ
  /-- The contract, which may depend on the load outcome (GOT contents, bases). -/
  spec : DynLoad → Spec σ

/-- The placement of a dynamic sentence's function in a load outcome with base `b`. -/
def DynSen.place (d : DynSen Φ σ) (b : Word) : Placement := ⟨b + BitVec.ofNat 64 d.off, d.code, 0⟩

/-- **Satisfaction of a dynamic sentence**: for every outcome of the loader that binds every
import, the function's object is loaded at some base and its placed contract holds on the
model with the imports' contracts linked in. -/
def DynSen.Sat (V : Views σ) (C : RelIsa σ) (d : DynSen Φ σ) : Prop :=
  ∀ r, d.loader.Loads d.exe d.libs r → r.Resolves d.imports →
    ∃ b, r.base d.obj = some b ∧
      (Spec.at V (d.place b) (d.spec r)).MustTotal (withImports C r d.imports)

/-- The documented initial state of a process: arguments, environment, auxiliary vector. -/
structure ProcEnv : Type where
  argv : List (List Byte)
  envp : List (List Byte)
  auxv : List (Nat × Nat)

/-- **Process creation** (trusted, explicit): the states a process of an executable with its
`DT_NEEDED` closure may start in, with environment `env`, after a load with outcome `r` (the
kernel's `execve`, the initial stack, and `ld.so`'s relocation, as one relation). -/
structure ProcLoader (σ : Type) : Type where
  Starts : Silmaril.X86.Link.Blob → List (String × Silmaril.X86.Link.Blob) → ProcEnv →
    DynLoad → σ → Prop

/-- **The observation of an ended process** (trusted, explicit): its exit status and the bytes
written to file descriptor 1, once it has ended. -/
structure ProcObs (σ : Type) : Type where
  ended : σ → Option (Nat × List Byte)

/-- **A sentence about a whole run**: every process of `exe` (with its closure `libs`), started
by `loader` with environment `env`, terminates with an exit status and output satisfying
`post`, relative to the contracts assumed of the imports. -/
structure ProcSen (σ : Type) : Type where
  loader : ProcLoader σ
  obs : ProcObs σ
  exe : Silmaril.X86.Link.Blob
  libs : List (String × Silmaril.X86.Link.Blob)
  env : ProcEnv
  imports : Imports σ
  /-- What the exit status and the bytes on `stdout` satisfy. -/
  post : Nat → List Byte → Prop

/-- The process has ended, its status and output satisfying `post`. -/
def ProcObs.Done (O : ProcObs σ) (post : Nat → List Byte → Prop) (t : σ) : Prop :=
  ∃ e out, O.ended t = some (e, out) ∧ post e out

/-- **Satisfaction of a process sentence**: from every live start state of every load that binds
every import, every run of the model with the imports linked in never stops and reaches an
ended state whose status and output satisfy `post`. -/
def ProcSen.Sat (C : RelIsa σ) (P : ProcSen σ) : Prop :=
  ∀ r s, P.loader.Starts P.exe P.libs P.env r s → C.live s → r.Resolves P.imports →
    RelIsa.Must (withImports C r P.imports) (fun _ => True) (P.obs.Done P.post) s

/-- **A sentence about a binary.** -/
inductive Sen (Φ σ : Type) : Type where
  /-- The function placed by `p`, listed as `L`, meets the System V contract `S`. -/
  | fn (p : Placement) (L : Listing Φ) (S : Spec σ)
  /-- **ELF level**: the loader `Ld` places `p` from the executable `exe`, and the function
  placed by `p` meets `S`. -/
  | elf (Ld : ELoader) (exe : Silmaril.X86.Link.Blob) (p : Placement) (L : Listing Φ)
      (S : Spec σ)
  /-- **Dynamic linking**: a function of a dynamically linked executable, relative to the
  loader's resolution and the contracts assumed of the imports. -/
  | dyn (d : DynSen Φ σ)
  /-- **A whole run** of a process: exit status and `stdout`, relative to the imports'
  contracts. -/
  | proc (P : ProcSen σ)
  /-- A contract family, the sentence of the per-binary institution. -/
  | family (φ : Word → Spec σ)

/-- **Sentence translation** along a renaming: the listing's forms are renamed. -/
def Sen.map (ρ : Φ → Ψ) : Sen Φ σ → Sen Ψ σ
  | .fn p L S => .fn p (L.map ρ) S
  | .elf Ld exe p L S => .elf Ld exe p (L.map ρ) S
  | .dyn d => .dyn { d with listing := d.listing.map ρ }
  | .proc P => .proc P
  | .family φ => .family φ

/-- **Satisfaction**: the placed contract (or every member of the family) is demonically
totally correct on `C`; an `elf` sentence also asks that the loader places the function. -/
def Sat (V : Views σ) (C : RelIsa σ) : Sen Φ σ → Prop
  | .fn p _ S => (Spec.at V p S).MustTotal C
  | .elf Ld exe p _ S => Places Ld exe p ∧ (Spec.at V p S).MustTotal C
  | .dyn d => d.Sat V C
  | .proc P => P.Sat C
  | .family φ => Silmaril.X86.Institution.Sat C φ

/-- The listing of a sentence with code, and the code it lists. -/
def Sen.listed : Sen Φ σ → Option (List Byte × Listing Φ)
  | .fn p L _ => some (p.code, L)
  | .elf _ _ p L _ => some (p.code, L)
  | .dyn d => some (d.code, d.listing)
  | .proc _ => none
  | .family _ => none

/-- **A well-formed sentence** of `G`: every listed instruction lies in the code and `G`
decodes its bytes as its form. Not part of satisfaction. -/
def Sen.WF (G : ISig Φ) (φ : Sen Φ σ) : Prop :=
  ∀ code L, φ.listed = some (code, L) → ∀ it ∈ L, it.off + it.len ≤ code.length ∧
    (⟨(code.drop it.off).take it.len, it.form⟩ : DEntry Φ) ∈ G.dec

/-! ## The institution -/

/-- **A morphism shrinks the top**: the top of `B` is below the top of `A`. -/
theorem Sign.Hom.topLe (V : Views σ) {A B : Sign} (f : Sign.Hom A B) :
    Le (B.sig.top V) (A.sig.top V) where
  views := rfl
  step {s r} _ h := by
    refine ⟨fun e he hat F hF => ?_, h.2⟩
    obtain ⟨F', hF', ht⟩ := f.forms e.form F hF
    obtain ⟨res, hres, hm⟩ := h.1 (mapEntry f.ρ e) (f.dec e he) hat F' hF'
    exact ⟨res, ht _ _ _ _ hres, hm⟩

/-- The reduct of a model along a morphism. -/
def Model.reduct {V : Views σ} {A B : Sign} (f : Sign.Hom A B) (M : Model V B) : Model V A :=
  ⟨M.1, M.2.1.trans (Sign.Hom.topLe V f), M.2.2⟩

/-- **The room of a signature.** -/
def room (V : Views σ) (A : Sign) : Room.{0, 0, 0} :=
  ⟨Sen A.Φ σ, Cat.of (Model V A), fun M φ => Sat V M.1 φ⟩

/-- **The corridor of a morphism**: listings renamed, models reduced. -/
def corridor (V : Views σ) {A B : Sign} (f : Sign.Hom A B) : room V A ⟶ room V B :=
  ⟨Sen.map f.ρ, (Monotone.functor (f := fun M : Model V B => M.reduct f) fun _ _ h => h :
    Model V B ⥤ Model V A), fun _ φ => by cases φ <;> exact Iff.rfl⟩

theorem Listing.map_id (L : Listing Φ) : L.map _root_.id = L := by
  induction L with
  | nil => rfl
  | cons it L ih =>
    simp only [Listing.map, List.map_cons] at ih ⊢
    rw [ih]; rfl

theorem Listing.map_comp {Χ : Type} (f : Φ → Ψ) (g : Ψ → Χ) (L : Listing Φ) :
    L.map (g ∘ f) = (L.map f).map g := by
  simp only [Listing.map, List.map_map]; rfl

theorem Sen.map_id : (Sen.map _root_.id : Sen Φ σ → Sen Φ σ) = _root_.id := by
  funext φ; cases φ <;> simp [Sen.map, Listing.map_id]

theorem Sen.map_comp {Χ : Type} (f : Φ → Ψ) (g : Ψ → Χ) :
    (Sen.map (g ∘ f) : Sen Φ σ → Sen Χ σ) = Sen.map g ∘ Sen.map f := by
  funext φ; cases φ <;> simp [Sen.map, Listing.map_comp]

/-- **The institution of ISA signatures and sentences about binaries**, as a functor into
rooms. -/
def inst (V : Views σ) : Sign ⥤ Room.{0, 0, 0} where
  obj := room V
  map f := corridor V f
  map_id A := Room.hom_ext (Sen.map_id (Φ := A.Φ)) rfl
  map_comp f g := Room.hom_ext (Sen.map_comp (Sign.Hom.ρ f) (Sign.Hom.ρ g)) rfl

/-- The institution in the classic presentation. -/
def classic (V : Views σ) : ClassicInstitution.{1, 0, 0, 0, 0} Sign :=
  ClassicInstitution.ofRoomFunctor (inst V)

/-- **The institution as a bundled `Inst`**: a node of a silmaril logic graph. -/
def bundled (V : Views σ) : Inst.{1, 0, 0, 0, 0} := ⟨Sign, inst V⟩

/-! ## The per-binary institution inside -/

/-- **A per-binary signature as an ISA signature**: its table is a finite decoder; a
tightening is a morphism with the identity renaming. -/
def embed (Φ : Type) : Silmaril.X86.Institution.Sig Φ ⥤ Sign where
  obj G := ⟨Φ, ISig.ofSig G⟩
  map h := ⟨_root_.id, fun e he => h.le.table e he, fun i F hF => h.le.forms i F hF⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The corridor from the per-binary room of `G` to the room of its ISA signature: a
contract family is a `family` sentence, a model is the same machine. -/
def embedCorridor (V : Views σ) (G : Silmaril.X86.Institution.Sig Φ) :
    Silmaril.X86.Institution.room V G ⟶ room V ((embed Φ).obj G) :=
  ⟨Sen.family, (Monotone.functor (f := fun M : Model V ((embed Φ).obj G) =>
      (⟨M.1, M.2.1, M.2.2⟩ : Silmaril.X86.Institution.Model V G)) fun _ _ h => h :
    Model V ((embed Φ).obj G) ⥤ Silmaril.X86.Institution.Model V G),
    fun _ _ => Iff.rfl⟩

/-- **The per-binary institution embeds in the ISA institution** (an institution
comorphism). -/
def embedCoHom (Φ : Type) (V : Views σ) :
    Inst.CoHom (Silmaril.X86.Institution.bundled Φ V) (bundled V) where
  Φ := embed Φ
  ρ := { app := embedCorridor V, naturality := fun _ _ _ => rfl }

/-- A table `D` that `A` decodes, with `A`'s forms, as a per-binary signature. -/
def pinSig (A : Sign) (D : DTable A.Φ) : Silmaril.X86.Institution.Sig A.Φ :=
  ⟨D, A.sig.forms, A.sig.sys⟩

/-- The morphism from the ISA signature of a table that `A` decodes to `A`. -/
def pinHom (A : Sign) (D : DTable A.Φ) (hD : ∀ e ∈ D, e ∈ A.sig.dec) :
    Sign.Hom ((embed A.Φ).obj (pinSig A D)) A :=
  ⟨_root_.id, fun e he => hD e he, fun _ F hF => ⟨F, hF, FormSpec.Tightens.refl F⟩⟩

/-- **The corridor from the per-binary room of one image to the ISA room**: for a table `D`
that `A` decodes (the code of an image), per-binary sentences become `family` sentences of
`A`, and every model of `A` is a per-binary model of `D`. -/
def pin (V : Views σ) (A : Sign) (D : DTable A.Φ) (hD : ∀ e ∈ D, e ∈ A.sig.dec) :
    Silmaril.X86.Institution.room V (pinSig A D) ⟶ room V A :=
  embedCorridor V (pinSig A D) ≫ (inst V).map (pinHom A D hD)

end Silmaril.X86.BinInstitution
