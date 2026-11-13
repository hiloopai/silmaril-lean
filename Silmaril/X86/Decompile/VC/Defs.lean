module

public import Silmaril.X86.Ext.Loop
public import Silmaril.X86.Ext.SymExec
public import Silmaril.X86.Decompile.Lift.Defs
public import Silmaril.Machine.CBackend.RTL.VC.Thms
public import Silmaril.Machine.X86.Decompile.SemLift.Defs
public import Silmaril.X86.SegVC

/-!
# A cut-point VC generator for x86-64 machine code, sound for total correctness

The machine-code stage of the imported translation-validation work.
The target is `Silmaril.X86.Ext` unchanged: the fetch/decode/execute machine `Ext.step`
over a loaded code image, with `Ext.Returns` as the meaning of "the function returns".

The **lifted program** is a *listing*: byte offset ↦ (instruction, length), proposed by any
untrusted lifter (objdump, the decompile ladder, an agent) and accepted by
`Listing.valid`, which re-decodes every entry with Silmaril's own decoder
(`Ext.decode`, which re-encodes what it reads). A function is annotated Floyd-style with
**cut points** (byte offsets of loop heads), each with an invariant over the whole machine
state and a `Nat` measure, as in `Silmaril.Machine.CBackend.RTL.VC.vc`.

`wpN` executes the listing symbolically (by `simp`, through `Ext.exec`) from an offset until
it reaches a cut point or the `ret` to the designated exit address, along both successors of
every conditional branch. `vc` asks this from the entry (under the precondition) and from
every cut point (under its invariant).

`sound`: if the listing is valid and `vc` holds, the function, entered at its entry with the
image loaded and the precondition true, **returns** (`Ext.Returns`: no fault, no trap, no
divergence) into the postcondition, and *every* return satisfies the postcondition
(`Ext.Returns.eq_of_reaches`, determinism). Memory that the code writes must stay outside the
image (a `Loaded` obligation after every step); calls are not supported.
-/

@[expose] public section
namespace Silmaril.X86.Decompile.VC

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext

/-- A lifted instruction listing: byte offset ↦ (instruction, encoded length). -/
abbrev Listing := List (Nat × Ext.Instr × Nat)

/-- The listing is what Silmaril's decoder reads from `code` at every listed offset. -/
def Listing.valid (code : List Byte) (L : Listing) : Bool :=
  L.all fun e => decide (Ext.decode ((code.drop e.1).take e.2.2) = some (e.2.1, e.2.2)) &&
    decide (e.1 + e.2.2 ≤ code.length)

/-- A cut point's annotation. -/
structure Cut where
  inv : MState → Prop
  measure : MState → Nat

/-- The measure bound on reaching a cut point: none from the entry. -/
def bound (μ : Option Nat) (w : Nat) : Prop :=
  match μ with
  | some μ => w < μ
  | none => True

section

variable (code : List Byte) (L : Listing) (cuts : List (Nat × Cut)) (base exit : Word)
  (post : MState → Prop)

/-- The offset of a state's RIP in the image. -/
def offOf (m : MState) : Nat := (m.core.rip - base).toNat

/-- Reaching the state `m`: the annotation of the cut point at its offset and the measure
bound, or else the continuation (the paths onward). -/
def nextP (μ : Option Nat) (cont : Nat → MState → Prop) (m : MState) : Prop :=
  match cuts.lookup (offOf base m) with
  | some c => c.inv m ∧ bound μ (c.measure m)
  | none => cont (offOf base m) m

/-- The weakest precondition of one listed instruction, given what reaching its successor
needs: it executes (no fault, defined flags for a branch), the image stays loaded, and a
`ret` returns to `exit` into the postcondition. -/
def wpI (next : MState → Prop) : Option (Ext.Instr × Nat) → MState → Prop
  | some (i, l), m =>
    match Ext.exec i m.core m.memory l with
    | .ok core mem =>
      Loaded mem base code ∧
        (if i = .ret then core.rip = exit ∧ post ⟨core, mem⟩ else next ⟨core, mem⟩)
    | _ => False
  | none, _ => False

/-- The weakest precondition of the paths from offset `o` to the next cut point or the
return, at most `k` instructions long. -/
def wpN (μ : Option Nat) : Nat → Nat → MState → Prop
  | 0, _, _ => False
  | k + 1, o, m => wpI code base exit post (nextP cuts base μ (wpN μ k)) (L.lookup o) m

/-- The VC of an annotated listing entered at offset `entry`: from the entry under the
precondition, and from every cut point under its invariant (paths at most `K` long). -/
def vc (entry : Nat) (pre : MState → Prop) (K : Nat) : Prop :=
  (∀ m : MState, Loaded m.memory base code → m.core.rip = base + BitVec.ofNat 64 entry →
    pre m → wpN code L cuts base exit post none K entry m) ∧
  (∀ oc ∈ cuts, ∀ m : MState, Loaded m.memory base code →
    m.core.rip = base + BitVec.ofNat 64 oc.1 → oc.2.inv m →
    wpN code L cuts base exit post (some (oc.2.measure m)) K oc.1 m)

/-- What the paths from `m` reach: a return into the postcondition, or a cut point whose
annotation holds within the measure bound, with the image loaded. -/
def Reach (μ : Option Nat) (m : MState) : Prop :=
  (∃ m' fin, Ext.Reaches exit m m' ∧ Ext.step exit m' = .returned fin ∧ post fin) ∨
  (∃ o c m', cuts.lookup o = some c ∧ c.inv m' ∧ bound μ (c.measure m') ∧ Reaches exit m m' ∧
    m'.core.rip = base + BitVec.ofNat 64 o ∧ Loaded m'.memory base code)

end

variable {code : List Byte} {L : Listing} {cuts : List (Nat × Cut)} {base exit : Word}
  {post : MState → Prop}

end Silmaril.X86.Decompile.VC

/-! The checked decompiler's RTL VC interface. The theorem in `Thms` composes
accepted lift and abstraction certificates with a proved RTL contract. -/

namespace Silmaril.X86.Decompile.VC

open Silmaril.X86 (Byte Word MState)
open Silmaril.X86.Decompile.SemLift

/-- Semantic block lifting's actual entry obligations: loaded bytes, no address
wrap, backed reads, writable stores, code separation, and declared aliases.
These conditions refer to the entry state and are never inferred from a
successful summary comparison. -/
structure BlockPre (code : List Byte) (base : Word) (summary : Summary)
    (initial : MState) : Prop where
  fits : base.toNat + code.length ≤ 2 ^ 64
  loaded : Silmaril.X86.Ext.Loaded initial.memory base code
  pc : initial.core.rip = base
  reads : ∀ access ∈ summary.reads,
    (Silmaril.X86.Ext.loadN initial.memory
      (access.1.eval initial.core initial.memory) access.2).isSome
  writes : ∀ store ∈ summary.stores,
    initial.memory.Permitted .write
      (store.1.eval initial.core initial.memory).toNat store.2.1
  codeClear : ∀ store ∈ summary.stores,
    base.toNat + code.length ≤ (store.1.eval initial.core initial.memory).toNat ∨
      (store.1.eval initial.core initial.memory).toNat + store.2.1 ≤ base.toNat
  aliases : AssumeHolds initial.core initial.memory summary.assume

/-- The checked straight-line SSA expression graph, including its store order
and flag summary, interpreted over the actual entry state. -/
structure BlockPost (base : Word) (summary : Summary) (initial final : MState) : Prop where
  pc : final.core.rip = base + BitVec.ofNat 64 summary.len
  values : ∀ output ∈ summary.outs,
    final.core.read output.1 = output.2.eval initial.core initial.memory
  stores : applyStores initial.core initial.memory initial.memory summary.stores =
    some final.memory
  flags : summary.flags.Holds initial.core initial.memory final.core.flags

/-- An accepted semantic block lift is a proved sub-segment summary for the
public VC generator. Unlike recompilation-based lifting, this checker can
accept instruction selections from clang and gcc in its supported fragment.
Use the result in `SegVC`'s `subs` table; the caller must separately discharge
continuation-PC and whole-image-loading obligations. -/
def checked_block_summary (exit base : Word) (code : List Byte) (instructions : Nat)
    (summary : Summary) (accepted : SemLift.check code instructions summary = true) :
    Silmaril.X86.SegVC.Call (Silmaril.X86.SegVC.Isa.ext exit) where
  pre := BlockPre code base summary
  post := BlockPost base summary
  runs := by
    intro initial _ admitted
    obtain ⟨final, execution, pc, values, stores, flags⟩ :=
      SemLift.check_sound (exit := exit) accepted admitted.fits initial admitted.loaded admitted.pc
        admitted.reads admitted.writes admitted.codeClear admitted.aliases
    exact ⟨final, ⟨instructions, execution⟩, pc, values, stores, flags⟩

end Silmaril.X86.Decompile.VC
