module

public import Silmaril.X86.Institution.Defs
public import Silmaril.X86.Loose.Sv1
public import Silmaril.X86.Str9.Thms

/-!
# The exact signature `Σexact`, and the concrete machines as models

A concrete machine `I : SegVC.Isa σ` determines, for each of its instructions `i`, the
**exact form specification** `FormSpec.exact I i`: where `I.exec i` retires with its side
condition and keeps `fsBase`, exactly that successor; everywhere else unspecified. It is the
per-form semantics of the machine (`Ext9.execNew`, `Str9.execStr`) read as a form table.

* `FormSpec.exact I i`, `exactForms I : Sigma I.Instr`;
* `DTable.Decodes I D`: every entry of `D` is what `I.decode` reads, at its full length
  (`DTable.decodes I D` is the same check as a `Bool`, for `decide`);
* `exactSig I D : Sig I.Instr`: the signature of `D` with the exact forms of `I`.

For the open x86 machines, over the form index `Str9.Instr` (an `Ext9` instruction or a
string form):

* **`Sig.exact D`** (`Σexact`): `exactSig Str9.isa D`, the exact forms of `Str9`. On an
  `Ext9` form they are the exact forms of `Open9` (the executors agree);
* `Sig.sv1 D`: the loose signature `⟨D, Sv1⟩`;
* `DTable.okOpen9 D`: every entry is an `Ext9` form that `Open9.decode` reads at its full
  length (the table of an image that `Open9` runs).

`Σ v1` leaves flags undefined (PF and AF after the integer forms, the flags that `Ext`
leaves `none`), and an undefined flag may take any value (`FlagP.undef`). So `Σexact`, which
defines them, **tightens** `Σ v1` form by form, and the morphism `Sig.sv1 D ⟶ Sig.exact D`
exists as soon as each specified form of `Σ v1` is tightened by its exact form. That is a
per-family statement about `Ext9` and `Str9`:

* `AllowsExec F i`: the form `F` allows every result of `Str9.exec i` (success or fault);
  with `allows_fs` this is tightening by `FormSpec.exact Str9.isa i`;
* `Task.ctlAllows`, `Task.mulDivAllows`, `Task.intAllows`: every specified form of the group
  allows the results of `Ext9`. All three are proved (`ctlAllows`, `mulDivAllows`,
  `intAllows` in `Thms`), as are the string forms (`allowsExec_str`);
* `Task.sv1Tight`: every form of `Σ v1` is tightened by its exact `Str9` form; it follows
  from the three group tasks and the string forms (`sv1Tight_of` in `Thms`), so it holds
  (`sv1Tight`).
-/

@[expose] public section

namespace Silmaril.X86.Exact

open Silmaril.X86 (State Word Byte RelIsa)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Loose (FormSpec DTable EffSpec)
open Silmaril.X86.Institution (Sig)

variable {σ : Type}

/-- **The exact form specification** of instruction `i` of the machine `I`: where `I.exec i`
retires with the side condition `I.ok` and keeps `fsBase`, exactly that successor;
unspecified everywhere else. -/
def FormSpec.exact (I : Isa σ) (i : I.Instr) : FormSpec where
  unspecified c m l := ¬ ∃ c' m', I.exec i c m l = .ok c' m' ∧ I.ok i c' ∧ c'.fsBase = c.fsBase
  allows c m l c' m' := I.exec i c m l = .ok c' m' ∧ I.ok i c' ∧ c'.fsBase = c.fsBase
  allows_fs h := h.2.2
  nonempty h := Classical.not_not.1 h

/-- The exact forms of a machine: every instruction specified exactly. -/
def exactForms (I : Isa σ) : Loose.Sigma I.Instr := fun i => some (FormSpec.exact I i)

/-- Every entry of `D` is what `I.decode` reads, at its full length. -/
def DTable.Decodes (I : Isa σ) (D : DTable I.Instr) : Prop :=
  ∀ e ∈ D, I.decode e.bytes = some (e.form, e.bytes.length)

/-- `DTable.Decodes` as a `Bool`. -/
def DTable.decodes (I : Isa σ) (D : DTable I.Instr) : Bool :=
  D.all fun e => decide (I.decode e.bytes = some (e.form, e.bytes.length))

/-- The signature of a table with the exact forms of `I`. -/
def exactSig (I : Isa σ) (D : DTable I.Instr) : Sig I.Instr := ⟨D, exactForms I, {}⟩

/-! ## The open x86 machines -/

/-- **`Σexact`**: the exact forms of `Str9` over a table. -/
def Sig.exact (D : DTable Silmaril.X86.Str9.Instr) : Sig Silmaril.X86.Str9.Instr :=
  exactSig Silmaril.X86.Str9.isa D

/-- **`Σ v1`** over a table. -/
def Sig.sv1 (D : DTable Silmaril.X86.Str9.Instr) : Sig Silmaril.X86.Str9.Instr :=
  ⟨D, Loose.Sv1, {}⟩

/-- Every entry is an `Ext9` form that `Open9.decode` reads at its full length. -/
def DTable.okOpen9 (D : DTable Silmaril.X86.Str9.Instr) : Bool :=
  D.all fun e => match e.form with
    | .ext9 i => decide (Silmaril.X86.Open9.decode e.bytes = some (i, e.bytes.length))
    | .str _ => false

/-! ## The per-family conditions -/

/-- **A form of `Σ v1` allows the results of `Str9`**: at every core, memory and length, the
result of `Str9.exec i` (a success or a fault) is one the form allows. With
`FormSpec.allows_fs`, this is the tightening of the form by `FormSpec.exact Str9.isa i`
(`tightens_of_allowsExec` in `Thms`). -/
def AllowsExec (F : EffSpec) (i : Silmaril.X86.Str9.Instr) : Prop :=
  ∀ c m l, F.toFormSpec.sem c m l (Silmaril.X86.Str9.exec i c m l)

/-- Every `Ctl` form allows the results of `Ext9` (proved: `ctlAllows` in `Thms`). -/
def Task.ctlAllows : Prop :=
  ∀ i F, Loose.Ctl.ctlSpec i = some F → AllowsExec F (.ext9 i)

/-- Every `MulDiv` form allows the results of `Ext9` (proved: `mulDivAllows` in `Thms`). -/
def Task.mulDivAllows : Prop :=
  ∀ i F, Loose.Forms.MulDiv.specOf i = some F → AllowsExec F (.ext9 i)

/-- Every `Int` form allows the results of `Ext9` (proved: `intAllows` in `Thms`). -/
def Task.intAllows : Prop :=
  ∀ i F, Loose.Forms.spec9 i = some F → AllowsExec F (.ext9 i)

/-- **Every form of `Σ v1` is tightened by its exact `Str9` form** (proved: `sv1Tight` in
`Thms`). -/
def Task.sv1Tight : Prop :=
  ∀ i F, Loose.Sv1 i = some F → F.Tightens (FormSpec.exact Silmaril.X86.Str9.isa i)

end Silmaril.X86.Exact
