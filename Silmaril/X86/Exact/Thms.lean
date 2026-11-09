module

public import Silmaril.X86.Exact.Defs
public import Silmaril.X86.Institution.Thms
import Silmaril.Proofs.X86.Exact.Le
import Silmaril.Proofs.X86.Exact.Str
import Silmaril.Proofs.X86.Exact.Ctl

/-!
# `Σexact`: the concrete machines as models, and the morphism from `Σ v1`

Proofs are in `Silmaril/Proofs/X86/Exact/{Le,Str}.lean`.

**Any machine.**

* `le_top_of_tightens`: a machine `I` is below the top of a signature `G` (`RelIsa.Le`)
  when every entry of `G` is what `I.decode` reads and each of its specified forms is
  tightened by the exact form of `I`;
* `le_exact`, `exactModel`: so `ofIsa I` is a **model** of `exactSig I D` for every table `D`
  that `I` decodes (`DTable.Decodes`, decidable as `DTable.decodes`, `decodes_iff`);
* `tightens_of_allowsExec`: a form that allows every result of an executor is tightened by
  the executor's exact form.

**The open x86 machines** (over the form index `Str9.Instr`):

* `str9_le_exact`, `str9Model`: `Str9` is a model of `Sig.exact D` (`Σexact`) for every
  table `D` that `Str9.decode` reads;
* `open9_le_exact`, `open9Model`: **`Open9` is a model of `Sig.exact D`** for every table of
  `Ext9` forms that `Open9.decode` reads (`DTable.okOpen9`);
* `allowsExec_str`: every string form of `Σ v1` allows the results of `Str9`;
* `ctlAllows`: **`Task.ctlAllows` is proved**: every `Ctl` form allows the results of `Ext9`
  (where it is specified, `Ext9` retires to exactly the allowed successor);
* `sv1Tight_of`, `sv1Tight_of'`: `Task.sv1Tight` from the group tasks; with `Ctl` and the
  string forms proved, the open goals are `Task.mulDivAllows` and `Task.intAllows`;
* `sv1_le_exact`: given `Task.sv1Tight`, **the signature morphism `Sig.sv1 D ⟶ Sig.exact D`**;
* `open9Sv1Model`, `str9Sv1Model`, `sat_open9_of_sv1`, `sat_str9_of_sv1`: given
  `Task.sv1Tight`, `Open9` and `Str9` are models of `Σ v1` (by reduct), so every sentence
  that holds on the top of `Sig.sv1 D` holds on them.

The examples at the end check small tables with `decide`.
-/

@[expose] public section

namespace Silmaril.X86.Exact

open Silmaril.X86 (State MState Word Byte RelIsa)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.RelIsa (Views ofIsa Le)
open Silmaril.X86.Loose (DTable EffSpec)
open Silmaril.X86.Institution (Sig Model Sen Sat sat_of_top)

variable {σ Φ : Type}

/-! ## Any machine -/

/-- **A machine is below the top of a signature whose forms its exact forms tighten**, at
every listed entry. -/
theorem le_top_of_tightens (I : Isa σ) (G : Sig Φ)
    (h : ∀ e ∈ G.table, ∃ i, I.decode e.bytes = some (i, e.bytes.length) ∧
      ∀ F, G.forms e.form = some F → F.Tightens (FormSpec.exact I i)) :
    Le (ofIsa I) (G.top (Views.ofIsa I)) :=
  Proofs.X86.Exact.le_top_of_tightens I G h

theorem decodes_iff {I : Isa σ} {D : DTable I.Instr} :
    DTable.decodes I D = true ↔ DTable.Decodes I D := by
  simp [DTable.decodes, DTable.Decodes]

/-- **A machine is below the top of its exact signature** over a table it decodes. -/
theorem le_exact (I : Isa σ) (D : DTable I.Instr) (hD : DTable.Decodes I D) :
    Le (ofIsa I) ((exactSig I D).top (Views.ofIsa I)) :=
  le_top_of_tightens I _ fun e he =>
    ⟨e.form, hD e he, fun _ hF => Option.some.inj hF ▸ Loose.FormSpec.Tightens.refl _⟩

/-- **A machine is a model of its exact signature** over a table it decodes. -/
def exactModel (I : Isa σ) (D : DTable I.Instr) (hD : DTable.Decodes I D) :
    Model (Views.ofIsa I) (exactSig I D) :=
  ⟨ofIsa I, le_exact I D hD, RelIsa.progress_ofIsa⟩

/-- **From "allows the executor's results" to tightening**, when the executor's side
condition always holds. -/
theorem tightens_of_allowsExec {F : Loose.FormSpec} {I : Isa σ} {i : I.Instr}
    (hok : ∀ c m l c' m', I.exec i c m l = .ok c' m' → I.ok i c')
    (h : ∀ c m l, F.sem c m l (I.exec i c m l)) : F.Tightens (FormSpec.exact I i) :=
  Proofs.X86.Exact.tightens_of_sem hok h

/-! ## `Str9` and `Open9` as models of `Σexact` -/

section
variable {D : DTable Silmaril.X86.Str9.Instr}

/-- **`Str9` is below the top of `Σexact`** over a table that `Str9.decode` reads. -/
theorem str9_le_exact (hD : DTable.decodes Silmaril.X86.Str9.isa D = true) :
    Le (ofIsa Silmaril.X86.Str9.isa) ((Sig.exact D).top Views.mstate) :=
  le_exact _ _ (decodes_iff.1 hD)

/-- **`Open9` is below the top of `Σexact`** over a table of `Ext9` forms that
`Open9.decode` reads. -/
theorem open9_le_exact (hD : DTable.okOpen9 D = true) :
    Le (ofIsa Silmaril.X86.Open9.isa) ((Sig.exact D).top Views.mstate) :=
  Proofs.X86.Exact.open9_le_exact hD

/-- `Str9` as a model of `Σexact`. -/
def str9Model (hD : DTable.decodes Silmaril.X86.Str9.isa D = true) :
    Model Views.mstate (Sig.exact D) :=
  ⟨ofIsa Silmaril.X86.Str9.isa, str9_le_exact hD, RelIsa.progress_ofIsa⟩

/-- **`Open9` as a model of `Σexact`.** -/
def open9Model (hD : DTable.okOpen9 D = true) : Model Views.mstate (Sig.exact D) :=
  ⟨ofIsa Silmaril.X86.Open9.isa, open9_le_exact hD, RelIsa.progress_ofIsa⟩

end

/-! ## The morphism `Σ v1 ⟶ Σexact` -/

/-- **Every string form of `Σ v1` allows the results of `Str9`.** -/
theorem allowsExec_str (i : Silmaril.X86.Str9.Str) :
    AllowsExec (Loose.Forms.Str.strSpec i) (.str i) :=
  Proofs.X86.Exact.sem_str i

/-- **Every `Ctl` form allows the results of `Ext9`** (`Task.ctlAllows` holds). -/
theorem ctlAllows : Task.ctlAllows := Proofs.X86.Exact.Ctl.allowsExec_ctl

/-- **`Task.sv1Tight` from the three group tasks** (the string forms are proved). -/
theorem sv1Tight_of (hctl : Task.ctlAllows) (hmd : Task.mulDivAllows) (hint : Task.intAllows) :
    Task.sv1Tight := by
  intro i F h
  have key : ∀ {E : EffSpec} {j}, AllowsExec E j → E.toFormSpec.Tightens
      (FormSpec.exact Silmaril.X86.Str9.isa j) :=
    fun hE => tightens_of_allowsExec (fun _ _ _ _ _ _ => trivial) hE
  cases i with
  | str j =>
    cases h
    exact key (allowsExec_str j)
  | ext9 j =>
    obtain ⟨E, hE, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Loose.sv1Eff, Loose.intSpec] at hE
    cases hc : Loose.Ctl.ctlSpec j with
    | some E' =>
      rw [hc] at hE; cases hE; exact key (hctl j _ hc)
    | none =>
      rw [hc] at hE
      cases hm : Loose.Forms.MulDiv.specOf j with
      | some E' =>
        rw [hm] at hE; cases hE; exact key (hmd j _ hm)
      | none =>
        rw [hm] at hE; exact key (hint j E hE)

/-- **`Task.sv1Tight` from the two open group tasks** (`Ctl` and the string forms are
proved). -/
theorem sv1Tight_of' (hmd : Task.mulDivAllows) (hint : Task.intAllows) : Task.sv1Tight :=
  sv1Tight_of ctlAllows hmd hint

/-- **The signature morphism `Σ v1 ⟶ Σexact`**: `Σexact` lists the same table and tightens
every form of `Σ v1`. -/
theorem sv1_le_exact (h : Task.sv1Tight) (D : DTable Silmaril.X86.Str9.Instr) :
    Sig.sv1 D ≤ Sig.exact D :=
  ⟨fun _ he => he, fun i F hF => ⟨_, rfl, h i F hF⟩⟩

section
variable {D : DTable Silmaril.X86.Str9.Instr}

/-- **`Open9` is a model of `Σ v1`** (the reduct of `open9Model`). -/
def open9Sv1Model (h : Task.sv1Tight) (hD : DTable.okOpen9 D = true) :
    Model Views.mstate (Sig.sv1 D) :=
  (open9Model hD).reduct (sv1_le_exact h D)

/-- `Str9` is a model of `Σ v1` (the reduct of `str9Model`). -/
def str9Sv1Model (h : Task.sv1Tight) (hD : DTable.decodes Silmaril.X86.Str9.isa D = true) :
    Model Views.mstate (Sig.sv1 D) :=
  (str9Model hD).reduct (sv1_le_exact h D)

/-- **Every sentence of the top of `Σ v1` holds on `Open9`.** -/
theorem sat_open9_of_sv1 (h : Task.sv1Tight) (hD : DTable.okOpen9 D = true) {φ : Sen MState}
    (hφ : Sat ((Sig.sv1 D).top Views.mstate) φ) : Sat (ofIsa Silmaril.X86.Open9.isa) φ :=
  sat_of_top hφ (open9Sv1Model h hD)

/-- Every sentence of the top of `Σ v1` holds on `Str9`. -/
theorem sat_str9_of_sv1 (h : Task.sv1Tight)
    (hD : DTable.decodes Silmaril.X86.Str9.isa D = true) {φ : Sen MState}
    (hφ : Sat ((Sig.sv1 D).top Views.mstate) φ) : Sat (ofIsa Silmaril.X86.Str9.isa) φ :=
  sat_of_top hφ (str9Sv1Model h hD)

end

/-! ## Examples -/

/-- A `ret` table is an `Open9` table. -/
example : DTable.okOpen9 [⟨[0xC3], .ext9 (.ext8 (.base .ret))⟩] = true := by decide

/-- The three string encodings are a `Str9` table. -/
example : DTable.decodes Silmaril.X86.Str9.isa
    [⟨[0xA4], .str .movsb⟩, ⟨[0xF3, 0x48, 0xA5], .str .repMovsq⟩,
      ⟨[0xF3, 0x48, 0xAB], .str .repStosq⟩] = true := by decide

end Silmaril.X86.Exact
