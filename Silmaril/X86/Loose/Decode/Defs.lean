module

public import Silmaril.X86.Loose.Defs
public import Silmaril.X86.Ext9.Defs
public import Silmaril.X86.Sse9.Defs
public import Silmaril.X86.Float.Encoding

/-!
# Decode tables of the loose x86 specification: lookup and checks

`Loose/Defs.lean` defines the address-free decode table `DTable Φ` (exact byte strings and
their forms) and `AtEntry`. This module adds what a table built from an image needs:

* `Form`: the form index of an image listing's loose part, `int Ext9.Instr | xmm Sse9.Instr |
  float Float.Instr`: an integer form of `Ext9`, an SSE move of `Sse9`, or a scalar
  floating-point form of `Silmaril.X86.Float`. Everything in the loose machine is parametric
  in the form index `Φ`; `Form` is the index of the tables that `Loose.Listing` builds.
* `AtListed D V s`: some entry of `D` is at `rip`.
* `DTable.lookup D bytes`: the table as a decoder. It never decodes the empty string.
* Decidable sanity checks: `DTable.prefixFree` (no entry is empty or a proper prefix of
  another), `DTable.functional` (equal bytes have equal forms), and `DTable.okExt9`,
  `DTable.okSse9`, `DTable.okFloat` (each entry of that kind is what the corresponding
  decoder reads, at the entry's full length).
-/

@[expose] public section

namespace Silmaril.X86.Loose

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Views)

/-- **The form index of a listing's loose part**: an integer form of `Ext9`, an SSE move of
`Sse9`, or a scalar floating-point form of `Silmaril.X86.Float`. -/
inductive Form where
  | int (i : Silmaril.X86.Ext9.Instr)
  | xmm (i : Silmaril.X86.Sse9.Instr)
  | float (i : Silmaril.X86.Float.Instr)
  deriving DecidableEq

variable {Φ σ : Type}

instance (e : DEntry Φ) (c : State) (m : Memory) : Decidable (AtEntry e c m) :=
  inferInstanceAs (Decidable (_ = _))

/-- Some entry of `D` is at the `rip` of `s`. -/
def AtListed (D : DTable Φ) (V : Views σ) (s : σ) : Prop :=
  ∃ e ∈ D, AtEntry e (V.core s) (V.mem s)

/-- The first entry whose bytes are exactly `bytes` (never for the empty string). -/
def DTable.find (D : DTable Φ) (bytes : List Byte) : Option (DEntry Φ) :=
  if bytes = [] then none else D.find? fun e => decide (e.bytes = bytes)

/-- **The table as a decoder**: a lookup. -/
def DTable.lookup (D : DTable Φ) (bytes : List Byte) : Option (Φ × Nat) :=
  (D.find bytes).map fun e => (e.form, bytes.length)

/-- Every entry is non-empty, and no entry's bytes are a proper prefix of another's (x86
decoding is prefix-free). An empty entry would be at every `rip` (`fetchBytes a 0 = some []`),
so it is rejected. -/
def DTable.prefixFree (D : DTable Φ) : Bool :=
  D.all (fun e => !e.bytes.isEmpty) &&
    D.all fun e => D.all fun e' => !(e.bytes ≠ e'.bytes && e.bytes.isPrefixOf e'.bytes)

/-- No two entries have the same bytes and different forms. -/
def DTable.functional [DecidableEq Φ] (D : DTable Φ) : Bool :=
  D.all fun e => D.all fun e' => !(e.bytes = e'.bytes && e.form ≠ e'.form)

/-- Every integer entry is what `Ext9.decode` reads, at its full length. -/
def DTable.okExt9 (D : DTable Form) : Bool :=
  D.all fun e => match e.form with
    | .int i => decide (Silmaril.X86.Ext9.decode e.bytes = some (i, e.bytes.length))
    | _ => true

/-- Every SSE entry is what the `Sse9` listing decoder reads, at its full length. -/
def DTable.okSse9 (D : DTable Form) : Bool :=
  D.all fun e => match e.form with
    | .xmm i => decide (Silmaril.X86.Sse9.decodeL e.bytes = some (i, e.bytes.length))
    | _ => true

/-- Every floating-point entry is what `Silmaril.X86.Float.decode` reads, at its full
length. -/
def DTable.okFloat (D : DTable Form) : Bool :=
  D.all fun e => match e.form with
    | .float i => decide (Silmaril.X86.Float.decode e.bytes = some (i, e.bytes.length))
    | _ => true

end Silmaril.X86.Loose
