module

public import Silmaril.Project.Shapes.CompilesTo.Defs
public import Silmaril.Project.CompilesTo.Thms
public import Silmaril.Project.Shapes.C.Thms
public import Silmaril.X86.Open9.Thms
import Silmaril.Proofs.Project.Shapes.CompilesTo

/-! # Standard problem shapes: C functions, segment by segment (theorems)

* **`FnData.compilesTo_of_segments`**: the segment rows of a function (`c.compiles_to.segment`,
  every point), its placement's `Enterable`, and the safety of its C function on some argument
  tuple from every entry (`F.cfn.meaning.Inhabited`) give its `c.compiles_to` row on
  `Silmaril.X86.Open.isa`. The composition runs to the **first** return: each segment run stops
  at its first cut point, and no point is a return (`FnData.notFinal`).
* **`FnData.compilesToCanonical_of_segments`**: the same with the canonical entry, where
  non-vacuity is the safety of one state (`c.compiles_to.canonical_entry`).
* `C.CompilesTo.of_canonical`: a canonical row and `F.meaning.Inhabited` give the standard row, so
  universal safety is exactly what a canonical row lacks.
* `CFn.canonicalEntry_entry`: the canonical entry of a function with at most six `int`
  parameters is a Core entry. `CFn.meaning_eq`: the standard meaning is `meaningFrom` the Core
  entries.
* `C.CompilesTo.open9_of_open`, `CompilesToCanonical.open9_of_open`: from `Open.isa` to
  `Open9.isa`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.CompilesTo

open Silmaril.Project.CompilesTo
open Silmaril.Project.Shapes.C (CFn)
open Silmaril.X86.SystemV.CApi (Signature Arguments)

/-- The standard meaning of a C function is its meaning from every Core entry. -/
theorem _root_.Silmaril.Project.Shapes.C.CFn.meaning_eq {sig : Signature} (F : CFn sig) :
    F.meaning = F.meaningFrom F.Entry := rfl

/-- **The canonical entry is a Core entry** (at most six `int` parameters, distinct keys). -/
theorem _root_.Silmaril.Project.Shapes.C.CFn.canonicalEntry_entry {sig : Signature}
    (F : CFn sig) (hint : ∀ k ∈ sig.arguments, k = .int32)
    (hlen : F.params.length = sig.arguments.length) (hsix : sig.arguments.length ≤ 6)
    (hnd : (F.params.map (·.1.key)).Nodup) (a : Arguments sig.arguments) :
    F.Entry a (F.canonicalEntry a) :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.canonicalEntry_entry F hint hlen hsix hnd a

/-- **No related state at a point is a return.** -/
theorem _root_.Silmaril.Project.CompilesTo.FnData.notFinal (F : FnData) (I : Model) (k0 : List Silmaril.Cerberus.Core.Dynamics.Frame) :
    ∀ k x0 s x, (F.corr I k0).rel k x0 s x → ¬ (F.corr I k0).tgtFinal x0 x :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.FnData.notFinal F I k0

/-- **The segments give the `c.compiles_to` row** (on `Open.isa`), with the C function's safety on
some argument tuple from every entry (`F.cfn.meaning.Inhabited`). -/
theorem _root_.Silmaril.Project.CompilesTo.FnData.compilesTo_of_segments (F : FnData) (haddr : F.addr < 2 ^ 64)
    (hp0 : F.points[0]? = some ⟨F.body, 0, .entry⟩)
    (hseg : ∀ k, F.Segment Silmaril.X86.Open.isa k)
    (henter : Silmaril.Project.Shapes.SysV.Enterable Silmaril.X86.Open.isa F.placement F.sig
      F.frame)
    (hint : ∀ k ∈ F.sig.arguments, k = .int32) (hlen : F.params.length = F.sig.arguments.length)
    (hsix : F.sig.arguments.length ≤ 6) (hnd : (F.params.map (·.1.key)).Nodup)
    (hsafe : F.cfn.meaning.Inhabited) :
    Silmaril.Project.Shapes.C.CompilesTo Silmaril.X86.Open.isa F.placement F.frame F.cfn :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.FnData.implements_of_segments F F.cfn.Entry
    (fun _ _ h => h) (fun a => ⟨_, F.cfn.canonicalEntry_entry hint hlen hsix hnd a⟩) haddr hp0
    hseg henter hsafe

/-- **The segments give the `c.compiles_to.canonical_entry` row** (on `Open.isa`), with the
safety of the canonical entry for one argument tuple. -/
theorem _root_.Silmaril.Project.CompilesTo.FnData.compilesToCanonical_of_segments (F : FnData) (haddr : F.addr < 2 ^ 64)
    (hp0 : F.points[0]? = some ⟨F.body, 0, .entry⟩)
    (hseg : ∀ k, F.Segment Silmaril.X86.Open.isa k)
    (henter : Silmaril.Project.Shapes.SysV.Enterable Silmaril.X86.Open.isa F.placement F.sig
      F.frame)
    (hint : ∀ k ∈ F.sig.arguments, k = .int32) (hlen : F.params.length = F.sig.arguments.length)
    (hsix : F.sig.arguments.length ≤ 6) (hnd : (F.params.map (·.1.key)).Nodup)
    (a : Arguments F.sig.arguments) (hsafe : (F.cfn.source []).Safe (F.cfn.canonicalEntry a)) :
    CompilesToCanonical Silmaril.X86.Open.isa F.placement F.frame F.cfn :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.FnData.implements_of_segments F
    (fun a s => s = F.cfn.canonicalEntry a)
    (fun a _ h => h ▸ F.cfn.canonicalEntry_entry hint hlen hsix hnd a) (fun _ => ⟨_, rfl⟩)
    haddr hp0 hseg henter ⟨a, fun _ h => h ▸ hsafe⟩

/-- **A canonical row with universal safety is a standard row.** -/
theorem _root_.Silmaril.Project.Shapes.C.CompilesTo.of_canonical {sig : Signature} {M : Model}
    {p : Silmaril.Project.Shapes.Placement} {frame : Nat} {F : CFn sig}
    (hentry : ∀ a, F.Entry a (F.canonicalEntry a)) (h : CompilesToCanonical M p frame F)
    (hs : F.meaning.Inhabited) : Silmaril.Project.Shapes.C.CompilesTo M p frame F :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.compilesTo_of_canonical hentry h hs

/-- `c.compiles_to` on `Open.isa` gives it on `Open9.isa`. -/
theorem _root_.Silmaril.Project.Shapes.C.CompilesTo.open9_of_open {sig : Signature} {p : Silmaril.Project.Shapes.Placement}
    {frame : Nat} {F : CFn sig}
    (h : Silmaril.Project.Shapes.C.CompilesTo Silmaril.X86.Open.isa p frame F) :
    Silmaril.Project.Shapes.C.CompilesTo Silmaril.X86.Open9.isa p frame F :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.implements_open9_of_open h

/-- `c.compiles_to.canonical_entry` on `Open.isa` gives it on `Open9.isa`. -/
theorem CompilesToCanonical.open9_of_open {sig : Signature}
    {p : Silmaril.Project.Shapes.Placement} {frame : Nat} {F : CFn sig}
    (h : CompilesToCanonical Silmaril.X86.Open.isa p frame F) :
    CompilesToCanonical Silmaril.X86.Open9.isa p frame F :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.implements_open9_of_open h

end Silmaril.Project.Shapes.CompilesTo

end
