module

public import Silmaril.Project.Shapes.C.Defs
public import Silmaril.Project.Shapes.SysV.Thms
import Silmaril.Proofs.Project.Shapes.C

/-! # Standard problem shapes: C functions (theorems)

* **`CompilesTo.of_lift`** (the composition, proved once): a row of `sysv.lifts` (this IR
  function is a lift of that placed machine function) and a row of `c.ir_refines` (this IR
  function corresponds to that C function) give the row of `c.compiles_to` (the placed machine
  function implements the C function): **x86 to IR and IR to C give x86 to C**.
* `CompilesTo.implements`: a `c.compiles_to` row is a `sysv.implements` row for the C function's
  Cerberus meaning (by definition), so the x86-to-C statement is the function-level translation
  validation shape for a C source.
* `CompilesToBuilds.of_lifts`: same source, several builds: a lift per build, each with its
  correspondence to the C function, give the row of `c.compiles_to.builds`.
* `CompilesTo.not_of_never_safe`: a C function that is never safe has no `compiles_to` row.
* `CFn.safe_of_final`: a returned state of a call with the empty continuation is safe (Core
  pops the procedure frame and halts with the defined value). `CFn.not_safe_of_final_mainNext`:
  with a continuation that goes wrong it is not, which is why `CFn.meaning` fixes the empty
  continuation.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.C

open Silmaril.X86.SystemV.CApi (Signature)
open Silmaril.Project.Shapes.SysV (Meaning Ir Lifts Implements)

/-- **x86 to IR and IR to C give x86 to C.** -/
theorem CompilesTo.of_lift {M : Model} {p : Placement} {frame : Nat} {I : Ir} {f : I.Fn}
    {F : CFn (I.sig f)} (hlift : Lifts M p frame I f) (hc : IrRefines I f F) :
    CompilesTo M p frame F :=
  hlift.implements_of_refines hc.1 hc.2

/-- A `c.compiles_to` row is the `sysv.implements` row for the C function's meaning. -/
theorem CompilesTo.implements {sig : Signature} {M : Model} {p : Placement} {frame : Nat}
    {F : CFn sig} (h : CompilesTo M p frame F) : Implements M p sig frame F.meaning := h

/-- **A C function that is never safe has no `compiles_to` row.** -/
theorem CompilesTo.not_of_never_safe {sig : Signature} {M : Model} {p : Placement}
    {frame : Nat} {F : CFn sig} (h : ∀ a, ¬ F.meaning.Safe a) : ¬ CompilesTo M p frame F :=
  SysV.Implements.not_of_never_safe h

/-- **One build's lift**: the build, the IR its machine code was lifted to, and the IR
function. -/
structure LiftedBuild (sig : Signature) where
  build : Build
  ir : Ir
  fn : ir.Fn
  sig_eq : ir.sig fn = sig

/-- **Same source, several builds**: if every build's code is lifted to an IR function that
corresponds to the C function `F`, every build implements `F`. -/
theorem CompilesToBuilds.of_lifts {sig : Signature} {M : Model} {F : CFn sig}
    (builds : List (LiftedBuild sig))
    (hlift : ∀ b ∈ builds, Lifts M b.build.placement b.build.frame b.ir b.fn)
    (hc : ∀ b ∈ builds, IrRefines b.ir b.fn (cast (congrArg CFn b.sig_eq.symm) F)) :
    CompilesToBuilds M F (builds.map (·.build)) := by
  intro b hb
  obtain ⟨lb, hlb, rfl⟩ := List.mem_map.mp hb
  have h := CompilesTo.of_lift (hlift lb hlb) (hc lb hlb)
  obtain ⟨build, ir, fn, sig_eq⟩ := lb
  subst sig_eq
  exact h

/-! ## After the return -/

/-- **A returned call is safe** (the empty caller continuation): Core pops the procedure frame
and halts with the defined value, so nothing after the return can go wrong. -/
theorem CFn.safe_of_final {sig : Signature} {F : CFn sig} {s : Silmaril.Cerberus.Core.Dynamics.State}
    {v : Silmaril.Cerberus.Core.Dynamics.Val} (h : (F.source []).final s v) :
    (F.source []).Safe s :=
  Silmaril.Proofs.Project.Shapes.C.safe_of_final h

/-- **A continuation that goes wrong makes a returned state unsafe**: Core runs on in the
caller's continuation after the return, here a `mainNext` frame outside the startup sequence,
which ends the run with an error. A meaning quantified over every continuation would therefore
be safe on no argument tuple; `CFn.meaning` fixes the empty one. -/
theorem CFn.not_safe_of_final_mainNext {sig : Signature} {F : CFn sig}
    {p : Silmaril.Cerberus.Mem.Concrete.Pointer} {w : Silmaril.Cerberus.Core.Dynamics.Val}
    {s : Silmaril.Cerberus.Core.Dynamics.State} {v : Silmaril.Cerberus.Core.Dynamics.Val}
    (h : (F.source [.mainNext p (.value w)]).final s v) :
    ¬ (F.source [.mainNext p (.value w)]).Safe s :=
  Silmaril.Proofs.Project.Shapes.C.not_safe_of_final_mainNext h

end Silmaril.Project.Shapes.C

end
