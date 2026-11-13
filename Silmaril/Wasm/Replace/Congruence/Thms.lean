module

public import Silmaril.Wasm.Replace.Congruence.Defs
public import Silmaril.Proofs.Wasm.Replace.Congruence.Diverges

/-!
# The replacement congruence over a reachability predicate (Wasm 1.0): theorems

Hypotheses throughout: `HostRespectsReplace host a b`, `StepClosed host Reach`,
`CallSimOn Reach host a b` and `SameFuncTypeOn Reach a b`.

* **`behavioursOf_replaceOn`**: from a store satisfying `Reach`, the replacement does not change
  the behaviours of any configuration. `behaviours_replaceOn` is the entry-point form.
* **`moduleEquiv_replaceOn`**: the replacement gives an equivalent module, at behaviour-set
  equality. This is the contentful form of silmaril-lean's `V1.Execution.moduleEquiv_replace`,
  whose hypothesis `∀ s, CallSim host a b s` forces `a = b` (`eq_of_forall_callSim`).
  `Silmaril.Wasm.Replace.Example` instantiates this one at two distinct addresses holding distinct
  instances.
* `moduleRefines_replaceOn` and its corollaries at `TrapRefines`, `TrapDiv` and `TrapRefinesDiv`,
  by silmaril-lean's inclusion lattice; `moduleEquivOn_replace`, the congruence at every store
  satisfying `Reach`.

The proof (in `Silmaril.Proofs.Wasm.Replace.Congruence`) is a simulation that is step for step
except at an invocation of `a`, where it jumps the whole callee run using `CallSim`. Ported from
an earlier development `Silmaril/Wasm/Equiv/Congruence.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Replace

open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Equiv (moduleEquiv_eq_iff moduleRefines_trapRefines_of_eq
  moduleRefines_trapDiv_of_eq moduleRefines_trapRefinesDiv_of_trapRefines)

variable {H : Type}

/-- **The replacement is invisible from every configuration** over a store satisfying
`Reach`. -/
theorem behavioursOf_replaceOn {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {s : Store H} (hreach : Reach s) (f : Frame) (X : List Admin) :
    behavioursOf host ⟨s, f, X⟩ = behavioursOf host ⟨s.replaceFunc a b, f, X⟩ := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x (⟨c, r, hsteps, hcode, rfl⟩ | ⟨rfl, hdv⟩)
    · have hrun : SimFwd host a b c s f X :=
        (steps_replace_forward hhost hcl hsim htyp ⟨r, hcode⟩ hsteps s f X rfl hreach).2
      exact mem_behavioursOf hrun hcode
    · exact Or.inr ⟨rfl, diverges_replace_forward hhost hcl hsim htyp hreach hdv⟩
  · rintro x (⟨c, r, hsteps, hcode, rfl⟩ | ⟨rfl, hdv⟩)
    · obtain ⟨sd, -, hrun⟩ :=
        (steps_replace_backward hhost hcl hsim htyp ⟨r, hcode⟩ hsteps).2 s f X rfl hreach
      exact mem_behavioursOf (c' := ⟨sd, c.frame, c.code⟩) hrun hcode
    · exact Or.inr ⟨rfl, diverges_replace_backward hhost hcl hsim htyp hreach hdv⟩

/-- The entry-point form: the replacement does not change the behaviours of any invocation. -/
theorem behaviours_replaceOn {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {s : Store H} (hreach : Reach s) (c : FuncAddr) (vs : List Runtime.Value) :
    behaviours host s c vs = behaviours host (s.replaceFunc a b) c vs :=
  behavioursOf_replaceOn hhost hcl hsim htyp hreach ⟨[], {}⟩ (values vs ++ [AdminInstr.invoke c])

/-- **The replacement congruence over a reachability predicate.** Replacing `a` by a function
indistinguishable from it at the call boundary, at the stores satisfying `Reach`, gives an
equivalent module. -/
theorem moduleEquiv_replaceOn {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {s : Store H} (hreach : Reach s) :
    ModuleEquiv (· = ·) host s (s.replaceFunc a b) :=
  (moduleEquiv_eq_iff fun c vs => (invokeOk_replaceFunc (htyp s hreach) c vs).symm).mpr
    fun c vs _ => behaviours_replaceOn hhost hcl hsim htyp hreach c vs

/-- The refinement half of `moduleEquiv_replaceOn`. -/
theorem moduleRefines_replaceOn {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {s : Store H} (hreach : Reach s) :
    ModuleRefines (· = ·) host s (s.replaceFunc a b) :=
  (moduleEquiv_replaceOn hhost hcl hsim htyp hreach).1

/-- The congruence at trap-insertion refinement. -/
theorem moduleRefines_replaceOn_trapRefines {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {s : Store H} (hreach : Reach s) :
    ModuleRefines Behaviour.TrapRefines host s (s.replaceFunc a b) :=
  moduleRefines_trapRefines_of_eq _ (moduleRefines_replaceOn hhost hcl hsim htyp hreach)

/-- The congruence at trap ≈ divergence. -/
theorem moduleRefines_replaceOn_trapDiv {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {s : Store H} (hreach : Reach s) :
    ModuleRefines Behaviour.TrapDiv host s (s.replaceFunc a b) :=
  moduleRefines_trapDiv_of_eq _ (moduleRefines_replaceOn hhost hcl hsim htyp hreach)

/-- The congruence at trap insertion modulo divergence. -/
theorem moduleRefines_replaceOn_trapRefinesDiv {host : HostSemantics H}
    {Reach : Store H → Prop} {a b : FuncAddr} (hhost : HostRespectsReplace host a b)
    (hcl : StepClosed host Reach) (hsim : CallSimOn Reach host a b)
    (htyp : SameFuncTypeOn Reach a b) {s : Store H} (hreach : Reach s) :
    ModuleRefines Behaviour.TrapRefinesDiv host s (s.replaceFunc a b) :=
  moduleRefines_trapRefinesDiv_of_trapRefines _
    (moduleRefines_replaceOn_trapRefines hhost hcl hsim htyp hreach)

/-- **The congruence at every store satisfying `Reach`.** -/
theorem moduleEquivOn_replace {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b) :
    ∀ s : Store H, Reach s → ModuleEquiv (· = ·) host s (s.replaceFunc a b) :=
  fun _ hreach => moduleEquiv_replaceOn hhost hcl hsim htyp hreach

end Silmaril.Wasm.Replace
