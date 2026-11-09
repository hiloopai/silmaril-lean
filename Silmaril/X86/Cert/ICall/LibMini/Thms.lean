module

public import Silmaril.X86.Cert.ICall.Thms
public import Silmaril.X86.Ladder.LibMini.Thms

/-!
# Indirect-call blocks: non-vacuity with libmini's `strlen` as the callee

The callee half of an `icall` block's WP (`Cert.ICall.Post`) with a real callee: Γ is the
singleton environment at `0x400000` whose code is libmini's `strlen` (ladder rung 02),
interpreted as its strict (first-return) contract, moved to `Open9.isa`
(`Ladder.LibMini.strlen_strict`, `FnContract.Spec.Strict.toOpen9`), with the run predicate
"not yet returned".

* `strlenReq_valid`, `strlenΓ_valid`: the environment's entry is valid;
* `strlen_post_nonvacuous`: **a concrete callee entry state** (rung 02's witness) satisfies
  `Post` (function pointer, System V entry, `strlen`'s precondition, run predicate and
  results), and `post_runs` then gives a run to a `strlen` result; so the indirect-call WP is
  not vacuous on the callee side.

This file is separate from `Cert/ICall/Thms.lean` because it imports the ladder rung.
-/

@[expose] public section

namespace Silmaril.X86.Cert.ICall.LibMini

open Silmaril.X86.FnContract (Returned RunsIn Spec)
open Silmaril.X86.Ladder.LibMini (strlenCode)
open Silmaril.X86.Stencils.ByteLoop (scanContract)

/-- libmini's `strlen` spec at load address `entry`, read at the first return: the stencil
contract `scanContract`, restricted to return addresses outside the code. -/
def strlenSpec (entry : Word) : Spec MState :=
  (scanContract strlenCode entry).restrict
    (FnContract.RetOutside Silmaril.X86.Open.isa entry strlenCode.length)

/-- `strlen` at `0x400000` as a requirement: its strict spec, with "not yet returned". -/
def strlenReq : Req MState := ⟨strlenSpec 0x400000, fun s m => ¬ Returned Open9.isa s m⟩

theorem strlenReq_valid : strlenReq.Valid Open9.isa :=
  (Ladder.LibMini.strlen_strict 0x400000).toOpen9

/-- The interpretation: the one code is `strlen`. -/
def strlenJ : Silmaril.X86.Link.Env.Env Unit → Unit → Req MState := fun _ _ => strlenReq

theorem strlenΓ_valid :
    ∀ a c, single 0x400000 a c → (strlenJ (single 0x400000) c).Valid Open9.isa :=
  fun _ _ _ => strlenReq_valid

/-- **Non-vacuity of the callee side**: a concrete callee entry state satisfies `Post` for
`strlen` through Γ, and the callee then runs to a `strlen` result. -/
theorem strlen_post_nonvacuous : ∃ m1 : MState,
    Post (I := Open9.isa) strlenJ (single 0x400000) strlenReq (fun _ => True)
      (fun t => strlenReq.spec.Result Open9.isa m1 t) m1 ∧
    ∃ t, RunsIn Open9.isa (fun _ => True) m1 t ∧ strlenReq.spec.Result Open9.isa m1 t := by
  obtain ⟨m, hab, he, -⟩ := Ladder.LibMini.strlen_strict_nonvacuous
  have hrip : m.core.rip = 0x400000 := he.1.1
  have hp : Post (I := Open9.isa) strlenJ (single 0x400000) strlenReq (fun _ => True)
      (fun t => strlenReq.spec.Result Open9.isa m t) m :=
    ⟨⟨(), by show m.core.rip.toNat = 0x400000; rw [hrip]; rfl, Req.Sub.refl _⟩, hab, he,
      fun _ _ => trivial, fun _ h => h⟩
  exact ⟨m, hp, post_runs strlenΓ_valid trivial hp⟩

end Silmaril.X86.Cert.ICall.LibMini
