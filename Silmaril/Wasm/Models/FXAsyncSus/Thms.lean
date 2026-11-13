module

public import Silmaril.Proofs.Wasm.Models.FXAsyncSus.Example

/-!
# The asyncify kernel and `StepFX'` with `suspend`: the tight fragment

`Silmaril.Wasm.Models.FXAsyncBack.beh_eq` (the converse of `kernel_in_fx`) holds on the calm
fragment, where no `suspend` is executed, and `suspend_nondet` shows that `StepFX'` is not
deterministic at `suspend`: any suffix of the values in front of it can be the payload. So the
calm statement does not extend by determinism. The restatement proved here keeps `suspend` and
asks that **every executed `suspend t n` finds exactly its `n` payload values on its frame**
(`TightSupported`). Then every other choice of `StepFX'` at a `suspend` is a dead end:

* `step_sus`: a step of code whose deep focus is a `suspend` is the `suspend` rule at some
  handler frame (no other rule applies);
* `canon_unique`: the captured context is fixed by the code up to the payload split (canonical
  forms of contexts);
* `sus_unique`: only the resumer's handler can take it (an inner handler for the tag would make
  the passed frames handle it, an outer one would see the resumer's handler);
* `inev_sus`: the full split is followed by a unique `br 0` to the related configuration; a
  shorter split leaves a `br 0` with fewer values than the handler label's arity, which is
  stuck and no result.

Statements (deterministic profile, no host calls, `Ok S W`, `Rel S W x c`):

* **`beh_eq_tight`**: `behavioursFX' … c = obsB '' beh (sstep W i32Test) x` on the tight
  fragment; `tight_of_calm` makes it an extension of `beh_eq`;
* **`ex_beh`** (non-vacuity): the generator program of `FXAsyncFX` (one `suspend`, resumed under
  a fresh handler) has exactly one `StepFX'` behaviour, returning `[3]`.

A `suspend` whose frame holds more than its payload is outside the fragment: `StepFX'` may then
also take a longer payload, which the `br 0` drops but the captured continuation loses. Whether
that changes behaviours is not decided here.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (SCfg Ins Prog sstep beh)
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (TightSupported)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (CalmSupported)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)} {o : GrowKind → Nat → Nat → Nat → Bool}

/-- **The calm fragment is tight.** -/
theorem tight_of_calm {x : SCfg Val} (h : CalmSupported W x) : TightSupported W x :=
  Silmaril.Proofs.Wasm.Models.FXAsyncSus.tight_of_calm h

/-- **Every `StepFX'` behaviour of the encoding is a kernel behaviour**, `suspend` included
(tight fragment). -/
theorem fx_in_kernel_tight (hP : S.P = Profile.deterministic o) (hH : S.host = noHost)
    (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : TightSupported W x) :
    ∀ b ∈ behavioursFX' S.P S.host S.fx c, ∃ ob ∈ beh (sstep W i32Test) x, obsB ob = b :=
  Silmaril.Proofs.Wasm.Models.FXAsyncSus.fx_in_kernel_tight S hP hH hok hR hsup

/-- **The `StepFX'` behaviours of the encoding are exactly the images of the kernel's**, on the
tight fragment. -/
theorem beh_eq_tight (hP : S.P = Profile.deterministic o) (hH : S.host = noHost)
    (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : TightSupported W x) :
    behavioursFX' S.P S.host S.fx c = obsB '' beh (sstep W i32Test) x :=
  Silmaril.Proofs.Wasm.Models.FXAsyncSus.beh_eq_tight S hP hH hok hR hsup

/-- **A suspending WasmFX program with exactly one `StepFX'` behaviour.** -/
theorem ex_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost Silmaril.Proofs.Wasm.Models.FXAsyncFX.exFx
      (fxInit (Silmaril.Proofs.Wasm.Models.FXAsyncFX.exS (Profile.deterministic o) noHost) 1 []) =
      {.returns [Val.i32 3]} :=
  Silmaril.Proofs.Wasm.Models.FXAsyncSus.ex_beh o

/-- info: 'Silmaril.Wasm.Models.FXAsyncSus.beh_eq_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms beh_eq_tight

/-- info: 'Silmaril.Wasm.Models.FXAsyncSus.ex_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ex_beh

end Silmaril.Wasm.Models.FXAsyncSus
