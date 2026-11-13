module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.Example
public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.Refute

/-!
# The converse of `kernel_in_fx`: `StepFX'` behaviours of the encoding are kernel behaviours

`Silmaril.Wasm.Models.FXAsyncFX.kernel_in_fx` shows that every behaviour of the asyncify handler
kernel, on the fragment, is a `StepFX'` behaviour of its WasmFX encoding. This module proves the
converse on the **calm fragment** (no `suspend` is executed; `resume`, of fresh and captured
continuations, is covered), in the deterministic profile and without host calls, so the two
behaviour sets are equal.

The proof is a backward simulation by inversion of `StepFX'` under contexts:

* `Silmaril.Proofs.Wasm.Models.FXAsyncBack.stepFX'_decomp`: every `StepFX'` step is a head step at
  the first non-value of the code (under a value prefix and a suffix), or the code has a trap or
  `throw_ref` there;
* `step_plug_inv`: a step of `E.plug X`, for an isolated context `E` and quiet code `X`, is a
  step of `X` lifted through `E`; `iso_outer`: the context of an encoded stack around its top
  frame is isolated;
* `head_plain_det`: Core head steps of a plain instruction are deterministic in the
  deterministic profile (Silmaril gives this only up to joinability);
* the unique local steps of every encoded instruction (`uniq_core`, `uniq_invoke`, `uniq_block`,
  `uniq_ifTrue`, `uniq_brZero`, ...), assembled into paths of unique steps for `push`, `prim`,
  `drop`, `contNew`, `call`, `cond`, `resume` and returns, through every waiting context
  (`umatched_top`);
* `fx_sub_kernel`: inevitability of the next related configuration gives inclusion of the
  `StepFX'` behaviours (finite runs by a decreasing run length, divergence by induction on the
  kernel's steps).

Statements:

* **`fx_in_kernel`**: every `StepFX'` behaviour of a related configuration is `obsB` of a kernel
  behaviour (hypotheses: `S.P = Profile.deterministic o`, `S.host = noHost`, `Ok S W`,
  `Rel S W x c`, `CalmSupported W x`);
* **`beh_eq`**: with `kernel_in_fx`, `behavioursFX' … c = obsB '' beh (sstep W i32Test) x`;
* **`add_beh`**, **`res_beh`** (non-vacuity): a one-function program (`1 + 2`) and a program
  that resumes a fresh continuation which returns `5` each have exactly one `StepFX'` behaviour.

**Refutation** (`suspend_split`): `StepFX'` is not deterministic at `suspend`: a non-empty
payload can be split anywhere, giving two different successors (`br_short_stuck`: a short split
whose branch carries fewer values than the handler label's arity is a dead end). So the converse
cannot come from determinism of `StepFX'` alone.

Not covered: `suspend` (the calm fragment excludes it); see "Stretch, fxasync (ws4 an earlier step)" in
`docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (CalmSupported addFx addS resFx resS)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)} {o : GrowKind → Nat → Nat → Nat → Bool}

/-- **Every `StepFX'` behaviour of the encoding is a kernel behaviour** (calm fragment,
deterministic profile, no host calls). -/
theorem fx_in_kernel (hP : S.P = Profile.deterministic o) (hH : S.host = noHost) (hok : Ok S W)
    {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c) (hsup : CalmSupported W x) :
    ∀ b ∈ behavioursFX' S.P S.host S.fx c, ∃ ob ∈ beh (sstep W i32Test) x, obsB ob = b :=
  Silmaril.Proofs.Wasm.Models.FXAsyncBack.fx_in_kernel S hP hH hok hR hsup

/-- **The `StepFX'` behaviours of the encoding are exactly the images of the kernel's.** -/
theorem beh_eq (hP : S.P = Profile.deterministic o) (hH : S.host = noHost) (hok : Ok S W)
    {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c) (hsup : CalmSupported W x) :
    behavioursFX' S.P S.host S.fx c = obsB '' beh (sstep W i32Test) x :=
  Silmaril.Proofs.Wasm.Models.FXAsyncBack.beh_eq S hP hH hok hR hsup

/-- **The WasmFX program `fxInit S W f args` behaves exactly as the kernel's call of `f`**. -/
theorem fxInit_beh_eq (hP : S.P = Profile.deterministic o) (hH : S.host = noHost)
    (hok : Ok S W) (f : Nat) (args : List Val)
    (hsup : CalmSupported W (sInit f (args.map .val))) :
    behavioursFX' S.P S.host S.fx (fxInit S f args) =
      obsB '' beh (sstep W i32Test) (sInit f (args.map .val)) :=
  beh_eq S hP hH hok (rel_init S f args) hsup

/-- **Non-vacuity**: `1 + 2` as a one-function WasmFX program has exactly one `StepFX'`
behaviour. -/
theorem add_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost addFx
      (fxInit (addS (Profile.deterministic o) noHost) 0 []) = {.returns [Val.i32 3]} :=
  Silmaril.Proofs.Wasm.Models.FXAsyncBack.add_beh o

/-- **Non-vacuity with `resume`**: resuming a fresh continuation that returns `5`. -/
theorem res_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost resFx
      (fxInit (resS (Profile.deterministic o) noHost) 1 []) = {.returns [Val.i32 5]} :=
  Silmaril.Proofs.Wasm.Models.FXAsyncBack.res_beh o

/-- **`StepFX'` is not deterministic at `suspend`**: two different successors of one
configuration, splitting the payload `v :: vs` differently. -/
theorem suspend_nondet {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause} {E : CtxV}
    {v : FVal} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    ∃ d₁ d₂, StepFX' P host fx
        ⟨s, K, f, [.handler hs (E.plug (fvals (v :: vs) ++ [.fx (.suspend x)]))]⟩ d₁ ∧
      StepFX' P host fx
        ⟨s, K, f, [.handler hs (E.plug (fvals (v :: vs) ++ [.fx (.suspend x)]))]⟩ d₂ ∧ d₁ ≠ d₂ :=
  let h := Silmaril.Proofs.Wasm.Models.FXAsyncBack.suspend_split (P := P) (host := host) (fx := fx)
    (K := K) (v := v) (vs := vs) ht hE hc
  ⟨_, _, h.1, h.2.1, h.2.2⟩

/-- info: 'Silmaril.Wasm.Models.FXAsyncBack.beh_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms beh_eq

/-- info: 'Silmaril.Wasm.Models.FXAsyncBack.add_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_beh

/-- info: 'Silmaril.Wasm.Models.FXAsyncBack.res_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms res_beh

end Silmaril.Wasm.Models.FXAsyncBack
