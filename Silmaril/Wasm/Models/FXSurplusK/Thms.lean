module

public import Silmaril.Proofs.Wasm.Models.FXSurplusK.Tight

/-!
# Surplus `suspend` operands on the encoded asyncify kernel fragment

`Silmaril.Wasm.Models.FXAsyncSus.beh_eq_tight` equates the `StepFX'` behaviours of the encoding of
`Silmaril.Wasm.Models.FXAsyncFX` with the images of the kernel's when every executed `suspend`
finds exactly its payload on its frame (tight). This module settles the case it left open,
a `suspend` whose frame holds more (statements and proofs in
`Silmaril.Proofs.Wasm.Models.FXSurplusK`):

* **`sim_suspend_ex`**, **`matched_suspend_ex`**: when the kernel frame holds `pl ++ ex ++ o`
  (top first) at `suspend t (ar t)`, the FX `suspend` with payload `ex ++ pl` followed by the
  `br 0` out of `block btH` reaches a configuration related (`Rel`) to the kernel's step from
  the configuration with `ex` deleted (`withOps x (pl ++ o)`);
* **`surplus_in_fx`**: so every kernel behaviour from that configuration (in the fragment) is a
  `StepFX'` behaviour of the encoding;
* **`sk_not_beh_eq`** (refutation): surplus operands **add behaviours**. A program `skW` in a
  concrete setting with `Ok`, `Rel` and `Supported` (for every profile and host) has the
  kernel behaviour `[21]` only (`sk_kernel_beh`), and the `StepFX'` behaviours `[21]`
  (`sk_fx_21`) and `[11]` (`sk_fx_11`): the surplus payload loses an operand of a frame that
  never returns, and a later `suspend` yields a deeper operand instead;
* **`sk_not_tight`**: hence that kernel run is not tight, and the tight hypothesis of
  `beh_eq_tight` cannot be dropped.

A Silmaril addition (Follow-up 5 workflow, track fx).
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXSurplusK

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXSurplusK (skW skFx skS skInit)
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (TightSupported)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- **A surplus `suspend` behaves as the kernel without the surplus.** -/
theorem surplus_in_fx (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    {fr : SFrame Val} {rest : List (SFrame Val)} {t : Nat} {cd : List (Ins Val)}
    {pl ex o : List (SV Val)} (hx : x.stack = fr :: rest)
    (hc : fr.code = .suspend t (S.ar t) :: cd) (hops : fr.ops = pl ++ ex ++ o)
    (hpl : pl.length = S.ar t)
    (hsup : Supported W (Silmaril.Proofs.Wasm.Models.FXSurplusK.withOps x (pl ++ o))) :
    ∀ b ∈ beh (sstep W i32Test) (Silmaril.Proofs.Wasm.Models.FXSurplusK.withOps x (pl ++ o)),
      obsB b ∈ behavioursFX' S.P S.host S.fx c :=
  Silmaril.Proofs.Wasm.Models.FXSurplusK.surplus_in_fx S hok hR hx hc hops hpl hsup

/-- **Surplus operands add behaviours on the encoded kernel fragment.** -/
theorem not_beh_eq (P : Profile) (host : HostSemantics Nat) :
    Ok (skS P host) skW ∧ Rel (skS P host) skW skInit (fxInit (skS P host) 1 []) ∧
      Supported skW skInit ∧
      beh (sstep skW i32Test) skInit = {Obs.done [.val (Val.i32 21)]} ∧
      Behaviour.returns [Val.i32 21] ∈ behavioursFX' P host skFx (fxInit (skS P host) 1 []) ∧
      Behaviour.returns [Val.i32 11] ∈ behavioursFX' P host skFx (fxInit (skS P host) 1 []) ∧
      behavioursFX' P host skFx (fxInit (skS P host) 1 []) ≠
        obsB '' beh (sstep skW i32Test) skInit :=
  ⟨Silmaril.Proofs.Wasm.Models.FXSurplusK.skOk P host,
    Silmaril.Proofs.Wasm.Models.FXAsyncFX.rel_init _ 1 [],
    Silmaril.Proofs.Wasm.Models.FXSurplusK.skSupported,
    Silmaril.Proofs.Wasm.Models.FXSurplusK.sk_kernel_beh,
    Silmaril.Proofs.Wasm.Models.FXSurplusK.sk_fx_21 P host,
    Silmaril.Proofs.Wasm.Models.FXSurplusK.sk_fx_11 P host,
    Silmaril.Proofs.Wasm.Models.FXSurplusK.sk_not_beh_eq P host⟩

/-- **The tight hypothesis of `beh_eq_tight` is needed.** -/
theorem not_tight (o : GrowKind → Nat → Nat → Nat → Bool) : ¬ TightSupported skW skInit :=
  Silmaril.Proofs.Wasm.Models.FXSurplusK.sk_not_tight o

/-- info: 'Silmaril.Wasm.Models.FXSurplusK.not_beh_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_beh_eq

/-- info: 'Silmaril.Wasm.Models.FXSurplusK.not_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_tight

/-- info: 'Silmaril.Wasm.Models.FXSurplusK.surplus_in_fx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms surplus_in_fx

end Silmaril.Wasm.Models.FXSurplusK
