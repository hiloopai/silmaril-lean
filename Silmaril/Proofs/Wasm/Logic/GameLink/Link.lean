module

public import Silmaril.Proofs.Wasm.Logic.GameLink.Strategy
public import Silmaril.Wasm.Game.Linking.Thms

/-!
# The logic and the Wasm game: verified static linking

From the game link (`strategy_sound`) and M3 (`Setup.link_is_composition_profile`:
the strategy of the module produced by silmaril-lean's static linker `link?` is
the composite of the provider's and the consumer's strategies):

* `answer_post`: in the closed world, a host-free Core run of an export call of a
  verified closed instance that ends in a result answers as `Ie.post` requires
  (from `ScalarInstance.ask_ans_iff`);
* `linked_sound`: if the provider meets `Im` (no imports) and the consumer
  (with host stubs for the provider functions) meets `Ie` under `Im`, then the
  strategy of the linked module refines `agStrat Ii Ie`;
* `linked_answer_post`: hence every terminating host-free run of an export
  call of the linked module meets `Ie`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.GameLink

open CategoryTheory Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.Logic.Strategy (ISpec agStrat AG comp_refines)

/-- A strategy refining `agStrat Ii Ie` answers an allowed export question as `Ie.post`
requires. -/
theorem ag_answer {E F : Sig.{0}} {Ii : ISpec E} {Ie : ISpec F} {σ : Strategy E F}
    (hσ : σ ≤ agStrat Ii Ie) {f : F.Op} {w : F.Ar f} (hf : Ie.pre f)
    (hp : [.inr (.ask f), .inr (.ans f w)] ∈ σ) : Ie.post f w :=
  (((hσ hp).2.1 trivial hf).2 trivial).1

/-- **Closed-world reading of the game link.** If an instance meets `Ie` under `Ii` from a
store meeting its invariant, a host-free Core run of an allowed export call that ends in a
result answers as `Ie.post` requires. -/
theorem answer_post {I : ScalarInstance} {P : Profile} {Inv : Store Nat → Prop}
    {Ii : ISpec I.E} {Ie : ISpec I.F} (hm : GameSat P I Inv Ii Ie) {s : Store Nat} (hs : Inv s)
    {f : I.F.Op} (hf : Ie.pre f) {d : Config Nat} {r : Result} {w : I.F.Ar f}
    (hrun : Steps P (SingleThreaded.Det.noHost : HostSemantics Nat) (invoke s (I.addr f.1) f.2.1) d)
    (hd : d.code = r.toAdmin) (hw : Answer.ofResult? (I.exports.get f.1) r = some w) :
    Ie.post f w :=
  ag_answer (strategy_sound hm hs) hf (ScalarInstance.ask_ans_iff.2 ⟨d, r, hrun, hd, hw⟩)

variable (S : Setup)

/-- **Verified static linking.** If the provider meets `Im` (it has no imports, so `Ii` is
irrelevant to it) from its instantiated store and the consumer, with host stubs for the
provider functions, meets `Ie` under `Im` from its instantiated store, then the strategy of
the statically linked module refines `agStrat Ii Ie`. -/
theorem linked_sound (hS : S.Scalar) (P : Profile) {Ii : ISpec (ifaceSig [])}
    {Im : ISpec (ifaceSig S.stubTypes)} {Ie : ISpec (ifaceSig S.exportTypes)}
    {Invp Invc : Store Nat → Prop} (hp : GameSat P S.providerI Invp Ii Im) (hp₀ : Invp S.sp)
    (hc : GameSat P S.consumerI Invc Im Ie) (hc₀ : Invc S.scs) :
    S.linkedI.σ P ≤ agStrat Ii Ie := by
  have hcomp : (S.providerI.σ P).comp (S.consumerI.σ P) ≤ agStrat Ii Ie :=
    comp_refines (strategy_sound hp hp₀) (strategy_sound hc hc₀)
  rw [S.link_is_composition_profile hS P]
  exact hcomp

/-- **Verified static linking, closed world.** Under the hypotheses of `linked_sound`, every
host-free Core run of an allowed export call of the linked module that ends in a result
answers as `Ie.post` requires. -/
theorem linked_answer_post (hS : S.Scalar) (P : Profile) {Ii : ISpec (ifaceSig [])}
    {Im : ISpec (ifaceSig S.stubTypes)} {Ie : ISpec (ifaceSig S.exportTypes)}
    {Invp Invc : Store Nat → Prop} (hp : GameSat P S.providerI Invp Ii Im) (hp₀ : Invp S.sp)
    (hc : GameSat P S.consumerI Invc Im Ie) (hc₀ : Invc S.scs)
    {f : (ifaceSig S.exportTypes).Op} (hf : Ie.pre f) {d : Config Nat} {r : Result}
    {w : (ifaceSig S.exportTypes).Ar f}
    (hrun : Steps P (SingleThreaded.Det.noHost : HostSemantics Nat) (invoke S.sl (S.linkedI.addr f.1) f.2.1) d)
    (hd : d.code = r.toAdmin) (hw : Answer.ofResult? (S.exportTypes.get f.1) r = some w) :
    Ie.post f w :=
  ag_answer (linked_sound S hS P hp hp₀ hc hc₀) hf
    (ScalarInstance.ask_ans_iff (I := S.linkedI).2 ⟨d, r, hrun, hd, hw⟩)

end Silmaril.Wasm.Logic.GameLink
