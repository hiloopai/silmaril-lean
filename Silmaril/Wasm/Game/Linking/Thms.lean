module

public import Silmaril.Wasm.Game.Linking.Defs
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Games.Category.Defs
public import Silmaril.Proofs.Wasm.Game.Linking.Main

/-!
# Static linking is composition (M3)

The output of silmaril-lean's GC static linker `link?` behaves as the
composition, in the game category `Silmaril.Games` (`Category Sig`), of the
strategies of its inputs:

* `Setup.link_is_composition_profile` (every profile `P`; `Setup.link_is_composition`
  for `profile o`):
  `σ_linked = σ_provider ≫ σ_consumer`, where `σ_consumer` is the strategy of
  the consumer with host stubs for the provider functions, and all three are
  the strategies of `Silmaril.Wasm.Game.Strategy` at the stores produced by
  `instantiateOnce?`. Composition is the plain composition of Silmaril
  strategies: the provider is **not** restarted at each call, its store
  persists across all of the consumer's calls. An earlier development could only
  state this equation for stateless providers (its layered composition
  restarted the provider at every call, and a mutable counter was a
  counterexample); its general statement went through `interact` of the
  provider object with the consumer's stateful plays, which is what Silmaril's
  composition is (`Setup.link_is_interact`, `Setup.linked_eq_comp`).
* `Setup.linked_adequacy_profile` (every profile; `Setup.linked_adequacy` for
  `profile o`): hence (with M2) the closed-world behaviours of an export call of
  the linked program are the observations of the composite of the strategies of
  its parts (with may-divergence under a nondeterministic profile).

Also exported from the proof modules (namespace `Silmaril.Wasm.Game.Linking`):
`Setup.linked_plays_eq_shared` (step A: linked = shared world over any number
of calls), `Setup.shared_objPlays_eq_split` (step B: the shared world splits
into provider and consumer), `Setup.provider_never_throws`,
`Setup.consumer_never_throws`, and `exists_scalar_setup` (nonvacuity: a
successful link, imports resolved up to closed subtyping, successful instantiations over a
host-free well-typed base store and scalar stub/export types gives a `Setup`
in the scalar fragment).

**Profiles.** M3 holds for an **arbitrary** profile `P`
(`Setup.link_is_composition_profile`). The inclusion
`σ_provider ≫ σ_consumer ≤ σ_linked` (`Setup.comp_le_link`) comes from forward
simulations: the split world is simulated by the shared world, which is
simulated by the linked module. The reverse inclusion needs two backward
simulations: `ReachReverse P` (linked runs are shared runs,
`reachReverse_all`) and `Setup.SplitReflects P` (shared plays are split plays,
`Setup.splitReflects`). silmaril-lean has only the forward simulation of the
linker relation (`Silmaril/Wasm/Link/LinkObservation.lean`: "the converse needs
a backward simulation"), and the first port proved both reverse directions
only for the deterministic profiles `profile o`, by uniqueness of normal forms
(where they had been frozen as Tasks; no Task remains).
They are now proved for every profile from **determinism up to profile
choices** (`Silmaril.Proofs.Wasm.Game.Choice.soft_join`: two host-free Core steps
from the same configuration have equal results, or both are `Soft`, i.e. a
numeric, vector, table or memory step, or a `TRAP`/`THROW_REF` bubble, under the
context rules): the forward image of a step of the related configuration is
the given step, unless the given step is `Soft`, and `Soft` steps are replayed
backwards structurally (the same choice is available on related
configurations: operands of numeric and vector instructions are equal, the
linker fragment has no tables or memories in relocated code and the stores
agree on them in unchanged code, and parts hold no exception references).
The deterministic statements `link_is_composition` and `linked_adequacy` are
corollaries.

Scope (as in an earlier development): scalar interfaces, no start functions (in `Setup`, every
`instantiateOnce?` returns no pending start call; `link?` itself rejects start functions;
links with start functions, their game-semantic link and M3 with start functions
(`StartSetup.link_is_composition_inst`, every profile, finite plays) are in
`Silmaril.Wasm.Game.LinkStart`), the linker fragment of
`Recipe.Assembly` (no memories, tables, tags, data or element segments). The
nonvacuity theorem no longer assumes exact import resolution
(`resolveImportsExact?`): it works with the public linker's resolution up to
closed subtyping, through `ExternAddrOk.sub`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Linking

namespace Setup

open CategoryTheory Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable (S : Setup)

/-- **M3, `≤`, every profile.** Under an arbitrary profile `P`, the composite of the
provider's and the consumer's strategies refines the strategy of the linked module: every
play of `σ_provider ≫ σ_consumer` is a play of `σ_linked` (forward simulations only). -/
theorem comp_le_link (hS : S.Scalar) (P : Profile) :
    (S.providerI.σ P).comp (S.consumerI.σ P) ≤ S.linkedI.σ P :=
  S.comp_le_linked hS P

/-- **M3 (static linking is composition), every profile.** In the category of signatures and
strategies, the strategy of the linked module is the composite of the provider's and the
consumer's strategies, with all stores persisting across calls, under an arbitrary silmaril
profile `P` (any `$ND`, relaxed choices, NaN policy and grow policy). -/
theorem link_is_composition_profile (hS : S.Scalar) (P : Profile) :
    (S.linkedI.σ P : ifaceSig [] ⟶ ifaceSig S.exportTypes) =
      CategoryStruct.comp (obj := Sig) (X := ifaceSig []) (Y := ifaceSig S.stubTypes)
        (Z := ifaceSig S.exportTypes) (S.providerI.σ P) (S.consumerI.σ P) :=
  S.linked_eq_comp hS P

/-- **M3 (static linking is composition)**, deterministic profiles. -/
theorem link_is_composition (hS : S.Scalar) (o : GrowOracle) :
    (S.linkedI.σ (profile o) : ifaceSig [] ⟶ ifaceSig S.exportTypes) =
      CategoryStruct.comp (obj := Sig) (X := ifaceSig []) (Y := ifaceSig S.stubTypes)
        (Z := ifaceSig S.exportTypes) (S.providerI.σ (profile o)) (S.consumerI.σ (profile o)) :=
  S.link_is_composition_profile hS (profile o)

/-- **M2 + M3, soundness, every profile.** Every terminating observation of the composite of
the strategies of the parts is a closed-world behaviour of the linked program. -/
theorem linked_answers_sound (hS : S.Scalar) (P : Profile) (K : Env (ifaceSig []))
    (f : (ifaceSig S.exportTypes).Op) {b : Behaviour Val} (hb : b ≠ .diverges)
    (h : b ∈ compositeObs (K.strategy.comp ((S.providerI.σ P).comp (S.consumerI.σ P))) f) :
    b ∈ behaviours P (fun _ _ _ _ => False : HostSemantics Nat) S.sl
        (S.linkedI.addr f.1) f.2.1 := by
  have hA := ScalarInstance.adequacy_closed_profile (I := S.linkedI) (P := P) hS.linked rfl K f
  rcases h with ⟨w, hw, rfl⟩ | ⟨rfl, -⟩
  · exact (Set.ext_iff.1 hA _).2
      (Or.inl (Or.inl ⟨w, Strategy.comp_mono le_rfl (S.comp_le_link hS P) hw, rfl⟩))
  · exact absurd rfl hb

/-- **M2 + M3, every profile.** The closed-world behaviours of an export call of the linked
program (under the empty host) are the observations of the composite of the strategies of its
parts, together with may-divergence. -/
theorem linked_adequacy_profile (hS : S.Scalar) (P : Profile) (K : Env (ifaceSig []))
    (f : (ifaceSig S.exportTypes).Op) :
    behaviours P (fun _ _ _ _ => False : HostSemantics Nat) S.sl
        (S.linkedI.addr f.1) f.2.1 =
      compositeObs (K.strategy.comp ((S.providerI.σ P).comp (S.consumerI.σ P))) f ∪
        {b | b = .diverges ∧ Diverges P (fun _ _ _ _ => False : HostSemantics Nat)
          (invoke S.sl (S.linkedI.addr f.1) f.2.1)} := by
  refine (ScalarInstance.adequacy_closed_profile (I := S.linkedI) (P := P) hS.linked rfl K f).trans
    ?_
  exact congrArg (fun σ => compositeObs (K.strategy.comp σ) f ∪
    {b | b = .diverges ∧ Diverges P (fun _ _ _ _ => False : HostSemantics Nat)
      (invoke S.sl (S.linkedI.addr f.1) f.2.1)}) (S.linked_eq_comp hS P)

/-- **M2 + M3**, deterministic profiles. The closed-world behaviours of an export call of the
linked program (under the empty host) are the observations of the composite of the strategies
of its parts. -/
theorem linked_adequacy (hS : S.Scalar) (o : GrowOracle) (K : Env (ifaceSig []))
    (f : (ifaceSig S.exportTypes).Op) :
    behaviours (profile o) (fun _ _ _ _ => False : HostSemantics Nat) S.sl
        (S.linkedI.addr f.1) f.2.1 =
      compositeObs (K.strategy.comp ((S.providerI.σ (profile o)).comp
        (S.consumerI.σ (profile o)))) f := by
  refine (ScalarInstance.adequacy_closed (I := S.linkedI) (o := o) hS.linked rfl K f).trans ?_
  exact congrArg (fun σ => compositeObs (K.strategy.comp σ) f) (S.linked_eq_comp hS (profile o))

end Setup

end Silmaril.Wasm.Game.Linking
