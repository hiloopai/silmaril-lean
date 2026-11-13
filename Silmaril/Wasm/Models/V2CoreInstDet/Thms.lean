module

public import Silmaril.Wasm.Models.V2CoreInstDet.Defs
import Silmaril.Proofs.Wasm.Models.V2CoreInstDet.Det
import Silmaril.Proofs.Wasm.Models.V2CoreInstDet.Emb

/-!
# The instantiation embedding with equal observations, at the deterministic profile

An earlier step left the reverse inclusion `coreInst ⊆ v20instG` of `v20InstEmbHU` open. This header
settles it in the form the call model already has (`v20EmbDet`):

* **`instCall_not_eq`** (refutation): with the call map `instCall`, the `eq` direction fails at
  every profile, already at the empty store with the closed host. A 2.0 module with no Core
  image (`noImg`) is sent to the empty Core module, which Core instantiates (its run returns
  `[]`), but `v20instG` observes nothing on it.
* **`coreInstObs_sub_det`**: at `Profile.deterministic g`, at a point of `v20instHT`'s domain,
  every spec observation of an image call lies inside the mapped 2.0 behaviours of any 2.0
  instantiation run `c` whose closed-host behaviours are not empty. This is the backward
  2.0 → Core direction at the instantiation configuration. It holds for every host in the domain,
  `liftHost` hosts included, through the closed-host behaviour: at the deterministic profile a
  closed-host behaviour of a Core configuration is its only behaviour under every host
  (`DetLift`).
* `instObs_eq_det`: on such calls the spec observations are the 2.0 instantiation observations.
* **`v20InstEmbDet g : (v20instDet g).Emb (coreInst (Profile.deterministic g) Nat v20)`**,
  direction **`eq`**, with the call map `instCallE` (`badModule` for modules that are not
  2.0-valid or have no Core image). The domain `domInstDet g` asks that every image call of a
  2.0-valid module that Core instantiates has a 2.0 run with a closed-host behaviour. It
  covers both open pieces , the backward simulation from the instantiation
  configuration, and calls that Core instantiates but 2.0 does not.
* **`not_domInstDetU`** (refutation): the validity premise is needed. Without it no point
  satisfies the condition, because Core instantiates the image of a 2.0 module with two
  memories, which 2.0 rejects (`hmems_le`).

The hypothesis is a domain condition, as in `v20EmbDet`'s `domDet`. At other profiles, and
without the closed-host behaviour, the call-level counterexample `DetFalse` applies: `liftHost`
can answer a host call from a different 2.0 argument with the same Core image. This header does
not lift that counterexample to an instantiation run.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstDet

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Atlas Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreInst
  Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- **With `instCall`, the `eq` direction of the instantiation embedding fails** at every
profile. -/
theorem instCall_not_eq (P : Profile) :
    ∃ p : Pt Nat, (v20instHT P).dom p ∧
      ∃ mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr,
        (coreInst P Nat v20).view some (ptCore p) (instCall mx) ≠ (v20instG P Nat).obs p mx :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstDet.instCall_not_eq P

/-- **The backward direction at the instantiation configuration**, at the deterministic
profile: spec observations of an image call lie inside the mapped 2.0 behaviours of a 2.0
instantiation run with a closed-host behaviour. -/
theorem coreInstObs_sub_det (g : GrowKind → Nat → Nat → Nat → Bool) {p : Pt Nat}
    (hp : (v20instHT (Profile.deterministic g)).dom p) {m : Silmaril.Wasm.V2.Module}
    {cm : Silmaril.Wasm.Module} (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr}
    {c : Silmaril.Wasm.V2.Execution.Config Nat}
    (hc : Silmaril.Wasm.V2.Execution.Instantiate (Profile.deterministic g) p.2 p.1 m xas c)
    (htot : (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) closedV
      c).Nonempty) :
    Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs (Profile.deterministic g) (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) ⊆
      Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) p.2 c) :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstDet.coreInstObs_sub_det g hp hcm hc htot

/-- On such calls the spec observations are the 2.0 instantiation observations. -/
theorem instObs_eq_det (g : GrowKind → Nat → Nat → Nat → Bool) {p : Pt Nat}
    (hp : (v20instHT (Profile.deterministic g)).dom p) {m : Silmaril.Wasm.V2.Module}
    {cm : Silmaril.Wasm.Module} (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr}
    {c : Silmaril.Wasm.V2.Execution.Config Nat}
    (hc : Silmaril.Wasm.V2.Execution.Instantiate (Profile.deterministic g) p.2 p.1 m xas c)
    (htot : (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) closedV
      c).Nonempty) :
    Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs (Profile.deterministic g) (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) =
      Silmaril.Proofs.Wasm.Models.V2Core.instObs (Profile.deterministic g) p (m, xas) :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstDet.instObs_eq_det g hp hcm hc htot

/-- At points of `domInstDet g`, the spec observations of `instCallE mx` are `v20instG`'s. -/
theorem obs_eq_det (g : GrowKind → Nat → Nat → Nat → Bool) {p : Pt Nat} (hp : domInstDet g p)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    (coreInst (Profile.deterministic g) Nat v20).view some (ptCore p) (instCallE mx) =
      (v20instG (Profile.deterministic g) Nat).obs p mx :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstDet.obs_eq_det g hp mx

/-- **The instantiation embedding with equal observations** at the deterministic profile
(direction `eq`). -/
noncomputable def v20InstEmbDet (g : GrowKind → Nat → Nat → Nat → Bool) :
    (v20instDet g).Emb (coreInst (Profile.deterministic g) Nat v20) where
  mod := modCore
  valid := (v20Emb (Profile.deterministic g) Nat).valid
  pt := ptCore
  call := instCallE
  readback := some
  dom _ hp := ptCore_dom hp.1.1
  dir := .eq
  sat _ hp mx := obs_eq_det g hp mx

theorem v20InstEmbDet_dir (g : GrowKind → Nat → Nat → Nat → Bool) :
    (v20InstEmbDet g).dir = .eq := rfl

/-- The equality atlas transition of `v20InstEmbDet`. -/
noncomputable def v20InstTransDet (g : GrowKind → Nat → Nat → Nat → Bool) :
    Transition (v20instDet g).chart
      ((coreInst (Profile.deterministic g) Nat v20).viewChart some) :=
  (v20InstEmbDet g).toTransition

/-- **Without the validity premise, the domain condition holds at no point.** -/
theorem not_domInstDetU (g : GrowKind → Nat → Nat → Nat → Bool) (p : Pt Nat) :
    ¬ DomInstDetU g p :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstDet.not_domInstDetU g p

/-- `v20instDet g`'s domain lies inside `v20instHT`'s. -/
theorem domInstDet_sub (g : GrowKind → Nat → Nat → Nat → Bool) {p : Pt Nat}
    (hp : domInstDet g p) : (v20instHT (Profile.deterministic g)).dom p :=
  hp.1

/-! The axiom audit. -/

/--
info: 'Silmaril.Wasm.Models.V2CoreInstDet.instCall_not_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms instCall_not_eq

/--
info: 'Silmaril.Wasm.Models.V2CoreInstDet.coreInstObs_sub_det' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coreInstObs_sub_det

/--
info: 'Silmaril.Wasm.Models.V2CoreInstDet.v20InstEmbDet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v20InstEmbDet

/--
info: 'Silmaril.Wasm.Models.V2CoreInstDet.not_domInstDetU' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_domInstDetU

end Silmaril.Wasm.Models.V2CoreInstDet
