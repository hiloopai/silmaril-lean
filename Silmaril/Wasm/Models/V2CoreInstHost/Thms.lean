module

public import Silmaril.Proofs.Wasm.Models.V2CoreInstHost.Main

/-!
# Instantiation through `liftHost`: the closed-host condition cannot be dropped

An earlier step proved the `eq` instantiation embedding `v20InstEmbDet g` at the deterministic
profile on `domInstDet g`, whose second conjunct asks for a 2.0 run with a closed-host behaviour.
It left open whether that condition, or the restriction to the deterministic profile, is needed.
The call model's counterexample `DetFalse` was expected to carry over to instantiation. This
header proves that it does, at every profile.

A Core null has no type, so `ref.null func` and `ref.null extern` have the same Core image, and
the induced host `liftHost src` answers a Core call on any 2.0 preimage of the Core store.

* `st`: a 2.0 store with one host function of type `[] → []` and one `funcref` table holding
  `ref.null func`; `stX`: the same store with `ref.null extern` in the table, an ill-typed store
  with the same Core image (`stX_toCore`). `StoreWF` holds for both.
* `src`: a host function call may always diverge, and returns when a table holds
  `ref.null extern`. It preserves stores and keeps functions, and it commutes with global
  embeddings (`src_embV`), so `pt = (st, src)` lies in `v20instHT P`'s domain (`pt_dom`).
* `mI`: a 2.0-valid module (`mI_ok`) that imports the host function and uses it as its start
  function.

At `st` every 2.0 instantiation run of `mI` (`inst_eq`) only diverges (`behaviours_st`,
`diverges_st`), so `v20instG` observes exactly `diverges` (`obs_pt`). At `stX` the run returns
`[]` (`returns_stX`). The forward inclusion into the spec's instantiation
(`inst_obs_sub_spec_H` with `specGlobalsImg`), read at `ptCore pt = ptCore (stX, src)`, puts
`returns []` among the spec observations of the image call (`core_returns`). Therefore:

* **`instHost_not_eq P`**: at every profile, with the call map `instCallE` of `v20InstEmbDet`,
  the spec observations and `v20instG`'s observations differ at a point of `v20instHT`'s domain on
  a valid module with a Core image;
* `not_domInstDet g`: `pt` is not in `domInstDet g`, which is consistent with `obs_eq_det`;
* **`coreInstObs_not_sub g`**: `coreInstObs_sub_det`'s conclusion fails for the run `cI st`,
  which has no closed-host behaviour.

So the `eq` embedding needs a domain condition at every profile, and the deterministic profile
alone is not enough. The ill-typed preimage `stX` is what `liftHost` permits; restricting
`liftHost` to well-typed preimages would be a different host map, not studied here.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstHost

/-- info: 'Silmaril.Proofs.Wasm.Models.V2CoreInstHost.instHost_not_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms instHost_not_eq

/-- info: 'Silmaril.Proofs.Wasm.Models.V2CoreInstHost.coreInstObs_not_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coreInstObs_not_sub

/-- info: 'Silmaril.Proofs.Wasm.Models.V2CoreInstHost.not_domInstDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_domInstDet

end Silmaril.Proofs.Wasm.Models.V2CoreInstHost
