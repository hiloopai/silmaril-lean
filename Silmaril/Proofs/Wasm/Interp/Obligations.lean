module

public import Silmaril.Proofs.Wasm.Interp.Profile
public import Silmaril.Proofs.Wasm.Interp.Invoke

@[expose] public section

/-!
# silmaril-lean's adequacy obligations at every profile (proofs)

On stores whose functions are native-profile Wasm code (`Binaryen.NativeFuncsOk`), the three
obligations of `Silmaril/Wasm/Binaryen/AdequacyReduce.lean` (`FwdSim`, `BwdSim`,
`NoDivOfTerm`) and `DivSim` (`AdequacyModule.lean`) do not depend on the profile
(`fwdSim_profile_iff`, `bwdSim_profile_iff`, `noDivOfTerm_profile_iff`, `divSim_profile_iff`),
because Core runs and divergence from `$invoke` do not (`Silmaril.Proofs.Wasm.Interp.Profile`).
With `fwdSim_of_storeChk`, silmaril-lean's deterministic-profile `bwdSim_of` transfers:
`bwdSim_of_storeChk` gives `BwdSim` at every profile from `DivSim` and `NoDivOfTerm` at any
one profile, and `behaviours_eq_nbeh` the native behaviours of an invocation from them. New
proofs. Summary in `Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen

variable {H : Type} {P P' : Profile} {s : Store H} {a : Nat} {vs : List Val}

theorem fwdSim_profile_iff (hF : NativeFuncsOk s.funcs) : FwdSim P s a vs ↔ FwdSim P' s a vs := by
  have hc : NConfig (invoke s a vs) := nConfig_invoke hF a vs
  simp only [FwdSim, steps_profile_iff (P := P) (P' := P') hc]

theorem bwdSim_profile_iff (hF : NativeFuncsOk s.funcs) : BwdSim P s a vs ↔ BwdSim P' s a vs := by
  have hc : NConfig (invoke s a vs) := nConfig_invoke hF a vs
  simp only [BwdSim, steps_profile_iff (P := P) (P' := P') hc]

theorem noDivOfTerm_profile_iff (hF : NativeFuncsOk s.funcs) :
    NoDivOfTerm P s a vs ↔ NoDivOfTerm P' s a vs := by
  have hc : NConfig (invoke s a vs) := nConfig_invoke hF a vs
  simp only [NoDivOfTerm, steps_profile_iff (P := P) (P' := P') hc,
    diverges_profile_iff (P := P) (P' := P') hc]

theorem divSim_profile_iff (hF : NativeFuncsOk s.funcs) : DivSim P s a vs ↔ DivSim P' s a vs := by
  have hc : NConfig (invoke s a vs) := nConfig_invoke hF a vs
  simp only [DivSim, diverges_profile_iff (P := P) (P' := P') hc]

/-- **`BwdSim` at every profile** on native, arity-checked stores, from `DivSim` and
`NoDivOfTerm` at any one profile. -/
theorem bwdSim_of_storeChk (hF : NativeFuncsOk s.funcs) (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) (div : DivSim P' s a vs) (sn : NoDivOfTerm P' s a vs) :
    BwdSim P s a vs := by
  let D : Profile := Profile.deterministic fun _ _ _ _ => false
  have fwd : FwdSim D s a vs := fwdSim_of_storeChk hS hok
  have div' : DivSim D s a vs := (divSim_profile_iff hF).mp div
  have sn' : NoDivOfTerm D s a vs := (noDivOfTerm_profile_iff hF).mp sn
  exact (bwdSim_profile_iff hF).mp (bwdSim_of fwd div' sn')

/-- **Native behaviours are Core behaviours at every profile** on typed, native, arity-checked
stores, given `DivSim` and `NoDivOfTerm` at any one profile. -/
theorem behaviours_eq_nbeh (hs : StoreOk s) (hF : NativeFuncsOk s.funcs)
    (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) (div : DivSim P' s a vs)
    (sn : NoDivOfTerm P' s a vs) : behaviours P closedHost s a vs = nbeh s a vs := by
  have fwd : FwdSim P s a vs := fwdSim_of_storeChk hS hok
  have bwd : BwdSim P s a vs := bwdSim_of_storeChk hF hS hok div sn
  have sn' : NoDivOfTerm P s a vs := (noDivOfTerm_profile_iff hF).mp sn
  exact Set.Subset.antisymm (behaviours_subset_of_sim fwd bwd sn')
    (nbeh_subset_of_sim hs hF.funcsOk hok fwd bwd)

end Silmaril.Wasm.Interp
