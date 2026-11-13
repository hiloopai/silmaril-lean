module

public import Silmaril.Wasm.Game.ULink.Defs
public import Silmaril.Proofs.Wasm.Game.Linking.Setup

/-!
# The semantic link of a `link?` setup

For a `Linking.Setup` `S` (silmaril-lean's `link?` in the fragment `Recipe.Assembly`, with the
provider and the consumer also instantiated into one shared store `S.sc`), the semantic link
`S.toULink` has

* the shared world's exports (`toULink_U`: its linked module is `S.sharedI.toU`);
* `toULink_stubS`: as stubbed store, **the store of the setup's consumer with stubs**,
  `S.scs` (from `Linking.Setup.scs_eq_stubOut`);
* `toULink_layout`, `toULink_stubsIn`: the shared store has the link's layout (it has no host
  function at all) and contains the stubbed functions.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril.Wasm.Game.Linking Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Link.GC

variable (S : Setup)

/-- The linked module of the semantic link is the shared world. -/
theorem toULink_U : S.toULink.U = S.sharedI.toU := rfl

/-- Stubbing in the semantic link is the setup's `stubOut`. -/
theorem toULink_stubFI : S.toULink.stubFI = fun a fi =>
    if S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs then
      { fi with code := .host (S.stubs.idxOf (a - S.base.funcs.length)) }
    else fi := by
  funext a fi
  by_cases hc : S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs
  · simp only [ULink.stubFI, Setup.toULink, Setup.ulinkStub, hc, and_self, ↓reduceIte]
  · simp only [ULink.stubFI, Setup.toULink, Setup.ulinkStub, hc, ↓reduceIte]

/-- **The stubbed shared store is the setup's consumer-with-stubs store.** -/
theorem toULink_stubS : S.toULink.stubS S.sc = S.scs := by
  rw [S.scs_eq_stubOut]
  show { S.sc with funcs := S.sc.funcs.mapIdx S.toULink.stubFI } = _
  rw [toULink_stubFI]
  rfl

/-- The shared store has no host function. -/
theorem sc_no_host (hS : S.Scalar) {a : Nat} {fi : FuncInst Nat} {h : Nat}
    (ha : S.sc.funcs[a]? = some fi) (hc : fi.code = .host h) : False := by
  obtain ⟨hlt, -⟩ := hS.shared.host_type a fi h ha hc
  exact Nat.not_lt_zero _ hlt

/-- **The shared store has the layout of the semantic link.** -/
theorem toULink_layout (hS : S.Scalar) : S.toULink.Layout S.sc := by
  refine ⟨fun a fi k c ha hs => ?_, fun a fi h ha hc => (sc_no_host S hS ha hc).elim⟩
  have hc : c = Setup.wasmCodeAt S.sc a := by
    have hs' : S.ulinkStub a = some (k, c) := hs
    unfold Setup.ulinkStub at hs'
    split at hs'
    · exact ((Prod.mk.inj (Option.some.inj hs')).2).symm
    · cases hs'
  cases hcode : fi.code with
  | host h => exact (sc_no_host S hS ha hcode).elim
  | wasm c' =>
    have hw : Setup.wasmCodeAt S.sc a = c' := by
      unfold Setup.wasmCodeAt
      rw [ha, Option.map_some, hcode]
    rw [hc, hw]

/-- **The stubbed functions are functions of the shared store.** -/
theorem toULink_stubsIn : S.toULink.StubsIn S.sc := by
  intro a k c hs
  have hs' : S.ulinkStub a = some (k, c) := hs
  unfold Setup.ulinkStub at hs'
  split at hs'
  · rename_i hcond
    have hcount : S.sp.funcs.length = S.base.funcs.length + S.provider.funcs.length :=
      (Views.once_counts S.assembly.providerProfile S.provInst).1
    obtain ⟨_, _, hsc⟩ := StoreRelation.once_function_list S.assembly.consumerProfile S.sharedInst
    have hprov : a - S.base.funcs.length < S.provider.funcs.length := S.stubs_lt _ hcond.2
    have hle : S.sp.funcs.length ≤ S.sc.funcs.length := by
      rw [hsc, List.length_append]
      exact Nat.le_add_right _ _
    omega
  · cases hs'

end Silmaril.Proofs.Wasm.Game.ULink
