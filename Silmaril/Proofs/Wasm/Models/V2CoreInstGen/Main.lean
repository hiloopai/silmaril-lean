module

public import Silmaril.Wasm.Models.V2CoreInstGen.Defs
public import Silmaril.Proofs.Wasm.Models.V2CoreInstGen.StartHost

/-!
# The 2.0 instantiation models at every host type

* `v20instHTG_nat`, `domInstPG_nat_iff`, `domInstHostG_nat_iff`, `importsTransportG_nat_iff`: at
  `H = Nat` the generic definitions are the originals.
* **`importsTransportG_all`**: the earlier `importsTransport_all` at every host type. The proof is
  the original one; only the statement was at `Pt Nat`.
* **`domInstHostG_of_storeOk`**: every typed point of `v20instHTG P H`'s domain with a host
  satisfying 2.0's `HostOk` is in `domInstHostG P`, at every `H` (an earlier
  `domInstHost_of_storeOk` at `Nat`).
* **`domInstPG_of_storeOk_any`**: every typed, host-free point of the domain is in
  `domInstPG P`, at every `H`.
* **`not_domInstPG_hostDivPt`**: `hostDivPt` is in neither `domInstP P` nor its generic form, so
  host-freeness cannot be dropped from the previous item.

New proofs; `importsTransportG_all` follows `V2CoreInstFn/Transport`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstGen

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Models.V2CoreInstGen (v20instHTG domInstPG domInstHostG ImportsTransportG)
open Silmaril.Wasm.Models.V2CoreInstImp (domInstP ImportsTransport)
open Silmaril.Wasm.Models.V2CoreInstHostFn (domInstHost hostDivPt)

variable {H : Type}

/-! ## At `Nat`, the originals -/

theorem v20instHTG_nat (P : Profile) : v20instHTG P Nat = v20instHT P := rfl

theorem domInstPG_nat_iff (P : Profile) (p : Pt Nat) : domInstPG P p ↔ domInstP P p := Iff.rfl

theorem domInstHostG_nat_iff (P : Profile) (p : Pt Nat) :
    domInstHostG P p ↔ domInstHost P p := Iff.rfl

theorem importsTransportG_nat_iff (p : Pt Nat) : ImportsTransportG p ↔ ImportsTransport p :=
  Iff.rfl

/-! ## At every host type -/

/-- **Import typing transports at every point whose store has a Core image**, at every host
type. -/
theorem importsTransportG_all {p : Pt H} (hd : (Store.toCore p.1).isSome) :
    ImportsTransportG p := by
  intro m cm xas ixt xt xtI xtE hm hcm hcok hxas
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 hd
  have hp : (ptCore p).1 = cs := by simp [ptCore, hcs]
  rw [hp] at hxas
  cases hm with
  | mk htypes himports =>
    cases hcok with
    | mk htypesC himportsC =>
      rw [Silmaril.Proofs.Wasm.Models.V2CoreInstFn.types_of_toCore hcm] at htypesC
      rw [Silmaril.Proofs.Wasm.Models.V2Core.Reflect.types_refl htypesC,
        Silmaril.Proofs.Wasm.Models.V2CoreInstDom.imports_of_toCore hcm] at himportsC
      obtain ⟨ixt', hi', rfl⟩ := Silmaril.Proofs.Wasm.Models.V2Core.Reflect.imports_refl himportsC
      rw [Silmaril.Proofs.Wasm.Models.V2CoreInstFn.types_eq_of_typeOk htypes] at himports
      rw [Silmaril.Proofs.Wasm.Models.V2CoreInstFn.importOk_det himports hi']
      exact Silmaril.Proofs.Wasm.Models.V2CoreInstFn.addrs_transport hcs hi' hxas

/-- **Every typed point of the domain with a well-behaved host is in `domInstHostG P`**, at
every host type, host functions allowed. -/
theorem domInstHostG_of_storeOk {P : Profile} {p : Pt H} (hd : (v20instHTG P H).dom p)
    (hs : StoreOk p.1) (hh : HostOk p.2) : domInstHostG P p := by
  refine ⟨hd, fun m cm xas hval hcm ⟨C, hC⟩ => ?_⟩
  obtain ⟨xtE, xtI, hok, hxas⟩ := hC.valid
  obtain ⟨ixt, xt, hm⟩ := hval
  have hx : List.Forall₂ (ExternAddrOk p.1) xas ixt :=
    importsTransportG_all hd.1.2.1 m cm xas ixt xt xtI xtE hm hcm hok hxas
  exact Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.instantiate_behaviours P hs hh hm hx
    (Silmaril.Proofs.Wasm.Models.V2CoreInstDom.segBounded_of_core hcm hC.bounded)

/-- **Every typed, host-free point of the domain is in `domInstPG P`**, at every host type. -/
theorem domInstPG_of_storeOk_any {P : Profile} {p : Pt H} (hd : (v20instHTG P H).dom p)
    (hs : StoreOk p.1) (hfree : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree p.1) :
    domInstPG P p := by
  refine ⟨hd, fun m cm xas hval hcm ⟨C, hC⟩ => ?_⟩
  obtain ⟨xtE, xtI, hok, hxas⟩ := hC.valid
  obtain ⟨ixt, xt, hm⟩ := hval
  have hx : List.Forall₂ (ExternAddrOk p.1) xas ixt :=
    importsTransportG_all hd.1.2.1 m cm xas ixt xt xtI xtE hm hcm hok hxas
  obtain ⟨c, hinst, hfree'⟩ := Silmaril.Wasm.Models.V2CoreInstImp.instantiate_imports P hs hfree hm hx
    (Silmaril.Proofs.Wasm.Models.V2CoreInstDom.segBounded_of_core hcm hC.bounded)
  obtain ⟨hok', -⟩ := Instantiate.ok Silmaril.Proofs.Wasm.Models.V2Sound.hostOk_divV hs
    (hinst Silmaril.Proofs.Wasm.Models.V2Sound.divV)
  exact ⟨c, hinst p.2, Silmaril.Proofs.Wasm.Models.V2Sound.behavioursOf_nonempty_of_safe
    fun _ hsteps => (Silmaril.Proofs.Wasm.Models.V2Sound.closed_safe hfree' hok' hsteps).2.2⟩

/-- `domInstPG` and `domInstHostG` agree at points with the closed host. -/
theorem domInstPG_iff_host_of_closed {P : Profile} {p : Pt H} (hc : p.2 = closedV) :
    domInstPG P p ↔ domInstHostG P p := by
  unfold domInstPG domInstHostG
  rw [hc]

/-- **`hostDivPt` is not in `domInstPG P`.** -/
theorem not_domInstPG_hostDivPt (P : Profile) : ¬ domInstPG P hostDivPt :=
  not_domInstP_hostDivPt P

end Silmaril.Proofs.Wasm.Models.V2CoreInstGen
