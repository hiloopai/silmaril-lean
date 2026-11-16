module

public import Silmaril.Logic.Consequence.Concrete.Defs
public import Silmaril.Logic.Consequence.HOL.Thms
public import Silmaril.Logic.Consequence.TypeTheory.Thms
public import Silmaril.Logic.HOLLight.SExp.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms
public import Silmaril.Logic.Institution.Borrowing
public import Silmaril.Proofs.Logic.Consequence.TypeTheory.Basic

/-! Proofs for `Silmaril.Logic.Consequence.Concrete.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Concrete

open CategoryTheory Silmaril.Logic Silmaril.Logic.Institution
open Silmaril.Consequence Silmaril.Consequence.Concrete
open Silmaril.Logic.Institution.Metatheory (HolSig)

universe u

/-! ## HOL -/

section HOL

open Silmaril.Logic.HOLLight Silmaril.Consequence.HOL

variable {S : HolSig}

theorem encode_toProp (e : HOLSen S) : SExp.encodeTm e.toProp.1 = e.1 := Classical.choose_spec e.2

theorem toProp_ofProp (p : HOLProp S) : (HOLSen.ofProp p).toProp = p :=
  Subtype.ext (SExp.encodeTm_injective (encode_toProp (HOLSen.ofProp p)))

theorem ofProp_toProp (e : HOLSen S) : HOLSen.ofProp e.toProp = e := Subtype.ext (encode_toProp e)

theorem map_toProp_ofProp (Γ : List (HOLProp S)) :
    (Γ.map HOLSen.ofProp).map HOLSen.toProp = Γ := by
  simp [List.map_map, Function.comp_def, toProp_ofProp]

theorem holKernel_ofProp_iff (Δ : Theory) (Γ : List (HOLProp S)) (p : HOLProp S) :
    holKernel S Δ (Γ.map HOLSen.ofProp) (HOLSen.ofProp p) ↔ kernelFrom S Δ Γ p := by
  simp only [holKernel, System.pullback_apply, map_toProp_ofProp, toProp_ofProp]

theorem holSeq_ofProp_iff (Γ : List (HOLProp S)) (p : HOLProp S) :
    holSeq.{u} S (Γ.map HOLSen.ofProp) (HOLSen.ofProp p) ↔ seq.{u} S Γ p := by
  simp only [holSeq, System.pullback_apply, map_toProp_ofProp, toProp_ofProp]

theorem holKernel_closed (Δ : Theory) : Structural.Closed Structural.tarskiRules (holKernel S Δ) :=
  TypeTheory.closed_pullback_map HOLSen.toProp (kernelFrom_closed Δ)

end HOL

/-! ## Extensional MLTT -/

section MLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem encode_toJdg (e : MLTTSen) : SExp.encodeJdg e.toJdg = e.1 := Classical.choose_spec e.2

theorem encodeJdg_injective : Function.Injective SExp.encodeJdg := fun a b h => by
  have := SExp.decodeJdg_encodeJdg a
  rw [h, SExp.decodeJdg_encodeJdg] at this
  exact (Option.some.inj this).symm

theorem toJdg_ofJdg (J : EJdg) : (MLTTSen.ofJdg J).toJdg = J :=
  encodeJdg_injective (encode_toJdg (MLTTSen.ofJdg J))

theorem ofJdg_toJdg (e : MLTTSen) : MLTTSen.ofJdg e.toJdg = e := Subtype.ext (encode_toJdg e)

theorem map_toJdg_ofJdg (Γ : List EJdg) : (Γ.map MLTTSen.ofJdg).map MLTTSen.toJdg = Γ := by
  simp [List.map_map, Function.comp_def, toJdg_ofJdg]

theorem mlttDerives_ofJdg_iff (Γ : List EJdg) (J : EJdg) :
    mlttDerives (Γ.map MLTTSen.ofJdg) (MLTTSen.ofJdg J) ↔ TypeTheory.extensionalDerives Γ J := by
  simp only [mlttDerives, System.pullback_apply, map_toJdg_ofJdg, toJdg_ofJdg]

theorem mlttEntails_ofJdg_iff (Γ : List EJdg) (J : EJdg) :
    mlttEntails.{u} (Γ.map MLTTSen.ofJdg) (MLTTSen.ofJdg J) ↔
      TypeTheory.extensionalEntails.{u} Γ J := by
  simp only [mlttEntails, System.pullback_apply, map_toJdg_ofJdg, toJdg_ofJdg]

theorem mlttDerives_closed : Structural.Closed Structural.tarskiRules mlttDerives :=
  TypeTheory.closed_pullback_map MLTTSen.toJdg Consequence.TypeTheory.extensionalDerives_closed

theorem mlttRoomEntails_iff (Γ : List MLTTSen) (e : MLTTSen) :
    mlttRoomEntails.{u} Γ e ↔ TypeTheory.extensionalEntails.{u} (Γ.map MLTTSen.toJdg) e.toJdg := by
  show roomSeq mlttRoom.{u} (Γ.map ULift.up) (ULift.up e) ↔
    roomSeq Institution.room.{u} ((Γ.map MLTTSen.toJdg).map ULift.up) (ULift.up e.toJdg)
  constructor
  · intro h M hM
    exact h M fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hM _ (List.mem_map_of_mem (List.mem_map_of_mem hy))
  · intro h M hM
    exact h M fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact hM _ (List.mem_map_of_mem hz)

end MLTT

end Silmaril.Proofs.Logic.Consequence.Concrete
