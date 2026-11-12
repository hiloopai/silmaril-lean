module

public import Silmaril.Wasm.Wac.Bridge.DecodeValue.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeImpl.Thms

/-!
# WAC bridge: value items, proofs

* `item_value`: a value item as an `ItemSim` (its descriptor `(value (type v))`, `v` the
  encoded value type, which decodes back by `valTy_sim`);
* `esOkV_sim`: every list of `EsOkV` satisfies `ListSim`, by induction, with the item
  simulations of `Bridge.DecodeNamed` for the other constructors;
* `decls_encodeL`: `DecodeNamed.decls_encode` for any lists that satisfy `ListSim`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty)
open DecodeEnc (typeAt_run ok_bind pure_ok)
open DecodeAnon (ext_refl)
open DecodeNamed

namespace DecodeValue

attribute [local simp] ok_bind pure_ok

/-- **A value item.** -/
theorem item_value {N : NomTable} {Γ : Ctx} {n : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (ht : TyOk Γ t) :
    ∀ σ δ, M N Γ σ δ → ItemSim N Γ Γ n (.value t) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc]
  exact vs_bind (valTy_sim ht σ δ hm) fun v σ1 δ1 hm1 _ hv => vs_pure hm1 fun σ2 hm2 =>
    ⟨δ1, by simp [decExtern, hv δ1 (ext_refl δ1), dk], hm2⟩

/-- **Every list of items of the fragment with values** is read back as `dks`. -/
theorem esOkV_sim {N : NomTable} {Γ : Ctx} {es : Externs} (h : EsOkV N Γ es) : ListSim N Γ es := by
  induction h with
  | nil => exact listSim_nil _ _
  | value ht _ ih => exact listSim_cons (item_value ht) rfl ih
  | func hs _ ih => exact listSim_cons (item_func hs) rfl ih
  | inst _ _ ihf ih => exact listSim_cons (item_inst ihf) rfl ih
  | comp _ _ _ ih1 ih2 ih => exact listSim_cons (item_comp ih1 ih2) rfl ih
  | res _ ih => exact listSim_cons item_res rfl ih
  | tyOwn ha _ ih => exact listSim_cons (item_tyOwn ha) rfl ih
  | tyRef ha _ ih => exact listSim_cons (item_tyRef ha) rfl ih
  | tyNom hn hN hd _ ih => exact listSim_cons (item_tyNom hn hN hd) rfl ih
  | tyVal hp ht _ ih =>
    exact listSim_cons (item_tyVal hp ht) (by simp only [extend, sortOf_plain hp]) ih
  | tyFunc hs _ ih => exact listSim_cons (item_tyFunc hs) rfl ih
  | tyInst _ _ ihf ih => exact listSim_cons (item_tyInst ihf) rfl ih
  | tyComp _ _ _ ih1 ih2 ih => exact listSim_cons (item_tyComp ih1 ih2) rfl ih

/-- **The fragment with values contains the named fragment.** -/
theorem esOkV_of_esOk {N : NomTable} {Γ : Ctx} {es : Externs} (h : EsOk N Γ es) : EsOkV N Γ es := by
  induction h with
  | nil => exact .nil
  | func hs _ ih => exact .func hs ih
  | inst _ _ ihf ih => exact .inst ihf ih
  | comp _ _ _ ih1 ih2 ih => exact .comp ih1 ih2 ih
  | res _ ih => exact .res ih
  | tyOwn ha _ ih => exact .tyOwn ha ih
  | tyRef ha _ ih => exact .tyRef ha ih
  | tyNom hn hN hd _ ih => exact .tyNom hn hN hd ih
  | tyVal hp ht _ ih => exact .tyVal hp ht ih
  | tyFunc hs _ ih => exact .tyFunc hs ih
  | tyInst _ _ ihf ih => exact .tyInst ihf ih
  | tyComp _ _ _ ih1 ih2 ih => exact .tyComp ih1 ih2 ih

/-- `DecodeNamed.decls_encode` for lists that satisfy `ListSim`. -/
theorem decls_encodeL {N : NomTable} (b : Bool) {is es : Externs} (his : ListSim N [] is)
    (hes : ListSim N (extend [] is) es) {δ : DScope} (hδ : δ.types = #[])
    (hn : ∀ p ∈ δ.nom, N.lookup p.1 = some p.2) :
    ∃ σ δ', ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      (decCDecls σ.decls [] []).run δ = .ok ((dks is, dks es), δ') ∧
      ∀ p ∈ δ'.nom, N.lookup p.1 = some p.2 := by
  obtain ⟨σ1, E1, δ1, hr1, hd1, hm1, hreads1⟩ := (his _ _ (m_start N b hδ hn)).1
  obtain ⟨σ2, E2, δ2, hr2, hd2, hm2, hreads2, -⟩ := (hes σ1 δ1 hm1).2
  have e : σ2.decls = E1 ++ (E2 ++ []) := by rw [hd2, hd1]; simp
  have h2 : (decCDecls (E2 ++ []) ([] ++ dks is) []).run δ1 =
      (decCDecls [] ([] ++ dks is) ([] ++ dks es)).run δ2 := hreads2 [] _ []
  refine ⟨σ2, δ2, by simp [hr1, hr2], ?_, hm2.dnom⟩
  rw [e, hreads1, h2]
  simp [decCDecls]

end DecodeValue

end Silmaril.Wasm.Wac.Bridge
