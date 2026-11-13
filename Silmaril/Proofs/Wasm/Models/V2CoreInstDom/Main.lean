module

public import Silmaril.Proofs.Wasm.Models.V2CoreInstDom.Alloc
public import Silmaril.Wasm.Models.V2CoreInstDet.Thms

/-!
# `domInstDet` is not empty

The empty 2.0 store with the closed host lies in `domInstDet g` at every grow policy `g`:

* Core 3.0 instantiates nothing with an import in the empty Core store (no external address
  is typed there, `not_externAddrOk_empty`), so a call that Core instantiates has no external
  addresses and its module has no imports (`imports_nil`);
* the 2.0 module then instantiates in the empty store (`instantiate_empty`), with segment bounds
  read off the Core image (`segBounded_of_core`);
* its configuration is typed (the copied `Instantiate.ok`, at the host `divV`) on a host-free
  store, so it has a closed-host behaviour (`closed_safe`, `behavioursOf_nonempty_of_safe`).

The proofs are new.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstDom

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
  Silmaril.Wasm.Models.V2CoreInstDet
open Silmaril.Proofs.Wasm.Models.V2Sound (HostFree divV hostOk_divV closed_safe
  behavioursOf_nonempty_of_safe)

/-- The empty 2.0 store with the closed host. -/
def emptyPt : Pt Nat := ({}, closedV)

/-- `emptyPt` is in `v20instHT`'s domain at every profile. -/
theorem emptyPt_dom (P : Profile) : (v20instHT P).dom emptyPt := by
  refine ⟨⟨⟨fun _ _ h => by simp [emptyPt] at h, fun _ _ h => by simp [emptyPt] at h,
    fun _ _ h => by simp [emptyPt] at h, fun _ _ h => by simp [emptyPt] at h⟩, rfl,
    Silmaril.Proofs.Wasm.Models.V2Core.closedV_preserves,
    Silmaril.Proofs.Wasm.Models.V2Core.closedV_keeps⟩, hostEmbV_none, ?_⟩
  intro fi hfi
  have e : (ptCore emptyPt).1.funcs = [] := rfl
  rw [e] at hfi
  simp at hfi

/-- **No external address is typed in the empty Core store.** -/
theorem not_externAddrOk_empty {xa : Silmaril.Wasm.Execution.Core.ExternAddr}
    {xt : Silmaril.Wasm.Validation.CExternType} :
    ¬ Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore emptyPt).1 xa xt := by
  intro h
  induction h with
  | tag h => exact absurd h (by simp [show (ptCore emptyPt).1.tags = [] from rfl])
  | global h => exact absurd h (by simp [show (ptCore emptyPt).1.globals = [] from rfl])
  | mem h => exact absurd h (by simp [show (ptCore emptyPt).1.mems = [] from rfl])
  | table h => exact absurd h (by simp [show (ptCore emptyPt).1.tables = [] from rfl])
  | func h => exact absurd h (by simp [show (ptCore emptyPt).1.funcs = [] from rfl])
  | sub _ _ _ ih => exact ih

/-- `List.mapM` in `Option` relates the two lists elementwise. -/
theorem forall₂_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (forall₂_of_mapM hbs)

/-- A related element in the second list of a `Forall₂`. -/
theorem exists_mem_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | _, _, .nil => fun _ h => by simp at h
  | _, _, .cons hab hrest => fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, hr⟩ := exists_mem_of_forall₂ hrest x hx
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- **The segment bounds of a 2.0 module are those of its Core image.** -/
theorem segBounded_of_core {m : Module} {cm : Silmaril.Wasm.Module}
    (hcm : Module.toCore m = some cm)
    (hb : cm.elems.length ≤ 2 ^ 32 ∧ cm.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ cm.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ cm.elems, e.init.length < 2 ^ 32)) :
    SegBounded m := by
  obtain ⟨hbE, hbD, hbd, hbe⟩ := hb
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcm
  obtain ⟨_, _, _, _, elems, he, data, hd, hcm⟩ := hcm
  subst hcm
  have he₂ := forall₂_of_mapM he
  have hd₂ := forall₂_of_mapM hd
  refine ⟨he₂.length_eq ▸ hbE, hd₂.length_eq ▸ hbD, fun d hdm => ?_, fun e hem => ?_⟩
  · obtain ⟨d', hd'm, hd'⟩ := exists_mem_of_forall₂ hd₂ d hdm
    have hbytes : d'.bytes = d.bytes := by
      simp only [Data.toCore, Option.map_eq_some_iff] at hd'
      obtain ⟨_, _, rfl⟩ := hd'
      rfl
    exact hbytes ▸ hbd d' hd'm
  · obtain ⟨e', he'm, he'⟩ := exists_mem_of_forall₂ he₂ e hem
    have hinit : e'.init.length = e.init.length := by
      simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he'
      obtain ⟨init, hinit, _, _, rfl⟩ := he'
      exact mapM_length_eq hinit
    exact hinit ▸ hbe e' he'm

/-- The Core image of a module has the image of its imports. -/
theorem imports_of_toCore {m : Module} {cm : Silmaril.Wasm.Module}
    (hcm : Module.toCore m = some cm) : cm.imports = m.imports.map Import.toCore := by
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcm
  obtain ⟨_, _, _, _, _, _, _, _, hcm⟩ := hcm
  subst hcm
  rfl

/-- The empty store is typed. -/
theorem storeOk_empty : StoreOk ({} : Store Nat) := by
  constructor <;> simp

/-- **`domInstDet g` is not empty**: the empty 2.0 store with the closed host is in it, at every
grow policy. -/
theorem domInstDet_emptyPt (g : GrowKind → Nat → Nat → Nat → Bool) : domInstDet g emptyPt := by
  refine ⟨emptyPt_dom _, fun m cm xas hval hcm ⟨C, hC⟩ => ?_⟩
  obtain ⟨xtE, xtI, hok, hxas⟩ := hC.valid
  have hxas0 : xas = [] := by
    cases xas with
    | nil => rfl
    | cons x xs =>
      cases hxas with
      | cons h _ => exact absurd h not_externAddrOk_empty
  subst hxas0
  have hxtI : xtI = [] := List.forall₂_nil_left_iff.mp hxas
  subst hxtI
  have hcimp : cm.imports = [] := by
    cases hok with
    | mk _ himports => exact List.forall₂_nil_right_iff.mp himports
  have himp : m.imports = [] := by
    rw [imports_of_toCore hcm] at hcimp
    exact List.map_eq_nil_iff.mp hcimp
  obtain ⟨ixt, xt, hm⟩ := hval
  have hixt : ixt = [] := by
    cases hm with
    | mk _ himports =>
      rw [himp] at himports
      exact List.forall₂_nil_left_iff.mp himports
  subst hixt
  obtain ⟨c, hinst, hfree⟩ :=
    instantiate_empty (H := Nat) (Profile.deterministic g) hm (segBounded_of_core hcm hC.bounded)
  refine ⟨c, hinst closedV, ?_⟩
  obtain ⟨hok', -⟩ := Instantiate.ok hostOk_divV storeOk_empty (hinst divV)
  exact behavioursOf_nonempty_of_safe fun _ hsteps => (closed_safe hfree hok' hsteps).2.2

/-- **`v20instDet g`'s domain is inhabited.** -/
theorem domInstDet_nonempty (g : GrowKind → Nat → Nat → Nat → Bool) : ∃ p, domInstDet g p :=
  ⟨emptyPt, domInstDet_emptyPt g⟩

end Silmaril.Proofs.Wasm.Models.V2CoreInstDom
