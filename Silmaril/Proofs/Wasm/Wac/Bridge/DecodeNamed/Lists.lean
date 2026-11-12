module

public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeNamed.Kinds

/-!
# WAC bridge: decoding inverts encoding on every list of items of the fragment

The remaining type items (`item_tyVal`, `item_tyFunc`, `item_tyInst`, `item_tyComp`) and
`esOk_sim`: by induction on the fragment `EsOk`, every list of items is encoded as import
and export declarations that the decoder reads back as `dks` of the items
(`ListSim`), the nested instance and component types included.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef)
open DecodeEnc (typeAt_run ok_bind pure_ok)
open DecodeAnon (Ext ext_refl push_self DecVal DecDef)

namespace DecodeNamed

attribute [local simp] ok_bind pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind throw_run

theorem vs_mono {N : NomTable} {Γ : Ctx} {α : Type} {m : TM α} {σ : Scope} {δ : DScope}
    {Q Q' : α → DScope → Prop} (h : VS N Γ m σ δ Q) (k : ∀ a δ', Q a δ' → Q' a δ') : VS N Γ m σ δ Q' := by
  obtain ⟨a, σ', E, δ', hr, hd, hm, hs, he, hR, hq⟩ := h
  exact ⟨a, σ', E, δ', hr, hd, hm, hs, he, hR, k a δ' hq⟩

/-! ## Anonymous, primitive and handle type items -/

/-- The branch of `typeBound (.value t)` for a type that is neither `own` nor a named
reference. -/
def tbv (t : Ty) : TM ExternDesc := do
  let _s ← get
  match ← freshVal t with
  | some i => pure (.type (.eq i))
  | none =>
    match ← valTy t with
    | .idx i => pure (.type (.eq i))
    | .prim p => pure (.type (.eq (← defTy (.val (.prim p)))))

theorem typeBound_plain {t : Ty} (hp : Plain t) : typeBound (.value t) = tbv t := by
  cases t <;> first | rfl | exact absurd hp id

theorem sortOf_plain {t : Ty} (hp : Plain t) : sortOf (.value t) = .val := by
  cases t <;> first | rfl | exact absurd hp id

/-- What a plain type item's descriptor is: `(type (eq j))`, `j` defining the type. -/
def TbOk (t : Ty) (d : ExternDesc) (δ : DScope) : Prop := ∃ j, d = .type (.eq j) ∧ δ.types[j]? = some (.val t)

theorem tbv_prim {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} (p : PrimValType) (hm : M N Γ σ δ) :
    VS N Γ (tbv (.prim p)) σ δ (TbOk (.prim p)) := by
  have hd : DecDef δ (.prim p) (.prim p) := fun _ _ => rfl
  have hrun : (tbv (.prim p)).run σ = (do let j ← defTy (.val (.prim p)); pure (ExternDesc.type (.eq j))).run σ := by
    simp [tbv, freshVal, valTy]
  exact vs_congr hrun (vs_bind (defTy_val_sim hm hd) fun j σ1 δ1 hm1 _ hj => vs_pure hm1 ⟨j, rfl, hj⟩)

theorem tbv_borrow {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {r : TyRef} (ht : TyOk Γ (.borrow r))
    (hm : M N Γ σ δ) : VS N Γ (tbv (.borrow r)) σ δ (TbOk (.borrow r)) := by
  have hrun : (tbv (.borrow r)).run σ = (do
      match ← valTy (.borrow r) with
      | .idx i => pure (ExternDesc.type (.eq i))
      | .prim p => pure (.type (.eq (← defTy (.val (.prim p)))))).run σ := by
    simp [tbv, freshVal]
  refine vs_congr hrun (vs_bind (valTy_sim ht σ δ hm) fun v σ1 δ1 hm1 _ hv => ?_)
  obtain ⟨j, rfl, hj⟩ := decVal_idx_of hv trivial (fun p e => Ty.noConfusion e)
  exact vs_pure hm1 ⟨j, rfl, hj⟩

theorem tbv_anon {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {t : Ty} (ht : TyOk Γ t)
    (hanon : ∀ p, t ≠ .prim p) (hb : ∀ r, t ≠ .borrow r) (hp : Plain t) (hm : M N Γ σ δ) :
    VS N Γ (tbv t) σ δ (TbOk t) := by
  refine vs_get (vs_bind (freshVal_sim ht hanon hb hp σ δ hm) fun o σ1 δ1 hm1 _ ho => ?_)
  obtain ⟨j, rfl, hj⟩ := ho
  exact vs_pure hm1 ⟨j, rfl, hj⟩

theorem tbv_sim {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {t : Ty} (ht : TyOk Γ t)
    (hp : Plain t) (hm : M N Γ σ δ) : VS N Γ (tbv t) σ δ (TbOk t) := by
  by_cases hpr : ∃ p, t = .prim p
  · obtain ⟨p, rfl⟩ := hpr
    exact tbv_prim p hm
  by_cases hbr : ∃ r, t = .borrow r
  · obtain ⟨r, rfl⟩ := hbr
    exact tbv_borrow ht hm
  exact tbv_anon ht (fun p e => hpr ⟨p, e⟩) (fun r e => hbr ⟨r, e⟩) hp hm

theorem item_tyVal {N : NomTable} {Γ : Ctx} {n : String} {t : Ty} (hp : Plain t) (ht : TyOk Γ t) :
    ∀ σ δ, M N Γ σ δ → ItemSim N Γ (Γ ++ [(n, .val)]) n (.type (.value t)) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc, typeBound_plain hp]
  refine vs_mono (tbv_sim ht hp hm) fun d δ1 hq σ1 hm1 => ?_
  obtain ⟨j, rfl, hj⟩ := hq
  refine ⟨{ δ1 with types := δ1.types.push (.val (.ref ⟨.local, n⟩)) },
    by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk], ?_⟩
  exact declare_eq hm1 hj id .val rfl hm1.dnom (by rw [← hm1.size]; exact push_self δ1 _)

/-! ## Function, instance and component type items -/

theorem item_tyFunc {N : NomTable} {Γ : Ctx} {n : String} {s : Sig} (hs : SigOk Γ s) :
    ∀ σ δ, M N Γ σ δ → ItemSim N Γ (Γ ++ [(n, .other)]) n (.type (.func s)) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc, typeBound]
  exact vs_bind (funcTy_sim hs hm) fun j σ1 δ1 hm1 _ hj => vs_pure hm1 fun σ2 hm2 =>
    ⟨{ δ1 with types := δ1.types.push (.func s) },
      by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk],
      declare_eq hm2 hj id .other rfl hm2.dnom trivial⟩

theorem item_tyInst {N : NomTable} {Γ : Ctx} {n : String} {i : Option String} {fs : Externs}
    (ih : ListSim N [] fs) :
    ∀ σ δ, M N Γ σ δ → ItemSim N Γ (Γ ++ [(n, .other)]) n (.type (.inst i fs)) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc, typeBound]
  obtain ⟨D, δi, hr, hd, hn⟩ := inst_type ih hm
  refine vs_bind (vs_of_run (Q := fun ds δ' => ds = D ∧ δ' = δ) hr hm ⟨rfl, rfl⟩) ?_
  rintro ds σ1 δ1 hm1 - ⟨rfl, rfl⟩
  exact vs_bind (defTy_sim hm1 id hd rfl hn) fun j σ2 δ2 hm2 _ hj => vs_pure hm2 fun σ3 hm3 =>
    ⟨{ δ2 with types := δ2.types.push (.inst (dks fs)) },
      by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk],
      declare_eq hm3 hj id .other rfl hm3.dnom trivial⟩

theorem item_tyComp {N : NomTable} {Γ : Ctx} {n : String} {i : Option String} {is fs : Externs}
    (h1 : ListSim N [] is) (h2 : ListSim N (extend [] is) fs) :
    ∀ σ δ, M N Γ σ δ → ItemSim N Γ (Γ ++ [(n, .other)]) n (.type (.comp i is fs)) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc, typeBound]
  obtain ⟨C, δi, hr, hd, hn⟩ := comp_type h1 h2 hm
  refine vs_bind (vs_of_run (Q := fun ds δ' => ds = C ∧ δ' = δ) hr hm ⟨rfl, rfl⟩) ?_
  rintro ds σ1 δ1 hm1 - ⟨rfl, rfl⟩
  exact vs_bind (defTy_sim hm1 id hd rfl hn) fun j σ2 δ2 hm2 _ hj => vs_pure hm2 fun σ3 hm3 =>
    ⟨{ δ2 with types := δ2.types.push (.comp (dks is) (dks fs)) },
      by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk],
      declare_eq hm3 hj id .other rfl hm3.dnom trivial⟩

/-! ## Lists -/

/-- **Every list of items of the fragment** is encoded as declarations that the decoder
reads back as `dks` of the items. -/
theorem esOk_sim {N : NomTable} {Γ : Ctx} {es : Externs} (h : EsOk N Γ es) : ListSim N Γ es := by
  induction h with
  | nil => exact listSim_nil _ _
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

/-- The empty scopes of a package's component type match. -/
theorem m_top (N : NomTable) : M N [] { share := true, nom := N } {} :=
  ⟨rfl, rfl, fun _ h => absurd h (by simp), fun _ _ h => absurd h (by simp),
    fun _ _ h => absurd h (by simp), fun _ _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp),
    fun _ => ⟨fun h => absurd h (by simp), fun h => by simp [IsRes] at h⟩, .nil⟩

end DecodeNamed

end Silmaril.Wasm.Wac.Bridge
