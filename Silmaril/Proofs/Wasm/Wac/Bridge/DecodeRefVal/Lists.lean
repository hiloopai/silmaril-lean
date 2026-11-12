module

public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeRefVal.Items

/-!
# WAC bridge: `ref` of a resource as a value type, every list of items

The type items of `EsOkR` (`item_resR`, `item_tyResR`, `item_tyAliR`, `item_tyRefR`,
`item_tyNomR`, `item_tyValR`, `item_tyFuncR`, `item_tyInstR`, `item_tyCompR`), and
`esOkR_sim`: every list of items of the fragment satisfies `ListSimR`, by induction on
`EsOkR`. `decls_encodeR` is `DecodeNamed.decls_encode` for the fragment: the declarations
of a package `(is, es)` are read back as `dks (rdEs [] is)`, `dks (rdEs (extendR [] is) es)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef)
open DecodeEnc (typeAt_run ok_bind pure_ok)
open DecodeAnon (Ext ext_refl push_self DecVal DecDef decDef_list decDef_fixedList decDef_map
  decDef_option decDef_result decDef_tuple decDef_future decDef_stream)
open DecodeNamed (Ctx NS M VS vs_bind vs_pure declF declS dk dks TyOk NomOk Plain tbv TbOk fresh_def
  declare_eq throw_run)

namespace DecodeRefVal

attribute [local simp] ok_bind pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind throw_run

/-! ## Read-back of type items -/

theorem rdTV_plain (Γ : Ctx) {t : Silmaril.Wasm.Wit.Binary.Ty} (hp : Plain t) : rdTV Γ t = .value (rdT Γ t) := by
  cases t <;> first | rfl | exact absurd hp id

theorem sortR_plain (Γ : Ctx) {t : Silmaril.Wasm.Wit.Binary.Ty} (hp : Plain t) : sortR Γ (.value t) = .val := by
  cases t <;> first | rfl | exact absurd hp id

theorem rdKd_res {Γ : Ctx} {a : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (hf : AliForm a t) (ha : Γ.lookup a = some .res) :
    rdKd Γ (.type (.value t)) = .type (.value (.own ⟨.local, a⟩)) := by
  rcases hf with rfl | rfl <;> simp [rdKd, rdTB, rdTV, rdAli, ha]

theorem rdKd_ali {Γ : Ctx} {a r : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (hf : AliForm a t) (ha : Γ.lookup a = some (.ali r)) :
    rdKd Γ (.type (.value t)) = .type (.value (.own ⟨.local, r⟩)) := by
  rcases hf with rfl | rfl <;> simp [rdKd, rdTB, rdTV, rdAli, ha]

theorem stepR_res {Γ : Ctx} {n a : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (hf : AliForm a t) (ha : Γ.lookup a = some .res) :
    stepR Γ (n, .type (.value t)) = Γ ++ [(n, .ali a)] := by
  rcases hf with rfl | rfl <;> simp [stepR, sortR, ha]

theorem stepR_ali {Γ : Ctx} {n a r : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (hf : AliForm a t)
    (ha : Γ.lookup a = some (.ali r)) : stepR Γ (n, .type (.value t)) = Γ ++ [(n, .ali r)] := by
  rcases hf with rfl | rfl <;> simp [stepR, sortR, ha]

theorem typeBound_ali {σ : Scope} {a : String} {t : Silmaril.Wasm.Wit.Binary.Ty} {i : Nat} (hf : AliForm a t)
    (hi : σ.names.lookup a = some i) : (typeBound (.value t)).run σ = .ok (.type (.eq i), σ) := by
  rcases hf with rfl | rfl <;> simp [typeBound, namedTy, hi]

/-! ## Resources and aliases of resources -/

theorem item_resR {N : NomTable} {Γ : Ctx} {n : String} :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ (Γ ++ [(n, .res)]) n (.type (.resource n)) σ δ := fun σ δ hm => by
  unfold ItemSimR; rw [externDesc, typeBound]
  refine vsr_pure hm fun σ1 hm1 => ⟨{ δ with types := δ.types.push (.res n) },
    by simp [decExtern, pushTy, dk, rdKd, rdTB], mr_up _ hm1 ?_⟩
  exact hm1.m.declare n .res (.res n) true rfl hm1.m.dnom ⟨fun _ => trivial, fun _ => rfl⟩
    ⟨by rw [← hm1.m.size]; exact push_self δ _, by simp [declS]⟩

/-- **`type n = own<a>` or `type n = a` of a resource `a`**: read back as `own<a>`. -/
theorem item_tyResR {N : NomTable} {Γ : Ctx} {n a : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (hf : AliForm a t)
    (ha : Γ.lookup a = some .res) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ (Γ ++ [(n, .ali a)]) n (.type (.value t)) σ δ := fun σ δ hm => by
  obtain ⟨i, hi, hat, -⟩ := hm.m.lookup ha
  have hi' : σ.names.lookup a = some i := hi
  unfold ItemSimR; rw [externDesc, rdKd_res hf ha]
  refine vsr_of_run (a := .type (.eq i)) (typeBound_ali hf hi') hm fun σ1 hm1 =>
    ⟨{ δ with types := δ.types.push (.resAlias n a) },
      by simp [decExtern, typeAt_run hat, pushTy, namedInfo, addNom, typeKind, dk], mr_up _ hm1 ?_⟩
  have hres : i ∈ (cm Γ σ1).resIdx := (hm1.m.res i).2 (by rw [hat]; trivial)
  have e : declF n (.type (.eq i)) (cm Γ σ1) = declS (cm Γ σ1) n true := by simp [declF, hres]
  rw [e]
  exact hm1.m.declare n (.ali a) (.resAlias n a) true rfl hm1.m.dnom ⟨fun _ => trivial, fun _ => rfl⟩
    ⟨by rw [← hm1.m.size]; exact push_self δ _, by simp [declS]⟩

/-- **`type n = own<a>` or `type n = a` of an alias `a` of the resource `r`**: read back
as `own<r>`, and `n` is another alias of `r`. -/
theorem item_tyAliR {N : NomTable} {Γ : Ctx} {n a r : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (hf : AliForm a t)
    (ha : Γ.lookup a = some (.ali r)) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ (Γ ++ [(n, .ali r)]) n (.type (.value t)) σ δ := fun σ δ hm => by
  obtain ⟨i, hi, hat, -⟩ := hm.m.lookup ha
  have hi' : σ.names.lookup a = some i := hi
  unfold ItemSimR; rw [externDesc, rdKd_ali hf ha]
  refine vsr_of_run (a := .type (.eq i)) (typeBound_ali hf hi') hm fun σ1 hm1 =>
    ⟨{ δ with types := δ.types.push (.resAlias n r) },
      by simp [decExtern, typeAt_run hat, pushTy, namedInfo, addNom, typeKind, dk], mr_up _ hm1 ?_⟩
  have hres : i ∈ (cm Γ σ1).resIdx := (hm1.m.res i).2 (by rw [hat]; trivial)
  have e : declF n (.type (.eq i)) (cm Γ σ1) = declS (cm Γ σ1) n true := by simp [declF, hres]
  rw [e]
  exact hm1.m.declare n (.ali r) (.resAlias n r) true rfl hm1.m.dnom ⟨fun _ => trivial, fun _ => rfl⟩
    ⟨by rw [← hm1.m.size]; exact push_self δ _, by simp [declS]⟩

/-! ## Named value types and records -/

theorem item_tyRefR {N : NomTable} {Γ : Ctx} {n a : String} (ha : Γ.lookup a = some .val) :
    ∀ σ δ, MR N Γ σ δ →
      ItemSimR N Γ (Γ ++ [(n, .val)]) n (.type (.value (.ref ⟨.local, a⟩))) σ δ := fun σ δ hm => by
  obtain ⟨i, hi, hat⟩ := hm.m.lookup ha
  have hi' : σ.names.lookup a = some i := hi
  have hat' : δ.types[i]? = some (.val (.ref ⟨.local, a⟩)) := hat
  have hk : rdKd Γ (.type (.value (.ref ⟨.local, a⟩))) = .type (.value (.ref ⟨.local, a⟩)) := by
    simp [rdKd, rdTB, rdTV, rdAli, ha]
  unfold ItemSimR; rw [externDesc, hk]
  refine vsr_of_run (a := .type (.eq i)) (by simp [typeBound, namedTy, hi']) hm fun σ1 hm1 =>
    ⟨{ δ with types := δ.types.push (.val (.ref ⟨.local, n⟩)) },
      by simp [decExtern, typeAt_run hat', pushTy, namedInfo, addNom, typeKind, dk], ?_⟩
  exact mr_up _ hm1 (declare_eq hm1.m hat' id .val rfl hm1.m.dnom (by rw [← hm1.m.size]; exact push_self δ _))

theorem indep_mapM {β γ : Type} {g : β → TM γ} : ∀ {l : List β}, (∀ x ∈ l, Indep (g x)) →
    Indep (l.mapM g)
  | [], _ => by rw [List.mapM_nil]; exact indep_pure _
  | x :: _, h => by
    rw [List.mapM_cons]
    exact indep_bind (h x List.mem_cons_self) fun _ =>
      indep_bind (indep_mapM fun y hy => h y (List.mem_cons_of_mem _ hy)) fun _ => indep_pure _

theorem tyOkR_of_tyOk {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : TyOk Γ t) : TyOkR Γ t := by
  induction h with
  | prim p => exact .prim p
  | refVal h => exact .refVal h
  | refAlias h => exact .refAlias h
  | own h => exact .own h
  | borrowRes h => exact .borrowRes h
  | borrowAlias h => exact .borrowAlias h
  | list _ ih => exact .list ih
  | fixedList n _ ih => exact .fixedList n ih
  | map _ _ ihk ihv => exact .map ihk ihv
  | option _ ih => exact .option ih
  | result _ _ iha ihb => exact .result iha ihb
  | tuple _ ih => exact .tuple ih
  | future _ ih => exact .future ih
  | stream _ ih => exact .stream ih

theorem indep_nominalTy {Γ : Ctx} {d : Nominal} (hd : NomOk Γ d) : Indep (nominalTy d) := by
  cases d with
  | record fs =>
    exact indep_bind (indep_mapM fun f hf => indep_bind (indep_valTy (tyOkR_of_tyOk (hd f hf)))
      fun _ => indep_pure _) fun _ => indep_defTy _
  | variant cs =>
    exact indep_bind (indep_mapM fun c hc => indep_bind (indep_valTyOpt fun t ht =>
      indep_valTy (tyOkR_of_tyOk (hd c hc t ht))) fun _ => indep_pure _) fun _ => indep_defTy _
  | enum _ => exact indep_defTy _
  | flags _ => exact indep_defTy _

theorem item_tyNomR {N : NomTable} {Γ : Ctx} {n : String} {d : Nominal} (hn : Γ.lookup n = none)
    (hN : N.lookup n = some d) (hd : NomOk Γ d) :
    ∀ σ δ, MR N Γ σ δ →
      ItemSimR N Γ (Γ ++ [(n, .val)]) n (.type (.value (.ref ⟨.local, n⟩))) σ δ := fun σ δ hm => by
  have hl : σ.names.lookup n = none := hm.m.lookup_none hn
  have hN' : σ.nom.lookup n = some d := by
    rw [show σ.nom = (cm Γ σ).nom from rfl, hm.m.nom]; exact hN
  have hk : rdKd Γ (.type (.value (.ref ⟨.local, n⟩))) = .type (.value (.ref ⟨.local, n⟩)) := by
    simp [rdKd, rdTB, rdTV, rdAli, hn]
  unfold ItemSimR; rw [externDesc, hk]
  refine vsr_congr (m' := do let j ← nominalTy d; pure (ExternDesc.type (.eq j)))
    (by simp [typeBound, hl, hN']) ?_
  refine vsr_bind (vsr_of_vs (indep_nominalTy hd) hm (DecodeNamed.nominalTy_sim hd hm.m))
    fun j σ1 δ1 hm1 _ hj => vsr_pure hm1 fun σ2 hm2 =>
    ⟨{ δ1 with types := δ1.types.push (.val (.ref ⟨.local, n⟩)), nom := δ1.nom ++ [(n, d)] },
      by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk], ?_⟩
  have hnom : ∀ p ∈ δ1.nom ++ [(n, d)], N.lookup p.1 = some p.2 := by
    intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hm2.m.dnom p h
    · rw [List.mem_singleton.1 h]; exact hN
  exact mr_up _ hm2 (declare_eq hm2.m hj id .val rfl hnom (by rw [← hm2.m.size]; exact push_self δ1 _))

/-! ## Anonymous, primitive and handle type items -/

/-- The definiens of an anonymous type item, defined anew, read back as `rdT Γ t`. -/
def FreshOkR (N : NomTable) (Γ : Ctx) (t : Silmaril.Wasm.Wit.Binary.Ty) : Prop :=
  ∀ σ δ, M N Γ σ δ → VS N Γ (freshVal t) σ δ
    (fun o δ' => ∃ j, o = some j ∧ δ'.types[j]? = some (.val (rdT Γ t)))

theorem freshVal_simR0 {N : NomTable} {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (ht : TyOkR Γ t)
    (hanon : ∀ p, t ≠ .prim p) (hb : ∀ r, t ≠ .borrow r) (hp : Plain t) : FreshOkR N Γ t := by
  intro σ δ hm
  cases ht with
  | prim p => exact absurd rfl (hanon p)
  | refVal _ | refAlias _ | refRes _ | own _ | ownAlias _ => exact absurd hp id
  | borrowRes _ | borrowAlias _ => exact absurd rfl (hb _)
  | list h => exact vs_bind (valTy_simR0 h σ δ hm) fun v σ1 δ1 hm1 _ hv => fresh_def hm1 (decDef_list hv)
  | fixedList k h =>
    exact vs_bind (valTy_simR0 h σ δ hm) fun v σ1 δ1 hm1 _ hv => fresh_def hm1 (decDef_fixedList k hv)
  | map hk hv =>
    exact vs_bind (valTy_simR0 hk σ δ hm) fun a σ1 δ1 hm1 _ ha =>
      vs_bind (valTy_simR0 hv σ1 δ1 hm1) fun b σ2 δ2 hm2 e2 hb' =>
        fresh_def hm2 (decDef_map (ha.mono e2) hb')
  | option h =>
    exact vs_bind (valTy_simR0 h σ δ hm) fun v σ1 δ1 hm1 _ hv => fresh_def hm1 (decDef_option hv)
  | result ha hb' =>
    exact vs_bind (valTyOpt_simR0 (fun t h => valTy_simR0 (ha t h)) hm) fun a σ1 δ1 hm1 _ hx =>
      vs_bind (valTyOpt_simR0 (fun t h => valTy_simR0 (hb' t h)) hm1) fun b σ2 δ2 hm2 e2 hy =>
        fresh_def hm2 (decDef_result (hx.mono e2) hy)
  | tuple h =>
    exact vs_bind (valTys_simR0 (fun t h' => valTy_simR0 (h t h')) hm) fun vs σ1 δ1 hm1 _ hvs =>
      fresh_def hm1 (decDef_tuple hvs)
  | future h =>
    exact vs_bind (valTyOpt_simR0 (fun t h' => valTy_simR0 (h t h')) hm) fun v σ1 δ1 hm1 _ hv =>
      fresh_def hm1 (decDef_future hv)
  | stream h =>
    exact vs_bind (valTyOpt_simR0 (fun t h' => valTy_simR0 (h t h')) hm) fun v σ1 δ1 hm1 _ hv =>
      fresh_def hm1 (decDef_stream hv)

theorem tyOk_borrow {Γ : Ctx} {r : TyRef} (h : TyOkR Γ (.borrow r)) : TyOk Γ (.borrow r) := by
  cases h with
  | borrowRes h => exact .borrowRes h
  | borrowAlias h => exact .borrowAlias h

theorem tbv_simR0 {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {t : Silmaril.Wasm.Wit.Binary.Ty} (ht : TyOkR Γ t)
    (hp : Plain t) (hm : M N Γ σ δ) : VS N Γ (tbv t) σ δ (TbOk (rdT Γ t)) := by
  by_cases hpr : ∃ p, t = .prim p
  · obtain ⟨p, rfl⟩ := hpr
    exact DecodeNamed.tbv_prim p hm
  by_cases hbr : ∃ r, t = .borrow r
  · obtain ⟨r, rfl⟩ := hbr
    exact DecodeNamed.tbv_borrow (tyOk_borrow ht) hm
  refine DecodeNamed.vs_get (vs_bind (freshVal_simR0 ht (fun p e => hpr ⟨p, e⟩) (fun r e => hbr ⟨r, e⟩)
    hp σ δ hm) fun o σ1 δ1 hm1 _ ho => ?_)
  obtain ⟨j, rfl, hj⟩ := ho
  exact vs_pure hm1 ⟨j, rfl, hj⟩

theorem indep_freshVal {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (ht : TyOkR Γ t) : Indep (freshVal t) := by
  cases ht with
  | prim _ | refVal _ | refAlias _ | refRes _ | own _ | ownAlias _ | borrowRes _ | borrowAlias _ =>
    exact indep_pure _
  | list h | option h | fixedList _ h =>
    exact indep_bind (indep_valTy h) fun _ => indep_bind (indep_defTy _) fun _ => indep_pure _
  | map hk hv =>
    exact indep_bind (indep_valTy hk) fun _ => indep_bind (indep_valTy hv) fun _ =>
      indep_bind (indep_defTy _) fun _ => indep_pure _
  | result ha hb =>
    exact indep_bind (indep_valTyOpt fun t h => indep_valTy (ha t h)) fun _ =>
      indep_bind (indep_valTyOpt fun t h => indep_valTy (hb t h)) fun _ =>
        indep_bind (indep_defTy _) fun _ => indep_pure _
  | tuple h =>
    exact indep_bind (indep_valTys fun t h' => indep_valTy (h t h')) fun _ =>
      indep_bind (indep_defTy _) fun _ => indep_pure _
  | future h | stream h =>
    exact indep_bind (indep_valTyOpt fun t h' => indep_valTy (h t h')) fun _ =>
      indep_bind (indep_defTy _) fun _ => indep_pure _

theorem indep_tbv {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (ht : TyOkR Γ t) : Indep (tbv t) := by
  unfold tbv
  refine indep_get (fun _ _ _ => rfl) fun _ => indep_bind (indep_freshVal ht) fun o => ?_
  split
  · exact indep_pure _
  · refine indep_bind (indep_valTy ht) fun v => ?_
    split
    · exact indep_pure _
    · exact indep_bind (indep_defTy _) fun _ => indep_pure _

theorem item_tyValR {N : NomTable} {Γ : Ctx} {n : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (hp : Plain t) (ht : TyOkR Γ t) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ (Γ ++ [(n, .val)]) n (.type (.value t)) σ δ := fun σ δ hm => by
  have hk : rdKd Γ (.type (.value t)) = .type (.value (rdT Γ t)) := by
    simp only [rdKd, rdTB, rdTV_plain Γ hp]
  unfold ItemSimR; rw [externDesc, DecodeNamed.typeBound_plain hp, hk]
  refine vsr_mono (vsr_of_vs (indep_tbv ht) hm (tbv_simR0 ht hp hm.m)) fun d δ1 hq σ1 hm1 => ?_
  obtain ⟨j, rfl, hj⟩ := hq
  refine ⟨{ δ1 with types := δ1.types.push (.val (.ref ⟨.local, n⟩)) },
    by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk], ?_⟩
  exact mr_up _ hm1 (declare_eq hm1.m hj id .val rfl hm1.m.dnom (by rw [← hm1.m.size]; exact push_self δ1 _))

/-! ## Function, instance and component type items -/

theorem item_tyFuncR {N : NomTable} {Γ : Ctx} {n : String} {s : Sig} (hs : SigOkR Γ s) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ (Γ ++ [(n, .other)]) n (.type (.func s)) σ δ := fun σ δ hm => by
  unfold ItemSimR; rw [externDesc, typeBound]
  exact vsr_bind (funcTy_simR hs hm) fun j σ1 δ1 hm1 _ hj => vsr_pure hm1 fun σ2 hm2 =>
    ⟨{ δ1 with types := δ1.types.push (.func (rdS Γ s)) },
      by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk, rdKd, rdTB],
      mr_up _ hm2 (declare_eq hm2.m hj id .other rfl hm2.m.dnom trivial)⟩

theorem item_tyInstR {N : NomTable} {Γ : Ctx} {n : String} {i : Option String} {fs : Externs}
    (ih : ListSimR N [] fs) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ (Γ ++ [(n, .other)]) n (.type (.inst i fs)) σ δ := fun σ δ hm => by
  unfold ItemSimR; rw [externDesc, typeBound]
  obtain ⟨D, δi, hr, hd, hn⟩ := inst_typeR ih hm
  refine vsr_bind (vsr_of_run (Q := fun ds δ' => ds = D ∧ δ' = δ) hr hm ⟨rfl, rfl⟩) ?_
  rintro ds σ1 δ1 hm1 - ⟨rfl, rfl⟩
  exact vsr_bind (defTy_simR hm1 id hd rfl hn) fun j σ2 δ2 hm2 _ hj => vsr_pure hm2 fun σ3 hm3 =>
    ⟨{ δ2 with types := δ2.types.push (.inst (dks (rdEs [] fs))) },
      by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk, rdKd, rdTB],
      mr_up _ hm3 (declare_eq hm3.m hj id .other rfl hm3.m.dnom trivial)⟩

theorem item_tyCompR {N : NomTable} {Γ : Ctx} {n : String} {i : Option String} {is fs : Externs}
    (h1 : ListSimR N [] is) (h2 : ListSimR N (extendR [] is) fs) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ (Γ ++ [(n, .other)]) n (.type (.comp i is fs)) σ δ := fun σ δ hm => by
  unfold ItemSimR; rw [externDesc, typeBound]
  obtain ⟨C, δi, hr, hd, hn⟩ := comp_typeR h1 h2 hm
  refine vsr_bind (vsr_of_run (Q := fun ds δ' => ds = C ∧ δ' = δ) hr hm ⟨rfl, rfl⟩) ?_
  rintro ds σ1 δ1 hm1 - ⟨rfl, rfl⟩
  exact vsr_bind (defTy_simR hm1 id hd rfl hn) fun j σ2 δ2 hm2 _ hj => vsr_pure hm2 fun σ3 hm3 =>
    ⟨{ δ2 with types := δ2.types.push (.comp (dks (rdEs [] is)) (dks (rdEs (extendR [] is) fs))) },
      by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk, rdKd, rdTB],
      mr_up _ hm3 (declare_eq hm3.m hj id .other rfl hm3.m.dnom trivial)⟩

/-! ## Lists -/

/-- **Every list of items of the fragment** is encoded as declarations that the decoder
reads back as `dks (rdEs Γ es)`. -/
theorem esOkR_sim {N : NomTable} {Γ : Ctx} {es : Externs} (h : EsOkR N Γ es) : ListSimR N Γ es := by
  induction h with
  | nil => exact listSimR_nil _ _
  | func hs _ ih => exact listSimR_cons (item_funcR hs) rfl ih
  | value ht _ ih => exact listSimR_cons (item_valueR ht) rfl ih
  | inst _ _ ihf ih => exact listSimR_cons (item_instR ihf) rfl ih
  | comp _ _ _ ih1 ih2 ih => exact listSimR_cons (item_compR ih1 ih2) rfl ih
  | res _ ih => exact listSimR_cons item_resR rfl ih
  | tyRes hf ha _ ih => exact listSimR_cons (item_tyResR hf ha) (stepR_res hf ha) ih
  | tyAli hf ha _ ih => exact listSimR_cons (item_tyAliR hf ha) (stepR_ali hf ha) ih
  | tyRef ha _ ih => exact listSimR_cons (item_tyRefR ha) (by simp [stepR, sortR, ha]) ih
  | tyNom hn hN hd _ ih => exact listSimR_cons (item_tyNomR hn hN hd) (by simp [stepR, sortR, hn]) ih
  | tyVal hp ht _ ih => exact listSimR_cons (item_tyValR hp ht) (by simp only [stepR, sortR_plain _ hp]) ih
  | tyFunc hs _ ih => exact listSimR_cons (item_tyFuncR hs) rfl ih
  | tyInst _ _ ihf ih => exact listSimR_cons (item_tyInstR ihf) rfl ih
  | tyComp _ _ _ ih1 ih2 ih => exact listSimR_cons (item_tyCompR ih1 ih2) rfl ih

/-- An empty decoder scope whose nominal table comes from `N` matches the empty encoder
scope. -/
theorem mr_start (N : NomTable) (b : Bool) {δ : DScope} (hδ : δ.types = #[])
    (hn : ∀ p ∈ δ.nom, N.lookup p.1 = some p.2) : MR N [] { share := b, nom := N } δ :=
  ⟨DecodeNamed.m_start N b hδ hn, fun _ _ h => absurd h (by simp)⟩

/-- **The declarations of a package of the fragment are read back** as
`dks (rdEs [] is)`, `dks (rdEs (extendR [] is) es)`, from any empty decoder scope. -/
theorem decls_encodeR {N : NomTable} (b : Bool) {is es : Externs} (his : EsOkR N [] is)
    (hes : EsOkR N (extendR [] is) es) {δ : DScope} (hδ : δ.types = #[])
    (hn : ∀ p ∈ δ.nom, N.lookup p.1 = some p.2) :
    ∃ σ δ', ((do importDecls is; exportDecls es : TM Unit)).run { share := b, nom := N } = .ok ((), σ) ∧
      (decCDecls σ.decls [] []).run δ = .ok ((dks (rdEs [] is), dks (rdEs (extendR [] is) es)), δ') ∧
      ∀ p ∈ δ'.nom, N.lookup p.1 = some p.2 := by
  obtain ⟨σ1, E1, δ1, hr1, hd1, hm1, hreads1⟩ := (esOkR_sim his _ _ (mr_start N b hδ hn)).1
  obtain ⟨σ2, E2, δ2, hr2, hd2, hm2, hreads2, -⟩ := (esOkR_sim hes σ1 δ1 hm1).2
  have e : σ2.decls = E1 ++ (E2 ++ []) := by rw [hd2, hd1]; simp
  have h2 : (decCDecls (E2 ++ []) ([] ++ dks (rdEs [] is)) []).run δ1 =
      (decCDecls [] ([] ++ dks (rdEs [] is)) ([] ++ dks (rdEs (extendR [] is) es))).run δ2 :=
    hreads2 [] _ []
  refine ⟨σ2, δ2, by simp [hr1, hr2], ?_, hm2.m.dnom⟩
  rw [e, hreads1, h2]
  simp [decCDecls]

end DecodeRefVal

end Silmaril.Wasm.Wac.Bridge
