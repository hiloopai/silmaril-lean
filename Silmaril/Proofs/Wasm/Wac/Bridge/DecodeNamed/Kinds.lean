module

public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeNamed.Items

/-!
# WAC bridge: decoding inverts encoding, item by item

Each constructor of the fragment `EsOk` as an `ItemSim` (`item_func`, `item_inst`,
`item_comp`, `item_res`, `item_tyOwn`, `item_tyRef`, `item_tyNom`, `item_tyVal`,
`item_tyFunc`, `item_tyInst`, `item_tyComp`), and `esOk_sim`: every list of items of the
fragment satisfies `ListSim`, by induction on `EsOk`. Instance and component types are
encoded in a nested scope (`inst_type`, `comp_type`) and shared through the cache
`kcache` in component types (`shared_sim`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef)
open DecodeEnc (typeAt_run ok_bind pure_ok ReadsI ReadsE InstOnly)
open DecodeIface (instOnly_eq cdecls_inst mem_of_lookupK)
open DecodeAnon (Ext ext_refl push_self DecVal DecDef decDef_list decDef_fixedList decDef_map
  decDef_option decDef_result decDef_tuple decDef_future decDef_stream reads_nil)

namespace DecodeNamed

attribute [local simp] ok_bind pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind

theorem throw_run {α : Type} (e : String) (δ : DScope) : (throw e : DM α).run δ = .error e := rfl

attribute [local simp] throw_run

/-! ## Steps that emit nothing -/

theorem vs_of_run {N : NomTable} {Γ : Ctx} {α : Type} {m : TM α} {σ : Scope} {δ : DScope} {a : α}
    {Q : α → DScope → Prop} (hr : m.run σ = .ok (a, σ)) (hm : M N Γ σ δ) (hq : Q a δ) :
    VS N Γ m σ δ Q :=
  ⟨a, σ, [], δ, hr, (List.append_nil _).symm, hm, rfl, ext_refl δ, reads_nil δ, hq⟩

theorem vs_get {N : NomTable} {Γ : Ctx} {α : Type} {f : Scope → TM α} {σ : Scope} {δ : DScope}
    {Q : α → DScope → Prop} (h : VS N Γ (f σ) σ δ Q) : VS N Γ (get >>= f) σ δ Q :=
  vs_congr (by simp) h

/-! ## Instance and component types -/

theorem m_nested {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} (hm : M N Γ σ δ) (b : Bool) :
    M N [] { nom := σ.nom, share := b } { outer := δ.types :: δ.outer, nom := δ.nom } := by
  rw [hm.nom]; exact m_empty b δ hm.dnom

/-- **An instance type of the fragment**, encoded in a nested scope and read back by the
decoder in a nested scope. -/
theorem inst_type {N : NomTable} {Γ : Ctx} {fs : Externs} {σ : Scope} {δ : DScope}
    (ih : ListSim N [] fs) (hm : M N Γ σ δ) :
    ∃ (D : List ComponentDecl) (δi : DScope), (nested false (exportDecls fs)).run σ = .ok (D, σ) ∧
      (decDefType (.instance (instDecls D))).run δ = .ok (.inst (dks fs), { δ with nom := δi.nom }) ∧
      ∀ p ∈ δi.nom, N.lookup p.1 = some p.2 := by
  obtain ⟨σi, E, δi, hr, hd, hmi, hreads, hinst⟩ := (ih _ _ (m_nested hm false)).2
  have hE : E = (instDecls E).map .inst := instOnly_eq hinst
  have hdecls : σi.decls = E := by simpa using hd
  have h1 := hreads [] [] []
  rw [List.append_nil, hE, cdecls_inst] at h1
  refine ⟨E, δi, by simp [nested, hr, hdecls], ?_, hmi.dnom⟩
  cases hD : (decIDecls (instDecls E) []).run { outer := δ.types :: δ.outer, nom := δ.nom } with
  | error e => simp [hD, decCDecls] at h1
  | ok p =>
    have e : p.1 = dks fs ∧ p.2 = δi := by simpa [hD, decCDecls] using h1
    simp [decDefType, inNested, hD, e.1, e.2]

/-- **A component type of the fragment.** -/
theorem comp_type {N : NomTable} {Γ : Ctx} {is fs : Externs} {σ : Scope} {δ : DScope}
    (h1 : ListSim N [] is) (h2 : ListSim N (extend [] is) fs) (hm : M N Γ σ δ) :
    ∃ (C : List ComponentDecl) (δi : DScope), (nested true (do importDecls is; exportDecls fs)).run σ = .ok (C, σ) ∧
      (decDefType (.component C)).run δ =
        .ok (.comp (dks is) (dks fs), { δ with nom := δi.nom }) ∧
      ∀ p ∈ δi.nom, N.lookup p.1 = some p.2 := by
  obtain ⟨σa, Ea, δa, hra, hda, hma, hreadsa⟩ := (h1 _ _ (m_nested hm true)).1
  obtain ⟨σb, Eb, δb, hrb, hdb, hmb, hreadsb, -⟩ := (h2 _ _ hma).2
  have hdecls : σb.decls = Ea ++ Eb := by rw [hdb, hda]; simp
  have hb : (decCDecls (Eb ++ []) ([] ++ dks is) []).run δa =
      (decCDecls [] ([] ++ dks is) ([] ++ dks fs)).run δb := hreadsb [] _ []
  have hdec : (decCDecls (Ea ++ Eb) [] []).run { outer := δ.types :: δ.outer, nom := δ.nom } =
      .ok ((dks is, dks fs), δb) := by
    rw [hreadsa, ← List.append_nil Eb, hb]
    simp [decCDecls]
  refine ⟨Ea ++ Eb, δb, by simp [nested, hra, hrb, hdecls], ?_, hmb.dnom⟩
  simp [decDefType, inNested, hdec]

theorem shared_miss {k : Kind} {m : TM Nat} {σ : Scope}
    (h : ¬ (σ.share = true ∧ ∃ j, σ.kcache.lookup k = some j)) :
    (shared k m).run σ = (do
      let j ← m
      modify fun sc : Scope => { sc with kcache := sc.kcache ++ [(k, j)] }
      pure j).run σ := by
  have h' : σ.share = false ∨ σ.kcache.lookup k = none := by
    cases hsh : σ.share <;> cases hl : σ.kcache.lookup k <;> simp_all
  rcases h' with h' | h'
  · cases hl : σ.kcache.lookup k <;> simp [shared, h', hl]
  · cases hsh : σ.share <;> simp [shared, h', hsh]

theorem cacheK_sim {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {k : Kind} {j : Nat}
    (hm : M N Γ σ δ) (hj : δ.types[j]? = some (infoK k)) :
    VS N Γ (do
      modify fun sc : Scope => { sc with kcache := sc.kcache ++ [(k, j)] }
      pure j) σ δ (fun j' δ' => δ'.types[j']? = some (infoK k)) := by
  have hkc : ∀ k' j', (k', j') ∈ σ.kcache ++ [(k, j)] → δ.types[j']? = some (infoK k') := by
    intro k' j' h
    rcases List.mem_append.1 h with h | h
    · exact hm.kc k' j' h
    · have e : (k', j') = (k, j) := List.mem_singleton.1 h
      rw [(Prod.mk.inj e).1, (Prod.mk.inj e).2]; exact hj
  have hm' : M N Γ { σ with kcache := σ.kcache ++ [(k, j)] } δ :=
    ⟨hm.size, hm.nom, hm.dnom, hm.fc, hm.vc, hm.hc, hkc, hm.res, hm.names⟩
  exact ⟨j, _, [], δ, by simp, by simp, hm', rfl, ext_refl δ, reads_nil δ, hj⟩

/-- **A shared instance or component type**: cached, or defined by `m`. -/
theorem shared_sim {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {k : Kind} {m : TM Nat}
    (hm : M N Γ σ δ) (h : VS N Γ m σ δ (fun j δ' => δ'.types[j]? = some (infoK k))) :
    VS N Γ (shared k m) σ δ (fun j δ' => δ'.types[j]? = some (infoK k)) := by
  by_cases hit : σ.share = true ∧ ∃ j, σ.kcache.lookup k = some j
  · obtain ⟨hsh, j, hl⟩ := hit
    exact vs_of_run (by simp [shared, hsh, hl]) hm (hm.kc k j (mem_of_lookupK hl))
  · exact vs_congr (shared_miss hit) (vs_bind h fun j σ1 δ1 hm1 _ hj => cacheK_sim hm1 hj)

theorem instTy_sim {N : NomTable} {Γ : Ctx} {fs : Externs} {σ : Scope} {δ : DScope}
    (ih : ListSim N [] fs) (hm : M N Γ σ δ) :
    VS N Γ (do let ds ← nested false (exportDecls fs); defTy (.instance (instDecls ds))) σ δ
      (fun j δ' => δ'.types[j]? = some (.inst (dks fs))) := by
  obtain ⟨D, δi, hr, hd, hn⟩ := inst_type ih hm
  refine vs_bind (vs_of_run (Q := fun ds δ' => ds = D ∧ δ' = δ) hr hm ⟨rfl, rfl⟩) ?_
  rintro ds σ1 δ1 hm1 - ⟨rfl, rfl⟩
  exact defTy_sim hm1 id hd rfl hn

theorem compTy_sim {N : NomTable} {Γ : Ctx} {is fs : Externs} {σ : Scope} {δ : DScope}
    (h1 : ListSim N [] is) (h2 : ListSim N (extend [] is) fs) (hm : M N Γ σ δ) :
    VS N Γ (do let ds ← nested true (do importDecls is; exportDecls fs); defTy (.component ds)) σ δ
      (fun j δ' => δ'.types[j]? = some (.comp (dks is) (dks fs))) := by
  obtain ⟨C, δi, hr, hd, hn⟩ := comp_type h1 h2 hm
  refine vs_bind (vs_of_run (Q := fun ds δ' => ds = C ∧ δ' = δ) hr hm ⟨rfl, rfl⟩) ?_
  rintro ds σ1 δ1 hm1 - ⟨rfl, rfl⟩
  exact defTy_sim hm1 id hd rfl hn

/-! ## Items that are not type items -/

theorem item_func {N : NomTable} {Γ : Ctx} {n : String} {s : Sig} (hs : SigOk Γ s) :
    ∀ σ δ, M N Γ σ δ → ItemSim N Γ Γ n (.func s) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc]
  exact vs_bind (funcTy_sim hs hm) fun j σ1 δ1 hm1 _ hj => vs_pure hm1 fun σ2 hm2 =>
    ⟨δ1, by simp [decExtern, typeAt_run hj, dk], hm2⟩

theorem item_inst {N : NomTable} {Γ : Ctx} {n : String} {i : Option String} {fs : Externs}
    (ih : ListSim N [] fs) : ∀ σ δ, M N Γ σ δ → ItemSim N Γ Γ n (.inst i fs) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc]
  exact vs_bind (shared_sim (k := .inst i fs) hm (instTy_sim ih hm)) fun j σ1 δ1 hm1 _ hj =>
    vs_pure hm1 fun σ2 hm2 => ⟨{ δ1 with insts := δ1.insts.push (dks fs) },
      by simp [decExtern, typeAt_run hj, dk, infoK], hm2.retype rfl hm2.dnom⟩

theorem item_comp {N : NomTable} {Γ : Ctx} {n : String} {i : Option String} {is fs : Externs}
    (h1 : ListSim N [] is) (h2 : ListSim N (extend [] is) fs) :
    ∀ σ δ, M N Γ σ δ → ItemSim N Γ Γ n (.comp i is fs) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc]
  exact vs_bind (shared_sim (k := .comp i is fs) hm (compTy_sim h1 h2 hm)) fun j σ1 δ1 hm1 _ hj =>
    vs_pure hm1 fun σ2 hm2 => ⟨δ1, by simp [decExtern, typeAt_run hj, dk, infoK], hm2⟩

/-! ## Type items -/

theorem namedInfo_nonres (n : String) {x : TInfo} (hx : ¬ IsRes (some x)) :
    ¬ IsRes (some (namedInfo n x)) := by
  cases x with
  | res r => exact absurd trivial hx
  | resAlias a r => exact absurd trivial hx
  | _ => exact id

/-- Declaring a type item `(type (eq j))` whose definiens `x` is not a resource. -/
theorem declare_eq {N : NomTable} {Γ : Ctx} {σ1 : Scope} {δ1 δ2 : DScope} (hm1 : M N Γ σ1 δ1)
    {n : String} {j : Nat} {x : TInfo} (hj : δ1.types[j]? = some x) (hx : ¬ IsRes (some x)) (ns : NS)
    (ht : δ2.types = δ1.types.push (namedInfo n x)) (hn : ∀ p ∈ δ2.nom, N.lookup p.1 = some p.2)
    (hy : NameAt δ2 (declS σ1 n false) n ns σ1.ntypes) :
    M N (Γ ++ [(n, ns)]) (declF n (.type (.eq j)) σ1) δ2 := by
  have hres : j ∉ σ1.resIdx := not_res hm1 hj hx
  have e : declF n (.type (.eq j)) σ1 = declS σ1 n false := by simp [declF, hres]
  rw [e]
  exact hm1.declare n ns (namedInfo n x) false ht hn
    ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h (namedInfo_nonres n hx)⟩ hy

theorem item_res {N : NomTable} {Γ : Ctx} {n : String} :
    ∀ σ δ, M N Γ σ δ → ItemSim N Γ (Γ ++ [(n, .res)]) n (.type (.resource n)) σ δ := fun σ δ hm => by
  unfold ItemSim; rw [externDesc, typeBound]
  refine vs_pure hm fun σ1 hm1 => ⟨{ δ with types := δ.types.push (.res n) },
    by simp [decExtern, pushTy, dk], ?_⟩
  exact hm1.declare n .res (.res n) true rfl hm1.dnom ⟨fun _ => trivial, fun _ => rfl⟩
    ⟨by rw [← hm1.size]; exact push_self δ _, by simp [declS]⟩

theorem item_tyOwn {N : NomTable} {Γ : Ctx} {n a : String} (ha : Γ.lookup a = some .res) :
    ∀ σ δ, M N Γ σ δ →
      ItemSim N Γ (Γ ++ [(n, .ali a)]) n (.type (.value (.own ⟨.local, a⟩))) σ δ := fun σ δ hm => by
  obtain ⟨i, hi, hat, -⟩ := hm.lookup ha
  unfold ItemSim; rw [externDesc]
  refine vs_of_run (a := .type (.eq i)) (by simp [typeBound, namedTy, hi]) hm fun σ1 hm1 =>
    ⟨{ δ with types := δ.types.push (.resAlias n a) },
      by simp [decExtern, typeAt_run hat, pushTy, namedInfo, addNom, typeKind, dk], ?_⟩
  have hres : i ∈ σ1.resIdx := (hm1.res i).2 (by rw [hat]; trivial)
  have e : declF n (.type (.eq i)) σ1 = declS σ1 n true := by simp [declF, hres]
  rw [e]
  exact hm1.declare n (.ali a) (.resAlias n a) true rfl hm1.dnom ⟨fun _ => trivial, fun _ => rfl⟩
    ⟨by rw [← hm1.size]; exact push_self δ _, by simp [declS]⟩

theorem item_tyRef {N : NomTable} {Γ : Ctx} {n a : String} (ha : Γ.lookup a = some .val) :
    ∀ σ δ, M N Γ σ δ →
      ItemSim N Γ (Γ ++ [(n, .val)]) n (.type (.value (.ref ⟨.local, a⟩))) σ δ := fun σ δ hm => by
  obtain ⟨i, hi, hat⟩ := hm.lookup ha
  have hat' : δ.types[i]? = some (.val (.ref ⟨.local, a⟩)) := hat
  unfold ItemSim; rw [externDesc]
  refine vs_of_run (a := .type (.eq i)) (by simp [typeBound, namedTy, hi]) hm fun σ1 hm1 =>
    ⟨{ δ with types := δ.types.push (.val (.ref ⟨.local, n⟩)) },
      by simp [decExtern, typeAt_run hat', pushTy, namedInfo, addNom, typeKind, dk], ?_⟩
  exact declare_eq hm1 hat' id .val rfl hm1.dnom (by rw [← hm1.size]; exact push_self δ _)

theorem item_tyNom {N : NomTable} {Γ : Ctx} {n : String} {d : Nominal} (hn : Γ.lookup n = none)
    (hN : N.lookup n = some d) (hd : NomOk Γ d) :
    ∀ σ δ, M N Γ σ δ →
      ItemSim N Γ (Γ ++ [(n, .val)]) n (.type (.value (.ref ⟨.local, n⟩))) σ δ := fun σ δ hm => by
  have hl : σ.names.lookup n = none := hm.lookup_none hn
  have hN' : σ.nom.lookup n = some d := by rw [hm.nom]; exact hN
  unfold ItemSim; rw [externDesc]
  refine vs_congr (m' := do let j ← nominalTy d; pure (ExternDesc.type (.eq j)))
    (by simp [typeBound, hl, hN']) ?_
  refine vs_bind (nominalTy_sim hd hm) fun j σ1 δ1 hm1 _ hj => vs_pure hm1 fun σ2 hm2 =>
    ⟨{ δ1 with types := δ1.types.push (.val (.ref ⟨.local, n⟩)), nom := δ1.nom ++ [(n, d)] },
      by simp [decExtern, typeAt_run hj, pushTy, namedInfo, addNom, typeKind, dk], ?_⟩
  have hnom : ∀ p ∈ δ1.nom ++ [(n, d)], N.lookup p.1 = some p.2 := by
    intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hm2.dnom p h
    · rw [List.mem_singleton.1 h]; exact hN
  exact declare_eq hm2 hj id .val rfl hnom (by rw [← hm2.size]; exact push_self δ1 _)

/-- The value type `v` the encoder returns for a type that is neither primitive nor a
named reference is an index defining that type. -/
theorem decVal_idx_of {δ : DScope} {v : ValType} {t : Ty} (h : DecVal δ v t) (hp : Plain t)
    (hnp : ∀ p, t ≠ .prim p) : ∃ j, v = .idx j ∧ δ.types[j]? = some (.val t) := by
  have h0 : (decVal v).run δ = .ok (t, δ) := h δ (ext_refl δ)
  cases v with
  | prim p => exact absurd (by simpa [decVal] using h0.symm) (hnp p)
  | idx j =>
    refine ⟨j, rfl, ?_⟩
    cases hj : δ.types[j]? with
    | none => simp [decVal, typeAt, hj] at h0
    | some x =>
      cases x with
      | val t' => simp_all [decVal, typeAt]
      | res r =>
        have e : Ty.own ⟨.local, r⟩ = t := by simpa [decVal, typeAt, hj] using h0
        have h' : Plain (Ty.own ⟨.local, r⟩) := e ▸ hp
        exact h'.elim
      | resAlias a r =>
        have e : Ty.ref ⟨.local, a⟩ = t := by simpa [decVal, typeAt, hj] using h0
        have h' : Plain (Ty.ref ⟨.local, a⟩) := e ▸ hp
        exact h'.elim
      | _ => simp [decVal, typeAt, hj] at h0

/-- The definiens of an anonymous type item, defined anew (`freshVal`). -/
def FreshOk (N : NomTable) (Γ : Ctx) (t : Ty) : Prop :=
  ∀ σ δ, M N Γ σ δ → VS N Γ (freshVal t) σ δ
    (fun o δ' => ∃ j, o = some j ∧ δ'.types[j]? = some (.val t))

theorem fresh_def {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {d : DefValType} {t : Ty}
    (hm : M N Γ σ δ) (hd : DecDef δ d t) :
    VS N Γ (do pure (some (← defTy (.val d)))) σ δ
      (fun o δ' => ∃ j, o = some j ∧ δ'.types[j]? = some (.val t)) :=
  vs_bind (defTy_val_sim hm hd) fun j _ _ hm2 _ hj => vs_pure hm2 ⟨j, rfl, hj⟩

/-- **Every anonymous type of the fragment is defined anew** by `freshVal`. -/
theorem freshVal_sim {N : NomTable} {Γ : Ctx} {t : Ty} (ht : TyOk Γ t)
    (hanon : ∀ p, t ≠ .prim p) (hb : ∀ r, t ≠ .borrow r) (hp : Plain t) : FreshOk N Γ t := by
  intro σ δ hm
  cases ht with
  | prim p => exact absurd rfl (hanon p)
  | refVal _ | refAlias _ | own _ => exact absurd hp id
  | borrowRes _ => exact absurd rfl (hb _)
  | borrowAlias _ => exact absurd rfl (hb _)
  | list h =>
    rw [freshVal]
    exact vs_bind (valTy_sim h σ δ hm) fun v σ1 δ1 hm1 _ hv => fresh_def hm1 (decDef_list hv)
  | fixedList k h =>
    rw [freshVal]
    exact vs_bind (valTy_sim h σ δ hm) fun v σ1 δ1 hm1 _ hv => fresh_def hm1 (decDef_fixedList k hv)
  | map hk hv =>
    rw [freshVal]
    exact vs_bind (valTy_sim hk σ δ hm) fun a σ1 δ1 hm1 _ ha =>
      vs_bind (valTy_sim hv σ1 δ1 hm1) fun b σ2 δ2 hm2 e2 hb' =>
        fresh_def hm2 (decDef_map (ha.mono e2) hb')
  | option h =>
    rw [freshVal]
    exact vs_bind (valTy_sim h σ δ hm) fun v σ1 δ1 hm1 _ hv => fresh_def hm1 (decDef_option hv)
  | result ha hb' =>
    rw [freshVal]
    exact vs_bind (valTyOpt_sim (fun t h => valTy_sim (ha t h)) hm) fun a σ1 δ1 hm1 _ hx =>
      vs_bind (valTyOpt_sim (fun t h => valTy_sim (hb' t h)) hm1) fun b σ2 δ2 hm2 e2 hy =>
        fresh_def hm2 (decDef_result (hx.mono e2) hy)
  | tuple h =>
    rw [freshVal]
    exact vs_bind (valTys_sim (fun t h' => valTy_sim (h t h')) hm) fun vs σ1 δ1 hm1 _ hvs =>
      fresh_def hm1 (decDef_tuple hvs)
  | future h =>
    rw [freshVal]
    exact vs_bind (valTyOpt_sim (fun t h' => valTy_sim (h t h')) hm) fun v σ1 δ1 hm1 _ hv =>
      fresh_def hm1 (decDef_future hv)
  | stream h =>
    rw [freshVal]
    exact vs_bind (valTyOpt_sim (fun t h' => valTy_sim (h t h')) hm) fun v σ1 δ1 hm1 _ hv =>
      fresh_def hm1 (decDef_stream hv)

end DecodeNamed

end Silmaril.Wasm.Wac.Bridge
