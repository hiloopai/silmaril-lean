module

public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeRefVal.Val

/-!
# WAC bridge: `ref` of a resource as a value type, the item level

Against the invariant `MR` of `Silmaril.Proofs.Wasm.Wac.Bridge.DecodeRefVal.Val`:

* `ItemSimR`, `ListSimR`: `DecodeNamed.ItemSim` and `ListSim` with `MR`, reading back
  `dk n (rdKd Γ k)` and `dks (rdEs Γ es)`;
* `shared_simR`: the cache of instance and component types, keyed by the kinds as
  written and decoded as `infoK (rdKd [] k)`;
* `inst_typeR`, `comp_typeR`: nested scopes, in which `MR` starts empty;
* the items that are not type items, the resource and alias type items, and
  `listSimR_cons`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef)
open DecodeEnc (typeAt_run ok_bind pure_ok ReadsI ReadsE InstOnly)
open DecodeIface (instOnly_eq cdecls_inst mem_of_lookupK dec_import_gen dec_export_gen)
open DecodeAnon (Ext ext_refl push_self DecVal reads_nil)
open DecodeNamed (Ctx NS M declF declS dk dks infoK m_nested shared_miss importDecls_run
  exportDecls_run declF_decls declF_decls' throw_run)

namespace DecodeRefVal

attribute [local simp] ok_bind pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind throw_run

/-! ## `MR` and the encoder's other steps -/

theorem MR.withDecls {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} (hm : MR N Γ σ δ)
    (ds : List ComponentDecl) : MR N Γ { σ with decls := ds } δ :=
  ⟨hm.m.withDecls ds, hm.fok⟩

theorem MR.retype {N : NomTable} {Γ : Ctx} {σ : Scope} {δ δ' : DScope} (hm : MR N Γ σ δ)
    (e : δ'.types = δ.types) (hn : ∀ p ∈ δ'.nom, N.lookup p.1 = some p.2) : MR N Γ σ δ' :=
  ⟨hm.m.retype e hn, hm.fok⟩

theorem declF_fcache (n : String) (d : ExternDesc) (σ : Scope) : (declF n d σ).fcache = σ.fcache := by
  cases d with
  | type b => cases b <;> rfl
  | _ => rfl

theorem cm_declF (Γ : Ctx) (n : String) (d : ExternDesc) (σ : Scope) :
    cm Γ (declF n d σ) = declF n d (cm Γ σ) := by
  cases d with
  | type b => cases b <;> rfl
  | _ => rfl

/-- **Declaring an item** with a grown context: from the declaration in `cm Γ σ`. -/
theorem mr_up {N : NomTable} {Γ : Ctx} (Δ : Ctx) {σ : Scope} {δ δ' : DScope} {n : String}
    {d : ExternDesc} (hm : MR N Γ σ δ) (h : M N (Γ ++ Δ) (declF n d (cm Γ σ)) δ') :
    MR N (Γ ++ Δ) (declF n d σ) δ' := by
  have hf : ∀ s j, (s, j) ∈ (declF n d σ).fcache → SigOkR Γ s := fun s j hs =>
    hm.fok s j (declF_fcache n d σ ▸ hs)
  have e : cm (Γ ++ Δ) (declF n d σ) = declF n d (cm Γ σ) := by rw [cm_app Δ hf, cm_declF]
  exact ⟨e ▸ h, fun s j hs => sigOkR_app Δ (hf s j hs)⟩

/-- The empty scope of a nested scope. -/
theorem mr_nested {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} (hm : MR N Γ σ δ) (b : Bool) :
    MR N [] { nom := σ.nom, share := b } { outer := δ.types :: δ.outer, nom := δ.nom } :=
  ⟨m_nested hm.m b, fun _ _ h => absurd h (by simp)⟩

/-! ## Items and lists -/

/-- **One item** against `MR`: the decoder reads it as `dk n (rdKd Γ k)`. -/
def ItemSimR (N : NomTable) (Γ Γ' : Ctx) (n : String) (k : Kind) (σ : Scope) (δ : DScope) : Prop :=
  VSR N Γ (externDesc k) σ δ (fun d δ1 => ∀ σ1, MR N Γ σ1 δ1 →
    ∃ δ2, (decExtern n d).run δ1 = .ok (dk n (rdKd Γ k), δ2) ∧ MR N Γ' (declF n d σ1) δ2)

/-- **A list of items** against `MR`: read back as `dks (rdEs Γ es)`. -/
def ListSimR (N : NomTable) (Γ : Ctx) (es : Externs) : Prop :=
  ∀ σ δ, MR N Γ σ δ →
    (∃ σ' E δ', (importDecls es).run σ = .ok ((), σ') ∧ σ'.decls = σ.decls ++ E ∧
      MR N (extendR Γ es) σ' δ' ∧ ReadsI (dks (rdEs Γ es)) E δ δ') ∧
    (∃ σ' E δ', (exportDecls es).run σ = .ok ((), σ') ∧ σ'.decls = σ.decls ++ E ∧
      MR N (extendR Γ es) σ' δ' ∧ ReadsE (dks (rdEs Γ es)) E δ δ' ∧ InstOnly E)

theorem listSimR_nil (N : NomTable) (Γ : Ctx) : ListSimR N Γ [] := fun σ δ hm =>
  ⟨⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, fun rest is es => by simp [dks, rdEs]⟩,
    ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, fun rest is es => by simp [dks, rdEs],
      fun _ h => absurd h List.not_mem_nil⟩⟩

/-- **Items one by one.** -/
theorem listSimR_cons {N : NomTable} {Γ Γ' : Ctx} {n : String} {k : Kind} {es : Externs}
    (hk : ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ Γ' n k σ δ) (hx : stepR Γ (n, k) = Γ')
    (ih : ListSimR N Γ' es) : ListSimR N Γ ((n, k) :: es) := by
  intro σ δ hm
  obtain ⟨d, σ1, E1, δ1, hr1, hd1, hm1, -, -, hR1, hq⟩ := hk σ δ hm
  obtain ⟨δ2, hx2, hm2⟩ := hq σ1 hm1
  have hmI : MR N Γ' (declF n d { σ1 with decls := σ1.decls ++ [.import ⟨n, .plain0⟩ d] }) δ2 := by
    rw [declF_decls]; exact hm2.withDecls _
  have hmE : MR N Γ' (declF n d { σ1 with decls := σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ d)] }) δ2 := by
    rw [declF_decls]; exact hm2.withDecls _
  have hext : extendR Γ ((n, k) :: es) = extendR Γ' es := by rw [← hx]; rfl
  have hrd : rdEs Γ ((n, k) :: es) = (n, rdKd Γ k) :: rdEs Γ' es := by rw [← hx]; rfl
  obtain ⟨σ', E, δ', hr, hd, hm', hreads⟩ := (ih _ δ2 hmI).1
  obtain ⟨σ'', F, δ'', hr', hd', hm'', hreads', hinst⟩ := (ih _ δ2 hmE).2
  refine ⟨⟨σ', E1 ++ .import ⟨n, .plain0⟩ d :: E, δ', ?_, ?_, hext ▸ hm', ?_⟩,
    ⟨σ'', E1 ++ .inst (.export ⟨n, .plain0⟩ d) :: F, δ'', ?_, ?_, hext ▸ hm'', ?_, ?_⟩⟩
  · rw [importDecls_run, hr1]; exact hr
  · rw [hd, declF_decls', hd1]; simp
  · intro rest is es'
    rw [List.append_assoc, hR1.2, List.cons_append, dec_import_gen hx2, hreads, hrd]
    simp [dks]
  · rw [exportDecls_run, hr1]; exact hr'
  · rw [hd', declF_decls', hd1]; simp
  · intro rest is es'
    rw [List.append_assoc, hR1.2, List.cons_append, dec_export_gen hx2, hreads', hrd]
    simp [dks]
  · exact DecodeAnon.instOnly_append hR1.1 fun d' hd'' =>
      (List.mem_cons.1 hd'').elim (fun e => ⟨_, e⟩) (hinst d')

/-! ## Instance and component types -/

/-- **An instance type of the fragment**, in a nested scope. -/
theorem inst_typeR {N : NomTable} {Γ : Ctx} {fs : Externs} {σ : Scope} {δ : DScope}
    (ih : ListSimR N [] fs) (hm : MR N Γ σ δ) :
    ∃ (D : List ComponentDecl) (δi : DScope), (nested false (exportDecls fs)).run σ = .ok (D, σ) ∧
      (decDefType (.instance (instDecls D))).run δ =
        .ok (.inst (dks (rdEs [] fs)), { δ with nom := δi.nom }) ∧
      ∀ p ∈ δi.nom, N.lookup p.1 = some p.2 := by
  obtain ⟨σi, E, δi, hr, hd, hmi, hreads, hinst⟩ := (ih _ _ (mr_nested hm false)).2
  have hE : E = (instDecls E).map .inst := instOnly_eq hinst
  have hdecls : σi.decls = E := by simpa using hd
  have h1 := hreads [] [] []
  rw [List.append_nil, hE, cdecls_inst] at h1
  refine ⟨E, δi, by simp [nested, hr, hdecls], ?_, hmi.m.dnom⟩
  cases hD : (decIDecls (instDecls E) []).run { outer := δ.types :: δ.outer, nom := δ.nom } with
  | error e => simp [hD, decCDecls] at h1
  | ok p =>
    have e : p.1 = dks (rdEs [] fs) ∧ p.2 = δi := by simpa [hD, decCDecls] using h1
    simp [decDefType, inNested, hD, e.1, e.2]

/-- **A component type of the fragment**, in a nested scope. -/
theorem comp_typeR {N : NomTable} {Γ : Ctx} {is fs : Externs} {σ : Scope} {δ : DScope}
    (h1 : ListSimR N [] is) (h2 : ListSimR N (extendR [] is) fs) (hm : MR N Γ σ δ) :
    ∃ (C : List ComponentDecl) (δi : DScope),
      (nested true (do importDecls is; exportDecls fs)).run σ = .ok (C, σ) ∧
      (decDefType (.component C)).run δ =
        .ok (.comp (dks (rdEs [] is)) (dks (rdEs (extendR [] is) fs)), { δ with nom := δi.nom }) ∧
      ∀ p ∈ δi.nom, N.lookup p.1 = some p.2 := by
  obtain ⟨σa, Ea, δa, hra, hda, hma, hreadsa⟩ := (h1 _ _ (mr_nested hm true)).1
  obtain ⟨σb, Eb, δb, hrb, hdb, hmb, hreadsb, -⟩ := (h2 _ _ hma).2
  have hdecls : σb.decls = Ea ++ Eb := by rw [hdb, hda]; simp
  have hb : (decCDecls (Eb ++ []) ([] ++ dks (rdEs [] is)) []).run δa =
      (decCDecls [] ([] ++ dks (rdEs [] is)) ([] ++ dks (rdEs (extendR [] is) fs))).run δb :=
    hreadsb [] _ []
  have hdec : (decCDecls (Ea ++ Eb) [] []).run { outer := δ.types :: δ.outer, nom := δ.nom } =
      .ok ((dks (rdEs [] is), dks (rdEs (extendR [] is) fs)), δb) := by
    rw [hreadsa, ← List.append_nil Eb, hb]
    simp [decCDecls]
  refine ⟨Ea ++ Eb, δb, by simp [nested, hra, hrb, hdecls], ?_, hmb.m.dnom⟩
  simp [decDefType, inNested, hdec]

theorem cacheK_simR {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {k : Kind} {j : Nat}
    (hm : MR N Γ σ δ) (hj : δ.types[j]? = some (infoK (rdKd [] k))) :
    VSR N Γ (do
      modify fun sc : Scope => { sc with kcache := sc.kcache ++ [(k, j)] }
      pure j) σ δ (fun j' δ' => δ'.types[j']? = some (infoK (rdKd [] k))) := by
  have hkc : ∀ k' j', (k', j') ∈ (cm Γ { σ with kcache := σ.kcache ++ [(k, j)] }).kcache →
      δ.types[j']? = some (infoK k') := by
    intro k' j' h
    have h' : (k', j') ∈ (cm Γ σ).kcache ∨ (k', j') = (rdKd [] k, j) := by
      simpa [cm, List.mem_append, List.mem_map] using h
    rcases h' with h' | h'
    · exact hm.m.kc k' j' h'
    · rw [(Prod.mk.inj h').1, (Prod.mk.inj h').2]; exact hj
  have hm' : MR N Γ { σ with kcache := σ.kcache ++ [(k, j)] } δ :=
    ⟨⟨hm.m.size, hm.m.nom, hm.m.dnom, hm.m.fc, hm.m.vc, hm.m.hc, hkc, hm.m.res, hm.m.names⟩, hm.fok⟩
  exact ⟨j, _, [], δ, by simp, by simp, hm', rfl, ext_refl δ, reads_nil δ, hj⟩

/-- **A shared instance or component type**: cached (under the kind as written), or
defined by `m`. -/
theorem shared_simR {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {k : Kind} {m : TM Nat}
    (hm : MR N Γ σ δ) (h : VSR N Γ m σ δ (fun j δ' => δ'.types[j]? = some (infoK (rdKd [] k)))) :
    VSR N Γ (shared k m) σ δ (fun j δ' => δ'.types[j]? = some (infoK (rdKd [] k))) := by
  by_cases hit : σ.share = true ∧ ∃ j, σ.kcache.lookup k = some j
  · obtain ⟨hsh, j, hl⟩ := hit
    have hmem : (rdKd [] k, j) ∈ (cm Γ σ).kcache :=
      List.mem_map_of_mem (f := fun p => (rdKd [] p.1, p.2)) (mem_of_lookupK hl)
    exact vsr_of_run (by simp [shared, hsh, hl]) hm (hm.m.kc _ j hmem)
  · exact vsr_congr (shared_miss hit) (vsr_bind h fun j σ1 δ1 hm1 _ hj => cacheK_simR hm1 hj)

theorem defTy_simR {N : NomTable} {Γ : Ctx} {σ : Scope} {δ δ0 : DScope} {D : DefType} {x : TInfo}
    (hm : MR N Γ σ δ) (hx : ¬ DecodeNamed.IsRes (some x)) (hd : (decDefType D).run δ = .ok (x, δ0))
    (ht : δ0.types = δ.types) (hn : ∀ p ∈ δ0.nom, N.lookup p.1 = some p.2) :
    VSR N Γ (defTy D) σ δ (fun j δ' => δ'.types[j]? = some x) :=
  vsr_of_vs (indep_defTy D) hm (DecodeNamed.defTy_sim hm.m hx hd ht hn)

theorem instTy_simR {N : NomTable} {Γ : Ctx} {fs : Externs} {σ : Scope} {δ : DScope}
    (ih : ListSimR N [] fs) (hm : MR N Γ σ δ) :
    VSR N Γ (do let ds ← nested false (exportDecls fs); defTy (.instance (instDecls ds))) σ δ
      (fun j δ' => δ'.types[j]? = some (.inst (dks (rdEs [] fs)))) := by
  obtain ⟨D, δi, hr, hd, hn⟩ := inst_typeR ih hm
  refine vsr_bind (vsr_of_run (Q := fun ds δ' => ds = D ∧ δ' = δ) hr hm ⟨rfl, rfl⟩) ?_
  rintro ds σ1 δ1 hm1 - ⟨rfl, rfl⟩
  exact defTy_simR hm1 id hd rfl hn

theorem compTy_simR {N : NomTable} {Γ : Ctx} {is fs : Externs} {σ : Scope} {δ : DScope}
    (h1 : ListSimR N [] is) (h2 : ListSimR N (extendR [] is) fs) (hm : MR N Γ σ δ) :
    VSR N Γ (do let ds ← nested true (do importDecls is; exportDecls fs); defTy (.component ds)) σ δ
      (fun j δ' => δ'.types[j]? = some (.comp (dks (rdEs [] is)) (dks (rdEs (extendR [] is) fs)))) := by
  obtain ⟨C, δi, hr, hd, hn⟩ := comp_typeR h1 h2 hm
  refine vsr_bind (vsr_of_run (Q := fun ds δ' => ds = C ∧ δ' = δ) hr hm ⟨rfl, rfl⟩) ?_
  rintro ds σ1 δ1 hm1 - ⟨rfl, rfl⟩
  exact defTy_simR hm1 id hd rfl hn

/-! ## Items that are not type items -/

theorem item_funcR {N : NomTable} {Γ : Ctx} {n : String} {s : Sig} (hs : SigOkR Γ s) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ Γ n (.func s) σ δ := fun σ δ hm => by
  unfold ItemSimR; rw [externDesc]
  exact vsr_bind (funcTy_simR hs hm) fun j σ1 δ1 hm1 _ hj => vsr_pure hm1 fun σ2 hm2 =>
    ⟨δ1, by simp [decExtern, typeAt_run hj, dk, rdKd], hm2⟩

theorem item_valueR {N : NomTable} {Γ : Ctx} {n : String} {t : Silmaril.Wasm.Wit.Binary.Ty} (ht : TyOkR Γ t) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ Γ n (.value t) σ δ := fun σ δ hm => by
  unfold ItemSimR; rw [externDesc]
  exact vsr_bind (valTy_simR ht hm) fun v σ1 δ1 hm1 _ hv => vsr_pure hm1 fun σ2 hm2 =>
    ⟨δ1, by simp [decExtern, hv δ1 (ext_refl δ1), dk, rdKd], hm2⟩

theorem item_instR {N : NomTable} {Γ : Ctx} {n : String} {i : Option String} {fs : Externs}
    (ih : ListSimR N [] fs) : ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ Γ n (.inst i fs) σ δ := fun σ δ hm => by
  unfold ItemSimR; rw [externDesc]
  exact vsr_bind (shared_simR (k := .inst i fs) hm (instTy_simR ih hm)) fun j σ1 δ1 hm1 _ hj =>
    vsr_pure hm1 fun σ2 hm2 => ⟨{ δ1 with insts := δ1.insts.push (dks (rdEs [] fs)) },
      by simp [decExtern, typeAt_run hj, dk, infoK, rdKd], hm2.retype rfl hm2.m.dnom⟩

theorem item_compR {N : NomTable} {Γ : Ctx} {n : String} {i : Option String} {is fs : Externs}
    (h1 : ListSimR N [] is) (h2 : ListSimR N (extendR [] is) fs) :
    ∀ σ δ, MR N Γ σ δ → ItemSimR N Γ Γ n (.comp i is fs) σ δ := fun σ δ hm => by
  unfold ItemSimR; rw [externDesc]
  exact vsr_bind (shared_simR (k := .comp i is fs) hm (compTy_simR h1 h2 hm)) fun j σ1 δ1 hm1 _ hj =>
    vsr_pure hm1 fun σ2 hm2 => ⟨δ1, by simp [decExtern, typeAt_run hj, dk, infoK, rdKd], hm2⟩

end DecodeRefVal

end Silmaril.Wasm.Wac.Bridge
