module

public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeNamed.Val
public import Silmaril.Wasm.Wac.Bridge.DecodeIface.Thms

/-!
# WAC bridge: decoding inverts encoding on items of the named fragment

The item level of `Silmaril.Wasm.Wac.Bridge.DecodeNamed.Thms`, over the value level of
`Silmaril.Proofs.Wasm.Wac.Bridge.DecodeNamed.Val`:

* `nominalTy_sim`: a record, variant, enum or flags definition decodes back at its index;
* `ItemSim`: one item's descriptor is encoded, its type definitions are read back, the
  decoder reads the item as `dk n k`, and declaring it extends the context;
* `ListSim`: the import and export declarations of a list of items;
* `esOk_sim`: **every list of items of the fragment** (`EsOk`) satisfies `ListSim`, by
  induction on the fragment, the nested instance and component types included.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef)
open DecodeEnc (typeAt_run ok_bind pure_ok ReadsI ReadsE InstOnly)
open DecodeIface (instDecls_map instOnly_eq cdecls_inst mem_of_lookupK dec_import_gen dec_export_gen)
open DecodeAnon (Ext ext_refl ext_trans push_keep ext_push push_self DecVal DecOpt DecVals DecDef
  decVal_idx decDef_list decDef_fixedList decDef_map decDef_option decDef_result decDef_tuple
  decDef_future decDef_stream Reads reads_nil instOnly_single)

namespace DecodeNamed

attribute [local simp] ok_bind pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind

/-! ## Defining one type -/

/-- **Defining a type** that the decoder reads as `x` (ending in `δ0`, which may differ
from `δ` in its nominal table), with no cache entry. -/
theorem defTy_sim {N : NomTable} {Γ : Ctx} {σ : Scope} {δ δ0 : DScope} {D : DefType} {x : TInfo}
    (hm : M N Γ σ δ) (hx : ¬ IsRes (some x)) (hd : (decDefType D).run δ = .ok (x, δ0))
    (ht : δ0.types = δ.types) (hn : ∀ p ∈ δ0.nom, N.lookup p.1 = some p.2) :
    VS N Γ (defTy D) σ δ (fun j δ' => δ'.types[j]? = some x) := by
  have hm0 : M N Γ σ δ0 := hm.retype ht hn
  let σ' : Scope := { σ with decls := σ.decls ++ [.inst (.type D)], ntypes := σ.ntypes + 1 }
  have hm' : M N Γ σ' { δ0 with types := δ0.types.push x } :=
    hm0.push x hx rfl rfl rfl rfl (fun _ _ h => Or.inl h) (fun _ _ h => Or.inl h)
      (fun _ _ _ h => Or.inl h) (fun _ _ h => Or.inl h)
  have he : Ext δ { δ0 with types := δ0.types.push x } := fun i z h => by
    show (δ0.types.push x)[i]? = some z
    rw [ht]; exact push_keep h
  have hnew : (δ0.types.push x)[σ.ntypes]? = some x := by rw [ht, ← hm.size]; exact push_self δ x
  refine ⟨σ.ntypes, σ', [.inst (.type D)], _, by simp [defTy]; rfl, rfl, hm', rfl, he,
    ⟨instOnly_single _, fun rest is es => ?_⟩, hnew⟩
  simp [decCDecls, decIDecl, hd, pushTy]

theorem defTy_val_sim {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {d : DefValType} {t : Ty}
    (hm : M N Γ σ δ) (hd : DecDef δ d t) :
    VS N Γ (defTy (.val d)) σ δ (fun j δ' => δ'.types[j]? = some (.val t)) :=
  defTy_sim hm id (by simp [decDefType, hd δ (ext_refl δ)]) rfl hm.dnom

/-! ## Nominal definitions -/

/-- A decoder computation over a list, pointwise. -/
theorem dmapM {β γ : Type} {h : β → DM γ} {δ : DScope} :
    ∀ {cs : List β} {l : List γ}, Pw (fun c x => (h c).run δ = .ok (x, δ)) cs l →
      (cs.mapM h).run δ = .ok (l, δ)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hc ht => by
    simp [List.mapM_cons, hc, dmapM ht]

/-- An encoder computation over a list, pointwise. -/
theorem mapM_sim {N : NomTable} {Γ : Ctx} {β γ : Type} {g : β → TM γ} {R : DScope → γ → β → Prop}
    (hR : ∀ δ δ' c x, Ext δ δ' → R δ c x → R δ' c x) :
    ∀ {l : List β}, (∀ x ∈ l, ∀ σ δ, M N Γ σ δ → VS N Γ (g x) σ δ (fun c δ' => R δ' c x)) →
      ∀ {σ : Scope} {δ : DScope}, M N Γ σ δ →
        VS N Γ (l.mapM g) σ δ (fun cs δ' => Pw (fun c x => R δ' c x) cs l)
  | [], _, σ, δ, hm => by
    rw [List.mapM_nil]
    exact vs_pure hm .nil
  | x :: l, h, σ, δ, hm => by
    rw [List.mapM_cons]
    exact vs_bind (h x List.mem_cons_self σ δ hm) fun c σ1 δ1 hm1 _ hc =>
      vs_bind (mapM_sim hR (fun y hy => h y (List.mem_cons_of_mem _ hy)) hm1) fun cs σ2 δ2 hm2 e2 hcs =>
        vs_pure hm2 (.cons (hR _ _ _ _ e2 hc) hcs)

/-- **A nominal definition of the fragment** decodes back at the index the encoder
returns. -/
theorem nominalTy_sim {N : NomTable} {Γ : Ctx} {d : Nominal} (hd : NomOk Γ d) {σ : Scope}
    {δ : DScope} (hm : M N Γ σ δ) :
    VS N Γ (nominalTy d) σ δ (fun j δ' => δ'.types[j]? = some (.nominal d)) := by
  cases d with
  | record fs =>
    show VS N Γ (nominalTy (.record fs)) σ δ (fun j δ' => δ'.types[j]? = some (.nominal (.record fs)))
    rw [nominalTy]
    refine vs_bind (mapM_sim
      (R := fun (δ : DScope) (c : String × ValType) (f : String × Ty) => c.1 = f.1 ∧ DecVal δ c.2 f.2)
      (fun _ _ _ _ e h => ⟨h.1, h.2.mono e⟩)
      (fun f hf σ δ hm => vs_bind (valTy_sim (hd f hf) σ δ hm) fun v σ1 δ1 hm1 _ hv =>
        vs_pure hm1 ⟨rfl, hv⟩) hm) fun cs σ1 δ1 hm1 _ hcs => defTy_sim hm1 id ?_ rfl hm1.dnom
    simp only [decDefType, decDefVal, StateT.run_bind]
    rw [dmapM (hcs.imp fun c f h => by simp [h.2 δ1 (ext_refl δ1), h.1])]
    rfl
  | variant cs =>
    show VS N Γ (nominalTy (.variant cs)) σ δ (fun j δ' => δ'.types[j]? = some (.nominal (.variant cs)))
    rw [nominalTy]
    refine vs_bind (mapM_sim (R := fun (δ : DScope) (c : String × Option ValType)
        (f : String × Option Ty) => c.1 = f.1 ∧ DecOpt δ c.2 f.2)
      (fun _ _ _ _ e h => ⟨h.1, h.2.mono e⟩)
      (fun f hf σ δ hm => vs_bind (valTyOpt_sim (fun t ht => valTy_sim (hd f hf t ht)) hm)
        fun v σ1 δ1 hm1 _ hv => vs_pure hm1 ⟨rfl, hv⟩) hm) fun vs σ1 δ1 hm1 _ hvs =>
      defTy_sim hm1 id ?_ rfl hm1.dnom
    simp only [decDefType, decDefVal, StateT.run_bind]
    rw [dmapM (hvs.imp fun c f h => by simp [h.2 δ1 (ext_refl δ1), h.1])]
    rfl
  | enum ls => exact defTy_sim hm id (by simp [decDefType, decDefVal]) rfl hm.dnom
  | flags ls => exact defTy_sim hm id (by simp [decDefType, decDefVal]) rfl hm.dnom

/-! ## Declaring items -/

/-- The scope after `declared n d`. -/
def declF (n : String) (d : ExternDesc) (σ : Scope) : Scope :=
  match d with
  | .type .subResource => declS σ n true
  | .type (.eq i) => declS σ n (decide (i ∈ σ.resIdx))
  | _ => σ

theorem declared_run (n : String) (d : ExternDesc) (σ : Scope) :
    (declared n d).run σ = .ok ((), declF n d σ) := by
  cases d with
  | type b => cases b <;> simp [declared, declF, declS]
  | _ => rfl

theorem declF_decls (n : String) (d : ExternDesc) (σ : Scope) (ds : List ComponentDecl) :
    declF n d { σ with decls := ds } = { declF n d σ with decls := ds } := by
  cases d with
  | type b => cases b <;> rfl
  | _ => rfl

theorem declF_decls' (n : String) (d : ExternDesc) (σ : Scope) : (declF n d σ).decls = σ.decls := by
  cases d with
  | type b => cases b <;> rfl
  | _ => rfl

/-- `M` does not read the declarations. -/
theorem M.withDecls {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} (hm : M N Γ σ δ)
    (ds : List ComponentDecl) : M N Γ { σ with decls := ds } δ :=
  ⟨hm.size, hm.nom, hm.dnom, hm.fc, hm.vc, hm.hc, hm.kc, hm.res, hm.names⟩

/-! ## One item -/

/-- **One item** `n` of kind `k`: its descriptor is encoded as a VS step, and in the end
the decoder reads the item as `dk n k`; declaring it gives `M` in the context `Γ'`. -/
def ItemSim (N : NomTable) (Γ Γ' : Ctx) (n : String) (k : Kind) (σ : Scope) (δ : DScope) : Prop :=
  VS N Γ (externDesc k) σ δ (fun d δ1 => ∀ σ1, M N Γ σ1 δ1 →
    ∃ δ2, (decExtern n d).run δ1 = .ok (dk n k, δ2) ∧ M N Γ' (declF n d σ1) δ2)

/-- **A list of items**: its import and its export declarations. -/
def ListSim (N : NomTable) (Γ : Ctx) (es : Externs) : Prop :=
  ∀ σ δ, M N Γ σ δ →
    (∃ σ' E δ', (importDecls es).run σ = .ok ((), σ') ∧ σ'.decls = σ.decls ++ E ∧
      M N (extend Γ es) σ' δ' ∧ ReadsI (dks es) E δ δ') ∧
    (∃ σ' E δ', (exportDecls es).run σ = .ok ((), σ') ∧ σ'.decls = σ.decls ++ E ∧
      M N (extend Γ es) σ' δ' ∧ ReadsE (dks es) E δ δ' ∧ InstOnly E)

theorem importDecls_run (n : String) (k : Kind) (es : Externs) (σ : Scope) :
    (importDecls ((n, k) :: es)).run σ = ((externDesc k).run σ).bind fun p =>
      (importDecls es).run (declF n p.1 { p.2 with decls := p.2.decls ++ [.import ⟨n, .plain0⟩ p.1] }) := by
  simp only [importDecls, StateT.run_bind]
  cases (externDesc k).run σ with
  | error e => rfl
  | ok p => simp [declared_run]

theorem exportDecls_run (n : String) (k : Kind) (es : Externs) (σ : Scope) :
    (exportDecls ((n, k) :: es)).run σ = ((externDesc k).run σ).bind fun p =>
      (exportDecls es).run
        (declF n p.1 { p.2 with decls := p.2.decls ++ [.inst (.export ⟨n, .plain0⟩ p.1)] }) := by
  simp only [exportDecls, StateT.run_bind]
  cases (externDesc k).run σ with
  | error e => rfl
  | ok p => simp [declared_run]

theorem listSim_nil (N : NomTable) (Γ : Ctx) : ListSim N Γ [] := fun σ δ hm =>
  ⟨⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, fun rest is es => by simp [dks]⟩,
    ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, fun rest is es => by simp [dks],
      fun _ h => absurd h List.not_mem_nil⟩⟩

/-- **Items one by one.** -/
theorem listSim_cons {N : NomTable} {Γ Γ' : Ctx} {n : String} {k : Kind} {es : Externs}
    (hk : ∀ σ δ, M N Γ σ δ → ItemSim N Γ Γ' n k σ δ) (hx : extend Γ ((n, k) :: es) = extend Γ' es)
    (ih : ListSim N Γ' es) : ListSim N Γ ((n, k) :: es) := by
  intro σ δ hm
  obtain ⟨d, σ1, E1, δ1, hr1, hd1, hm1, -, -, hR1, hq⟩ := hk σ δ hm
  obtain ⟨δ2, hx2, hm2⟩ := hq σ1 hm1
  have hmI : M N Γ' (declF n d { σ1 with decls := σ1.decls ++ [.import ⟨n, .plain0⟩ d] }) δ2 := by
    rw [declF_decls]; exact hm2.withDecls _
  have hmE : M N Γ' (declF n d { σ1 with decls := σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ d)] }) δ2 := by
    rw [declF_decls]; exact hm2.withDecls _
  obtain ⟨σ', E, δ', hr, hd, hm', hreads⟩ := (ih _ δ2 hmI).1
  obtain ⟨σ'', F, δ'', hr', hd', hm'', hreads', hinst⟩ := (ih _ δ2 hmE).2
  refine ⟨⟨σ', E1 ++ .import ⟨n, .plain0⟩ d :: E, δ', ?_, ?_, hx ▸ hm', ?_⟩,
    ⟨σ'', E1 ++ .inst (.export ⟨n, .plain0⟩ d) :: F, δ'', ?_, ?_, hx ▸ hm'', ?_, ?_⟩⟩
  · rw [importDecls_run, hr1]; exact hr
  · rw [hd, declF_decls', hd1]; simp
  · intro rest is es'
    rw [List.append_assoc, hR1.2, List.cons_append, dec_import_gen hx2, hreads]
    simp [dks]
  · rw [exportDecls_run, hr1]; exact hr'
  · rw [hd', declF_decls', hd1]; simp
  · intro rest is es'
    rw [List.append_assoc, hR1.2, List.cons_append, dec_export_gen hx2, hreads']
    simp [dks]
  · exact DecodeAnon.instOnly_append hR1.1 fun d' hd'' =>
      (List.mem_cons.1 hd'').elim (fun e => ⟨_, e⟩) (hinst d')

end DecodeNamed

end Silmaril.Wasm.Wac.Bridge
