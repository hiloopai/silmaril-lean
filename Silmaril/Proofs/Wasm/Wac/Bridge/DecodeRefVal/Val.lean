module

public import Silmaril.Wasm.Wac.Bridge.DecodeRefVal.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Thms

/-!
# WAC bridge: `ref` of a resource as a value type, the value level

`DecodeNamed.M` relates every cached function type `s` of the encoder (`fcache`) to the
decoder's type `.func s` at its index, and every cached instance or component kind `k`
(`kcache`) to `infoK k`. In the fragment `EsOkR` the decoder reads them back as
`rdS Γ s` and `infoK (rdKd [] k)`, while the caches stay keyed by the types as written.
The invariant here, `MR N Γ σ δ`, is `M` **up to the read-back**: `M` of the scope
`cm Γ σ`, whose caches are the encoder's with `rdS Γ` and `rdKd []` applied to the keys,
and the cached function types are in the fragment (so that `rdS` does not change when
the context grows, `cm_app`).

Every encoder computation that neither reads nor writes the two caches (`Indep`: value
types, parameters, nominal definitions, type definitions, nested scopes) runs alike on
`σ` and on `cm Γ σ`, so the `DecodeNamed.VS` simulations of `DecodeNamed` apply to it
(`vsr_of_vs`). Value types are simulated at that level (`valTy_simR0`, over `TyOkR`,
reading back `rdT Γ t`). Function types read the cache and are simulated against `MR`
directly (`funcTy_simR`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef)
open DecodeEnc (typeAt_run ok_bind pure_ok)
open DecodeAnon (Ext ext_refl ext_trans push_keep ext_push push_self DecVal DecOpt DecVals DecPs
  DecDef decVal_prim decVal_idx decOpt_none decOpt_some decVals_nil decVals_cons decPs_nil
  decPs_cons decDef_list decDef_fixedList decDef_map decDef_option decDef_result decDef_tuple
  decDef_future decDef_stream Reads reads_nil instOnly_single decFunc_run funcMiss funcTy_miss)
open DecodeNamed (Ctx NS M VS vs_pure vs_bind vs_congr handle_sim defVal_sim decDef_own_res
  decDef_own_alias decDef_borrow_res decDef_borrow_alias valTy_ref_run valTy_own_run
  valTy_borrow_run not_res TyOk)

namespace DecodeRefVal

attribute [local simp] ok_bind pure_ok

/-! ## Contexts grow at the end -/

theorem lookup_app {a : String} {x : NS} : ∀ {Γ : Ctx} (Δ : Ctx), Γ.lookup a = some x →
    (Γ ++ Δ).lookup a = some x
  | [], _, h => absurd h (by simp)
  | (b, y) :: Γ, Δ, h => by
    by_cases e : a = b
    · have hb : (a == b) = true := beq_iff_eq.2 e
      have hy : y = x := by simpa [List.lookup, hb] using h
      simp [List.lookup, hb, hy]
    · have hb : (a == b) = false := beq_false_of_ne e
      have h' : Γ.lookup a = some x := by simpa [List.lookup, hb] using h
      simpa [List.lookup, hb] using lookup_app Δ h'

theorem rdTo_congr {Γ Γ' : Ctx} {a : Option Silmaril.Wasm.Wit.Binary.Ty} (h : ∀ t ∈ a, rdT Γ' t = rdT Γ t) :
    rdTo Γ' a = rdTo Γ a := by
  cases a with
  | none => rfl
  | some t => simp [rdTo, h t rfl]

theorem rdTs_congr {Γ Γ' : Ctx} : ∀ {ts : List Silmaril.Wasm.Wit.Binary.Ty}, (∀ t ∈ ts, rdT Γ' t = rdT Γ t) →
    rdTs Γ' ts = rdTs Γ ts
  | [], _ => rfl
  | t :: ts, h => by
    simp [rdTs, h t List.mem_cons_self, rdTs_congr (fun t' ht => h t' (List.mem_cons_of_mem _ ht))]

/-- **What a value type of the fragment reads back as does not change** when the
context grows. -/
theorem rdT_app {Γ : Ctx} (Δ : Ctx) {t : Silmaril.Wasm.Wit.Binary.Ty} (h : TyOkR Γ t) : rdT (Γ ++ Δ) t = rdT Γ t := by
  induction h with
  | prim p => rfl
  | refVal h | refAlias h | refRes h | own h | ownAlias h => simp [rdT, h, lookup_app Δ h]
  | borrowRes _ | borrowAlias _ => rfl
  | list _ ih | option _ ih | fixedList _ _ ih => simp [rdT, ih]
  | map _ _ ihk ihv => simp [rdT, ihk, ihv]
  | result _ _ iha ihb => simp [rdT, rdTo_congr iha, rdTo_congr ihb]
  | tuple _ ih => simp [rdT, rdTs_congr ih]
  | future _ ih | stream _ ih => simp [rdT, rdTo_congr ih]

theorem tyOkR_app {Γ : Ctx} (Δ : Ctx) {t : Silmaril.Wasm.Wit.Binary.Ty} (h : TyOkR Γ t) : TyOkR (Γ ++ Δ) t := by
  induction h with
  | prim p => exact .prim p
  | refVal h => exact .refVal (lookup_app Δ h)
  | refAlias h => exact .refAlias (lookup_app Δ h)
  | refRes h => exact .refRes (lookup_app Δ h)
  | own h => exact .own (lookup_app Δ h)
  | ownAlias h => exact .ownAlias (lookup_app Δ h)
  | borrowRes h => exact .borrowRes (lookup_app Δ h)
  | borrowAlias h => exact .borrowAlias (lookup_app Δ h)
  | list _ ih => exact .list ih
  | fixedList n _ ih => exact .fixedList n ih
  | map _ _ ihk ihv => exact .map ihk ihv
  | option _ ih => exact .option ih
  | result _ _ iha ihb => exact .result iha ihb
  | tuple _ ih => exact .tuple ih
  | future _ ih => exact .future ih
  | stream _ ih => exact .stream ih

theorem rdPs_congr {Γ Γ' : Ctx} : ∀ {ps : List (String × Silmaril.Wasm.Wit.Binary.Ty)}, (∀ p ∈ ps, rdT Γ' p.2 = rdT Γ p.2) →
    rdPs Γ' ps = rdPs Γ ps
  | [], _ => rfl
  | (n, t) :: ps, h => by
    simp [rdPs, h (n, t) List.mem_cons_self, rdPs_congr (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem rdS_app {Γ : Ctx} (Δ : Ctx) {s : Sig} (h : SigOkR Γ s) : rdS (Γ ++ Δ) s = rdS Γ s := by
  simp [rdS, rdPs_congr (fun p hp => rdT_app Δ (h.1 p hp)), rdTo_congr (fun t ht => rdT_app Δ (h.2 t ht))]

theorem sigOkR_app {Γ : Ctx} (Δ : Ctx) {s : Sig} (h : SigOkR Γ s) : SigOkR (Γ ++ Δ) s :=
  ⟨fun p hp => tyOkR_app Δ (h.1 p hp), fun t ht => tyOkR_app Δ (h.2 t ht)⟩

/-! ## The invariant up to the read-back -/

/-- The encoder's scope with the read-back applied to the keys of its caches. -/
def cm (Γ : Ctx) (σ : Scope) : Scope :=
  { σ with fcache := σ.fcache.map (fun p => (rdS Γ p.1, p.2)),
           kcache := σ.kcache.map (fun p => (rdKd [] p.1, p.2)) }

/-- **The invariant**: `DecodeNamed.M` up to the read-back, with the cached function types
in the fragment. -/
structure MR (N : NomTable) (Γ : Ctx) (σ : Scope) (δ : DScope) : Prop where
  m : M N Γ (cm Γ σ) δ
  fok : ∀ s j, (s, j) ∈ σ.fcache → SigOkR Γ s

theorem cm_app {Γ : Ctx} (Δ : Ctx) {σ : Scope} (h : ∀ s j, (s, j) ∈ σ.fcache → SigOkR Γ s) :
    cm (Γ ++ Δ) σ = cm Γ σ := by
  have e : σ.fcache.map (fun p => (rdS (Γ ++ Δ) p.1, p.2)) = σ.fcache.map (fun p => (rdS Γ p.1, p.2)) :=
    List.map_congr_left fun p hp => by rw [rdS_app Δ (h p.1 p.2 hp)]
  simp only [cm, e]

/-! ## Computations that do not touch the two caches -/

/-- `m` neither reads nor writes `fcache` and `kcache`. -/
def Indep {α : Type} (m : TM α) : Prop :=
  ∀ (σ : Scope) (fc : List (Sig × Nat)) (kc : List (Kind × Nat)),
    m.run { σ with fcache := fc, kcache := kc } =
      (m.run σ).map fun p => (p.1, { p.2 with fcache := fc, kcache := kc })

theorem indep_pure {α : Type} (a : α) : Indep (pure a : TM α) := fun _ _ _ => rfl

theorem indep_throw {α : Type} (e : String) : Indep (throw e : TM α) := fun _ _ _ => rfl

theorem indep_bind {α β : Type} {m : TM α} {f : α → TM β} (hm : Indep m) (hf : ∀ a, Indep (f a)) :
    Indep (m >>= f) := by
  intro σ fc kc
  simp only [StateT.run_bind, hm σ fc kc]
  cases m.run σ with
  | error e => rfl
  | ok p => exact hf p.1 p.2 fc kc

theorem indep_get {α : Type} {f : Scope → TM α}
    (hf : ∀ σ fc kc, f { σ with fcache := fc, kcache := kc } = f σ) (hi : ∀ σ, Indep (f σ)) :
    Indep (get >>= f) := by
  intro σ fc kc
  show (f _).run _ = ((f σ).run σ).map _
  rw [hf]
  exact hi σ σ fc kc

theorem indep_defTy (d : DefType) : Indep (defTy d) := fun _ _ _ => rfl

theorem indep_namedTy (n : String) : Indep (namedTy n) := by
  unfold namedTy
  refine indep_get (fun _ _ _ => rfl) fun σ => ?_
  split
  · exact indep_pure _
  · exact indep_throw _

theorem indep_defVal (d : DefValType) : Indep (defVal d) := by
  unfold defVal
  refine indep_get (fun _ _ _ => rfl) fun σ => ?_
  split
  · exact indep_pure _
  · exact indep_bind (indep_defTy _) fun j => indep_bind (fun _ _ _ => rfl) fun _ => indep_pure _

theorem indep_handle (o : Bool) (i : Nat) : Indep (handle o i) := by
  unfold handle
  refine indep_get (fun _ _ _ => rfl) fun σ => ?_
  split
  · exact indep_pure _
  · exact indep_bind (indep_defTy _) fun j => indep_bind (fun _ _ _ => rfl) fun _ => indep_pure _

theorem indep_ref (r : TyRef) : Indep (valTy (.ref r)) := by
  rw [valTy]
  refine indep_bind (indep_namedTy _) fun i => indep_get (fun _ _ _ => rfl) fun σ => ?_
  split
  · exact indep_handle _ _
  · exact indep_pure _

theorem indep_valTyOpt {a : Option Silmaril.Wasm.Wit.Binary.Ty} (ih : ∀ t ∈ a, Indep (valTy t)) : Indep (valTyOpt a) := by
  cases a with
  | none => exact indep_pure _
  | some t => exact indep_bind (ih t rfl) fun _ => indep_pure _

theorem indep_valTys : ∀ {ts : List Silmaril.Wasm.Wit.Binary.Ty}, (∀ t ∈ ts, Indep (valTy t)) → Indep (valTys ts)
  | [], _ => indep_pure _
  | t :: _, ih => indep_bind (ih t List.mem_cons_self) fun _ =>
      indep_bind (indep_valTys fun t' h => ih t' (List.mem_cons_of_mem _ h)) fun _ => indep_pure _

/-- **Value types do not touch the two caches.** -/
theorem indep_valTy {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : TyOkR Γ t) : Indep (valTy t) := by
  induction h with
  | prim p => exact indep_pure _
  | refVal _ | refAlias _ | refRes _ => exact indep_ref _
  | own _ | ownAlias _ => exact indep_bind (indep_namedTy _) fun i => indep_handle _ _
  | borrowRes _ | borrowAlias _ => exact indep_bind (indep_namedTy _) fun i => indep_handle _ _
  | list _ ih | option _ ih | fixedList _ _ ih => exact indep_bind ih fun _ => indep_defVal _
  | map _ _ ihk ihv => exact indep_bind ihk fun _ => indep_bind ihv fun _ => indep_defVal _
  | result _ _ iha ihb =>
    exact indep_bind (indep_valTyOpt iha) fun _ => indep_bind (indep_valTyOpt ihb) fun _ => indep_defVal _
  | tuple _ ih => exact indep_bind (indep_valTys ih) fun _ => indep_defVal _
  | future _ ih | stream _ ih => exact indep_bind (indep_valTyOpt ih) fun _ => indep_defVal _

theorem indep_paramTys {Γ : Ctx} : ∀ {ps : List (String × Silmaril.Wasm.Wit.Binary.Ty)}, (∀ p ∈ ps, TyOkR Γ p.2) →
    Indep (paramTys ps)
  | [], _ => indep_pure _
  | (n, t) :: _, h => indep_bind (indep_valTy (h (n, t) List.mem_cons_self)) fun _ =>
      indep_bind (indep_paramTys fun p hp => h p (List.mem_cons_of_mem _ hp)) fun _ => indep_pure _

/-- An `Indep` computation runs on `cm Γ σ` as on `σ`. -/
theorem indep_run {α : Type} {m : TM α} (hi : Indep m) (Γ : Ctx) {σ σ0 : Scope} {a : α}
    (hr : m.run σ = .ok (a, σ0)) :
    σ0.fcache = σ.fcache ∧ σ0.kcache = σ.kcache ∧ m.run (cm Γ σ) = .ok (a, cm Γ σ0) := by
  have h1 : (Except.ok (a, σ0) : Except String (α × Scope)) =
      Except.ok (a, { σ0 with fcache := σ.fcache, kcache := σ.kcache }) := by
    have e : m.run σ = (m.run σ).map fun p => (p.1, { p.2 with fcache := σ.fcache, kcache := σ.kcache }) :=
      hi σ σ.fcache σ.kcache
    rw [hr] at e
    exact e
  have h2 : σ0 = { σ0 with fcache := σ.fcache, kcache := σ.kcache } := (Prod.mk.inj (Except.ok.inj h1)).2
  have hf : σ0.fcache = σ.fcache := by rw [h2]
  have hk : σ0.kcache = σ.kcache := by rw [h2]
  refine ⟨hf, hk, ?_⟩
  have e : m.run (cm Γ σ) = (m.run σ).map fun p => (p.1, { p.2 with
      fcache := σ.fcache.map (fun p => (rdS Γ p.1, p.2)), kcache := σ.kcache.map (fun p => (rdKd [] p.1, p.2)) }) :=
    hi σ _ _
  rw [e, hr]
  simp only [cm, hf, hk, Except.map]

/-! ## Encoder steps against `MR` -/

/-- An encoder step against `MR` (as `DecodeNamed.VS` against `M`). -/
def VSR {α : Type} (N : NomTable) (Γ : Ctx) (m : TM α) (σ : Scope) (δ : DScope)
    (Q : α → DScope → Prop) : Prop :=
  ∃ a σ' E δ', m.run σ = .ok (a, σ') ∧ σ'.decls = σ.decls ++ E ∧ MR N Γ σ' δ' ∧
    σ'.share = σ.share ∧ Ext δ δ' ∧ Reads E δ δ' ∧ Q a δ'

theorem vsr_pure {N : NomTable} {Γ : Ctx} {α : Type} {a : α} {σ : Scope} {δ : DScope}
    {Q : α → DScope → Prop} (hm : MR N Γ σ δ) (hq : Q a δ) : VSR N Γ (pure a) σ δ Q :=
  ⟨a, σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, ext_refl δ, reads_nil δ, hq⟩

theorem vsr_of_run {N : NomTable} {Γ : Ctx} {α : Type} {m : TM α} {σ : Scope} {δ : DScope} {a : α}
    {Q : α → DScope → Prop} (hr : m.run σ = .ok (a, σ)) (hm : MR N Γ σ δ) (hq : Q a δ) :
    VSR N Γ m σ δ Q :=
  ⟨a, σ, [], δ, hr, (List.append_nil _).symm, hm, rfl, ext_refl δ, reads_nil δ, hq⟩

theorem vsr_bind {N : NomTable} {Γ : Ctx} {α β : Type} {m : TM α} {f : α → TM β} {σ : Scope}
    {δ : DScope} {Q : α → DScope → Prop} {R : β → DScope → Prop} (h : VSR N Γ m σ δ Q)
    (k : ∀ a σ' δ', MR N Γ σ' δ' → Ext δ δ' → Q a δ' → VSR N Γ (f a) σ' δ' R) :
    VSR N Γ (m >>= f) σ δ R := by
  obtain ⟨a, σ1, E1, δ1, hr1, hd1, hm1, hs1, he1, hR1, hq1⟩ := h
  obtain ⟨b, σ2, E2, δ2, hr2, hd2, hm2, hs2, he2, hR2, hq2⟩ := k a σ1 δ1 hm1 he1 hq1
  refine ⟨b, σ2, E1 ++ E2, δ2, ?_, ?_, hm2, hs2.trans hs1, ext_trans he1 he2, ?_, hq2⟩
  · simp [StateT.run_bind, hr1, hr2]
  · rw [hd2, hd1, List.append_assoc]
  · refine ⟨DecodeAnon.instOnly_append hR1.1 hR2.1, fun rest is es => ?_⟩
    rw [List.append_assoc, hR1.2, hR2.2]

theorem vsr_congr {N : NomTable} {Γ : Ctx} {α : Type} {m m' : TM α} {σ : Scope} {δ : DScope}
    {Q : α → DScope → Prop} (e : m.run σ = m'.run σ) (h : VSR N Γ m' σ δ Q) : VSR N Γ m σ δ Q := by
  obtain ⟨a, σ', E, δ', hr, rest⟩ := h
  exact ⟨a, σ', E, δ', e.trans hr, rest⟩

theorem vsr_mono {N : NomTable} {Γ : Ctx} {α : Type} {m : TM α} {σ : Scope} {δ : DScope}
    {Q Q' : α → DScope → Prop} (h : VSR N Γ m σ δ Q) (k : ∀ a δ', Q a δ' → Q' a δ') :
    VSR N Γ m σ δ Q' := by
  obtain ⟨a, σ', E, δ', hr, hd, hm, hs, he, hR, hq⟩ := h
  exact ⟨a, σ', E, δ', hr, hd, hm, hs, he, hR, k a δ' hq⟩

/-- **Lifting**: a `DecodeNamed.VS` step of an `Indep` computation from `cm Γ σ` is a
`VSR` step from `σ`. -/
theorem vsr_of_vs {N : NomTable} {Γ : Ctx} {α : Type} {m : TM α} (hi : Indep m) {σ : Scope}
    {δ : DScope} {Q : α → DScope → Prop} (hm : MR N Γ σ δ) (h : VS N Γ m (cm Γ σ) δ Q) :
    VSR N Γ m σ δ Q := by
  obtain ⟨a, σc, E, δ', hr, hd, hm', hs, he, hR, hq⟩ := h
  have hcm : m.run (cm Γ σ) = (m.run σ).map fun p => (p.1, { p.2 with
      fcache := σ.fcache.map (fun p => (rdS Γ p.1, p.2)), kcache := σ.kcache.map (fun p => (rdKd [] p.1, p.2)) }) :=
    hi σ _ _
  cases hr0 : m.run σ with
  | error e =>
    have h1 : m.run (cm Γ σ) = .error e := by rw [hcm, hr0]; rfl
    exact absurd (h1.symm.trans hr) (by intro h; cases h)
  | ok p =>
    show VSR N Γ m σ δ Q
    obtain ⟨b, σ0⟩ := p
    obtain ⟨hf, -, hrc⟩ := indep_run hi Γ hr0
    have e : (b, cm Γ σ0) = (a, σc) := Except.ok.inj (hrc.symm.trans hr)
    have hb : b = a := (Prod.mk.inj e).1
    have hc : cm Γ σ0 = σc := (Prod.mk.inj e).2
    have hmr : MR N Γ σ0 δ' := ⟨hc ▸ hm', fun s j h => hm.fok s j (hf ▸ h)⟩
    have hd0 : σ0.decls = σ.decls ++ E :=
      calc σ0.decls = (cm Γ σ0).decls := rfl
        _ = σc.decls := by rw [hc]
        _ = σ.decls ++ E := hd
    have hs0 : σ0.share = σ.share :=
      calc σ0.share = (cm Γ σ0).share := rfl
        _ = σc.share := by rw [hc]
        _ = σ.share := hs
    exact ⟨b, σ0, E, δ', hr0, hd0, hmr, hs0, he, hR, hb ▸ hq⟩

/-! ## Value types, at the level of `M` -/

/-- What `valTy_simR0` proves of a type: it decodes back as `rdT Γ t`. -/
def ValOkR (N : NomTable) (Γ : Ctx) (t : Silmaril.Wasm.Wit.Binary.Ty) : Prop :=
  ∀ σ δ, M N Γ σ δ → VS N Γ (valTy t) σ δ (fun v δ' => DecVal δ' v (rdT Γ t))

theorem valTyOpt_simR0 {N : NomTable} {Γ : Ctx} {a : Option Silmaril.Wasm.Wit.Binary.Ty} (ih : ∀ t ∈ a, ValOkR N Γ t)
    {σ : Scope} {δ : DScope} (hm : M N Γ σ δ) :
    VS N Γ (valTyOpt a) σ δ (fun v δ' => DecOpt δ' v (rdTo Γ a)) := by
  cases a with
  | none => exact vs_pure hm (decOpt_none δ)
  | some t => exact vs_bind (ih t rfl σ δ hm) fun v σ1 δ1 hm1 _ hv => vs_pure hm1 (decOpt_some hv)

theorem valTys_simR0 {N : NomTable} {Γ : Ctx} : ∀ {ts : List Silmaril.Wasm.Wit.Binary.Ty}, (∀ t ∈ ts, ValOkR N Γ t) →
    ∀ {σ : Scope} {δ : DScope}, M N Γ σ δ →
      VS N Γ (valTys ts) σ δ (fun vs δ' => DecVals δ' vs (rdTs Γ ts))
  | [], _, _, δ, hm => vs_pure hm (decVals_nil δ)
  | t :: _, ih, σ, δ, hm =>
    vs_bind (ih t List.mem_cons_self σ δ hm) fun _ _ _ hm1 _ hv =>
      vs_bind (valTys_simR0 (fun t' h => ih t' (List.mem_cons_of_mem _ h)) hm1) fun _ _ _ hm2 e2 hvs =>
        vs_pure hm2 (decVals_cons (hv.mono e2) hvs)

theorem refRes_simR0 {N : NomTable} {Γ : Ctx} {a : String} (h : Γ.lookup a = some .res) :
    ValOkR N Γ (.ref ⟨.local, a⟩) := fun σ δ hm => by
  obtain ⟨i, hi, hat, hres⟩ := hm.lookup h
  have e : rdT Γ (.ref ⟨.local, a⟩) = .own ⟨.local, a⟩ := by simp [rdT, h]
  rw [e]
  refine vs_congr (valTy_ref_run (r := ⟨.local, a⟩) hi) ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true hres)]
  exact handle_sim hm (decDef_own_res hat)

theorem ownAlias_simR0 {N : NomTable} {Γ : Ctx} {a r : String} (h : Γ.lookup a = some (.ali r)) :
    ValOkR N Γ (.own ⟨.local, a⟩) := fun σ δ hm => by
  obtain ⟨i, hi, hat, -⟩ := hm.lookup h
  have e : rdT Γ (.own ⟨.local, a⟩) = .ref ⟨.local, a⟩ := by simp [rdT, h]
  rw [e]
  exact vs_congr (valTy_own_run (r := ⟨.local, a⟩) hi) (handle_sim hm (decDef_own_alias hat))

/-- A case of `DecodeNamed.valTy_sim` whose type reads back as itself. -/
theorem keep_simR0 {N : NomTable} {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (e : rdT Γ t = t)
    (h : ∀ σ δ, M N Γ σ δ → VS N Γ (valTy t) σ δ (fun v δ' => DecVal δ' v t)) : ValOkR N Γ t := by
  intro σ δ hm
  rw [e]
  exact h σ δ hm

/-- **Every value type of the fragment** is encoded as a value type that decodes back as
`rdT Γ t`. -/
theorem valTy_simR0 {N : NomTable} {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : TyOkR Γ t) : ValOkR N Γ t := by
  induction h with
  | prim p => exact fun σ δ hm => vs_pure hm (decVal_prim δ p)
  | refVal h => exact keep_simR0 (by simp [rdT, h]) (DecodeNamed.refVal_sim h)
  | refAlias h => exact keep_simR0 (by simp [rdT, h]) (DecodeNamed.refAlias_sim h)
  | refRes h => exact refRes_simR0 h
  | own h => exact keep_simR0 (by simp [rdT, h]) (DecodeNamed.own_sim h)
  | ownAlias h => exact ownAlias_simR0 h
  | borrowRes h => exact keep_simR0 rfl (DecodeNamed.borrowRes_sim h)
  | borrowAlias h => exact keep_simR0 rfl (DecodeNamed.borrowAlias_sim h)
  | list _ ih =>
    exact fun σ δ hm => vs_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv => defVal_sim hm1 (decDef_list hv)
  | fixedList n _ ih =>
    exact fun σ δ hm => vs_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv =>
      defVal_sim hm1 (decDef_fixedList n hv)
  | map _ _ ihk ihv =>
    exact fun σ δ hm => vs_bind (ihk σ δ hm) fun k σ1 δ1 hm1 _ hk =>
      vs_bind (ihv σ1 δ1 hm1) fun v σ2 δ2 hm2 e2 hv => defVal_sim hm2 (decDef_map (hk.mono e2) hv)
  | option _ ih =>
    exact fun σ δ hm => vs_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv => defVal_sim hm1 (decDef_option hv)
  | result _ _ iha ihb =>
    exact fun σ δ hm => vs_bind (valTyOpt_simR0 iha hm) fun x σ1 δ1 hm1 _ hx =>
      vs_bind (valTyOpt_simR0 ihb hm1) fun y σ2 δ2 hm2 e2 hy =>
        defVal_sim hm2 (decDef_result (hx.mono e2) hy)
  | tuple _ ih =>
    exact fun σ δ hm => vs_bind (valTys_simR0 ih hm) fun vs σ1 δ1 hm1 _ hvs =>
      defVal_sim hm1 (decDef_tuple hvs)
  | future _ ih =>
    exact fun σ δ hm => vs_bind (valTyOpt_simR0 ih hm) fun x σ1 δ1 hm1 _ hx =>
      defVal_sim hm1 (decDef_future hx)
  | stream _ ih =>
    exact fun σ δ hm => vs_bind (valTyOpt_simR0 ih hm) fun x σ1 δ1 hm1 _ hx =>
      defVal_sim hm1 (decDef_stream hx)

theorem paramTys_simR0 {N : NomTable} {Γ : Ctx} : ∀ {ps : List (String × Silmaril.Wasm.Wit.Binary.Ty)}, (∀ p ∈ ps, TyOkR Γ p.2) →
    ∀ {σ : Scope} {δ : DScope}, M N Γ σ δ →
      VS N Γ (paramTys ps) σ δ (fun vs δ' => DecPs δ' vs (rdPs Γ ps))
  | [], _, _, δ, hm => vs_pure hm (decPs_nil δ)
  | (n, t) :: _, h, σ, δ, hm =>
    vs_bind (valTy_simR0 (h (n, t) List.mem_cons_self) σ δ hm) fun _ _ _ hm1 _ hv =>
      vs_bind (paramTys_simR0 (fun p hp => h p (List.mem_cons_of_mem _ hp)) hm1) fun _ _ _ hm2 e2 hvs =>
        vs_pure hm2 (decPs_cons n (hv.mono e2) hvs)

/-! ## Value types and function types against `MR` -/

theorem valTy_simR {N : NomTable} {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : TyOkR Γ t) {σ : Scope} {δ : DScope}
    (hm : MR N Γ σ δ) : VSR N Γ (valTy t) σ δ (fun v δ' => DecVal δ' v (rdT Γ t)) :=
  vsr_of_vs (indep_valTy h) hm (valTy_simR0 h _ _ hm.m)

theorem defFunc_simR {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {vs : List (String × Silmaril.Wasm.Component.Binary.ValType)}
    {vr : Option Silmaril.Wasm.Component.Binary.ValType} {s : Sig} (hm : MR N Γ σ δ) (hs : SigOkR Γ s)
    (hps : DecPs δ vs (rdS Γ s).params) (hr : DecOpt δ vr (rdS Γ s).result) :
    VSR N Γ (do
        let j ← defTy (.func ⟨vs, vr, s.async⟩)
        modify fun sc => { sc with fcache := sc.fcache ++ [(s, j)] }
        pure j) σ δ (fun j δ' => δ'.types[j]? = some (.func (rdS Γ s))) := by
  let σ' : Scope := { σ with decls := σ.decls ++ [.inst (.type (.func ⟨vs, vr, s.async⟩))]
                             ntypes := σ.ntypes + 1
                             fcache := σ.fcache ++ [(s, σ.ntypes)] }
  have hfc : ∀ s' j, (s', j) ∈ (cm Γ σ').fcache →
      (s', j) ∈ (cm Γ σ).fcache ∨ (j = (cm Γ σ).ntypes ∧ TInfo.func (rdS Γ s) = .func s') := by
    intro s' j hj
    have hj' : (s', j) ∈ (cm Γ σ).fcache ∨ (s', j) = (rdS Γ s, σ.ntypes) := by
      simpa [cm, σ', List.mem_append, List.mem_map] using hj
    rcases hj' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(Prod.mk.inj h).2, by rw [(Prod.mk.inj h).1]⟩
  have hm' : M N Γ (cm Γ σ') { δ with types := δ.types.push (.func (rdS Γ s)) } :=
    hm.m.push (.func (rdS Γ s)) id rfl rfl rfl rfl hfc (fun _ _ h => Or.inl h)
      (fun _ _ _ h => Or.inl h) (fun _ _ h => Or.inl h)
  have hok : ∀ s' j, (s', j) ∈ σ'.fcache → SigOkR Γ s' := by
    intro s' j hj
    rcases List.mem_append.1 hj with h | h
    · exact hm.fok s' j h
    · rw [(Prod.mk.inj (List.mem_singleton.1 h)).1]; exact hs
  have hnew : (δ.types.push (.func (rdS Γ s)))[σ.ntypes]? = some (.func (rdS Γ s)) := by
    rw [← show (cm Γ σ).ntypes = σ.ntypes from rfl, ← hm.m.size]; exact push_self δ _
  refine ⟨σ.ntypes, σ', [.inst (.type (.func ⟨vs, vr, s.async⟩))], _, ?_, rfl, ⟨hm', hok⟩, rfl,
    ext_push δ _, ⟨instOnly_single _, fun rest is es => ?_⟩, hnew⟩
  · simp [defTy]
    rfl
  · simp [decCDecls, decIDecl, decDefType, pushTy, decFunc_run hps hr s.async rfl]

/-- **Every function type of the fragment** is encoded at an index that decodes back as
`rdS Γ s`, shared or defined. -/
theorem funcTy_simR {N : NomTable} {Γ : Ctx} {s : Sig} (hs : SigOkR Γ s) {σ : Scope} {δ : DScope}
    (hm : MR N Γ σ δ) : VSR N Γ (funcTy s) σ δ (fun j δ' => δ'.types[j]? = some (.func (rdS Γ s))) := by
  by_cases hit : σ.share = true ∧ ∃ j, σ.fcache.lookup s = some j
  · obtain ⟨hsh, j, hl⟩ := hit
    have hmem : (rdS Γ s, j) ∈ (cm Γ σ).fcache :=
      List.mem_map_of_mem (f := fun p => (rdS Γ p.1, p.2)) (DecodeEnc.mem_of_lookup hl)
    exact vsr_of_run (by simp [funcTy, hsh, hl]) hm (hm.m.fc _ j hmem)
  · have h : σ.share = false ∨ σ.fcache.lookup s = none := by
      cases hsh : σ.share <;> cases hl : σ.fcache.lookup s <;> simp_all
    refine vsr_congr (funcTy_miss h) ?_
    unfold funcMiss
    exact vsr_bind (vsr_of_vs (indep_paramTys hs.1) hm (paramTys_simR0 hs.1 hm.m)) fun ps σ1 δ1 hm1 _ hps =>
      vsr_bind (vsr_of_vs (indep_valTyOpt fun t ht => indep_valTy (hs.2 t ht)) hm1
        (valTyOpt_simR0 (fun t ht => valTy_simR0 (hs.2 t ht)) hm1.m)) fun r σ2 δ2 hm2 e2 hr =>
        defFunc_simR hm2 hs (hps.mono e2) hr

end DecodeRefVal

end Silmaril.Wasm.Wac.Bridge
