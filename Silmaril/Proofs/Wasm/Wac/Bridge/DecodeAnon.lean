module

public import Silmaril.Wasm.Wac.Bridge.DecodeEnc.Thms

/-!
# WAC bridge: decoding inverts encoding on functions over anonymous value types

The simulation of `Silmaril.Wasm.Wac.Bridge.DecodeEnc`, extended from primitive value
types to anonymous value types (`Anon`: `list`, fixed-size `list`, `map`, `option`,
`result`, `tuple`, `future`, `stream`, over primitives). The encoder defines each
anonymous type once per scope (`defVal`, the cache `vcache`); the decoder reads the
definitions back as `TInfo.val`.

* `DecVal δ v t`: the encoded value type `v` decodes to `t` in every extension of the
  decoder's scope `δ` (the decoder only pushes types, `Ext`);
* `MatchA σ δ`: the encoder's scope `σ` and the decoder's `δ` have as many types, every
  cached function type is decoded at its index, and every cached anonymous type `d` at
  index `j` is decoded at `j` to the type `d` decodes to (`DecDef`);
* `VSim m σ δ Q`: running the encoder step `m` from `σ` succeeds, emits declarations the
  decoder reads as type pushes only, keeps `MatchA`, and ends with `Q`;
* `valTy_sim`, `funcTy_sim`: every anonymous value type and every function type over
  them is encoded at an index (or as a primitive) that decodes back to it, shared or not;
* `imports_sim`, `exports_sim`: the import and export declarations.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)
open DecodeEnc (typeAt_run ok_bind pure_ok ReadsI ReadsE importDecls_cons exportDecls_cons
  dec_import dec_export)

namespace DecodeAnon

attribute [local simp] ok_bind pure_ok

/-! ## The fragment -/

/-- **Anonymous value types**: built from primitives by the anonymous type constructors
(no named types, handles, records, variants, enums or flags). -/
inductive Anon : Ty → Prop
  | prim (p : PrimValType) : Anon (.prim p)
  | list {t : Ty} : Anon t → Anon (.list t)
  | fixedList {t : Ty} (n : Nat) : Anon t → Anon (.fixedList t n)
  | map {k v : Ty} : Anon k → Anon v → Anon (.map k v)
  | option {t : Ty} : Anon t → Anon (.option t)
  | result {a b : Option Ty} : (∀ t ∈ a, Anon t) → (∀ t ∈ b, Anon t) → Anon (.result a b)
  | tuple {ts : List Ty} : (∀ t ∈ ts, Anon t) → Anon (.tuple ts)
  | future {a : Option Ty} : (∀ t ∈ a, Anon t) → Anon (.future a)
  | stream {a : Option Ty} : (∀ t ∈ a, Anon t) → Anon (.stream a)

/-- A function type over anonymous value types. -/
def AnonSig (s : Sig) : Prop := (∀ p ∈ s.params, Anon p.2) ∧ ∀ t ∈ s.result, Anon t

/-- Named functions over anonymous value types. -/
def AnonFns (es : Externs) : Prop := ∀ p ∈ es, ∃ s, p.2 = .func s ∧ AnonSig s

/-! ## Decoder scopes and what encoded types decode to -/

/-- `δ'` extends the type index space of `δ`. -/
def Ext (δ δ' : DScope) : Prop := ∀ (i : Nat) (x : TInfo), δ.types[i]? = some x → δ'.types[i]? = some x

theorem ext_refl (δ : DScope) : Ext δ δ := fun _ _ h => h

theorem ext_trans {δ₁ δ₂ δ₃ : DScope} (h₁ : Ext δ₁ δ₂) (h₂ : Ext δ₂ δ₃) : Ext δ₁ δ₃ :=
  fun i x h => h₂ i x (h₁ i x h)

theorem push_keep {δ : DScope} {t : TInfo} {j : Nat} {x : TInfo} (h : δ.types[j]? = some x) :
    (δ.types.push t)[j]? = some x := by
  have hlt : j < δ.types.size := (Array.getElem?_eq_some_iff.1 h).1
  simpa [Array.getElem?_push, Nat.ne_of_lt hlt] using h

theorem ext_push (δ : DScope) (t : TInfo) : Ext δ { δ with types := δ.types.push t } :=
  fun _ _ h => push_keep h

theorem push_self (δ : DScope) (t : TInfo) : (δ.types.push t)[δ.types.size]? = some t := by
  simp

/-- The encoded value type `v` decodes to `t` in every extension of `δ`. -/
def DecVal (δ : DScope) (v : ValType) (t : Ty) : Prop :=
  ∀ δ', Ext δ δ' → (decVal v).run δ' = .ok (t, δ')

def DecOpt (δ : DScope) (v : Option ValType) (t : Option Ty) : Prop :=
  ∀ δ', Ext δ δ' → (decValOpt v).run δ' = .ok (t, δ')

def DecVals (δ : DScope) (vs : List ValType) (ts : List Ty) : Prop :=
  ∀ δ', Ext δ δ' → (vs.mapM decVal).run δ' = .ok (ts, δ')

/-- The decoding of named parameters, as `decFunc` reads them. -/
def decParam (p : String × ValType) : DM (String × Ty) := do
  let x ← decVal p.2
  pure (p.1, x)

def DecPs (δ : DScope) (vs : List (String × ValType)) (ps : List (String × Ty)) : Prop :=
  ∀ δ', Ext δ δ' → (vs.mapM decParam).run δ' = .ok (ps, δ')

/-- The anonymous type definition `d` decodes to the value type `t`. -/
def DecDef (δ : DScope) (d : DefValType) (t : Ty) : Prop :=
  ∀ δ', Ext δ δ' → (decDefVal d).run δ' = .ok (.val t, δ')

theorem DecVal.mono {δ δ' : DScope} {v : ValType} {t : Ty} (h : DecVal δ v t) (e : Ext δ δ') :
    DecVal δ' v t := fun δ'' e' => h δ'' (ext_trans e e')

theorem DecOpt.mono {δ δ' : DScope} {v : Option ValType} {t : Option Ty} (h : DecOpt δ v t)
    (e : Ext δ δ') : DecOpt δ' v t := fun δ'' e' => h δ'' (ext_trans e e')

theorem DecVals.mono {δ δ' : DScope} {vs : List ValType} {ts : List Ty} (h : DecVals δ vs ts)
    (e : Ext δ δ') : DecVals δ' vs ts := fun δ'' e' => h δ'' (ext_trans e e')

theorem DecPs.mono {δ δ' : DScope} {vs : List (String × ValType)} {ps : List (String × Ty)}
    (h : DecPs δ vs ps) (e : Ext δ δ') : DecPs δ' vs ps := fun δ'' e' => h δ'' (ext_trans e e')

theorem DecDef.mono {δ δ' : DScope} {d : DefValType} {t : Ty} (h : DecDef δ d t) (e : Ext δ δ') :
    DecDef δ' d t := fun δ'' e' => h δ'' (ext_trans e e')

theorem DecDef.det {δ : DScope} {d : DefValType} {t t' : Ty} (h : DecDef δ d t) (h' : DecDef δ d t') :
    t = t' := by
  have e := (h δ (ext_refl δ)).symm.trans (h' δ (ext_refl δ))
  simp only [Except.ok.injEq, Prod.mk.injEq, TInfo.val.injEq] at e
  exact e.1

theorem decVal_prim (δ : DScope) (p : PrimValType) : DecVal δ (.prim p) (.prim p) :=
  fun _ _ => rfl

theorem decVal_idx {δ : DScope} {j : Nat} {t : Ty} (h : δ.types[j]? = some (.val t)) :
    DecVal δ (.idx j) t := fun δ' e => by
  simp [decVal, typeAt_run (e _ _ h)]

theorem decOpt_none (δ : DScope) : DecOpt δ none none := fun _ _ => rfl

theorem decOpt_some {δ : DScope} {v : ValType} {t : Ty} (h : DecVal δ v t) :
    DecOpt δ (some v) (some t) := fun δ' e => by
  simp [decValOpt, h δ' e]

theorem decVals_nil (δ : DScope) : DecVals δ [] [] := fun _ _ => rfl

theorem decVals_cons {δ : DScope} {v : ValType} {vs : List ValType} {t : Ty} {ts : List Ty}
    (h : DecVal δ v t) (hs : DecVals δ vs ts) : DecVals δ (v :: vs) (t :: ts) := fun δ' e => by
  simp [List.mapM_cons, h δ' e, hs δ' e]

theorem decPs_nil (δ : DScope) : DecPs δ [] [] := fun _ _ => rfl

theorem decPs_cons {δ : DScope} (n : String) {v : ValType} {vs : List (String × ValType)} {t : Ty}
    {ps : List (String × Ty)} (h : DecVal δ v t) (hs : DecPs δ vs ps) :
    DecPs δ ((n, v) :: vs) ((n, t) :: ps) := fun δ' e => by
  simp [List.mapM_cons, decParam, h δ' e, hs δ' e]

/-! ## One anonymous type definition -/

theorem decDef_list {δ : DScope} {v : ValType} {t : Ty} (h : DecVal δ v t) :
    DecDef δ (.list v) (.list t) := fun δ' e => by simp [decDefVal, h δ' e]

theorem decDef_fixedList {δ : DScope} {v : ValType} {t : Ty} (n : Nat) (h : DecVal δ v t) :
    DecDef δ (.fixedList v n) (.fixedList t n) := fun δ' e => by simp [decDefVal, h δ' e]

theorem decDef_map {δ : DScope} {v w : ValType} {t u : Ty} (h : DecVal δ v t) (h' : DecVal δ w u) :
    DecDef δ (.map v w) (.map t u) := fun δ' e => by simp [decDefVal, h δ' e, h' δ' e]

theorem decDef_option {δ : DScope} {v : ValType} {t : Ty} (h : DecVal δ v t) :
    DecDef δ (.option v) (.option t) := fun δ' e => by simp [decDefVal, h δ' e]

theorem decDef_result {δ : DScope} {v w : Option ValType} {t u : Option Ty} (h : DecOpt δ v t)
    (h' : DecOpt δ w u) : DecDef δ (.result v w) (.result t u) := fun δ' e => by
  simp [decDefVal, h δ' e, h' δ' e]

theorem decDef_tuple {δ : DScope} {vs : List ValType} {ts : List Ty} (h : DecVals δ vs ts) :
    DecDef δ (.tuple vs) (.tuple ts) := fun δ' e => by simp [decDefVal, h δ' e]

theorem decDef_future {δ : DScope} {v : Option ValType} {t : Option Ty} (h : DecOpt δ v t) :
    DecDef δ (.future v) (.future t) := fun δ' e => by simp [decDefVal, h δ' e]

theorem decDef_stream {δ : DScope} {v : Option ValType} {t : Option Ty} (h : DecOpt δ v t) :
    DecDef δ (.stream v) (.stream t) := fun δ' e => by simp [decDefVal, h δ' e]


/-! ## The simulation -/

/-- The encoder's and the decoder's type scopes agree. -/
structure MatchA (σ : Scope) (δ : DScope) : Prop where
  size : δ.types.size = σ.ntypes
  fc : ∀ s j, (s, j) ∈ σ.fcache → δ.types[j]? = some (.func s)
  vc : ∀ d j, (d, j) ∈ σ.vcache → ∃ t, δ.types[j]? = some (.val t) ∧ DecDef δ d t

/-- The decoder reads `E` as type definitions only, from `δ` to `δ'`; `E` consists of
instance declarations (it may sit in an instance type). -/
def Reads (E : List ComponentDecl) (δ δ' : DScope) : Prop :=
  DecodeEnc.InstOnly E ∧
    ∀ rest is es, (decCDecls (E ++ rest) is es).run δ = (decCDecls rest is es).run δ'

/-- An encoder step from `σ`, against the decoder at `δ`: it succeeds with `a`, emits
`E`, which the decoder reads as type definitions, keeps `MatchA`, `share` and the
decoder's nominal table, and ends with `Q a`. -/
def VSim {α : Type} (m : TM α) (σ : Scope) (δ : DScope) (Q : α → DScope → Prop) : Prop :=
  ∃ a σ' E δ', m.run σ = .ok (a, σ') ∧ σ'.decls = σ.decls ++ E ∧ MatchA σ' δ' ∧
    σ'.share = σ.share ∧ σ'.kcache = σ.kcache ∧ δ'.nom = δ.nom ∧ Ext δ δ' ∧ Reads E δ δ' ∧ Q a δ'

theorem reads_nil (δ : DScope) : Reads [] δ δ :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl⟩

theorem instOnly_append {E₁ E₂ : List ComponentDecl} (h₁ : DecodeEnc.InstOnly E₁)
    (h₂ : DecodeEnc.InstOnly E₂) : DecodeEnc.InstOnly (E₁ ++ E₂) := fun d hd =>
  (List.mem_append.1 hd).elim (h₁ d) (h₂ d)

theorem instOnly_single (x : InstanceDecl) : DecodeEnc.InstOnly [.inst x] := fun _ hd =>
  ⟨x, List.mem_singleton.1 hd⟩

theorem vsim_pure {α : Type} {a : α} {σ : Scope} {δ : DScope} {Q : α → DScope → Prop}
    (hm : MatchA σ δ) (hq : Q a δ) : VSim (pure a) σ δ Q :=
  ⟨a, σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl, rfl, ext_refl δ, reads_nil δ, hq⟩

theorem vsim_bind {α β : Type} {m : TM α} {f : α → TM β} {σ : Scope} {δ : DScope}
    {Q : α → DScope → Prop} {R : β → DScope → Prop} (h : VSim m σ δ Q)
    (k : ∀ a σ' δ', MatchA σ' δ' → Ext δ δ' → Q a δ' → VSim (f a) σ' δ' R) :
    VSim (m >>= f) σ δ R := by
  obtain ⟨a, σ1, E1, δ1, hr1, hd1, hm1, hs1, hk1, hn1, he1, hR1, hq1⟩ := h
  obtain ⟨b, σ2, E2, δ2, hr2, hd2, hm2, hs2, hk2, hn2, he2, hR2, hq2⟩ := k a σ1 δ1 hm1 he1 hq1
  refine ⟨b, σ2, E1 ++ E2, δ2, ?_, ?_, hm2, hs2.trans hs1, hk2.trans hk1, hn2.trans hn1, ext_trans he1 he2, ?_, hq2⟩
  · simp [StateT.run_bind, hr1, hr2]
  · rw [hd2, hd1, List.append_assoc]
  · refine ⟨instOnly_append hR1.1 hR2.1, fun rest is es => ?_⟩
    rw [List.append_assoc, hR1.2, hR2.2]

theorem vsim_congr {α : Type} {m m' : TM α} {σ : Scope} {δ : DScope} {Q : α → DScope → Prop}
    (e : m.run σ = m'.run σ) (h : VSim m' σ δ Q) : VSim m σ δ Q := by
  obtain ⟨a, σ', E, δ', hr, rest⟩ := h
  exact ⟨a, σ', E, δ', e.trans hr, rest⟩

theorem vsim_mono {α : Type} {m : TM α} {σ : Scope} {δ : DScope} {Q Q' : α → DScope → Prop}
    (h : VSim m σ δ Q) (k : ∀ a δ', Q a δ' → Q' a δ') : VSim m σ δ Q' := by
  obtain ⟨a, σ', E, δ', hr, hd, hm, hs, hk, hn, he, hR, hq⟩ := h
  exact ⟨a, σ', E, δ', hr, hd, hm, hs, hk, hn, he, hR, k a δ' hq⟩

theorem mem_of_lookupD {d : DefValType} {j : Nat} :
    ∀ {l : List (DefValType × Nat)}, l.lookup d = some j → (d, j) ∈ l
  | [], h => absurd h (by simp)
  | (d', j') :: l, h => by
    by_cases e : d = d'
    · have hb : (d == d') = true := beq_iff_eq.2 e
      have hj : j' = j := by simpa [List.lookup, hb] using h
      rw [e, hj]; exact List.mem_cons_self
    · have hb : (d == d') = false := beq_false_of_ne e
      have h' : l.lookup d = some j := by simpa [List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (mem_of_lookupD h')

/-- Defining a type keeps `MatchA` for the earlier types. -/
theorem matchA_push {σ σ' : Scope} {δ : DScope} (hm : MatchA σ δ) (x : TInfo)
    (hsz : σ'.ntypes = σ.ntypes + 1)
    (hfc : ∀ s j, (s, j) ∈ σ'.fcache → (s, j) ∈ σ.fcache ∨ (j = σ.ntypes ∧ x = .func s))
    (hvc : ∀ d j, (d, j) ∈ σ'.vcache → (d, j) ∈ σ.vcache ∨
      (j = σ.ntypes ∧ ∃ t, x = .val t ∧ DecDef δ d t)) :
    MatchA σ' { δ with types := δ.types.push x } := by
  have hsize : δ.types.size = σ.ntypes := hm.size
  constructor
  · simp [hsz, hsize]
  · intro s j hj
    rcases hfc s j hj with h | ⟨rfl, rfl⟩
    · exact push_keep (hm.fc s j h)
    · rw [← hsize]; exact push_self δ _
  · intro d j hj
    rcases hvc d j hj with h | ⟨rfl, t, rfl, hd⟩
    · obtain ⟨t, ht, hd⟩ := hm.vc d j h
      exact ⟨t, push_keep ht, hd.mono (ext_push δ _)⟩
    · refine ⟨t, ?_, hd.mono (ext_push δ _)⟩
      rw [← hsize]; exact push_self δ _

/-- The scope after defining the anonymous type `d`. -/
def defV (σ : Scope) (d : DefValType) : Scope :=
  { σ with decls := σ.decls ++ [.inst (.type (.val d))], ntypes := σ.ntypes + 1,
           vcache := σ.vcache ++ [(d, σ.ntypes)] }

theorem defVal_miss {d : DefValType} {σ : Scope} (hl : σ.vcache.lookup d = none) :
    (defVal d).run σ = .ok (.idx σ.ntypes, defV σ d) := by
  simp [defVal, hl, defTy]
  rfl

theorem reads_defVal {d : DefValType} {t : Ty} {δ : DScope} (hd : DecDef δ d t) :
    Reads [.inst (.type (.val d))] δ { δ with types := δ.types.push (.val t) } := by
  refine ⟨instOnly_single _, fun rest is es => ?_⟩
  simp [decCDecls, decIDecl, decDefType, pushTy, hd δ (ext_refl δ)]

theorem matchA_defV {d : DefValType} {t : Ty} {σ : Scope} {δ : DScope} (hm : MatchA σ δ)
    (hd : DecDef δ d t) : MatchA (defV σ d) { δ with types := δ.types.push (.val t) } := by
  refine matchA_push hm (.val t) rfl (fun s j hj => Or.inl hj) (fun d' j hj => ?_)
  rcases List.mem_append.1 hj with h | h
  · exact Or.inl h
  · have e := List.mem_singleton.1 h
    rw [(Prod.mk.inj e).1, (Prod.mk.inj e).2]
    exact Or.inr ⟨rfl, t, rfl, hd⟩

/-- **An anonymous type definition**: shared, or defined at the next index. -/
theorem vsim_defVal {d : DefValType} {t : Ty} {σ : Scope} {δ : DScope} (hm : MatchA σ δ)
    (hd : DecDef δ d t) : VSim (defVal d) σ δ (fun v δ' => DecVal δ' v t) := by
  cases hl : σ.vcache.lookup d with
  | some j =>
    obtain ⟨t', ht', hd'⟩ := hm.vc d j (mem_of_lookupD hl)
    have e : t' = t := hd'.det hd
    have hr : (defVal d).run σ = .ok (.idx j, σ) := by simp [defVal, hl]
    exact ⟨.idx j, σ, [], δ, hr, (List.append_nil _).symm, hm, rfl, rfl, rfl, ext_refl δ, reads_nil δ,
      decVal_idx (e ▸ ht')⟩
  | none =>
    have h : ({ δ with types := δ.types.push (.val t) } : DScope).types[σ.ntypes]? =
        some (.val t) := by rw [← hm.size]; exact push_self δ _
    exact ⟨.idx σ.ntypes, defV σ d, [.inst (.type (.val d))], _, defVal_miss hl, rfl,
      matchA_defV hm hd, rfl, rfl, rfl, ext_push δ _, reads_defVal hd, decVal_idx h⟩

/-! ## Value types -/

/-- What `valTy_sim` proves of a type. -/
def ValOk (t : Ty) : Prop :=
  ∀ σ δ, MatchA σ δ → VSim (valTy t) σ δ (fun v δ' => DecVal δ' v t)

theorem valTyOpt_sim {a : Option Ty} (ih : ∀ t ∈ a, ValOk t) {σ : Scope} {δ : DScope}
    (hm : MatchA σ δ) : VSim (valTyOpt a) σ δ (fun v δ' => DecOpt δ' v a) := by
  cases a with
  | none =>
    rw [valTyOpt]
    exact vsim_pure hm (decOpt_none δ)
  | some t =>
    rw [valTyOpt]
    exact vsim_bind (ih t rfl σ δ hm) fun v σ1 δ1 hm1 _ hv => vsim_pure hm1 (decOpt_some hv)

theorem valTys_sim : ∀ {ts : List Ty}, (∀ t ∈ ts, ValOk t) → ∀ {σ : Scope} {δ : DScope},
    MatchA σ δ → VSim (valTys ts) σ δ (fun vs δ' => DecVals δ' vs ts)
  | [], _, σ, δ, hm => by
    rw [valTys]
    exact vsim_pure hm (decVals_nil δ)
  | t :: ts, ih, σ, δ, hm => by
    have iht : ValOk t := ih t List.mem_cons_self
    have ihs : ∀ t' ∈ ts, ValOk t' := fun t' h => ih t' (List.mem_cons_of_mem _ h)
    rw [valTys]
    exact vsim_bind (iht σ δ hm) fun v σ1 δ1 hm1 _ hv =>
      vsim_bind (valTys_sim ihs hm1) fun vs σ2 δ2 hm2 e2 hvs =>
        vsim_pure hm2 (decVals_cons (hv.mono e2) hvs)

/-- **Every anonymous value type is encoded as a value type that decodes back to it.** -/
theorem valTy_sim {t : Ty} (h : Anon t) : ValOk t := by
  induction h with
  | prim p =>
    intro σ δ hm
    rw [valTy]
    exact vsim_pure hm (decVal_prim δ p)
  | list _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vsim_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv => vsim_defVal hm1 (decDef_list hv)
  | fixedList n _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vsim_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv => vsim_defVal hm1 (decDef_fixedList n hv)
  | map _ _ ihk ihv =>
    intro σ δ hm
    rw [valTy]
    exact vsim_bind (ihk σ δ hm) fun k σ1 δ1 hm1 _ hk =>
      vsim_bind (ihv σ1 δ1 hm1) fun v σ2 δ2 hm2 e2 hv => vsim_defVal hm2 (decDef_map (hk.mono e2) hv)
  | option _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vsim_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv => vsim_defVal hm1 (decDef_option hv)
  | result _ _ iha ihb =>
    intro σ δ hm
    rw [valTy]
    exact vsim_bind (valTyOpt_sim iha hm) fun x σ1 δ1 hm1 _ hx =>
      vsim_bind (valTyOpt_sim ihb hm1) fun y σ2 δ2 hm2 e2 hy =>
        vsim_defVal hm2 (decDef_result (hx.mono e2) hy)
  | tuple _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vsim_bind (valTys_sim ih hm) fun vs σ1 δ1 hm1 _ hvs => vsim_defVal hm1 (decDef_tuple hvs)
  | future _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vsim_bind (valTyOpt_sim ih hm) fun x σ1 δ1 hm1 _ hx => vsim_defVal hm1 (decDef_future hx)
  | stream _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vsim_bind (valTyOpt_sim ih hm) fun x σ1 δ1 hm1 _ hx => vsim_defVal hm1 (decDef_stream hx)

/-! ## Function types -/

theorem paramTys_sim : ∀ {ps : List (String × Ty)}, (∀ p ∈ ps, Anon p.2) → ∀ {σ : Scope}
    {δ : DScope}, MatchA σ δ → VSim (paramTys ps) σ δ (fun vs δ' => DecPs δ' vs ps)
  | [], _, σ, δ, hm => by
    rw [paramTys]
    exact vsim_pure hm (decPs_nil δ)
  | (n, t) :: ps, h, σ, δ, hm => by
    have ht : Anon t := h (n, t) List.mem_cons_self
    have hps : ∀ p ∈ ps, Anon p.2 := fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [paramTys]
    exact vsim_bind (valTy_sim ht σ δ hm) fun v σ1 δ1 hm1 _ hv =>
      vsim_bind (paramTys_sim hps hm1) fun vs σ2 δ2 hm2 e2 hvs =>
        vsim_pure hm2 (decPs_cons n (hv.mono e2) hvs)

theorem decFunc_run {δ : DScope} {vs : List (String × ValType)} {vr : Option ValType}
    {s : Sig} (hps : DecPs δ vs s.params) (hr : DecOpt δ vr s.result) (a : Bool) (h : a = s.async) :
    (decFunc ⟨vs, vr, a⟩).run δ = .ok (s, δ) := by
  have hp : (List.mapM (fun p : String × ValType => do let x ← decVal p.2; pure (p.1, x)) vs).run δ =
      .ok (s.params, δ) := hps δ (ext_refl δ)
  have hr' : (decValOpt vr).run δ = .ok (s.result, δ) := hr δ (ext_refl δ)
  unfold decFunc
  simp only [StateT.run_bind, hp, hr', ok_bind, StateT.run_pure, pure_ok, h]

/-- The block of `funcTy` that defines a function type. -/
def funcMiss (s : Sig) : TM Nat := do
  let ps ← paramTys s.params
  let r ← valTyOpt s.result
  let j ← defTy (.func ⟨ps, r, s.async⟩)
  modify fun sc => { sc with fcache := sc.fcache ++ [(s, j)] }
  pure j

theorem funcTy_miss {s : Sig} {σ : Scope} (h : σ.share = false ∨ σ.fcache.lookup s = none) :
    (funcTy s).run σ = (funcMiss s).run σ := by
  rcases h with h | h
  · cases hl : σ.fcache.lookup s <;> simp [funcTy, funcMiss, h, hl]
  · cases hsh : σ.share <;> simp [funcTy, funcMiss, h, hsh]

theorem vsim_defFunc {σ : Scope} {δ : DScope} {vs : List (String × ValType)}
    {vr : Option ValType} {s : Sig} (hm : MatchA σ δ) (hps : DecPs δ vs s.params)
    (hr : DecOpt δ vr s.result) :
    VSim (do
        let j ← defTy (.func ⟨vs, vr, s.async⟩)
        modify fun sc => { sc with fcache := sc.fcache ++ [(s, j)] }
        pure j) σ δ (fun j δ' => δ'.types[j]? = some (.func s)) := by
  let σ' : Scope := { σ with decls := σ.decls ++ [.inst (.type (.func ⟨vs, vr, s.async⟩))]
                             ntypes := σ.ntypes + 1
                             fcache := σ.fcache ++ [(s, σ.ntypes)] }
  let δ' : DScope := { δ with types := δ.types.push (.func s) }
  refine ⟨σ.ntypes, σ', [.inst (.type (.func ⟨vs, vr, s.async⟩))], δ', ?_, rfl, ?_, rfl, rfl, rfl,
    ext_push δ _, ?_, ?_⟩
  · simp [defTy]
    rfl
  · refine matchA_push hm (.func s) rfl (fun s' j hj => ?_) (fun d j hj => Or.inl hj)
    rcases List.mem_append.1 hj with h | h
    · exact Or.inl h
    · have e := List.mem_singleton.1 h
      rw [(Prod.mk.inj e).1, (Prod.mk.inj e).2]
      exact Or.inr ⟨rfl, rfl⟩
  · refine ⟨instOnly_single _, fun rest is es => ?_⟩
    simp [decCDecls, decIDecl, decDefType, pushTy, decFunc_run hps hr s.async rfl]
    rfl
  · show (δ.types.push (.func s))[σ.ntypes]? = some (.func s)
    rw [← hm.size]
    exact push_self δ _

/-- **Every function type over anonymous value types** is encoded at an index that decodes
back to it, shared or defined. -/
theorem funcTy_sim {s : Sig} (hs : AnonSig s) {σ : Scope} {δ : DScope} (hm : MatchA σ δ) :
    VSim (funcTy s) σ δ (fun j δ' => δ'.types[j]? = some (.func s)) := by
  by_cases hit : σ.share = true ∧ ∃ j, σ.fcache.lookup s = some j
  · obtain ⟨hsh, j, hl⟩ := hit
    refine ⟨j, σ, [], δ, ?_, (List.append_nil _).symm, hm, rfl, rfl, rfl, ext_refl δ, reads_nil δ,
      hm.fc s j (DecodeEnc.mem_of_lookup hl)⟩
    simp [funcTy, hsh, hl]
  · have h : σ.share = false ∨ σ.fcache.lookup s = none := by
      cases hsh : σ.share <;> cases hl : σ.fcache.lookup s <;> simp_all
    refine vsim_congr (funcTy_miss h) ?_
    unfold funcMiss
    exact vsim_bind (paramTys_sim hs.1 hm) fun ps σ1 δ1 hm1 _ hps =>
      vsim_bind (valTyOpt_sim (fun t ht => valTy_sim (hs.2 t ht)) hm1) fun r σ2 δ2 hm2 e2 hr =>
        vsim_defFunc hm2 (hps.mono e2) hr

/-! ## Imports and exports -/

/-- What encoding items does: ok, emitting `E`, keeping `MatchA`, `share` and the
decoder's nominal table, and the decoder reads `E` as `Rd` says. -/
def SimA (Rd : List ComponentDecl → DScope → DScope → Prop) (m : TM Unit) (σ : Scope)
    (δ : DScope) : Prop :=
  ∃ σ' E δ', m.run σ = .ok ((), σ') ∧ σ'.decls = σ.decls ++ E ∧ MatchA σ' δ' ∧
    σ'.share = σ.share ∧ δ'.nom = δ.nom ∧ Rd E δ δ'

theorem imports_sim : ∀ (is : Externs), AnonFns is → ∀ σ δ, MatchA σ δ →
    SimA (ReadsI is) (importDecls is) σ δ
  | [], _, σ, δ, hm => ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl,
      fun rest is es => by simp [List.append_nil]⟩
  | (n, k) :: xs, h, σ, δ, hm => by
    obtain ⟨s, hk, hs⟩ : ∃ s, k = .func s ∧ AnonSig s := h (n, k) List.mem_cons_self
    have hxs : AnonFns xs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [hk]
    obtain ⟨j, σ1, E1, δ1, hr1, hd1, hm1, hs1, -, hn1, -, hR1, hj⟩ := funcTy_sim hs hm
    let σ2 : Scope := { σ1 with decls := σ1.decls ++ [.import ⟨n, .plain0⟩ (.func j)] }
    have hm2 : MatchA σ2 δ1 := ⟨hm1.size, hm1.fc, hm1.vc⟩
    obtain ⟨σ', E, δ', hr, hd, hm', hsh, hn, hreads⟩ := imports_sim xs hxs σ2 δ1 hm2
    refine ⟨σ', E1 ++ .import ⟨n, .plain0⟩ (.func j) :: E, δ', ?_, ?_, hm', hsh.trans hs1,
      hn.trans hn1, ?_⟩
    · rw [importDecls_cons, hr1]
      exact hr
    · rw [hd, show σ2.decls = σ1.decls ++ [.import ⟨n, .plain0⟩ (.func j)] from rfl, hd1]
      simp
    · intro rest is es
      rw [List.append_assoc, hR1.2, List.cons_append, dec_import hj n, hreads]
      simp

theorem exports_sim : ∀ (es : Externs), AnonFns es → ∀ σ δ, MatchA σ δ →
    SimA (fun E δ δ' => ReadsE es E δ δ' ∧ DecodeEnc.InstOnly E) (exportDecls es) σ δ
  | [], _, σ, δ, hm => ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl,
      fun rest is es => by simp [List.append_nil], fun _ h => absurd h List.not_mem_nil⟩
  | (n, k) :: xs, h, σ, δ, hm => by
    obtain ⟨s, hk, hs⟩ : ∃ s, k = .func s ∧ AnonSig s := h (n, k) List.mem_cons_self
    have hxs : AnonFns xs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [hk]
    obtain ⟨j, σ1, E1, δ1, hr1, hd1, hm1, hs1, -, hn1, -, hR1, hj⟩ := funcTy_sim hs hm
    let σ2 : Scope := { σ1 with decls := σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ (.func j))] }
    have hm2 : MatchA σ2 δ1 := ⟨hm1.size, hm1.fc, hm1.vc⟩
    obtain ⟨σ', E, δ', hr, hd, hm', hsh, hn, hreads⟩ := exports_sim xs hxs σ2 δ1 hm2
    refine ⟨σ', E1 ++ .inst (.export ⟨n, .plain0⟩ (.func j)) :: E, δ', ?_, ?_, hm', hsh.trans hs1,
      hn.trans hn1, ?_⟩
    · rw [exportDecls_cons, hr1]
      exact hr
    · rw [hd, show σ2.decls = σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ (.func j))] from rfl, hd1]
      simp
    · exact ⟨fun rest is es => by
        rw [List.append_assoc, hR1.2, List.cons_append, dec_export hj n, hreads.1]
        simp, instOnly_append hR1.1 fun d hd => (List.mem_cons.1 hd).elim (fun e => ⟨_, e⟩)
          (hreads.2 d)⟩

/-- The empty scopes match. -/
theorem matchA_empty : MatchA { share := true } {} :=
  ⟨rfl, fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp)⟩

end DecodeAnon

end Silmaril.Wasm.Wac.Bridge
