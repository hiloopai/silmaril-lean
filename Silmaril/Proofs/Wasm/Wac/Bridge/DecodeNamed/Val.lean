module

public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeAnon

/-!
# WAC bridge: decoding inverts encoding on named value types

The value level of `Silmaril.Wasm.Wac.Bridge.DecodeNamed.Thms`. The invariant `M N Γ σ δ`
relates the encoder's scope `σ` (nominal table `N`) and the decoder's `δ` to the
context `Γ`: as many types; the cached function, anonymous, handle, instance and
component types decode at their indices; the indices recorded as resources decode to
resources; and the encoder's `names` are those of `Γ`, each at an index the decoder
reads as what `Γ` says (`NameAt`). The decoder's nominal definitions all come from `N`.

* `valTy_sim`: every value type of the fragment (`TyOk Γ`) is encoded as a value type
  that decodes back to it in every later scope (`DecodeAnon.DecVal`);
* `funcTy_sim`, `nominalTy_sim`: function types and nominal definitions decode back at
  the index the encoder returns.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef)
open DecodeEnc (typeAt_run ok_bind pure_ok)
open DecodeAnon (Ext ext_refl ext_trans push_keep ext_push push_self DecVal DecOpt DecVals DecPs
  DecDef decVal_prim decVal_idx decOpt_none decOpt_some decVals_nil decVals_cons decPs_nil
  decPs_cons decDef_list decDef_fixedList decDef_map decDef_option decDef_result decDef_tuple
  decDef_future decDef_stream Reads reads_nil instOnly_single mem_of_lookupD decFunc_run funcMiss
  funcTy_miss)

namespace DecodeNamed

attribute [local simp] ok_bind pure_ok

/-! ## The invariant -/

/-- A resource or a resource alias. -/
def IsRes : Option TInfo → Prop
  | some (.res _) | some (.resAlias _ _) => True
  | _ => False

/-- The decoder reads index `i` as what the name `a` stands for. -/
def NameAt (δ : DScope) (σ : Scope) (a : String) : NS → Nat → Prop
  | .res, i => δ.types[i]? = some (.res a) ∧ i ∈ σ.resIdx
  | .ali r, i => δ.types[i]? = some (.resAlias a r) ∧ i ∈ σ.resIdx
  | .val, i => δ.types[i]? = some (.val (.ref ⟨.local, a⟩))
  | .other, _ => True

/-- Two lists related pointwise. -/
inductive Pw {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pw R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : R a b → Pw R l l' → Pw R (a :: l) (b :: l')

theorem Pw.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, Pw R l l' → Pw S l l'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hab ht => .cons (h _ _ hab) (Pw.imp h ht)

theorem Pw.concat {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ {l : List α} {l' : List β}, Pw R l l' → Pw R (l ++ [a]) (l' ++ [b])
  | [], [], .nil => .cons hab .nil
  | _ :: _, _ :: _, .cons h ht => .cons h (Pw.concat hab ht)

/-- The decoding of a handle type. -/
def hdef (o : Bool) (i : Nat) : DefValType := if o then .own i else .borrow i

/-- **The invariant** between the encoder's scope `σ` and the decoder's `δ`. -/
structure M (N : NomTable) (Γ : Ctx) (σ : Scope) (δ : DScope) : Prop where
  size : δ.types.size = σ.ntypes
  nom : σ.nom = N
  dnom : ∀ p ∈ δ.nom, N.lookup p.1 = some p.2
  fc : ∀ s j, (s, j) ∈ σ.fcache → δ.types[j]? = some (.func s)
  vc : ∀ d j, (d, j) ∈ σ.vcache → ∃ t, δ.types[j]? = some (.val t) ∧ DecDef δ d t
  hc : ∀ o i j, ((o, i), j) ∈ σ.hcache → ∃ t, δ.types[j]? = some (.val t) ∧ DecDef δ (hdef o i) t
  kc : ∀ k j, (k, j) ∈ σ.kcache → δ.types[j]? = some (infoK k)
  res : ∀ i, i ∈ σ.resIdx ↔ IsRes δ.types[i]?
  names : Pw (fun p q => p.1 = q.1 ∧ NameAt δ σ q.1 q.2 p.2) σ.names Γ

theorem lt_of_some {δ : DScope} {i : Nat} {x : TInfo} (h : δ.types[i]? = some x) : i < δ.types.size :=
  (Array.getElem?_eq_some_iff.1 h).1

theorem isRes_lt {δ : DScope} {i : Nat} (h : IsRes δ.types[i]?) : i < δ.types.size := by
  cases e : δ.types[i]? with
  | none => rw [e] at h; exact absurd h id
  | some x => exact lt_of_some e

theorem not_res {σ : Scope} {δ : DScope} {N : NomTable} {Γ : Ctx} (hm : M N Γ σ δ) {i : Nat} {x : TInfo}
    (h : δ.types[i]? = some x) (hx : ¬ IsRes (some x)) : i ∉ σ.resIdx := fun hi =>
  hx (h ▸ (hm.res i).1 hi)

theorem isRes_push (δ : DScope) (y : TInfo) (i : Nat) :
    IsRes (δ.types.push y)[i]? ↔ IsRes δ.types[i]? ∨ (i = δ.types.size ∧ IsRes (some y)) := by
  by_cases e : i = δ.types.size
  · have h0 : δ.types[i]? = none := by simp [e]
    have h1 : (δ.types.push y)[i]? = some y := by rw [e]; exact push_self δ y
    rw [h1, h0]
    exact ⟨fun h => Or.inr ⟨e, h⟩, fun h => h.elim (fun h => absurd h id) (fun h => h.2)⟩
  · have e' : (δ.types.push y)[i]? = δ.types[i]? := by simp [Array.getElem?_push, e]
    rw [e']
    exact ⟨Or.inl, fun h => h.elim id (fun h => absurd h.1 e)⟩

theorem nameAt_mono {δ δ' : DScope} {σ σ' : Scope} {a : String} {x : NS} {i : Nat}
    (he : Ext δ δ') (hr : ∀ j ∈ σ.resIdx, j ∈ σ'.resIdx) (h : NameAt δ σ a x i) : NameAt δ' σ' a x i := by
  cases x with
  | res => exact ⟨he _ _ h.1, hr _ h.2⟩
  | ali r => exact ⟨he _ _ h.1, hr _ h.2⟩
  | val => exact he _ _ h
  | other => trivial

theorem names_mono {δ δ' : DScope} {σ σ' : Scope} (he : Ext δ δ') (hr : ∀ j ∈ σ.resIdx, j ∈ σ'.resIdx)
    {l : List (String × Nat)} {Γ : Ctx}
    (h : Pw (fun p q => p.1 = q.1 ∧ NameAt δ σ q.1 q.2 p.2) l Γ) :
    Pw (fun p q => p.1 = q.1 ∧ NameAt δ' σ' q.1 q.2 p.2) l Γ :=
  Pw.imp (fun _ _ hpq => ⟨hpq.1, nameAt_mono he hr hpq.2⟩) h

/-- Lookups in the encoder's names follow those in the context. -/
theorem lookup_names {P : String → NS → Nat → Prop} {a : String} :
    ∀ {l : List (String × Nat)} {Γ : Ctx}, Pw (fun p q => p.1 = q.1 ∧ P q.1 q.2 p.2) l Γ →
      (∀ x, Γ.lookup a = some x → ∃ i, l.lookup a = some i ∧ P a x i) ∧
        (Γ.lookup a = none → l.lookup a = none)
  | [], [], .nil => ⟨fun _ h => absurd h (by simp), fun _ => rfl⟩
  | (b, i) :: l, (c, y) :: Γ, .cons hpq ht => by
    obtain ⟨ih1, ih2⟩ := lookup_names ht
    have hbc : b = c := hpq.1
    by_cases e : a = c
    · have hb : (a == c) = true := beq_iff_eq.2 e
      have hb' : (a == b) = true := beq_iff_eq.2 (e.trans hbc.symm)
      refine ⟨fun x hx => ⟨i, by simp [List.lookup, hb'], ?_⟩, fun hx => by simp [List.lookup, hb] at hx⟩
      have hxy : y = x := by simpa [List.lookup, hb] using hx
      rw [e, ← hxy]; exact hpq.2
    · have hb : (a == c) = false := beq_false_of_ne e
      have hb' : (a == b) = false := beq_false_of_ne fun e' => e (e'.trans hbc)
      refine ⟨fun x hx => ?_, fun hx => ?_⟩
      · obtain ⟨j, hj, hp⟩ := ih1 x (by simpa [List.lookup, hb] using hx)
        exact ⟨j, by simp [List.lookup, hb', hj], hp⟩
      · simpa [List.lookup, hb'] using ih2 (by simpa [List.lookup, hb] using hx)

theorem M.lookup {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} (hm : M N Γ σ δ) {a : String}
    {x : NS} (h : Γ.lookup a = some x) : ∃ i, σ.names.lookup a = some i ∧ NameAt δ σ a x i :=
  (lookup_names hm.names).1 x h

theorem M.lookup_none {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} (hm : M N Γ σ δ) {a : String}
    (h : Γ.lookup a = none) : σ.names.lookup a = none :=
  (lookup_names hm.names).2 h

/-- The decoder's other components (nominal table, instances) may change. -/
theorem M.retype {N : NomTable} {Γ : Ctx} {σ : Scope} {δ δ' : DScope} (hm : M N Γ σ δ)
    (e : δ'.types = δ.types) (hn : ∀ p ∈ δ'.nom, N.lookup p.1 = some p.2) : M N Γ σ δ' := by
  have he : Ext δ δ' := fun i x h => by rw [e]; exact h
  refine ⟨by rw [e]; exact hm.size, hm.nom, hn, fun s j hj => he _ _ (hm.fc s j hj), fun d j hj => ?_,
    fun o i j hj => ?_, fun k j hj => he _ _ (hm.kc k j hj), fun i => by rw [e]; exact hm.res i,
    names_mono he (fun _ h => h) hm.names⟩
  · obtain ⟨t, ht, hd⟩ := hm.vc d j hj
    exact ⟨t, he _ _ ht, hd.mono he⟩
  · obtain ⟨t, ht, hd⟩ := hm.hc o i j hj
    exact ⟨t, he _ _ ht, hd.mono he⟩

/-- **Defining a type** keeps `M` for the earlier types, if the caches grow only by the
new index, decoded as `x`. -/
theorem M.push {N : NomTable} {Γ : Ctx} {σ σ' : Scope} {δ : DScope} (hm : M N Γ σ δ) (x : TInfo)
    (hx : ¬ IsRes (some x))
    (hsz : σ'.ntypes = σ.ntypes + 1) (hnom : σ'.nom = σ.nom) (hres : σ'.resIdx = σ.resIdx)
    (hnames : σ'.names = σ.names)
    (hfc : ∀ s j, (s, j) ∈ σ'.fcache → (s, j) ∈ σ.fcache ∨ (j = σ.ntypes ∧ x = .func s))
    (hvc : ∀ d j, (d, j) ∈ σ'.vcache → (d, j) ∈ σ.vcache ∨
      (j = σ.ntypes ∧ ∃ t, x = .val t ∧ DecDef δ d t))
    (hhc : ∀ o i j, ((o, i), j) ∈ σ'.hcache → ((o, i), j) ∈ σ.hcache ∨
      (j = σ.ntypes ∧ ∃ t, x = .val t ∧ DecDef δ (hdef o i) t))
    (hkc : ∀ k j, (k, j) ∈ σ'.kcache → (k, j) ∈ σ.kcache ∨ (j = σ.ntypes ∧ x = infoK k)) :
    M N Γ σ' { δ with types := δ.types.push x } := by
  have hsize : δ.types.size = σ.ntypes := hm.size
  have he : Ext δ { δ with types := δ.types.push x } := ext_push δ x
  have hnew : ({ δ with types := δ.types.push x } : DScope).types[σ.ntypes]? = some x := by
    rw [← hsize]; exact push_self δ x
  refine ⟨by simp [hsz, hsize], hnom.trans hm.nom, hm.dnom, fun s j hj => ?_, fun d j hj => ?_,
    fun o i j hj => ?_, fun k j hj => ?_, fun i => ?_, ?_⟩
  · rcases hfc s j hj with h | ⟨rfl, rfl⟩
    · exact he _ _ (hm.fc s j h)
    · exact hnew
  · rcases hvc d j hj with h | ⟨rfl, t, rfl, hd⟩
    · obtain ⟨t, ht, hd⟩ := hm.vc d j h
      exact ⟨t, he _ _ ht, hd.mono he⟩
    · exact ⟨t, hnew, hd.mono he⟩
  · rcases hhc o i j hj with h | ⟨rfl, t, rfl, hd⟩
    · obtain ⟨t, ht, hd⟩ := hm.hc o i j h
      exact ⟨t, he _ _ ht, hd.mono he⟩
    · exact ⟨t, hnew, hd.mono he⟩
  · rcases hkc k j hj with h | ⟨rfl, rfl⟩
    · exact he _ _ (hm.kc k j h)
    · exact hnew
  · show i ∈ σ'.resIdx ↔ IsRes (δ.types.push x)[i]?
    rw [hres, isRes_push, ← hm.res i]
    exact ⟨Or.inl, fun h => h.elim id (fun h => absurd h.2 hx)⟩
  · rw [hnames]
    exact names_mono he (fun j h => hres ▸ h) hm.names

/-- The scope after declaring the type name `n` at the next index. -/
def declS (σ : Scope) (n : String) (isRes : Bool) : Scope :=
  { σ with
    ntypes := σ.ntypes + 1
    names := σ.names ++ [(n, σ.ntypes)]
    resIdx := if isRes then σ.resIdx ++ [σ.ntypes] else σ.resIdx }

/-- **Declaring a type name** `n` at the next index, decoded as `y`. -/
theorem M.declare {N : NomTable} {Γ : Ctx} {σ : Scope} {δ δ' : DScope} (hm : M N Γ σ δ) (n : String)
    (x : NS) (y : TInfo) (isRes : Bool) (ht : δ'.types = δ.types.push y)
    (hn : ∀ p ∈ δ'.nom, N.lookup p.1 = some p.2)
    (hr : isRes = true ↔ IsRes (some y))
    (hy : NameAt δ' (declS σ n isRes) n x σ.ntypes) :
    M N (Γ ++ [(n, x)]) (declS σ n isRes) δ' := by
  have hsize : δ.types.size = σ.ntypes := hm.size
  have he : Ext δ δ' := fun i z h => by rw [ht]; exact push_keep h
  have hres : ∀ j ∈ σ.resIdx, j ∈ (if isRes then σ.resIdx ++ [σ.ntypes] else σ.resIdx) := by
    intro j hj
    cases isRes <;> simp [hj]
  refine ⟨by simp [ht, hsize, declS], hm.nom, hn, fun s j hj => he _ _ (hm.fc s j hj), fun d j hj => ?_,
    fun o i j hj => ?_, fun k j hj => he _ _ (hm.kc k j hj), fun i => ?_, ?_⟩
  · obtain ⟨t, h1, hd⟩ := hm.vc d j hj
    exact ⟨t, he _ _ h1, hd.mono he⟩
  · obtain ⟨t, h1, hd⟩ := hm.hc o i j hj
    exact ⟨t, he _ _ h1, hd.mono he⟩
  · show i ∈ (if isRes then σ.resIdx ++ [σ.ntypes] else σ.resIdx) ↔ IsRes δ'.types[i]?
    rw [ht, isRes_push, ← hm.res i, hsize]
    cases isRes with
    | false => exact ⟨Or.inl, fun h => h.elim id fun h => absurd (hr.2 h.2) Bool.false_ne_true⟩
    | true =>
      simp only [ite_true, List.mem_append, List.mem_singleton]
      exact ⟨fun h => h.elim Or.inl fun h => Or.inr ⟨h, hr.1 rfl⟩, fun h => h.elim Or.inl fun h => Or.inr h.1⟩
  · exact Pw.concat ⟨rfl, hy⟩ (names_mono he hres hm.names)

/-- The empty scopes of a nested scope match. -/
theorem m_empty {N : NomTable} (b : Bool) (δ : DScope) (hn : ∀ p ∈ δ.nom, N.lookup p.1 = some p.2) :
    M N [] { nom := N, share := b } { outer := δ.types :: δ.outer, nom := δ.nom } :=
  ⟨rfl, rfl, hn, fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp),
    fun _ _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp),
    fun _ => ⟨fun h => absurd h (by simp), fun h => by simp [IsRes] at h⟩, .nil⟩

/-! ## Encoder steps -/

/-- An encoder step from `σ`, against the decoder at `δ`: it succeeds with `a`, emits `E`,
which the decoder reads as type definitions, keeps `M` (in the same context) and
`share`, and ends with `Q a`. -/
def VS {α : Type} (N : NomTable) (Γ : Ctx) (m : TM α) (σ : Scope) (δ : DScope)
    (Q : α → DScope → Prop) : Prop :=
  ∃ a σ' E δ', m.run σ = .ok (a, σ') ∧ σ'.decls = σ.decls ++ E ∧ M N Γ σ' δ' ∧
    σ'.share = σ.share ∧ Ext δ δ' ∧ Reads E δ δ' ∧ Q a δ'

theorem vs_pure {N : NomTable} {Γ : Ctx} {α : Type} {a : α} {σ : Scope} {δ : DScope}
    {Q : α → DScope → Prop} (hm : M N Γ σ δ) (hq : Q a δ) : VS N Γ (pure a) σ δ Q :=
  ⟨a, σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, ext_refl δ, reads_nil δ, hq⟩

theorem vs_bind {N : NomTable} {Γ : Ctx} {α β : Type} {m : TM α} {f : α → TM β} {σ : Scope}
    {δ : DScope} {Q : α → DScope → Prop} {R : β → DScope → Prop} (h : VS N Γ m σ δ Q)
    (k : ∀ a σ' δ', M N Γ σ' δ' → Ext δ δ' → Q a δ' → VS N Γ (f a) σ' δ' R) :
    VS N Γ (m >>= f) σ δ R := by
  obtain ⟨a, σ1, E1, δ1, hr1, hd1, hm1, hs1, he1, hR1, hq1⟩ := h
  obtain ⟨b, σ2, E2, δ2, hr2, hd2, hm2, hs2, he2, hR2, hq2⟩ := k a σ1 δ1 hm1 he1 hq1
  refine ⟨b, σ2, E1 ++ E2, δ2, ?_, ?_, hm2, hs2.trans hs1, ext_trans he1 he2, ?_, hq2⟩
  · simp [StateT.run_bind, hr1, hr2]
  · rw [hd2, hd1, List.append_assoc]
  · refine ⟨DecodeAnon.instOnly_append hR1.1 hR2.1, fun rest is es => ?_⟩
    rw [List.append_assoc, hR1.2, hR2.2]

theorem vs_congr {N : NomTable} {Γ : Ctx} {α : Type} {m m' : TM α} {σ : Scope} {δ : DScope}
    {Q : α → DScope → Prop} (e : m.run σ = m'.run σ) (h : VS N Γ m' σ δ Q) : VS N Γ m σ δ Q := by
  obtain ⟨a, σ', E, δ', hr, rest⟩ := h
  exact ⟨a, σ', E, δ', e.trans hr, rest⟩

/-! ## Handles -/

theorem decDef_own_res {δ : DScope} {i : Nat} {a : String} (h : δ.types[i]? = some (.res a)) :
    DecDef δ (hdef true i) (.own ⟨.local, a⟩) := fun δ' e => by
  simp [hdef, decDefVal, resAt, typeAt_run (e _ _ h)]

theorem decDef_own_alias {δ : DScope} {i : Nat} {a r : String} (h : δ.types[i]? = some (.resAlias a r)) :
    DecDef δ (hdef true i) (.ref ⟨.local, a⟩) := fun δ' e => by
  simp [hdef, decDefVal, typeAt_run (e _ _ h)]

theorem decDef_borrow_res {δ : DScope} {i : Nat} {a : String} (h : δ.types[i]? = some (.res a)) :
    DecDef δ (hdef false i) (.borrow ⟨.local, a⟩) := fun δ' e => by
  simp [hdef, decDefVal, resAt, typeAt_run (e _ _ h)]

theorem decDef_borrow_alias {δ : DScope} {i : Nat} {a r : String}
    (h : δ.types[i]? = some (.resAlias a r)) : DecDef δ (hdef false i) (.borrow ⟨.local, a⟩) :=
  fun δ' e => by simp [hdef, decDefVal, resAt, typeAt_run (e _ _ h)]

theorem mem_of_lookupH {k : Bool × Nat} {j : Nat} :
    ∀ {l : List ((Bool × Nat) × Nat)}, l.lookup k = some j → (k, j) ∈ l
  | [], h => absurd h (by simp)
  | (k', j') :: l, h => by
    by_cases e : k = k'
    · have hb : (k == k') = true := beq_iff_eq.2 e
      have hj : j' = j := by simpa [List.lookup, hb] using h
      rw [e, hj]; exact List.mem_cons_self
    · have hb : (k == k') = false := beq_false_of_ne e
      have h' : l.lookup k = some j := by simpa [List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (mem_of_lookupH h')

/-- **A handle type**: shared, or defined at the next index. -/
theorem handle_sim {N : NomTable} {Γ : Ctx} {o : Bool} {i : Nat} {t : Silmaril.Wasm.Wit.Binary.Ty} {σ : Scope} {δ : DScope}
    (hm : M N Γ σ δ) (hd : DecDef δ (hdef o i) t) : VS N Γ (handle o i) σ δ (fun v δ' => DecVal δ' v t) := by
  cases hl : σ.hcache.lookup (o, i) with
  | some j =>
    obtain ⟨t', ht', hd'⟩ := hm.hc o i j (mem_of_lookupH hl)
    have e : t' = t := hd'.det hd
    have hr : (handle o i).run σ = .ok (.idx j, σ) := by simp [handle, hl]
    exact ⟨.idx j, σ, [], δ, hr, (List.append_nil _).symm, hm, rfl, ext_refl δ, reads_nil δ,
      decVal_idx (e ▸ ht')⟩
  | none =>
    show VS N Γ (handle o i) σ δ (fun v δ' => DecVal δ' v t)
    let σ' : Scope := { σ with
      decls := σ.decls ++ [.inst (.type (.val (hdef o i)))]
      ntypes := σ.ntypes + 1
      hcache := σ.hcache ++ [((o, i), σ.ntypes)] }
    have hr : (handle o i).run σ = .ok (.idx σ.ntypes, σ') := by
      cases o <;> simp [handle, hl, defTy, hdef, σ']
    have hm' : M N Γ σ' { δ with types := δ.types.push (.val t) } := by
      refine hm.push (.val t) id rfl rfl rfl rfl (fun s j hj => Or.inl hj) (fun d j hj => Or.inl hj)
        (fun o' i' j hj => ?_) (fun k j hj => Or.inl hj)
      rcases List.mem_append.1 hj with h | h
      · exact Or.inl h
      · have e : ((o', i'), j) = ((o, i), σ.ntypes) := List.mem_singleton.1 h
        have e1 : (o', i') = (o, i) := (Prod.mk.inj e).1
        rw [(Prod.mk.inj e1).1, (Prod.mk.inj e1).2, (Prod.mk.inj e).2]
        exact Or.inr ⟨rfl, t, rfl, hd⟩
    have h : ({ δ with types := δ.types.push (.val t) } : DScope).types[σ.ntypes]? = some (.val t) := by
      rw [← hm.size]; exact push_self δ _
    refine ⟨.idx σ.ntypes, σ', [.inst (.type (.val (hdef o i)))], _, hr, rfl, hm', rfl, ext_push δ _,
      ⟨instOnly_single _, fun rest is es => ?_⟩, decVal_idx h⟩
    simp [decCDecls, decIDecl, decDefType, pushTy, hd δ (ext_refl δ)]

/-! ## Anonymous types -/

/-- **An anonymous type definition**: shared, or defined at the next index. -/
theorem defVal_sim {N : NomTable} {Γ : Ctx} {d : DefValType} {t : Silmaril.Wasm.Wit.Binary.Ty} {σ : Scope} {δ : DScope}
    (hm : M N Γ σ δ) (hd : DecDef δ d t) : VS N Γ (defVal d) σ δ (fun v δ' => DecVal δ' v t) := by
  cases hl : σ.vcache.lookup d with
  | some j =>
    obtain ⟨t', ht', hd'⟩ := hm.vc d j (mem_of_lookupD hl)
    have e : t' = t := hd'.det hd
    have hr : (defVal d).run σ = .ok (.idx j, σ) := by simp [defVal, hl]
    exact ⟨.idx j, σ, [], δ, hr, (List.append_nil _).symm, hm, rfl, ext_refl δ, reads_nil δ,
      decVal_idx (e ▸ ht')⟩
  | none =>
    show VS N Γ (defVal d) σ δ (fun v δ' => DecVal δ' v t)
    have hm' : M N Γ (DecodeAnon.defV σ d) { δ with types := δ.types.push (.val t) } := by
      refine hm.push (.val t) id rfl rfl rfl rfl (fun s j hj => Or.inl hj) (fun d' j hj => ?_)
        (fun o i j hj => Or.inl hj) (fun k j hj => Or.inl hj)
      rcases List.mem_append.1 hj with h | h
      · exact Or.inl h
      · have e : (d', j) = (d, σ.ntypes) := List.mem_singleton.1 h
        rw [(Prod.mk.inj e).1, (Prod.mk.inj e).2]
        exact Or.inr ⟨rfl, t, rfl, hd⟩
    have h : ({ δ with types := δ.types.push (.val t) } : DScope).types[σ.ntypes]? = some (.val t) := by
      rw [← hm.size]; exact push_self δ _
    exact ⟨.idx σ.ntypes, DecodeAnon.defV σ d, [.inst (.type (.val d))], _, DecodeAnon.defVal_miss hl,
      rfl, hm', rfl, ext_push δ _, DecodeAnon.reads_defVal hd, decVal_idx h⟩

/-! ## Value types -/

/-- What `valTy_sim` proves of a type. -/
def ValOk (N : NomTable) (Γ : Ctx) (t : Silmaril.Wasm.Wit.Binary.Ty) : Prop :=
  ∀ σ δ, M N Γ σ δ → VS N Γ (valTy t) σ δ (fun v δ' => DecVal δ' v t)

theorem valTyOpt_sim {N : NomTable} {Γ : Ctx} {a : Option Silmaril.Wasm.Wit.Binary.Ty} (ih : ∀ t ∈ a, ValOk N Γ t)
    {σ : Scope} {δ : DScope} (hm : M N Γ σ δ) : VS N Γ (valTyOpt a) σ δ (fun v δ' => DecOpt δ' v a) := by
  cases a with
  | none =>
    rw [valTyOpt]
    exact vs_pure hm (decOpt_none δ)
  | some t =>
    rw [valTyOpt]
    exact vs_bind (ih t rfl σ δ hm) fun v σ1 δ1 hm1 _ hv => vs_pure hm1 (decOpt_some hv)

theorem valTys_sim {N : NomTable} {Γ : Ctx} : ∀ {ts : List Silmaril.Wasm.Wit.Binary.Ty}, (∀ t ∈ ts, ValOk N Γ t) →
    ∀ {σ : Scope} {δ : DScope}, M N Γ σ δ → VS N Γ (valTys ts) σ δ (fun vs δ' => DecVals δ' vs ts)
  | [], _, σ, δ, hm => by
    rw [valTys]
    exact vs_pure hm (decVals_nil δ)
  | t :: ts, ih, σ, δ, hm => by
    have iht : ValOk N Γ t := ih t List.mem_cons_self
    have ihs : ∀ t' ∈ ts, ValOk N Γ t' := fun t' h => ih t' (List.mem_cons_of_mem _ h)
    rw [valTys]
    exact vs_bind (iht σ δ hm) fun v σ1 δ1 hm1 _ hv =>
      vs_bind (valTys_sim ihs hm1) fun vs σ2 δ2 hm2 e2 hvs =>
        vs_pure hm2 (decVals_cons (hv.mono e2) hvs)

theorem namedTy_run {σ : Scope} {a : String} {i : Nat} (h : σ.names.lookup a = some i) :
    (namedTy a).run σ = .ok (i, σ) := by
  simp [namedTy, h]

theorem valTy_ref_run {σ : Scope} {r : TyRef} {i : Nat} (h : σ.names.lookup r.name = some i) :
    (valTy (.ref r)).run σ = (if i ∈ σ.resIdx then handle true i else pure (.idx i)).run σ := by
  simp [valTy, namedTy, h]

theorem valTy_own_run {σ : Scope} {r : TyRef} {i : Nat} (h : σ.names.lookup r.name = some i) :
    (valTy (.own r)).run σ = (handle true i).run σ := by
  simp [valTy, namedTy, h]

theorem valTy_borrow_run {σ : Scope} {r : TyRef} {i : Nat} (h : σ.names.lookup r.name = some i) :
    (valTy (.borrow r)).run σ = (handle false i).run σ := by
  simp [valTy, namedTy, h]

theorem refVal_sim {N : NomTable} {Γ : Ctx} {a : String} (h : Γ.lookup a = some .val) :
    ValOk N Γ (.ref ⟨.local, a⟩) := fun σ δ hm => by
  obtain ⟨i, hi, hat⟩ := hm.lookup h
  have hat' : δ.types[i]? = some (.val (.ref ⟨.local, a⟩)) := hat
  have hnr : i ∉ σ.resIdx := not_res hm hat' id
  refine vs_congr (valTy_ref_run (r := ⟨.local, a⟩) hi) ?_
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnr)]
  exact vs_pure hm (decVal_idx hat')

theorem refAlias_sim {N : NomTable} {Γ : Ctx} {a r : String} (h : Γ.lookup a = some (.ali r)) :
    ValOk N Γ (.ref ⟨.local, a⟩) := fun σ δ hm => by
  obtain ⟨i, hi, hat, hres⟩ := hm.lookup h
  refine vs_congr (valTy_ref_run (r := ⟨.local, a⟩) hi) ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true hres)]
  exact handle_sim hm (decDef_own_alias hat)

theorem own_sim {N : NomTable} {Γ : Ctx} {a : String} (h : Γ.lookup a = some .res) :
    ValOk N Γ (.own ⟨.local, a⟩) := fun σ δ hm => by
  obtain ⟨i, hi, hat, -⟩ := hm.lookup h
  exact vs_congr (valTy_own_run (r := ⟨.local, a⟩) hi) (handle_sim hm (decDef_own_res hat))

theorem borrowRes_sim {N : NomTable} {Γ : Ctx} {a : String} (h : Γ.lookup a = some .res) :
    ValOk N Γ (.borrow ⟨.local, a⟩) := fun σ δ hm => by
  obtain ⟨i, hi, hat, -⟩ := hm.lookup h
  exact vs_congr (valTy_borrow_run (r := ⟨.local, a⟩) hi) (handle_sim hm (decDef_borrow_res hat))

theorem borrowAlias_sim {N : NomTable} {Γ : Ctx} {a r : String} (h : Γ.lookup a = some (.ali r)) :
    ValOk N Γ (.borrow ⟨.local, a⟩) := fun σ δ hm => by
  obtain ⟨i, hi, hat, -⟩ := hm.lookup h
  exact vs_congr (valTy_borrow_run (r := ⟨.local, a⟩) hi) (handle_sim hm (decDef_borrow_alias hat))

/-- **Every value type of the fragment** is encoded as a value type that decodes back
to it. -/
theorem valTy_sim {N : NomTable} {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : TyOk Γ t) : ValOk N Γ t := by
  induction h with
  | prim p => exact fun σ δ hm => by rw [valTy]; exact vs_pure hm (decVal_prim δ p)
  | refVal h => exact refVal_sim h
  | refAlias h => exact refAlias_sim h
  | own h => exact own_sim h
  | borrowRes h => exact borrowRes_sim h
  | borrowAlias h => exact borrowAlias_sim h
  | list _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vs_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv => defVal_sim hm1 (decDef_list hv)
  | fixedList n _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vs_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv => defVal_sim hm1 (decDef_fixedList n hv)
  | map _ _ ihk ihv =>
    intro σ δ hm
    rw [valTy]
    exact vs_bind (ihk σ δ hm) fun k σ1 δ1 hm1 _ hk =>
      vs_bind (ihv σ1 δ1 hm1) fun v σ2 δ2 hm2 e2 hv => defVal_sim hm2 (decDef_map (hk.mono e2) hv)
  | option _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vs_bind (ih σ δ hm) fun v σ1 δ1 hm1 _ hv => defVal_sim hm1 (decDef_option hv)
  | result _ _ iha ihb =>
    intro σ δ hm
    rw [valTy]
    exact vs_bind (valTyOpt_sim iha hm) fun x σ1 δ1 hm1 _ hx =>
      vs_bind (valTyOpt_sim ihb hm1) fun y σ2 δ2 hm2 e2 hy =>
        defVal_sim hm2 (decDef_result (hx.mono e2) hy)
  | tuple _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vs_bind (valTys_sim ih hm) fun vs σ1 δ1 hm1 _ hvs => defVal_sim hm1 (decDef_tuple hvs)
  | future _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vs_bind (valTyOpt_sim ih hm) fun x σ1 δ1 hm1 _ hx => defVal_sim hm1 (decDef_future hx)
  | stream _ ih =>
    intro σ δ hm
    rw [valTy]
    exact vs_bind (valTyOpt_sim ih hm) fun x σ1 δ1 hm1 _ hx => defVal_sim hm1 (decDef_stream hx)

/-! ## Function types -/

theorem paramTys_sim {N : NomTable} {Γ : Ctx} : ∀ {ps : List (String × Silmaril.Wasm.Wit.Binary.Ty)}, (∀ p ∈ ps, TyOk Γ p.2) →
    ∀ {σ : Scope} {δ : DScope}, M N Γ σ δ → VS N Γ (paramTys ps) σ δ (fun vs δ' => DecPs δ' vs ps)
  | [], _, σ, δ, hm => by
    rw [paramTys]
    exact vs_pure hm (decPs_nil δ)
  | (n, t) :: ps, h, σ, δ, hm => by
    have ht : TyOk Γ t := h (n, t) List.mem_cons_self
    have hps : ∀ p ∈ ps, TyOk Γ p.2 := fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [paramTys]
    exact vs_bind (valTy_sim ht σ δ hm) fun v σ1 δ1 hm1 _ hv =>
      vs_bind (paramTys_sim hps hm1) fun vs σ2 δ2 hm2 e2 hvs =>
        vs_pure hm2 (decPs_cons n (hv.mono e2) hvs)

theorem defFunc_sim {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} {vs : List (String × Silmaril.Wasm.Component.Binary.ValType)}
    {vr : Option Silmaril.Wasm.Component.Binary.ValType} {s : Sig} (hm : M N Γ σ δ) (hps : DecPs δ vs s.params)
    (hr : DecOpt δ vr s.result) :
    VS N Γ (do
        let j ← defTy (.func ⟨vs, vr, s.async⟩)
        modify fun sc => { sc with fcache := sc.fcache ++ [(s, j)] }
        pure j) σ δ (fun j δ' => δ'.types[j]? = some (.func s)) := by
  let σ' : Scope := { σ with decls := σ.decls ++ [.inst (.type (.func ⟨vs, vr, s.async⟩))]
                             ntypes := σ.ntypes + 1
                             fcache := σ.fcache ++ [(s, σ.ntypes)] }
  have hm' : M N Γ σ' { δ with types := δ.types.push (.func s) } := by
    refine hm.push (.func s) id rfl rfl rfl rfl (fun s' j hj => ?_) (fun d j hj => Or.inl hj)
      (fun o i j hj => Or.inl hj) (fun k j hj => Or.inl hj)
    rcases List.mem_append.1 hj with h | h
    · exact Or.inl h
    · have e := List.mem_singleton.1 h
      rw [(Prod.mk.inj e).1, (Prod.mk.inj e).2]
      exact Or.inr ⟨rfl, rfl⟩
  refine ⟨σ.ntypes, σ', [.inst (.type (.func ⟨vs, vr, s.async⟩))], _, ?_, rfl, hm', rfl,
    ext_push δ _, ⟨instOnly_single _, fun rest is es => ?_⟩, ?_⟩
  · simp [defTy]
    rfl
  · simp [decCDecls, decIDecl, decDefType, pushTy, decFunc_run hps hr s.async rfl]
  · show (δ.types.push (.func s))[σ.ntypes]? = some (.func s)
    rw [← hm.size]
    exact push_self δ _

/-- **Every function type of the fragment** is encoded at an index that decodes back to
it, shared or defined. -/
theorem funcTy_sim {N : NomTable} {Γ : Ctx} {s : Sig} (hs : SigOk Γ s) {σ : Scope} {δ : DScope}
    (hm : M N Γ σ δ) : VS N Γ (funcTy s) σ δ (fun j δ' => δ'.types[j]? = some (.func s)) := by
  by_cases hit : σ.share = true ∧ ∃ j, σ.fcache.lookup s = some j
  · obtain ⟨hsh, j, hl⟩ := hit
    refine ⟨j, σ, [], δ, ?_, (List.append_nil _).symm, hm, rfl, ext_refl δ, reads_nil δ,
      hm.fc s j (DecodeEnc.mem_of_lookup hl)⟩
    simp [funcTy, hsh, hl]
  · have h : σ.share = false ∨ σ.fcache.lookup s = none := by
      cases hsh : σ.share <;> cases hl : σ.fcache.lookup s <;> simp_all
    refine vs_congr (funcTy_miss h) ?_
    unfold funcMiss
    exact vs_bind (paramTys_sim hs.1 hm) fun ps σ1 δ1 hm1 _ hps =>
      vs_bind (valTyOpt_sim (fun t ht => valTy_sim (hs.2 t ht)) hm1) fun r σ2 δ2 hm2 e2 hr =>
        defFunc_sim hm2 (hps.mono e2) hr

end DecodeNamed

end Silmaril.Wasm.Wac.Bridge
