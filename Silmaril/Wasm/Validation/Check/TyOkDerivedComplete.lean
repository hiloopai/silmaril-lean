module

public import Silmaril.Wasm.Validation.Check.TyOk

@[expose] public section

/-! # Completeness of the derived type checkers (relative to `TyOk.check`)

The core `TyOk.check` is not complete (see `Validation/Check/TyOk.lean`), so every
result here takes its completeness as a hypothesis
`hT : ∀ {k} {t : Ty k}, TyOk Δ t → TyOk.check Δ t = true`.

Where subtyping is involved we also need `Δ.Ok` and `Δ.recs = []` (for
`Sub.check_complete`) and validity of both sides. Checkers whose subtyping
premise mentions types not constrained by the judgment itself need extra
validity hypotheses:

* `CatchOk.check`: validity of the label result types and of the tag parameter
  types (`hlab`, `htag`).
* `superAtChk` / `SubTypeOkAt.check` / `RecTypeOkAt.check`: validity of the
  unrolled body of the declared supertype (`hsup`).

`SubTypeOkAt.check`/`RecTypeOkAt.check` do not call `SubOk2.check`/`GroupOk2.check`,
so no completeness hypotheses for those are needed.
-/

namespace Silmaril.Wasm.Validation

/-- Completeness hypothesis for the core `TyOk.check` in `Δ`. -/
def TyOkComplete (Δ : TypeCtx) : Prop := ∀ {k : TKind} {t : Ty k}, TyOk Δ t → TyOk.check Δ t = true

theorem TyOk.check_iff_of_complete {Δ : TypeCtx} (hT : TyOkComplete Δ) {k : TKind} {t : Ty k} :
    TyOk.check Δ t = true ↔ TyOk Δ t :=
  ⟨TyOk.check_sound, hT⟩

/-! ## Result and instruction types -/

theorem ResultOk.check_complete {Δ : TypeCtx} (hT : TyOkComplete Δ) {ts : List CValType}
    (h : ResultOk Δ ts) : ResultOk.check Δ ts = true := by
  simp only [ResultOk.check, List.all_eq_true]
  exact fun t ht => hT (h t ht)

theorem ResultOk.check_iff {Δ : TypeCtx} (hT : TyOkComplete Δ) {ts : List CValType} :
    ResultOk.check Δ ts = true ↔ ResultOk Δ ts :=
  ⟨ResultOk.check_sound, ResultOk.check_complete hT⟩

theorem ResultSub.check_iff {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {ts₁ ts₂ : List CValType} (h₁ : ResultOk Δ ts₁) (h₂ : ResultOk Δ ts₂) :
    ResultSub.check Δ ts₁ ts₂ = true ↔ ResultSub Δ ts₁ ts₂ :=
  ⟨ResultSub.check_sound, ResultSub.check_complete hΔ hr h₁ h₂⟩

theorem InstrTypeOk.check_complete {C : Context} (hT : TyOkComplete C.toTypeCtx)
    {it : InstrType} (h : InstrTypeOk C it) : InstrTypeOk.check C it = true := by
  obtain ⟨hp, hr, hi⟩ := h
  simp only [InstrTypeOk.check, Bool.and_eq_true, List.all_eq_true, Option.isSome_iff_exists]
  exact ⟨⟨ResultOk.check_complete hT hp, ResultOk.check_complete hT hr⟩, hi⟩

theorem InstrTypeOk.check_iff {C : Context} (hT : TyOkComplete C.toTypeCtx) {it : InstrType} :
    InstrTypeOk.check C it = true ↔ InstrTypeOk C it :=
  ⟨InstrTypeOk.check_sound, InstrTypeOk.check_complete hT⟩

theorem localSet_complete {C : Context} {x : Nat} {t : CValType}
    (h : C.locals[x]? = some ⟨.set, t⟩) : localSet C x = true := by
  simp [localSet, h]

theorem localSet_iff {C : Context} {x : Nat} :
    localSet C x = true ↔ ∃ t, C.locals[x]? = some ⟨.set, t⟩ :=
  ⟨localSet_sound, fun ⟨_, h⟩ => localSet_complete h⟩

/-- Completeness of `InstrTypeSub.check`, given validity of both sides. -/
theorem InstrTypeSub.check_complete {C : Context} (hΔ : C.toTypeCtx.Ok)
    (hr : C.toTypeCtx.recs = []) {it it' : InstrType} (hit : InstrTypeOk C it)
    (hit' : InstrTypeOk C it') (h : InstrTypeSub C it it') :
    InstrTypeSub.check C it it' = true := by
  obtain ⟨hp, hres, hi⟩ := h
  simp only [InstrTypeSub.check, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨ResultSub.check_complete hΔ hr hit'.1 hit.1 hp,
    ResultSub.check_complete hΔ hr hit.2.1 hit'.2.1 hres⟩, fun x hx => ?_⟩
  by_cases hm : x ∈ it.inits
  · exact .inl hm
  · obtain ⟨t, ht⟩ := hi x hx hm
    exact .inr (localSet_complete ht)

theorem InstrTypeSub.check_iff {C : Context} (hΔ : C.toTypeCtx.Ok)
    (hr : C.toTypeCtx.recs = []) {it it' : InstrType} (hit : InstrTypeOk C it)
    (hit' : InstrTypeOk C it') :
    InstrTypeSub.check C it it' = true ↔ InstrTypeSub C it it' :=
  ⟨InstrTypeSub.check_sound, InstrTypeSub.check_complete hΔ hr hit hit'⟩

/-! ## Catch clauses -/

theorem tyOk_refT_exn (Δ : TypeCtx) : TyOk Δ (Ty.refT false (.abs .exn)) :=
  .refv (.ref (.abs _))

/-- Completeness of `CatchOk.check`, given validity of the label types and of the
parameter types of the tags. -/
theorem CatchOk.check_complete {C : Context} (hΔ : C.toTypeCtx.Ok)
    (hr : C.toTypeCtx.recs = [])
    (hlab : ∀ {l : Nat} {lt : List CValType}, C.labels[l]? = some lt → ResultOk C.toTypeCtx lt)
    (htag : ∀ {x : Nat} {d : DefType} {ts : Ty (.list .val)}, C.tags[x]? = some d →
      Expand d (.func ts .nil) → ResultOk C.toTypeCtx ts.toList)
    {c : Catch} (h : CatchOk C c) : CatchOk.check C c = true := by
  cases h with
  | catch_ hx he hl hs =>
    have hts := htag hx he
    have he' := Expand.iff.1 he
    simp only [CatchOk.check, hx, Option.bind_eq_bind, Option.bind_some, he', tagParams?, hl]
    exact ResultSub.check_complete hΔ hr hts (hlab hl) hs
  | catchRef hx he hl hs =>
    have hts := htag hx he
    have he' := Expand.iff.1 he
    simp only [CatchOk.check, hx, Option.bind_eq_bind, Option.bind_some, he', tagParams?, hl]
    refine ResultSub.check_complete hΔ hr ?_ (hlab hl) hs
    intro t ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hts t ht
    · exact tyOk_refT_exn _
  | catchAll hl hs =>
    simp only [CatchOk.check, hl]
    exact ResultSub.check_complete hΔ hr (by simp [ResultOk]) (hlab hl) hs
  | catchAllRef hl hs =>
    simp only [CatchOk.check, hl]
    refine ResultSub.check_complete hΔ hr ?_ (hlab hl) hs
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact tyOk_refT_exn _

theorem CatchOk.check_iff {C : Context} (hΔ : C.toTypeCtx.Ok)
    (hr : C.toTypeCtx.recs = [])
    (hlab : ∀ {l : Nat} {lt : List CValType}, C.labels[l]? = some lt → ResultOk C.toTypeCtx lt)
    (htag : ∀ {x : Nat} {d : DefType} {ts : Ty (.list .val)}, C.tags[x]? = some d →
      Expand d (.func ts .nil) → ResultOk C.toTypeCtx ts.toList)
    {c : Catch} : CatchOk.check C c = true ↔ CatchOk C c :=
  ⟨CatchOk.check_sound, CatchOk.check_complete hΔ hr hlab htag⟩

/-! ## Tag, global, table and extern types -/

theorem expandsToTag_complete {d : DefType} {ps : Ty (.list .val)}
    (h : Expand d (.func ps .nil)) : expandsToTag d = true := by
  simp [expandsToTag, Expand.iff.1 h]

theorem expandsToTag_iff {d : DefType} : expandsToTag d = true ↔ ∃ ps, Expand d (.func ps .nil) :=
  ⟨expandsToTag_sound, fun ⟨_, h⟩ => expandsToTag_complete h⟩

theorem expandsToFunc_complete {d : DefType} {ps rs : Ty (.list .val)}
    (h : Expand d (.func ps rs)) : expandsToFunc d = true := by
  simp [expandsToFunc, Expand.iff.1 h]

theorem expandsToFunc_iff {d : DefType} :
    expandsToFunc d = true ↔ ∃ ps rs, Expand d (.func ps rs) :=
  ⟨expandsToFunc_sound, fun ⟨_, _, h⟩ => expandsToFunc_complete h⟩

theorem TagTypeOk.check_complete {Δ : TypeCtx} (hT : TyOkComplete Δ) {d : DefType}
    (h : TagTypeOk Δ d) : TagTypeOk.check Δ d = true := by
  obtain ⟨hd, _, he⟩ := h
  simp [TagTypeOk.check, hT hd, expandsToTag_complete he]

theorem TagTypeOk.check_iff {Δ : TypeCtx} (hT : TyOkComplete Δ) {d : DefType} :
    TagTypeOk.check Δ d = true ↔ TagTypeOk Δ d :=
  ⟨TagTypeOk.check_sound, TagTypeOk.check_complete hT⟩

theorem GlobalTypeOk.check_complete {Δ : TypeCtx} (hT : TyOkComplete Δ) {g : CGlobalType}
    (h : GlobalTypeOk Δ g) : GlobalTypeOk.check Δ g = true := hT h

theorem GlobalTypeOk.check_iff {Δ : TypeCtx} (hT : TyOkComplete Δ) {g : CGlobalType} :
    GlobalTypeOk.check Δ g = true ↔ GlobalTypeOk Δ g :=
  ⟨GlobalTypeOk.check_sound, GlobalTypeOk.check_complete hT⟩

theorem MemTypeOk.check_complete {m : MemoryType} (h : MemTypeOk m) : MemTypeOk.check m = true :=
  MemTypeOk.check_iff.2 h

theorem TableTypeOk.check_complete {Δ : TypeCtx} (hT : TyOkComplete Δ) {t : CTableType}
    (h : TableTypeOk Δ t) : TableTypeOk.check Δ t = true := by
  simp only [TableTypeOk.check, Bool.and_eq_true, Limits.check_eq_true]
  exact ⟨h.1, hT h.2⟩

theorem TableTypeOk.check_iff {Δ : TypeCtx} (hT : TyOkComplete Δ) {t : CTableType} :
    TableTypeOk.check Δ t = true ↔ TableTypeOk Δ t :=
  ⟨TableTypeOk.check_sound, TableTypeOk.check_complete hT⟩

theorem ExternTypeOk.check_complete {Δ : TypeCtx} (hT : TyOkComplete Δ) {e : CExternType}
    (h : ExternTypeOk Δ e) : ExternTypeOk.check Δ e = true := by
  cases h with
  | tag h => exact TagTypeOk.check_complete hT h
  | global h => exact GlobalTypeOk.check_complete hT h
  | mem h => exact MemTypeOk.check_complete h
  | table h => exact TableTypeOk.check_complete hT h
  | func h he =>
    simp only [ExternTypeOk.check, Bool.and_eq_true]
    exact ⟨hT h, expandsToFunc_complete he⟩

theorem ExternTypeOk.check_iff {Δ : TypeCtx} (hT : TyOkComplete Δ) {e : CExternType} :
    ExternTypeOk.check Δ e = true ↔ ExternTypeOk Δ e :=
  ⟨ExternTypeOk.check_sound, ExternTypeOk.check_complete hT⟩

/-! ## Module-level sub types and recursive groups -/

/-- Validity of the unrolled bodies of the (non-final) type definitions of `C`:
the extra hypothesis `superAtChk` needs (the judgment `SubTypeOkAt` itself does
not constrain the supertype's body). -/
def SuperBodiesOk (C : Context) : Prop :=
  ∀ {x : Nat} {d : DefType} {sups' : Ty (.list .use)} {ct' : CCompType},
    C.types[x]? = some d → unrolldt d = some (.sub false sups' ct') → TyOk C.toTypeCtx ct'

theorem superAtChk_complete {C : Context} (hΔ : C.toTypeCtx.Ok) (hr : C.toTypeCtx.recs = [])
    (hsup : SuperBodiesOk C) {x : TypeIdx} {ct : CompositeType} {d : DefType}
    {sups' : Ty (.list .use)} {ct' : CCompType}
    (hd : C.types[x.toNat]? = some d) (hun : unrolldt d = some (.sub false sups' ct'))
    (hct : TyOk C.toTypeCtx (C.closeComp ct)) (hsub : Sub C.toTypeCtx (C.closeComp ct) ct') :
    superAtChk C x ct = true := by
  simp only [superAtChk, hd, hun]
  exact Sub.check_complete hΔ hr hsub hct (hsup hd hun)

theorem SubTypeOkAt.check_complete {C : Context} (hT : TyOkComplete C.toTypeCtx)
    (hΔ : C.toTypeCtx.Ok) (hr : C.toTypeCtx.recs = []) (hsup : SuperBodiesOk C)
    {st : SubType} {x₀ : Nat} (h : SubTypeOkAt C st x₀) : SubTypeOkAt.check C st x₀ = true := by
  cases h with
  | noSuper hct => exact hT hct
  | oneSuper hx hd hun hct hsub =>
    simp only [SubTypeOkAt.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hx, hT hct⟩, superAtChk_complete hΔ hr hsup hd hun hct hsub⟩

theorem SubTypeOkAt.check_iff {C : Context} (hT : TyOkComplete C.toTypeCtx)
    (hΔ : C.toTypeCtx.Ok) (hr : C.toTypeCtx.recs = []) (hsup : SuperBodiesOk C)
    {st : SubType} {x₀ : Nat} : SubTypeOkAt.check C st x₀ = true ↔ SubTypeOkAt C st x₀ :=
  ⟨SubTypeOkAt.check_sound, SubTypeOkAt.check_complete hT hΔ hr hsup⟩

theorem RecTypeOkAt.check_complete {C : Context} (hT : TyOkComplete C.toTypeCtx)
    (hΔ : C.toTypeCtx.Ok) (hr : C.toTypeCtx.recs = []) (hsup : SuperBodiesOk C) :
    ∀ {sts : List SubType} {x : Nat}, RecTypeOkAt C sts x → RecTypeOkAt.check C sts x = true
  | [], _, _ => rfl
  | _ :: _, _, .cons h hs => by
    simp only [RecTypeOkAt.check, Bool.and_eq_true]
    exact ⟨SubTypeOkAt.check_complete hT hΔ hr hsup h, RecTypeOkAt.check_complete hT hΔ hr hsup hs⟩

theorem RecTypeOkAt.check_iff {C : Context} (hT : TyOkComplete C.toTypeCtx)
    (hΔ : C.toTypeCtx.Ok) (hr : C.toTypeCtx.recs = []) (hsup : SuperBodiesOk C)
    {sts : List SubType} {x : Nat} : RecTypeOkAt.check C sts x = true ↔ RecTypeOkAt C sts x :=
  ⟨RecTypeOkAt.check_sound, RecTypeOkAt.check_complete hT hΔ hr hsup⟩

end Silmaril.Wasm.Validation
