module

public import Silmaril.Wasm.Validation.Subtyping.Check
public import Silmaril.Wasm.Validation.Subtyping.CheckRecs
public import Silmaril.Wasm.Validation.TypeOk
public import Silmaril.Wasm.Validation.Instructions
public import Silmaril.Wasm.Validation.Examples

@[expose] public section

/-! # A computable checker for type-level validation (§2.1)

Boolean checkers, with **soundness** proofs, for the type-validity judgments:

* `TyOk.check`, `SubOk2.check`, `GroupOk2.check` for the mutual core
  `TyOk`/`SubOk2`/`GroupOk2` (`Validation/Subtyping.lean`). All three are one
  structurally recursive function `tyChk` with a mode flag (`false`: `TyOk`;
  `true`: `Subtype_ok2`/`Rectype_ok2` on sub types and sequences of sub types,
  where the sequence position is the running index `i`).
* derived checkers: `ResultOk`, `ResultSub`, `InstrTypeOk`, `InstrTypeSub`,
  `BlockTypeOk` (`blockType?`, sound and complete up to `TyOk.check`),
  `CatchOk`, `TagTypeOk`, `GlobalTypeOk`, `MemTypeOk`, `TableTypeOk`,
  `ExternTypeOk`, `SubTypeOkAt`, `RecTypeOkAt`.

**`RECS`.** The declared-supertype premise of `Subtype_ok2` is discharged under
`C, RECS subtype*` (`Deftype_ok`), where `Heaptype_sub/rec-*` apply. `superChk`
therefore uses the `REC`-aware `Sub.checkRWith` (`Subtyping/CheckRecs.lean`) with
the membership oracle `recOracle Δ` (accept exactly the `_DEF` supertypes of
`RECS` entries). That oracle is sound whenever those supertypes are valid
(`RecSupOk Δ`); inside `Deftype_ok` this is established by the mode-`true`
traversal of the group itself, which checks every declared supertype.
The top-level `SubOk2.check`/`GroupOk2.check` first check `RecSupOk` of the
ambient `RECS` (`recSupChk`), so their soundness is unconditional.

**Completeness** is proved in `Check/TyOkComplete.lean` (`TyOk.check_complete`).
-/

namespace Silmaril.Wasm.Validation

/-! ## The core checker -/

/-- The `REC`-subtyping oracle: the `_DEF` supertypes of `RECS` entries. -/
def recOracle (Δ : TypeCtx) (d : DefType) : Bool :=
  Δ.recs.any fun st => decide ((.dt d : CTypeUse) ∈ st.supers)

/-- The declared-supertype premise of `Subtype_ok2`. -/
def superChk (Δ : TypeCtx) (u : CTypeUse) (ct : CCompType) : Bool :=
  match Δ.unrollUse u with
  | some (.sub false _ ct') => Sub.checkRWith (recOracle Δ) Δ ct ct'
  | _ => false

/-- The checker. Mode `m = false` decides `TyOk Δ t` (the index is ignored);
mode `m = true` decides `SubOk2 Δ st i` on a sub type and `GroupOk2 Δ (.group sts) i`
on a sequence of sub types. -/
def tyChk (Δ : TypeCtx) (m : Bool) : {k : TKind} → Ty k → Nat → Bool
  | _, .nil, _ => true
  | _, .cons a l, n =>
    if m then tyChk Δ true a n && tyChk Δ true l (n + 1)
    else tyChk Δ false a 0 && tyChk Δ false l 0
  | _, .idx x, _ => (Δ.types[x]?).isSome
  | _, .recv i, _ => (Δ.recs[i]?).isSome
  | _, .dt d, _ => tyChk Δ false d 0
  | _, .defn (.group subs) i, _ =>
    tyChk (Δ.withRecs subs.toList) true subs 0 && decide (i < subs.length)
  | _, .abs _, _ => true
  | _, .bot, _ => true
  | _, .use u, _ => tyChk Δ false u 0
  | _, .ref _ h, _ => tyChk Δ false h 0
  | _, .num _, _ => true
  | _, .vec _, _ => true
  | _, .refv r, _ => tyChk Δ false r 0
  | _, .botv, _ => true
  | _, .val t, _ => tyChk Δ false t 0
  | _, .pack _, _ => true
  | _, .field _ s, _ => tyChk Δ false s 0
  | _, .struct fs, _ => tyChk Δ false fs 0
  | _, .array f, _ => tyChk Δ false f 0
  | _, .func ps rs, _ => tyChk Δ false ps 0 && tyChk Δ false rs 0
  | _, .sub _ .nil ct, _ => m && tyChk Δ false ct 0
  | _, .sub _ (.cons u .nil) ct, n =>
    m && tyChk Δ false u 0 && before u n && tyChk Δ false ct 0 && superChk Δ u ct
  | _, .sub _ (.cons _ (.cons _ _)) _, _ => false
  | _, .group _, _ => false

/-- `TyOk` checker. -/
def TyOk.check (Δ : TypeCtx) {k : TKind} (t : Ty k) : Bool := tyChk Δ false t 0

/-- Every declared supertype of a `RECS` entry passes `TyOk.check`. -/
def recSupChk (Δ : TypeCtx) : Bool :=
  Δ.recs.all fun st => st.supers.all fun u => tyChk Δ false u 0

/-- `Subtype_ok2` checker. -/
def SubOk2.check (Δ : TypeCtx) (st : CSubType) (i : Nat) : Bool :=
  recSupChk Δ && tyChk Δ true st i

/-- `Rectype_ok2` checker. -/
def GroupOk2.check (Δ : TypeCtx) : CRecType → Nat → Bool
  | .group subs, i => recSupChk Δ && tyChk Δ true subs i

/-- What mode `true` establishes, by the shape of the term. -/
def GSpec (Δ : TypeCtx) : {k : TKind} → Ty k → Nat → Prop
  | _, .sub fin sups ct, n => SubOk2 Δ (.sub fin sups ct) n
  | _, .cons a l, n => GSpec Δ a n ∧ GSpec Δ l (n + 1)
  | _, _, _ => True

/-- What mode `true` establishes without any hypothesis: declared supertypes are valid. -/
def GPre (Δ : TypeCtx) : {k : TKind} → Ty k → Prop
  | _, .sub _ sups _ => ∀ u ∈ sups.toList, TyOk Δ u
  | _, .cons a l => GPre Δ a ∧ GPre Δ l
  | _, _ => True

/-- The `_DEF` supertypes of the `RECS` entries are valid (soundness of `recOracle`). -/
def RecSupOk (Δ : TypeCtx) : Prop := ∀ d, recOracle Δ d = true → TyOk Δ d

theorem GPre.mem {Δ : TypeCtx} : ∀ {subs : Ty (.list .sub)}, GPre Δ subs →
    ∀ st ∈ subs.toList, ∀ u ∈ st.supers, TyOk Δ u
  | .nil, _, st, hst, _, _ => by simp at hst
  | .cons (.sub fin sups ct) l, h, st, hst, u, hu => by
    simp only [Ty.toList_cons, List.mem_cons] at hst
    rcases hst with rfl | hst
    · exact h.1 u (by simpa [Ty.supers] using hu)
    · exact GPre.mem h.2 st hst u hu

theorem RecSupOk.of_all {Δ : TypeCtx} (h : ∀ st ∈ Δ.recs, ∀ u ∈ st.supers, TyOk Δ u) :
    RecSupOk Δ := by
  intro d hd
  simp only [recOracle, List.any_eq_true, decide_eq_true_eq] at hd
  obtain ⟨st, hst, hm⟩ := hd
  cases h st hst _ hm with
  | dt h => exact h

theorem GSpec.group {Δ : TypeCtx} : ∀ {subs : Ty (.list .sub)} {n : Nat},
    GSpec Δ subs n → GroupOk2 Δ (.group subs) n
  | .nil, _, _ => .nil
  | .cons (.sub fin sups ct) l, _, h => .cons h.1 (GSpec.group h.2)

theorem superChk_sound {Δ : TypeCtx} (hO : RecSupOk Δ) {u : CTypeUse} {ct : CCompType}
    (h : superChk Δ u ct = true) :
    ∃ sups' ct', Δ.unrollUse u = some (.sub false sups' ct') ∧ Sub Δ ct ct' := by
  unfold superChk at h
  split at h
  · rename_i sups' ct' heq
    exact ⟨_, _, heq, Sub.checkRWith_sound hO h⟩
  · simp at h

/-- Leaf cases of `tyChk_sound` (no mode-`true` content). -/
theorem tyChk_sound_leaf {Δ : TypeCtx} {m : Bool} {k : TKind} {t : Ty k} {n : Nat}
    (ht : m = false → TyOk Δ t) (hp : GPre Δ t = True) (hs : GSpec Δ t n = True) :
    (m = false → TyOk Δ t) ∧ (m = true → GPre Δ t) ∧ (m = true → RecSupOk Δ → GSpec Δ t n) :=
  ⟨ht, fun _ => hp ▸ trivial, fun _ _ => hs ▸ trivial⟩

theorem tyChk_sound : ∀ (Δ : TypeCtx) (m : Bool) {k : TKind} (t : Ty k) (n : Nat),
    tyChk Δ m t n = true →
      (m = false → TyOk Δ t) ∧ (m = true → GPre Δ t) ∧ (m = true → RecSupOk Δ → GSpec Δ t n)
  | Δ, m, _, .nil, n, _ => tyChk_sound_leaf (fun _ => .nil) rfl rfl
  | Δ, m, _, .cons a l, n, h => by
    cases m with
    | false =>
      simp only [tyChk, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
      exact ⟨fun _ => .cons ((tyChk_sound Δ false a 0 h.1).1 rfl)
        ((tyChk_sound Δ false l 0 h.2).1 rfl), fun h => by simp at h, fun h => by simp at h⟩
    | true =>
      simp only [tyChk, ↓reduceIte, Bool.and_eq_true] at h
      have ha := tyChk_sound Δ true a n h.1
      have hl := tyChk_sound Δ true l (n + 1) h.2
      exact ⟨fun h => by simp at h, fun _ => ⟨ha.2.1 rfl, hl.2.1 rfl⟩,
        fun _ hO => ⟨ha.2.2 rfl hO, hl.2.2 rfl hO⟩⟩
  | Δ, m, _, .idx x, n, h => by
    simp only [tyChk, Option.isSome_iff_exists] at h
    obtain ⟨d, hd⟩ := h
    exact tyChk_sound_leaf (fun _ => .idx hd) rfl rfl
  | Δ, m, _, .recv i, n, h => by
    simp only [tyChk, Option.isSome_iff_exists] at h
    obtain ⟨d, hd⟩ := h
    exact tyChk_sound_leaf (fun _ => .recv hd) rfl rfl
  | Δ, m, _, .dt d, n, h => by
    simp only [tyChk] at h
    exact tyChk_sound_leaf (fun _ => .dt ((tyChk_sound Δ false d 0 h).1 rfl)) rfl rfl
  | Δ, m, _, .defn (.group subs) i, n, h => by
    simp only [tyChk, Bool.and_eq_true, decide_eq_true_eq] at h
    have hs := tyChk_sound _ true subs 0 h.1
    have hO : RecSupOk (Δ.withRecs subs.toList) :=
      RecSupOk.of_all fun st hst u hu => GPre.mem (hs.2.1 rfl) st hst u hu
    exact tyChk_sound_leaf (fun _ => .defn (GSpec.group (hs.2.2 rfl hO)) h.2) rfl rfl
  | Δ, m, _, .abs a, n, _ => tyChk_sound_leaf (fun _ => .abs a) rfl rfl
  | Δ, m, _, .bot, n, _ => tyChk_sound_leaf (fun _ => .bot) rfl rfl
  | Δ, m, _, .use u, n, h => by
    simp only [tyChk] at h
    exact tyChk_sound_leaf (fun _ => .use ((tyChk_sound Δ false u 0 h).1 rfl)) rfl rfl
  | Δ, m, _, .ref _ hh, n, h => by
    simp only [tyChk] at h
    exact tyChk_sound_leaf (fun _ => .ref ((tyChk_sound Δ false hh 0 h).1 rfl)) rfl rfl
  | Δ, m, _, .num t, n, _ => tyChk_sound_leaf (fun _ => .num t) rfl rfl
  | Δ, m, _, .vec t, n, _ => tyChk_sound_leaf (fun _ => .vec t) rfl rfl
  | Δ, m, _, .refv r, n, h => by
    simp only [tyChk] at h
    exact tyChk_sound_leaf (fun _ => .refv ((tyChk_sound Δ false r 0 h).1 rfl)) rfl rfl
  | Δ, m, _, .botv, n, _ => tyChk_sound_leaf (fun _ => .botv) rfl rfl
  | Δ, m, _, .val t, n, h => by
    simp only [tyChk] at h
    exact tyChk_sound_leaf (fun _ => .val ((tyChk_sound Δ false t 0 h).1 rfl)) rfl rfl
  | Δ, m, _, .pack p, n, _ => tyChk_sound_leaf (fun _ => .pack p) rfl rfl
  | Δ, m, _, .field _ s, n, h => by
    simp only [tyChk] at h
    exact tyChk_sound_leaf (fun _ => .field ((tyChk_sound Δ false s 0 h).1 rfl)) rfl rfl
  | Δ, m, _, .struct fs, n, h => by
    simp only [tyChk] at h
    exact tyChk_sound_leaf (fun _ => .struct ((tyChk_sound Δ false fs 0 h).1 rfl)) rfl rfl
  | Δ, m, _, .array f, n, h => by
    simp only [tyChk] at h
    exact tyChk_sound_leaf (fun _ => .array ((tyChk_sound Δ false f 0 h).1 rfl)) rfl rfl
  | Δ, m, _, .func ps rs, n, h => by
    simp only [tyChk, Bool.and_eq_true] at h
    exact tyChk_sound_leaf (fun _ => .func ((tyChk_sound Δ false ps 0 h.1).1 rfl)
      ((tyChk_sound Δ false rs 0 h.2).1 rfl)) rfl rfl
  | Δ, m, _, .sub fin .nil ct, n, h => by
    simp only [tyChk, Bool.and_eq_true] at h
    refine ⟨fun hm => by simp [hm] at h, fun _ => by simp [GPre], fun _ _ => ?_⟩
    exact .noSuper ((tyChk_sound Δ false ct 0 h.2).1 rfl)
  | Δ, m, _, .sub fin (.cons u .nil) ct, n, h => by
    simp only [tyChk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hm, hu⟩, hb⟩, hct⟩, hs⟩ := h
    have hu' := (tyChk_sound Δ false u 0 hu).1 rfl
    refine ⟨fun h => by simp [h] at hm, fun _ => ?_, fun _ hO => ?_⟩
    · intro w hw
      simp only [Ty.toList_cons, Ty.toList_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      exact hw ▸ hu'
    · obtain ⟨sups', ct', hun, hsub⟩ := superChk_sound hO hs
      exact .oneSuper hu' hb hun ((tyChk_sound Δ false ct 0 hct).1 rfl) hsub
  | Δ, m, _, .sub _ (.cons _ (.cons _ _)) _, n, h => by simp [tyChk] at h
  | Δ, m, _, .group _, n, h => by simp [tyChk] at h

/-- Soundness of `recSupChk`. -/
theorem recSupChk_sound {Δ : TypeCtx} (h : recSupChk Δ = true) : RecSupOk Δ :=
  RecSupOk.of_all fun st hst u hu => by
    simp only [recSupChk, List.all_eq_true] at h
    exact (tyChk_sound Δ false u 0 (h st hst u hu)).1 rfl

/-- **Soundness** of the `TyOk` checker. -/
theorem TyOk.check_sound {Δ : TypeCtx} {k : TKind} {t : Ty k} (h : TyOk.check Δ t = true) :
    TyOk Δ t :=
  (tyChk_sound Δ false t 0 h).1 rfl

/-- **Soundness** of the `Subtype_ok2` checker. -/
theorem SubOk2.check_sound {Δ : TypeCtx} {st : CSubType} {i : Nat}
    (h : SubOk2.check Δ st i = true) : SubOk2 Δ st i := by
  simp only [SubOk2.check, Bool.and_eq_true] at h
  have := (tyChk_sound Δ true st i h.2).2.2 rfl (recSupChk_sound h.1)
  cases st with
  | sub fin sups ct => exact this

/-- **Soundness** of the `Rectype_ok2` checker. -/
theorem GroupOk2.check_sound {Δ : TypeCtx} {rt : CRecType} {i : Nat}
    (h : GroupOk2.check Δ rt i = true) : GroupOk2 Δ rt i := by
  cases rt with
  | group subs =>
    simp only [GroupOk2.check, Bool.and_eq_true] at h
    exact GSpec.group ((tyChk_sound Δ true subs i h.2).2.2 rfl (recSupChk_sound h.1))

/-! ## Result and instruction types -/

/-- `Resulttype_ok` checker. -/
def ResultOk.check (Δ : TypeCtx) (ts : List CValType) : Bool := ts.all (TyOk.check Δ)

theorem ResultOk.check_sound {Δ : TypeCtx} {ts : List CValType}
    (h : ResultOk.check Δ ts = true) : ResultOk Δ ts := by
  simp only [ResultOk.check, List.all_eq_true] at h
  exact fun t ht => TyOk.check_sound (h t ht)

/-- `Resulttype_sub` checker. -/
def ResultSub.check (Δ : TypeCtx) (ts₁ ts₂ : List CValType) : Bool :=
  Sub.check Δ (Ty.ofList ts₁) (Ty.ofList ts₂)

theorem ResultSub.check_sound {Δ : TypeCtx} {ts₁ ts₂ : List CValType}
    (h : ResultSub.check Δ ts₁ ts₂ = true) : ResultSub Δ ts₁ ts₂ :=
  (ResultSub.iff_sub Δ ts₁ ts₂).2 (Sub.check_sound h)

theorem ResultSub.check_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {ts₁ ts₂ : List CValType} (h₁ : ResultOk Δ ts₁) (h₂ : ResultOk Δ ts₂)
    (h : ResultSub Δ ts₁ ts₂) : ResultSub.check Δ ts₁ ts₂ = true :=
  Sub.check_complete hΔ hr ((ResultSub.iff_sub Δ ts₁ ts₂).1 h)
    (TyOk.of_forall (by simpa [ResultOk] using h₁)) (TyOk.of_forall (by simpa [ResultOk] using h₂))

/-- `Instrtype_ok` checker. -/
def InstrTypeOk.check (C : Context) (it : InstrType) : Bool :=
  ResultOk.check C.toTypeCtx it.params && ResultOk.check C.toTypeCtx it.results &&
    it.inits.all fun x => (C.locals[x]?).isSome

theorem InstrTypeOk.check_sound {C : Context} {it : InstrType}
    (h : InstrTypeOk.check C it = true) : InstrTypeOk C it := by
  simp only [InstrTypeOk.check, Bool.and_eq_true, List.all_eq_true,
    Option.isSome_iff_exists] at h
  exact ⟨ResultOk.check_sound h.1.1, ResultOk.check_sound h.1.2, h.2⟩

/-- Whether local `x` is set in `C`. -/
def localSet (C : Context) (x : Nat) : Bool :=
  match C.locals[x]? with
  | some ⟨.set, _⟩ => true
  | _ => false

theorem localSet_sound {C : Context} {x : Nat} (h : localSet C x = true) :
    ∃ t, C.locals[x]? = some ⟨.set, t⟩ := by
  unfold localSet at h
  split at h
  · rename_i t heq; exact ⟨t, heq⟩
  · simp at h

/-- `Instrtype_sub` checker. -/
def InstrTypeSub.check (C : Context) (it it' : InstrType) : Bool :=
  ResultSub.check C.toTypeCtx it'.params it.params &&
    ResultSub.check C.toTypeCtx it.results it'.results &&
    it'.inits.all fun x => decide (x ∈ it.inits) || localSet C x

theorem InstrTypeSub.check_sound {C : Context} {it it' : InstrType}
    (h : InstrTypeSub.check C it it' = true) : InstrTypeSub C it it' := by
  simp only [InstrTypeSub.check, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  refine ⟨ResultSub.check_sound h.1.1, ResultSub.check_sound h.1.2, fun x hx hn => ?_⟩
  rcases h.2 x hx with h' | h'
  · exact absurd h' hn
  · exact localSet_sound h'

/-! ## Block types and catch clauses -/

/-- `Blocktype_ok` as a function. -/
def blockType? (C : Context) : BlockType → Option (List CValType × List CValType)
  | .empty => some ([], [])
  | .value t => if TyOk.check C.toTypeCtx (C.closeVal t) then some ([], [C.closeVal t]) else none
  | .typeIdx x =>
    match C.type? x >>= DefType.expand? with
    | some (.func ps rs) => some (ps.toList, rs.toList)
    | _ => none

theorem blockType?_sound {C : Context} {bt : BlockType} {ps rs : List CValType}
    (h : blockType? C bt = some (ps, rs)) : BlockTypeOk C bt ps rs := by
  cases bt with
  | empty =>
    simp only [blockType?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .empty
  | value t =>
    simp only [blockType?] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .value (TyOk.check_sound hc)
    · simp at h
  | typeIdx x =>
    simp only [blockType?] at h
    split at h
    · rename_i ps' rs' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases hd : C.type? x with
      | none => simp [hd] at heq
      | some d =>
        simp only [hd, Option.bind_eq_bind, Option.bind_some] at heq
        exact .typeIdx hd (Expand.iff.2 heq)
    · simp at h

/-- Completeness of `blockType?`, up to the completeness of `TyOk.check` on the
(closed) value type of a `.value` block type (see the module doc). -/
theorem blockType?_complete {C : Context} {bt : BlockType} {ps rs : List CValType}
    (h : BlockTypeOk C bt ps rs)
    (hv : ∀ t, bt = .value t → TyOk.check C.toTypeCtx (C.closeVal t) = true) :
    blockType? C bt = some (ps, rs) := by
  cases h with
  | empty => rfl
  | value _ => simp [blockType?, hv _ rfl]
  | typeIdx hd he =>
    have := Expand.iff.1 he
    simp [blockType?, hd, this]

/-- The parameters of a tag's function type (no results). -/
def tagParams? : Option CCompType → Option (Ty (.list .val))
  | some (.func ts .nil) => some ts
  | _ => none

theorem tagParams?_sound {o : Option CCompType} {ts : Ty (.list .val)}
    (h : tagParams? o = some ts) : o = some (.func ts .nil) := by
  unfold tagParams? at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp at h

/-- `Catch_ok` checker. -/
def CatchOk.check (C : Context) : Catch → Bool
  | .catch_ x l =>
    match tagParams? (C.tags[x.toNat]? >>= DefType.expand?), C.labels[l.toNat]? with
    | some ts, some lt => ResultSub.check C.toTypeCtx ts.toList lt
    | _, _ => false
  | .catchRef x l =>
    match tagParams? (C.tags[x.toNat]? >>= DefType.expand?), C.labels[l.toNat]? with
    | some ts, some lt =>
      ResultSub.check C.toTypeCtx (ts.toList ++ [.refT false (.abs .exn)]) lt
    | _, _ => false
  | .catchAll l =>
    match C.labels[l.toNat]? with
    | some lt => ResultSub.check C.toTypeCtx [] lt
    | none => false
  | .catchAllRef l =>
    match C.labels[l.toNat]? with
    | some lt => ResultSub.check C.toTypeCtx [.refT false (.abs .exn)] lt
    | none => false

theorem tag_expand {C : Context} {x : TagIdx} {ct : CCompType}
    (h : (C.tags[x.toNat]? >>= DefType.expand?) = some ct) :
    ∃ d, C.tags[x.toNat]? = some d ∧ Expand d ct := by
  cases hd : C.tags[x.toNat]? with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
    exact ⟨d, rfl, Expand.iff.2 h⟩

theorem CatchOk.check_sound {C : Context} {c : Catch} (h : CatchOk.check C c = true) :
    CatchOk C c := by
  cases c with
  | catch_ x l =>
    simp only [CatchOk.check] at h
    split at h
    · rename_i ts lt he hl
      obtain ⟨d, hd, hx⟩ := tag_expand (tagParams?_sound he)
      exact .catch_ hd hx hl (ResultSub.check_sound h)
    · simp at h
  | catchRef x l =>
    simp only [CatchOk.check] at h
    split at h
    · rename_i ts lt he hl
      obtain ⟨d, hd, hx⟩ := tag_expand (tagParams?_sound he)
      exact .catchRef hd hx hl (ResultSub.check_sound h)
    · simp at h
  | catchAll l =>
    simp only [CatchOk.check] at h
    split at h
    · rename_i lt hl
      exact .catchAll hl (ResultSub.check_sound h)
    · simp at h
  | catchAllRef l =>
    simp only [CatchOk.check] at h
    split at h
    · rename_i lt hl
      exact .catchAllRef hl (ResultSub.check_sound h)
    · simp at h

/-! ## Tag, global, memory, table and extern types -/

/-- Whether a defined type expands to a function type with no results. -/
def expandsToTag (d : DefType) : Bool :=
  match d.expand? with
  | some (.func _ .nil) => true
  | _ => false

/-- Whether a defined type expands to a function type. -/
def expandsToFunc (d : DefType) : Bool :=
  match d.expand? with
  | some (.func _ _) => true
  | _ => false

theorem expandsToTag_sound {d : DefType} (h : expandsToTag d = true) :
    ∃ ps, Expand d (.func ps .nil) := by
  unfold expandsToTag at h
  split at h
  · rename_i ps heq; exact ⟨ps, Expand.iff.2 heq⟩
  · simp at h

theorem expandsToFunc_sound {d : DefType} (h : expandsToFunc d = true) :
    ∃ ps rs, Expand d (.func ps rs) := by
  unfold expandsToFunc at h
  split at h
  · rename_i ps rs heq; exact ⟨ps, rs, Expand.iff.2 heq⟩
  · simp at h

/-- `Tagtype_ok` checker. -/
def TagTypeOk.check (Δ : TypeCtx) (d : DefType) : Bool := TyOk.check Δ d && expandsToTag d

theorem TagTypeOk.check_sound {Δ : TypeCtx} {d : DefType} (h : TagTypeOk.check Δ d = true) :
    TagTypeOk Δ d := by
  simp only [TagTypeOk.check, Bool.and_eq_true] at h
  exact ⟨TyOk.check_sound h.1, expandsToTag_sound h.2⟩

/-- `Globaltype_ok` checker. -/
def GlobalTypeOk.check (Δ : TypeCtx) (g : CGlobalType) : Bool := TyOk.check Δ g.type

theorem GlobalTypeOk.check_sound {Δ : TypeCtx} {g : CGlobalType}
    (h : GlobalTypeOk.check Δ g = true) : GlobalTypeOk Δ g := TyOk.check_sound h

/-- `Memtype_ok` checker. -/
def MemTypeOk.check (m : MemoryType) : Bool := decide m.Valid

theorem MemTypeOk.check_iff {m : MemoryType} : MemTypeOk.check m = true ↔ MemTypeOk m := by
  simp [MemTypeOk.check, MemTypeOk]

theorem MemTypeOk.check_sound {m : MemoryType} (h : MemTypeOk.check m = true) : MemTypeOk m :=
  MemTypeOk.check_iff.1 h

/-- `Tabletype_ok` checker. -/
def TableTypeOk.check (Δ : TypeCtx) (t : CTableType) : Bool :=
  t.limits.check (2 ^ t.address.width - 1) && TyOk.check Δ t.element

theorem TableTypeOk.check_sound {Δ : TypeCtx} {t : CTableType}
    (h : TableTypeOk.check Δ t = true) : TableTypeOk Δ t := by
  simp only [TableTypeOk.check, Bool.and_eq_true, Limits.check_eq_true] at h
  exact ⟨h.1, TyOk.check_sound h.2⟩

/-- `Externtype_ok` checker. -/
def ExternTypeOk.check (Δ : TypeCtx) : CExternType → Bool
  | .tag d => TagTypeOk.check Δ d
  | .global g => GlobalTypeOk.check Δ g
  | .mem m => MemTypeOk.check m
  | .table t => TableTypeOk.check Δ t
  | .func d => TyOk.check Δ d && expandsToFunc d

theorem ExternTypeOk.check_sound {Δ : TypeCtx} {e : CExternType}
    (h : ExternTypeOk.check Δ e = true) : ExternTypeOk Δ e := by
  cases e with
  | tag d => exact .tag (TagTypeOk.check_sound h)
  | global g => exact .global (GlobalTypeOk.check_sound h)
  | mem m => exact .mem (MemTypeOk.check_sound h)
  | table t => exact .table (TableTypeOk.check_sound h)
  | func d =>
    simp only [ExternTypeOk.check, Bool.and_eq_true] at h
    obtain ⟨ps, rs, he⟩ := expandsToFunc_sound h.2
    exact .func (TyOk.check_sound h.1) he

/-! ## Module-level sub types and recursive groups -/

/-- The declared-supertype premise of `Subtype_ok` (`OK(x)`). -/
def superAtChk (C : Context) (x : TypeIdx) (ct : CompositeType) : Bool :=
  match C.types[x.toNat]? with
  | some d =>
    match unrolldt d with
    | some (.sub false _ ct') => Sub.check C.toTypeCtx (C.closeComp ct) ct'
    | _ => false
  | none => false

/-- `Subtype_ok: OK(x₀)` checker. -/
def SubTypeOkAt.check (C : Context) (st : SubType) (x₀ : Nat) : Bool :=
  match st.supertypes with
  | [] => TyOk.check C.toTypeCtx (C.closeComp st.body)
  | [x] => decide (x.toNat < x₀) && TyOk.check C.toTypeCtx (C.closeComp st.body) &&
      superAtChk C x st.body
  | _ :: _ :: _ => false

theorem SubTypeOkAt.check_sound {C : Context} {st : SubType} {x₀ : Nat}
    (h : SubTypeOkAt.check C st x₀ = true) : SubTypeOkAt C st x₀ := by
  obtain ⟨fin, sups, ct⟩ := st
  match sups, h with
  | [], h => exact .noSuper (TyOk.check_sound h)
  | [x], h =>
    simp only [SubTypeOkAt.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hct⟩, hs⟩ := h
    unfold superAtChk at hs
    split at hs
    · rename_i d hd
      split at hs
      · rename_i sups' ct' hun
        exact .oneSuper hx hd hun (TyOk.check_sound hct) (Sub.check_sound hs)
      · simp at hs
    · simp at hs
  | _ :: _ :: _, h => simp [SubTypeOkAt.check] at h

/-- `Rectype_ok: OK(x)` checker. -/
def RecTypeOkAt.check (C : Context) : List SubType → Nat → Bool
  | [], _ => true
  | st :: sts, x => SubTypeOkAt.check C st x && RecTypeOkAt.check C sts (x + 1)

theorem RecTypeOkAt.check_sound {C : Context} :
    ∀ {sts : List SubType} {x : Nat}, RecTypeOkAt.check C sts x = true → RecTypeOkAt C sts x
  | [], _, _ => .nil
  | st :: sts, x, h => by
    simp only [RecTypeOkAt.check, Bool.and_eq_true] at h
    exact .cons (SubTypeOkAt.check_sound h.1) (RecTypeOkAt.check_sound h.2)

/-! ## Examples -/

section Examples
open Examples

example : TyOk.check {} ftI32.toDefType = true := by decide
example : TyOk {} ftI32.toDefType := TyOk.check_sound (by decide)
example : TyOk.check {} ((rolldt 3 (liftRec listRec)).head!) = true := by decide
example : (rolldt 2 (liftRec pairRec2)).all (TyOk.check {}) = true := by decide
example : TyOk.check {} (Ty.refT true (.defHeap ftI32.toDefType)) = true := by decide
/-- An open type (a dangling `_IDX`) is rejected in the empty context. -/
example : TyOk.check {} ((rolldt 1 (liftRec refPrev)).head!) = false := by decide
example : ExternTypeOk.check {} (.func ftI32.toDefType) = true := by decide
example : ExternTypeOk.check {} (.tag ftI32.toDefType) = true := by decide
example : blockType? { types := [ftI32.toDefType] } (.typeIdx ⟨0⟩) = some ([Ty.i32], []) := by
  decide

end Examples

end Silmaril.Wasm.Validation
