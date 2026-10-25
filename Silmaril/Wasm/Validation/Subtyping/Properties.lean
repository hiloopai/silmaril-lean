module

public import Silmaril.Wasm.Validation.Subtyping.Extern
public import Silmaril.Wasm.Validation.TypeOk

@[expose] public section

/-! # Milestones: reflexivity, transitivity and decidability of subtyping

The spec does not state these metatheorems. Transitivity needs the
well-formedness of the middle type, mirroring the `Heaptype_ok` premise of
`Heaptype_sub/trans`.

`Sub` is only a spec judgment at the sorts listed by `TKind.HasSub` (plus
sequences of them); at `use`, `sub` and `group` it is empty.
-/

namespace Silmaril.Wasm.Validation

/-- The sorts that carry a spec subtyping judgment. -/
def TKind.HasSub : TKind → Prop
  | .heap | .ref | .val | .storage | .field | .comp | .def => True
  | .list k => k.HasSub
  | .use | .sub | .group => False

theorem Ty.app_nil {k : TKind} (l : Ty (.list k)) : l.app .nil = l := by
  simp [Ty.app]

/-- Reflexivity at every subtyping sort. -/
theorem Sub.refl (Δ : TypeCtx) : {k : TKind} → k.HasSub → (t : Ty k) → Sub Δ t t
  | _, _, .nil => .nil
  | .list k, hk, .cons a l => .cons (Sub.refl Δ (k := k) hk a) (Sub.refl Δ (k := .list k) hk l)
  | _, _, .abs _ => .heapRefl
  | _, _, .bot => .heapRefl
  | _, _, .use _ => .heapRefl
  | _, hk, .ref false h => .refNonNull (Sub.refl Δ (k := .heap) trivial h)
  | _, hk, .ref true h => .refNull (Sub.refl Δ (k := .heap) trivial h)
  | _, _, .num _ => .num
  | _, _, .vec _ => .vec
  | _, _, .refv r => .refv (Sub.refl Δ (k := .ref) trivial r)
  | _, _, .botv => .botv
  | _, _, .val t => .val (Sub.refl Δ (k := .val) trivial t)
  | _, _, .pack _ => .pack
  | _, _, .field .const z => .fieldConst (Sub.refl Δ (k := .storage) trivial z)
  | _, _, .field .var z =>
      .fieldVar (Sub.refl Δ (k := .storage) trivial z) (Sub.refl Δ (k := .storage) trivial z)
  | _, _, .struct fs => by
      have h := Sub.struct (Δ := Δ) (extra := .nil) (Sub.refl Δ (k := .list .field) trivial fs)
      rwa [Ty.app_nil] at h
  | _, _, .array f => .array (Sub.refl Δ (k := .field) trivial f)
  | _, _, .func ps rs =>
      .func (Sub.refl Δ (k := .list .val) trivial ps) (Sub.refl Δ (k := .list .val) trivial rs)
  | _, _, .defn _ _ => .defRefl rfl
  | _, hk, .idx _ => hk.elim
  | _, hk, .recv _ => hk.elim
  | _, hk, .dt _ => hk.elim
  | _, hk, .sub _ _ _ => hk.elim
  | _, hk, .group _ => hk.elim

/-- Well-formedness of the type fields of a context: every defined type in
`TYPES` is closed and valid. Transitivity of subtyping needs it, because
`Deftype_sub/refl` compares closures over `TYPES` while `Deftype_sub/super`
unrolls syntactically. -/
def TypeCtx.Ok (Δ : TypeCtx) : Prop := ∀ d ∈ Δ.types, d.Closed ∧ TyOk Δ d

/-! ### Helper lemmas for transitivity -/

-- `Ty.toList_subst` / `Ty.length_subst` live in `DefTypes.lean`.

theorem Ty.toList_app {k : TKind} (a b : Ty (.list k)) :
    (a.app b).toList = a.toList ++ b.toList := by
  simp [Ty.app]

theorem Ty.app_assoc {k : TKind} (a b c : Ty (.list k)) :
    (a.app b).app c = a.app (b.app c) := by
  simp [Ty.app]

theorem Sub.ofList_iff (Δ : TypeCtx) {k : TKind} (xs ys : List (Ty k)) :
    Sub Δ (Ty.ofList xs) (Ty.ofList ys) ↔ List.Forall₂ (Sub Δ) xs ys := by
  constructor
  · induction xs generalizing ys with
    | nil =>
      intro h
      cases ys with
      | nil => exact .nil
      | cons b l => cases h
    | cons a l ih =>
      intro h
      cases ys with
      | nil => cases h
      | cons b l' =>
        cases h with
        | cons hab hl => exact .cons hab (ih _ hl)
  · intro h
    induction h with
    | nil => exact .nil
    | cons hab _ ih => exact .cons hab ih

theorem Sub.list_iff (Δ : TypeCtx) {k : TKind} (l l' : Ty (.list k)) :
    Sub Δ l l' ↔ List.Forall₂ (Sub Δ) l.toList l'.toList := by
  rw [← Sub.ofList_iff, Ty.ofList_toList, Ty.ofList_toList]

theorem Sub.list_length {Δ : TypeCtx} {k : TKind} {l l' : Ty (.list k)} (h : Sub Δ l l') :
    l.toList.length = l'.toList.length :=
  ((Sub.list_iff Δ l l').1 h).length_eq

theorem Sub.app {Δ : TypeCtx} {k : TKind} {x y z w : Ty (.list k)}
    (h₁ : Sub Δ x z) (h₂ : Sub Δ y w) : Sub Δ (x.app y) (z.app w) := by
  rw [Sub.list_iff, Ty.toList_app, Ty.toList_app]
  exact List.rel_append ((Sub.list_iff _ _ _).1 h₁) ((Sub.list_iff _ _ _).1 h₂)

theorem Sub.app_right_inv {Δ : TypeCtx} {k : TKind} {x z w : Ty (.list k)}
    (h : Sub Δ x (z.app w)) : ∃ p q, x = p.app q ∧ Sub Δ p z := by
  rw [Sub.list_iff, Ty.toList_app] at h
  refine ⟨Ty.ofList (x.toList.take z.toList.length),
    Ty.ofList (x.toList.drop z.toList.length), ?_, ?_⟩
  · simp [Ty.app]
  · rw [Sub.list_iff, Ty.toList_ofList]
    simpa using List.forall₂_take z.toList.length h

theorem Sub.app_cancel {Δ : TypeCtx} {k : TKind} {x y z w : Ty (.list k)}
    (hl : x.toList.length = z.toList.length) (h : Sub Δ (x.app y) (z.app w)) : Sub Δ x z := by
  rw [Sub.list_iff, Ty.toList_app, Ty.toList_app] at h
  rw [Sub.list_iff]
  simpa [hl] using List.forall₂_take x.toList.length h

/-- A type with no free `REC` variables: substitutions acting only on `REC`
leave it alone. -/
def Ty.RecFree {k : TKind} (u : Ty k) : Prop :=
  ∀ ρ : Subst, (∀ x, ρ (.idx x) = none) → u.subst ρ = u

theorem Subst.minusRecs_of_idx_none {ρ : Subst} (h : ∀ x, ρ (.idx x) = none) :
    ∀ v, ρ.minusRecs v = none := by
  intro v; cases v <;> simp [Subst.minusRecs, h]

theorem Subst.minusRecs_eq {σ : Subst} (h : ∀ i, σ (.recv i) = none) : σ.minusRecs = σ := by
  funext v; cases v <;> simp [Subst.minusRecs, h]

theorem Ty.recFree_def (d : DefType) : d.RecFree := by
  intro ρ hρ
  cases d with
  | defn g j =>
    cases g with
    | group s =>
      simp only [Ty.subst]
      rw [Ty.subst_of_none _ _ (Subst.minusRecs_of_idx_none hρ)]

theorem Ty.recFree_dt (d : DefType) : (Ty.dt d).RecFree := by
  intro ρ hρ
  simp only [Ty.subst]
  rw [Ty.recFree_def d ρ hρ]

/-- Commuting a `REC`-only substitution past an `_IDX`-only one whose images
are `REC`-free. -/
def SubstCommOk (τ σ : Subst) : Prop :=
  (∀ x, τ (.idx x) = none) ∧ (∀ i, σ (.recv i) = none) ∧
    (∀ x u, σ (.idx x) = some u → Ty.RecFree u)

theorem Ty.subst_comm_aux {k : TKind} (t : Ty k) : ∀ (τ σ : Subst), SubstCommOk τ σ →
    (t.subst τ).subst σ = (t.subst σ).subst (fun v => (τ v).map (·.subst σ)) := by
  induction t with
  | idx x =>
    rintro τ σ ⟨hτ, hσ, hσu⟩
    cases h : σ (.idx x) with
    | none => simp [Ty.subst, hτ, h]
    | some u =>
      simp only [Ty.subst, hτ, h, Option.getD_none, Option.getD_some]
      exact (hσu x u h _ (by simp [hτ])).symm
  | recv i =>
    rintro τ σ ⟨hτ, hσ, hσu⟩
    cases h : τ (.recv i) with
    | none => simp [Ty.subst, hσ, h]
    | some u => simp [Ty.subst, hσ, h]
  | group subs ih =>
    rintro τ σ ⟨hτ, hσ, hσu⟩
    simp only [Ty.subst]
    rw [ih τ.minusRecs σ.minusRecs ⟨by simp [Subst.minusRecs, hτ], by simp [Subst.minusRecs],
      by intro x u h; exact hσu x u (by simpa [Subst.minusRecs] using h)⟩]
    congr 2
    funext v; cases v <;> simp [Subst.minusRecs, hτ]
  | _ => intro τ σ hP; simp_all [Ty.subst]

theorem Ty.subst_comm {k : TKind} (t : Ty k) (τ σ : Subst) (hτ : ∀ x, τ (.idx x) = none)
    (hσ : ∀ i, σ (.recv i) = none) (hσu : ∀ x u, σ (.idx x) = some u → u.RecFree) :
    (t.subst τ).subst σ = (t.subst σ).subst (fun v => (τ v).map (·.subst σ)) :=
  t.subst_comm_aux τ σ ⟨hτ, hσ, hσu⟩

/-- Unrolling commutes with an `_IDX`-only substitution with `REC`-free images. -/
theorem unrolldt_subst (σ : Subst) (hσ : ∀ i, σ (.recv i) = none)
    (hσu : ∀ x u, σ (.idx x) = some u → u.RecFree) (d : DefType) :
    unrolldt (d.subst σ) = (unrolldt d).map (·.subst σ) := by
  cases d with
  | defn g i =>
    cases g with
    | group subs =>
      have hd : (Ty.defn (.group subs) i).subst σ = .defn (.group (subs.subst σ)) i := by
        simp only [Ty.subst, Subst.minusRecs_eq hσ]
      rw [hd]
      simp only [unrolldt, unrollrt, Ty.subs]
      rw [← List.getElem?_map, ← Ty.toList_subst,
        Ty.subst_comm _ _ _ (fun _ => rfl) hσ hσu, Ty.length_subst]
      congr 3
      funext v
      cases v with
      | idx x => rfl
      | recv j =>
        by_cases hj : j < subs.length
        · simp [hj, Ty.subst, Subst.minusRecs_eq hσ]
        · simp [hj]

/-- The substitution `$clos` performs in a well-formed context. -/
def TypeCtx.closSubst (Δ : TypeCtx) : Subst := Subst.all (Δ.types.map .dt)

theorem TypeCtx.Ok.clos_eq {Δ : TypeCtx} (hΔ : Δ.Ok) {k : TKind} (t : Ty k) :
    t.clos Δ.types = t.subst Δ.closSubst := by
  simp [Ty.clos, Ty.substAll, TypeCtx.closSubst,
    closDefTypes_closed (fun d hd => (hΔ d hd).1)]

theorem TypeCtx.closSubst_recv (Δ : TypeCtx) (i : Nat) : Δ.closSubst (.recv i) = none := rfl

theorem TypeCtx.closSubst_idx (Δ : TypeCtx) (x : Nat) :
    Δ.closSubst (.idx x) = (Δ.types[x]?).map .dt := by
  simp [TypeCtx.closSubst, Subst.all]

theorem TypeCtx.closSubst_recFree (Δ : TypeCtx) :
    ∀ x u, Δ.closSubst (.idx x) = some u → u.RecFree := by
  intro x u h
  rw [TypeCtx.closSubst_idx] at h
  cases hx : Δ.types[x]? with
  | none => simp [hx] at h
  | some d =>
    simp only [hx, Option.map_some, Option.some.injEq] at h
    subst h
    exact Ty.recFree_dt d

theorem TypeCtx.subst_idx (Δ : TypeCtx) (x : Nat) :
    (Ty.idx x).subst Δ.closSubst = ((Δ.types[x]?).map .dt).getD (.idx x) := by
  simp [Ty.subst, TypeCtx.closSubst_idx]

/-- Two type uses with the same closure are heap subtypes. -/
theorem Sub.use_of_subst_eq {Δ : TypeCtx} (hΔ : Δ.Ok) {u' u : CTypeUse}
    (h : u'.subst Δ.closSubst = u.subst Δ.closSubst) : Sub Δ (.use u') (.use u) := by
  have hcl : ∀ {x : Nat} {d : DefType}, Δ.types[x]? = some d → d.clos Δ.types = d := by
    intro x d hx
    rw [hΔ.clos_eq]
    exact Ty.subst_closed d _ (fun _ => rfl) (hΔ d (List.mem_of_getElem? hx)).1
  cases u' with
  | idx x =>
    cases hx : Δ.types[x]? with
    | none =>
      rw [TypeCtx.subst_idx, hx] at h
      cases u with
      | idx y =>
        cases hy : Δ.types[y]? with
        | none => rw [TypeCtx.subst_idx, hy] at h; simp at h; subst h; exact .heapRefl
        | some e => rw [TypeCtx.subst_idx, hy] at h; simp at h
      | recv i => simp [Ty.subst, TypeCtx.closSubst_recv] at h
      | dt e => simp [Ty.subst] at h
    | some d =>
      rw [TypeCtx.subst_idx, hx] at h
      simp only [Option.map_some, Option.getD_some] at h
      cases u with
      | idx y =>
        cases hy : Δ.types[y]? with
        | none => rw [TypeCtx.subst_idx, hy] at h; simp at h
        | some e =>
          rw [TypeCtx.subst_idx, hy] at h
          simp only [Option.map_some, Option.getD_some, Ty.dt.injEq] at h
          subst h
          exact .idxL hx (.idxR hy .heapRefl)
      | recv i => simp [Ty.subst, TypeCtx.closSubst_recv] at h
      | dt e =>
        simp only [Ty.subst, Ty.dt.injEq] at h
        exact .idxL hx (.defDef (.defRefl (by rw [hcl hx, hΔ.clos_eq, h])))
  | recv i =>
    cases u with
    | idx y =>
      cases hy : Δ.types[y]? with
      | none => rw [TypeCtx.subst_idx, hy] at h; simp [Ty.subst, TypeCtx.closSubst_recv] at h
      | some e => rw [TypeCtx.subst_idx, hy] at h; simp [Ty.subst, TypeCtx.closSubst_recv] at h
    | recv j =>
      simp [Ty.subst, TypeCtx.closSubst_recv] at h
      subst h; exact .heapRefl
    | dt e => simp [Ty.subst, TypeCtx.closSubst_recv] at h
  | dt e' =>
    cases u with
    | idx y =>
      cases hy : Δ.types[y]? with
      | none => rw [TypeCtx.subst_idx, hy] at h; simp [Ty.subst] at h
      | some e =>
        rw [TypeCtx.subst_idx, hy] at h
        simp only [Ty.subst, Option.map_some, Option.getD_some, Ty.dt.injEq] at h
        exact .idxR hy (.defDef (.defRefl (by rw [hcl hy, hΔ.clos_eq, h])))
    | recv j => simp [Ty.subst, TypeCtx.closSubst_recv] at h
    | dt e =>
      simp only [Ty.subst, Ty.dt.injEq] at h
      exact .defDef (.defRefl (by rw [hΔ.clos_eq, hΔ.clos_eq, h]))

theorem GroupOk2.get {Δ : TypeCtx} : ∀ (subs : Ty (.list .sub)) {m k : Nat} {st : CSubType},
    GroupOk2 Δ (.group subs) m → subs.toList[k]? = some st → SubOk2 Δ st (m + k)
  | .nil, _, _, _, _, h => by simp at h
  | .cons s l, m, 0, st, hg, h => by
      cases hg with
      | cons h1 _ =>
        simp only [Ty.toList_cons, List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        simpa using h1
  | .cons s l, m, k + 1, st, hg, h => by
      cases hg with
      | cons _ h2 =>
        have := GroupOk2.get l h2 (by simpa using h)
        rwa [show m + 1 + k = m + (k + 1) by omega] at this

theorem SubOk2.super_ok {Δ : TypeCtx} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    {i : Nat} (h : SubOk2 Δ (.sub fin sups ct) i) : ∀ u ∈ sups.toList, TyOk Δ u := by
  cases h with
  | noSuper => simp
  | oneSuper hu => intro u hmem; simp at hmem; subst hmem; exact hu

theorem TyOk.def_congr {Δ₁ Δ₂ : TypeCtx} (ht : Δ₁.types = Δ₂.types) {d : DefType}
    (h : TyOk Δ₁ d) : TyOk Δ₂ d := by
  cases h with
  | defn hg hi =>
    have e : ∀ X, Δ₁.withRecs X = Δ₂.withRecs X := by
      intro X; cases Δ₁; cases Δ₂; simp_all [TypeCtx.withRecs]
    exact .defn (e _ ▸ hg) hi

/-- The declared supertypes of a valid defined type are valid heap types. -/
theorem TyOk.unroll_super {Δ : TypeCtx} {b : DefType} (hb : TyOk Δ b) {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType}
    (hu : unrolldt b = some (.sub fin sups ct)) {u : CTypeUse} (hmem : u ∈ sups.toList) :
    TyOk Δ (.use u) := by
  cases hb with
  | @defn _ subs i hg hi =>
    simp only [unrolldt, unrollrt, Ty.subs] at hu
    rw [Ty.toList_subst, List.getElem?_map] at hu
    cases hst : subs.toList[i]? with
    | none => simp [hst] at hu
    | some st =>
      rw [hst] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      have hso := GroupOk2.get subs hg hst
      cases st with
      | sub fin0 sups0 ct0 =>
        simp only [Ty.subst, Ty.sub.injEq] at hu
        obtain ⟨-, hsups, -⟩ := hu
        subst hsups
        rw [Ty.toList_subst, List.mem_map] at hmem
        obtain ⟨u0, hu0, rfl⟩ := hmem
        have hok := hso.super_ok u0 hu0
        cases u0 with
        | idx x =>
          cases hok with
          | idx h => simp only [Ty.subst, Option.getD_none]; exact .use (.idx h)
        | recv j =>
          cases hok with
          | recv h =>
            have hj : j < subs.length := by
              have := (List.getElem?_eq_some_iff.1 h).1
              simpa [TypeCtx.withRecs, Ty.length] using this
            simp only [Ty.subst, hj, ite_true, Option.getD_some]
            exact .use (.dt (.defn hg hj))
        | dt e =>
          rw [Ty.recFree_dt e _ (fun _ => rfl)]
          cases hok with
          | dt h => exact .use (.dt (TyOk.def_congr (Δ₁ := Δ.withRecs subs.toList) (Δ₂ := Δ) rfl h))

theorem Sub.trans_aux {Δ : TypeCtx} (hΔ : Δ.Ok) {k : TKind} (b : Ty k) :
    ∀ {a c : Ty k}, TyOk Δ b → Sub Δ a b → Sub Δ b c → Sub Δ a c := by
  induction b with
  | nil => intro a c _ hab hbc; cases hbc; exact hab
  | cons x l ihx ihl =>
    intro a c hb hab hbc
    cases hb with
    | cons hx hl =>
      cases hab with
      | cons h1 h2 =>
        cases hbc with
        | cons h3 h4 => exact .cons (ihx hx h1 h3) (ihl hl h2 h4)
  | idx x => intro a c _ hab; cases hab
  | recv i => intro a c _ hab; cases hab
  | dt d _ => intro a c _ hab; cases hab
  | sub f s b _ _ => intro a c _ hab; cases hab
  | group s _ => intro a c _ hab; cases hab
  | abs x => intro a c hb hab hbc; exact .heapTrans hb hab hbc
  | bot => intro a c hb hab hbc; exact .heapTrans hb hab hbc
  | use u _ => intro a c hb hab hbc; exact .heapTrans hb hab hbc
  | ref n h _ =>
    intro a c hb hab hbc
    cases hb with
    | ref hh =>
      cases hab with
      | refNonNull h1 =>
        cases hbc with
        | refNonNull h2 => exact .refNonNull (.heapTrans hh h1 h2)
        | refNull h2 => exact .refNull (.heapTrans hh h1 h2)
      | refNull h1 =>
        cases hbc with
        | refNull h2 => exact .refNull (.heapTrans hh h1 h2)
  | num t =>
    intro a c _ hab hbc
    cases hab with
    | num => exact hbc
    | botv => exact .botv
  | vec t =>
    intro a c _ hab hbc
    cases hab with
    | vec => exact hbc
    | botv => exact .botv
  | refv r ih =>
    intro a c hb hab hbc
    cases hb with
    | refv hr =>
      cases hab with
      | botv => exact .botv
      | refv h1 =>
        cases hbc with
        | refv h2 => exact .refv (ih hr h1 h2)
  | botv => intro a c _ hab hbc; cases hab; exact .botv
  | val t ih =>
    intro a c hb hab hbc
    cases hb with
    | val ht =>
      cases hab with
      | val h1 =>
        cases hbc with
        | val h2 => exact .val (ih ht h1 h2)
  | pack p => intro a c _ hab hbc; cases hab; exact hbc
  | field m s ih =>
    intro a c hb hab hbc
    cases hb with
    | field hs =>
      cases hab with
      | fieldConst h1 =>
        cases hbc with
        | fieldConst h2 => exact .fieldConst (ih hs h1 h2)
      | fieldVar h1 h1' =>
        cases hbc with
        | fieldVar h2 h2' => exact .fieldVar (ih hs h1 h2) (ih hs h2' h1')
  | array f ih =>
    intro a c hb hab hbc
    cases hb with
    | array hf =>
      cases hab with
      | array h1 =>
        cases hbc with
        | array h2 => exact .array (ih hf h1 h2)
  | func ps rs ihp ihr =>
    intro a c hb hab hbc
    cases hb with
    | func hp hr =>
      cases hab with
      | func hp1 hr1 =>
        cases hbc with
        | func hp2 hr2 => exact .func (ihp hp hp2 hp1) (ihr hr hr1 hr2)
  | struct fs ih =>
    intro a c hb hab hbc
    cases hb with
    | struct hfs =>
      cases hbc with
      | @struct _ fsb e2 fs3 h23 =>
        cases hab with
        | @struct _ fs1 extra _ h12 =>
          obtain ⟨p, q, rfl, hp⟩ := Sub.app_right_inv h12
          have hpad := ih hfs (Sub.app hp (Sub.refl Δ (k := .list .field) trivial e2))
            (Sub.app h23 (Sub.refl Δ (k := .list .field) trivial e2))
          have hp3 := Sub.app_cancel ((Sub.list_length hp).trans (Sub.list_length h23)) hpad
          have := Sub.struct (Δ := Δ) (extra := q.app extra) hp3
          rwa [Ty.app_assoc]
  | defn g i _ =>
    intro a c hb hab hbc
    have hdb : TyOk Δ (.use (.dt (.defn g i))) := .use (.dt hb)
    cases hab with
    | defSuper hu hj hs => exact .defSuper hu hj (.heapTrans hdb hs (.defDef hbc))
    | defRefl hab =>
      cases hbc with
      | defRefl hbc => exact .defRefl (hab.trans hbc)
      | @defSuper _ _ _ fin sups ct j u hu hj hs =>
        rw [hΔ.clos_eq, hΔ.clos_eq] at hab
        have e1 := unrolldt_subst Δ.closSubst Δ.closSubst_recv Δ.closSubst_recFree a
        have e2 := unrolldt_subst Δ.closSubst Δ.closSubst_recv Δ.closSubst_recFree (.defn g i)
        rw [hab, e2, hu] at e1
        cases hua : unrolldt a with
        | none => rw [hua] at e1; simp at e1
        | some st' =>
          rw [hua] at e1
          cases st' with
          | sub fin' sups' ct' =>
            simp only [Option.map_some, Option.some.injEq, Ty.subst, Ty.sub.injEq] at e1
            have hl := congrArg Ty.toList e1.2.1
            rw [Ty.toList_subst, Ty.toList_subst] at hl
            have hj' : (sups'.toList.map (·.subst Δ.closSubst))[j]? =
                some (u.subst Δ.closSubst) := by
              rw [← hl, List.getElem?_map, hj]; rfl
            rw [List.getElem?_map] at hj'
            cases hu' : sups'.toList[j]? with
            | none => rw [hu'] at hj'; simp at hj'
            | some u' =>
              rw [hu'] at hj'
              simp only [Option.map_some, Option.some.injEq] at hj'
              have hok := hb.unroll_super hu (List.mem_of_getElem? hj)
              exact .defSuper hua hu' (.heapTrans hok (Sub.use_of_subst_eq hΔ hj') hs)

/-- Transitivity through a well-formed middle type, in a well-formed context. -/
theorem Sub.trans {Δ : TypeCtx} {k : TKind} {a b c : Ty k} (hΔ : Δ.Ok)
    (hb : TyOk Δ b) (hab : Sub Δ a b) (hbc : Sub Δ b c) : Sub Δ a c :=
  Sub.trans_aux hΔ b hb hab hbc

theorem ResultSub.refl (Δ : TypeCtx) (ts : List CValType) : ResultSub Δ ts ts :=
  List.forall₂_same.mpr fun t _ => Sub.refl Δ (k := .val) trivial t

theorem LimitsSub.refl (l : Limits) : LimitsSub l l := by
  rcases l with ⟨n, _ | m⟩
  · exact .eps (Nat.le_refl _)
  · exact .max (Nat.le_refl _) (by rintro _ ⟨⟩; exact Nat.le_refl _)

theorem ExternSub.refl (Δ : TypeCtx) (x : CExternType) : ExternSub Δ x x := by
  cases x with
  | tag d => exact .tag ⟨Sub.refl Δ (k := .def) trivial d, Sub.refl Δ (k := .def) trivial d⟩
  | global g =>
    rcases g with ⟨_ | _, t⟩
    · exact .global (.const (Sub.refl Δ (k := .val) trivial t))
    · exact .global (.var (Sub.refl Δ (k := .val) trivial t) (Sub.refl Δ (k := .val) trivial t))
  | mem m => exact .mem (by rcases m with ⟨a, l⟩; exact .mk (LimitsSub.refl l))
  | table t =>
    rcases t with ⟨a, l, r⟩
    exact .table (.mk (LimitsSub.refl l) (Sub.refl Δ (k := .ref) trivial r)
      (Sub.refl Δ (k := .ref) trivial r))
  | func d => exact .func (Sub.refl Δ (k := .def) trivial d)

theorem LimitsSub.trans {a b c : Limits} (hab : LimitsSub a b) (hbc : LimitsSub b c) :
    LimitsSub a c := by
  cases hbc with
  | max hn2 hm2 =>
    cases hab with
    | max hn1 hm1 =>
      exact .max (Nat.le_trans hn2 hn1) (fun m hm => Nat.le_trans (hm1 _ rfl) (hm2 m hm))
  | eps hn2 =>
    cases hab with
    | max hn1 hm1 => exact .max (Nat.le_trans hn2 hn1) (by intro m hm; cases hm)
    | eps hn1 => exact .eps (Nat.le_trans hn2 hn1)

theorem ExternSub.trans {Δ : TypeCtx} {a b c : CExternType} (hΔ : Δ.Ok)
    (hb : ExternTypeOk Δ b) (hab : ExternSub Δ a b) (hbc : ExternSub Δ b c) :
    ExternSub Δ a c := by
  cases hb with
  | tag hbt =>
    cases hab with
    | tag h1 =>
      cases hbc with
      | tag h2 => exact .tag ⟨Sub.trans hΔ hbt.1 h1.1 h2.1, Sub.trans hΔ hbt.1 h2.2 h1.2⟩
  | global hg =>
    cases hab with
    | global h1 =>
      cases hbc with
      | global h2 =>
        refine .global ?_
        cases h1 with
        | const h1 =>
          cases h2 with
          | const h2 => exact .const (Sub.trans hΔ hg h1 h2)
        | var h1 h1' =>
          cases h2 with
          | var h2 h2' => exact .var (Sub.trans hΔ hg h1 h2) (Sub.trans hΔ hg h2' h1')
  | mem hm =>
    cases hab with
    | mem h1 =>
      cases hbc with
      | mem h2 =>
        refine .mem ?_
        cases h1 with
        | mk l1 =>
          cases h2 with
          | mk l2 => exact .mk (l1.trans l2)
  | table ht =>
    cases hab with
    | table h1 =>
      cases hbc with
      | table h2 =>
        refine .table ?_
        cases h1 with
        | mk hl1 hr1 hr1' =>
          cases h2 with
          | mk hl2 hr2 hr2' =>
            exact .mk (hl1.trans hl2) (Sub.trans hΔ ht.2 hr1 hr2) (Sub.trans hΔ ht.2 hr2' hr1')
  | func hd he =>
    cases hab with
    | func h1 =>
      cases hbc with
      | func h2 => exact .func (Sub.trans hΔ hd h1 h2)

/-- On defined types with no declared supertypes (all V1/Lime1 images),
subtyping is closure-equality. -/
theorem Sub.def_iff_of_noSupers {Δ : TypeCtx} {d₁ d₂ : DefType}
    (h : ∀ fin sups ct, unrolldt d₁ = some (.sub fin sups ct) → sups = .nil) :
    Sub Δ d₁ d₂ ↔ d₁.clos Δ.types = d₂.clos Δ.types := by
  constructor
  · intro hs
    cases hs with
    | defRefl h' => exact h'
    | defSuper hu hj _ =>
      have := h _ _ _ hu
      subst this
      simp at hj
  · exact .defRefl

end Silmaril.Wasm.Validation
