module

public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Defs

/-!
# Round 6: Core's judgments are SpecTec's

Core's `TyOk`/`Sub` imply SpecTec's `TyOkS`/`SubS`, in the same context with any `RECS` appended
(`ext Δ M`). The two differences are handled as follows:

* **Append vs replace.** Core checks a group under `RECS = subs`, SpecTec under
  `RECS = subs ++ outer`; every judgment survives appending to `RECS` (`ext`), since it only
  looks up indices that are already present.
* **Parent-free `REC` rules.** Core's `recStruct` at a member with a declared supertype `u` is
  admissible in SpecTec (`recKind`): `REC i <: u` by `rec-sub`, `u <: STRUCT` by induction (an
  earlier member, `before`) or by `Heaptype_sub/struct` (a defined type), joined by `trans`.
  This needs the group to be valid (`RecsGood`: each declared supertype comes earlier, is valid,
  and unrolls to a non-final subtype of the same kind), which `GroupOk2` gives
  (`recsGood_withRecs`).

Results: `tyOkS_of_tyOk`, `subS_of_sub`, and in `{}`: `tyOkS_empty`, `subS_empty`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.Wasm
open Silmaril.Wasm.Validation

/-- `Δ` with `M` appended to its `RECS`. -/
def ext (Δ : TypeCtx) (M : List CSubType) : TypeCtx := { Δ with recs := Δ.recs ++ M }

theorem recs_ext {Δ : TypeCtx} {M : List CSubType} {i : Nat} {st : CSubType}
    (h : Δ.recs[i]? = some st) : (ext Δ M).recs[i]? = some st := by
  simp only [ext]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

theorem unrollUse_ext {Δ : TypeCtx} {M : List CSubType} {u : CTypeUse} {st : CSubType}
    (h : Δ.unrollUse u = some st) : (ext Δ M).unrollUse u = some st := by
  cases u with
  | idx x => exact h
  | recv i => exact recs_ext h
  | dt d => exact h

/-- The `RECS` of `Δ` are a valid group, as far as the `rec-*` rules need: each declared
supertype comes earlier, is valid in every extension, and unrolls to a non-final subtype of
the same kind. -/
def RecsGood (Δ : TypeCtx) : Prop :=
  ∀ (i : Nat) (st : CSubType), Δ.recs[i]? = some st → ∀ u ∈ st.supers, before u i = true ∧
    (∀ M, TyOkS (ext Δ M) u) ∧
    ∃ sups' ct', Δ.unrollUse u = some (.sub false sups' ct') ∧ compAbs ct' = compAbs st.body

/-- `deftype <: STRUCT/ARRAY/FUNC`, by the kind of the expansion. -/
theorem subS_kind {Δ : TypeCtx} {d : DefType} {fin : Bool} {sups : Ty (.list .use)}
    {ct : CCompType} (h : unrolldt d = some (.sub fin sups ct)) :
    SubS Δ (.use (.dt d)) (.abs (compAbs ct)) := by
  cases ct with
  | struct fs => exact .defStruct (.mk h)
  | array f => exact .defArray (.mk h)
  | func ps rs => exact .defFunc (.mk h)

/-- `REC i <: STRUCT/ARRAY/FUNC` at a parent-free member. -/
theorem subS_recKindNil {Δ : TypeCtx} {i : Nat} {fin : Bool} {ct : CCompType}
    (h : Δ.recs[i]? = some (.sub fin .nil ct)) :
    SubS Δ (.use (.recv i)) (.abs (compAbs ct)) := by
  cases ct with
  | struct fs => exact .recStruct h
  | array f => exact .recArray h
  | func ps rs => exact .recFunc h

/-- A type use that unrolls to a subtype is below that subtype's kind. -/
theorem subS_useKind {Δ : TypeCtx} {M : List CSubType} {u : CTypeUse} {sups : Ty (.list .use)}
    {ct : CCompType} (h : Δ.unrollUse u = some (.sub false sups ct))
    (hrec : ∀ k, u = .recv k → SubS (ext Δ M) (.use (.recv k)) (.abs (compAbs ct))) :
    SubS (ext Δ M) (.use u) (.abs (compAbs ct)) := by
  cases u with
  | recv k => exact hrec k rfl
  | dt d => exact subS_kind h
  | idx x =>
    simp only [TypeCtx.unrollUse] at h
    cases hx : Δ.types[x]? with
    | none => simp [hx] at h
    | some d =>
      rw [hx] at h
      exact .idxL hx (subS_kind h)

/-- **Core's `rec-*` kind rules are admissible in SpecTec** over a valid group: `REC i` is
below the kind of `RECS[i]`, whatever its supertypes. -/
theorem recKind {Δ : TypeCtx} (hR : RecsGood Δ) (M : List CSubType) :
    ∀ (i : Nat) (st : CSubType), Δ.recs[i]? = some st →
      SubS (ext Δ M) (.use (.recv i)) (.abs (compAbs st.body)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro st hst
    cases st with
    | sub fin sups ct =>
    cases sups with
    | nil => exact subS_recKindNil (recs_ext hst)
    | cons u rest =>
      obtain ⟨hb, hok, sups', ct', hun, hk⟩ := hR i _ hst u (by simp [Ty.supers])
      have hu : SubS (ext Δ M) (.use u) (.abs (compAbs ct')) := subS_useKind hun fun k hk' => by
        subst hk'
        exact ih k (by simpa [before] using hb) _ hun
      simp only [Ty.body] at hk ⊢
      rw [← hk]
      exact .heapTrans (.use (hok M)) (.recSub (j := 0) (recs_ext hst) rfl) hu

/-- `GroupOk2` makes its own `RECS` good, given that the declared supertypes are valid in every
extension. -/
theorem recsGood_withRecs {Δ : TypeCtx} {subs : Ty (.list .sub)}
    (hg : GroupOk2 (Δ.withRecs subs.toList) (.group subs) 0)
    (hok : ∀ (k : Nat) (st : CSubType), subs.toList[k]? = some st → ∀ M, ∀ u ∈ st.supers,
      TyOkS (ext (Δ.withRecs subs.toList) M) u) :
    RecsGood (Δ.withRecs subs.toList) := by
  intro i st hst u hu
  have hst' : subs.toList[i]? = some st := hst
  have hso := GroupOk2.get subs hg hst'
  rw [Nat.zero_add] at hso
  cases hso with
  | noSuper => simp [Ty.supers] at hu
  | oneSuper _ hb hunroll _ hsub =>
    simp only [Ty.supers, Ty.toList_cons, Ty.toList_nil, List.mem_singleton] at hu
    subst hu
    exact ⟨hb, fun M => hok i _ hst' M _ (by simp [Ty.supers]), _, _, hunroll,
      (Sub.compAbs_eq hsub).symm⟩

mutual

/-- **Core-valid is SpecTec-valid**, in the same context with any `RECS` appended. -/
theorem tyOkS_of_tyOk : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k}, TyOk Δ t →
    ∀ M, TyOkS (ext Δ M) t
  | _, _, _, .idx h, _ => .idx h
  | _, _, _, .recv h, _ => .recv (recs_ext h)
  | _, _, _, .dt h, M => .dt (tyOkS_of_tyOk h M)
  | Δ, _, _, .defn hg hi, M =>
    .defn ((groupOk2S_of hg).2 (recsGood_withRecs hg (groupOk2S_of hg).1) (Δ.recs ++ M)) hi
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, M => .use (tyOkS_of_tyOk h M)
  | _, _, _, .ref h, M => .ref (tyOkS_of_tyOk h M)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, M => .refv (tyOkS_of_tyOk h M)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, M => .val (tyOkS_of_tyOk h M)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, M => .field (tyOkS_of_tyOk h M)
  | _, _, _, .struct h, M => .struct (tyOkS_of_tyOk h M)
  | _, _, _, .array h, M => .array (tyOkS_of_tyOk h M)
  | _, _, _, .func hp hr, M => .func (tyOkS_of_tyOk hp M) (tyOkS_of_tyOk hr M)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, M => .cons (tyOkS_of_tyOk ha M) (tyOkS_of_tyOk hl M)

/-- `SubOk2`: its supertypes are SpecTec-valid, and over good `RECS` it is `SubOk2S`. -/
theorem subOk2S_of : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2 Δ st i →
    (∀ M, ∀ u ∈ st.supers, TyOkS (ext Δ M) u) ∧
      (RecsGood Δ → ∀ M, SubOk2S (ext Δ M) st i)
  | _, _, _, .noSuper hct =>
    ⟨fun _ _ hu => by simp [Ty.supers] at hu, fun _ M => .noSuper (tyOkS_of_tyOk hct M)⟩
  | _, _, _, .oneSuper hu hb hunroll hct hsub =>
    ⟨fun M u' hu' => (show _ = u' from (List.mem_singleton.1 hu').symm) ▸ tyOkS_of_tyOk hu M,
     fun hR M => .oneSuper (tyOkS_of_tyOk hu M) hb (unrollUse_ext hunroll)
      (tyOkS_of_tyOk hct M) (subS_of_sub hsub hR M)⟩

/-- `GroupOk2`: its members' supertypes are SpecTec-valid, and over good `RECS` it is
`GroupOk2S`. -/
theorem groupOk2S_of : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2 Δ g i →
    (∀ (k : Nat) (st : CSubType), g.subs.toList[k]? = some st → ∀ M, ∀ u ∈ st.supers,
      TyOkS (ext Δ M) u) ∧
      (RecsGood Δ → ∀ M, GroupOk2S (ext Δ M) g i)
  | _, _, _, .nil => ⟨fun _ _ h => by simp [Ty.subs] at h, fun _ _ => .nil⟩
  | _, _, _, .cons h hs =>
    ⟨fun k st hk => by
      cases k with
      | zero =>
        simp only [Ty.subs, Ty.toList_cons, List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact (subOk2S_of h).1
      | succ k =>
        simp only [Ty.subs, Ty.toList_cons, List.getElem?_cons_succ] at hk
        exact (groupOk2S_of hs).1 k st hk,
     fun hR M => .cons ((subOk2S_of h).2 hR M) ((groupOk2S_of hs).2 hR M)⟩

/-- **Core subtyping is SpecTec subtyping** over good `RECS`, with any `RECS` appended. -/
theorem subS_of_sub : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k}, Sub Δ a b → RecsGood Δ →
    ∀ M, SubS (ext Δ M) a b
  | _, _, _, _, .heapRefl, _, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hR, M =>
    .heapTrans (tyOkS_of_tyOk hok M) (subS_of_sub h₁ hR M) (subS_of_sub h₂ hR M)
  | _, _, _, _, .eqAny, _, _ => .eqAny
  | _, _, _, _, .i31Eq, _, _ => .i31Eq
  | _, _, _, _, .structEq, _, _ => .structEq
  | _, _, _, _, .arrayEq, _, _ => .arrayEq
  | _, _, _, _, .defStruct h, _, _ => .defStruct h
  | _, _, _, _, .defArray h, _, _ => .defArray h
  | _, _, _, _, .defFunc h, _, _ => .defFunc h
  | _, _, _, _, .defDef h, hR, M => .defDef (subS_of_sub h hR M)
  | _, _, _, _, .idxL hx hs, hR, M => .idxL hx (subS_of_sub hs hR M)
  | _, _, _, _, .idxR hx hs, hR, M => .idxR hx (subS_of_sub hs hR M)
  | _, _, _, _, .recStruct h, hR, M => recKind hR M _ _ h
  | _, _, _, _, .recArray h, hR, M => recKind hR M _ _ h
  | _, _, _, _, .recFunc h, hR, M => recKind hR M _ _ h
  | _, _, _, _, .recSub h hj, _, _ => .recSub (recs_ext h) hj
  | _, _, _, _, .none hs hb, hR, M => .none (subS_of_sub hs hR M) hb
  | _, _, _, _, .nofunc hs hb, hR, M => .nofunc (subS_of_sub hs hR M) hb
  | _, _, _, _, .noexn hs hb, hR, M => .noexn (subS_of_sub hs hR M) hb
  | _, _, _, _, .noextern hs hb, hR, M => .noextern (subS_of_sub hs hR M) hb
  | _, _, _, _, .bot, _, _ => .bot
  | _, _, _, _, .refNonNull h, hR, M => .refNonNull (subS_of_sub h hR M)
  | _, _, _, _, .refNull h, hR, M => .refNull (subS_of_sub h hR M)
  | _, _, _, _, .num, _, _ => .num
  | _, _, _, _, .vec, _, _ => .vec
  | _, _, _, _, .refv h, hR, M => .refv (subS_of_sub h hR M)
  | _, _, _, _, .botv, _, _ => .botv
  | _, _, _, _, .val h, hR, M => .val (subS_of_sub h hR M)
  | _, _, _, _, .pack, _, _ => .pack
  | _, _, _, _, .fieldConst h, hR, M => .fieldConst (subS_of_sub h hR M)
  | _, _, _, _, .fieldVar h₁ h₂, hR, M => .fieldVar (subS_of_sub h₁ hR M) (subS_of_sub h₂ hR M)
  | _, _, _, _, .struct h, hR, M => .struct (subS_of_sub h hR M)
  | _, _, _, _, .array h, hR, M => .array (subS_of_sub h hR M)
  | _, _, _, _, .func hp hr, hR, M => .func (subS_of_sub hp hR M) (subS_of_sub hr hR M)
  | _, _, _, _, .defRefl h, _, _ => .defRefl h
  | _, _, _, _, .defSuper h hj hs, hR, M => .defSuper h hj (subS_of_sub hs hR M)
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons h hl, hR, M => .cons (subS_of_sub h hR M) (subS_of_sub hl hR M)

end

/-- `{}` has good `RECS` (it has none). -/
theorem recsGood_empty : RecsGood {} := fun _ _ h => by simp at h

/-- **Core-valid in `{}` is SpecTec-valid in `{}`.** -/
theorem tyOkS_empty {k : TKind} {t : Ty k} (h : TyOk {} t) : TyOkS {} t :=
  tyOkS_of_tyOk h []

/-- **Core subtyping in `{}` is SpecTec subtyping in `{}`.** -/
theorem subS_empty {k : TKind} {a b : Ty k} (h : Sub {} a b) : SubS {} a b :=
  subS_of_sub h recsGood_empty []

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
