module

public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Defs
public import Silmaril.Wasm.Validation.Subtyping.DefInv

/-!
# Round 6: kinds are coherent along supertypes of SpecTec-valid types

`Heaptype_sub/trans` needs only `Heaptype_ok` of its middle type, and SpecTec's `Heaptype_ok`
(`TyOkS`) accepts types Core's `TyOk` rejects (append vs replace). What the subtyping argument
needs of a middle type is only that its declared supertypes keep its kind (`struct`, `array`,
`func`): `Coh d`, every defined type reachable from `d` along declared supertypes
(`TypeCtx.Reach {}`) has `d`'s kind (`defKind`).

* `coh_of_tyOkS`: **every `TyOkS`-valid defined type is coherent**, in any context without
  `TYPES`. `Subtype_ok2` checks `Comptype_sub` against the declared supertype, which keeps the
  kind, and a supertype is either an earlier member of the same group or a smaller defined type.
* `coh_of_tyOk`: the same for Core's `TyOk {}` (Silmaril's `TypeCtx.Reach.ok_kind`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Validation.DefInv (subst_def_u len_of_get unroll_of_get subst_recv)

/-- Coherence passes along `Reach`. -/
theorem Coh.reach {d e : DefType} (hd : Coh d) (he : ({} : TypeCtx).Reach d e) : Coh e :=
  fun f hf => (hd f (he.trans hf)).trans (hd e he).symm

/-- `SubS` at the composite sort keeps the kind. -/
theorem SubS.compAbs_eq {Δ : TypeCtx} {c c' : CCompType} (h : SubS Δ c c') :
    compAbs c = compAbs c' := by
  cases h <;> rfl

/-- The members of a `GroupOk2S` group are `SubOk2S` at their position. -/
theorem GroupOk2S.get {Δ : TypeCtx} : ∀ (subs : Ty (.list .sub)) {m k : Nat} {st : CSubType},
    GroupOk2S Δ (.group subs) m → subs.toList[k]? = some st → SubOk2S Δ st (m + k)
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
        have := GroupOk2S.get l h2 (by simpa using h)
        rwa [show m + 1 + k = m + (k + 1) by omega] at this

/-- A supertype in a member's list is smaller than the member's group. -/
theorem size_lt_of_super {subs : Ty (.list .sub)} {j : Nat} {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} {d0 : DefType}
    (hst : subs.toList[j]? = some (.sub fin sups ct)) (hmem : Ty.dt d0 ∈ sups.toList) :
    d0.size < (Ty.defn (.group subs) j).size := by
  have h1 := Ty.size_lt_of_mem (List.mem_of_getElem? hst)
  have h2 := Ty.size_lt_of_mem hmem
  simp only [Ty.size] at h1 h2 ⊢
  omega

/-- The kind of a member of a group. -/
theorem defKind_member {subs : Ty (.list .sub)} {j : Nat} {fin : Bool} {sups : Ty (.list .use)}
    {ct : CCompType} (hst : subs.toList[j]? = some (.sub fin sups ct)) :
    defKind (.defn (.group subs) j) = some (compAbs ct) := by
  have hun : unrolldt (.defn (.group subs) j) =
      some (.sub fin (sups.subst (unrollSubst subs)) (ct.subst (unrollSubst subs))) :=
    unroll_of_get hst
  rw [defKind_of_unroll hun, compAbs_subst]

/-- The declared supertypes of a member of a group, unrolled. -/
theorem supersOf_member {subs : Ty (.list .sub)} {j : Nat} {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} (hst : subs.toList[j]? = some (.sub fin sups ct)) :
    supersOf (.defn (.group subs) j) = sups.toList.map (·.subst (unrollSubst subs)) := by
  have hun : unrolldt (.defn (.group subs) j) =
      some (.sub fin (sups.subst (unrollSubst subs)) (ct.subst (unrollSubst subs))) :=
    unroll_of_get hst
  rw [supersOf_of_unroll hun, Ty.supers, Ty.toList_subst]

/-- What one step along a declared supertype of a group member gives. -/
def StepFact (Δ : TypeCtx) (subs : Ty (.list .sub)) (j : Nat) (d' : DefType) : Prop :=
  defKind d' = defKind (.defn (.group subs) j) ∧
    ((∃ k, k < j ∧ d' = .defn (.group subs) k) ∨
      (d'.size < (Ty.defn (.group subs) j).size ∧ TyOkS (withRecsA Δ subs.toList) d'))

/-- The step to an earlier member `REC k`. -/
theorem stepFact_recv {Δ : TypeCtx} {subs : Ty (.list .sub)} {j k : Nat} {fin : Bool}
    {ct ct' : CCompType} {sups sups' : Ty (.list .use)}
    (hst : subs.toList[j]? = some (.sub fin sups ct)) (hkj : k < j)
    (hunroll : (withRecsA Δ subs.toList).unrollUse (.recv k) = some (.sub false sups' ct'))
    (hk : compAbs ct = compAbs ct') : StepFact Δ subs j (.defn (.group subs) k) := by
  have hkl : k < subs.toList.length :=
    Nat.lt_trans hkj (List.getElem?_eq_some_iff.1 hst).1
  have hk' : subs.toList[k]? = some (.sub false sups' ct') := by
    simpa [TypeCtx.unrollUse, withRecsA, List.getElem?_append_left hkl] using hunroll
  refine ⟨?_, .inl ⟨k, hkj, rfl⟩⟩
  rw [defKind_member hk', defKind_member hst, hk]

/-- The step to a defined type `d0` of the member's supertype list. -/
theorem stepFact_dt {Δ : TypeCtx} {subs : Ty (.list .sub)} {j : Nat} {fin : Bool}
    {ct ct' : CCompType} {d0 : DefType} {sups' : Ty (.list .use)}
    (hst : subs.toList[j]? = some (.sub fin (.cons (.dt d0) .nil) ct))
    (hu0 : TyOkS (withRecsA Δ subs.toList) (.dt d0))
    (hunroll : unrolldt d0 = some (.sub false sups' ct'))
    (hk : compAbs ct = compAbs ct') : StepFact Δ subs j d0 := by
  have hok : TyOkS (withRecsA Δ subs.toList) d0 := by
    cases hu0 with
    | dt h => exact h
  refine ⟨?_, .inr ⟨size_lt_of_super hst (by simp), hok⟩⟩
  rw [defKind_of_unroll hunroll, defKind_member hst, hk]

/-- One step along the declared supertype `u0` of member `j`. -/
theorem stepFact_one {Δ : TypeCtx} (hT : Δ.types = []) {subs : Ty (.list .sub)} {j : Nat}
    {fin : Bool} {u0 : CTypeUse} {ct ct' : CCompType} {sups' : Ty (.list .use)}
    (hst : subs.toList[j]? = some (.sub fin (.cons u0 .nil) ct))
    (hu0 : TyOkS (withRecsA Δ subs.toList) u0) (hb : before u0 j = true)
    (hunroll : (withRecsA Δ subs.toList).unrollUse u0 = some (.sub false sups' ct'))
    (hk : compAbs ct = compAbs ct') {d' : DefType}
    (hr : ({} : TypeCtx).resolve (u0.subst (unrollSubst subs)) = some d') :
    StepFact Δ subs j d' := by
  cases u0 with
  | idx x =>
    cases hu0 with
    | idx h => exact absurd h (by simp [withRecsA, hT])
  | recv k =>
    have hkj : k < j := by simpa [before] using hb
    have hks : k < subs.length := Nat.lt_trans hkj (len_of_get hst)
    have hd' : Ty.defn (.group subs) k = d' := by simpa [subst_recv hks] using hr
    exact hd' ▸ stepFact_recv hst hkj hunroll hk
  | dt d0 =>
    have hd' : d0 = d' := by simpa [Ty.subst, subst_def_u] using hr
    exact hd' ▸ stepFact_dt hst hu0 hunroll hk

/-- One step along a declared supertype of a member of a `GroupOk2S` group, in a context
without `TYPES`: the supertype is an earlier member, or a `TyOkS`-valid defined type of the
member's supertype list; either way it has the member's kind. -/
theorem super_step_S {Δ : TypeCtx} (hT : Δ.types = []) {subs : Ty (.list .sub)}
    (hg : GroupOk2S (withRecsA Δ subs.toList) (.group subs) 0) {j : Nat}
    (hj : j < subs.length) {u : CTypeUse} {d' : DefType}
    (hu : u ∈ supersOf (.defn (.group subs) j)) (hr : ({} : TypeCtx).resolve u = some d') :
    StepFact Δ subs j d' := by
  obtain ⟨st, hst⟩ : ∃ st, subs.toList[j]? = some st :=
    ⟨_, List.getElem?_eq_getElem (by simpa [Ty.length] using hj)⟩
  have hso : SubOk2S (withRecsA Δ subs.toList) st j := by
    simpa using GroupOk2S.get subs hg hst
  cases hso with
  | noSuper => exact absurd hu (by simp [supersOf_member hst])
  | @oneSuper _ _ u0 _ _ _ _ hu0 hb hunroll _ hsub =>
    have hu' : u = u0.subst (unrollSubst subs) := by simpa [supersOf_member hst] using hu
    exact stepFact_one hT hst hu0 hb hunroll hsub.compAbs_eq (hu' ▸ hr)

/-- **`TyOkS`-valid defined types are coherent**, in a context without `TYPES`. -/
theorem coh_of_tyOkS : ∀ (n : Nat) {Δ : TypeCtx} {d : DefType}, d.size < n →
    Δ.types = [] → TyOkS Δ d → Coh d
  | 0, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, Δ, d, hn, hT, h => by
    cases h with
    | @defn _ subs i hg hi =>
    have hT' : (withRecsA Δ subs.toList).types = [] := hT
    suffices H : ∀ j, j < subs.length → Coh (.defn (.group subs) j) from H i hi
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj e he
      cases he with
      | refl => rfl
      | @step _ d' _ u hu hr hrest =>
        obtain ⟨hk, hcase⟩ := super_step_S hT hg hj hu hr
        rw [← hk]
        rcases hcase with ⟨k, hkj, rfl⟩ | ⟨hlt, hok⟩
        · exact ih k hkj (by omega) e hrest
        · exact coh_of_tyOkS n (by simp only [Ty.size] at hn hlt ⊢; omega) hT' hok e hrest

/-- Coherence of a `TyOkS`-valid heap type, in a context without `TYPES`. -/
theorem cohH_of_tyOkS {Δ : TypeCtx} (hT : Δ.types = []) {h : CHeapType} (hh : TyOkS Δ h) :
    CohH h := by
  cases hh with
  | abs => trivial
  | bot => trivial
  | use hu =>
    cases hu with
    | idx => trivial
    | recv => trivial
    | dt hd => exact coh_of_tyOkS _ (Nat.lt_succ_self _) hT hd

/-- **Core-valid defined types are coherent** (Silmaril's `TypeCtx.Reach.ok_kind`). -/
theorem coh_of_tyOk {d : DefType} (hd : TyOk {} d) : Coh d :=
  fun _ he => (he.ok_kind DefInv.okEmpty hd).2

/-- Coherence of a Core-valid heap type. -/
theorem cohH_of_tyOk {h : CHeapType} (hh : TyOk {} h) : CohH h := by
  cases hh with
  | abs => trivial
  | bot => trivial
  | use hu =>
    cases hu with
    | idx => trivial
    | recv => trivial
    | dt hd => exact coh_of_tyOk hd

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
