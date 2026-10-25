module

public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Function subtyping for `call_ref` (helper for `Ctx.fill_callout_typed`)

A function reference whose type is (by a chain of subtypings) below
`ref null (defHeap d)` has a function type with as many parameters as `d`'s
expansion and results that are subtypes of `d`'s results (`co_K`).

* `co_sub_rho`: substituting the members of a valid recursive group for its
  `REC` variables preserves subtyping (the `RECS` of the group's context are
  eliminated);
* `co_super_sub`: the expansion of a valid defined type is a subtype of the
  expansion of each of its declared supertypes;
* `co_chain`: along any subtyping derivation starting from a defined function
  type, every defined type reached (up to closure) has such a function type.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

/-! ## `REC`-free types -/

/-- Types valid in a context without `RECS` have no free `REC` variables. -/
theorem co_subst_norecs {Δ : TypeCtx} (hr : Δ.recs = []) {ρ : Subst}
    (hρ : ∀ x, ρ (.idx x) = none) : ∀ {k : TKind} (t : Ty k), TyOk Δ t → t.subst ρ = t := by
  intro k t
  induction t with
  | idx x => intro _; simp [Ty.subst, hρ]
  | recv i => intro h; cases h with | recv hx => simp [hr] at hx
  | defn g i => intro _; exact Ty.recFree_def _ ρ hρ
  | _ => intro h; cases h <;> simp_all [Ty.subst]

theorem co_def_rho (subs : Ty (.list .sub)) (d : DefType) : d.subst (unrollSubst subs) = d :=
  Ty.recFree_def d _ (fun _ => rfl)

theorem co_rho_recv {subs : Ty (.list .sub)} {j : Nat} (hj : j < subs.length) :
    (Ty.recv j).subst (unrollSubst subs) = .dt (.defn (.group subs) j) := by
  simp [Ty.subst, unrollSubst, hj]

theorem co_unroll_defn {subs : Ty (.list .sub)} {i : Nat} {st : CSubType}
    (hst : subs.toList[i]? = some st) :
    unrolldt (.defn (.group subs) i) = some (st.subst (unrollSubst subs)) := by
  rw [unrolldt_defn, hst]; rfl

theorem co_recs_lt {Δ₁ : TypeCtx} {subs : Ty (.list .sub)} (hrecs : Δ₁.recs = subs.toList)
    {j : Nat} {st : CSubType} (h : Δ₁.recs[j]? = some st) : j < subs.length := by
  rw [hrecs] at h
  exact (List.getElem?_eq_some_iff.1 h).1

/-- The unrolled declared supertypes of a valid defined type are not `REC`. -/
theorem co_unroll_super_norecv {Δ : TypeCtx} {b : DefType} (hb : TyOk Δ b) {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType}
    (hu : unrolldt b = some (.sub fin sups ct)) {u : CTypeUse} (hmem : u ∈ sups.toList) :
    ∀ i, u ≠ .recv i := by
  cases hb with
  | @defn _ subs i hg hi =>
    rw [unrolldt_defn] at hu
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
        | idx x => intro j; simp [Ty.subst, unrollSubst]
        | recv j =>
          cases hok with
          | recv h =>
            have hj : j < subs.length := by
              have := (List.getElem?_eq_some_iff.1 h).1
              simpa [TypeCtx.withRecs, Ty.length] using this
            intro k; simp [Ty.subst, unrollSubst, hj]
        | dt e => intro k; simp [Ty.subst]

theorem co_heap_subst_ne_bot {h : CHeapType} {σ : Subst} (hb : h ≠ .bot) : h.subst σ ≠ .bot := by
  cases h <;> simp_all [Ty.subst]

theorem co_subst_app {k : TKind} (σ : Subst) (x y : Ty (.list k)) :
    (x.app y).subst σ = (x.subst σ).app (y.subst σ) := by
  have inj : ∀ a b : Ty (.list k), a.toList = b.toList → a = b := fun a b h => by
    rw [← Ty.ofList_toList a, h, Ty.ofList_toList]
  apply inj
  simp [Ty.app, Ty.toList_subst]

/-! ## Substituting a valid group for its `REC` variables -/

theorem co_rho_ok {Δ Δ₁ : TypeCtx} {subs : Ty (.list .sub)} (hrecs : Δ₁.recs = subs.toList)
    (htypes : Δ₁.types = Δ.types) (hg : GroupOk2 Δ₁ (.group subs) 0) :
    ∀ {k : TKind} (t : Ty k), TyOk Δ₁ t → TyOk Δ (t.subst (unrollSubst subs)) := by
  have hΔ₁ : Δ₁ = Δ.withRecs subs.toList := by
    cases Δ₁; cases Δ; simp_all [TypeCtx.withRecs]
  subst hΔ₁
  intro k t ht
  refine Execution.Core.TyOk.subst_recs (Δ := Δ) (Δ' := Δ.withRecs subs.toList) rfl
    (fun _ => rfl) ?_ t ht
  intro i st h
  have hi : i < subs.length := co_recs_lt hrecs h
  exact ⟨_, by simp [unrollSubst, hi], .dt (.defn hg hi)⟩

theorem co_sub_rho {Δ Δ₁ : TypeCtx} {subs : Ty (.list .sub)} (hrecs : Δ₁.recs = subs.toList)
    (htypes : Δ₁.types = Δ.types) (hg : GroupOk2 Δ₁ (.group subs) 0)
    (hT : ∀ d ∈ Δ.types, TyOk {} d) :
    ∀ {k : TKind} {a b : Ty k}, Validation.Sub Δ₁ a b → TyOk Δ₁ a → TyOk Δ₁ b →
      Validation.Sub Δ (a.subst (unrollSubst subs)) (b.subst (unrollSubst subs))
  | _, _, _, .heapRefl, _, _ => .heapRefl
  | _, _, _, .heapTrans hok h₁ h₂, ha, hb =>
    .heapTrans (co_rho_ok hrecs htypes hg _ hok) (co_sub_rho hrecs htypes hg hT h₁ ha hok)
      (co_sub_rho hrecs htypes hg hT h₂ hok hb)
  | _, _, _, .eqAny, _, _ => .eqAny
  | _, _, _, .i31Eq, _, _ => .i31Eq
  | _, _, _, .structEq, _, _ => .structEq
  | _, _, _, .arrayEq, _, _ => .arrayEq
  | _, _, _, .defStruct h, _, _ => by
    show Validation.Sub Δ (.use (.dt (Ty.subst _ _))) _
    rw [co_def_rho]; exact .defStruct h
  | _, _, _, .defArray h, _, _ => by
    show Validation.Sub Δ (.use (.dt (Ty.subst _ _))) _
    rw [co_def_rho]; exact .defArray h
  | _, _, _, .defFunc h, _, _ => by
    show Validation.Sub Δ (.use (.dt (Ty.subst _ _))) _
    rw [co_def_rho]; exact .defFunc h
  | _, _, _, .defDef h, ha, hb =>
    .defDef (co_sub_rho hrecs htypes hg hT h ha.use_inv.dt_inv hb.use_inv.dt_inv)
  | _, _, _, .idxL (x := x) (d := d) hx hs, _, hb => by
    have hd : TyOk Δ₁ (Ty.use (Ty.dt d)) :=
      .use (.dt (TyOk.of_empty _ (hT d (htypes ▸ List.mem_of_getElem? hx))))
    have := co_sub_rho hrecs htypes hg hT hs hd hb
    simp only [Ty.subst, co_def_rho] at this
    show Validation.Sub Δ (.use ((unrollSubst subs (.idx x)).getD (.idx x))) _
    exact .idxL (htypes ▸ hx) this
  | _, _, _, .idxR (x := x) (d := d) hx hs, ha, _ => by
    have hd : TyOk Δ₁ (Ty.use (Ty.dt d)) :=
      .use (.dt (TyOk.of_empty _ (hT d (htypes ▸ List.mem_of_getElem? hx))))
    have := co_sub_rho hrecs htypes hg hT hs ha hd
    simp only [Ty.subst, co_def_rho] at this
    show Validation.Sub Δ _ (.use ((unrollSubst subs (.idx x)).getD (.idx x)))
    exact .idxR (htypes ▸ hx) this
  | _, _, _, .recStruct (i := i) (sups := sups) (fs := fs) h, _, _ => by
    have hi := co_recs_lt hrecs h
    rw [hrecs] at h
    show Validation.Sub Δ (.use ((Ty.recv i).subst _)) _
    rw [co_rho_recv hi]
    exact .defStruct ⟨co_unroll_defn h⟩
  | _, _, _, .recArray (i := i) h, _, _ => by
    have hi := co_recs_lt hrecs h
    rw [hrecs] at h
    show Validation.Sub Δ (.use ((Ty.recv i).subst _)) _
    rw [co_rho_recv hi]
    exact .defArray ⟨co_unroll_defn h⟩
  | _, _, _, .recFunc (i := i) h, _, _ => by
    have hi := co_recs_lt hrecs h
    rw [hrecs] at h
    show Validation.Sub Δ (.use ((Ty.recv i).subst _)) _
    rw [co_rho_recv hi]
    exact .defFunc ⟨co_unroll_defn h⟩
  | _, _, _, .recSub (i := i) (j := j) (sups := sups) (u := u) h hj, _, hb => by
    have hi := co_recs_lt hrecs h
    rw [hrecs] at h
    have hun := co_unroll_defn h
    simp only [Ty.subst] at hun
    have hj' : (sups.subst (unrollSubst subs)).toList[j]? = some (u.subst (unrollSubst subs)) := by
      rw [Ty.toList_subst, List.getElem?_map, hj]; rfl
    show Validation.Sub Δ (.use ((Ty.recv i).subst _)) (.use (u.subst _))
    rw [co_rho_recv hi]
    have hu := hb.use_inv
    cases u with
    | idx x =>
      cases hu with
      | idx hx =>
        rw [htypes] at hx
        exact .idxR hx (.defDef (.defSuper hun hj' (.idxL hx .heapRefl)))
    | recv j' =>
      cases hu with
      | recv hx =>
        have hj'' := co_recs_lt hrecs hx
        rw [co_rho_recv hj''] at hj' ⊢
        exact .defDef (.defSuper hun hj' .heapRefl)
    | dt e =>
      simp only [Ty.subst, co_def_rho] at hj' ⊢
      exact .defDef (.defSuper hun hj' .heapRefl)
  | _, _, _, .none hs hb', ha, hb =>
    .none (co_sub_rho hrecs htypes hg hT hs hb (.abs _)) (co_heap_subst_ne_bot hb')
  | _, _, _, .nofunc hs hb', ha, hb =>
    .nofunc (co_sub_rho hrecs htypes hg hT hs hb (.abs _)) (co_heap_subst_ne_bot hb')
  | _, _, _, .noexn hs hb', ha, hb =>
    .noexn (co_sub_rho hrecs htypes hg hT hs hb (.abs _)) (co_heap_subst_ne_bot hb')
  | _, _, _, .noextern hs hb', ha, hb =>
    .noextern (co_sub_rho hrecs htypes hg hT hs hb (.abs _)) (co_heap_subst_ne_bot hb')
  | _, _, _, .bot, _, _ => .bot
  | _, _, _, .refNonNull h, ha, hb =>
    .refNonNull (co_sub_rho hrecs htypes hg hT h ha.ref_inv hb.ref_inv)
  | _, _, _, .refNull h, ha, hb =>
    .refNull (co_sub_rho hrecs htypes hg hT h ha.ref_inv hb.ref_inv)
  | _, _, _, .num, _, _ => .num
  | _, _, _, .vec, _, _ => .vec
  | _, _, _, .refv h, ha, hb => .refv (co_sub_rho hrecs htypes hg hT h ha.refv_inv hb.refv_inv)
  | _, _, _, .botv, _, _ => .botv
  | _, _, _, .val h, ha, hb => .val (co_sub_rho hrecs htypes hg hT h ha.val_inv hb.val_inv)
  | _, _, _, .pack, _, _ => .pack
  | _, _, _, .fieldConst h, ha, hb =>
    .fieldConst (co_sub_rho hrecs htypes hg hT h ha.field_inv hb.field_inv)
  | _, _, _, .fieldVar h₁ h₂, ha, hb =>
    .fieldVar (co_sub_rho hrecs htypes hg hT h₁ ha.field_inv hb.field_inv)
      (co_sub_rho hrecs htypes hg hT h₂ hb.field_inv ha.field_inv)
  | _, _, _, .struct (fs₁ := fs₁) (extra := extra) h, ha, hb => by
    have := co_sub_rho hrecs htypes hg hT h ha.struct_inv.app_left hb.struct_inv
    show Validation.Sub Δ (.struct ((fs₁.app extra).subst _)) _
    rw [co_subst_app]
    exact .struct this
  | _, _, _, .array h, ha, hb => .array (co_sub_rho hrecs htypes hg hT h ha.array_inv hb.array_inv)
  | _, _, _, .func hp hr, ha, hb =>
    .func (co_sub_rho hrecs htypes hg hT hp hb.func_inv.1 ha.func_inv.1)
      (co_sub_rho hrecs htypes hg hT hr ha.func_inv.2 hb.func_inv.2)
  | _, _, _, .defRefl h, _, _ => by
    rw [co_def_rho, co_def_rho]
    exact .defRefl (htypes ▸ h)
  | _, _, _, .defSuper (d₁ := d₁) (u := u) h hj hs, ha, hb => by
    have hu : TyOk Δ₁ (.use u) := ha.unroll_super h (List.mem_of_getElem? hj)
    have hnr := co_unroll_super_norecv ha h (List.mem_of_getElem? hj)
    have := co_sub_rho hrecs htypes hg hT hs hu (.use (.dt hb))
    have hu' : u.subst (unrollSubst subs) = u := by
      cases u with
      | idx x => rfl
      | recv i => exact absurd rfl (hnr i)
      | dt e => simp [Ty.subst, co_def_rho]
    simp only [Ty.subst, hu', co_def_rho] at this
    rw [co_def_rho, co_def_rho]
    exact .defSuper h hj this
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .cons h hl, ha, hb =>
    .cons (co_sub_rho hrecs htypes hg hT h ha.cons_inv.1 hb.cons_inv.1)
      (co_sub_rho hrecs htypes hg hT hl ha.cons_inv.2 hb.cons_inv.2)

/-! ## Declared supertypes of valid defined types -/

/-- The expansion of a valid defined type is a subtype of the expansion of each of
its (resolved) declared supertypes, which are valid. -/
theorem co_super_sub {Δ : TypeCtx} (hT : ∀ d ∈ Δ.types, TyOk {} d) {e D' : DefType}
    (he : TyOk Δ e) {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (hu : unrolldt e = some (.sub fin sups ct)) {u : CTypeUse} (hmem : u ∈ sups.toList)
    (hr : Δ.resolve u = some D') :
    TyOk Δ D' ∧ ∃ ct', Expand D' ct' ∧ Validation.Sub Δ ct ct' := by
  cases he with
  | @defn _ subs i hg hi =>
    rw [unrolldt_defn] at hu
    cases hst : subs.toList[i]? with
    | none => simp [hst] at hu
    | some st =>
      rw [hst] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      have hso := GroupOk2.get subs hg hst
      rw [Nat.zero_add] at hso
      cases st with
      | sub fin0 sups0 ct0 =>
        simp only [Ty.subst, Ty.sub.injEq] at hu
        obtain ⟨rfl, rfl, rfl⟩ := hu
        cases hso with
        | noSuper hct => simp [Ty.subst] at hmem
        | oneSuper hu0 hb hunroll hct hsub =>
          simp only [Ty.subst, Ty.toList_cons, Ty.toList_nil, List.mem_singleton] at hmem
          subst hmem
          have h0 : ∀ {D : DefType} {ct1 : CCompType} {fin1 : Bool} {sups1 : Ty (.list .use)},
              TyOk Δ D → unrolldt D = some (.sub fin1 sups1 ct1) →
              ct1.subst (unrollSubst subs) = ct1 ∧ TyOk (Δ.withRecs subs.toList) ct1 := by
            intro D ct1 fin1 sups1 hD hun
            refine ⟨co_subst_norecs (Δ := { types := Δ.types }) rfl (fun _ => rfl) ct1
              (Expand.tyOk (TyOk.def_congr (Δ₁ := Δ) (Δ₂ := { types := Δ.types }) rfl hD) ⟨hun⟩), ?_⟩
            exact Expand.tyOk (TyOk.def_congr (Δ₁ := Δ) (Δ₂ := Δ.withRecs subs.toList) rfl hD) ⟨hun⟩
          rename_i u0 _ _
          cases u0 with
          | idx x =>
            simp only [Ty.subst, unrollSubst, Option.getD_none, TypeCtx.resolve] at hr
            simp only [TypeCtx.unrollUse, TypeCtx.withRecs, hr] at hunroll
            have hD' : TyOk Δ D' := TyOk.of_empty _ (hT _ (List.mem_of_getElem? hr))
            obtain ⟨h1, h2⟩ := h0 hD' hunroll
            have := co_sub_rho (Δ := Δ) (Δ₁ := Δ.withRecs subs.toList) rfl rfl hg hT hsub hct h2
            rw [h1] at this
            exact ⟨hD', _, ⟨hunroll⟩, this⟩
          | recv j =>
            cases hu0 with
            | recv hx =>
              have hj := co_recs_lt (Δ₁ := Δ.withRecs subs.toList) rfl hx
              rw [co_rho_recv hj] at hr
              simp only [TypeCtx.resolve, Option.some.injEq] at hr
              subst hr
              simp only [TypeCtx.unrollUse, TypeCtx.withRecs] at hunroll
              have hct1 := (GroupOk2.get subs hg hunroll).body
              refine ⟨.defn hg hj, _, ⟨co_unroll_defn hunroll⟩, ?_⟩
              exact co_sub_rho (Δ := Δ) (Δ₁ := Δ.withRecs subs.toList) rfl rfl hg hT hsub hct hct1
          | dt d0 =>
            simp only [Ty.subst, co_def_rho, TypeCtx.resolve, Option.some.injEq] at hr
            subst hr
            simp only [TypeCtx.unrollUse] at hunroll
            have hd0 : TyOk Δ _ := TyOk.def_congr (Δ₁ := Δ.withRecs subs.toList) (Δ₂ := Δ) rfl hu0.dt_inv
            obtain ⟨h1, h2⟩ := h0 hd0 hunroll
            have := co_sub_rho (Δ := Δ) (Δ₁ := Δ.withRecs subs.toList) rfl rfl hg hT hsub hct h2
            rw [h1] at this
            exact ⟨hd0, _, ⟨hunroll⟩, this⟩

/-! ## Chains of subtypings from a defined function type -/

theorem co_expand_cs {Δ : TypeCtx} {d : DefType} {ct : CCompType} (h : Expand d ct) :
    Expand (d.subst Δ.closSubst) (ct.subst Δ.closSubst) := by
  obtain ⟨hu⟩ := h
  rename_i fin sups
  exact .mk (fin := fin) (sups := sups.subst Δ.closSubst) (by
    rw [unrolldt_subst _ (TypeCtx.closSubst_recv Δ) (TypeCtx.closSubst_recFree Δ), hu]; rfl)

theorem co_closed_cs {Δ : TypeCtx} (hΔ : Δ.Ok) {x : Nat} {d : DefType}
    (hx : Δ.types[x]? = some d) : d.subst Δ.closSubst = d :=
  Ty.subst_closed d _ (TypeCtx.closSubst_recv Δ) (hΔ d (List.mem_of_getElem? hx)).1

/-- A defined type (a closed representative) whose expansion is a function type
with `ps.length` parameters and results above `rs`. -/
def CoFA (Δ : TypeCtx) (ps rs : Ty (.list .val)) (e : DefType) : Prop :=
  TyOk Δ e ∧ ∃ ps₂ rs₂, Expand e (.func ps₂ rs₂) ∧ ps.length = ps₂.length ∧
    ResultSub Δ rs.toList rs₂.toList

/-- The heap types reachable from such a defined type. -/
def CoGH (Δ : TypeCtx) (ps rs : Ty (.list .val)) : CHeapType → Prop
  | .use (.dt d) => CoFA Δ ps rs (d.subst Δ.closSubst)
  | .use (.idx x) => ∃ d, Δ.types[x]? = some d ∧ CoFA Δ ps rs d
  | .abs .func => True
  | _ => False

def CoMotK (Δ : TypeCtx) (ps rs : Ty (.list .val)) : (k : TKind) → Ty k → Ty k → Prop
  | .heap, a, b => CoGH Δ ps rs a → CoGH Δ ps rs b
  | .def, a, b => CoFA Δ ps rs (a.subst Δ.closSubst) → CoFA Δ ps rs (b.subst Δ.closSubst)
  | _, _, _ => True

theorem co_chain {Δ : TypeCtx} (hΔ : Δ.Ok) (hT : ∀ d ∈ Δ.types, TyOk {} d)
    {ps rs : Ty (.list .val)} :
    ∀ {k : TKind} {a b : Ty k}, Validation.Sub Δ a b → CoMotK Δ ps rs k a b
  | _, _, _, .heapRefl => id
  | _, _, _, .heapTrans _ h₁ h₂ => fun h => co_chain hΔ hT h₂ (co_chain hΔ hT h₁ h)
  | _, _, _, .eqAny => fun h => by simp [CoGH] at h
  | _, _, _, .i31Eq => fun h => by simp [CoGH] at h
  | _, _, _, .structEq => fun h => by simp [CoGH] at h
  | _, _, _, .arrayEq => fun h => by simp [CoGH] at h
  | _, _, _, .defStruct he => fun h => by
    obtain ⟨_, ps₂, rs₂, hE, _⟩ := h
    have := Expand.func_eq (co_expand_cs (Δ := Δ) he) hE
    simp [Ty.subst] at this
  | _, _, _, .defArray he => fun h => by
    obtain ⟨_, ps₂, rs₂, hE, _⟩ := h
    have := Expand.func_eq (co_expand_cs (Δ := Δ) he) hE
    simp [Ty.subst] at this
  | _, _, _, .defFunc _ => fun _ => trivial
  | _, _, _, .defDef h => fun hf => co_chain hΔ hT h hf
  | _, _, _, .idxL (d := d) hx hs => fun h => by
    obtain ⟨d', hx', hf⟩ := h
    rw [hx] at hx'
    cases hx'
    apply co_chain hΔ hT hs
    show CoFA Δ ps rs (d.subst Δ.closSubst)
    rwa [co_closed_cs hΔ hx]
  | _, _, _, .idxR (d := d) hx hs => fun h => by
    have := co_chain hΔ hT hs h
    change CoFA Δ ps rs (d.subst Δ.closSubst) at this
    rw [co_closed_cs hΔ hx] at this
    exact ⟨d, hx, this⟩
  | _, _, _, .recStruct _ => fun h => by simp [CoGH] at h
  | _, _, _, .recArray _ => fun h => by simp [CoGH] at h
  | _, _, _, .recFunc _ => fun h => by simp [CoGH] at h
  | _, _, _, .recSub _ _ => fun h => by simp [CoGH] at h
  | _, _, _, .none _ _ => fun h => by simp [CoGH] at h
  | _, _, _, .nofunc _ _ => fun h => by simp [CoGH] at h
  | _, _, _, .noexn _ _ => fun h => by simp [CoGH] at h
  | _, _, _, .noextern _ _ => fun h => by simp [CoGH] at h
  | _, _, _, .bot => fun h => by simp [CoGH] at h
  | _, _, _, .refNonNull _ => trivial
  | _, _, _, .refNull _ => trivial
  | _, _, _, .num => trivial
  | _, _, _, .vec => trivial
  | _, _, _, .refv _ => trivial
  | _, _, _, .botv => trivial
  | _, _, _, .val _ => trivial
  | _, _, _, .pack => trivial
  | _, _, _, .fieldConst _ => trivial
  | _, _, _, .fieldVar _ _ => trivial
  | _, _, _, .struct _ => trivial
  | _, _, _, .array _ => trivial
  | _, _, _, .func _ _ => trivial
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial
  | _, _, _, .defRefl h => fun hf => by
    rw [hΔ.clos_eq, hΔ.clos_eq] at h
    rwa [← h]
  | _, _, _, .defSuper (d₁ := d₁) (fin := fin) (sups := sups) (ct := ct) (u := u) h hj hs =>
    fun hf => by
    obtain ⟨he, ps₂, rs₂, hE, hlen, hrs⟩ := hf
    have hun : unrolldt (d₁.subst Δ.closSubst) =
        some (.sub fin (sups.subst Δ.closSubst) (ct.subst Δ.closSubst)) := by
      rw [unrolldt_subst _ (TypeCtx.closSubst_recv Δ) (TypeCtx.closSubst_recFree Δ), h]; rfl
    have hmem : u.subst Δ.closSubst ∈ (sups.subst Δ.closSubst).toList := by
      rw [Ty.toList_subst]; exact List.mem_map_of_mem (List.mem_of_getElem? hj)
    have hnr := co_unroll_super_norecv he hun hmem
    have hok := he.unroll_super hun hmem
    obtain ⟨D', hD'r, hGH⟩ : ∃ D', Δ.resolve (u.subst Δ.closSubst) = some D' ∧
        (CoFA Δ ps rs D' → CoGH Δ ps rs (.use u)) := by
      cases u with
      | idx x =>
        cases hx : Δ.types[x]? with
        | none =>
          exfalso
          have e : (Ty.idx x).subst Δ.closSubst = .idx x := by
            simp [Ty.subst, TypeCtx.closSubst_idx, hx]
          rw [e] at hok
          cases hok with
          | use h' => cases h' with | idx h'' => simp [hx] at h''
        | some d' =>
          refine ⟨d', by simp [Ty.subst, TypeCtx.closSubst_idx, hx, TypeCtx.resolve], ?_⟩
          intro h
          exact ⟨d', hx, h⟩
      | recv i => exact absurd (by simp [Ty.subst, TypeCtx.closSubst_recv]) (hnr i)
      | dt d' => exact ⟨d'.subst Δ.closSubst, by simp [Ty.subst, TypeCtx.resolve], fun h => h⟩
    obtain ⟨hD', ct', hE', hsub⟩ := co_super_sub hT he hun hmem hD'r
    have hct : ct.subst Δ.closSubst = .func ps₂ rs₂ := Expand.func_eq ⟨hun⟩ hE
    rw [hct] at hsub
    cases hsub with
    | func hp hr =>
      apply co_chain hΔ hT hs
      apply hGH
      refine ⟨hD', _, _, hE', ?_, ?_⟩
      · rw [hlen]; simp only [Ty.length]; exact (Sub.list_length hp).symm
      · exact forall₂_sub_trans hΔ hrs ((Sub.list_iff _ _ _).1 hr) (Expand.func_ok he hE).2

/-! ## Function references -/

def CoGR (Δ : TypeCtx) (ps rs : Ty (.list .val)) : CRefType → Prop
  | .ref _ h => CoGH Δ ps rs h

theorem co_ref_step {Δ : TypeCtx} (hΔ : Δ.Ok) (hT : ∀ d ∈ Δ.types, TyOk {} d)
    {ps rs : Ty (.list .val)} {r r' : CRefType} (h : Validation.Sub Δ r r') :
    CoGR Δ ps rs r → CoGR Δ ps rs r' := by
  cases h with
  | refNonNull hh => exact co_chain hΔ hT hh
  | refNull hh => exact co_chain hΔ hT hh

def CoGV (Δ : TypeCtx) (ps rs : Ty (.list .val)) : CValType → Prop
  | .refv r => CoGR Δ ps rs r
  | _ => False

theorem co_val_step {Δ : TypeCtx} (hΔ : Δ.Ok) (hT : ∀ d ∈ Δ.types, TyOk {} d)
    {ps rs : Ty (.list .val)} {t t' : CValType} (h : Validation.Sub Δ t t') :
    CoGV Δ ps rs t → CoGV Δ ps rs t' := by
  cases h with
  | refv hh => exact co_ref_step hΔ hT hh
  | botv => intro h; simp [CoGV] at h
  | num => intro h; simp [CoGV] at h
  | vec => intro h; simp [CoGV] at h

theorem co_refok {H : Type} {s : Store H} {Δ : TypeCtx} (hΔ : Δ.Ok)
    (hT : ∀ d ∈ Δ.types, TyOk {} d) {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hfi : TyOk {} fi.type) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    {rt : CRefType} (h : RefOk s (.func a) rt) : CoGR Δ ps rs rt := by
  generalize hr : Ref.func a = r at h
  induction h with
  | func hf' =>
    cases hr
    rw [hf] at hf'
    cases hf'
    show CoFA Δ ps rs (fi.type.subst Δ.closSubst)
    have hcl : fi.type.freeIdx = [] := by
      have := TyOk.freeIdx_lt hfi
      cases hfr : fi.type.freeIdx with
      | nil => rfl
      | cons y l => have := this y (by simp [hfr]); simp at this
    rw [Ty.subst_closed _ _ (TypeCtx.closSubst_recv Δ) hcl]
    exact ⟨TyOk.of_empty _ hfi, ps, rs, he, rfl, ResultSub.refl _ _⟩
  | sub _ _ hs ih =>
    exact co_ref_step hΔ hT (Execution.Core.Sub.weakenE hs Δ rfl (fun _ _ h => by simp at h))
      (ih hr)
  | _ => cases hr

/-! ## Closure -/

theorem co_cs_idem {Δ : TypeCtx} (hΔ : Δ.Ok) :
    ∀ {k : TKind} (t : Ty k), (t.subst Δ.closSubst).subst Δ.closSubst = t.subst Δ.closSubst := by
  intro k t
  induction t with
  | idx x =>
    cases hx : Δ.types[x]? with
    | none => simp [Ty.subst, TypeCtx.closSubst_idx, hx]
    | some d =>
      simp only [Ty.subst, TypeCtx.closSubst_idx, hx, Option.map_some, Option.getD_some]
      rw [co_closed_cs hΔ hx]
  | recv i => simp [Ty.subst, TypeCtx.closSubst_recv]
  | group subs ih =>
    simp only [Ty.subst, Subst.minusRecs_eq (TypeCtx.closSubst_recv Δ)]
    rw [ih]
  | _ => simp_all [Ty.subst]

theorem co_heap_eqclos {Δ : TypeCtx} (hΔ : Δ.Ok) :
    ∀ (a b : CHeapType), a.subst Δ.closSubst = b.subst Δ.closSubst → Validation.Sub Δ a b
  | .abs x, .abs y, e => by simp [Ty.subst] at e; subst e; exact .heapRefl
  | .bot, .bot, _ => .heapRefl
  | .use u, .use u', e => by
    simp only [Ty.subst, Ty.use.injEq] at e
    exact Sub.use_of_subst_eq hΔ e
  | .abs _, .bot, e => by simp [Ty.subst] at e
  | .abs _, .use _, e => by simp [Ty.subst] at e
  | .bot, .abs _, e => by simp [Ty.subst] at e
  | .bot, .use _, e => by simp [Ty.subst] at e
  | .use _, .abs _, e => by simp [Ty.subst] at e
  | .use _, .bot, e => by simp [Ty.subst] at e

theorem co_val_eqclos {Δ : TypeCtx} (hΔ : Δ.Ok) :
    ∀ (a b : CValType), a.subst Δ.closSubst = b.subst Δ.closSubst → Validation.Sub Δ a b
  | .num t, b, e => by cases b <;> simp [Ty.subst] at e; subst e; exact .num
  | .vec t, b, e => by
    cases b <;> simp [Ty.subst] at e
    rename_i t'
    cases t; cases t'; exact .vec
  | .botv, _, _ => .botv
  | .refv (.ref n h), b, e => by
    cases b with
    | refv r =>
      cases r with
      | ref n' h' =>
        simp only [Ty.subst, Ty.refv.injEq, Ty.ref.injEq] at e
        obtain ⟨rfl, e⟩ := e
        have hh := co_heap_eqclos hΔ h h' e
        cases n
        · exact .refv (.refNonNull hh)
        · exact .refv (.refNull hh)
    | _ => simp [Ty.subst] at e

/-! ## The lemma -/

/-- **Function subtyping, as seen by `call_ref`.** -/
theorem co_K' {H : Type} {s : Store H} {Δ : TypeCtx} (hΔT : ∀ d ∈ Δ.types, TyOk {} d)
    (hS : StoreOk s) {a : Nat} {fi : FuncInst H} {ps rs ps' rs' : Ty (.list .val)} {d : DefType}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hr : ValTo s Δ (.ref (.func a)) (.refT true (.defHeap d))) (_hd : TyOk Δ d)
    (he' : Expand d (.func ps' rs')) :
    ps.length = ps'.length ∧ ResultSub Δ rs.toList rs'.toList := by
  have hcl : ∀ d ∈ Δ.types, d.freeIdx = [] := by
    intro d hd
    have := TyOk.freeIdx_lt (hΔT d hd)
    cases hfr : d.freeIdx with
    | nil => rfl
    | cons y l => have := this y (by simp [hfr]); simp at this
  have hΔ : Δ.Ok := fun d hd => ⟨hcl d hd, TyOk.of_empty _ (hΔT d hd)⟩
  have hfi : TyOk {} fi.type := by
    have := hS.funcs fi (List.mem_of_getElem? hf)
    cases this with
    | wasm hdt => exact hdt
    | host hdt => exact hdt
  obtain ⟨t₀, hv, hc⟩ := hr
  cases hv with
  | @ref r rt hro =>
    have h0 : CoGV Δ ps rs (.refv rt) := co_refok hΔ hΔT hfi hf he hro
    have h1' : ∀ T, Relation.ReflTransGen (Validation.Sub Δ) (.refv rt) T → CoGV Δ ps rs T := by
      intro T hc
      induction hc with
      | refl => exact h0
      | tail _ hst ih => exact co_val_step hΔ hΔT hst ih
    have h1 : CoGV Δ ps rs (.refT true (.defHeap d)) := h1' _ hc
    change CoFA Δ ps rs (d.subst Δ.closSubst) at h1
    obtain ⟨hdc, ps₂, rs₂, hE, hlen, hrs⟩ := h1
    have hE' := co_expand_cs (Δ := Δ) he'
    have heq := Expand.func_eq hE hE'
    simp only [Ty.subst, Ty.func.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨by rw [hlen, Ty.length_subst], ?_⟩
    have hmid : ResultOk Δ (rs'.subst Δ.closSubst).toList := (Expand.func_ok hdc hE').2
    have hback : ResultSub Δ (rs'.subst Δ.closSubst).toList rs'.toList := by
      rw [Ty.toList_subst]
      have : ∀ l : List CValType,
          List.Forall₂ (Validation.Sub Δ) (l.map (·.subst Δ.closSubst)) l := by
        intro l
        induction l with
        | nil => exact .nil
        | cons y l ih =>
          exact .cons (co_val_eqclos hΔ _ _ (co_cs_idem hΔ y)) ih
      exact this _
    exact forall₂_sub_trans hΔ hrs hback hmid

end Silmaril.Wasm.SingleThreaded
