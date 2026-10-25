module

public import Silmaril.Wasm.Validation.RollClosed.Roll

@[expose] public section

/-! # Rolling: the closed defined types of a valid module are valid in `{}`

`Types_ok` checks each recursive group with the *index-based* `Rectype_ok: OK(x)`
against a context that already holds the group's rolled, closed defined types.
Instantiation needs the *rolled* `Deftype_ok` judgment (`Rectype_ok2` with `REC i`)
in the empty context. This file proves the bridge (Rossberg's roll/unroll argument):

1. `Rectype_ok: OK(x)` gives validity of the rolled types in the module context
   `Δ` (`tyOk_rolled`), so `Δ` is a well-formed closed context;
2. subtyping premises of the group are then decided by the algorithmic checker in `Δ`
   (`Sub.complete`), and a successful check between unrolled types folds back into
   the group context (`RollClosed.comp_fold`), giving `Rectype_ok2` in `{}`.
-/

namespace Silmaril.Wasm.Validation

namespace RollClosed

open DefInv

/-- The types of the context after adding the rolled group. -/
abbrev Dof (T : List DefType) (sts : List SubType) : List DefType :=
  T ++ (List.range sts.length).map (Ty.defn (.group (rsubs T sts)))

theorem _root_.Silmaril.Wasm.Validation.SubTypeOkAt.hctRC {C : Context} {st : SubType} {x : Nat} (h : SubTypeOkAt C st x) :
    TyOk C.toTypeCtx (C.closeComp st.body) := by
  cases h with
  | noSuper hct => exact hct
  | oneSuper _ _ _ hct _ => exact hct

theorem _root_.Silmaril.Wasm.Validation.RecTypeOkAt.getRC {C : Context} : ∀ {sts : List SubType} {x : Nat}, RecTypeOkAt C sts x →
    ∀ k (hk : k < sts.length), SubTypeOkAt C sts[k] (x + k)
  | _, _, .cons h _, 0, _ => by simpa using h
  | _, _, .cons _ hs, k + 1, hk => by
    have := RecTypeOkAt.getRC hs k (by simpa using hk)
    simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem groupOk2_of_get {Δ : TypeCtx} : ∀ {s : Ty (.list .sub)} {i : Nat},
    (∀ k st, s.toList[k]? = some st → SubOk2 Δ st (i + k)) → GroupOk2 Δ (.group s) i
  | .nil, _, _ => .nil
  | .cons st l, i, h =>
    .cons (by simpa using h 0 st rfl)
      (groupOk2_of_get fun k st' hk => by
        have := h (k + 1) st' (by simpa using hk)
        rwa [show i + (k + 1) = i + 1 + k by omega] at this)

section

variable (T : List DefType) (sts : List SubType)

theorem u_lt {y : Nat} (h : y < T.length) :
    ((Ty.idx y : CTypeUse).subst (rho T.length sts.length)).subst (Subst.all (T.map .dt)) =
      .dt T[y] := by
  have e1 : (Ty.idx y : CTypeUse).subst (rho T.length sts.length) = .idx y := by
    simp [Ty.subst, rho, show ¬ T.length ≤ y by omega]
  rw [e1]
  simp [Ty.subst, Subst.all, List.getElem?_map, List.getElem?_eq_getElem h]

theorem u_ge {y : Nat} (h1 : T.length ≤ y) (h2 : y < T.length + sts.length) :
    ((Ty.idx y : CTypeUse).subst (rho T.length sts.length)).subst (Subst.all (T.map .dt)) =
      .recv (y - T.length) := by
  have e1 : (Ty.idx y : CTypeUse).subst (rho T.length sts.length) = .recv (y - T.length) := by
    simp [Ty.subst, rho, h1, h2]
  rw [e1]; rfl

theorem D_lt {y : Nat} (h : y < T.length) : (Dof T sts)[y]? = T[y]? :=
  List.getElem?_append_left h

theorem D_ge {y : Nat} (h1 : T.length ≤ y) (h2 : y < T.length + sts.length) :
    (Dof T sts)[y]? = some (.defn (.group (rsubs T sts)) (y - T.length)) := by
  rw [List.getElem?_append_right h1, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem member_eq {k : Nat} (hk : k < sts.length) :
    (rsubs T sts).toList[k]? = some (.sub sts[k].final_
      (((Ty.ofList (sts[k].supertypes.map liftTypeIdx)).subst (rho T.length sts.length)).subst
        (Subst.all (T.map .dt)))
      (((liftComp sts[k].body).subst (rho T.length sts.length)).subst (Subst.all (T.map .dt)))) := by
  rw [rsubs_get, List.getElem?_eq_getElem hk]
  rfl

end

section Main

variable {T : List DefType} {sts : List SubType}

/-- Free indices of the source members are bounded by the extended context. -/
theorem bound_of_ok {C' : Context} (hC : C'.types = Dof T sts) (hok : RecTypeOkAt C' sts T.length)
    {k : Nat} (hk : k < sts.length) :
    (∀ y ∈ (liftComp sts[k].body).freeIdx, y < T.length + sts.length) ∧
    (∀ y ∈ (Ty.ofList (sts[k].supertypes.map liftTypeIdx)).freeIdx, y < T.length + sts.length) := by
  have hb := hok.freeIdx_lt sts[k] (List.getElem_mem hk)
  have hl : C'.types.length = T.length + sts.length := by simp [hC]
  rw [hl] at hb
  exact ⟨fun y hy => hb y (by simp [liftSub, Ty.freeIdx, hy]),
    fun y hy => hb y (by simp [liftSub, Ty.freeIdx, hy])⟩

theorem src_supers (st : SubType) : Src (Ty.ofList (st.supertypes.map liftTypeIdx)) :=
  src_ofList (by simp only [List.mem_map]; rintro _ ⟨x, _, rfl⟩; trivial)

theorem goodSubs (hT : ∀ d ∈ T, TyOk {} d) {C' : Context} (hC : C'.types = Dof T sts)
    (hok : RecTypeOkAt C' sts T.length) : GoodSubs (rsubs T sts) := by
  intro fin sups b hmem
  obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hmem
  have hk' : k < sts.length := by rw [← length_rsubs T sts]; exact hk
  have hget := member_eq T sts hk'
  rw [List.getElem?_eq_getElem hk, hkeq, Option.some.injEq, Ty.sub.injEq] at hget
  obtain ⟨-, rfl, rfl⟩ := hget
  have hsz := Ty.size_lt_of_mem hmem
  simp only [Ty.size] at hsz
  have hl : (rsubs T sts).length = sts.length := length_rsubs T sts
  obtain ⟨hb1, hb2⟩ := bound_of_ok hC hok hk'
  have conv : ∀ {k : TKind} (t : Ty k), Lv sts.length (fun e => e ∈ T) t →
      t.size < (rsubs T sts).size → Lv (rsubs T sts).length (OkS (rsubs T sts)) t := by
    intro k t h hs
    refine Lv.mono (by omega) ?_ t (Lv.size t h (le_of_lt hs))
    rintro e ⟨he, hes⟩
    exact ⟨hT e he, by omega⟩
  exact ⟨conv _ (lv_roll T _ _ _ (src_supers _) hb2 le_rfl) (by omega),
    conv _ (lv_roll T _ _ _ (src_liftComp _) hb1 le_rfl) (by omega)⟩

theorem closeComp_eq {C' : Context} (hC : C'.types = Dof T sts) (hok : RecTypeOkAt C' sts T.length)
    {k : Nat} (hk : k < sts.length) :
    C'.closeComp sts[k].body =
      (((liftComp sts[k].body).subst (rho T.length sts.length)).subst
        (Subst.all (T.map .dt))).subst (unrollSubst (rsubs T sts)) := by
  rw [roll_unroll T sts.length (rsubs T sts) (length_rsubs T sts) _ (src_liftComp _)
    (bound_of_ok hC hok hk).1]
  simp only [Context.closeComp, Ty.substAll, hC]

theorem ctx_eq {C' : Context} (hC : C'.types = Dof T sts) (hr : C'.recs = []) :
    C'.toTypeCtx = ⟨Dof T sts, []⟩ := by
  rw [show C'.toTypeCtx = ⟨C'.types, C'.recs⟩ from rfl, hC, hr]

theorem tyOk_T (_hT : ∀ d ∈ T, TyOk {} d) {C' : Context} (hC : C'.types = Dof T sts)
    (hr : C'.recs = []) {k : TKind} {t : Ty k} (h : TyOk {} t) : TyOk C'.toTypeCtx t := by
  rw [ctx_eq hC hr]
  exact TyOk.wkTypesRC (Dof T sts) h rfl

/-- Step 1: the rolled types are valid in the extended module context. -/
theorem tyOk_rolled (hT : ∀ d ∈ T, TyOk {} d) {C' : Context} (hC : C'.types = Dof T sts)
    (hr : C'.recs = []) (hok : RecTypeOkAt C' sts T.length) :
    GroupOk2 (C'.toTypeCtx.withRecs (rsubs T sts).toList) (.group (rsubs T sts)) 0 := by
  have hl : (rsubs T sts).length = sts.length := length_rsubs T sts
  by_cases hA : ∃ k, ∃ hk : k < sts.length, ∃ y ∈ (liftComp sts[k].body).freeIdx, T.length ≤ y
  · -- some member mentions the group: its validity premise contains the group's
    obtain ⟨k, hk, y, hy, hge⟩ := hA
    have hct := (hok.getRC k hk).hctRC
    have hlt := (bound_of_ok hC hok hk).1 y hy
    have hσ : Subst.all ((Dof T sts).map .dt) (.idx y) =
        some (.dt (.defn (.group (rsubs T sts)) (y - T.length))) := by
      simp only [Subst.all, List.getElem?_map, D_ge T sts hge hlt, Option.map_some]
    have hct' : TyOk C'.toTypeCtx ((liftComp sts[k].body).subst
        (Subst.all ((Dof T sts).map .dt))) := by
      simpa only [Context.closeComp, Ty.substAll, hC] using hct
    have := tyOk_extract _ (src_liftComp _) hct' y hy _ hσ
    cases this with
    | defn hg _ => exact hg
  · -- no member mentions the group in its body: check each member directly
    push Not at hA
    refine groupOk2_of_get fun k st' hst' => ?_
    have hk : k < sts.length := by
      have := (List.getElem?_eq_some_iff.1 hst').1
      rw [← hl]; exact this
    rw [member_eq T sts hk, Option.some.injEq] at hst'
    subst hst'
    have hlv : ∀ j (hj : j < sts.length), Lv 0 (fun e => e ∈ T)
        (((liftComp sts[j].body).subst (rho T.length sts.length)).subst (Subst.all (T.map .dt))) :=
      fun j hj => lv_roll T _ 0 _ (src_liftComp _)
        (fun y hy => by have := hA j hj y hy; omega) (Nat.zero_le _)
    have hbody : ∀ j (hj : j < sts.length), C'.closeComp sts[j].body =
        ((liftComp sts[j].body).subst (rho T.length sts.length)).subst (Subst.all (T.map .dt)) :=
      fun j hj => by
        rw [closeComp_eq hC hok hj, Lv.subst_id _ (fun _ => rfl) _ (hlv j hj)]
    have hsk := hok.getRC k hk
    have hbk := hbody k hk
    generalize hst : sts[k] = st at hsk hbk
    obtain ⟨fin, sups, ct⟩ := st
    cases hsk with
    | noSuper hct =>
      rw [hbk] at hct
      simp only [List.map_nil, Ty.ofList_nil, Ty.subst]
      exact .noSuper (TyOk.wkRecsRC _ hct hr)
    | @oneSuper _ x _ _ d sups' ct' hx hd hunroll hct hsub =>
      rw [hbk] at hct hsub
      simp only [List.map_cons, List.map_nil, Ty.ofList_cons, Ty.ofList_nil, liftTypeIdx]
      rw [hC] at hd
      by_cases hxl : x.toNat < T.length
      · rw [D_lt T sts hxl, List.getElem?_eq_getElem hxl, Option.some.injEq] at hd
        subst hd
        show SubOk2 _ (.sub fin (.cons (((Ty.idx x.toNat).subst _).subst _) (Ty.nil.subst _)) _) _
        rw [u_lt T sts hxl]
        exact .oneSuper (.dt (TyOk.def_congr (Δ₁ := C'.toTypeCtx) (Δ₂ := C'.toTypeCtx.withRecs (rsubs T sts).toList) rfl
            (tyOk_T hT hC hr (hT _ (List.getElem_mem hxl))))) rfl hunroll
          (TyOk.wkRecsRC _ hct hr) (Sub.wkRecsRC _ hsub hr)
      · have hxge : T.length ≤ x.toNat := by omega
        have hxk : x.toNat < T.length + sts.length := by omega
        rw [D_ge T sts hxge hxk, Option.some.injEq] at hd
        subst hd
        show SubOk2 _ (.sub fin (.cons (((Ty.idx x.toNat).subst _).subst _) (Ty.nil.subst _)) _) _
        rw [u_ge T sts hxge hxk]
        have hj : x.toNat - T.length < sts.length := by omega
        rw [unroll_of_get (member_eq T sts hj)] at hunroll
        simp only [Ty.subst, Option.some.injEq, Ty.sub.injEq] at hunroll
        obtain ⟨hfin, -, hct'⟩ := hunroll
        rw [Lv.subst_id _ (fun _ => rfl) _ (hlv _ hj)] at hct'
        subst hct'
        exact .oneSuper (.recv (member_eq T sts hj)) (by simp [before]; omega)
          (by show (rsubs T sts).toList[_]? = _; rw [member_eq T sts hj, hfin])
          (TyOk.wkRecsRC _ hct hr) (Sub.wkRecsRC _ hsub hr)

/-- The body of an unrolled `{}`-valid defined type has small `{}`-valid leaves. -/
theorem unroll_body_lv {d : DefType} (hd : TyOk {} d) {fin : Bool} {sups : Ty (.list .use)}
    {ct : CCompType} (hu : unrolldt d = some (.sub fin sups ct)) :
    Lv 0 (fun e => TyOk {} e ∧ e.size ≤ d.size) ct := by
  cases hd with
  | @defn _ s' i hg hi =>
    rw [unrolldt_defn] at hu
    cases hst : s'.toList[i]? with
    | none => rw [hst] at hu; simp at hu
    | some st0 =>
      rw [hst] at hu
      cases st0 with
      | sub fin0 sups0 ct0 =>
      simp only [Option.map_some, Option.some.injEq, Ty.subst, Ty.sub.injEq] at hu
      obtain ⟨-, -, rfl⟩ := hu
      have hso := GroupOk2.get s' hg hst
      have hct0 : TyOk (gctx s') ct0 := by
        cases hso with
        | noSuper hct => exact hct
        | oneSuper _ _ _ hct _ => exact hct
      have h1 := Lv.of_tyOk (Δ := gctx s') rfl ct0 trivial hct0
      have hsz := Ty.size_lt_of_mem (List.mem_of_getElem? hst)
      simp only [Ty.size] at hsz
      have h2 := Lv.size (S := s'.size + 2) ct0 h1 (by omega)
      refine Lv.subst_unroll s' (m := s'.length) le_rfl ?_ ct0 (Lv.mono le_rfl ?_ ct0 h2)
      · intro j hj; exact ⟨.defn hg hj, le_rfl⟩
      · rintro e ⟨he, hes⟩; exact ⟨he, by simp only [Ty.size]; omega⟩

/-- Step 2: the rolled group is valid in the empty context (`Rectype_ok2`). -/
theorem group_ok (hT : ∀ d ∈ T, TyOk {} d) {C' : Context} (hC : C'.types = Dof T sts)
    (hr : C'.recs = []) (hok : RecTypeOkAt C' sts T.length) :
    GroupOk2 (gctx (rsubs T sts)) (.group (rsubs T sts)) 0 := by
  have hl : (rsubs T sts).length = sts.length := length_rsubs T sts
  have hs := goodSubs hT hC hok
  have hg1 := tyOk_rolled hT hC hr hok
  have hΔc : ∀ d ∈ C'.toTypeCtx.types, d.Closed := by
    intro d hd
    change d ∈ C'.types at hd
    rw [hC, List.mem_append] at hd
    rcases hd with hd | hd
    · exact SubClosed.closed_of_empty (hT d hd)
    · simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨j, _, rfl⟩ := hd
      exact hs.defn_closed j
  have hΔok : C'.toTypeCtx.Ok := by
    intro d hd
    refine ⟨hΔc d hd, ?_⟩
    change d ∈ C'.types at hd
    rw [hC, List.mem_append] at hd
    rcases hd with hd | hd
    · exact tyOk_T hT hC hr (hT d hd)
    · simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      exact .defn hg1 (by omega)
  refine groupOk2_of_get fun k st' hst' => ?_
  have hk : k < sts.length := by
    have := (List.getElem?_eq_some_iff.1 hst').1
    rw [← hl]; exact this
  have hmem := member_eq T sts hk
  rw [hmem, Option.some.injEq] at hst'
  subst hst'
  have hsk := hok.getRC k hk
  have hcomp := closeComp_eq hC hok hk
  generalize hst : sts[k] = st at hsk hcomp hmem ⊢
  obtain ⟨fin, sups, ct⟩ := st
  have hLv := hs _ _ _ (List.mem_of_getElem? hmem)
  simp only at hLv hcomp ⊢
  have hOk : ∀ e, OkS (rsubs T sts) e → TyOk {} e := fun e h => h.1
  have hrl : (rsubs T sts).length ≤ (gctx (rsubs T sts)).recs.length := le_rfl
  have hbody := Lv.tyOk hOk rfl hrl _ hLv.2
  cases hsk with
  | noSuper hct =>
    exact .noSuper hbody
  | @oneSuper _ x _ _ d sups' ct' hx hd hunroll hct hsub =>
    rw [hcomp] at hct hsub
    rw [hC] at hd
    simp only [List.map_cons, List.map_nil, Ty.ofList_cons, Ty.ofList_nil, liftTypeIdx] at hLv ⊢
    by_cases hxl : x.toNat < T.length
    · rw [D_lt T sts hxl, List.getElem?_eq_getElem hxl, Option.some.injEq] at hd
      subst hd
      show SubOk2 _ (.sub fin (.cons (((Ty.idx x.toNat).subst _).subst _) (Ty.nil.subst _)) _) _
      have hu := u_lt T sts hxl
      have hLu : Lv (rsubs T sts).length (OkS (rsubs T sts))
          (((Ty.idx x.toNat : CTypeUse).subst (rho T.length sts.length)).subst
            (Subst.all (T.map .dt))) := hLv.1.1
      rw [hu] at hLu ⊢
      have hTx : TyOk {} T[x.toNat] := hT _ (List.getElem_mem hxl)
      have hOx : OkS (rsubs T sts) T[x.toNat] := hLu
      have hct'' : TyOk C'.toTypeCtx ct' := tyOk_T hT hC hr (unroll_ok hTx hunroll).1
      have hlv0 : Lv 0 (OkS (rsubs T sts)) ct' :=
        Lv.mono le_rfl (fun e ⟨h1, h2⟩ => ⟨h1, le_trans h2 hOx.2⟩) ct' (unroll_body_lv hTx hunroll)
      have hcheck := Sub.complete hΔok hr hsub hct hct''
      rw [← Lv.subst_id (unrollSubst (rsubs T sts)) (fun _ => rfl) ct' hlv0] at hcheck
      have hsub' := comp_fold hs hΔc hLv.2 (Lv.mono (Nat.zero_le _) (fun _ h => h) ct' hlv0) hcheck
      exact .oneSuper (.dt (TyOk.def_congr (Δ₁ := {}) (Δ₂ := gctx (rsubs T sts)) rfl hTx)) rfl
        hunroll hbody hsub'
    · have hxge : T.length ≤ x.toNat := by omega
      have hxk : x.toNat < T.length + sts.length := by omega
      rw [D_ge T sts hxge hxk, Option.some.injEq] at hd
      subst hd
      show SubOk2 _ (.sub fin (.cons (((Ty.idx x.toNat).subst _).subst _) (Ty.nil.subst _)) _) _
      rw [u_ge T sts hxge hxk]
      have hj : x.toNat - T.length < sts.length := by omega
      have hmj := member_eq T sts hj
      rw [unroll_of_get hmj] at hunroll
      simp only [Ty.subst, Option.some.injEq, Ty.sub.injEq] at hunroll
      obtain ⟨hfin, -, hct'⟩ := hunroll
      subst hct'
      have hct'' := (hok.getRC _ hj).hctRC
      rw [closeComp_eq hC hok hj] at hct''
      have hLvj := hs _ _ _ (List.mem_of_getElem? hmj)
      have hcheck := Sub.complete hΔok hr hsub hct hct''
      have hsub' := comp_fold hs hΔc hLv.2 hLvj.2 hcheck
      exact .oneSuper (.recv hmj) (by simp [before]; omega)
        (by show (rsubs T sts).toList[_]? = _; rw [hmj, hfin]) hbody hsub'

end Main

end RollClosed

open RollClosed

/-- The rolled group added by one `Types_ok` step is valid in the empty context. -/
theorem Context.rollGroup_tyOk {C : Context} (hT : ∀ d ∈ C.types, TyOk {} d) (hr : C.recs = [])
    {rt : RecType}
    (hok : RecTypeOkAt { C with types := C.types ++ C.rollGroup rt } rt.types C.types.length) :
    ∀ d ∈ C.rollGroup rt, TyOk {} d := by
  have hC : ({ C with types := C.types ++ C.rollGroup rt } : Context).types =
      Dof C.types rt.types := by
    show C.types ++ C.rollGroup rt = _
    rw [rollGroup_eq]
  have hg := group_ok hT hC hr hok
  intro d hd
  rw [rollGroup_eq, List.mem_map] at hd
  obtain ⟨j, hj, rfl⟩ := hd
  exact .defn hg (by rw [length_rsubs]; simpa using hj)

theorem TypesOk.tyOk_empty_gen {C : Context} {rts : List RecType} {dts : List DefType}
    (h : TypesOk C rts dts) : (∀ d ∈ C.types, TyOk {} d) → C.recs = [] → ∀ d ∈ dts, TyOk {} d := by
  induction h with
  | nil => intro _ _; simp
  | @cons C rt rts dts hok _ ih =>
    intro hT hr
    have hg := Context.rollGroup_tyOk hT hr hok
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hg d hd
    · refine ih (fun d hd => ?_) hr d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hT d hd
      · exact hg d hd

/-- **Rolling.** The closed defined types of a valid module's type section are valid in
the empty context (what instantiation allocates). -/
theorem TypesOk.tyOk_empty' {rts : List RecType} {dts : List DefType}
    (h : TypesOk {} rts dts) : ∀ d ∈ dts, TyOk {} d :=
  h.tyOk_empty_gen (by simp) rfl

end Silmaril.Wasm.Validation
