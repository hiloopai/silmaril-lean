module

public import Silmaril.Proofs.Wasm.Component.Reference.ValidTypes
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The validator imposes the flat arities on `Simple.toRef`

`validArity_holds : Simple.ValidArity`. Validating `Simple.toRef` of a component in the fragment
(`Good`, `Inst`) walks its definitions (`exportsDefs_chk`): the core module type is the
module's, the core instance exports it, and per export the emitted types resolve to `toCl`
(`emitTys_chk`), the function type to the lifted type, the alias to the core export of the
interface's flat type (`coreExport_flat`), and the `canon lift` check (`LiftOk.callee`) then
equates the core type with the lift flattening of the emitted function type. With no options
the flattening keeps at most 16 parameters and one result, so the equation gives the flat
arities (`arity_of_lift`); the result types after the first have nonempty flattenings (the
validator checks records nonempty), so there is at most one.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Types (TypeDef)

/-! ## The flat arities from the lift flattening -/

theorem fitParams_eq {p : Silmaril.Wasm.AddrType} {ps : List Silmaril.Wasm.NumType}
    (h : fitParams 16 p ps = ps) : ps.length ≤ 16 := by
  unfold fitParams at h
  split at h
  · assumption
  · have hl : ps.length = 1 := by rw [← h]; rfl
    omega

theorem flatList_nil : ∀ {ts : List ValTy}, ValTy.flatList ts = [] → (∀ u ∈ ts, WF (toCl u)) →
    ts = []
  | [], _, _ => rfl
  | t :: ts, h, hwf => by
    have ht : t.flat = [] := (List.append_eq_nil_iff.1 h).1
    exact absurd ht (flat_ne_nil t (hwf t List.mem_cons_self))

/-- The results of the lift flattening of the first result type are all the flat results. -/
theorem results_bound {p : Silmaril.Wasm.AddrType} {t : ValTy} {rest : List ValTy}
    (hwf : ∀ u ∈ rest, WF (toCl u))
    (h : (if t.flat.length ≤ maxFlatResults then t.flat else [pointerType p]) =
      t.flat ++ ValTy.flatList rest) :
    rest = [] ∧ t.flat.length ≤ 1 := by
  split at h
  · next hle =>
    have hl := congrArg List.length h
    have hr : ValTy.flatList rest = [] := by
      rw [List.length_append] at hl
      exact List.length_eq_zero_iff.1 (by omega)
    exact ⟨flatList_nil hr hwf, hle⟩
  · next hgt =>
    have hl := congrArg List.length h
    simp only [List.length_cons, List.length_nil, List.length_append, maxFlatResults] at hl hgt
    omega

/-- The two components of the lift flattening without options. -/
theorem flattenFunc_parts {p : Silmaril.Wasm.AddrType} {ps rs : List (WIT.ClosedType Nat)}
    {P R : List Silmaril.Wasm.NumType}
    (h : flattenFunc ⟨p, false, false⟩ .lift ⟨ps, rs⟩ = ⟨P, R⟩) :
    fitParams maxFlatParams p (flattenTypes p ps) = P ∧
      (if (flattenTypes p rs).length ≤ maxFlatResults then flattenTypes p rs
        else [pointerType p]) = R := by
  simp only [flattenFunc, Bool.not_false, ↓reduceIte] at h
  have hp := congrArg Silmaril.Wasm.V1.FuncType.params h
  have hr := congrArg Silmaril.Wasm.V1.FuncType.results h
  split at hp <;> split at hr
  all_goals first
    | exact ⟨hp, by rw [ite_eq_left ‹_›]; exact hr⟩
    | exact ⟨hp, by rw [ite_eq_right ‹_›]; exact hr⟩

/-- **The flat arities** of a lifted type whose lift flattening (without options) is the
interface's flat type. -/
theorem arity_of_lift {p : Silmaril.Wasm.AddrType} {params results : List ValTy}
    (hwf : ∀ t ∈ results, WF (toCl t))
    (h : flattenFunc ⟨p, false, false⟩ .lift ⟨toClList params, ((toClList results).head?).toList⟩ =
      ⟨ValTy.flatList params, ValTy.flatList results⟩) :
    (ValTy.flatList params).length ≤ 16 ∧ (ValTy.flatList results).length ≤ 1 ∧
      results.length ≤ 1 := by
  obtain ⟨hP, hR⟩ := flattenFunc_parts h
  rw [flattenTypes_toCl] at hP
  refine ⟨fitParams_eq hP, ?_⟩
  cases results with
  | nil => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | cons t rest =>
    have hR' : (if t.flat.length ≤ maxFlatResults then t.flat else [pointerType p]) =
        t.flat ++ ValTy.flatList rest := by
      simpa only [toClList, List.head?_cons, Option.toList_some, flattenTypes,
        flatten_toCl, List.append_nil, ValTy.flatList] using hR
    obtain ⟨rfl, hle⟩ := results_bound (fun u hu => hwf u (List.mem_cons_of_mem _ hu)) hR'
    simp only [ValTy.flatList, List.append_nil, List.length_singleton]
    exact ⟨hle, Nat.le_refl _⟩

/-! ## The definitions of one export -/

variable {sc : Scopes Core3Extern}

theorem resolveOpt?_head {Γ : Ctx Core3Extern} {tys : List (TypeDef Nat Core3Extern)}
    (hΓ : tys <+: Γ.types.map (·.def_)) :
    ∀ {vs : List Syntax.VT} {ts : List (WIT.ClosedType Nat)}, List.Forall₂ (VRes tys) vs ts →
      resolveOpt? Γ vs.head? = .ok ts.head?
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h _ => by
    simp only [List.head?_cons, resolveOpt?, h Γ hΓ]

/-- The emitted function type resolves to the lifted type. -/
theorem funcType_resolved {s : DefState Core3Extern} {ps r : List Syntax.VT}
    {params results : List ValTy} {ftv : Types.FuncType Nat}
    (hps : List.Forall₂ (VRes (ValidView s).1) ps (toClList params))
    (hrs : List.Forall₂ (VRes (ValidView s).1) r (toClList results))
    (h : checkFuncType? Features.p2 s.ctx { params := labels "a" ps, result := r.head? } =
      .ok ftv) :
    ftv = ⟨labels "a" (toClList params), (toClList results).head?, false⟩ := by
  have hpr : resolveFields? s.ctx (labels "a" ps) = .ok (labels "a" (toClList params)) :=
    resolveFields?_mapIdx (tag "a") (hps.imp fun _ _ hv => hv s.ctx (List.prefix_refl _))
  have hrr : resolveOpt? s.ctx r.head? = .ok (toClList results).head? :=
    resolveOpt?_head (List.prefix_refl _) hrs
  simp only [checkFuncType?, hpr, hrr] at h
  split at h
  · exact (Except.ok.inj h).symm
  · cases h

/-- The lift flattening of the lifted type of an export. -/
theorem liftCoreType_eq (Γ : Ctx Core3Extern) (params results : List ValTy) :
    CanonOpts.liftCoreType core3Profile.view.core Γ []
        ⟨labels "a" (toClList params), (toClList results).head?, false⟩ =
      flattenFunc ⟨CanonOpts.ptrType core3Profile.view.core Γ [], false, false⟩ .lift
        ⟨toClList params, ((toClList results).head?).toList⟩ := by
  simp only [CanonOpts.liftCoreType, CanonOpts.abiOptions, FuncType.ofWIT, labels_map_snd]
  rfl

/-- The element at the end of a list. -/
theorem getElem?_last {α : Type} {l : List α} {a : α} {n : Nat} (h : l.length = n) :
    (l ++ [a])[n]? = some a := by
  rw [List.getElem?_append_right (by omega), h, Nat.sub_self]
  rfl

/-- The core function pushed by the alias, read back by the lift. -/
theorem coreFuncType_alias {s₃ s₄ : DefState Core3Extern} {x0 : Core3Extern} {i : Nat}
    (hl : (ValidView s₃).2.1.length = i)
    (hV : ValidView s₄ = ((ValidView s₃).1, (ValidView s₃).2.1 ++ [x0], (ValidView s₃).2.2)) :
    CanonOpts.coreFuncType? core3Profile.view.core s₄.ctx i =
      core3Profile.view.core.funcType? x0 := by
  have hc : s₄.ctx.coreFuncs = (ValidView s₃).2.1 ++ [x0] := congrArg (·.2.1) hV
  simp only [CanonOpts.coreFuncType?, Ctx.coreFunc?, hc, getElem?_last hl, Option.bind_some]

/-- **The tail of an export's definitions** (function type, alias, lift, export): the aliased
core export's flat type is the lift flattening of the lifted type. -/
theorem tail_chk {t : Types.CoreModuleType Core3Extern} {s₂ s' : DefState Core3Extern}
    {ps r : List Syntax.VT} {params results : List ValTy} {n₂ i : Nat} {core nm : String}
    (hl : (ValidView s₂).1.length = n₂) (hcf : (ValidView s₂).2.1.length = i)
    (hci : (ValidView s₂).2.2 = [t.exports])
    (hps : List.Forall₂ (VRes (ValidView s₂).1) ps (toClList params))
    (hrs : List.Forall₂ (VRes (ValidView s₂).1) r (toClList results))
    (h : chks sc s₂ [.type (.func { params := labels "a" ps, result := r.head? }),
      .alias (.coreExport 0 core .func), .canon (.lift i [] n₂),
      .export_ { name := nm } ⟨.func, 2 * i⟩ none] = .ok s') :
    (∃ x0 p, t.exports.lookup core = some x0 ∧ core3Profile.view.core.funcType? x0 =
      some (flattenFunc ⟨p, false, false⟩ .lift
        ⟨toClList params, ((toClList results).head?).toList⟩)) ∧
      (ValidView s').1.length = n₂ + 1 ∧ (ValidView s').2.1.length = i + 1 ∧
      (ValidView s').2.2 = [t.exports] := by
  obtain ⟨s₃, h₁, h₂⟩ := chks_cons h
  obtain ⟨s₄, h₃, h₄⟩ := chks_cons h₂
  obtain ⟨s₅, h₅, h₆⟩ := chks_cons h₄
  obtain ⟨s₆, h₇, h₈⟩ := chks_cons h₆
  have hs : s' = s₆ := chks_nil h₈
  obtain ⟨ftv, hftv, hV₃⟩ := chk_typeFunc h₁
  have hft := funcType_resolved hps hrs hftv
  obtain ⟨ex, x0, hex, hx0, hV₄⟩ := chk_aliasCoreFunc h₃
  obtain ⟨ft, hty, hok, hV₅⟩ := chk_lift h₅
  obtain ⟨e, he, hV₆⟩ := chk_export rfl h₇
  have hext : ex = t.exports := by
    have hci₃ : s₃.ctx.coreInstances = [t.exports] := by
      rw [show s₃.ctx.coreInstances = (ValidView s₃).2.2 from rfl, hV₃]
      exact hci
    rw [hci₃] at hex
    exact (Option.some.inj hex).symm
  have hftt : ft = ftv := by
    have hty' : s₄.ctx.type? n₂ = some (.func ftv) := by
      rw [← hl]
      exact type?_last ((congrArg (·.1) hV₄).trans (congrArg (·.1) hV₃))
    exact Types.TypeDef.func.inj (Option.some.inj (hty.symm.trans hty'))
  have hcall := hok.callee
  rw [coreFuncType_alias (by rw [hV₃]; exact hcf) hV₄, hftt, hft, liftCoreType_eq] at hcall
  obtain ⟨ft', -, rfl⟩ := Option.map_eq_some_iff.1 he
  have hV' : ValidView s' = ((ValidView s₂).1 ++ [.func ftv], (ValidView s₂).2.1 ++ [x0],
      (ValidView s₂).2.2) := by
    rw [hs]
    show CtxView s₆.ctx = _
    rw [hV₆, pushEntity_func_view]
    show ValidView s₅ = _
    rw [hV₅, hV₄, hV₃]
  refine ⟨⟨x0, _, hext ▸ hx0, hcall⟩, ?_, ?_, ?_⟩
  · rw [hV', List.length_append, hl]
    rfl
  · rw [hV', List.length_append, hcf]
    rfl
  · rw [hV', hci]

/-- The arity conditions of one export. -/
def ExportArity (x : SimpleExport) : Prop :=
  (ValTy.flatList x.ty.params).length ≤ 16 ∧ (ValTy.flatList x.ty.results).length ≤ 1 ∧
    x.ty.results.length ≤ 1

/-- The definitions of one export. -/
theorem exportDefs_eq_chk {m : NumModule} {x : SimpleExport} {nm : String} {ft : CoreFuncTy}
    {i n n₁ n₂ : Nat} {ps r : List Syntax.VT} {dps drs : List (Syntax.Definition Silmaril.Wasm.Module)}
    (hk : m.exports[x.core]? = some (nm, ft))
    (hp : emitTys (M := Silmaril.Wasm.Module) x.ty.params n = (ps, dps, n₁))
    (hr : emitTys (M := Silmaril.Wasm.Module) x.ty.results n₁ = (r, drs, n₂)) :
    Simple.exportDefs m i x n = (dps ++ drs ++
      [.type (.func { params := labels "a" ps, result := r.head? }),
        .alias (.coreExport 0 nm .func), .canon (.lift i [] n₂),
        .export_ { name := x.name } ⟨.func, 2 * i⟩ none], n₂ + 1) := by
  simp only [Simple.exportDefs, hp, hr, hk, Option.map_some, Option.getD_some]

/-- **The definitions of one export**: accepted, they force its arity, and they add one type
index past the emitted types and one core function. -/
theorem exportDefs_chk {c : Simple} (hi : c.Inst) {x : SimpleExport} {nm : String}
    (hk : c.mod.exports[x.core]? = some (nm, x.ty.flat))
    {t : Types.CoreModuleType Core3Extern} (ht : core3ModuleType? c.mod.mod = some t)
    {s s' : DefState Core3Extern} {n i : Nat} (hl : (ValidView s).1.length = n)
    (hcf : (ValidView s).2.1.length = i) (hci : (ValidView s).2.2 = [t.exports])
    (h : chks sc s (Simple.exportDefs c.mod i x n).1 = .ok s') :
    ExportArity x ∧ (ValidView s').1.length = (Simple.exportDefs c.mod i x n).2 ∧
      (ValidView s').2.1.length = i + 1 ∧ (ValidView s').2.2 = [t.exports] := by
  rcases hp : emitTys (M := Silmaril.Wasm.Module) x.ty.params n with ⟨ps, dps, n₁⟩
  rcases hr : emitTys (M := Silmaril.Wasm.Module) x.ty.results n₁ with ⟨r, drs, n₂⟩
  rw [exportDefs_eq_chk hk hp hr] at h ⊢
  obtain ⟨s₂, h₁₂, h₃⟩ := chks_append h
  obtain ⟨s₁, h₁, h₂⟩ := chks_append h₁₂
  have E1 := emitTys_chk (sc := sc) x.ty.params n s s₁ hl (by rw [hp]; exact h₁)
  rw [hp] at E1
  have E2 := emitTys_chk (sc := sc) x.ty.results n₁ s₁ s₂ E1.1.2.1 (by rw [hr]; exact h₂)
  rw [hr] at E2
  have hv₂ : (ValidView s₂).2 = (ValidView s).2 := E2.1.2.2.trans E1.1.2.2
  obtain ⟨⟨x0, p, hx0, hfx⟩, hl', hc', hci'⟩ := tail_chk (sc := sc) (t := t) (nm := x.name)
    E2.1.2.1 (by rw [hv₂]; exact hcf) (by rw [hv₂]; exact hci)
    (E1.2.1.imp fun _ _ hv => hv.mono E2.1.prefix) E2.2.1 h₃
  have hv := coreExport_flat hi hk ht hx0 hfx
  exact ⟨arity_of_lift E2.2.2 hv, hl', hc', hci'⟩

/-- **The definitions of the exports from number `i` on**: accepted, they force the arity of
each export. -/
theorem exportsDefs_chk {c : Simple} (hc : c.Good) (hi : c.Inst)
    {t : Types.CoreModuleType Core3Extern} (ht : core3ModuleType? c.mod.mod = some t) :
    ∀ (xs : List SimpleExport), (∀ x ∈ xs, x ∈ c.exports) →
      ∀ (i n : Nat) (s s' : DefState Core3Extern), (ValidView s).1.length = n →
        (ValidView s).2.1.length = i → (ValidView s).2.2 = [t.exports] →
        chks sc s (Simple.exportsDefs c.mod i xs n) = .ok s' → ∀ x ∈ xs, ExportArity x
  | [], _, _, _, _, _, _, _, _, _ => fun _ hx => absurd hx List.not_mem_nil
  | x :: xs, hxs, i, n, s, s', hl, hcf, hci, h => by
    rcases he : Simple.exportDefs c.mod i x n with ⟨ds, n'⟩
    have hdef : Simple.exportsDefs c.mod i (x :: xs) n = ds ++ Simple.exportsDefs c.mod (i + 1) xs n' := by
      simp only [Simple.exportsDefs, he]
    rw [hdef] at h
    obtain ⟨s₁, h₁, h₂⟩ := chks_append h
    obtain ⟨nm, hk⟩ := hc.core x (hxs x List.mem_cons_self)
    have hE := exportDefs_chk (sc := sc) hi hk ht hl hcf hci (by rw [he]; exact h₁)
    rw [he] at hE
    have ih := exportsDefs_chk hc hi ht xs (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      (i + 1) n' s₁ s' hE.2.1 hE.2.2.1 hE.2.2.2 h₂
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hE.1
    · exact ih y hy

/-- The validator accepts `c.toRef` exactly when its definitions are accepted from the initial
state (and the component is finished). -/
theorem chks_of_check {c : Simple} {ct : Silmaril.Wasm.Component.Reference.ComponentType}
    (h : Silmaril.Wasm.Component.Reference.check? Features.p2 c.toRef = .ok ct) :
    ∃ s, chks [] initState c.toRef = .ok s := by
  simp only [Silmaril.Wasm.Component.Reference.check?, checkCore3?, Validation.check?] at h
  split at h
  · cases h
  · next s hs => exact ⟨s, hs⟩

/-- The core module and the core instance of `c.toRef`, validated from the initial state, leave
no type, no core function and one core instance: the exports of the module's type. -/
theorem prefix_chk {c : Simple} {s₂ : DefState Core3Extern}
    (h : chks [] initState [.coreModule c.mod.mod, .coreInstance (.instantiate 0 [])] = .ok s₂) :
    ∃ t, core3ModuleType? c.mod.mod = some t ∧ (ValidView s₂).1.length = 0 ∧
      (ValidView s₂).2.1.length = 0 ∧ (ValidView s₂).2.2 = [t.exports] := by
  obtain ⟨s₁, h₁, h₂⟩ := chks_cons h
  obtain ⟨s₂', h₃, h₄⟩ := chks_cons h₂
  have hs : s₂ = s₂' := chks_nil h₄
  obtain ⟨mt, hmt, hmods, hV₁⟩ := chk_coreModule h₁
  obtain ⟨mt', hmt', hV₂⟩ := chk_coreInstance h₃
  have hm : mt' = mt := by
    rw [hmods] at hmt'
    exact (Option.some.inj hmt').symm
  refine ⟨mt, hmt, ?_, ?_, ?_⟩ <;> rw [hs, hV₂, hV₁, hm] <;> rfl

/-- **The reference validator imposes the flat arities** on the translation of a `Simple`
component in the fragment. -/
theorem validArity_holds : Simple.ValidArity := by
  intro c hc _ hi ⟨ct, hct⟩
  obtain ⟨s, hs⟩ := chks_of_check hct
  obtain ⟨s₂, h₁, h₂⟩ := chks_append (ds := [.coreModule c.mod.mod, .coreInstance (.instantiate 0 [])])
    hs
  obtain ⟨t, ht, hl, hcf, hci⟩ := prefix_chk h₁
  exact exportsDefs_chk hc hi ht c.exports (fun _ hx => hx) 0 0 s₂ s hl hcf hci h₂

end Silmaril.Proofs.Wasm.Component.Reference
