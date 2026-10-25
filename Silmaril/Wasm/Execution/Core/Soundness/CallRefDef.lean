module

public import Silmaril.Wasm.Execution.Core.Soundness.CallRefInv
public import Silmaril.Wasm.Execution.Core.Soundness.RefOkClosed
public import Silmaril.Wasm.Validation.Subtyping.Closed
public import Silmaril.Wasm.Validation.Subtyping.DefInv

@[expose] public section

/-! # Discharging `hD` of `callRef_inv_of`

`CallRefDef.hD`: along a `Sub Δ` chain (`Δ = C.toTypeCtx` of a well-typed frame) from a
closed defined type `d₁` into a function type `d`, `d₁` is a function type whose
parameters are supertypes of those of `d`.

Proof: translate the chain along the closure substitution `σ = σT Δ.types`
(`SubClosed.Sub.tr`), collapse it to a single `Sub {}` (`SubClosed.Sub.drop`), invert with
`Sub.defHeap_func_list`, and relate each parameter `p` of `d` to `p.subst σ` in `Δ`
(`sub_subst_val`, no validity needed). -/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

namespace CallRefDef

open Silmaril.Wasm.Validation.SubClosed

/-- A substitution that is `none` on `REC`s and on every free index is the identity. -/
theorem subst_eq_of_freeIdx {k : TKind} (t : Ty k) :
    ∀ σ : Subst, (∀ i, σ (.recv i) = none) → (∀ y ∈ t.freeIdx, σ (.idx y) = none) →
      t.subst σ = t := by
  induction t with
  | idx x => intro σ _ h; simp [Ty.subst, h x (by simp [Ty.freeIdx])]
  | recv i => intro σ hσ _; simp [Ty.subst, hσ]
  | group subs ih =>
    intro σ hσ h
    simp only [Ty.subst]
    rw [ih _ (fun i => by simp [Subst.minusRecs])
      (fun y hy => by simpa [Subst.minusRecs] using h y (by simpa [Ty.freeIdx] using hy))]
  | cons a l iha ihl =>
    intro σ hσ h
    simp only [Ty.freeIdx, List.mem_append] at h
    simp only [Ty.subst, iha σ hσ (fun y hy => h y (.inl hy)),
      ihl σ hσ (fun y hy => h y (.inr hy))]
  | func ps rs ihp ihr =>
    intro σ hσ h
    simp only [Ty.freeIdx, List.mem_append] at h
    simp only [Ty.subst, ihp σ hσ (fun y hy => h y (.inl hy)),
      ihr σ hσ (fun y hy => h y (.inr hy))]
  | sub fin sups b ihs ihb =>
    intro σ hσ h
    simp only [Ty.freeIdx, List.mem_append] at h
    simp only [Ty.subst, ihs σ hσ (fun y hy => h y (.inl hy)),
      ihb σ hσ (fun y hy => h y (.inr hy))]
  | _ => intro σ hσ h; simp_all [Ty.subst, Ty.freeIdx]

/-- The closure substitution of closed types is idempotent. -/
theorem σT_idem {T : List DefType} (hT : ∀ d ∈ T, d.Closed) {k : TKind} (t : Ty k) :
    (t.subst (σT T)).subst (σT T) = t.subst (σT T) := by
  refine subst_eq_of_freeIdx _ _ (σT_recv T) (fun y hy => ?_)
  rcases Ty.freeIdx_subst t _ (σT_recv T) y hy with ⟨-, h⟩ | ⟨x, -, u, hu, hy'⟩
  · exact h
  · exfalso
    have hu' : ({ types := T } : TypeCtx).closSubst (.idx x) = some u := hu
    rw [TypeCtx.closSubst_idx] at hu'
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 hu'
    have hc : d.freeIdx = [] := hT d (List.mem_of_getElem? hd)
    simp [Ty.freeIdx, hc] at hy'

/-- Every heap type is below its closure. -/
theorem sub_subst_heap {Δ : TypeCtx} (hΔ : Δ.Ok) (h : CHeapType) :
    Sub Δ h (h.subst (σT Δ.types)) := by
  have hT : ∀ d ∈ Δ.types, d.Closed := fun d hd => (hΔ d hd).1
  cases h with
  | abs a => exact .heapRefl
  | bot => exact .heapRefl
  | use u =>
    cases u with
    | idx x =>
      cases hx : Δ.types[x]? with
      | none =>
        have e : (Ty.use (Ty.idx x) : CHeapType).subst (σT Δ.types) = .use (.idx x) := by
          simp [Ty.subst, TypeCtx.closSubst_idx, hx]
        rw [e]; exact .heapRefl
      | some d =>
        have e : (Ty.use (Ty.idx x) : CHeapType).subst (σT Δ.types) = .use (.dt d) := by
          simp [Ty.subst, TypeCtx.closSubst_idx, hx]
        rw [e]; exact .idxL hx .heapRefl
    | recv i => exact .heapRefl
    | dt e =>
      refine .defDef (.defRefl ?_)
      show e.clos Δ.types = (e.subst (σT Δ.types)).clos Δ.types
      rw [hΔ.clos_eq, hΔ.clos_eq]
      exact (σT_idem hT e).symm

/-- Every value type is below its closure. -/
theorem sub_subst_val {Δ : TypeCtx} (hΔ : Δ.Ok) (p : CValType) :
    Sub Δ p (p.subst (σT Δ.types)) := by
  cases p with
  | num t => exact .num
  | vec t => exact .vec
  | botv => exact .botv
  | refv r =>
    cases r with
    | ref n h =>
      refine .refv ?_
      cases n with
      | false => exact .refNonNull (sub_subst_heap hΔ h)
      | true => exact .refNull (sub_subst_heap hΔ h)

/-- A heap chain in a context without `TYPES`, from a `Good` heap type. -/
theorem chain_heap_drop {Δ : TypeCtx} (hΔ : Δ.types = []) {a b : CHeapType}
    (h : Relation.ReflTransGen (Sub Δ) a b) (ha : Good a) : Good b ∧ Sub {} a b := by
  induction h with
  | refl => exact ⟨ha, .heapRefl⟩
  | tail _ hs ih =>
    obtain ⟨hm, s₁⟩ := ih
    obtain ⟨hb, s₂⟩ := Sub.drop hs hΔ hm
    exact ⟨hb, .heapTrans (good_heap_ok hm) s₁ s₂⟩

theorem emptyOk_of_stateOk {H : Type} {s : Store H} {f : Frame} {C : Context}
    (hst : StateOk s f C) : C.toTypeCtx.EmptyOk := fun d hd =>
  have h := hst.2.types_tyOk_empty d hd
  ⟨closed_of_empty h, h⟩

theorem ok_of_emptyOk {Δ : TypeCtx} (h : Δ.EmptyOk) : Δ.Ok := fun d hd =>
  ⟨(h d hd).1, TyOk.ofEmpty (h d hd).2 Δ⟩

theorem resultSub_of_subst {Δ : TypeCtx} (hΔ : Δ.Ok) :
    ∀ {l l' : List CValType}, List.Forall₂ (Sub {}) (l.map (·.subst (σT Δ.types))) l' →
      ResultOk {} (l.map (·.subst (σT Δ.types))) → ResultSub Δ l l'
  | [], _, .nil, _ => .nil
  | p :: l, _ :: _, .cons hp hl, hok =>
    .cons (Sub.trans hΔ (TyOk.ofEmpty (hok _ (by simp)) Δ) (sub_subst_val hΔ p)
        (Sub.of_empty hp Δ))
      (resultSub_of_subst hΔ hl (fun x hx => hok x (List.mem_cons_of_mem _ hx)))

/-- `hD` of `callRef_inv_of`. (`hd` is not needed by the proof.) -/
theorem hD {H : Type} {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    {d : DefType} {ps rs : Ty (.list .val)} (hd : TyOk C.toTypeCtx d)
    (he : Expand d (.func ps rs)) :
    ∀ d₁ : DefType, TyOk {} d₁ →
      Relation.ReflTransGen (Sub C.toTypeCtx) (Ty.defHeap d₁) (Ty.defHeap d) →
      ∃ ps' rs', Expand d₁ (.func ps' rs') ∧ ResultSub C.toTypeCtx ps.toList ps'.toList := by
  have _ := hd
  intro d₁ hd₁ hc
  have hE := emptyOk_of_stateOk hst
  have hOk := ok_of_emptyOk hE
  set Δ := C.toTypeCtx
  set σ := σT Δ.types
  have h1 : Relation.ReflTransGen (Sub (trCtx Δ.types Δ)) ((Ty.defHeap d₁).subst σ)
      ((Ty.defHeap d).subst σ) :=
    hc.lift (fun t : CHeapType => t.subst σ) (fun _ _ hs => Sub.tr hE hs rfl)
  have e1 : (Ty.defHeap d₁).subst σ = Ty.defHeap d₁ := closed_σT (closed_of_empty (.use (.dt hd₁)))
  have e2 : (Ty.defHeap d).subst σ = Ty.defHeap (d.subst σ) := rfl
  rw [e1, e2] at h1
  obtain ⟨hg, hs⟩ := chain_heap_drop rfl h1 (hd₁ : Good (Ty.use (Ty.dt d₁)))
  have hd' : TyOk {} (d.subst σ) := hg
  have he' := expand_σT Δ.types he
  obtain ⟨ps', rs', he₁, hps⟩ := Sub.defHeap_func_list hs hd₁ hd' he'
  refine ⟨ps', rs', he₁, ?_⟩
  have hmid : ResultOk {} (ps.subst σ).toList := (Expand.func_ok hd' he').1
  rw [Ty.toList_subst] at hps hmid
  exact resultSub_of_subst hOk hps hmid

end CallRefDef

/-- `callRef_inv` with `hD` discharged (`CallRefDef.hD`). Compared to `callRef_inv`
it adds `hd : TyOk C.toTypeCtx d` (available at every call site) and the value
transfer fact `hV` as an explicit hypothesis. -/
theorem callRef_inv_closed {H : Type} {s : Store H} {f : Frame} {C : Context} {d : DefType}
    {ps rs : Ty (.list .val)} {vs : List Val} {r : Ref}
    (hst : StateOk s f C) (hd : TyOk C.toTypeCtx d) (he : Expand d (.func ps rs))
    (hv : ValsTo s C.toTypeCtx vs ps.toList)
    (hr : ValTo s C.toTypeCtx (.ref r) (Ty.refT true (Ty.defHeap d)))
    (hV : ∀ (v : Val) (t : CValType), ValTo s C.toTypeCtx v t → TyOk {} t → ValOk s v t) :
    r = .null ∨ ∃ a fi ps' rs', r = .func a ∧ s.funcs[a]? = some fi ∧
      Expand fi.type (.func ps' rs') ∧ List.Forall₂ (ValOk s) vs ps'.toList :=
  callRef_inv_of hst he hv hr hV (CallRefDef.hD hst hd he)

end Silmaril.Wasm.Execution.Core
