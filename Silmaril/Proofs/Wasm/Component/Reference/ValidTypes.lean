module

public import Silmaril.Proofs.Wasm.Component.Reference.ValidStep
public import Silmaril.Proofs.Wasm.Component.Reference.FlatABI

/-!
# The validator on the type definitions of `Simple.toRef`

`toCl t` is the type the validator resolves for the IR type `t` (records labelled `f, fx, …`,
variants `c, cx, …`, as `toClosed` but with the validator's resource variables). Validating the
type definitions `emitTy t n` emits only extends the type index space, after which the emitted
value type resolves to `toCl t` in every extension (`emitTy_chk`), and `toCl t` is well formed
(records are nonempty, which the validator checks). Flattening `toCl t` is `t.flat`
(`flatten_toCl`), and a well-formed type has a nonempty flattening (`flat_ne_nil`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Types (TypeDef)

mutual
/-- The validator's resolved type of an IR type. -/
def toCl : ValTy → WIT.ClosedType Nat
  | .bool => .prim .bool
  | .s8 => .prim .s8 | .u8 => .prim .u8 | .s16 => .prim .s16 | .u16 => .prim .u16
  | .s32 => .prim .s32 | .u32 => .prim .u32 | .s64 => .prim .s64 | .u64 => .prim .u64
  | .f32 => .prim .f32 | .f64 => .prim .f64 | .char => .prim .char
  | .record ts => .record (labels "f" (toClList ts))
  | .variant cs => .variant (labels "c" (toClCases cs))

/-- `toCl` on lists. -/
def toClList : List ValTy → List (WIT.ClosedType Nat)
  | [] => []
  | t :: ts => toCl t :: toClList ts

/-- `toCl` on variant cases. -/
def toClCases : List (Option ValTy) → List (Option (WIT.ClosedType Nat))
  | [] => []
  | none :: cs => none :: toClCases cs
  | some t :: cs => some (toCl t) :: toClCases cs
end

/-! ## Flattening -/

mutual
theorem flatten_toCl (p : Silmaril.Wasm.AddrType) :
    ∀ t : ValTy, flatten p (toCl t) = t.flat
  | .bool | .s8 | .u8 | .s16 | .u16 | .s32 | .u32 | .s64 | .u64 | .f32 | .f64 | .char => by
    first | (simp only [toCl, flatten, flattenPrimitive, ValTy.flat])
  | .record ts => by
    simp only [toCl, flatten, ValTy.flat]
    exact flattenFields_toCl p ts _ (labels_map_snd "f" _)
  | .variant cs => by
    simp only [toCl, flatten, ValTy.flat]
    rw [flattenCases_toCl p cs _ (labels_map_snd "c" _)]

theorem flattenFields_toCl (p : Silmaril.Wasm.AddrType) :
    ∀ (ts : List ValTy) (fs : List (String × WIT.ClosedType Nat)),
      fs.map Prod.snd = toClList ts → flattenFields p fs = ValTy.flatList ts
  | [], [], _ => by simp only [flattenFields, ValTy.flatList]
  | [], _ :: _, h => by simp [toClList] at h
  | _ :: _, [], h => by simp [toClList] at h
  | t :: ts, (n, u) :: fs, h => by
    simp only [List.map_cons, toClList, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [flattenFields, ValTy.flatList, flatten_toCl p t, flattenFields_toCl p ts fs h]

theorem flattenCases_toCl (p : Silmaril.Wasm.AddrType) :
    ∀ (cs : List (Option ValTy)) (fs : List (String × Option (WIT.ClosedType Nat))),
      fs.map Prod.snd = toClCases cs →
        variantPayload (flattenCases p fs) = ValTy.flatCases cs
  | [], [], _ => by simp only [flattenCases, variantPayload, ValTy.flatCases]
  | [], _ :: _, h => by simp [toClCases] at h
  | none :: _, [], h => by simp [toClCases] at h
  | some _ :: _, [], h => by simp [toClCases] at h
  | none :: cs, (n, u) :: fs, h => by
    simp only [List.map_cons, toClCases, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [flattenCases, variantPayload, flattenOption, ValTy.flatCases, ValTy.flatOpt,
      flattenCases_toCl p cs fs h, ← joinFlat_eq]
  | some t :: cs, (n, u) :: fs, h => by
    simp only [List.map_cons, toClCases, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [flattenCases, variantPayload, flattenOption, ValTy.flatCases, ValTy.flatOpt,
      flattenCases_toCl p cs fs h, flatten_toCl p t, ← joinFlat_eq]
end

theorem flattenTypes_toCl (p : Silmaril.Wasm.AddrType) :
    ∀ ts : List ValTy, flattenTypes p (toClList ts) = ValTy.flatList ts
  | [] => by simp only [toClList, flattenTypes, ValTy.flatList]
  | t :: ts => by
    simp only [toClList, flattenTypes, ValTy.flatList, flatten_toCl, flattenTypes_toCl p ts]

/-- Well-formedness of the validator's types (no references, every resource allowed). -/
abbrev WF (t : WIT.ClosedType Nat) : Prop := WIT.ValType.WellFormed (fun _ => True) (fun _ => True) t

/-- **A well-formed type has a nonempty flattening** (records are nonempty). -/
theorem flat_ne_nil : ∀ t : ValTy, WF (toCl t) → t.flat ≠ []
  | .bool, _ | .s8, _ | .u8, _ | .s16, _ | .u16, _ | .s32, _ | .u32, _ | .s64, _ | .u64, _
  | .f32, _ | .f64, _ | .char, _ => by simp [ValTy.flat]
  | .variant cs, _ => by simp [ValTy.flat]
  | .record [], h => by
    cases h with
    | record hne _ _ => exact absurd rfl hne
  | .record (t :: ts), h => by
    cases h with
    | record _ _ hm =>
      have ht : WF (toCl t) := hm (tag "f" 0, toCl t) (by simp [labels, toClList])
      have hf := flat_ne_nil t ht
      simp only [ValTy.flat, ValTy.flatList, ne_eq, List.append_eq_nil_iff, not_and]
      exact fun h₁ => absurd h₁ hf

/-! ## Resolution in extended contexts -/

/-- `v` resolves to `t` in every context whose type definitions extend `tys`. -/
def VRes (tys : List (TypeDef Nat Core3Extern)) (v : Syntax.VT) (t : WIT.ClosedType Nat) :
    Prop :=
  ∀ Γ : Ctx Core3Extern, tys <+: Γ.types.map (·.def_) → resolveVT? Γ v = .ok t

/-- `o` resolves to `ot` in every context whose type definitions extend `tys`. -/
def VResO (tys : List (TypeDef Nat Core3Extern)) (o : Option Syntax.VT)
    (ot : Option (WIT.ClosedType Nat)) : Prop :=
  ∀ Γ : Ctx Core3Extern, tys <+: Γ.types.map (·.def_) → resolveOpt? Γ o = .ok ot

theorem VRes.mono {tys tys' : List (TypeDef Nat Core3Extern)} {v : Syntax.VT}
    {t : WIT.ClosedType Nat} (h : VRes tys v t) (hp : tys <+: tys') : VRes tys' v t :=
  fun Γ hΓ => h Γ (hp.trans hΓ)

theorem VResO.mono {tys tys' : List (TypeDef Nat Core3Extern)} {o : Option Syntax.VT}
    {ot : Option (WIT.ClosedType Nat)} (h : VResO tys o ot) (hp : tys <+: tys') :
    VResO tys' o ot :=
  fun Γ hΓ => h Γ (hp.trans hΓ)

theorem VResO.some {tys : List (TypeDef Nat Core3Extern)} {v : Syntax.VT}
    {t : WIT.ClosedType Nat} (h : VRes tys v t) : VResO tys (some v) (some t) := by
  intro Γ hΓ
  simp only [resolveOpt?, h Γ hΓ]

theorem VResO.none (tys : List (TypeDef Nat Core3Extern)) : VResO tys none none :=
  fun _ _ => rfl

/-- A type index whose definition is a value type resolves to it. -/
theorem VRes.idx {tys : List (TypeDef Nat Core3Extern)} {i : Nat} {t : WIT.ClosedType Nat}
    (h : tys[i]? = some (.val t)) : VRes tys (.idx i) t := by
  intro Γ hΓ
  obtain ⟨l, hl⟩ := hΓ
  have hi : (Γ.types.map (·.def_))[i]? = some (.val t) := by
    rw [← hl, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]
  rw [List.getElem?_map] at hi
  obtain ⟨sl, hsl, hdef⟩ := Option.map_eq_some_iff.1 hi
  simp only [resolveVT?, Ctx.typeSlotAt?, Ctx.listAt?, hsl, hdef]

/-- Labelled resolved fields. -/
theorem resolveFields?_mapIdx {Γ : Ctx Core3Extern} :
    ∀ {vs : List Syntax.VT} {ts : List (WIT.ClosedType Nat)} (f : Nat → String),
      List.Forall₂ (fun v t => resolveVT? Γ v = .ok t) vs ts →
        resolveFields? Γ (vs.mapIdx fun i v => (f i, v)) = .ok (ts.mapIdx fun i t => (f i, t))
  | [], [], _, .nil => rfl
  | v :: vs, t :: ts, f, .cons h hs => by
    rw [List.mapIdx_cons, List.mapIdx_cons]
    simp only [resolveFields?, h, resolveFields?_mapIdx (fun i => f (i + 1)) hs]

/-- Labelled resolved cases. -/
theorem resolveCases?_mapIdx {Γ : Ctx Core3Extern} :
    ∀ {os : List (Option Syntax.VT)} {ts : List (Option (WIT.ClosedType Nat))} (f : Nat → String),
      List.Forall₂ (fun o t => resolveOpt? Γ o = .ok t) os ts →
        resolveCases? Γ (os.mapIdx fun i o => (f i, o)) = .ok (ts.mapIdx fun i t => (f i, t))
  | [], [], _, .nil => rfl
  | o :: os, t :: ts, f, .cons h hs => by
    rw [List.mapIdx_cons, List.mapIdx_cons]
    simp only [resolveCases?, h, resolveCases?_mapIdx (fun i => f (i + 1)) hs]

/-- An accepted record definition is the record of its resolved fields, well formed. -/
theorem checkDefValType?_record {Γ : Ctx Core3Extern} {fs : List (String × Syntax.VT)}
    {ts : List (String × WIT.ClosedType Nat)} {t : WIT.ClosedType Nat}
    (hf : resolveFields? Γ fs = .ok ts) (h : checkDefValType? Features.p2 Γ (.record fs) = .ok t) :
    t = .record ts ∧ WF t := by
  have hv := checkDefValType?_iff.1 h
  have hr : resolveDef? Γ (.record fs) = .ok t := resolveDef?_eq_ok.2 hv.resolve
  simp only [resolveDef?, hf] at hr
  cases hr
  exact ⟨rfl, hv.wf.1⟩

/-- An accepted variant definition is the variant of its resolved cases, well formed. -/
theorem checkDefValType?_variant {Γ : Ctx Core3Extern} {cs : List (String × Option Syntax.VT)}
    {ts : List (String × Option (WIT.ClosedType Nat))} {t : WIT.ClosedType Nat}
    (hf : resolveCases? Γ cs = .ok ts)
    (h : checkDefValType? Features.p2 Γ (.variant cs) = .ok t) : t = .variant ts ∧ WF t := by
  have hv := checkDefValType?_iff.1 h
  have hr : resolveDef? Γ (.variant cs) = .ok t := resolveDef?_eq_ok.2 hv.resolve
  simp only [resolveDef?, hf] at hr
  cases hr
  exact ⟨rfl, hv.wf.1⟩

/-! ## Validating emitted type definitions -/

/-- The definitions took `s` to `s'`, extending the type definitions to `n'` and keeping the
core functions and instances. -/
def EmitOk (s s' : DefState Core3Extern) (n' : Nat) : Prop :=
  (∃ new, (ValidView s').1 = (ValidView s).1 ++ new) ∧ (ValidView s').1.length = n' ∧
    (ValidView s').2 = (ValidView s).2

theorem EmitOk.refl (s : DefState Core3Extern) : EmitOk s s (ValidView s).1.length :=
  ⟨⟨[], (List.append_nil _).symm⟩, rfl, rfl⟩

theorem EmitOk.trans {s s₁ s₂ : DefState Core3Extern} {n₁ n₂ : Nat} (h₁ : EmitOk s s₁ n₁)
    (h₂ : EmitOk s₁ s₂ n₂) : EmitOk s s₂ n₂ := by
  obtain ⟨⟨a, ha⟩, -, hc₁⟩ := h₁
  obtain ⟨⟨b, hb⟩, hl, hc₂⟩ := h₂
  exact ⟨⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩, hl, hc₂.trans hc₁⟩

theorem EmitOk.prefix {s s' : DefState Core3Extern} {n' : Nat} (h : EmitOk s s' n') :
    (ValidView s).1 <+: (ValidView s').1 := by
  obtain ⟨⟨a, ha⟩, -, -⟩ := h
  exact ⟨a, ha.symm⟩

variable {sc : Scopes Core3Extern}

/-- The type at the end of the definitions. -/
theorem type?_last {Γ : Ctx Core3Extern} {tys : List (TypeDef Nat Core3Extern)}
    {td : TypeDef Nat Core3Extern} (h : Γ.types.map (·.def_) = tys ++ [td]) :
    Γ.type? tys.length = some td := by
  have hi : (Γ.types.map (·.def_))[tys.length]? = some td := by
    rw [h, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  rw [List.getElem?_map] at hi
  exact hi

/-- A value type definition followed by its type export pushes the resolved type twice. -/
theorem chk_defExport {s₁ s' : DefState Core3Extern} {d : Syntax.DefValType} {n' : Nat}
    (hlen : (ValidView s₁).1.length = n')
    (h : chks sc s₁ [.type (.val d), typeExport n'] = .ok s') :
    ∃ t', checkDefValType? Features.p2 s₁.ctx d = .ok t' ∧
      ValidView s' = ((ValidView s₁).1 ++ [.val t', .val t'], (ValidView s₁).2) := by
  obtain ⟨s₂, h₁, h₂⟩ := chks_cons h
  obtain ⟨s₃, h₃, h₄⟩ := chks_cons h₂
  have hs : s₃ = s' := by
    simp only [chks, checkDefs?] at h₄
    exact Except.ok.inj h₄
  obtain ⟨t', ht', hV₂⟩ := chk_typeVal h₁
  obtain ⟨e, he, hview⟩ := chk_export (it := ⟨.type, n'⟩) rfl h₃
  have hty : s₂.ctx.type? n' = some (.val t') := by
    rw [← hlen]
    exact type?_last (congrArg Prod.fst hV₂)
  have he' : e = .type (.val t') := by
    simp only [itemEntity?, hty, Option.map_some] at he
    exact (Option.some.inj he).symm
  refine ⟨t', ht', ?_⟩
  rw [← hs]
  show CtxView s₃.ctx = _
  rw [hview, he', pushEntity_type_view]
  show ((ValidView s₂).1 ++ [.val t'], (ValidView s₂).2) = _
  rw [hV₂, List.append_assoc]
  rfl

/-- The type definitions after `chk_defExport` end with the defined type. -/
theorem defExport_emit {s s₁ s' : DefState Core3Extern} {n' : Nat} {t' : WIT.ClosedType Nat}
    (hE : EmitOk s s₁ n')
    (hV : ValidView s' = ((ValidView s₁).1 ++ [.val t', .val t'], (ValidView s₁).2)) :
    EmitOk s s' (n' + 2) ∧ VRes (ValidView s').1 (.idx (n' + 1)) t' := by
  have hl : (ValidView s₁).1.length = n' := hE.2.1
  have hE₂ : EmitOk s₁ s' (n' + 2) := by
    have h₂ : (ValidView s').2 = (ValidView s₁).2 := by rw [hV]
    refine ⟨⟨_, congrArg Prod.fst hV⟩, ?_, h₂⟩
    rw [hV, List.length_append, hl]
    rfl
  have hidx : (ValidView s').1[n' + 1]? = some (.val t') := by
    rw [hV, List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left]
    rfl
  exact ⟨hE.trans hE₂, VRes.idx hidx⟩

/-- A record type: its fields' definitions, the record definition and its type export. -/
theorem record_case {s s' : DefState Core3Extern} {ts : List ValTy} {vs : List Syntax.VT}
    {ds : List (Syntax.Definition Silmaril.Wasm.Module)} {n' : Nat}
    (IH : ∀ s₁, chks sc s ds = .ok s₁ →
      EmitOk s s₁ n' ∧ List.Forall₂ (VRes (ValidView s₁).1) vs (toClList ts))
    (h : chks sc s (ds ++ [.type (.val (.record (labels "f" vs))), typeExport n']) = .ok s') :
    EmitOk s s' (n' + 2) ∧ VRes (ValidView s').1 (.idx (n' + 1)) (toCl (.record ts)) ∧
      WF (toCl (.record ts)) := by
  obtain ⟨s₁, h₁, h₂⟩ := chks_append h
  obtain ⟨hE, hF⟩ := IH s₁ h₁
  obtain ⟨t', ht', hV⟩ := chk_defExport hE.2.1 h₂
  have hres : resolveFields? s₁.ctx (labels "f" vs) = .ok (labels "f" (toClList ts)) :=
    resolveFields?_mapIdx (tag "f") (hF.imp fun _ _ hv => hv s₁.ctx (List.prefix_refl _))
  obtain ⟨rfl, hwf⟩ := checkDefValType?_record hres ht'
  have hD := defExport_emit hE hV
  exact ⟨hD.1, hD.2, hwf⟩

/-- A variant type: its cases' definitions, the variant definition and its type export. -/
theorem variant_case {s s' : DefState Core3Extern} {cs : List (Option ValTy)}
    {os : List (Option Syntax.VT)} {ds : List (Syntax.Definition Silmaril.Wasm.Module)} {n' : Nat}
    (IH : ∀ s₁, chks sc s ds = .ok s₁ →
      EmitOk s s₁ n' ∧ List.Forall₂ (VResO (ValidView s₁).1) os (toClCases cs))
    (h : chks sc s (ds ++ [.type (.val (.variant (labels "c" os))), typeExport n']) = .ok s') :
    EmitOk s s' (n' + 2) ∧ VRes (ValidView s').1 (.idx (n' + 1)) (toCl (.variant cs)) ∧
      WF (toCl (.variant cs)) := by
  obtain ⟨s₁, h₁, h₂⟩ := chks_append h
  obtain ⟨hE, hF⟩ := IH s₁ h₁
  obtain ⟨t', ht', hV⟩ := chk_defExport hE.2.1 h₂
  have hres : resolveCases? s₁.ctx (labels "c" os) = .ok (labels "c" (toClCases cs)) :=
    resolveCases?_mapIdx (tag "c") (hF.imp fun _ _ hv => hv s₁.ctx (List.prefix_refl _))
  obtain ⟨rfl, hwf⟩ := checkDefValType?_variant hres ht'
  have hD := defExport_emit hE hV
  exact ⟨hD.1, hD.2, hwf⟩

/-- The parts of a list of types: the head's definitions, then the tail's. -/
theorem cons_case {s s' : DefState Core3Extern} {n₁ n₂ : Nat}
    {ds ds' : List (Syntax.Definition Silmaril.Wasm.Module)} {P₁ : DefState Core3Extern → Prop}
    {P₂ : DefState Core3Extern → Prop}
    (IH₁ : ∀ s₁, chks sc s ds = .ok s₁ → EmitOk s s₁ n₁ ∧ P₁ s₁)
    (IH₂ : ∀ s₁ s₂, (ValidView s₁).1.length = n₁ → chks sc s₁ ds' = .ok s₂ →
      EmitOk s₁ s₂ n₂ ∧ P₂ s₂)
    (h : chks sc s (ds ++ ds') = .ok s') :
    ∃ s₁, EmitOk s s₁ n₁ ∧ EmitOk s₁ s' n₂ ∧ P₁ s₁ ∧ P₂ s' := by
  obtain ⟨s₁, h₁, h₂⟩ := chks_append h
  obtain ⟨hE₁, hP₁⟩ := IH₁ s₁ h₁
  obtain ⟨hE₂, hP₂⟩ := IH₂ s₁ s' hE₁.2.1 h₂
  exact ⟨s₁, hE₁, hE₂, hP₁, hP₂⟩

theorem chks_nil {s s' : DefState Core3Extern} (h : chks sc s [] = .ok s') : s' = s := by
  simp only [chks, checkDefs?] at h
  exact (Except.ok.inj h).symm

/-- A primitive type emits nothing and resolves to itself. -/
theorem prim_case {s s' : DefState Core3Extern} {n : Nat} (p : Syntax.Prim)
    (hl : (ValidView s).1.length = n) (h : chks sc s [] = .ok s') :
    EmitOk s s' n ∧ VRes (ValidView s').1 (.prim p) (primType p) := by
  have hs : s' = s := chks_nil h
  rw [hs]
  exact ⟨hl ▸ EmitOk.refl s, fun _ _ => rfl⟩

mutual
/-- **Validating the definitions emitted for an IR type** extends the type definitions, after
which the emitted value type resolves to `toCl t`, which is well formed. -/
theorem emitTy_chk : ∀ (t : ValTy) (n : Nat) (s s' : DefState Core3Extern),
    (ValidView s).1.length = n →
    chks sc s (emitTy (M := Silmaril.Wasm.Module) t n).2.1 = .ok s' →
    EmitOk s s' (emitTy (M := Silmaril.Wasm.Module) t n).2.2 ∧
      VRes (ValidView s').1 (emitTy (M := Silmaril.Wasm.Module) t n).1 (toCl t) ∧ WF (toCl t)
  | .bool, _, _, _, hl, h => ⟨(prim_case .bool hl h).1, (prim_case .bool hl h).2, .prim _⟩
  | .s8, _, _, _, hl, h => ⟨(prim_case .s8 hl h).1, (prim_case .s8 hl h).2, .prim _⟩
  | .u8, _, _, _, hl, h => ⟨(prim_case .u8 hl h).1, (prim_case .u8 hl h).2, .prim _⟩
  | .s16, _, _, _, hl, h => ⟨(prim_case .s16 hl h).1, (prim_case .s16 hl h).2, .prim _⟩
  | .u16, _, _, _, hl, h => ⟨(prim_case .u16 hl h).1, (prim_case .u16 hl h).2, .prim _⟩
  | .s32, _, _, _, hl, h => ⟨(prim_case .s32 hl h).1, (prim_case .s32 hl h).2, .prim _⟩
  | .u32, _, _, _, hl, h => ⟨(prim_case .u32 hl h).1, (prim_case .u32 hl h).2, .prim _⟩
  | .s64, _, _, _, hl, h => ⟨(prim_case .s64 hl h).1, (prim_case .s64 hl h).2, .prim _⟩
  | .u64, _, _, _, hl, h => ⟨(prim_case .u64 hl h).1, (prim_case .u64 hl h).2, .prim _⟩
  | .f32, _, _, _, hl, h => ⟨(prim_case .f32 hl h).1, (prim_case .f32 hl h).2, .prim _⟩
  | .f64, _, _, _, hl, h => ⟨(prim_case .f64 hl h).1, (prim_case .f64 hl h).2, .prim _⟩
  | .char, _, _, _, hl, h => ⟨(prim_case .char hl h).1, (prim_case .char hl h).2, .prim _⟩
  | .record ts, n, s, s', hl, h => by
    rcases he : emitTys (M := Silmaril.Wasm.Module) ts n with ⟨vs, ds, n'⟩
    have hdef : emitTy (M := Silmaril.Wasm.Module) (.record ts) n =
        (.idx (n' + 1), ds ++ [.type (.val (.record (labels "f" vs))), typeExport n'], n' + 2) := by
      simp only [emitTy, he]
    rw [hdef] at h ⊢
    refine record_case (fun s₁ h₁ => ?_) h
    have hI := emitTys_chk ts n s s₁ hl (by rw [he]; exact h₁)
    rw [he] at hI
    exact ⟨hI.1, hI.2.1⟩
  | .variant cs, n, s, s', hl, h => by
    rcases he : emitCases (M := Silmaril.Wasm.Module) cs n with ⟨os, ds, n'⟩
    have hdef : emitTy (M := Silmaril.Wasm.Module) (.variant cs) n =
        (.idx (n' + 1), ds ++ [.type (.val (.variant (labels "c" os))), typeExport n'], n' + 2) := by
      simp only [emitTy, he]
    rw [hdef] at h ⊢
    refine variant_case (fun s₁ h₁ => ?_) h
    have hI := emitCases_chk cs n s s₁ hl (by rw [he]; exact h₁)
    rw [he] at hI
    exact hI

/-- `emitTy_chk` on lists. -/
theorem emitTys_chk : ∀ (ts : List ValTy) (n : Nat) (s s' : DefState Core3Extern),
    (ValidView s).1.length = n →
    chks sc s (emitTys (M := Silmaril.Wasm.Module) ts n).2.1 = .ok s' →
    EmitOk s s' (emitTys (M := Silmaril.Wasm.Module) ts n).2.2 ∧
      List.Forall₂ (VRes (ValidView s').1) (emitTys (M := Silmaril.Wasm.Module) ts n).1
        (toClList ts) ∧ ∀ t ∈ ts, WF (toCl t)
  | [], n, s, s', hl, h => by
    have hs : s' = s := chks_nil h
    rw [hs]
    exact ⟨hl ▸ EmitOk.refl s, .nil, fun _ ht => absurd ht List.not_mem_nil⟩
  | t :: ts, n, s, s', hl, h => by
    rcases he : emitTy (M := Silmaril.Wasm.Module) t n with ⟨v, ds, n₁⟩
    rcases he' : emitTys (M := Silmaril.Wasm.Module) ts n₁ with ⟨vs, ds', n₂⟩
    have hdef : emitTys (M := Silmaril.Wasm.Module) (t :: ts) n = (v :: vs, ds ++ ds', n₂) := by
      simp only [emitTys, he, he']
    rw [hdef] at h ⊢
    obtain ⟨s₁, hE₁, hE₂, hP₁, hP₂⟩ := cons_case
      (P₁ := fun s₁ => VRes (ValidView s₁).1 v (toCl t) ∧ WF (toCl t))
      (P₂ := fun s₂ => List.Forall₂ (VRes (ValidView s₂).1) vs (toClList ts) ∧
        ∀ t ∈ ts, WF (toCl t))
      (fun s₁ h₁ => by
        have hI := emitTy_chk t n s s₁ hl (by rw [he]; exact h₁)
        rw [he] at hI
        exact ⟨hI.1, hI.2.1, hI.2.2⟩)
      (fun s₁ s₂ hl₁ h₂ => by
        have hI := emitTys_chk ts n₁ s₁ s₂ hl₁ (by rw [he']; exact h₂)
        rw [he'] at hI
        exact ⟨hI.1, hI.2.1, hI.2.2⟩) h
    refine ⟨hE₁.trans hE₂, .cons (hP₁.1.mono hE₂.prefix) hP₂.1, fun u hu => ?_⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hP₁.2
    · exact hP₂.2 u hu

/-- `emitTy_chk` on variant cases. -/
theorem emitCases_chk : ∀ (cs : List (Option ValTy)) (n : Nat) (s s' : DefState Core3Extern),
    (ValidView s).1.length = n →
    chks sc s (emitCases (M := Silmaril.Wasm.Module) cs n).2.1 = .ok s' →
    EmitOk s s' (emitCases (M := Silmaril.Wasm.Module) cs n).2.2 ∧
      List.Forall₂ (VResO (ValidView s').1) (emitCases (M := Silmaril.Wasm.Module) cs n).1
        (toClCases cs)
  | [], n, s, s', hl, h => by
    have hs : s' = s := chks_nil h
    rw [hs]
    exact ⟨hl ▸ EmitOk.refl s, .nil⟩
  | none :: cs, n, s, s', hl, h => by
    rcases he : emitCases (M := Silmaril.Wasm.Module) cs n with ⟨os, ds, n'⟩
    have hdef : emitCases (M := Silmaril.Wasm.Module) (none :: cs) n = (none :: os, ds, n') := by
      simp only [emitCases, he]
    rw [hdef] at h ⊢
    have hI := emitCases_chk cs n s s' hl (by rw [he]; exact h)
    rw [he] at hI
    exact ⟨hI.1, .cons (VResO.none _) hI.2⟩
  | some t :: cs, n, s, s', hl, h => by
    rcases he : emitTy (M := Silmaril.Wasm.Module) t n with ⟨v, ds, n₁⟩
    rcases he' : emitCases (M := Silmaril.Wasm.Module) cs n₁ with ⟨os, ds', n₂⟩
    have hdef : emitCases (M := Silmaril.Wasm.Module) (some t :: cs) n =
        (some v :: os, ds ++ ds', n₂) := by
      simp only [emitCases, he, he']
    rw [hdef] at h ⊢
    obtain ⟨s₁, hE₁, hE₂, hP₁, hP₂⟩ := cons_case (P₁ := fun s₁ => VRes (ValidView s₁).1 v (toCl t))
      (P₂ := fun s₂ => List.Forall₂ (VResO (ValidView s₂).1) os (toClCases cs))
      (fun s₁ h₁ => by
        have hI := emitTy_chk t n s s₁ hl (by rw [he]; exact h₁)
        rw [he] at hI
        exact ⟨hI.1, hI.2.1⟩)
      (fun s₁ s₂ hl₁ h₂ => by
        have hI := emitCases_chk cs n₁ s₁ s₂ hl₁ (by rw [he']; exact h₂)
        rw [he'] at hI
        exact hI) h
    exact ⟨hE₁.trans hE₂, .cons (VResO.some (hP₁.mono hE₂.prefix)) hP₂⟩
end

end Silmaril.Proofs.Wasm.Component.Reference
