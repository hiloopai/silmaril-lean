module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflInstr
public import Silmaril.Wasm.Models.Syntax.Defs

/-!
# Reflecting constant expressions, limits and external types

Module validation checks constant expressions in contexts whose globals differ between the two
versions: Core 3.0 lets a global initialiser read the globals defined before it and checks
element and data segments in the full module context, while 2.0 only ever offers the imported
globals (`6-typing:703`). `RelK C D` is the relation for this: the Core context `D` has the
functions, references and well-formedness of the image of `C`, and the globals of `C` are a
prefix of those of `D`. A `global.get` that reads below that prefix (`ConstReadsImports`) then
reads the same global on both sides.

* `const_refl`: a Core constant expression of `v20` (a single constant instruction,
  `simpleConst`) on the image of a 2.0 expression reflects to a 2.0 constant expression;
* `limits_of`, `tableTypeOk_of`, `memTypeOk_of`, `import_refl`: limits, table and memory types
  and imports reflect;
* `forall₂_lift`, `forall₂_mapM_lift`: reading back a `Forall₂` premise along a list map.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC liftResult)
open Silmaril.Wasm.Validation (TypeCtx TyOk)

/-! ## Lists -/

/-- Reading a `Forall₂` premise on a mapped list back to the source list. -/
theorem forall₂_lift {α β γ δ : Type} {f : α → β} {R : β → γ → Prop} {S : α → δ → Prop}
    {g : δ → γ} (hRS : ∀ a c, R (f a) c → ∃ d, S a d ∧ c = g d) :
    ∀ {l : List α} {l' : List γ}, List.Forall₂ R (l.map f) l' →
      ∃ l'' : List δ, List.Forall₂ S l l'' ∧ l' = l''.map g
  | [], _, .nil => ⟨[], .nil, rfl⟩
  | _ :: _, _, .cons h hs =>
    let ⟨d, hd, e⟩ := hRS _ _ h
    let ⟨l'', h'', e'⟩ := forall₂_lift hRS hs
    ⟨d :: l'', .cons hd h'', by rw [e, e']; rfl⟩

/-- Reading a `Forall₂` premise on a `mapM` image back to the source list. -/
theorem forall₂_mapM_lift {α β γ δ : Type} {f : α → Option β} {R : β → γ → Prop}
    {S : α → δ → Prop} {g : δ → γ}
    (hRS : ∀ a b c, f a = some b → R b c → ∃ d, S a d ∧ c = g d) :
    ∀ {l : List α} {lb : List β} {l' : List γ}, l.mapM f = some lb → List.Forall₂ R lb l' →
      ∃ l'' : List δ, List.Forall₂ S l l'' ∧ l' = l''.map g
  | [], lb, _, hm, h => by
    obtain rfl : lb = [] := (Option.some.inj hm).symm
    cases h
    exact ⟨[], .nil, rfl⟩
  | a :: l, lb, l', hm, h => by
    obtain ⟨b, hb, lb', hlb', rfl⟩ : ∃ b, f a = some b ∧ ∃ lb', l.mapM f = some lb' ∧
        b :: lb' = lb := by
      simpa [List.mapM_cons, Option.bind_eq_some_iff] using hm
    cases h with
    | cons hr hs =>
      obtain ⟨d, hd, rfl⟩ := hRS a b _ hb hr
      obtain ⟨l'', h'', rfl⟩ := forall₂_mapM_lift hRS hlb' hs
      exact ⟨d :: l'', .cons hd h'', rfl⟩

/-- Membership in a `mapM` image. -/
theorem mem_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {lb : List β}, l.mapM f = some lb → ∀ b ∈ lb, ∃ a ∈ l, f a = some b :=
  fun h b hb => Silmaril.Wasm.V2.Validation.mem_of_mapM h b hb

/-! ## Limits and external types -/

theorem limits_of {l : Silmaril.Wasm.V2.Limits} {k : Nat}
    (h : Silmaril.Wasm.Limits.Valid k l.toCore) : Silmaril.Wasm.V2.Limits.Ok k l := by
  obtain ⟨hmin, hmax⟩ := h
  refine ⟨hmin, ?_⟩
  rcases hm : l.max with _ | mx
  · trivial
  · simpa [Silmaril.Wasm.V2.Limits.toCore, hm, Silmaril.Wasm.V2.widen32] using hmax

theorem tableTypeOk_of {Δ : TypeCtx} {t : Silmaril.Wasm.V2.TableType}
    (h : Silmaril.Wasm.Validation.TableTypeOk Δ (tableToC t)) :
    Silmaril.Wasm.V2.TableType.Ok t :=
  limits_of (k := 2 ^ 32 - 1) h.1

theorem memTypeOk_of {t : Silmaril.Wasm.V2.MemoryType}
    (h : Silmaril.Wasm.Validation.MemTypeOk t.toCore) :
    Silmaril.Wasm.V2.MemoryType.Ok t :=
  limits_of (k := 2 ^ 16) h

theorem externTypeOk_of {Δ : TypeCtx} {xt : Silmaril.Wasm.V2.ExternType}
    (h : Silmaril.Wasm.Validation.ExternTypeOk Δ xt.toCore) :
    Silmaril.Wasm.V2.ExternType.Ok xt := by
  cases xt with
  | func t => trivial
  | global t => trivial
  | table t => cases h with | table h => exact tableTypeOk_of h
  | memory t => cases h with | mem h => exact memTypeOk_of h

/-- `Import_ok` reflects: the Core extern type is the image of the 2.0 one. -/
theorem import_refl {types : List Silmaril.Wasm.V2.FuncType} {i : Silmaril.Wasm.V2.Import}
    {xt : Silmaril.Wasm.Validation.CExternType}
    (h : Silmaril.Wasm.Validation.ImportOk { types := types.map Silmaril.Wasm.V2.FuncType.toDefType }
      i.toCore xt) :
    ∃ vx, Silmaril.Wasm.V2.Validation.ImportOk { types := types } i vx ∧ xt = vx.toCore := by
  obtain ⟨hx, hok⟩ := h
  rcases i with ⟨mn, n, d⟩
  cases d with
  | func x =>
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨ft, hft, rfl⟩ := getElem?_map_some hd
    exact ⟨.func ft, ⟨by simp [Silmaril.Wasm.V2.Module.importType?, hft], trivial⟩, rfl⟩
  | table t =>
    obtain rfl := (Option.some.inj hx).symm
    exact ⟨.table t, ⟨rfl, externTypeOk_of (xt := .table t) (by simpa using hok)⟩, by simp⟩
  | memory t =>
    obtain rfl := (Option.some.inj hx).symm
    exact ⟨.memory t, ⟨rfl, externTypeOk_of (xt := .memory t) hok⟩, rfl⟩
  | global t =>
    obtain rfl := (Option.some.inj hx).symm
    exact ⟨.global t, ⟨rfl, trivial⟩, by simp⟩

/-! ## Constant expressions -/

/-- The relation for constant expressions: functions and references are the image, the globals
of `C` are a prefix of those of `D`, and `D` is well formed. -/
structure RelK (C : VCtx) (D : KCtx) : Prop where
  funcs : D.funcs = C.funcs.map Silmaril.Wasm.V2.FuncType.toDefType
  globals : C.globals.map globalToC <+: D.globals
  refs : D.refs = C.refs.map Silmaril.Wasm.Idx.toNat
  recs : D.recs = []
  wf : D.Wf

/-- `RelK` from an image context with the same functions and references. -/
theorem RelK.of_rel {C Cx : VCtx} {D : KCtx} (hR : Rel Cx D) (hf : C.funcs = Cx.funcs)
    (hg : C.globals.map globalToC <+: D.globals) (hr : C.refs = Cx.refs) : RelK C D where
  funcs := hf ▸ hR.funcs
  globals := hg
  refs := hr ▸ hR.refs
  recs := hR.recs
  wf := hR.wf

/-- A global below the prefix. -/
theorem RelK.global_get {C : VCtx} {D : KCtx} (hK : RelK C D) {x : Nat}
    {g : Silmaril.Wasm.Validation.CGlobalType} (hx : x < C.globals.length)
    (h : D.globals[x]? = some g) : ∃ gt, C.globals[x]? = some gt ∧ globalToC gt = g := by
  have hC : (C.globals.map globalToC)[x]? = some (globalToC C.globals[x]) := by simp [hx]
  have e := Silmaril.Wasm.V2.Validation.prefix_getElem? hK.globals hC
  rw [h] at e
  exact ⟨_, List.getElem?_eq_getElem hx, (Option.some.inj e).symm⟩

/-- `global.get` of an imported global, under `RelK`. -/
theorem k_globalGet {C : VCtx} {D : KCtx} {it : Silmaril.Wasm.Validation.InstrType}
    (hK : RelK C D) {x : Silmaril.Wasm.GlobalIdx} (hx : x.toNat < C.globals.length)
    (h : KOk D (.globalGet x) it) :
    VSeq C [.globalGet x] (erT D.toTypeCtx it) := by
  cases h
  case «variable» h =>
    cases h with
    | globalGet ht =>
      obtain ⟨gt, hgt, e⟩ := hK.global_get hx ht
      obtain rfl := (congrArg Silmaril.Wasm.Validation.CGlobalType.type e).symm
      simp only [erT, ers, List.map_cons, List.map_nil, globalToC, er_toC]
      exact vone (.globalGet hgt)
  all_goals (rename_i h; cases h)

/-- `ref.func`, under `RelK`. -/
theorem k_refFunc {C : VCtx} {D : KCtx} {it : Silmaril.Wasm.Validation.InstrType}
    (hK : RelK C D) {x : Silmaril.Wasm.FuncIdx} (h : KOk D (.refFunc x) it) :
    VSeq C [.refFunc x] (erT D.toTypeCtx it) := by
  cases h
  case reference h =>
    cases h with
    | refFunc hd hr =>
      obtain ⟨ft, hft, rfl⟩ := getElem?_map_some (hK.funcs ▸ hd)
      have hr' : x ∈ C.refs := by
        have hr₁ : x.toNat ∈ C.refs.map Silmaril.Wasm.Idx.toNat := hK.refs ▸ hr
        obtain ⟨y, hy, e⟩ := List.mem_map.mp hr₁
        have hyx : y = x := by
          cases x; cases y
          simp only [Silmaril.Wasm.Idx.toNat] at e
          exact congrArg _ (Fin.ext e)
        exact hyx ▸ hy
      simp only [erT, ers, List.map_cons, List.map_nil, Silmaril.Wasm.Validation.Ty.refT,
        er_defHeap]
      exact vone (.refFunc hft hr')
  all_goals (rename_i h; cases h)

/-- The heap type of a 2.0 `ref.null` image. -/
theorem ofCoreHeap_inv {h : Silmaril.Wasm.HeapType} {rt : Silmaril.Wasm.V2.RefType}
    (e : Silmaril.Wasm.V2.RefType.ofCoreHeap? h = some rt) : h = rt.toCoreHeap := by
  rcases h with a | x
  · cases a <;> simp [Silmaril.Wasm.V2.RefType.ofCoreHeap?] at e <;> subst e <;> rfl
  · simp [Silmaril.Wasm.V2.RefType.ofCoreHeap?] at e

/-- A global read below a prefix of the globals. -/
theorem prefix_global {C : VCtx} {D : KCtx} (hg : C.globals.map globalToC <+: D.globals) {x : Nat}
    {g : Silmaril.Wasm.Validation.CGlobalType} (hx : x < C.globals.length)
    (h : D.globals[x]? = some g) : ∃ gt, C.globals[x]? = some gt ∧ globalToC gt = g := by
  have hC : (C.globals.map globalToC)[x]? = some (globalToC C.globals[x]) := by simp [hx]
  have e := Silmaril.Wasm.V2.Validation.prefix_getElem? hg hC
  rw [h] at e
  exact ⟨_, List.getElem?_eq_getElem hx, (Option.some.inj e).symm⟩

/-- The 2.0 instruction of a `v20` constant Core instruction is a 2.0 constant instruction. -/
theorem const_shape {C : VCtx} {D : KCtx} (hglob : C.globals.map globalToC <+: D.globals)
    {i : Silmaril.Wasm.V2.Instr} {c : Silmaril.Wasm.Instr}
    (hi : Silmaril.Wasm.V2.Instr.toCore i = some c)
    (hs : Silmaril.Wasm.Models.simpleConst [c] = true)
    (hcst : Silmaril.Wasm.Validation.InstrConst D c)
    (hg : ∀ x, i = .globalGet x → x.toNat < C.globals.length) :
    Silmaril.Wasm.V2.Validation.InstrConst C i := by
  have hof := Silmaril.Wasm.V2.Instr.ofCore?_toCore hi
  match c, hs, hof, hcst with
  | .intConst _ _, _, hof, _ => obtain rfl := (Option.some.inj hof).symm; exact .intConst _ _
  | .floatConst _ _, _, hof, _ => obtain rfl := (Option.some.inj hof).symm; exact .floatConst _ _
  | .vecConst _, _, hof, _ => obtain rfl := (Option.some.inj hof).symm; exact .vecConst _
  | .refFunc _, _, hof, _ => obtain rfl := (Option.some.inj hof).symm; exact .refFunc _
  | .refNull _, _, hof, _ =>
    obtain ⟨rt, -, rfl⟩ := Option.map_eq_some_iff.mp hof
    exact .refNull _
  | .globalGet x, _, hof, .globalGet hx =>
    obtain rfl := (Option.some.inj hof).symm
    obtain ⟨gt, hgt, e⟩ := prefix_global hglob (hg x rfl) hx
    exact .globalGet hgt (congrArg Silmaril.Wasm.Validation.CGlobalType.mutability e)

/-- The typing of a 2.0 constant instruction reflects. -/
theorem const_typed {C : VCtx} {D : KCtx} {it : Silmaril.Wasm.Validation.InstrType}
    (hK : RelK C D) {i : Silmaril.Wasm.V2.Instr} {c : Silmaril.Wasm.Instr}
    (hi : Silmaril.Wasm.V2.Instr.toCore i = some c)
    (hs : Silmaril.Wasm.Models.simpleConst [c] = true)
    (hg : ∀ x, i = .globalGet x → x.toNat < C.globals.length) (h : KOk D c it) :
    VSeq C [i] (erT D.toTypeCtx it) := by
  have hof := Silmaril.Wasm.V2.Instr.ofCore?_toCore hi
  match c, hs, hof with
  | .intConst _ _, _, hof => obtain rfl := (Option.some.inj hof).symm; exact r_intConst h
  | .floatConst _ _, _, hof => obtain rfl := (Option.some.inj hof).symm; exact r_floatConst h
  | .vecConst _, _, hof => obtain rfl := (Option.some.inj hof).symm; exact r_vecConst h
  | .refFunc _, _, hof => obtain rfl := (Option.some.inj hof).symm; exact k_refFunc hK h
  | .refNull _, _, hof =>
    obtain ⟨rt, hrt, rfl⟩ := Option.map_eq_some_iff.mp hof
    obtain rfl := ofCoreHeap_inv hrt
    exact r_refNull h
  | .globalGet x, _, hof =>
    obtain rfl := (Option.some.inj hof).symm
    exact k_globalGet hK (hg x rfl) h

/-- A sequence of two or more instructions is not a simple constant expression. -/
theorem simpleConst_two (a b : Silmaril.Wasm.Instr) (l : List Silmaril.Wasm.Instr) :
    Silmaril.Wasm.Models.simpleConst (a :: b :: l) = false := by
  cases a <;> rfl

/-- A constant expression of `v20` is empty or a single instruction. -/
theorem simpleConst_cases {ce : List Silmaril.Wasm.Instr} (hs : Silmaril.Wasm.Models.simpleConst ce = true) :
    ce = [] ∨ ∃ c, ce = [c] ∧ Silmaril.Wasm.Models.simpleConst [c] = true := by
  match ce, hs with
  | [], _ => exact .inl rfl
  | [c], hs => exact .inr ⟨c, rfl, hs⟩
  | a :: b :: l, hs => exact absurd hs (by rw [simpleConst_two]; decide)

/-- The image of a single-instruction expression. -/
theorem toCore_single_inv {e : List Silmaril.Wasm.V2.Instr} {c : Silmaril.Wasm.Instr}
    (h : Silmaril.Wasm.V2.Expr.toCore e = some [c]) :
    ∃ i, e = [i] ∧ Silmaril.Wasm.V2.Instr.toCore i = some c := by
  obtain ⟨i, e', rfl, hi, he'⟩ := toCore_cons_inv h
  obtain rfl := toCore_nil_inv he'
  exact ⟨i, rfl, hi⟩

/-- **The constant-instruction part of a constant expression reflects.** -/
theorem exprConst_refl {C : VCtx} {D : KCtx} (hglob : C.globals.map globalToC <+: D.globals)
    {e : List Silmaril.Wasm.V2.Instr} {ce : List Silmaril.Wasm.Instr}
    (hc : Silmaril.Wasm.V2.Expr.toCore e = some ce) (hs : Silmaril.Wasm.Models.simpleConst ce = true)
    (hk : Silmaril.Wasm.Validation.ExprConst D ce)
    (hg : ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ e → x.toNat < C.globals.length) :
    Silmaril.Wasm.V2.Validation.ExprConst C e := by
  rcases simpleConst_cases hs with rfl | ⟨c, rfl, hs₁⟩
  · obtain rfl := toCore_nil_inv hc
    exact Silmaril.Wasm.V2.Validation.exprConst_nil C
  · obtain ⟨i, rfl, hi⟩ := toCore_single_inv hc
    have hci : Silmaril.Wasm.V2.Validation.InstrConst C i :=
      const_shape hglob hi hs₁ (hk c (by simp)) (fun x e => hg x (by simp [e]))
    exact Silmaril.Wasm.V2.Validation.ExprConst.cons hci
      (Silmaril.Wasm.V2.Validation.exprConst_nil C)

/-- The result of a single Core instruction typed at `[] -> [t]`, up to subsumption. -/
theorem single_const_inv {D : KCtx} (hwf : D.Wf) {c : Silmaril.Wasm.Instr} {t : KVal}
    (h : Silmaril.Wasm.Validation.InstrsOk D [c] (.plain [] [t])) :
    ∃ it₀, KOk D c it₀ ∧ it₀.params = [] ∧
      Silmaril.Wasm.Validation.ResultSub D.toTypeCtx it₀.results [t] := by
  obtain ⟨ts, it₀, hi, hs⟩ := Silmaril.Wasm.Validation.InstrsOk.single_inv hwf h
  have hp : ts ++ it₀.params = [] := List.forall₂_nil_left_iff.mp hs.1
  obtain ⟨rfl, hp'⟩ := List.append_eq_nil_iff.mp hp
  exact ⟨it₀, hi, hp', by simpa using hs.2.1⟩

/-- **Constant expressions reflect.** -/
theorem const_refl {C : VCtx} {D : KCtx} (hK : RelK C D) {e : List Silmaril.Wasm.V2.Instr}
    {ce : List Silmaril.Wasm.Instr} (hc : Silmaril.Wasm.V2.Expr.toCore e = some ce)
    (hs : Silmaril.Wasm.Models.simpleConst ce = true) {tv : Silmaril.Wasm.V2.ValType}
    (hk : Silmaril.Wasm.Validation.ExprOkConst D ce (Silmaril.Wasm.V2.ValType.toC tv))
    (hg : ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ e → x.toNat < C.globals.length) :
    Silmaril.Wasm.V2.Validation.ExprOkConst C e tv := by
  have hconst : Silmaril.Wasm.V2.Validation.ExprConst C e :=
    exprConst_refl hK.globals hc hs hk.const hg
  rcases simpleConst_cases hs with rfl | ⟨c, rfl, hs₁⟩
  · have hn := (Silmaril.Wasm.Validation.InstrsOk.nil_inv hK.wf hk.typed).1
    cases hn
  · obtain ⟨i, rfl, hi⟩ := toCore_single_inv hc
    obtain ⟨it₀, hi₀, hp, hr⟩ := single_const_inv hK.wf hk.typed
    have v : VSeq C [i] (erT D.toTypeCtx it₀) :=
      const_typed hK hi hs₁ (fun x e => hg x (by simp [e])) hi₀
    have hsub : Silmaril.Wasm.V2.Validation.CResultType.Sub (ers D.toTypeCtx it₀.results)
        [.val tv] := by
      have := ers_sub hK.wf.types hK.recs (hi₀.regular hK.wf).2.1
        (fun t ht => by simp at ht; exact ht ▸ Silmaril.Wasm.V2.Validation.tyOk_toC _ tv) hr
      simpa using this
    refine ⟨.sub v ⟨?_, hsub⟩, hconst⟩
    simp [erT, hp]

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
