module

public import Silmaril.Wasm.JcoTool.RefSimpleI.Defs
public import Silmaril.Proofs.Wasm.JcoTool.RefSimple.Read
import Silmaril.Wasm.Perf.ValidateR.Thms

/-!
# `ofRefI?` reads back `SimpleI.toRef`, and `checkI` decides the fragment

* `funcTyOf_emit`, `importPair?_spec`, `importsGroup_spec`: the imports;
* `dropLowers_spec`: the lowers;
* `exportAt?_spec`, `groupAt_spec`: the exports, aliased from core instance `inst` after `base`
  functions;
* `ofRefI?_toRef`: `ofRefI? c = some s` gives `s.toRef = c`;
* `checkI_spec`: `checkI s = true` gives `SimpleI.Good`, `FloatFree`, `Arity`, and `SimpleI.Inst`
  once the core module has an instance.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.RefSimpleI

open Silmaril.Wasm.Component (Syntax.Definition Syntax.Component Syntax.VT)
open Silmaril.Wasm.Component (ValTy FuncTy CoreFuncTy CoreIface Iface)
open Silmaril.Wasm.Component.Reference (SimpleI SimpleExport ImpModule labels Core3Component
  funcExportNames floatFreeList emitTys)
open Silmaril.Wasm.JcoTool.RefSimple (scalarVT resultsOf exportIface emitTys_scalar emitTys_results)

theorem ft_eq {ft : Silmaril.Wasm.Component.Syntax.FuncType} (ha : ft.async_ = false)
    (hp : ft.params = labels "a" (ft.params.map (·.2))) :
    ft = { params := labels "a" (ft.params.map (·.2)), result := ft.result.toList.head? } := by
  obtain ⟨a, p, r⟩ := ft
  have ha' : a = false := ha
  have hp' : p = labels "a" (p.map (·.2)) := hp
  rw [ha', ← hp']
  cases r <;> rfl

theorem en_eq {en : Silmaril.Wasm.Component.Syntax.ExternName} (h : en.attrs = []) :
    en = { name := en.name } := by
  obtain ⟨n, a⟩ := en
  have h' : a = [] := h
  rw [h']

/-- A function type read by `funcTyOf` is emitted back without type definitions. -/
theorem funcTyOf_emit {ft : Silmaril.Wasm.Component.Syntax.FuncType} {ty : FuncTy}
    (h : funcTyOf ft = some ty) (n : Nat) :
    emitTys (M := Silmaril.Wasm.Module) ty.params n = (ft.params.map (·.2), [], n) ∧
      emitTys (M := Silmaril.Wasm.Module) ty.results n = (ft.result.toList, [], n) ∧
      ft = { params := labels "a" (ft.params.map (·.2)), result := ft.result.toList.head? } := by
  unfold funcTyOf at h
  split at h
  · rename_i hc
    split at h
    · rename_i ps rs hps hrs
      cases h
      exact ⟨emitTys_scalar hps n, emitTys_results hrs n, ft_eq hc.1 hc.2⟩
    · cases h
  · cases h

theorem importPair?_spec {n : Nat} {d₁ d₂ : Syntax.Definition Silmaril.Wasm.Module}
    {p : String × FuncTy} (h : importPair? n d₁ d₂ = some p) :
    SimpleI.importDefs p n = ([d₁, d₂], n + 1) := by
  unfold importPair? at h
  split at h
  · rename_i ft en t
    split at h
    · rename_i hc
      obtain ⟨ty, hty, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨e₁, e₂, hft⟩ := funcTyOf_emit hty n
      obtain ⟨rfl, hen⟩ := hc
      simp only [SimpleI.importDefs, e₁, e₂, List.nil_append]
      rw [← hft, ← en_eq hen]
    · cases h
  · cases h

/-- **`importsGroup` reads back `SimpleI.importsDefs`.** -/
theorem importsGroup_spec (n : Nat) (c : Core3Component) :
    (SimpleI.importsDefs (importsGroup n c).1 n).1 ++ (importsGroup n c).2 = c ∧
      (SimpleI.importsDefs (importsGroup n c).1 n).2 = n + (importsGroup n c).1.length := by
  fun_induction importsGroup n c with
  | case1 n d₁ d₂ rest p hp r ih =>
    have e := importPair?_spec hp
    obtain ⟨ih₁, ih₂⟩ := ih
    refine ⟨?_, ?_⟩
    · show (SimpleI.importsDefs (p :: (importsGroup (n + 1) rest).1) n).1 ++
          (importsGroup (n + 1) rest).2 = _
      simp only [SimpleI.importsDefs, e, List.cons_append, List.nil_append, ih₁]
    · show (SimpleI.importsDefs (p :: (importsGroup (n + 1) rest).1) n).2 =
        n + (p :: (importsGroup (n + 1) rest).1).length
      simp only [SimpleI.importsDefs, e, List.length_cons]
      rw [ih₂]
      omega
  | case2 => exact ⟨rfl, by simp [SimpleI.importsDefs]⟩
  | case3 => exact ⟨rfl, by simp [SimpleI.importsDefs]⟩

/-- **`dropLowers` drops the lowers of `SimpleI.toRef`.** -/
theorem dropLowers_spec {α : Type} :
    ∀ {k m : Nat} {ds ds' : Core3Component}, dropLowers k m ds = some ds' →
      ∀ xs : List α, xs.length = m →
        ds = xs.mapIdx (fun j _ => (.canon (.lower (k + j) []) : Syntax.Definition _)) ++ ds' := by
  intro k m ds
  fun_induction dropLowers k m ds with
  | case1 => intro ds' h xs hx; cases h; simp_all
  | case2 m k rest ih =>
    intro ds' h xs hx
    obtain ⟨y, ys, rfl⟩ : ∃ y ys, xs = y :: ys := List.exists_cons_of_length_eq_add_one hx
    have e := ih h ys (by simpa using hx)
    simp only [List.mapIdx_cons, Nat.add_zero, List.cons_append, e]
    congr 2
    congr 1
    funext j _
    rw [Nat.add_assoc, Nat.add_comm 1 j]
  | case3 => intro ds' h; cases h
  | case4 => intro ds' h; cases h

/-- The definitions of one export, from the facts `exportAt?` checks. -/
theorem exportDefsAt_of {names : CoreIface} {inst base i n core : Nat}
    {ft : Silmaril.Wasm.Component.Syntax.FuncType} {ty : FuncTy} {cn : String}
    {en : Silmaril.Wasm.Component.Syntax.ExternName} (hty : funcTyOf ft = some ty)
    (hen : en.attrs = []) (hcn : (names[core]?).map (·.1) = some cn) :
    SimpleI.exportDefsAt names inst base i ⟨en.name, ty, core⟩ n =
      ([.type (.func ft), .alias (.coreExport inst cn .func), .canon (.lift (base + i) [] n),
        .export_ en ⟨.func, base + 2 * i⟩ none], n + 1) := by
  obtain ⟨e₁, e₂, hft⟩ := funcTyOf_emit hty n
  have hcore : ((names[core]?).map (·.1)).getD "" = cn := by rw [hcn]; rfl
  simp only [SimpleI.exportDefsAt, e₁, e₂, List.nil_append, hcore]
  rw [← hft, ← en_eq hen]

theorem exportAt?_spec {names : CoreIface} {inst base i n : Nat}
    {d₁ d₂ d₃ d₄ : Syntax.Definition Silmaril.Wasm.Module} {x : SimpleExport}
    (h : exportAt? names inst base i n d₁ d₂ d₃ d₄ = some x) :
    SimpleI.exportDefsAt names inst base i x n = ([d₁, d₂, d₃, d₄], n + 1) := by
  unfold exportAt? at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, rfl, hen⟩ := hc
      split at h
      · rename_i hty _
        split at h
        · cases h
          exact exportDefsAt_of hty hen ‹_›
        · cases h
      · cases h
    · cases h
  · cases h

/-- **`groupAt` reads back `SimpleI.exportsDefsAt`.** -/
theorem groupAt_spec {names : CoreIface} {inst base : Nat} :
    ∀ {i n : Nat} {ds : Core3Component} {xs : List SimpleExport},
      groupAt names inst base i n ds = some xs → SimpleI.exportsDefsAt names inst base i xs n = ds := by
  intro i n ds
  fun_induction groupAt names inst base i n ds with
  | case1 => intro xs h; cases h; rfl
  | case2 i n d₁ d₂ d₃ d₄ rest ih =>
    intro xs h
    obtain ⟨x, hx, xs', hxs', rfl⟩ : ∃ x, exportAt? names inst base i n d₁ d₂ d₃ d₄ = some x ∧
        ∃ xs', groupAt names inst base (i + 1) (n + 1) rest = some xs' ∧ x :: xs' = xs := by
      simpa [Option.bind_eq_some_iff] using h
    show SimpleI.exportsDefsAt names inst base i (x :: xs') n = _
    simp only [SimpleI.exportsDefsAt, exportAt?_spec hx, ih hxs', List.cons_append,
      List.nil_append]
  | case3 => intro xs h; cases h

/-- What `ofRefI?` checks. -/
theorem ofRefI?_inv {c : Core3Component} {s : SimpleI} (h : ofRefI? c = some s) :
    ∃ ims m rest₁ rest₂ imps ex es rest₃ xs,
      importsGroup 0 c = (ims, .coreModule m :: rest₁) ∧ dropLowers 0 ims.length rest₁ = some rest₂ ∧
      rest₂ = .coreInstance (.exports es) :: .coreInstance (.instantiate 0 [("env", 0)]) :: rest₃ ∧
      es = imps.mapIdx (fun k p => (p.1, ⟨.func, k⟩)) ∧
      groupAt ex 1 ims.length 0 ims.length rest₃ = some xs ∧ s = ⟨⟨m, imps, ex⟩, ims, xs⟩ := by
  unfold ofRefI? at h
  split at h
  split at h
  · obtain ⟨imps, -, h₁⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ex, -, h₂⟩ := Option.bind_eq_some_iff.1 h₁
    obtain ⟨rest₂, hd, h₃⟩ := Option.bind_eq_some_iff.1 h₂
    split at h₃
    · split at h₃
      · obtain ⟨xs, hxs, hs⟩ := Option.bind_eq_some_iff.1 h₃
        exact ⟨_, _, _, _, imps, ex, _, _, xs, ‹_›, hd, rfl, ‹_›, hxs, (Option.some.inj hs).symm⟩
      · cases h₃
    · cases h₃
  · cases h

/-- **`ofRefI?` reads back `SimpleI.toRef`.** -/
theorem ofRefI?_toRef {c : Core3Component} {s : SimpleI} (h : ofRefI? c = some s) :
    s.toRef = c := by
  obtain ⟨ims, m, rest₁, rest₂, imps, ex, es, rest₃, xs, hg, hd, h₂, hes, hxs, rfl⟩ :=
    ofRefI?_inv h
  have hspec := importsGroup_spec 0 c
  have hc : (SimpleI.importsDefs ims 0).1 ++ (.coreModule m :: rest₁) = c := by
    simpa only [hg] using hspec.1
  have hlen : (SimpleI.importsDefs ims 0).2 = 0 + ims.length := by simpa only [hg] using hspec.2
  have hr₁ := dropLowers_spec hd ims rfl
  have hx := groupAt_spec hxs
  show SimpleI.toRef ⟨⟨m, imps, ex⟩, ims, xs⟩ = c
  rw [← hc, hr₁, h₂, hes, ← hx]
  simp only [SimpleI.toRef, hlen, Nat.zero_add, List.append_assoc, List.cons_append,
    List.nil_append]

/-- The import types check. -/
theorem importTypesOk_spec {s : SimpleI} (h : importTypesOk s = true) :
    ∃ mt, Silmaril.Wasm.Validation.validate? s.mod.mod = some mt ∧
      mt.imports = s.imports.map fun p =>
        .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩) := by
  unfold importTypesOk at h
  rw [Silmaril.Wasm.Perf.ValidateR.validateR_eq] at h
  split at h
  · rename_i mt hv
    exact ⟨mt, hv, of_decide_eq_true h⟩
  · cases h

/-- **`checkI` decides the fragment conditions of `SimpleI.sound`.** -/
theorem checkI_spec {s : SimpleI} (h : checkI s = true) :
    s.Good ∧ s.FloatFree ∧ s.Arity ∧ ((∃ I, s.mod.IsInst I) → s.Inst) := by
  simp only [checkI, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hc⟩, himp⟩, hfe⟩, hfi⟩, hae⟩, hai⟩, hnm⟩, hin⟩, henv⟩, hty⟩ := h
  refine ⟨⟨hn, fun x hx => ?_, himp⟩, ⟨fun x hx => by simpa using hfe x hx,
    fun p hp => by simpa using hfi p hp⟩, ⟨fun x hx => by simpa [and_assoc] using hae x hx,
    fun p hp => by simpa [and_assoc] using hai p hp⟩, fun hi => ⟨hi, hnm, hin, henv,
    importTypesOk_spec hty⟩⟩
  obtain ⟨p, hp, hp2⟩ := Option.map_eq_some_iff.1 (hc x hx)
  exact ⟨p.1, by rw [hp, ← hp2]⟩

end Silmaril.Wasm.JcoTool.RefSimpleI
