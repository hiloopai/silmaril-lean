module

public import Silmaril.Wasm.JcoTool.RefSimple.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs

/-!
# `ofRef?` reads back `Simple.toRef`, and `check` decides the fragment

* `emitTy_scalar`, `emitTys_scalar`, `emitTys_results`: on scalar types, `Bridge.emitTy` emits no
  type definition and returns the primitive;
* `group_toRef`: `group nm i n ds = some xs` gives `Simple.exportsDefs nm i xs n = ds`;
* `ofRef?_toRef`: `ofRef? c = some s` gives `s.toRef = c`;
* `check_spec`: `check s = true` gives `Simple.Good`, `Simple.FloatFree`, `Simple.Arity` and the
  export names of `Simple.Inst`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.RefSimple

open Silmaril.Wasm.Component (Syntax.Definition Syntax.Component Syntax.VT Syntax.Prim)
open Silmaril.Wasm.Component (ValTy FuncTy CoreFuncTy CoreIface)
open Silmaril.Wasm.Component.Reference (Simple SimpleExport NumModule labels Core3Component
  funcExportNames floatFreeList emitTy emitTys)

theorem emitTy_scalar {v : Syntax.VT} {t : ValTy} (h : scalarVT v = some t) (n : Nat) :
    emitTy (M := Silmaril.Wasm.Module) t n = (v, [], n) := by
  rcases v with p | i
  · cases p <;> simp only [scalarVT, scalarOf, Option.some.injEq, reduceCtorEq] at h <;>
      (subst h; rfl)
  · exact absurd h (by simp [scalarVT])

theorem emitTys_scalar : ∀ {ps : List (String × Syntax.VT)} {ts : List ValTy},
    ps.mapM (fun p => scalarVT p.2) = some ts → ∀ n : Nat,
      emitTys (M := Silmaril.Wasm.Module) ts n = (ps.map (·.2), [], n)
  | [], ts, h, n => by
    have ht : ts = [] := by simpa using h.symm
    rw [ht]; rfl
  | p :: ps, ts, h, n => by
    obtain ⟨t, ht, ts', hts, rfl⟩ : ∃ t, scalarVT p.2 = some t ∧ ∃ ts',
        ps.mapM (fun p => scalarVT p.2) = some ts' ∧ t :: ts' = ts := by
      simpa [List.mapM_cons, Option.bind_eq_some_iff] using h
    have e₁ := emitTy_scalar ht n
    have e₂ := emitTys_scalar hts n
    simp only [emitTys, e₁, e₂, List.map_cons, List.nil_append]

theorem emitTys_results {r : Option Syntax.VT} {rs : List ValTy} (h : resultsOf r = some rs)
    (n : Nat) : emitTys (M := Silmaril.Wasm.Module) rs n = (r.toList, [], n) := by
  rcases r with _ | v
  · have hr : rs = [] := by simpa [resultsOf] using h.symm
    rw [hr]; rfl
  · obtain ⟨t, ht, rfl⟩ : ∃ t, scalarVT v = some t ∧ [t] = rs := by
      simpa [resultsOf] using h
    have e₁ := emitTy_scalar ht n
    simp only [emitTys, e₁, Option.toList_some, List.append_nil]

/-- One export group, read back. -/
theorem exportDefs_group {nm : NumModule} {i n : Nat}
    {ft : Silmaril.Wasm.Component.Syntax.FuncType} {cn : String}
    {en : Silmaril.Wasm.Component.Syntax.ExternName} {ps rs : List ValTy} {core : Nat}
    (ha : ft.async_ = false) (hen : en.attrs = [])
    (hp : ft.params = labels "a" (ft.params.map (·.2)))
    (hps : ft.params.mapM (fun p => scalarVT p.2) = some ps) (hrs : resultsOf ft.result = some rs)
    (hc : (nm.exports[core]?).map (·.1) = some cn) :
    Simple.exportDefs nm i ⟨en.name, ⟨ps, rs⟩, core⟩ n =
      ([.type (.func ft), .alias (.coreExport 0 cn .func), .canon (.lift i [] n),
        .export_ en ⟨.func, 2 * i⟩ none], n + 1) := by
  have e₁ := emitTys_scalar hps n
  have e₂ := emitTys_results hrs n
  have hcore : ((nm.exports[core]?).map (·.1)).getD "" = cn := by rw [hc]; rfl
  have hft : ft = { params := labels "a" (ft.params.map (·.2)), result := ft.result.toList.head? } := by
    obtain ⟨a, p, r⟩ := ft
    have ha' : a = false := ha
    have hp' : p = labels "a" (p.map (·.2)) := hp
    rw [ha', ← hp']
    cases r <;> rfl
  have hen' : en = { name := en.name } := by
    obtain ⟨nm', at'⟩ := en
    have h' : at' = [] := hen
    rw [h']
  simp only [Simple.exportDefs, e₁, e₂, List.nil_append, hcore]
  rw [← hft, ← hen']

/-- **`group` reads back `Simple.exportsDefs`.** -/
theorem group_toRef {nm : NumModule} :
    ∀ {i n : Nat} {ds : Syntax.Component Silmaril.Wasm.Module} {xs : List SimpleExport},
      group nm i n ds = some xs → Simple.exportsDefs nm i xs n = ds := by
  intro i n ds
  fun_induction group nm i n ds with
  | case1 => intro xs h; cases h; rfl
  | case2 i n ft cn i' os n' en k rest hcond ps rs core _ hrs hps hc ih =>
    intro xs h
    obtain ⟨ha, hi, ho, hn, hk, hen, hp⟩ := hcond
    subst i' os n' k
    obtain ⟨xs', hxs', rfl⟩ := Option.map_eq_some_iff.1 h
    show Simple.exportsDefs nm i (⟨en.name, ⟨ps, rs⟩, core⟩ :: xs') n = _
    simp only [Simple.exportsDefs, exportDefs_group ha hen hp hps hrs hc, ih hxs',
      List.cons_append, List.nil_append]
  | case3 => intro xs h; cases h
  | case4 => intro xs h; cases h
  | case5 => intro xs h; cases h
  | case6 => intro xs h; cases h

/-- **`ofRef?` reads back `Simple.toRef`.** -/
theorem ofRef?_toRef {c : Core3Component} {s : Simple} (h : ofRef? c = some s) : s.toRef = c := by
  unfold ofRef? at h
  split at h
  · rename_i m rest
    obtain ⟨ex, -, xs, hxs, rfl⟩ : ∃ ex, exportIface m = some ex ∧ ∃ xs,
        group ⟨m, ex⟩ 0 0 rest = some xs ∧ (⟨⟨m, ex⟩, xs⟩ : Simple) = s := by
      simpa [Option.bind_eq_some_iff] using h
    show [.coreModule m, .coreInstance (.instantiate 0 [])] ++ Simple.exportsDefs ⟨m, ex⟩ 0 xs 0 = _
    rw [group_toRef hxs]; rfl
  · cases h

/-- **`check` decides the fragment conditions.** -/
theorem check_spec {s : Simple} (h : check s = true) :
    s.Good ∧ s.FloatFree ∧ s.Arity ∧ funcExportNames s.mod.mod = s.mod.exports.map (·.1) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hc⟩, hf⟩, ha⟩, hx⟩ := h
  refine ⟨⟨hn, fun x hx' => ?_⟩, fun x hx' => by simpa using hf x hx', fun x hx' => by
    simpa [and_assoc] using ha x hx', hx⟩
  obtain ⟨p, hp, hp2⟩ := Option.map_eq_some_iff.1 (hc x hx')
  exact ⟨p.1, by rw [hp, ← hp2]⟩

end Silmaril.Wasm.JcoTool.RefSimple
