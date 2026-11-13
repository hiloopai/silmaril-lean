module

public import Silmaril.Wasm.Component.Algebra.WacShapes.Defs
public import Silmaril.Wasm.Component.Algebra.Ops.Thms
public import Silmaril.Wasm.Component.Algebra.Plug.Thms
public import Silmaril.Games.Handler.Thms

/-!
# WAC statement shapes: lemmas

* `resolve_congr`, `tyOf_congr`, `mkNodes_congr`: the wiring of a graph depends on its
  instances only, not on its exports or declared imports;
* `getElem?_filterMap_get`, `implsH_filterMap`: keeping the exports of indices `keep` is
  `selectH keep` above the export handler.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra.WacShapesProof

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Wac

variable {M : Type}

theorem offset_congr {S : Nat → PkgSig} {g g' : Graph} (h : g.nodes = g'.nodes) :
    g.offset S = g'.offset S := by
  funext k
  simp only [Graph.offset, h]

theorem resolve_congr {S : Nat → PkgSig} {g g' : Graph} (h : g.nodes = g'.nodes) (I : Iface)
    (b : Nat) : g.resolve S I b = g'.resolve S I b := by
  funext s
  cases s with
  | imp x => rfl
  | out k q => simp only [Graph.resolve, h, offset_congr (S := S) h]

theorem tyOf_congr {S : Nat → PkgSig} {g g' : Graph} (h : g.nodes = g'.nodes) (I : Iface) :
    g.tyOf S I = g'.tyOf S I := by
  funext s
  cases s with
  | imp x => rfl
  | out k q => simp only [Graph.tyOf, h]

theorem mkNodes_congr {S : Nat → PkgSig} (P : Nat → Comp M) {g g' : Graph}
    (h : g.nodes = g'.nodes) (I : Iface) :
    ∀ (k : Nat) (ns : List Inst), g.mkNodes S P I k ns = g'.mkNodes S P I k ns
  | _, [] => rfl
  | k, n :: ns => by
    simp only [Graph.mkNodes, Graph.argsOf, resolve_congr h, mkNodes_congr P h I (k + 1) ns]

/-- Keeping entries by index, then reading one: the index among the kept indices in range. -/
theorem getElem?_filterMap_get {α : Type} (l : List α) :
    ∀ (keep : List Nat) (i : Nat), (keep.filterMap fun j => l[j]?)[i]? =
      ((keep.filter (· < l.length))[i]?).bind fun j => l[j]?
  | [], i => by simp
  | j :: keep, i => by
    by_cases hj : j < l.length
    · have hs : l[j]? = some l[j] := List.getElem?_eq_getElem hj
      cases i with
      | zero => simp [hj]
      | succ i =>
        simp only [List.filterMap_cons, hs, List.filter_cons, hj, decide_true, ↓reduceIte,
          List.getElem?_cons_succ]
        exact getElem?_filterMap_get l keep i
    · have hs : l[j]? = none := List.getElem?_eq_none (by omega)
      simp only [List.filterMap_cons, hs, List.filter_cons, hj, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact getElem?_filterMap_get l keep i

theorem length_filterMap_get {α : Type} (l : List α) :
    ∀ keep : List Nat, (keep.filterMap fun j => l[j]?).length = (keep.filter (· < l.length)).length
  | [] => rfl
  | j :: keep => by
    by_cases hj : j < l.length
    · have hs : l[j]? = some l[j] := List.getElem?_eq_getElem hj
      simp only [List.filterMap_cons, hs, List.filter_cons, hj, decide_true, ↓reduceIte,
        List.length_cons, length_filterMap_get l keep]
    · have hs : l[j]? = none := List.getElem?_eq_none (by omega)
      simp only [List.filterMap_cons, hs, List.filter_cons, hj, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact length_filterMap_get l keep

/-- **Keeping the exports of indices `keep` is selection above the export handler.** -/
theorem implsH_filterMap (e : Nat) (ims : List Impl) (keep : List Nat) :
    implsH e (keep.filterMap fun j => ims[j]?) =
      (implsH e ims).comp (selectH (keep.filter (· < ims.length))) := by
  funext q
  obtain ⟨i, a⟩ := q
  have hk := getElem?_filterMap_get ims keep i
  simp only [implsH, Handler.comp, selectH, hk]
  cases (keep.filter (· < ims.length))[i]? with
  | none => simp only [Option.bind_none, Prog.interp_pure]
  | some j =>
    simp only [Option.bind_some, Prog.interp_call, Prog.interp_pure, Prog.bind_pure]
    rfl

end Silmaril.Wasm.Component.Algebra.WacShapesProof
