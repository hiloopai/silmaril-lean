module

public import Silmaril.Wasm.JcoTool.LayoutRefX.Defs
public import Silmaril.Wasm.JcoTool.LayoutRef.Thms

/-!
# `toRefX` extends `toRef` and keeps its index spaces

* `secToX_of`, `toRefX_of_toRef`: where `toRef` succeeds, `toRefX` gives the same definitions;
* `xsecX_eq`, `spacesRef_toRefX`: the spaces of `toRefX x` are `Layout.spaces x` translated
  (`mapRS`), as for `toRef` (`LayoutRef.spacesRef_toRef`): core types, of functions or modules,
  are in none of the spaces either reading keeps, and nested components are one definition of
  the untracked sort `component` whatever their content.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.LayoutRefX

open Silmaril.Wasm.JcoTool.LayoutRef
open Silmaril.Wasm.Component (Syntax.Definition Syntax.Component)

section
variable {M : Type} {rd : ByteArray → Option M}

theorem coreTypeToX_of {t : B.CoreType} {d : Silmaril.Wasm.Component.Syntax.CoreTypeDef}
    (h : coreTypeTo t = some d) : coreTypeToX t = some d := by
  cases t with
  | func t => exact h
  | module _ => cases h

theorem mapM_of {α β : Type} {f g : α → Option β} (H : ∀ a b, f a = some b → g a = some b) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.mapM g = some ys
  | [], ys, h => h
  | x :: xs, ys, h => by
    obtain ⟨b, hb, bs, hbs, rfl⟩ : ∃ b, f x = some b ∧ ∃ bs, xs.mapM f = some bs ∧ b :: bs = ys := by
      simpa [List.mapM_cons, Option.bind_eq_some_iff] using h
    simp [List.mapM_cons, H x b hb, mapM_of H hbs]

mutual
theorem secToX_of : ∀ (s : B.Section) {ds : List (Syntax.Definition M)},
    secTo rd s = some ds → secToX rd s = some ds
  | .coreTypes xs, ds, h => by
    obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.1 h
    show (xs.mapM coreTypeToX).map _ = _
    rw [mapM_of (fun _ _ => coreTypeToX_of) hys]; rfl
  | .component (.mk ss), ds, h => by
    obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.1 h
    show (secsToX rd ss).map _ = _
    rw [secsToX_of ss hys]; rfl
  | .custom _ _, _, h | .coreModule _, _, h | .coreInstances _, _, h | .instances _, _, h
  | .aliases _, _, h | .types _, _, h | .canons _, _, h | .start _, _, h | .imports _, _, h
  | .exports _, _, h | .values _, _, h => h
theorem secsToX_of : ∀ (ss : List B.Section) {ds : List (Syntax.Definition M)},
    secsTo rd ss = some ds → secsToX rd ss = some ds
  | [], _, h => h
  | s :: ss, ds, h => by
    obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a, secTo rd s = some a ∧ ∃ b, secsTo rd ss = some b ∧
        a ++ b = ds := by
      simpa [secsTo, Option.bind_eq_some_iff] using h
    show (do pure ((← secToX rd s) ++ (← secsToX rd ss))) = _
    rw [secToX_of s ha, secsToX_of ss hb]; rfl
end

theorem xsecToX_of {s : XSec} {ds : List (Syntax.Definition M)} (h : xsecTo rd s = some ds) :
    xsecToX rd s = some ds := by
  rcases s with (s | xs)
  · cases s with
    | canons => cases h
    | _ => exact secToX_of _ h
  · exact h

/-- **`toRefX` extends `toRef`.** -/
theorem toRefX_of_toRef {x : XComp} {c : Syntax.Component M} (h : toRef rd x = some c) :
    toRefX rd x = some c := by
  obtain ⟨yss, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  show (x.sections.mapM (xsecToX rd)).map _ = _
  rw [mapM_of (fun _ _ => xsecToX_of) hy]; rfl

theorem xsecToX_sec {s : B.Section} (h1 : ∀ xs, s ≠ .coreTypes xs) (h2 : ∀ c, s ≠ .component c)
    (h3 : ∀ xs, s ≠ .canons xs) : xsecToX rd (.sec s) = xsecTo rd (.sec s) := by
  cases s <;> simp_all [xsecToX, xsecTo, secToX]

/-- **One section of a parsed output**, with core module types. -/
theorem xsecX_eq {s : XSec} {ds : List (Syntax.Definition M)} (h : xsecToX rd s = some ds)
    (r : Layout.RS) : ds.foldl def1 (mapRS r) = mapRS (Layout.sec1 r s) := by
  rcases s with (s | xs)
  · cases s with
    | coreTypes xs =>
      obtain ⟨ys, -, hys⟩ := Option.map_eq_some_iff.1 h
      rw [← hys]; exact foldl_map_untracked _ (fun _ => .inr (.inl rfl)) (fun _ _ => rfl) ys _
    | component c =>
      obtain ⟨ys, -, hys⟩ := Option.map_eq_some_iff.1 h
      rw [← hys]; exact untracked_core (d := .component ys) _ (.inr (.inr (.inl rfl))) rfl
    | canons => cases h
    | custom | coreModule | coreInstances | instances | aliases | types | start | imports
    | exports | values =>
      exact sec_eq ((xsecToX_sec (by simp) (by simp) (by simp)).symm.trans h) r
  · exact xsec_eq (show xsecTo rd (.canons xs) = some ds from h) r

/-- **The spaces of `toRefX x` are the translated spaces.** -/
theorem spacesRef_toRefX {x : XComp} {c : Syntax.Component M} (h : toRefX rd x = some c) :
    spacesRef c = mapRS (Layout.spaces x) := by
  obtain ⟨yss, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 : ({} : RS) = mapRS {} := by simp [mapRS]
  rw [spacesRef, List.foldl_flatten, h0]
  exact foldl_mapM (fun _ _ r hs => xsecX_eq hs r) {} hy

end

end Silmaril.Wasm.JcoTool.LayoutRefX
