module

public import Silmaril.Wasm.Jco.Thin.Thms

/-!
# Thin-wrapper recognition: relating FFI naming styles

Recognition depends on core names only through the style. Renaming the core
imports of a module by an injective `fi` and its core exports by an injective
`fe`, and post-composing the style with the same renamings, gives the same
plan (`recognize_rename`). In particular a module in `cm32p2` naming is
recognized by `Style.cm32p2` exactly when its plain-named twin is recognized
by `Style.plain`, with the same plan (`recognize_cm32p2_plain`), so the two
thin wrappers differ only in the core module they instantiate.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Thin

open Silmaril.Wasm.Component

/-- Rename the functions of a core interface. -/
def renameCore (f : String → String) (cs : CoreIface) : CoreIface :=
  cs.map fun c => (f c.1, c.2)

/-- Post-compose a style with renamings of core import and export names. -/
def Style.post (s : Style) (fi fe : String → String) : Style :=
  ⟨fi ∘ s.importName, fe ∘ s.exportName⟩

theorem findCore_rename {f : String → String} (hf : Function.Injective f) (n : String)
    (ty : CoreFuncTy) : ∀ cs : CoreIface, findCore (f n) ty (renameCore f cs) = findCore n ty cs
  | [] => rfl
  | (n', ty') :: cs => by
    simp only [renameCore, List.map_cons, findCore] at *
    have e : (f n' = f n ∧ ty' = ty) ↔ (n' = n ∧ ty' = ty) :=
      and_congr_left fun _ => hf.eq_iff
    simp only [e]
    rw [← findCore_rename hf n ty cs]
    rfl

theorem findWorld_post {f : String → String} (hf : Function.Injective f)
    (name : String → String) (n : String) (ty : CoreFuncTy) :
    ∀ fs : Iface, findWorld (f ∘ name) (f n) ty fs = findWorld name n ty fs
  | [] => rfl
  | (n', ft) :: fs => by
    simp only [findWorld, Function.comp_apply]
    have e : (f (name n') = f n ∧ ft.flat = ty) ↔ (name n' = n ∧ ft.flat = ty) :=
      and_congr_left fun _ => hf.eq_iff
    simp only [e, findWorld_post hf name n ty fs]

/-- **Renaming invariance of recognition.** -/
theorem recognize_rename {fi fe : String → String} (hi : Function.Injective fi)
    (he : Function.Injective fe) (s : Style) (w : World) (imps exps : CoreIface) :
    recognize (s.post fi fe) w (renameCore fi imps) (renameCore fe exps) =
      recognize s w imps exps := by
  simp only [recognize, renameCore, List.mapM_map, Style.post]
  have h₁ : ((fun c : String × CoreFuncTy => findWorld (fi ∘ s.importName) c.1 c.2 w.imports) ∘
      fun c : String × CoreFuncTy => (fi c.1, c.2)) = fun c => findWorld s.importName c.1 c.2 w.imports := by
    funext c
    exact findWorld_post hi s.importName c.1 c.2 w.imports
  have h₂ : (fun f : String × FuncTy =>
      findCore ((fe ∘ s.exportName) f.1) f.2.flat (exps.map fun c => (fe c.1, c.2))) =
      fun f => findCore (s.exportName f.1) f.2.flat exps := by
    funext f
    exact findCore_rename he (s.exportName f.1) f.2.flat exps
  rw [h₁, h₂]

theorem prefix_injective (p : String) : Function.Injective (p ++ ·) := by
  intro a b h
  exact (String.append_right_inj p).mp h

theorem cm32p2_eq_post :
    Style.cm32p2 = Style.plain.post ("cm32p2|" ++ ·) ("cm32p2||" ++ ·) := rfl

/-- **`cm32p2` naming against plain naming**: the mangled twin of a module is
recognized in the `cm32p2` style with the plan of the module in the plain
style. -/
theorem recognize_cm32p2_plain (w : World) (imps exps : CoreIface) :
    recognize .cm32p2 w (renameCore ("cm32p2|" ++ ·) imps) (renameCore ("cm32p2||" ++ ·) exps) =
      recognize .plain w imps exps := by
  rw [cm32p2_eq_post]
  exact recognize_rename (prefix_injective _) (prefix_injective _) _ w imps exps

end Silmaril.Wasm.Jco.Thin
