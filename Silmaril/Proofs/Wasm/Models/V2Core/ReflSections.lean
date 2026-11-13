module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflConst
public import Silmaril.Proofs.Wasm.Models.V2Core.Module

/-!
# Reflecting the sections of a module

Per-section reflection lemmas for `Module_ok` on the image of a 2.0 module: the type section,
imports, globals (Core's sequential `Globals_ok`), tables, memories, element and data
segments, functions, the start function and exports. Each says that the Core premise on the
image gives the 2.0 premise, and that the Core types it assigns are the images of 2.0 types.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC liftResult)
open Silmaril.Wasm.Validation (TypeCtx TyOk)

/-! ## Lists -/

/-- A `Forall₂` on a mapped list whose right side is a function of the left. -/
theorem forall₂_map_eq {α β γ : Type} {f : α → β} {g : α → γ} {R : β → γ → Prop} {P : α → Prop}
    (hR : ∀ a c, R (f a) c → c = g a ∧ P a) :
    ∀ {l : List α} {l' : List γ}, List.Forall₂ R (l.map f) l' → l' = l.map g ∧ ∀ a ∈ l, P a
  | [], _, .nil => ⟨rfl, by simp⟩
  | a :: l, _, .cons h hs => by
    obtain ⟨rfl, hp⟩ := hR a _ h
    obtain ⟨rfl, hps⟩ := forall₂_map_eq hR hs
    exact ⟨rfl, fun b hb => (List.mem_cons.mp hb).elim (fun e => e ▸ hp) (hps b)⟩

/-- `forall₂_map_eq` along a `mapM`. -/
theorem forall₂_mapM_eq {α β γ : Type} {f : α → Option β} {g : α → γ} {R : β → γ → Prop}
    {P : α → Prop} (hR : ∀ a b c, f a = some b → R b c → c = g a ∧ P a) :
    ∀ {l : List α} {lb : List β} {l' : List γ}, l.mapM f = some lb → List.Forall₂ R lb l' →
      l' = l.map g ∧ ∀ a ∈ l, P a := by
  intro l lb l' hm h
  obtain ⟨l'', h'', rfl⟩ := forall₂_mapM_lift (S := fun a d => d = a ∧ P a) (g := g)
    (fun a b c hb hr => let ⟨e, hp⟩ := hR a b c hb hr; ⟨a, ⟨rfl, hp⟩, e⟩) hm h
  have e : l'' = l := by
    clear hm h
    induction h'' with
    | nil => rfl
    | cons hab _ ih => rw [hab.1, ih]
  subst e
  exact ⟨rfl, fun a ha => (forall₂_left h'' a ha).elim fun _ hd => hd.1 ▸ hd.2⟩

/-- A relation that holds of each element and a function of it. -/
theorem forall₂_map_self {α β : Type} {R : α → β → Prop} {f : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, R a (f a)) → List.Forall₂ R l (l.map f)
  | [], _ => .nil
  | _ :: _, h => .cons (h _ (by simp)) (forall₂_map_self fun a ha => h a (by simp [ha]))

/-- Two lists of units of the same length are equal. -/
theorem units_eq {α β : Type} {l : List α} {l' : List β} (h : l.length = l'.length) :
    l.map (fun _ => ()) = l'.map (fun _ => ()) := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons a l ih => cases l' <;> simp_all

/-! ## Types and imports -/

theorem types_refl {ts : List Silmaril.Wasm.V2.FuncType} {dts : List Silmaril.Wasm.Validation.DefType}
    (h : Silmaril.Wasm.Validation.TypesOk {} (ts.map Silmaril.Wasm.V2.FuncType.toCoreRec) dts) :
    dts = ts.map Silmaril.Wasm.V2.FuncType.toDefType :=
  Silmaril.Wasm.Validation.TypesOk.det h (Silmaril.Wasm.V2.Validation.typesOk_map ts {})

theorem imports_refl {types : List Silmaril.Wasm.V2.FuncType} {is : List Silmaril.Wasm.V2.Import}
    {xtI : List Silmaril.Wasm.Validation.CExternType}
    (h : List.Forall₂ (Silmaril.Wasm.Validation.ImportOk
      { types := types.map Silmaril.Wasm.V2.FuncType.toDefType })
      (is.map Silmaril.Wasm.V2.Import.toCore) xtI) :
    ∃ ixt, List.Forall₂ (Silmaril.Wasm.V2.Validation.ImportOk { types := types }) is ixt ∧
      xtI = ixt.map Silmaril.Wasm.V2.ExternType.toCore :=
  forall₂_lift (fun _ _ h => import_refl h) h

/-- Is an import a global? (the filter of `ConstReadsImports`) -/
def isGlobalImport (i : Silmaril.Wasm.V2.Import) : Bool :=
  match i.desc with | .global _ => true | _ => false

/-- The imported globals are counted by the import types. -/
theorem globals_count {C : VCtx} :
    ∀ {is : List Silmaril.Wasm.V2.Import} {ixt : List Silmaril.Wasm.V2.ExternType},
      List.Forall₂ (Silmaril.Wasm.V2.Validation.ImportOk C) is ixt →
        (Silmaril.Wasm.V2.ExternType.globals ixt).length = (is.filter isGlobalImport).length
  | _, _, .nil => rfl
  | i :: _, _, .cons hok hrest => by
    have ih := globals_count hrest
    rcases i with ⟨_, _, d⟩
    cases d <;> (obtain ⟨hty, -⟩ := hok; simp [Silmaril.Wasm.V2.Module.importType?] at hty) <;>
      (obtain ⟨_, -, rfl⟩ := hty
       simpa [Silmaril.Wasm.V2.ExternType.globals, isGlobalImport, List.filter_cons] using ih)

/-! ## Globals -/

/-- Every premise of Core's sequential `Globals_ok`, each in a context whose globals extend the
outer ones by earlier entries. -/
theorem globalsOk_each : ∀ {D : KCtx} {cgs : List Silmaril.Wasm.Global}
    {gts : List Silmaril.Wasm.Validation.CGlobalType},
    Silmaril.Wasm.Validation.GlobalsOk D cgs gts →
      List.Forall₂ (fun cg gt => ∃ G, D.globals <+: G ∧ (∀ g ∈ G, g ∈ D.globals ∨ g ∈ gts) ∧
        Silmaril.Wasm.Validation.GlobalOk { D with globals := G } cg gt) cgs gts
  | _, _, _, .nil => .nil
  | D, _, _, .cons (gt := gt) (gts := gts) h hs => by
    have ih := globalsOk_each hs
    refine .cons ⟨D.globals, List.prefix_refl _, fun g hg => .inl hg, h⟩ (ih.imp ?_)
    rintro cg gt' ⟨G, hG, hmem, hok⟩
    refine ⟨G, (List.prefix_append _ _).trans hG, fun g hg => ?_, hok⟩
    rcases hmem g hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact .inl hg
      · exact .inr (by simp_all)
    · exact .inr (List.mem_cons_of_mem _ hg)

/-- A Core context with more globals, all of image types, is well formed. -/
theorem wf_globals {D : KCtx} (hwf : D.Wf) {G : List Silmaril.Wasm.Validation.CGlobalType}
    (hG : ∀ g ∈ G, TyOk D.toTypeCtx g.type) : ({ D with globals := G } : KCtx).Wf :=
  { hwf with globals := hG }

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
