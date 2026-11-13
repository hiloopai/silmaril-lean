module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflSections

/-!
# Reflecting globals, tables, element and data segments, functions and exports

The per-item reflection lemmas of `Module_ok`. Constant expressions go through `const_refl`
under `RelK`; function bodies through `instrs_refl` under `Rel`, in the function-entry context
(`Rel.funcBody`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC liftResult)
open Silmaril.Wasm.Validation (TypeCtx TyOk)

/-- The image of an element of a `mapM` source. -/
theorem mapM_mem_of {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ a ∈ l, ∃ b, f a = some b ∧ b ∈ l'
  | [], _, _, a, ha => by simp at ha
  | x :: l, l', h, a, ha => by
    obtain ⟨b, hb, l'', hl'', rfl⟩ : ∃ b, f x = some b ∧ ∃ l'', l.mapM f = some l'' ∧
        b :: l'' = l' := by
      simpa [List.mapM_cons, Option.bind_eq_some_iff] using h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, hb, by simp⟩
    · obtain ⟨c, hc, hmem⟩ := mapM_mem_of hl'' a ha
      exact ⟨c, hc, List.mem_cons_of_mem _ hmem⟩

/-- Core subtyping between image reference types is equality (in any image type context). -/
theorem refToC_sub' {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {r r' : Silmaril.Wasm.V2.RefType}
    (h : Silmaril.Wasm.Validation.Sub Δ r.toC r'.toC) : r = r' :=
  Silmaril.Wasm.V2.ValType.ref.inj (toC_sub_toC hΔ hr (t := .ref r) (u := .ref r') (.refv h))

/-! ## Globals -/

/-- The Core type of a global of the image is the image of its 2.0 type. -/
theorem global_type {D : KCtx} {g : Silmaril.Wasm.V2.Global} {cg : Silmaril.Wasm.Global}
    {gt : Silmaril.Wasm.Validation.CGlobalType} (hcg : Silmaril.Wasm.V2.Global.toCore g = some cg)
    (h : Silmaril.Wasm.Validation.GlobalOk D cg gt) : gt = globalToC g.type := by
  obtain ⟨init, -, rfl⟩ := Option.map_eq_some_iff.mp hcg
  rw [h.1]
  exact Silmaril.Wasm.V2.Validation.closeGlobalType_toCore D g.type

/-- A global of the image reflects. -/
theorem global_one {Cp : VCtx} {D : KCtx} (hK : RelK Cp D) {g : Silmaril.Wasm.V2.Global}
    {cg : Silmaril.Wasm.Global} {gt : Silmaril.Wasm.Validation.CGlobalType}
    (hcg : Silmaril.Wasm.V2.Global.toCore g = some cg) (h : Silmaril.Wasm.Validation.GlobalOk D cg gt)
    (hs : Silmaril.Wasm.Models.simpleConst cg.init = true)
    (hb : ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ g.init → x.toNat < Cp.globals.length) :
    Silmaril.Wasm.V2.Validation.GlobalOk Cp g g.type := by
  have hgt : gt = globalToC g.type := global_type hcg h
  obtain ⟨init, hinit, rfl⟩ := Option.map_eq_some_iff.mp hcg
  have hk : Silmaril.Wasm.Validation.ExprOkConst D init
      (Silmaril.Wasm.V2.ValType.toC g.type.value) := by
    subst hgt
    exact h.2.2
  exact ⟨rfl, trivial, const_refl hK hinit hs hk hb⟩

/-- **Core's sequential `Globals_ok` on the image reflects.** -/
theorem globals_refl {Cp : VCtx} {D : KCtx} (hK : RelK Cp D) {gs : List Silmaril.Wasm.V2.Global}
    {cgs : List Silmaril.Wasm.Global} {gts : List Silmaril.Wasm.Validation.CGlobalType}
    (hm : gs.mapM Silmaril.Wasm.V2.Global.toCore = some cgs)
    (h : Silmaril.Wasm.Validation.GlobalsOk D cgs gts)
    (hs : ∀ g ∈ gs, ∀ cg, Silmaril.Wasm.V2.Global.toCore g = some cg →
      Silmaril.Wasm.Models.simpleConst cg.init = true)
    (hb : ∀ g ∈ gs, ∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ g.init → x.toNat < Cp.globals.length) :
    gts = gs.map (fun g => globalToC g.type) ∧
      ∀ g ∈ gs, Silmaril.Wasm.V2.Validation.GlobalOk Cp g g.type := by
  have each : List.Forall₂ (fun cg gt => ∃ G, D.globals <+: G ∧
      (∀ g ∈ G, g ∈ D.globals ∨ g ∈ gts) ∧
      Silmaril.Wasm.Validation.GlobalOk { D with globals := G } cg gt) cgs gts :=
    globalsOk_each h
  have htys : gts = gs.map (fun g => globalToC g.type) :=
    (forall₂_mapM_eq (P := fun _ => True)
      (fun _ _ _ hcg hr => let ⟨_, _, _, hok⟩ := hr; ⟨global_type hcg hok, trivial⟩) hm each).1
  have hty : ∀ g ∈ D.globals ++ gts, TyOk D.toTypeCtx g.type := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hK.wf.globals g hg
    · have hg' : g ∈ gs.map (fun g => globalToC g.type) := htys ▸ hg
      obtain ⟨g', -, e⟩ := List.mem_map.mp hg'
      exact e ▸ Silmaril.Wasm.V2.Validation.tyOk_toC _ _
  have hall : ∀ g ∈ gs, ((∀ cg, Silmaril.Wasm.V2.Global.toCore g = some cg →
      Silmaril.Wasm.Models.simpleConst cg.init = true) →
      (∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ g.init → x.toNat < Cp.globals.length) →
      Silmaril.Wasm.V2.Validation.GlobalOk Cp g g.type) := (forall₂_mapM_eq (g := fun g => globalToC g.type)
    (P := fun g => (∀ cg, Silmaril.Wasm.V2.Global.toCore g = some cg →
      Silmaril.Wasm.Models.simpleConst cg.init = true) →
      (∀ x, Silmaril.Wasm.V2.Instr.globalGet x ∈ g.init → x.toNat < Cp.globals.length) →
      Silmaril.Wasm.V2.Validation.GlobalOk Cp g g.type) (fun g cg gt hcg hr => by
        obtain ⟨G, hpre, hmem, hok⟩ := hr
        have hK' : RelK Cp { D with globals := G } :=
          { hK with
            globals := hK.globals.trans hpre
            wf := wf_globals hK.wf fun g' hg' => hty g' (List.mem_append.mpr (hmem g' hg')) }
        exact ⟨global_type hcg hok, fun hs' hb' => global_one hK' hcg hok (hs' cg hcg) hb'⟩)
    hm each).2
  exact ⟨htys, fun g hg => hall g hg (hs g hg) (hb g hg)⟩

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
