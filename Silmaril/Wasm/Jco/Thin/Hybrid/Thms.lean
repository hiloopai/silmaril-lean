module

public import Silmaril.Wasm.Jco.Thin.Hybrid.Defs
public import Silmaril.Wasm.Jco.Thin.Thms

/-!
# Hybrid wrappers: correctness

* `flatten_wrapGlue_hybrid`: in the flat form of a hybrid wrapper, each
  recognized export is the plain `canon lift` of its core export (as in the
  thin wrapper) and every other export is the lift followed by its glue.
* `hybridGlue_all`: when every export is recognized, the hybrid glue is the
  identity glue of the plan; with `recognize_exports`, the thin wrapper is
  the hybrid wrapper of a fully recognized module (`denU_wrapGlue_hybrid_all`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Thin

open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- The flat export of a hybrid wrapper at a world function `ft`. -/
def hybridAt (n w : Nat) (ft : FuncTy) (r : Option Nat) (g : Impl) : Impl :=
  match r with
  | some j => liftAt n w ft j
  | none => glueAt n w ft g

theorem getElem?_hybridGlue (rs : List (Option Nat)) (G : List Impl) (k : Nat) :
    (hybridGlue rs G)[k]? =
      if k < rs.length then
        some (match rs[k]? with
          | some (some j) => Impl.fwd j
          | _ => G[k]?.getD Impl.trap)
      else none := by
  simp only [hybridGlue, List.getElem?_map]
  split
  · next h => rw [List.getElem?_range h]; rfl
  · next h => rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]; rfl

/-- **The flat form of a hybrid wrapper.** Export `k` (with `k < rs.length`) is
`hybridAt` of the recognition `rs[k]` and the glue `G[k]`. -/
theorem flatten_wrapGlue_hybrid (s : Style) (w : World) (m : M) (args : List Impl)
    (rs : List (Option Nat)) (G : List Impl) (hrs : rs.length = w.exports.length) :
    flatten (wrapGlue s w m args (hybridGlue rs G)) =
      ⟨w.imports, [(m, args.map (Impl.subst (σ₀ w.imports.length)))],
        (w.exports.zip (rs.zip ((List.range rs.length).map fun k => G[k]?.getD Impl.trap))).map
          fun x => ⟨x.1.1, x.1.2,
            hybridAt w.imports.length (CoreModule.exports m).length x.1.2 x.2.1 x.2.2⟩⟩ := by
  rw [flatten_wrapGlue]
  congr 1
  apply List.ext_getElem
  · simp [hybridGlue, hrs]
  · intro k h₁ h₂
    simp only [List.length_map, List.length_zip, hybridGlue, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_zip]
    congr 1
    simp only [hybridGlue, List.getElem_map, List.getElem_range, hybridAt]
    have hk : k < rs.length := by omega
    rw [List.getElem?_eq_getElem hk]
    cases rs[k] with
    | some j => exact glueAt_fwd _ _ _ j
    | none => rfl

/-- **Full recognition**: the hybrid glue of a fully recognized list is the
identity glue of the plan. -/
theorem hybridGlue_all (js : List Nat) (G : List Impl) :
    hybridGlue (js.map some) G = Plan.glue ⟨[], js⟩ := by
  apply List.ext_getElem
  · simp [hybridGlue, Plan.glue]
  · intro k h₁ h₂
    simp only [hybridGlue, Plan.glue, List.getElem_map, List.getElem_range, List.length_map]
    simp only [hybridGlue, List.length_map, List.length_range] at h₁
    rw [List.getElem?_map, List.getElem?_eq_getElem h₁]
    rfl

/-- The per-export recognition of a recognized plan is the plan. -/
theorem recognize_exports {s : Style} {w : World} {imps exps : CoreIface} {p : Plan}
    (h : recognize s w imps exps = some p) :
    recognizeExports s w exps = p.exports.map some := by
  have hx := (recognize_eq_some h).2
  obtain ⟨hl, hk⟩ := mapM_some hx
  apply List.ext_getElem
  · simp [recognizeExports, hl]
  · intro k h₁ h₂
    simp only [recognizeExports, List.length_map] at h₁
    obtain ⟨j, hj, hf⟩ := hk k h₁
    simp only [recognizeExports, List.getElem_map]
    rw [hf, List.getElem?_eq_some_iff.mp hj |>.2]

/-- **The thin wrapper is the hybrid wrapper of a recognized module**, for
any fallback glue. -/
theorem denU_wrapGlue_hybrid_all (C : CoreSem M) (s : Style) (w : World) (m : M) (p : Plan)
    (G : List Impl) (h : recognize s w (CoreModule.imports m) (CoreModule.exports m) = some p) :
    (wrapGlue s w m (importWiring w p)
        (hybridGlue (recognizeExports s w (CoreModule.exports m)) G)).denU C =
      (thin w m p).denU C := by
  rw [recognize_exports h, hybridGlue_all]
  exact denU_wrapGlue_glue C s w m ⟨p.imports, p.exports⟩

end Silmaril.Wasm.Jco.Thin
