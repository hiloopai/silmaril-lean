module

public import Silmaril.Wasm.Jco.Thin.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Thms
import Batteries.Data.List.Lemmas

/-!
# Thin-wrapper recognition: correctness and agreement with the adaptor

* `flatten_thin`, `flatten_wrapGlue`: the flat forms of the thin wrapper and of
  the wrapped component with an arbitrary adaptor glue (the adaptor's glue is
  substituted into the `canon lift` of each export).
* **Agreement** `flatten_wrapGlue_glue`, `denU_wrapGlue_glue`,
  `denT_wrapGlue_glue`: with the identity glue of a plan, the wrapped
  component (adaptor present) and the thin wrapper (no adaptor) have the same
  flat form, hence the same denotation, for every core semantics `C`. The
  adaptor is then behaviourally the identity. No hypothesis on the plan is
  needed: an index out of range traps on both sides.
* Recognition: `recognize_fits` (a recognized plan meets `Plan.Fits`) and
  `recognize_isSome_iff` (recognition succeeds exactly when every core import
  of the module is a world import and every world export is a core export of
  the module, with the flattened types and the names of the style).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Thin

open Silmaril.Wasm.Component
open Silmaril.Games

variable {M : Type} [CoreModule M]

/-! ## Substitution facts -/

/-- The initial substitution of `flatten`. -/
abbrev σ₀ (n : Nat) : List Impl := (List.range n).map Impl.fwd

/-- The substitution after one core instance of `w` functions. -/
abbrev σ₁ (n w : Nat) : List Impl := σ₀ n ++ (List.range w).map fun i => Impl.fwd (n + i)

theorem subst_call (σ : List Impl) (c : List Adapter) (r : Nat) :
    Impl.subst σ ⟨c, .call r⟩ =
      match σ[r]? with
      | some im' => ⟨c ++ im'.chain, im'.target⟩
      | none => ⟨c, .const none⟩ := rfl

theorem σ₁_get (n w j : Nat) :
    (σ₁ n w)[n + j]? = if j < w then some (Impl.fwd (n + j)) else none := by
  simp only [σ₁, σ₀]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left, List.getElem?_map]
  split
  · next h => rw [List.getElem?_range h]; rfl
  · next h => rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]; rfl

/-- The adaptor's imports, substituted: forwarding to the module's exports. -/
theorem σc_eq (n w : Nat) :
    ((List.range w).map fun i =>
        ((((List.range w).map fun i => Impl.fwd (n + i))[i]?).getD Impl.trap).subst (σ₁ n w)) =
      (List.range w).map fun i => Impl.fwd (n + i) := by
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, Impl.fwd]
  rw [subst_call, σ₁_get, ite_eq_left hi]
  rfl

/-- What the `canon lift` of core export `j` (of `w`, starting at `n`) becomes. -/
def liftAt (n w : Nat) (ft : FuncTy) (j : Nat) : Impl :=
  if j < w then ⟨[.lift ft], .call (n + j)⟩ else ⟨[.lift ft], .const none⟩

theorem subst_lift_σ₁ (n w : Nat) (ft : FuncTy) (j : Nat) :
    Impl.subst (σ₁ n w) ⟨[.lift ft], .call (n + j)⟩ = liftAt n w ft j := by
  rw [subst_call, σ₁_get, liftAt]
  by_cases h : j < w
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte]

/-! ## Flat forms -/

/-- The flat exports of a thin wrapper. -/
def flatExports (n w : Nat) (fs : Iface) (js : List Nat) : List Export :=
  (fs.zip js).map fun x => ⟨x.1.1, x.1.2, liftAt n w x.1.2 x.2⟩

/-- **The flat form of the thin wrapper.** -/
theorem flatten_thin (w : World) (m : M) (p : Plan) :
    flatten (thin w m p) =
      ⟨w.imports, [(m, (importWiring w p).map (Impl.subst (σ₀ w.imports.length)))],
        flatExports w.imports.length (CoreModule.exports m).length w.exports p.exports⟩ := by
  simp only [thin, flatten, flattenNodes]
  congr 1
  simp only [thinExports, flatExports, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  rw [subst_lift_σ₁]

/-- Forwarding to the `w` functions starting at `n`. -/
abbrev fwdsFrom (n w : Nat) : List Impl := (List.range w).map fun i => Impl.fwd (n + i)

theorem fwdsFrom_get (n w j : Nat) :
    (fwdsFrom n w)[j]? = if j < w then some (Impl.fwd (n + j)) else none := by
  simp only [fwdsFrom, List.getElem?_map]
  split
  · next h => rw [List.getElem?_range h]; rfl
  · next h => rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]; rfl

/-- What the `canon lift` of adaptor glue `g` becomes, once the adaptor is
inlined: the lift followed by the glue, over the module's exports. -/
def glueAt (n w : Nat) (ft : FuncTy) (g : Impl) : Impl :=
  let g' := g.subst (fwdsFrom n w)
  ⟨.lift ft :: g'.chain, g'.target⟩

/-- The identity glue is the plain `canon lift`. -/
theorem glueAt_fwd (n w : Nat) (ft : FuncTy) (j : Nat) :
    glueAt n w ft (Impl.fwd j) = liftAt n w ft j := by
  simp only [glueAt, Impl.fwd, subst_call, fwdsFrom_get, liftAt]
  by_cases h : j < w
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte]

/-- **The flat form of the wrapped component**, for any adaptor glue `G`:
one instance of the module, and each export is the `canon lift` followed by
its glue. -/
theorem flatten_wrapGlue (s : Style) (w : World) (m : M) (args G : List Impl) :
    flatten (wrapGlue s w m args G) =
      ⟨w.imports, [(m, args.map (Impl.subst (σ₀ w.imports.length)))],
        (w.exports.zip G).map fun x =>
          ⟨x.1.1, x.1.2, glueAt w.imports.length (CoreModule.exports m).length x.1.2 x.2⟩⟩ := by
  simp only [wrapGlue, adaptor, flatten, flattenNodes, List.length_map, List.append_nil]
  rw [σc_eq]
  congr 1
  apply List.ext_getElem
  · simp [thinExports]
  · intro k h₁ h₂
    simp only [List.length_map, List.length_zip, List.length_range, thinExports] at h₁
    simp only [thinExports, List.getElem_map, List.getElem_zip, List.getElem_range]
    congr 1
    have hl : (σ₁ w.imports.length (CoreModule.exports m).length).length =
        w.imports.length + (CoreModule.exports m).length := by simp
    have hz : (((adaptorTys s w).zip G).map fun x =>
        ({ name := x.1.1, ty := CoreFuncTy.asFuncTy x.1.2, impl := x.2 } : Export))[k]? =
        some ⟨s.exportName w.exports[k].1, CoreFuncTy.asFuncTy w.exports[k].2.flat, G[k]⟩ := by
      rw [List.getElem?_eq_getElem (by simp [adaptorTys]; omega)]
      simp [adaptorTys]
    rw [subst_call, List.getElem?_append_right (by simp), hl, Nat.add_sub_cancel_left,
      List.getElem?_map, hz]
    rfl

/-! ## Agreement of the thin wrapper and the wrapped component -/

/-- **Agreement, flat forms**: with the identity glue of a plan, wrapping the
module with the adaptor and the thin wrapper flatten to the same component. -/
theorem flatten_wrapGlue_glue (s : Style) (w : World) (m : M) (p : Plan) :
    flatten (wrapGlue s w m (importWiring w p) p.glue) = flatten (thin w m p) := by
  rw [flatten_wrapGlue, flatten_thin]
  congr 1
  simp only [flatExports, Plan.glue, List.zip_map_right, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, Prod.map, id, glueAt_fwd]

/-- The denotation of the wrapped component, for any glue, is that of its flat
form. -/
theorem denU_wrapGlue (C : CoreSem M) (s : Style) (w : World) (m : M) (args G : List Impl) :
    (wrapGlue s w m args G).denU C =
      Linked.denU C ⟨w.imports, [(m, args.map (Impl.subst (σ₀ w.imports.length)))],
        (w.exports.zip G).map fun x =>
          ⟨x.1.1, x.1.2, glueAt w.imports.length (CoreModule.exports m).length x.1.2 x.2⟩⟩ := by
  rw [← denU_flatten' C, flatten_wrapGlue]

/-- **Agreement of (a) and (b)**: for every core semantics, the component
wrapping the module with the identity adaptor of a plan and the thin wrapper
along the plan have the same strategy. -/
theorem denU_wrapGlue_glue (C : CoreSem M) (s : Style) (w : World) (m : M) (p : Plan) :
    (wrapGlue s w m (importWiring w p) p.glue).denU C = (thin w m p).denU C := by
  rw [← denU_flatten' C, flatten_wrapGlue_glue, denU_flatten']

/-- **Agreement with interface sizes**: the two are acceptable replacements of
each other in every direction (`compDomain`). -/
theorem denT_wrapGlue_glue (C : CoreSem M) (s : Style) (w : World) (m : M) (p : Plan) :
    (wrapGlue s w m (importWiring w p) p.glue).denT C = (thin w m p).denT C := by
  simp only [Comp.denT, denU_wrapGlue_glue]
  simp [wrapGlue, thin, thinExports, Plan.glue]

/-! ## Recognition -/

theorem mapM_some {α β : Type} {f : α → Option β} {l : List α} {r : List β}
    (h : l.mapM f = some r) :
    r.length = l.length ∧ ∀ (k : Nat) (hk : k < l.length), ∃ b, r[k]? = some b ∧ f l[k] = some b := by
  rw [List.mapM_eq_some_iff_forall₂] at h
  induction h with
  | nil => exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | @cons a b l r hab _ ih =>
    refine ⟨by simp [ih.1], ?_⟩
    intro k hk
    cases k with
    | zero => exact ⟨b, rfl, hab⟩
    | succ k =>
      obtain ⟨b', h₁, h₂⟩ := ih.2 k (by simpa using hk)
      exact ⟨b', by simpa using h₁, by simpa using h₂⟩

theorem mapM_isSome {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (l.mapM f).isSome ↔ ∀ a ∈ l, (f a).isSome
  | [] => by simp
  | a :: l => by
    rw [List.mapM_cons]
    cases h : f a with
    | none => simp [h]
    | some b =>
      have ih := mapM_isSome (f := f) (l := l)
      cases h' : l.mapM f with
      | none =>
        have hn := ih.not.mp (by simp [h'])
        simp only [h, Option.bind_eq_bind, Option.bind_some, Option.bind_none,
          Option.isSome_none, Bool.false_eq_true, List.mem_cons, forall_eq_or_imp,
          Option.isSome_some, true_and, false_iff]
        exact hn
      | some r =>
        simp only [h', Option.isSome_some, true_iff] at ih
        simp only [h, Option.bind_eq_bind, Option.bind_some, List.mem_cons, forall_eq_or_imp,
          Option.isSome_some, true_and]
        exact ⟨fun _ => ih, fun _ => rfl⟩

theorem findCore_some {n : String} {ty : CoreFuncTy} :
    ∀ {cs : CoreIface} {j : Nat}, findCore n ty cs = some j → cs[j]? = some (n, ty)
  | [], _, h => by simp [findCore] at h
  | (n', ty') :: cs, j, h => by
    simp only [findCore] at h
    split at h
    · next hc =>
      cases h
      obtain ⟨rfl, rfl⟩ := hc
      rfl
    · cases h' : findCore n ty cs with
      | none => simp [h'] at h
      | some j' =>
        simp only [h', Option.map_some, Option.some.injEq] at h
        subst h
        simpa using findCore_some h'

theorem findCore_isSome {n : String} {ty : CoreFuncTy} :
    ∀ {cs : CoreIface}, (findCore n ty cs).isSome ↔ (n, ty) ∈ cs
  | [] => by simp [findCore]
  | (n', ty') :: cs => by
    simp only [findCore]
    split
    · next hc => obtain ⟨rfl, rfl⟩ := hc; simp
    · next hc =>
      rw [Option.isSome_map, findCore_isSome, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · cases h; exact absurd ⟨rfl, rfl⟩ hc
        · exact h

theorem findWorld_some {name : String → String} {n : String} {ty : CoreFuncTy} :
    ∀ {fs : Iface} {i : Nat}, findWorld name n ty fs = some i →
      ∃ f, fs[i]? = some f ∧ name f.1 = n ∧ f.2.flat = ty
  | [], _, h => by simp [findWorld] at h
  | (n', ft) :: fs, i, h => by
    simp only [findWorld] at h
    split at h
    · next hc =>
      cases h
      exact ⟨(n', ft), rfl, hc⟩
    · cases h' : findWorld name n ty fs with
      | none => simp [h'] at h
      | some i' =>
        simp only [h', Option.map_some, Option.some.injEq] at h
        subst h
        simpa using findWorld_some h'

theorem findWorld_isSome {name : String → String} {n : String} {ty : CoreFuncTy} :
    ∀ {fs : Iface}, (findWorld name n ty fs).isSome ↔ ∃ f ∈ fs, name f.1 = n ∧ f.2.flat = ty
  | [] => by simp [findWorld]
  | (n', ft) :: fs => by
    simp only [findWorld]
    split
    · next hc => simp only [Option.isSome_some, true_iff]; exact ⟨_, List.mem_cons_self, hc⟩
    · next hc =>
      rw [Option.isSome_map, findWorld_isSome]
      constructor
      · rintro ⟨f, hf, h⟩; exact ⟨f, List.mem_cons_of_mem _ hf, h⟩
      · rintro ⟨f, hf, h⟩
        rcases List.mem_cons.mp hf with rfl | hf
        · exact absurd h hc
        · exact ⟨f, hf, h⟩

theorem recognize_eq_some {s : Style} {w : World} {imps exps : CoreIface} {p : Plan}
    (h : recognize s w imps exps = some p) :
    (imps.mapM fun c => findWorld s.importName c.1 c.2 w.imports) = some p.imports ∧
      (w.exports.mapM fun f => findCore (s.exportName f.1) f.2.flat exps) = some p.exports := by
  simp only [recognize] at h
  cases h₁ : imps.mapM fun c => findWorld s.importName c.1 c.2 w.imports with
  | none => simp [h₁] at h
  | some is =>
    cases h₂ : w.exports.mapM fun f => findCore (s.exportName f.1) f.2.flat exps with
    | none => simp [h₁, h₂] at h
    | some xs =>
      simp only [h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

/-- **Soundness of recognition**: a recognized plan fits. -/
theorem recognize_fits {s : Style} {w : World} {imps exps : CoreIface} {p : Plan}
    (h : recognize s w imps exps = some p) : p.Fits s w imps exps := by
  obtain ⟨hi, hx⟩ := recognize_eq_some h
  obtain ⟨hil, hik⟩ := mapM_some hi
  obtain ⟨hxl, hxk⟩ := mapM_some hx
  refine ⟨hil, hxl, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, h₁, h₂⟩ := hik k hk
    obtain ⟨f, hf, hn, ht⟩ := findWorld_some h₂
    exact ⟨i, f, h₁, hf, hn, ht⟩
  · intro k hk
    obtain ⟨j, h₁, h₂⟩ := hxk k hk
    exact ⟨j, _, h₁, findCore_some h₂, rfl, rfl⟩

/-- **When recognition succeeds**: exactly when every core import of the
module is a world import and every world export is a core export of the
module, with the flattened types and the names of the style. -/
theorem recognize_isSome_iff (s : Style) (w : World) (imps exps : CoreIface) :
    (recognize s w imps exps).isSome ↔
      (∀ c ∈ imps, ∃ f ∈ w.imports, s.importName f.1 = c.1 ∧ f.2.flat = c.2) ∧
        ∀ f ∈ w.exports, (s.exportName f.1, f.2.flat) ∈ exps := by
  have e : (recognize s w imps exps).isSome ↔
      (imps.mapM fun c => findWorld s.importName c.1 c.2 w.imports).isSome ∧
        (w.exports.mapM fun f => findCore (s.exportName f.1) f.2.flat exps).isSome := by
    simp only [recognize]
    cases imps.mapM fun c => findWorld s.importName c.1 c.2 w.imports <;>
      cases w.exports.mapM fun f => findCore (s.exportName f.1) f.2.flat exps <;> simp
  rw [e, mapM_isSome, mapM_isSome]
  simp only [findWorld_isSome, findCore_isSome]

/-! ## A fitting thin wrapper is already flat -/

theorem Plan.Fits.imports_lt {s : Style} {w : World} {imps exps : CoreIface} {p : Plan}
    (h : p.Fits s w imps exps) : ∀ i ∈ p.imports, i < w.imports.length := by
  intro i hi
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hi
  obtain ⟨i', f, h₁, h₂, -⟩ := h.imports_ok k (h.imports_length ▸ hk)
  rw [List.getElem?_eq_getElem hk, hki, Option.some.injEq] at h₁
  subst h₁
  exact (List.getElem?_eq_some_iff.mp h₂).1

theorem Plan.Fits.exports_lt {s : Style} {w : World} {imps exps : CoreIface} {p : Plan}
    (h : p.Fits s w imps exps) : ∀ j ∈ p.exports, j < exps.length := by
  intro j hj
  obtain ⟨k, hk, hkj⟩ := List.mem_iff_getElem.mp hj
  obtain ⟨j', c, h₁, h₂, -⟩ := h.exports_ok k (h.exports_length ▸ hk)
  rw [List.getElem?_eq_getElem hk, hkj, Option.some.injEq] at h₁
  subst h₁
  exact (List.getElem?_eq_some_iff.mp h₂).1

theorem subst_σ₀_lower (n : Nat) (ft : FuncTy) {i : Nat} (hi : i < n) :
    Impl.subst (σ₀ n) ⟨[.lower ft], .call i⟩ = ⟨[.lower ft], .call i⟩ := by
  rw [subst_call, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- **A fitting thin wrapper is a fixed point of flattening**: its flat form
is itself (as a flat component). -/
theorem flatten_thin_of_fits (s : Style) (w : World) (m : M) (p : Plan)
    (h : p.Fits s w (CoreModule.imports m) (CoreModule.exports m)) :
    flatten (thin w m p) =
      ⟨w.imports, [(m, importWiring w p)],
        thinExports w.imports.length w.exports p.exports⟩ := by
  rw [flatten_thin]
  congr 1
  · congr 2
    simp only [importWiring, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact subst_σ₀_lower _ _ (h.imports_lt i hi)
  · simp only [flatExports, thinExports]
    apply List.map_congr_left
    intro x hx
    have hj := h.exports_lt x.2 (List.of_mem_zip hx).2
    simp only [liftAt, hj, ↓reduceIte]

/-- The same, as components. -/
theorem toComponent_flatten_thin_of_fits (s : Style) (w : World) (m : M) (p : Plan)
    (h : p.Fits s w (CoreModule.imports m) (CoreModule.exports m)) :
    (flatten (thin w m p)).toComponent = thin w m p := by
  rw [flatten_thin_of_fits s w m p h]
  rfl

end Silmaril.Wasm.Jco.Thin
