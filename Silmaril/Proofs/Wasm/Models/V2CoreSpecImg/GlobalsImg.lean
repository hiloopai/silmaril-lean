module

public import Silmaril.Wasm.Models.V2CoreSpec.Defs
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
public import Silmaril.Wasm.V2.ToCore.Modules
public import Silmaril.Wasm.V2.ToCore.Validation

/-!
# Spec preparations of 2.0 images hold only 2.0 globals

* `VImg v`: a Core value is the image of a 2.0 value; `CImg i`: a Core instruction is the image
  of a 2.0 instruction; `GsImg s`: every global of `s` is the image of a 2.0 global (`GImg`).
* `constInstr?_globals`, `evalConst?_globals`: constant evaluation never changes the globals
  (it only allocates structures and arrays).
* `constInstr?_img`, `evalConst?_img`: on a store of image globals, an image instruction (or
  expression) pushes only image values. The GC instructions and the extern/any conversions are
  not images (`Instr.ofCore?` rejects them), so this needs no validity.
* `evalGlobals?_img`: the first (`$evalglobals`) allocation keeps `GsImg`.
* `allocModule?_img`: `$allocmodule` keeps `GsImg` when the values are images.
* **`prepare?_img`**: the spec preparation of a 2.0 module's Core image into a store of image
  globals holds only image globals.
* **`specGlobalsImg_of`**: `SpecGlobalsImg X` for every such `X` (no module validity used).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpecImg

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.V2CoreSpec

variable {H : Type}

/-- A Core value is the image of a 2.0 value. -/
def VImg (v : Val) : Prop := ∃ w : Silmaril.Wasm.V2.Execution.Val,
  Silmaril.Wasm.V2.Execution.Val.toCore w = v

/-- A Core instruction is the image of a 2.0 instruction. -/
def CImg (i : Instr) : Prop := ∃ j : Silmaril.Wasm.V2.Instr, Silmaril.Wasm.V2.Instr.toCore j = some i

/-- Every global of a Core store is the image of a 2.0 global. -/
def GsImg (s : Store H) : Prop := ∀ g ∈ s.globals, GImg g

/-- A Core global type is the image of a 2.0 global type. -/
def TImg (t : CGlobalType) : Prop := ∃ u : Silmaril.Wasm.V2.GlobalType,
  Silmaril.Wasm.V2.Execution.ToCore.globalToC u = t

theorem vimg_num (v : NumVal) : VImg (.num v) := ⟨.num ⟨v.type, v.bits⟩, rfl⟩

theorem vimg_vec (b : BitVec 128) : VImg (.vec b) := ⟨.vec b, rfl⟩

theorem vimg_null : VImg (.ref .null) := ⟨.ref (.null .funcref), rfl⟩

theorem vimg_func (a : Nat) : VImg (.ref (.func a)) := ⟨.ref (.funcAddr a), rfl⟩

theorem gimg_mk {t : CGlobalType} {v : Val} (ht : TImg t) (hv : VImg v) : GImg ⟨t, v⟩ := by
  obtain ⟨u, rfl⟩ := ht
  obtain ⟨w, rfl⟩ := hv
  exact ⟨⟨u, w⟩, rfl⟩

/-! ## Constant evaluation keeps the globals -/

theorem structNew?_globals {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    (h : structNew? s f vs x = some (s', vs')) : s'.globals = s.globals := by
  unfold structNew? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨_, _, _, _, _, _, _, h⟩ := h
  split at h
  · cases h; rfl
  · cases h

theorem arrayNewFixed?_globals {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    {n : Fin (2 ^ 32)} (h : arrayNewFixed? s f vs x n = some (s', vs')) :
    s'.globals = s.globals := by
  unfold arrayNewFixed? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨_, _, _, _, _, _, _, h⟩ := h
  split at h
  · cases h; rfl
  · cases h

theorem intBinOp_globals {s s' : Store H} {f : Frame} {vs vs' : List Val} {t : IntType}
    {op : IntBinOp} (h : constInstr? s f vs (.intBinOp t op) = some (s', vs')) :
    s'.globals = s.globals := by
  simp only [constInstr?] at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := h
    split at h
    · cases h; rfl
    · cases h
  · cases h

theorem anyConvertExtern_globals {s s' : Store H} {f : Frame} {vs vs' : List Val}
    (h : constInstr? s f vs .anyConvertExtern = some (s', vs')) : s'.globals = s.globals := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨_, v, _, h⟩ := h
  split at h <;> first | (cases h; rfl) | cases h

theorem externConvertAny_globals {s s' : Store H} {f : Frame} {vs vs' : List Val}
    (h : constInstr? s f vs .externConvertAny = some (s', vs')) : s'.globals = s.globals := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨_, v, _, h⟩ := h
  split at h
  · split at h <;> (cases h; rfl)
  · cases h

theorem structNewDefault_globals {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    (h : constInstr? s f vs (.structNewDefault x) = some (s', vs')) : s'.globals = s.globals := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  exact structNew?_globals h

theorem arrayNew_globals {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    (h : constInstr? s f vs (.arrayNew x) = some (s', vs')) : s'.globals = s.globals := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  exact arrayNewFixed?_globals h

theorem arrayNewDefault_globals {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    (h : constInstr? s f vs (.arrayNewDefault x) = some (s', vs')) : s'.globals = s.globals := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  exact arrayNewFixed?_globals h

theorem bindKeep_globals {α : Type} {o : Option α} {k : α → Option (Store H × List Val)}
    {s s' : Store H} {vs' : List Val} (hk : ∀ a r, k a = some r → r.1 = s)
    (h : o.bind k = some (s', vs')) : s'.globals = s.globals := by
  obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.mp h
  rw [show s' = s from hk a _ ha]

theorem refI31_globals {s s' : Store H} {f : Frame} {vs vs' : List Val}
    (h : constInstr? s f vs .refI31 = some (s', vs')) : s'.globals = s.globals := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, h⟩ := h
  cases h; rfl

set_option linter.unusedTactic false in
/-- One constant instruction keeps the globals. -/
theorem constInstr?_globals {s s' : Store H} {f : Frame} {vs vs' : List Val} {i : Instr}
    (h : constInstr? s f vs i = some (s', vs')) : s'.globals = s.globals := by
  cases i
  case intBinOp => exact intBinOp_globals h
  case anyConvertExtern => exact anyConvertExtern_globals h
  case externConvertAny => exact externConvertAny_globals h
  case structNew => exact structNew?_globals h
  case structNewDefault => exact structNewDefault_globals h
  case arrayNew => exact arrayNew_globals h
  case arrayNewDefault => exact arrayNewDefault_globals h
  case arrayNewFixed => exact arrayNewFixed?_globals h
  case refFunc => exact bindKeep_globals (fun _ _ ha => by cases ha; rfl) h
  case refI31 => exact refI31_globals h
  case globalGet => exact bindKeep_globals (fun _ _ ha => by cases ha; rfl) h
  all_goals (cases h; try rfl)

/-- A constant expression keeps the globals. -/
theorem constFold_globals {f : Frame} :
    ∀ (e : Expr) {s s' : Store H} {vs vs' : List Val},
      e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (s, vs) =
        some (s', vs') → s'.globals = s.globals
  | [], s, s', vs, vs', h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | i :: e, s, s', vs, vs', h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s₁, vs₁⟩, h₁, h₂⟩ := h
    exact (constFold_globals e h₂).trans (constInstr?_globals h₁)

theorem evalConst?_globals {s s' : Store H} {f : Frame} {e : Expr} {v : Val}
    (h : evalConst? s f e = some (s', v)) : s'.globals = s.globals := by
  unfold evalConst? at h
  split at h
  · rename_i hc
    cases h
    exact constFold_globals e hc
  · cases h

theorem evalExprs?_globals :
    ∀ {s : Store H} {f : Frame} {es : List Expr} {s' : Store H} {f' : Frame} {rs : List Ref},
      evalExprs? evalConst? s f es = some (s', f', rs) → s'.globals = s.globals
  | s, f, [], s', f', rs, h => by
    simp only [evalExprs?, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | s, f, e :: es, s', f', rs, h => by
    simp only [evalExprs?] at h
    split at h
    · rename_i s₁ r h₁
      split at h
      · cases h
      · rename_i s₂ f₂ rs₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, evalExprs?_globals h₂, evalConst?_globals h₁]
    · cases h

theorem evalExprss?_globals :
    ∀ {s : Store H} {f : Frame} {ess : List (List Expr)} {s' : Store H} {f' : Frame}
      {rss : List (List Ref)},
      evalExprss? evalConst? s f ess = some (s', f', rss) → s'.globals = s.globals
  | s, f, [], s', f', rs, h => by
    simp only [evalExprss?, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | s, f, es :: ess, s', f', rs, h => by
    simp only [evalExprss?] at h
    split at h
    · cases h
    · rename_i s₁ f₁ r h₁
      split at h
      · cases h
      · rename_i s₂ f₂ rs₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, evalExprss?_globals h₂, evalExprs?_globals h₁]

/-! ## Constant evaluation of image code pushes image values -/

theorem cimg_not {i : Instr} (hi : CImg i) (h : Silmaril.Wasm.V2.Instr.ofCore? i = none) :
    False := by
  obtain ⟨j, hj⟩ := hi
  rw [Silmaril.Wasm.V2.Instr.ofCore?_toCore hj] at h
  cases h

theorem vimg_snoc {vs : List Val} {w : Val} (hvs : ∀ v ∈ vs, VImg v) (hw : VImg w) :
    ∀ v ∈ vs ++ [w], VImg v := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hvs v hv
  · rw [List.mem_singleton.mp hv]; exact hw

theorem global?_img {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hs : GsImg s) (h : s.global? f x = some (a, g)) : VImg g.value := by
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, g', hg', _, rfl⟩ := h
  obtain ⟨gv, rfl⟩ := hs _ (List.mem_of_getElem? hg')
  exact ⟨gv.value, rfl⟩

theorem refFunc_img {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : FuncIdx}
    (hvs : ∀ v ∈ vs, VImg v) (h : constInstr? s f vs (.refFunc x) = some (s', vs')) :
    ∀ v ∈ vs', VImg v := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  cases h
  exact vimg_snoc hvs (vimg_func _)

theorem globalGet_img {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : GlobalIdx}
    (hs : GsImg s) (hvs : ∀ v ∈ vs, VImg v)
    (h : constInstr? s f vs (.globalGet x) = some (s', vs')) : ∀ v ∈ vs', VImg v := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨_, g, hg, h⟩ := h
  cases h
  exact vimg_snoc hvs (global?_img hs hg)

theorem intBinOp_img {s s' : Store H} {f : Frame} {vs vs' : List Val} {t : IntType}
    {op : IntBinOp} (hvs : ∀ v ∈ vs, VImg v)
    (h : constInstr? s f vs (.intBinOp t op) = some (s', vs')) : ∀ v ∈ vs', VImg v := by
  simp only [constInstr?] at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
    obtain ⟨pre, _, _, hp, _, _, _, _, h⟩ := h
    have hpre : ∀ v ∈ pre, VImg v := fun v hv => hvs v (by rw [pop2?_eq hp]; simp [hv])
    split at h
    · cases h
      exact vimg_snoc hpre (vimg_num _)
    · cases h
  · cases h

/-- One image instruction, on a store of image globals and a stack of image values, pushes only
image values. -/
theorem constInstr?_img {s s' : Store H} {f : Frame} {vs vs' : List Val} {i : Instr}
    (hi : CImg i) (hs : GsImg s) (hvs : ∀ v ∈ vs, VImg v)
    (h : constInstr? s f vs i = some (s', vs')) : ∀ v ∈ vs', VImg v := by
  cases i
  case intConst | floatConst => cases h; exact vimg_snoc hvs (vimg_num _)
  case vecConst => cases h; exact vimg_snoc hvs (vimg_vec _)
  case refNull => cases h; exact vimg_snoc hvs vimg_null
  case refFunc => exact refFunc_img hvs h
  case globalGet => exact globalGet_img hs hvs h
  case intBinOp => exact intBinOp_img hvs h
  case refI31 | anyConvertExtern | externConvertAny | structNew | structNewDefault | arrayNew
      | arrayNewDefault | arrayNewFixed =>
    exact (cimg_not hi (by simp [Silmaril.Wasm.V2.Instr.ofCore?])).elim
  all_goals cases h

theorem constFold_img {f : Frame} :
    ∀ (e : Expr) {s s' : Store H} {vs vs' : List Val}, (∀ i ∈ e, CImg i) → GsImg s →
      (∀ v ∈ vs, VImg v) →
      e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (s, vs) =
        some (s', vs') → ∀ v ∈ vs', VImg v
  | [], s, s', vs, vs', _, _, hvs, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact hvs
  | i :: e, s, s', vs, vs', he, hs, hvs, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s₁, vs₁⟩, h₁, h₂⟩ := h
    have hs₁ : GsImg s₁ := by
      intro g hg
      rw [constInstr?_globals h₁] at hg
      exact hs g hg
    exact constFold_img e (fun j hj => he j (List.mem_cons_of_mem _ hj)) hs₁
      (constInstr?_img (he i List.mem_cons_self) hs hvs h₁) h₂

theorem evalConst?_img {s s' : Store H} {f : Frame} {e : Expr} {v : Val}
    (he : ∀ i ∈ e, CImg i) (hs : GsImg s) (h : evalConst? s f e = some (s', v)) : VImg v := by
  unfold evalConst? at h
  split at h
  · rename_i s₁ v₁ hc
    cases h
    exact constFold_img e he hs (by simp) hc _ List.mem_cons_self
  · cases h

/-! ## The two allocations -/

theorem evalGlobals?_img :
    ∀ {s : Store H} {f : Frame} {gs : List CGlobalType} {es : List Expr} {s' : Store H}
      {f' : Frame} {vs : List Val}, (∀ g ∈ gs, TImg g) → (∀ e ∈ es, ∀ i ∈ e, CImg i) →
      GsImg s → evalGlobals? evalConst? s f gs es = some (s', f', vs) →
      GsImg s' ∧ ∀ v ∈ vs, VImg v
  | s, f, [], [], s', f', vs, _, _, hs, h => by
    simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨hs, by simp⟩
  | s, f, [], _ :: _, s', f', vs, _, _, _, h => by simp [evalGlobals?] at h
  | s, f, _ :: _, [], s', f', vs, _, _, _, h => by simp [evalGlobals?] at h
  | s, f, g :: gs, e :: es, s', f', vs, hg, he, hs, h => by
    simp only [evalGlobals?] at h
    split at h
    · cases h
    · rename_i s₁ v h₁
      split at h
      · cases h
      · rename_i s₂ f₂ vs₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        have hv : VImg v := evalConst?_img (he e List.mem_cons_self) hs h₁
        have hs₁ : GsImg (allocGlobal s₁ g v).1 := by
          intro g' hg'
          simp only [allocGlobal, List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · rw [evalConst?_globals h₁] at hg'
            exact hs g' hg'
          · exact gimg_mk (hg g List.mem_cons_self) hv
        obtain ⟨hs₂, hvs₂⟩ := evalGlobals?_img (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
          (fun e' he' => he e' (List.mem_cons_of_mem _ he')) hs₁ h₂
        refine ⟨hs₂, ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact hvs₂ w hw

theorem allocModule?_img {s s' : Store H} {m : Module} {xas : List ExternAddr} {valsG : List Val}
    {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst}
    (hT : ∀ g ∈ m.globals, TImg ⟨g.type.mutability,
      (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
    (hv : ∀ v ∈ valsG, VImg v) (hs : GsImg s)
    (h : allocModule? s m xas valsG refsT refsE = some (s', mi)) : GsImg s' := by
  obtain ⟨_, _, _, -, -, -, -, rfl⟩ := allocModule?_inv h
  intro g hg
  simp only [List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨p, hp, rfl⟩
  · exact hs g hg
  · have h1 := (List.of_mem_zip hp).1
    have h2 := (List.of_mem_zip hp).2
    obtain ⟨g₀, hg₀, hpe⟩ := List.mem_map.mp h1
    exact gimg_mk (hpe ▸ hT g₀ hg₀) (hv _ h2)

/-! ## The image module -/

theorem mem_of_mapM {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') : ∀ y ∈ l', ∃ x ∈ l, f x = some y := by
  have hf := Silmaril.Wasm.V2.Validation.forall₂_of_mapM h
  clear h
  induction hf with
  | nil => simp
  | cons hab _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨x, hx, hfx⟩ := ih y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem closed_liftVal (t : Silmaril.Wasm.V2.ValType) (tus : List CTypeUse) :
    (liftVal t.toCore).substAll tus = t.toC :=
  Ty.substAll_closed (by cases t <;> first | rfl | (rename_i r; cases r <;> rfl)) _

/-- The globals of a 2.0 module's Core image have image types and image initialisers. -/
theorem image_globals {m : Silmaril.Wasm.V2.Module} {cm : Module}
    (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm) (σ : List CTypeUse) :
    ∀ g ∈ cm.globals, TImg ⟨g.type.mutability, (liftVal g.type.value).substAll σ⟩ ∧
      ∀ i ∈ g.init, CImg i := by
  simp only [Silmaril.Wasm.V2.Module.toCore, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hcm
  obtain ⟨gs, hgs, _, _, _, _, _, _, rfl⟩ := hcm
  intro g hg
  obtain ⟨g₂, -, hg₂⟩ := mem_of_mapM hgs g hg
  simp only [Silmaril.Wasm.V2.Global.toCore, Option.map_eq_some_iff] at hg₂
  obtain ⟨init, hinit, rfl⟩ := hg₂
  refine ⟨⟨g₂.type, ?_⟩, ?_⟩
  · simp only [Silmaril.Wasm.V2.GlobalType.toCore, closed_liftVal]
    rfl
  · intro i hi
    rw [Silmaril.Wasm.V2.Expr.toCore_eq_mapM] at hinit
    obtain ⟨j, -, hj⟩ := mem_of_mapM hinit i hi
    exact ⟨j, hj⟩

set_option linter.unusedTactic false in
/-- The stages of `prepare?` (any store type). -/
theorem prepare?_stages {X : Store H} {cm : Module} {cxas : List ExternAddr} {c : Config H}
    {st : Option FuncIdx} (h : prepare? evalConst? X cm cxas = some (c, st)) :
    ∃ s₁ f₁ valsG s₂ f₂ refsT s₃ f₃ refsE mi,
      evalGlobals? evalConst? X ⟨[], ModuleInst.initial X cm cxas⟩
        (cm.globals.map fun g => ⟨g.type.mutability,
          (liftVal g.type.value).substAll ((allocTypes cm.types).map .dt)⟩)
        (cm.globals.map Global.init) = some (s₁, f₁, valsG) ∧
      evalExprs? evalConst? s₁ f₁ (cm.tables.map Table.init) = some (s₂, f₂, refsT) ∧
      evalExprss? evalConst? s₂ f₂ (cm.elems.map Elem.init) = some (s₃, f₃, refsE) ∧
      allocModule? s₃ cm cxas valsG refsT refsE = some (c.store, mi) := by
  unfold prepare? at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  exact ⟨_, _, _, _, _, _, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›⟩

/-- **The spec preparation of a 2.0 image into a store of image globals holds only image
globals.** -/
theorem prepare?_img {X : Store H} {m : Silmaril.Wasm.V2.Module} {cm : Module}
    {cxas : List ExternAddr} {c : Config H} {st : Option FuncIdx}
    (hX : GsImg X) (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    (h : prepare? evalConst? X cm cxas = some (c, st)) : GsImg c.store := by
  have hI := image_globals hcm
  obtain ⟨s₁, _, valsG, s₂, _, _, s₃, _, _, _, hG, hT, hE, hM⟩ := prepare?_stages h
  have hTy : ∀ t ∈ cm.globals.map (fun g => (⟨g.type.mutability,
      (liftVal g.type.value).substAll ((allocTypes cm.types).map .dt)⟩ : CGlobalType)),
      TImg t := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht
    exact (hI _ g hg).1
  have hIn : ∀ e ∈ cm.globals.map Global.init, ∀ i ∈ e, CImg i := by
    intro e he
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
    exact (hI [] g hg).2
  obtain ⟨hs₁, hv⟩ : GsImg s₁ ∧ ∀ v ∈ valsG, VImg v := evalGlobals?_img hTy hIn hX hG
  have h₃ : s₃.globals = s₁.globals := (evalExprss?_globals hE).trans (evalExprs?_globals hT)
  have hs₃ : GsImg s₃ := fun g hg => hs₁ g (h₃ ▸ hg)
  exact allocModule?_img (fun g hg => (hI _ g hg).1) hv hs₃ hM

/-- **`SpecGlobalsImg` holds on every store of image globals** (no module validity used). -/
theorem specGlobalsImg_of {X : Store H} (hX : GsImg X) : SpecGlobalsImg X := by
  intro m cm cxas c st _ hcm hp
  exact prepare?_img hX hcm hp

/-- The Core image of a 2.0 store holds only image globals. -/
theorem gsImg_toCore {s : Silmaril.Wasm.V2.Execution.Store H} {X : Store H}
    (h : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) : GsImg X := by
  simp only [Silmaril.Wasm.V2.Execution.Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  intro g hg
  obtain ⟨gv, -, rfl⟩ := List.mem_map.mp hg
  exact ⟨gv, rfl⟩

end Silmaril.Proofs.Wasm.Models.V2CoreSpecImg
