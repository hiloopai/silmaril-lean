module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Runtime
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Lime1 → Core step simulation: evaluation contexts

Congruence infrastructure for `Step.toCore` (`Lime1/ToCore/Execution.lean`):
decomposition of `Sim` along the Lime1 evaluation contexts (instruction
sequences, labels, frames), lifting of Core `TransGen` runs through the Core
context rules, and the store/frame invariants of Lime1 steps needed to
re-establish `Sim` on the outer configuration (function store only grows with the
same types; the frame's module is unchanged).
-/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution.Runtime

variable {H : Type}

/-! ## Store extension -/

theorem storeExt_refl (s : Store H) : StoreExt s s := ListExt.refl _ _

theorem StoreExt.lt {s s' : Store H} (hext : StoreExt s s') {i : Nat}
    (hi : i < s.funcs.length) : i < s'.funcs.length := ListExt.lt hext hi

theorem StoreExt.funcDefType {s s' : Store H} (hext : StoreExt s s') {a : FuncAddr}
    (ha : a.value < s.funcs.length) : s'.funcDefType a = s.funcDefType a := by
  simp only [Silmaril.Wasm.Execution.Runtime.Store.funcDefType,
    ListExt.map_getElem? hext (g := V1.FuncType.toDefType) ha]

theorem ModWF.mono {s s' : Store H} {m : ModuleInst} (h : ModWF s m) (hext : StoreExt s s') :
    ModWF s' m := fun a ha => StoreExt.lt hext (h a ha)

/-! ## Well-formedness lemmas -/

@[simp] theorem listWF_nil (s : Store H) : Admin.listWF s [] = True := by simp [Admin.listWF]

@[simp] theorem listWF_cons (s : Store H) (a : Admin) (as : List Admin) :
    Admin.listWF s (a :: as) = (Admin.WF s a ∧ Admin.listWF s as) := by simp [Admin.listWF]

@[simp] theorem WF_source (s : Store H) (i : Instr) : Admin.WF s (.source i) = True := by
  simp [Admin.WF]

@[simp] theorem WF_invoke (s : Store H) (a : FuncAddr) :
    Admin.WF s (.invoke a) = (a.value < s.funcs.length) := by simp [Admin.WF]

@[simp] theorem WF_label (s : Store H) (n : Nat) (k : Expr) (b : List Admin) :
    Admin.WF s (.label n k b) = Admin.listWF s b := by simp [Admin.WF]

@[simp] theorem WF_frame (s : Store H) (n : Nat) (f : Frame) (b : List Admin) :
    Admin.WF s (.frame n f b) = (ModWF s f.module ∧ Admin.listWF s b) := by simp [Admin.WF]

@[simp] theorem WF_trap (s : Store H) : Admin.WF s .trap = True := by simp [Admin.WF]

theorem listWF_append (s : Store H) (xs ys : List Admin) :
    Admin.listWF s (xs ++ ys) ↔ Admin.listWF s xs ∧ Admin.listWF s ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, and_assoc]

theorem WF_value (s : Store H) (v : Value) : Admin.WF s (value v) := by
  rcases v with ⟨⟨_ | _⟩, _⟩ <;> simp [value]

theorem listWF_values (s : Store H) (vs : List Value) : Admin.listWF s (values vs) := by
  induction vs with
  | nil => simp [values]
  | cons v vs ih => exact (listWF_cons s _ _).mpr ⟨WF_value s v, ih⟩

mutual
theorem WF_mono {s s' : Store H} (hext : StoreExt s s') :
    (a : Admin) → Admin.WF s a → Admin.WF s' a
  | .source _, _ => by simp
  | .invoke a, h => by simp only [WF_invoke] at h ⊢; exact StoreExt.lt hext h
  | .label _ _ b, h => by simp only [WF_label] at h ⊢; exact listWF_mono hext b h
  | .frame _ f b, h => by
    simp only [WF_frame] at h ⊢; exact ⟨ModWF.mono h.1 hext, listWF_mono hext b h.2⟩
  | .trap, _ => by simp

theorem listWF_mono {s s' : Store H} (hext : StoreExt s s') :
    (l : List Admin) → Admin.listWF s l → Admin.listWF s' l
  | [], _ => by simp
  | a :: as, h => by
    simp only [listWF_cons] at h ⊢; exact ⟨WF_mono hext a h.1, listWF_mono hext as h.2⟩
end

mutual
theorem toCore_congr {s s' : Store H} (hext : StoreExt s s') :
    (a : Admin) → Admin.WF s a → Admin.toCore s' a = Admin.toCore s a
  | .source _, _ => by simp
  | .invoke a, h => by simp only [WF_invoke] at h; simp [StoreExt.funcDefType hext h]
  | .label _ _ b, h => by simp only [WF_label] at h; simp [listToCore_congr hext b h]
  | .frame _ _ b, h => by simp only [WF_frame] at h; simp [listToCore_congr hext b h.2]
  | .trap, _ => by simp

theorem listToCore_congr {s s' : Store H} (hext : StoreExt s s') :
    (l : List Admin) → Admin.listWF s l → Admin.listToCore s' l = Admin.listToCore s l
  | [], _ => by simp
  | a :: as, h => by
    simp only [listWF_cons] at h
    simp only [listToCore_cons]
    rw [toCore_congr hext a h.1, listToCore_congr hext as h.2]
end

/-! ## Invariants of Lime1 steps -/

/-- Lime1 steps extend the function store (host calls by `HostPreserves`). -/
theorem storeExt {src : HostSemantics H} (hp : HostPreserves src) {a b : Config H}
    (h : Step src a b) (hwf : StoreWF a.store) : StoreExt a.store b.store := by
  induction h with
  | context _ _ _ ih => exact ih hwf
  | label _ _ _ ih => exact ih hwf
  | frame _ _ _ ih => exact ih hwf
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact (hp _ _ _ _ _ behavior hwf).2
  | _ => exact fun _ fi h => ⟨fi, h, rfl⟩

/-- Lime1 steps do not change the module of the current frame. -/
theorem module_eq {src : HostSemantics H} {a b : Config H} (h : Step src a b) :
    b.frame.module = a.frame.module := by
  induction h with
  | context _ _ _ ih => exact ih
  | label _ _ _ ih => exact ih
  | _ => rfl

/-! ## Frames and module types -/

theorem types_of_erase {g : ToCore.CFrame} {fl : Frame}
    (h : ToCore.Frame.erase g = fl.toCore) :
    g.module.types = fl.module.types.map V1.FuncType.toDefType := by
  have := congrArg (fun x : ToCore.CFrame => x.module.types) h
  simpa [ToCore.Frame.erase, ToCore.ModuleInst.erase,
    Silmaril.Wasm.Execution.Runtime.Frame.toCore,
    Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this

/-! ## Lifting Core runs through contexts -/

section Lift

open Silmaril.Wasm.Execution.Core (vals)

variable {P : Silmaril.Wasm.Numerics.Profile} {host : ToCore.CHostSemantics H}

theorem transGen_ctxtInstrs {s s' : ToCore.CStore H} {f f' : ToCore.CFrame}
    {vs : List ToCore.CVal} {is is' rest : List ToCore.CAdmin}
    (h : Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P host) ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P host) ⟨s, f, vals vs ++ is ++ rest⟩
      ⟨s', f', vals vs ++ is' ++ rest⟩ :=
  Relation.TransGen.lift
    (fun c : ToCore.CConfig H => (⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩ : ToCore.CConfig H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩
      rcases b with ⟨sb, fb, ib⟩
      by_cases hne : vs ≠ [] ∨ rest ≠ []
      · exact Silmaril.Wasm.Execution.Core.Step.ctxtInstrs hs hne
      · simp only [ne_eq, not_or, not_not] at hne
        obtain ⟨rfl, rfl⟩ := hne
        simpa [vals] using hs) _ _ h

theorem transGen_label {s s' : ToCore.CStore H} {f f' : ToCore.CFrame} {n : Nat}
    {cont : List Silmaril.Wasm.Instr} {is is' : List ToCore.CAdmin}
    (h : Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P host) ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P host) ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ :=
  Relation.TransGen.lift
    (fun c : ToCore.CConfig H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : ToCore.CConfig H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact Silmaril.Wasm.Execution.Core.Step.ctxtLabel hs) _ _ h

theorem transGen_frame {s s' : ToCore.CStore H} {f fi fi' : ToCore.CFrame} {n : Nat}
    {is is' : List ToCore.CAdmin}
    (h : Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P host) ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P host) ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ :=
  Relation.TransGen.lift
    (fun c : ToCore.CConfig H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : ToCore.CConfig H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact Silmaril.Wasm.Execution.Core.Step.ctxtFrame hs) _ _ h

end Lift

/-! ## The three context cases of the simulation -/

section Cases

open Silmaril.Wasm.Execution.Core (vals)

variable {P : Silmaril.Wasm.Numerics.Profile} {tgt : ToCore.CHostSemantics H}

/-- `Step.context`: values prefix and arbitrary tail. -/
theorem context {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (ih : ∀ c, Sim ⟨s, f, before⟩ c →
      ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧ Sim ⟨s', f', after⟩ c')
    (hext : StoreExt s s') (hmod : f'.module = f.module)
    (vs : List Value) (tail : List Admin) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, values vs ++ before ++ tail⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧ Sim ⟨s', f', values vs ++ after ++ tail⟩ c' := by
  obtain ⟨hn, hwf⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  obtain ⟨hst, hfr, hl⟩ := hn
  obtain ⟨hsw, hmw, hlw⟩ := hwf
  simp only [listWF_append] at hlw
  obtain ⟨⟨-, hbw⟩, htw⟩ := hlw
  simp only [listToCore_append, values_toCore] at hl
  obtain ⟨l12, l3, rfl, h12, h3⟩ := List.map_eq_append_iff.mp hl
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.mp h12
  have h1' := ToCore.map_norm_vals h1
  subst h1'
  have hin : Sim ⟨s, f, before⟩ ⟨cs, cf, l2⟩ :=
    ⟨ToCore.Config.norm_eq_toCore_iff.mpr ⟨hst, hfr, h2⟩, hsw, hmw, hbw⟩
  obtain ⟨⟨cs', cf', l2'⟩, hT, hn', hwf'⟩ := ih _ hin
  rw [ToCore.Config.norm_eq_toCore_iff] at hn'
  obtain ⟨hst', hfr', hl2'⟩ := hn'
  refine ⟨⟨cs', cf', vals (vs.map Value.toCore) ++ l2' ++ l3⟩, transGen_ctxtInstrs hT, ?_, ?_⟩
  · rw [ToCore.Config.norm_eq_toCore_iff]
    refine ⟨hst', hfr', ?_⟩
    have ht : cf'.module.types = cf.module.types := by
      rw [types_of_erase hfr', types_of_erase hfr, hmod]
    simp only [List.map_append, ToCore.Admin.map_norm_vals, hl2', listToCore_append,
      values_toCore]
    rw [ToCore.Admin.map_norm_congr ht l3, h3, listToCore_congr hext tail htw]
  · exact ⟨hwf'.1, hwf'.2.1, (listWF_append _ _ _).mpr
      ⟨(listWF_append _ _ _).mpr ⟨listWF_values _ _, hwf'.2.2⟩, listWF_mono hext tail htw⟩⟩

/-- `Step.label`. -/
theorem label {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (ih : ∀ c, Sim ⟨s, f, before⟩ c →
      ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧ Sim ⟨s', f', after⟩ c')
    (n : Nat) (cont : Expr) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [.label n cont before]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧ Sim ⟨s', f', [.label n cont after]⟩ c' := by
  obtain ⟨hn, hwf⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  obtain ⟨hst, hfr, hl⟩ := hn
  obtain ⟨hsw, hmw, hlw⟩ := hwf
  simp only [listWF_cons, WF_label, listWF_nil, and_true] at hlw
  simp only [listToCore_cons, label_toCore, listToCore_nil, List.append_nil] at hl
  obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp hl
  obtain ⟨b', rfl, hb'⟩ := ToCore.norm_eq_label hx
  have hin : Sim ⟨s, f, before⟩ ⟨cs, cf, b'⟩ :=
    ⟨ToCore.Config.norm_eq_toCore_iff.mpr ⟨hst, hfr, hb'⟩, hsw, hmw, hlw⟩
  obtain ⟨⟨cs', cf', b''⟩, hT, hn', hwf'⟩ := ih _ hin
  rw [ToCore.Config.norm_eq_toCore_iff] at hn'
  obtain ⟨hst', hfr', hb''⟩ := hn'
  refine ⟨⟨cs', cf', [.label n (cont.map Instr.toCore) b'']⟩, transGen_label hT, ?_, ?_⟩
  · rw [ToCore.Config.norm_eq_toCore_iff]
    refine ⟨hst', hfr', ?_⟩
    simp [hb'']
  · exact ⟨hwf'.1, hwf'.2.1, by simpa using hwf'.2.2⟩

/-- `Step.frame`. -/
theorem frame {s s' : Store H} {inner inner' : Frame} {before after : List Admin}
    (ih : ∀ c, Sim ⟨s, inner, before⟩ c →
      ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧ Sim ⟨s', inner', after⟩ c')
    (hext : StoreExt s s') (n : Nat) (outer : Frame) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, outer, [.frame n inner before]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧
      Sim ⟨s', outer, [.frame n inner' after]⟩ c' := by
  obtain ⟨hn, hwf⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  obtain ⟨hst, hfr, hl⟩ := hn
  obtain ⟨hsw, hmw, hlw⟩ := hwf
  simp only [listWF_cons, WF_frame, listWF_nil, and_true] at hlw
  simp only [listToCore_cons, frame_toCore, listToCore_nil, List.append_nil] at hl
  obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp hl
  obtain ⟨fi, b', rfl, hfi, hb'⟩ := ToCore.norm_eq_frame hx
  have hin : Sim ⟨s, inner, before⟩ ⟨cs, fi, b'⟩ :=
    ⟨ToCore.Config.norm_eq_toCore_iff.mpr ⟨hst, hfi, hb'⟩, hsw, hlw.1, hlw.2⟩
  obtain ⟨⟨cs', fi', b''⟩, hT, hn', hwf'⟩ := ih _ hin
  rw [ToCore.Config.norm_eq_toCore_iff] at hn'
  obtain ⟨hst', hfi', hb''⟩ := hn'
  refine ⟨⟨cs', cf, [.frame n fi' b'']⟩, transGen_frame hT, ?_, ?_⟩
  · rw [ToCore.Config.norm_eq_toCore_iff]
    refine ⟨hst', hfr, ?_⟩
    simp [hb'', hfi']
  · exact ⟨hwf'.1, ModWF.mono hmw hext, by simpa using ⟨hwf'.2.1, hwf'.2.2⟩⟩

end Cases

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
