module

public import Silmaril.Proofs.Wasm.LimeCompile.Select.Step
public import Silmaril.Wasm.Binaryen.CodeSimModule

/-!
# Erasing `select` annotations: modules

A module and its erasure `selM m` have bodies related by silmaril-lean's code-relation closure
`Sim.InstrsRel SelBI` (`instrsRel_selL`), so silmaril-lean's `instantiate_bodiesRel` instantiates
them to configurations with equal frame and code and related stores; related stores erase
equally (`selS_of_storeRel`). From there runs, divergence and sessions of export calls carry
over by the bisimulation of `Step.lean`, and the two modules are export equivalent
(`exportRefines_sel`, `exportEquiv_selM`), for every profile and every host that respects
erasure.

New proofs (the shape of the module-level argument follows silmaril-lean's
`exportRefines_of_bodiesRel`, which needs a `BaseSim` instead of our bisimulation).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Select

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (ModuleBodiesRel ExportRefines ExportEquiv Session SessionRel Call
  moduleObs instantiate_bodiesRel)
open Silmaril.Wasm.LimeCompile.Select

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Code relations -/

theorem selL_append (l l' : List Instr) : selL (l ++ l') = selL l ++ selL l' := by
  simp only [selL_eq_map, List.map_append]

/-- Every body is `SelBI`-related to its erasure. -/
theorem instrsRel_selL (l : List Instr) : Sim.InstrsRel SelBI l (selL l) := by
  cases l with
  | nil => exact .nil
  | cons i l =>
    cases i with
    | select ts =>
      exact .append (x := [.select ts]) (.base ⟨ts, none, rfl, rfl⟩) (instrsRel_selL l)
    | block bt b => exact .cons (.block bt (instrsRel_selL b)) (instrsRel_selL l)
    | loop bt b => exact .cons (.loop bt (instrsRel_selL b)) (instrsRel_selL l)
    | if_ bt b₁ b₂ =>
      exact .cons (.if_ bt (instrsRel_selL b₁) (instrsRel_selL b₂)) (instrsRel_selL l)
    | tryTable bt cs b => exact .cons (.tryTable bt cs (instrsRel_selL b)) (instrsRel_selL l)
    | _ => exact .cons (.refl _) (instrsRel_selL l)
termination_by sizeOf l

mutual
/-- Related instructions erase equally, for a base relation that does. -/
theorem selI_of_instrRel {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → selL x = selL y) :
    ∀ {i j : Instr}, Sim.InstrRel BI i j → selI i = selI j
  | _, _, .refl _ => rfl
  | _, _, .block bt h => by rw [selI_block, selI_block, selL_of_instrsRel hBI h]
  | _, _, .loop bt h => by rw [selI_loop, selI_loop, selL_of_instrsRel hBI h]
  | _, _, .if_ bt h₁ h₂ => by
    rw [selI_if, selI_if, selL_of_instrsRel hBI h₁, selL_of_instrsRel hBI h₂]
  | _, _, .tryTable bt cs h => by rw [selI_tryTable, selI_tryTable, selL_of_instrsRel hBI h]

/-- Related sequences erase equally, for a base relation that does. -/
theorem selL_of_instrsRel {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → selL x = selL y) :
    ∀ {x y : List Instr}, Sim.InstrsRel BI x y → selL x = selL y
  | _, _, .nil => rfl
  | _, _, .cons hi hs => by
    rw [selL_cons, selL_cons, selI_of_instrRel hBI hi, selL_of_instrsRel hBI hs]
  | _, _, .base h => hBI _ _ h
  | _, _, .append h₁ h₂ => by
    rw [selL_append, selL_append, selL_of_instrsRel hBI h₁, selL_of_instrsRel hBI h₂]
end

theorem selBI_sel : ∀ x y, SelBI x y → selL x = selL y := by
  rintro _ _ ⟨ts, ts', rfl, rfl⟩
  rfl

theorem selBI_flip_sel : ∀ x y, SelBI y x → selL x = selL y :=
  fun x y h => (selBI_sel y x h).symm

/-- A module's bodies are `SelBI`-related to those of its erasure. -/
theorem bodiesRel_selM (m : Module) : ModuleBodiesRel SelBI m (selM m) := by
  refine ⟨rfl, ?_⟩
  simp only [selM]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, instrsRel_selL f.body⟩ ih

/-! ## Stores -/

theorem selFI_of_funcRel {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → selL x = selL y) {fi gi : FuncInst H} (h : Sim.FuncRel BI fi gi) :
    selFI fi = selFI gi := by
  obtain ⟨ty, m, code⟩ := fi
  obtain ⟨ty', m', code'⟩ := gi
  obtain ⟨rfl, rfl, hc⟩ := h
  cases code <;> cases code' <;> simp only [Sim.FuncCodeRel] at hc
  · obtain ⟨ht, hl, hb⟩ := hc
    simp only [selFI, selFn, ht, hl, selL_of_instrsRel hBI hb]
  · simp only [selFI, hc]

theorem map_selFI_of_forall₂ {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → selL x = selL y) :
    ∀ {X Y : List (FuncInst H)}, List.Forall₂ (Sim.FuncRel BI) X Y → X.map selFI = Y.map selFI
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    rw [List.map_cons, List.map_cons, selFI_of_funcRel hBI h, map_selFI_of_forall₂ hBI hs]

/-- Stores with `FuncRel BI`-related functions erase equally. -/
theorem selS_of_storeRel {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → selL x = selL y) {s t : Store H}
    (h : Sim.StoreRel (Sim.FuncRel BI) s t) : selS s = selS t := by
  have ht : t = { s with funcs := t.funcs } := (Silmaril.Wasm.Binaryen.storeRel_eq_withFuncs h).symm
  have hf : s.funcs.map selFI = t.funcs.map selFI := map_selFI_of_forall₂ hBI h.funcs
  rw [ht]
  simp only [selS, hf]

theorem valOk_sel {s t : Store H} (h : selS s = selS t) {v : Val} {ty : CValType}
    (hv : ValOk s v ty) : ValOk t v ty := by
  have ht : t = { s with funcs := t.funcs } := (selS_eq h).1
  rw [ht]
  cases hv with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref hr => exact .ref ((refOk_funcs_iff (types_eq_of_selS h)).mpr hr)

theorem invokeOk_sel {s t : Store H} (h : selS s = selS t) {a : Nat} {vs : List Val}
    (hok : InvokeOk s a vs) : InvokeOk t a vs := by
  obtain ⟨fi, ps, rs, hf, he, hv⟩ := hok
  obtain ⟨fi', hf', hfe⟩ := funcs_get_of_selS h hf
  have hty : fi'.type = fi.type := (selFI_eq hfe).1
  exact ⟨fi', ps, rs, hf', by rw [hty]; exact he, hv.imp fun _ _ hv => valOk_sel h hv⟩

/-! ## Runs and sessions -/

theorem run_sel (hh : HostResp host) {c d c₁ : Config H} (hcd : selC c = selC d)
    (hS : Steps P host c c₁) {r : Result} (hr : c₁.code = r.toAdmin) :
    ∃ d₁, Steps P host d d₁ ∧ d₁.code = r.toAdmin ∧ selS c₁.store = selS d₁.store := by
  obtain ⟨d₁, hS', h₁⟩ := steps_sim hh hS d hcd
  have hrel := selC_iff.mp h₁
  have hcode : selAs d₁.code = selAs r.toAdmin := by rw [← hr]; exact hrel.2.2.symm
  exact ⟨d₁, hS', eq_of_selAs_rig (allRig_result r) hcode, hrel.1⟩

/-- **Session transport**: a session from a store is one from every store erasing like it. -/
theorem session_sel (hh : HostResp host) {mi : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (hs : Session P host mi s script bs) :
    ∀ {t : Store H}, selS s = selS t → Session P host mi t script bs := by
  induction hs with
  | nil => exact fun _ => .nil
  | stop h => exact fun hst => .stop fun a ha hok => h a ha (invokeOk_sel hst.symm hok)
  | done ha hok run hr _ ih =>
    intro t hst
    obtain ⟨d, hd, hdc, hst'⟩ := run_sel hh (invoke_sel hst _ _) run hr
    exact .done ha (invokeOk_sel hst hok) hd hdc (ih hst')
  | diverge ha hok hd =>
    exact fun hst => .diverge ha (invokeOk_sel hst hok) (diverges_sim hh hd (invoke_sel hst _ _))

/-- The observations of an instantiation configuration carry over to every configuration that
erases like it. -/
theorem obs_sel (hh : HostResp host) {c c' : Config H} (hcc : selC c = selC c')
    {script : List Call} {bs : List (Behaviour Val)}
    (hcase : (∃ c₁ bs', Steps P host c c₁ ∧ c₁.code = [] ∧
        Session P host c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps P host c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges P host c ∧ bs = [.diverges])) :
    (∃ c₁ bs', Steps P host c' c₁ ∧ c₁.code = [] ∧
        Session P host c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps P host c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges P host c' ∧ bs = [.diverges]) := by
  have hfr : c.frame = c'.frame := (selC_iff.mp hcc).2.1
  rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ | ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
  · obtain ⟨d, hd, hdc, hst⟩ := run_sel hh hcc hS (r := .values []) hcode
    exact Or.inl ⟨d, bs', hd, hdc, hfr ▸ session_sel hh hsess hst, rfl⟩
  · obtain ⟨d, hd, hdc, -⟩ := run_sel hh hcc hS hcode
    exact Or.inr (Or.inl ⟨d, r, hd, hdc, hr, rfl⟩)
  · exact Or.inr (Or.inr ⟨diverges_sim hh hd hcc, rfl⟩)

/-! ## Modules -/

/-- **Modules whose bodies erase equally refine each other at the export API** (under `Eq`),
for a host that respects erasure. -/
theorem exportRefines_sel (hh : HostResp host) {BI : List Instr → List Instr → Prop}
    (hBI : ∀ x y, BI x y → selL x = selL y)
    {m m' : Module} (hrel : ModuleBodiesRel BI m m') (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk m' mt) : ExportRefines (· = ·) P host m m' := by
  refine ⟨fun s xas c' _ hI' => ?_, fun s xas script _ bs hbs => ?_⟩
  · obtain ⟨c, hc, -⟩ := instantiate_bodiesRel hrel.flip hm hI'
    exact ⟨c, hc⟩
  · obtain ⟨c, hI, hcase⟩ := hbs
    obtain ⟨c', hI', hfr, hco, hst⟩ := instantiate_bodiesRel hrel hm' hI
    have hcc : selC c = selC c' := selC_iff.mpr ⟨selS_of_storeRel hBI hst, hfr.symm, by rw [hco]⟩
    exact ⟨bs, ⟨c', hI', obs_sel hh hcc hcase⟩, SessionRel.refl (fun _ => rfl) bs⟩

/-- **A module and its erasure are export equivalent.** -/
theorem exportEquiv_selM (hh : HostResp host) {m : Module} (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk (selM m) mt) : ExportEquiv (· = ·) P host m (selM m) :=
  ⟨exportRefines_sel hh selBI_sel (bodiesRel_selM m) hm hm',
    (exportRefines_sel hh selBI_flip_sel (bodiesRel_selM m).flip hm' hm).mono
      fun _ _ h => h.symm⟩

end Silmaril.Proofs.Wasm.LimeCompile.Select
