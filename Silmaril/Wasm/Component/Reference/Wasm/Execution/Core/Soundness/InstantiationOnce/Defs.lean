module

public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Core.Soundness.InstantiationOnceAlloc.Defs

/-!
# `Wasm.Execution.Core.Soundness.InstantiationOnce`: the laws that definitions cite

The theorems of the component reference copy `Wasm.Execution.Core.Soundness.InstantiationOnce` that
definition parts cite (engine records bundle such laws as fields). The other theorems stay in
`Silmaril.Raw.Wasm.Component.Wasm.Execution.Core.Soundness.InstantiationOnce`, which imports this
module.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
variable {H : Type}

/-- The parts of a successful `prepare?` of the residue after `$evalglobals`: the residue has no
globals, so its own global evaluation returns the store, the initial frame and no values. -/
theorem prepare?_residue_inv {s₁ : Store H} {m : Module} {xas : List ExternAddr}
    {c : Config H} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue xas = some (c, st)) :
    ∃ s₂ f₂ refsT s₃ f₃ refsE s₄ mi,
      (m.globalResidue.elems.length ≤ 2 ^ 32 ∧ m.globalResidue.data.length ≤ 2 ^ 32 ∧
        (∀ d ∈ m.globalResidue.data, d.bytes.size < 2 ^ 32) ∧
        (∀ e ∈ m.globalResidue.elems, e.init.length < 2 ^ 32)) ∧
      evalExprs? evalConst? s₁ ⟨[], ModuleInst.initial s₁ m.globalResidue xas⟩
        (m.globalResidue.tables.map Table.init) = some (s₂, f₂, refsT) ∧
      evalExprss? evalConst? s₂ f₂ (m.globalResidue.elems.map Elem.init) = some (s₃, f₃, refsE) ∧
      allocModule? s₃ m.globalResidue xas [] refsT refsE = some (s₄, mi) ∧
      c = ⟨s₄, { module := mi },
        expression ((List.range m.globalResidue.elems.length).zip m.globalResidue.elems |>.flatMap
          fun (i, e) => runElem i e) ++
        expression ((List.range m.globalResidue.data.length).zip m.globalResidue.data |>.flatMap
          fun (i, d) => runData i d)⟩ ∧
      st = m.globalResidue.start := by
  unfold prepare? at hp
  split at hp <;> try contradiction
  rename_i hb
  split at hp <;> try contradiction
  rename_i s₁' f₁' valsG' hG
  simp only [Module.globalResidue_globals, List.map_nil, evalGlobals?, Option.some.injEq,
    Prod.mk.injEq] at hG
  obtain ⟨rfl, rfl, rfl⟩ := hG
  split at hp <;> try contradiction
  rename_i s₂ f₂ refsT hT
  split at hp <;> try contradiction
  rename_i s₃ f₃ refsE hE
  split at hp <;> try contradiction
  rename_i s₄ mi hM
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨s₂, f₂, refsT, s₃, f₃, refsE, s₄, mi, hb, hT, hE, hM, rfl, rfl⟩

/-- Allocating the residue after an evaluation of the shape `EvalShape` extends the original
store. -/
theorem allocModule?_residue_extend {s s₃ s₄ : Store H} {m : Module} {xas : List ExternAddr}
    {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst} (hs : StoreOk s)
    (hsh : EvalShape s s₃)
    (hM : allocModule? s₃ m.globalResidue xas [] refsT refsE = some (s₄, mi)) :
    Extend s s₄ := by
  obtain ⟨tagTypes, funcTypes, xi, -, -, -, -, hs₄eq⟩ := allocModule?_inv hM
  rw [hs₄eq]
  simp only [Module.globalResidue, List.map_nil, List.zip_nil_right]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ExtendsList.of_prefix (by rw [← hsh.tags]; exact List.prefix_append _ _)
      fun _ _ => rfl
  · exact ExtendsList.of_prefix (hsh.globals.trans (List.prefix_append _ _))
      fun _ _ => ⟨rfl, .inr rfl⟩
  · exact ExtendsList.of_prefix (by rw [← hsh.mems]; exact List.prefix_append _ _)
      fun _ _ => ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  · exact ExtendsList.of_prefix (by rw [← hsh.tables]; exact List.prefix_append _ _)
      fun _ _ => ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  · exact ExtendsList.of_prefix (by rw [← hsh.funcs]; exact List.prefix_append _ _)
      fun _ _ => ⟨rfl, rfl, fun _ h => h, fun _ h => h⟩
  · exact ExtendsList.of_prefix (by rw [← hsh.datas]; exact List.prefix_append _ _)
      fun _ _ => .inl rfl
  · exact ExtendsList.of_prefix (by rw [← hsh.elems]; exact List.prefix_append _ _)
      fun _ _ => ⟨rfl, .inl rfl⟩
  · refine ExtendsList.of_prefix hsh.structs fun si hsi => ?_
    obtain ⟨fs, he, hf⟩ := hs.structs si hsi
    exact ⟨rfl, fs, he, rfl, by simpa using hf.length_eq, fun _ _ h => .inr h⟩
  · refine ExtendsList.of_prefix hsh.arrays fun ai hai => ?_
    obtain ⟨ft, he, _⟩ := hs.arrays ai hai
    match ft, he with
    | .field m z, he => exact ⟨rfl, m, z, he, rfl, .inr rfl⟩
  · exact ExtendsList.of_prefix (by rw [hsh.exns]) fun _ _ => rfl

/-- Allocating the residue appends only the module's Wasm functions. -/
theorem allocModule?_residue_funcs {s s₃ s₄ : Store H} {m : Module} {xas : List ExternAddr}
    {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst} (hsh : EvalShape s s₃)
    (hM : allocModule? s₃ m.globalResidue xas [] refsT refsE = some (s₄, mi)) :
    ∃ new : List (FuncInst H), s₄.funcs = s.funcs ++ new ∧
      ∀ fi ∈ new, ∃ code, fi.code = .wasm code := by
  obtain ⟨tagTypes, funcTypes, xi, -, -, -, -, hs₄eq⟩ := allocModule?_inv hM
  rw [hs₄eq]
  refine ⟨_, by rw [← hsh.funcs], ?_⟩
  intro fi hfi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hfi
  exact ⟨p.2, rfl⟩

/-- The preparation of the residue after `$evalglobals` is typed: the configuration that the
spec's `prepare?` builds, with its start call, is typed at `[]`, its store extends the original
store, and the only new function instances are the module's Wasm functions. -/
theorem prepare?_globalResidue_ok {P : Profile} {host : HostSemantics H} (_hhost : HostOk host)
    {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {s₁ : Store H} {f₁ : Frame} {vs : List Val} {c : Config H} {st : Option FuncIdx}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c, st)) :
    ConfigOk (c.withStart st) [] ∧ Extend s c.store ∧
      ∃ new : List (FuncInst H), c.store.funcs = s.funcs ++ new ∧
        ∀ fi ∈ new, ∃ code, fi.code = .wasm code := by
  obtain ⟨xtE, xtI, hm, hxas⟩ := hvalid
  have hf₁ : f₁ = ⟨[], ModuleInst.initial s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length)⟩ := evalGlobals?_initial hg
  have hgG : s₁.globals =
      s.globals ++ List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) vs :=
    (evalGlobals?_shape hg).1
  have hg' : EvalGlobals P host s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) s₁ f₁ vs := evalGlobals?_sound evalConst?_evalSound hg
  obtain ⟨s₂, f₂, refsT, s₃, f₃, refsE, s₄, mi, hb, hT, hE, hM, rfl, rfl⟩ :=
    prepare?_residue_inv hp
  have hT' : evalExprs? evalConst? s₁ f₁ (m.tables.map Table.init) = some (s₂, f₂, refsT) := by
    rw [hf₁]
    exact hT
  have hTG : s₂.globals = s₁.globals := (evalExprs?_shape hT').1
  have hEG : s₃.globals = s₂.globals := (evalExprss?_shape hE).1
  have ht' : EvalExprs P host s₁ f₁ (m.tables.map Table.init) s₂ f₂ refsT :=
    evalExprs?_sound evalConst?_evalSound hT'
  have he' : EvalExprss P host s₂ f₂ (m.elems.map Elem.init) s₃ f₃ refsE :=
    evalExprss?_sound evalConst?_evalSound hE
  have hglob : s₃.globals =
      s.globals ++ List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) vs := by
    rw [hEG, hTG, hgG]
  cases hm with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart
      hexports hdisjoint =>
    show ConfigOk _ [] ∧ Extend s s₄ ∧ ∃ new : List (FuncInst H), s₄.funcs = s.funcs ++ new ∧
      ∀ fi ∈ new, ∃ code, fi.code = .wasm code
    rename_i C' C
    obtain ⟨hs₄, hmi⟩ := Instantiate.alloc_ok_residue hs htypes himports hC' hC htags
      hglobals hmems htables hfuncs helems hexports hdisjoint hxas hg' ht' he' hglob hM
    obtain ⟨hsh, -⟩ := initEval_ok hs htypes himports hC' hC htags hglobals htables
      hfuncs helems hxas hg' ht' he'
    have hcode := InstrsOk.rangeRefs (Module.initCode_ok helems (by subst hC; rfl)
      hdata (by subst hC; rfl) hstart hb.1)
    have hok : ConfigOk (⟨s₄, { module := mi }, expression m.initCode⟩ : Config H) [] := by
      refine ⟨_, ⟨hs₄, _, [], hmi, .nil, rfl⟩, ?_⟩
      have hctx : ({ { C with refs := List.range C.funcs.length } with
          locals := ({ C with refs := List.range C.funcs.length } : Context).locals ++
            [] } : Context) = { C with refs := List.range C.funcs.length } := by
        simp
      rw [hctx]
      exact AdminsOk.of_instrsOk (s := s₄) hcode
    refine ⟨?_, allocModule?_residue_extend hs hsh hM, allocModule?_residue_funcs hsh hM⟩
    convert hok using 1
    rw [Module.expression_initCode]
    cases hst : m.start <;> simp [Config.withStart, Module.globalResidue, hst]

end Silmaril.Wasm.Execution.Core
