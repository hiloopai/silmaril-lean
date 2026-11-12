module

public import Silmaril.Proofs.Wasm.Game.Instantiate.Alloc

/-!
# Typing of `instantiateOnce?` (Residue)
-/

@[expose] public section

/-! # Typing of instantiation with every global allocated once

`instantiateOnce?` (Exec/InstantiateOnce.lean) runs `$evalglobals` and then the spec's
instantiation of the global-free residue `Module.globalResidue`, whose trailing global imports
are the globals `$evalglobals` allocated. `Instantiate.ok` (the typing of `$instantiate`) does not
apply to the residue: a residue whose initialisers mention `ref.func` of a function defined later
is not typed against the store `$evalglobals` leaves (its provisional instance names function
addresses that `$allocmodule` only allocates). The typing of the residue is therefore proved from
the module's own `Module_ok`:

* `Instantiate.alloc_ok_residue` (Soundness/InstantiationOnceAlloc.lean): the allocation of the
  residue, against the globals that `$evalglobals` allocated (typed at the module's closed global
  types), gives a typed store and a module instance typed against the module context (the
  counterpart of `Instantiate.alloc_ok_aux`);
* `prepare?_globalResidue_ok`: the configuration that the spec's `prepare?` builds for the
  residue, with its start call, is typed, its store extends the original store, and the only new
  function instances are the module's Wasm functions.
-/

namespace Silmaril.Proofs.Wasm.Game.InstantiateAux

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- The steps of `prepare?` for the global-free residue: its (empty) globals evaluate to
nothing, then the table and element initialisers are evaluated and the module allocated. -/
private theorem prepare?_globalResidue_inv {s₁ : Store H} {m : Module} {xas : List ExternAddr}
    {c : Config H} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue xas = some (c, st)) :
    m.elems.length ≤ 2 ^ 32 ∧ ∃ s₂ f₂ refsT s₃ f₃ refsE s₄ mi,
      evalExprs? evalConst? s₁ ⟨[], ModuleInst.initial s₁ m.globalResidue xas⟩
        (m.tables.map Table.init) = some (s₂, f₂, refsT) ∧
      evalExprss? evalConst? s₂ f₂ (m.elems.map Elem.init) = some (s₃, f₃, refsE) ∧
      allocModule? s₃ m.globalResidue xas [] refsT refsE = some (s₄, mi) ∧
      c = ⟨s₄, { module := mi },
        expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
        expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d)⟩ ∧
      st = m.start := by
  unfold prepare? at hp
  split at hp
  · rename_i hb
    simp only [Module.globalResidue_globals, List.map_nil, evalGlobals?] at hp
    split at hp
    · cases hp
    rename_i s₂ f₂ refsT hT
    split at hp
    · cases hp
    rename_i s₃ f₃ refsE hE
    split at hp
    · cases hp
    rename_i s₄ mi hM
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    exact ⟨hb.1, _, _, _, _, _, _, _, _, hT, hE, hM, hp.1.symm, hp.2.symm⟩
  · cases hp

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
  obtain ⟨hgG, -, -⟩ := evalGlobals?_shape hg
  have hg' : EvalGlobals P host s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) s₁ f₁ vs := evalGlobals?_sound evalConst?_evalSound hg
  obtain ⟨hb, s₂, f₂, refsT, s₃, f₃, refsE, s₄, mi, hT, hE, hM, hc, hst⟩ :=
    prepare?_globalResidue_inv hp
  obtain ⟨hTG, -, -⟩ := evalExprs?_shape hT
  obtain ⟨hEG, -, -⟩ := evalExprss?_shape hE
  have hT' : evalExprs? evalConst? s₁ f₁ (m.tables.map Table.init) = some (s₂, f₂, refsT) := by
    rw [hf₁]
    exact hT
  have ht' : EvalExprs P host s₁ f₁ (m.tables.map Table.init) s₂ f₂ refsT :=
    evalExprs?_sound evalConst?_evalSound hT'
  have he' : EvalExprss P host s₂ f₂ (m.elems.map Elem.init) s₃ f₃ refsE :=
    evalExprss?_sound evalConst?_evalSound hE
  have hglob : s₃.globals =
      s.globals ++ List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) vs := by
    rw [hEG, hTG, hgG]
  cases hm with
  | @mk dts _ jts gts tts fdts rts _ C' C htypes himports hC' hC htags hglobals hmems htables
      hfuncs hdata helems hstart hexports hdisjoint =>
    show ConfigOk (c.withStart st) [] ∧ Extend s c.store ∧
      ∃ new : List (FuncInst H), c.store.funcs = s.funcs ++ new ∧
        ∀ fi ∈ new, ∃ code, fi.code = .wasm code
    obtain ⟨hs₄, hmi⟩ := Instantiate.alloc_ok_residue hs htypes himports hC' hC htags
      hglobals hmems htables hfuncs helems hexports hdisjoint hxas hg' ht' he' hglob hM
    obtain ⟨hsh, -⟩ := initEval_ok hs htypes himports hC' hC htags hglobals htables
      hfuncs helems hxas hg' ht' he'
    obtain ⟨tagTypes, funcTypes, xi, -, -, -, -, hs₄eq⟩ := allocModule?_inv hM
    refine ⟨?_, ?_, ?_⟩
    · show ConfigOk (c.withStart st) []
      have hcode := Execution.Core.InstrsOk.rangeRefs (Module.initCode_ok helems (by subst hC; rfl)
        hdata (by subst hC; rfl) hstart hb)
      have hok : ConfigOk (⟨s₄, { module := mi }, expression m.initCode⟩ : Config H)
          [] := by
        refine ⟨_, ⟨hs₄, _, [], hmi, .nil, rfl⟩, ?_⟩
        have hctx : ({ { C with refs := List.range C.funcs.length } with
            locals := ({ C with refs := List.range C.funcs.length } : Context).locals ++
              [] } : Context) = { C with refs := List.range C.funcs.length } := by
          simp
        rw [hctx]
        exact AdminsOk.of_instrsOk (s := s₄) hcode
      rw [hc, hst]
      convert hok using 1
      rw [Module.expression_initCode]
      cases m.start <;> simp [Config.withStart]
    · show Extend s c.store
      rw [hc, hs₄eq]
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
    · rw [hc, hs₄eq]
      refine ⟨_, by rw [← hsh.funcs], ?_⟩
      intro fi hfi
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hfi
      exact ⟨p.2, rfl⟩

end Silmaril.Proofs.Wasm.Game.InstantiateAux
