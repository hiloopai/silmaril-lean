module

public import Silmaril.Wasm.Tools.Gen.Cmd.Equiv.Defs
public import Silmaril.Wasm.Tools.Gen.Cmd.Mutate.Thms
public import Silmaril.Wasm.Binaryen.InlDeadFunc

/-!
# `--preserve-semantics` is observationally equivalent

* `exportEquiv_appendFunc`: appending a defined function to a valid module whose function
  types take numeric parameters, such that the result is valid, is an export equivalence (the
  Core-level form of silmaril's `exportEquiv_append_unreferenced_func`, through its lemmas
  `InlDF.inst_fwd`, `inst_back`, `inst_left_facts` and `df_obs_corr`: a lockstep simulation up
  to the extra trailing function instance, which nothing can name);
* `numParamsB_spec`: the executable check of the side condition;
* **`mutate_preserve_equiv`**: every output of `wasm-tools mutate --preserve-semantics` on a
  valid input is `ObsEquiv` to the input.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Equiv

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation Silmaril.Wasm.Models Silmaril.Wasm.Tools.Gen.Cmd.Mutate

/-- The side condition, as silmaril states it. -/
def NumParams (m : Module) : Prop :=
  ∀ st ∈ m.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
    ∀ t ∈ ft.params, ∃ nt, t = .num nt

theorem numParamsB_spec {m : Module} (h : numParamsB m = true) : NumParams m := by
  intro st hst ft hb t ht
  have h1 : (match st.body with
      | .func ft => ft.params.all Smith.isNum
      | _ => true) = true := List.all_eq_true.mp h st hst
  have h2 : ft.params.all Smith.isNum = true := by simpa only [hb] using h1
  have h3 : Smith.isNum t = true := List.all_eq_true.mp h2 t ht
  cases t with
  | num nt => exact ⟨nt, rfl⟩
  | vec _ => simp [Smith.isNum] at h3
  | ref _ => simp [Smith.isNum] at h3

variable {H : Type} {host : HostSemantics H} {oracle : GrowKind → Nat → Nat → Nat → Bool}

/-- The extended module refines the original one. -/
theorem appendFunc_refines {M : Module} {F : Func} (hp : NumParams M) (hM : ModuleValid M)
    (hM₁ : ModuleValid (appendFunc M F)) (hR : HostRespectsCode host) (hok : HostOk host) :
    ExportRefines (· = ·) (Profile.deterministic oracle) host (appendFunc M F) M := by
  obtain ⟨⟨xtI, xtE⟩, hM⟩ := hM
  obtain ⟨⟨xtI₁, xtE₁⟩, hM₁⟩ := hM₁
  have hp' : ∀ d ∈ allocTypes M.types, InlDF.NumParams d := InlDF.numParams_types hp
  refine ⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩
  · obtain ⟨c', hi', -⟩ := InlDF.inst_fwd (F := F) hM₁ hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hobs⟩ := hbs
    obtain ⟨c, hi, hrel⟩ := InlDF.inst_back hM hi'
    have hinv : InlDF.SessInv c.store c.frame.module := InlDF.inst_left_facts hs hp' hi
    have hc : ConfigOk c [] := Instantiate.ok hok hs hi
    have hc' : ConfigOk c' [] := Instantiate.ok hok hs hi'
    exact ⟨bs, ⟨c, hi, (InlDF.df_obs_corr hR hok hc hc' hrel hinv script bs).2 hobs⟩,
      SessionRel.refl (fun _ => rfl) bs⟩

/-- The original module refines the extended one. -/
theorem appendFunc_refines_back {M : Module} {F : Func} (hp : NumParams M) (hM : ModuleValid M)
    (hM₁ : ModuleValid (appendFunc M F)) (hR : HostRespectsCode host) (hok : HostOk host) :
    ExportRefines (fun b b' => b' = b) (Profile.deterministic oracle) host M (appendFunc M F) := by
  obtain ⟨⟨xtI, xtE⟩, hM⟩ := hM
  obtain ⟨⟨xtI₁, xtE₁⟩, hM₁⟩ := hM₁
  have hp' : ∀ d ∈ allocTypes M.types, InlDF.NumParams d := InlDF.numParams_types hp
  refine ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩
  · obtain ⟨c, hi, -⟩ := InlDF.inst_back hM hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hobs⟩ := hbs
    obtain ⟨c', hi', hrel⟩ := InlDF.inst_fwd (F := F) hM₁ hi
    have hinv : InlDF.SessInv c.store c.frame.module := InlDF.inst_left_facts hs hp' hi
    have hc : ConfigOk c [] := Instantiate.ok hok hs hi
    have hc' : ConfigOk c' [] := Instantiate.ok hok hs hi'
    exact ⟨bs, ⟨c', hi', (InlDF.df_obs_corr hR hok hc hc' hrel hinv script bs).1 hobs⟩,
      SessionRel.refl (R := fun b b' => b' = b) (fun _ => rfl) bs⟩

/-- **Appending a function is an observational equivalence** (valid module and result, numeric
parameters). -/
theorem exportEquiv_appendFunc {M : Module} {F : Func} (hp : NumParams M) (hM : ModuleValid M)
    (hM₁ : ModuleValid (appendFunc M F)) : ObsEquiv (appendFunc M F) M :=
  fun _ _ _ hR hok => ⟨appendFunc_refines hp hM hM₁ hR hok, appendFunc_refines_back hp hM hM₁ hR hok⟩

/-- `ObsEquiv` is symmetric. -/
theorem ObsEquiv.symm {m m' : Module} (h : ObsEquiv m m') : ObsEquiv m' m :=
  fun o H host hR hok =>
    ⟨(h o H host hR hok).2.mono (fun _ _ e => e.symm), (h o H host hR hok).1.mono (fun _ _ e => e.symm)⟩

/-- **`wasm-tools mutate --preserve-semantics` preserves the semantics**: on an input valid in
the model, every output is observationally equivalent to the input. -/
theorem mutate_preserve_equiv {S : FeatureSet} {cfg : Smith.Config} {o : Opts} {seed : UInt64}
    {m m' : Module} (ho : o.preserveSemantics = true) (hm : ValidIn S m)
    (h : mutate S cfg o seed m = some m') : ObsEquiv m' m := by
  have hv : ValidIn S m' := mutate_validIn h
  obtain ⟨hn, f, rfl⟩ := mutateExtend_appends (mutate_preserve_eq ho h)
  exact exportEquiv_appendFunc (numParamsB_spec hn) hm.1 hv.1

end Silmaril.Wasm.Tools.Gen.Cmd.Equiv
