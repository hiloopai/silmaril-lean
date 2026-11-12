module

public import Silmaril.Proofs.Wasm.LimeCompile.Container.Lime
public import Silmaril.Wasm.LimeCompile.Select.Thms
public import Silmaril.Wasm.Models.Lime1Core.Thms

/-!
# The 3.0 → Lime container compiler: correctness on the pass-1 fragment

* **`compile_correct`**: on `Frag` (valid Core modules that are, up to `select` annotations, the
  Core image of a valid Lime1 module), `compile M` is a valid Lime1 module `L`, and the Core
  image of `L` under `lime1Emb` is **export equivalent** to `M` under `Eq` (silmaril-lean's
  `ExportEquiv`: same instantiation run, then the same behaviours for every session of export
  invocations), for every profile and every host that respects erasure (e.g. the closed host,
  `Select.hostResp_closed`);
* `compile_toCore`, `frag_toCore`: the compiler is the identity on Lime1 (it reads back the
  Lime1 module of a Lime1 image), and every valid Lime1 module is in the fragment;
* `compile_of_frag_unique`: on the fragment the compiler's output is the unique Lime1 module with
  the erased Core image;
* the API side: `types_of_frag` (every type of a fragment module is a single final function type
  over numeric value types), `tags_of_frag` (no exception tags), and the refutation
  `not_frag_of_type`/`funcrefResult_not_lime`: a module whose type section declares, e.g., a
  function type returning `funcref` is outside the fragment, and *no* Lime1 module has it as Core
  image up to `select` annotations. Such an API cannot be preserved exactly; it has to be
  translated (restated at the API level), which is left to later passes.

New statements over the proofs in `Silmaril.Proofs.Wasm.LimeCompile.Container` and
`Silmaril.Proofs.Wasm.LimeCompile.Select`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Container

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (ExportEquiv)
open Silmaril.Wasm.LimeCompile.Select

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The compiler is the identity on Lime1**: it reads back the Lime1 module of a Lime1
image. -/
theorem compile_toCore (L : Lime1.Module) : compile L.toCore = some L :=
  Silmaril.Proofs.Wasm.LimeCompile.Container.compile_toCore L

/-- Every valid Lime1 module's Core image is in the fragment. -/
theorem frag_toCore {L : Lime1.Module} (hL : Lime1.Validation.ModuleValid L) : Frag L.toCore :=
  ⟨(Silmaril.Wasm.Models.Lime1Core.validIn_v30 hL).1,
    L, hL, (Silmaril.Proofs.Wasm.LimeCompile.Container.selM_toCore L).symm⟩

/-- On the fragment, the output is the Lime1 module whose image is the erased module. -/
theorem compile_of_frag_unique {m : Module} {L : Lime1.Module} (hL : L.toCore = selM m) :
    compile m = some L :=
  Silmaril.Proofs.Wasm.LimeCompile.Container.compile_of_eq hL

/-- **Container correctness.** On the fragment, the compiler returns a valid Lime1
module whose Core image (the module map of `lime1Emb`) is export equivalent to the source. -/
theorem compile_correct (hh : HostResp host) {m : Module} (hF : Frag m) :
    ∃ L, compile m = some L ∧ Lime1.Validation.ModuleValid L ∧
      ExportEquiv (· = ·) P host ((Silmaril.Wasm.Models.Lime1Core.lime1Emb H).mod L) m := by
  obtain ⟨hm, L, hL, hLm⟩ := hF
  have hv : ∃ mt, ModuleOk (selM m) mt := hLm ▸ (Silmaril.Wasm.Models.Lime1Core.validIn_v30 hL).1
  have he : ExportEquiv (· = ·) P host m (selM m) := exportEquiv_selM hh hm hv
  refine ⟨L, compile_of_frag_unique hLm, hL, ?_⟩
  show ExportEquiv (· = ·) P host L.toCore m
  rw [hLm]
  exact ⟨he.2.mono fun _ _ h => h.symm, he.1.mono fun _ _ h => h.symm⟩

/-! ## What the fragment's API can be -/

/-- Every type of a fragment module is a single final function type over numeric value
types. -/
theorem types_of_frag {m : Module} (hF : Frag m) :
    ∀ rt ∈ m.types, ∃ ft : V1.FuncType, rt = ft.toCoreRec := by
  obtain ⟨-, L, -, hLm⟩ := hF
  have ht : m.types = L.toCore.types := by rw [hLm]; rfl
  rw [ht]
  exact Silmaril.Proofs.Wasm.LimeCompile.Container.types_toCore L

/-- A fragment module declares no exception tags. -/
theorem tags_of_frag {m : Module} (hF : Frag m) : m.tags = [] := by
  obtain ⟨-, L, -, hLm⟩ := hF
  have ht : m.tags = L.toCore.tags := by rw [hLm]; rfl
  rw [ht]
  rfl

/-- **Refutation**: a module declaring a type that is not a numeric function type is outside the
fragment. -/
theorem not_frag_of_type {m : Module} {rt : RecType} (hrt : rt ∈ m.types)
    (h : ∀ ft : V1.FuncType, rt ≠ ft.toCoreRec) : ¬ Frag m := fun hF =>
  let ⟨ft, hft⟩ := types_of_frag hF rt hrt
  h ft hft

/-- The function type `[] → [funcref]` is not the image of a Lime1 type. -/
theorem funcrefResult_not_lime :
    ∀ ft : V1.FuncType, (⟨[⟨true, [], .func ⟨[], [.ref ⟨true, .abstract .func⟩]⟩⟩]⟩ : RecType) ≠
      ft.toCoreRec := by
  intro ft h
  have h' := congrArg resultsOf h
  have hr : [ValType.ref ⟨true, .abstract .func⟩] = ft.results.map ValType.num :=
    Option.some.inj h'
  cases hres : ft.results with
  | nil => rw [hres] at hr; cases hr
  | cons t ts => rw [hres] at hr; cases hr

end Silmaril.Wasm.LimeCompile.Container
