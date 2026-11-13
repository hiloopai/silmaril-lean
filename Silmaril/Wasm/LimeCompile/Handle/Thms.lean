module

public import Silmaril.Wasm.LimeCompile.Handle.Defs
public import Silmaril.Proofs.Wasm.LimeCompile.Handle.Sem
public import Silmaril.Wasm.LimeCompile.Frag.Thms

/-!
# The 3.0 → Lime compiler: `funcref`/`externref` exports as `i32` handles

**API level** (consistent with `Preserve.api_iff`):

* `handleApi_lime`: a translated API is a Lime API (`Preserve.ApiLime`);
* **`handleApi_eq_self_iff`**: the translation fixes exactly the Lime APIs, so
  **`exact_iff_fixed`**: an API can be preserved exactly (`Preserve.api_iff`) iff the handle
  translation leaves it unchanged;
* **`api_handle_iff`**: an API can be *translated* (some Lime1 module has the translated API) iff
  `handleApi` is defined on it: every export type is a Lime type, or a final function type /
  global type whose non-Lime value types are `funcref`/`externref`;
* witnesses: `(func (param externref))` becomes `(func (param i32))`
  (`handleApi_externrefFunc`), `(func (result funcref))` becomes `(func (result i32))`; GC struct
  references, `v128`, tags and 64-bit memories have no translation (`handleApi_structFunc`,
  ... are `none`).

**Behaviour level** ("correct up to the API translation", `Handle.HandleCorrectOn`):

* `equivUpTo_of_exportEquiv`: exact export equivalence at a Lime source API is equivalence up to
  the handle translation (for every handle table);
* `handleCorrectOn_of_exact`: a compiler that keeps the export API and is exactly correct is
  correct up to the translation; hence the **direct compiler** (`direct_handleCorrect`, valid
  inputs), the **container** (`container_handleCorrect`, pass-1 fragment, and
  `container_handleCorrect_num`, on `Frag.NumFrag`) are correct in the restated sense.

**Not done (open).** No compiler here produces a translated API for a source whose API is not
already Lime: such sources are outside every fragment above, so `HandleCorrectOn` is only
witnessed where the translation is the identity. A compiler that rewrites reference-typed
parameters, results and locals to `i32` handles (a code translation together with a
simulation relating references to handles through `σ`, with handles allocated during a
session) is the next target; it is not stated as a `Task`, because the fixed-table
formulation here cannot express handles for references created by the module itself.

New statements over `Silmaril.Proofs.Wasm.LimeCompile.Handle`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Handle

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (ExportEquiv)
open Silmaril.Wasm.LimeCompile.Preserve (ApiTy ApiLime Compiler funcExport externrefFunc structFunc
  v128Func tagExport mem64Export)
open Silmaril.Proofs.Wasm.LimeCompile.Handle

/-! ## API level -/

/-- A translated API is a Lime API. -/
theorem handleApi_lime' {A A' : List (String × Option ApiTy)} (h : handleApi A = some A') :
    ApiLime A' :=
  handleApi_lime h

/-- **The translation fixes exactly the Lime APIs.** -/
theorem handleApi_eq_self_iff (A : List (String × Option ApiTy)) :
    handleApi A = some A ↔ ApiLime A :=
  ⟨handleApi_lime, handleApi_of_apiLime⟩

/-- **Exact preservation, restated**: an export API is kept exactly by some Lime1 module iff the
handle translation leaves it unchanged. -/
theorem exact_iff_fixed (M : Module) (hlen : M.exports.length ≤ 2 ^ 32 - 1) :
    (∃ l : Lime1.Module, Preserve.Module.exportApi l.toCore = Preserve.Module.exportApi M) ↔
      handleApi (Preserve.Module.exportApi M) = some (Preserve.Module.exportApi M) := by
  rw [handleApi_eq_self_iff]
  exact Preserve.api_iff M hlen

/-- **When an export API can be translated**: some Lime1 module has the translated API iff the
translation is defined. -/
theorem api_handle_iff (M : Module) (hlen : M.exports.length ≤ 2 ^ 32 - 1) :
    (∃ l : Lime1.Module,
        some (Preserve.Module.exportApi l.toCore) = handleApi (Preserve.Module.exportApi M)) ↔
      (handleApi (Preserve.Module.exportApi M)).isSome = true := by
  constructor
  · rintro ⟨l, hl⟩
    rw [← hl]
    rfl
  · intro h
    obtain ⟨A', hA'⟩ := Option.isSome_iff_exists.mp h
    have hlen' : A'.length ≤ 2 ^ 32 - 1 := by
      rw [length_of_mapM hA']
      simpa [Preserve.Module.exportApi] using hlen
    obtain ⟨l, hl⟩ := Preserve.exists_of_apiLime (handleApi_lime hA') hlen'
    exact ⟨l, by rw [hl, hA']⟩

/-! ### Witnesses -/

/-- `(func (param externref))` is translated to `(func (param i32))`. -/
theorem handleApi_externrefFunc :
    handleApi (Preserve.Module.exportApi externrefFunc) =
      some (Preserve.Module.exportApi (funcExport ⟨[.i32], []⟩)) := by decide

/-- `(func (result funcref))` is translated to `(func (result i32))`. -/
theorem handleApi_funcrefResult :
    handleApi (Preserve.Module.exportApi (funcExport ⟨[], [.ref ⟨true, .abstract .func⟩]⟩)) =
      some (Preserve.Module.exportApi (funcExport ⟨[], [.i32]⟩)) := by decide

theorem handleApi_structFunc : handleApi (Preserve.Module.exportApi structFunc) = none := by
  decide
theorem handleApi_v128Func : handleApi (Preserve.Module.exportApi v128Func) = none := by decide
theorem handleApi_tagExport : handleApi (Preserve.Module.exportApi tagExport) = none := by decide
theorem handleApi_mem64Export : handleApi (Preserve.Module.exportApi mem64Export) = none := by
  decide

/-! ## Behaviour level -/

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Exact equivalence at a Lime source API is equivalence up to handles.** -/
theorem equivUpTo_of_exportEquiv' {σ : List Val} {m' m : Module}
    (hA : ApiLime (Preserve.Module.exportApi m)) (he : ExportEquiv (· = ·) P host m' m) :
    EquivUpTo σ P host m' m :=
  equivUpTo_of_exportEquiv hA he

/-- A compiler that keeps the export API and is exactly correct is correct up to the handle
translation. -/
theorem handleCorrectOn_of_exact {S : Module → Prop} {c : Compiler}
    (hc : ∀ M l, S M → c M = some l →
      Preserve.Module.exportApi l.toCore = Preserve.Module.exportApi M ∧
        ∀ (H : Type) (P : Profile) (host : HostSemantics H), Sim.HostParametric host →
          ExportEquiv (· = ·) P host l.toCore M) :
    HandleCorrectOn S c := by
  intro M l hS hl
  obtain ⟨hapi, he⟩ := hc M l hS hl
  have hA : ApiLime (Preserve.Module.exportApi M) := hapi ▸ Preserve.apiLime_toCore l
  refine ⟨?_, fun H σ P host hp => equivUpTo_of_exportEquiv hA (he H P host hp)⟩
  rw [hapi]
  exact handleApi_of_apiLime hA

/-- **The direct compiler is correct up to the handle translation** (valid inputs). -/
theorem direct_handleCorrect : HandleCorrectOn (fun M => ∃ mt, ModuleOk M mt) Direct.compile :=
  handleCorrectOn_of_exact fun M _ hM hl =>
    ⟨(congrArg Preserve.Module.exportApi (Direct.compile_toCore hl)).trans
        (exportApi_lowerModule M),
      fun _ _ _ hp => DirectAgree.exportEquiv_symm (Direct.compile_correct hp hl hM)⟩

/-- **The container is correct up to the handle translation** on an earlier fragment. -/
theorem container_handleCorrect : HandleCorrectOn Container.Frag Container.compile :=
  handleCorrectOn_of_exact fun M l hF hl => by
    have ⟨_, L, _, hL⟩ := hF
    obtain rfl : L = l := Option.some.inj ((Container.compile_of_frag_unique hL).symm.trans hl)
    refine ⟨by rw [hL, exportApi_selM], fun H P host hp => ?_⟩
    obtain ⟨L₂, hc₂, -, he⟩ := Frag.container_correct_param (P := P) hp hF
    obtain rfl : L₂ = L := Option.some.inj (hc₂.symm.trans hl)
    exact he

/-- The container is correct up to the handle translation on `Frag.NumFrag`. -/
theorem container_handleCorrect_num : HandleCorrectOn Frag.NumFrag Container.compile := by
  intro M l hF hl
  obtain ⟨hM, L, hL⟩ := hF
  have hd : Direct.compile M = some l := by
    rw [(Frag.container_eq_direct hL).2, ← (Frag.container_eq_direct hL).1, hl]
  exact direct_handleCorrect M l hM hd

/-- info: 'Silmaril.Wasm.LimeCompile.Handle.api_handle_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms api_handle_iff

/-- info: 'Silmaril.Wasm.LimeCompile.Handle.container_handleCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms container_handleCorrect

end Silmaril.Wasm.LimeCompile.Handle
