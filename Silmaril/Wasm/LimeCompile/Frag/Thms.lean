module

public import Silmaril.Wasm.LimeCompile.Frag.Defs
public import Silmaril.Wasm.LimeCompile.Agree.Thms
public import Silmaril.Proofs.Wasm.LimeCompile.Frag.Basic
public import Silmaril.Proofs.Wasm.LimeCompile.Frag.Counter

/-!
# The 3.0 → Lime compiler, validity and host conditions discharged

**Host conditions.** an earlier step stated the container's correctness for hosts that respect `select`
erasure (`Select.HostResp`) and the direct compiler's for code-parametric hosts
(`Sim.HostParametric`), so their agreement needed both. Here:

* **`hostResp_of_parametric`**: every code-parametric host respects erasure (take the reflexive
  function relation "equal after erasure");
* `container_correct_param`, **`container_direct_agree_param`**: container correctness and the
  container/direct agreement under the single hypothesis `HostParametric`.

The converse fails (**`hostResp_not_parametric`**): a host that reports whether every function
body is empty respects erasure but is not code-parametric. So `HostParametric` is the stronger
condition, and the single hypothesis of the agreement theorem.

**Validity.** On `NumFrag` (a valid source whose numeric-`select` lowering is a Lime1 image `L`;
no Lime1 validity assumed):

* `numFrag_iff`: `NumFrag m` iff `m` is valid and the direct compiler succeeds on `m`;
* `numFrag_sel`, `container_eq_direct`: the image is also the full erasure, `L.toCore = selM m`,
  and the container and direct compilers both return `L`;
* **`container_correct_num`**: the container's own correctness proof (erasure bisimulation)
  goes through with the validity of the output's image *derived* from the source
  (`Direct.lowerModule_valid`), for hosts that respect erasure; `container_correct_num_param`
  for code-parametric hosts;
* `frag_of_numFrag`: with a valid `L`, a `NumFrag` module is in `Container.Frag`; and
  `frag_of_numFrag_task`: under the frozen open target `Task.lime1ValidOfCore`, `NumFrag ⊆ Frag`.

What is still not derived: Lime1-level validity (`Lime1.Validation.ModuleValid L`) of the
output; the theorems here give Core validity of `L.toCore` instead. `NumFrag` is smaller than
an earlier `Frag`: a typed `select` at a reference type in dead code (e.g. after `unreachable`) is
allowed by `Frag` (if its erasure is still valid) and rejected by `NumFrag`.

New statements over `Silmaril.Proofs.Wasm.LimeCompile.Frag.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Frag

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (ExportEquiv)
open Silmaril.Wasm.LimeCompile.Select (selM HostResp)
open Silmaril.Wasm.LimeCompile.Direct (lowerModule)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Host conditions -/

/-- **A code-parametric host respects `select` erasure.** -/
theorem hostResp_of_parametric (hp : Sim.HostParametric host) : HostResp host :=
  Silmaril.Proofs.Wasm.LimeCompile.Frag.hostResp_of_parametric hp

/-- Container correctness (pass-1 fragment) for code-parametric hosts. -/
theorem container_correct_param (hp : Sim.HostParametric host) {m : Module}
    (hF : Container.Frag m) :
    ∃ L, Container.compile m = some L ∧ Lime1.Validation.ModuleValid L ∧
      ExportEquiv (· = ·) P host L.toCore m :=
  Container.compile_correct (hostResp_of_parametric hp) hF

/-- **Container and direct translation agree, under one host hypothesis.** -/
theorem container_direct_agree_param (hp : Sim.HostParametric host) {m : Module}
    {l : Lime1.Module} (hF : Container.Frag m) (hd : Direct.compile m = some l) :
    ∃ L, Container.compile m = some L ∧ Lime1.Validation.ModuleValid L ∧
      ExportEquiv (· = ·) P host L.toCore l.toCore :=
  Agree.container_direct_agree (hostResp_of_parametric hp) hp hF hd

/-- **Refutation of the converse**: respecting erasure does not make a host code-parametric. -/
theorem hostResp_not_parametric :
    ∃ host : HostSemantics Unit, HostResp host ∧ ¬ Sim.HostParametric host :=
  ⟨_, Silmaril.Proofs.Wasm.LimeCompile.Frag.bodyHost_resp,
    Silmaril.Proofs.Wasm.LimeCompile.Frag.bodyHost_not_parametric⟩

/-! ## The fragment without a Lime1 validity hypothesis -/

/-- On `NumFrag`, the lowering's Lime1 image is the full erasure. -/
theorem numFrag_sel {m : Module} {L : Lime1.Module} (h : L.toCore = lowerModule m) :
    L.toCore = selM m :=
  Silmaril.Proofs.Wasm.LimeCompile.Frag.selM_eq_of_lower h

/-- On `NumFrag`, the container and the direct compiler return the same Lime1 module. -/
theorem container_eq_direct {m : Module} {L : Lime1.Module} (h : L.toCore = lowerModule m) :
    Container.compile m = some L ∧ Direct.compile m = some L :=
  ⟨Container.compile_of_frag_unique (numFrag_sel h),
    Silmaril.Proofs.Wasm.LimeCompile.Frag.direct_compile_of_lower h⟩

/-- `NumFrag m` iff `m` is valid and the direct compiler succeeds on it. -/
theorem numFrag_iff {m : Module} :
    NumFrag m ↔ (∃ mt, ModuleOk m mt) ∧ ∃ l, Direct.compile m = some l := by
  constructor
  · rintro ⟨hm, L, hL⟩
    exact ⟨hm, L, (container_eq_direct hL).2⟩
  · rintro ⟨hm, l, hl⟩
    exact ⟨hm, l, Direct.compile_toCore hl⟩

/-- **Container correctness on `NumFrag`**: no Lime1 validity hypothesis; the validity of the
output's Core image is derived from the source (same module type). -/
theorem container_correct_num (hh : HostResp host) {m : Module} {mt : CModuleType}
    (hm : ModuleOk m mt) {L : Lime1.Module} (hL : L.toCore = lowerModule m) :
    Container.compile m = some L ∧ ModuleOk L.toCore mt ∧
      ExportEquiv (· = ·) P host L.toCore m := by
  have hv : ModuleOk L.toCore mt := hL ▸ Direct.lowerModule_valid hm
  have hs : L.toCore = selM m := numFrag_sel hL
  have he : ExportEquiv (· = ·) P host m (selM m) :=
    Select.exportEquiv_selM hh ⟨mt, hm⟩ ⟨mt, hs ▸ hv⟩
  refine ⟨(container_eq_direct hL).1, hv, ?_⟩
  rw [hs]
  exact DirectAgree.exportEquiv_symm he

/-- Container correctness on `NumFrag`, for code-parametric hosts. -/
theorem container_correct_num_param (hp : Sim.HostParametric host) {m : Module}
    (hF : NumFrag m) :
    ∃ L, Container.compile m = some L ∧ (∃ mt, ModuleOk L.toCore mt) ∧
      ExportEquiv (· = ·) P host L.toCore m := by
  obtain ⟨⟨mt, hm⟩, L, hL⟩ := hF
  obtain ⟨hc, hv, he⟩ := container_correct_num (P := P) (hostResp_of_parametric hp) hm hL
  exact ⟨L, hc, ⟨mt, hv⟩, he⟩

/-- With a valid Lime1 output, a `NumFrag` module is 's fragment. -/
theorem frag_of_numFrag {m : Module} (hm : ∃ mt, ModuleOk m mt) {L : Lime1.Module}
    (hL : L.toCore = lowerModule m) (hv : Lime1.Validation.ModuleValid L) : Container.Frag m :=
  ⟨hm, L, hv, numFrag_sel hL⟩

/-- **Conditional**: under the open target `Task.lime1ValidOfCore`, `NumFrag ⊆ Container.Frag`. -/
theorem frag_of_numFrag_task (ht : Task.lime1ValidOfCore) {m : Module} (hF : NumFrag m) :
    Container.Frag m := by
  obtain ⟨⟨mt, hm⟩, L, hL⟩ := hF
  exact frag_of_numFrag ⟨mt, hm⟩ hL (ht L ⟨mt, hL ▸ Direct.lowerModule_valid hm⟩)

/-- info: 'Silmaril.Wasm.LimeCompile.Frag.container_correct_num_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms container_correct_num_param

/-- info: 'Silmaril.Wasm.LimeCompile.Frag.container_direct_agree_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms container_direct_agree_param

end Silmaril.Wasm.LimeCompile.Frag
