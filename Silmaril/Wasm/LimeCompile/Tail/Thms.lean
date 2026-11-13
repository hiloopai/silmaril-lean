module

public import Silmaril.Proofs.Wasm.LimeCompile.Tail.Typing
public import Silmaril.Wasm.LimeCompile.DirectAgree.Thms
public import Silmaril.Wasm.Execution.Core.Soundness.Defs

/-!
# The direct 3.0 → Lime compiler with tail calls: results

The compiler `compile` (`Silmaril.Wasm.LimeCompile.Tail.Defs`) lowers typed `select`s
(`Direct.lowerModule`) and rewrites `return_call x` to `call x; return` and
`return_call_indirect t y` to `call_indirect t y; return` outside `try_table` bodies
(`tailModule`), then reads the result back as a Lime1 module.

Proved (no `Task`):

* `tailModule_valid`, `lower_valid`, `compile_valid`: the rewrite keeps validity and the module
  type (`call x; return` has the type of `return_call x`, by subsumption on `return`);
* `compile_toCore`: a successful compilation is the lowering, read in Core;
* `compile_api`: the API is kept exactly (only function bodies change);
* **`compile_lime`**: the compiler is the identity on Lime1 modules;
* `compile_eq_direct`: on modules whose lowered bodies have no tail call (outside `try_table`)
  it is the pass-1 direct compiler `Direct.compile`;
* `size_tailL`: size data, one extra instruction (`return`) per replaced tail call.

Open, frozen as **`Task.tailSim`** (a `Prop`, not assumed anywhere unconditionally): a valid
module and its tail rewrite are exactly export-equivalent, at every profile and every host that
is code-parametric and satisfies the host contract `HostOk` (well-typed results; the callee's
results are returned by the caller's `return`, so their number must be the caller's arity).
Correctness of the compiler is stated conditionally on it (`compile_correct`).

The relation that `Task.tailSim` needs is not a code-relation closure with matching exit kernels
(silmaril-lean's `BaseSim`): after `return_call x` the source exits its labels and its frame with
the kernel `return_call_ref` and runs the callee *outside* the caller's frame, while the target
runs the callee *inside* it, under the caller's labels, and only then exits with `return`. See
"Tail calls" in `docs/projects/wasm-wasi.md` for the non-local relation and the plan.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Tail

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.LimeCompile.Tail

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Open target (frozen)**: a valid module and its tail-call rewrite are exactly
export-equivalent, at every profile and every code-parametric host satisfying the host
contract. -/
def Task.tailSim : Prop :=
  ∀ (H : Type) (P : Profile) (host : HostSemantics H), Execution.Core.Sim.HostParametric host →
    HostOk host → ∀ m : Module, (∃ mt, ModuleOk m mt) →
      ExportEquiv (· = ·) P host m (tailModule m)

/-- **The tail rewrite of a valid module is valid**, with the same module type. -/
theorem tailModule_valid {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    ModuleOk (tailModule m) mt :=
  tailModule_ok h

/-- The whole lowering keeps validity and the module type. -/
theorem lower_valid {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    ModuleOk (lower m) mt :=
  tailModule_ok (Direct.lowerModule_valid h)

/-- The check of a successful compilation, and the read-back. -/
theorem compile_some {m : Module} {l : Lime1.Module} (h : compile m = some l) :
    Direct.funcrefElemsB (lower m) = true ∧ Lime1.Module.ofCore? (lower m) = some l := by
  unfold compile at h
  split at h
  · rename_i hc
    exact ⟨hc, h⟩
  · cases h

/-- **A successful compilation is the lowering, read in Core.** -/
theorem compile_toCore {m : Module} {l : Lime1.Module} (h : compile m = some l) :
    l.toCore = lower m := by
  obtain ⟨hf, hl⟩ := compile_some h
  rw [Silmaril.Wasm.Component.Lime1Inst.module_retract hl, Direct.funcrefElems_eq hf]

/-- The Core image of the output of a valid module validates, with the same module type. -/
theorem compile_valid {m : Module} {l : Lime1.Module} (h : compile m = some l)
    {mt : CModuleType} (hm : ModuleOk m mt) : ModuleOk l.toCore mt := by
  rw [compile_toCore h]
  exact lower_valid hm

/-- **The API is kept exactly**: only function bodies change. -/
theorem compile_api {m : Module} {l : Lime1.Module} (h : compile m = some l) :
    ({ l.toCore with funcs := [] } : Module) = { m with funcs := [] } ∧
      l.toCore.funcs.map (fun f => (f.type, f.locals)) =
        m.funcs.map (fun f => (f.type, f.locals)) := by
  rw [compile_toCore h]
  refine ⟨rfl, ?_⟩
  simp only [lower, tailModule, Direct.lowerModule, List.map_map]
  rfl

/-- **The compiler is the identity on Lime1**: every Lime1 module is compiled to itself. -/
theorem compile_lime (l : Lime1.Module) : compile l.toCore = some l := by
  have he : Direct.funcrefElemsB l.toCore = true := by
    simp [Direct.funcrefElemsB, Lime1.Module.toCore, Lime1.Elem.toCore]
  unfold compile
  simp only [lower_toCore, he, ↓reduceIte, Lime1.Module.ofCore?_toCore]

/-- Without tail calls (outside `try_table`) the tail rewrite is the identity. -/
theorem tailModule_of_count {m : Module} (h : ∀ f ∈ m.funcs, tailCountL f.body = 0) :
    tailModule m = m := by
  have hf : m.funcs.map tailFunc = m.funcs := by
    conv => rhs; rw [← List.map_id m.funcs]
    exact List.map_congr_left fun f hf => by
      simp only [tailFunc, tailL_of_count f.body (h f hf), id]
  simp only [tailModule, hf]

/-- **On modules without tail calls the compiler is the pass-1 direct compiler.** -/
theorem compile_eq_direct {m : Module}
    (h : ∀ f ∈ (Direct.lowerModule m).funcs, tailCountL f.body = 0) :
    compile m = Direct.compile m := by
  unfold compile Direct.compile
  rw [lower, tailModule_of_count h]

/-- **Size data**: counting every instruction, nested bodies included, the rewrite adds exactly
one instruction per replaced tail call. -/
theorem size_tailL (is : List Instr) : size (tailL is) = size is + tailCountL is :=
  Silmaril.Proofs.Wasm.LimeCompile.Tail.size_tailL is

/-- **Conditional correctness**: given `Task.tailSim`, a valid Core 3.0 module and the Core image
of its compilation are exactly export-equivalent, at every profile and every code-parametric
host satisfying the host contract. -/
theorem compile_correct (hT : Task.tailSim) (hhost : Execution.Core.Sim.HostParametric host)
    (hok : HostOk host) {m : Module} {l : Lime1.Module} (h : compile m = some l)
    (hm : ∃ mt, ModuleOk m mt) : ExportEquiv (· = ·) P host m l.toCore := by
  rw [compile_toCore h]
  obtain ⟨mt, hmt⟩ := hm
  exact DirectAgree.exportEquiv_trans (Direct.lower_exportEquiv hhost ⟨mt, hmt⟩)
    (hT H P host hhost hok _ ⟨mt, Direct.lowerModule_valid hmt⟩)

/-- info: 'Silmaril.Wasm.LimeCompile.Tail.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compile_correct

end Silmaril.Wasm.LimeCompile.Tail
