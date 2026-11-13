module

public import Silmaril.Wasm.LimeCompile.Direct.Thms

/-!
# The direct compiler agrees with every correct 3.0 → Lime compiler

Exact export equivalence (`ExportEquiv (· = ·)`) is an equivalence relation on modules
(`exportEquiv_refl`, `exportEquiv_symm`, `exportEquiv_trans`). So any other compiler `c` that is
correct for it on its fragment (for instance the container compiler, which hosts the input in
an interpreter) **agrees with the direct compiler** wherever both apply: their outputs, read in
Core 3.0 through `Lime1.Module.toCore`, are exactly export-equivalent (`agree`).

* `CorrectOn S c`: on the inputs satisfying `S`, every output of `c` is exactly
  export-equivalent to its input, at every profile and code-parametric host;
* `direct_correctOn`: the direct compiler is `CorrectOn` the valid modules;
* **`agree`**: the direct compiler and any `CorrectOn S` compiler give exactly
  export-equivalent outputs on a valid input in `S` that both compile.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.DirectAgree

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Direct

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem exportEquiv_refl (m : Module) : ExportEquiv (· = ·) P host m m :=
  ⟨ExportRefines.refl (fun _ => rfl) m, ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) m⟩

theorem exportEquiv_symm {m m' : Module} (h : ExportEquiv (· = ·) P host m m') :
    ExportEquiv (· = ·) P host m' m :=
  ⟨h.2.mono fun _ _ e => e.symm, h.1.mono fun _ _ e => e.symm⟩

theorem exportEquiv_trans {m m' m'' : Module} (h : ExportEquiv (· = ·) P host m m')
    (h' : ExportEquiv (· = ·) P host m' m'') : ExportEquiv (· = ·) P host m m'' :=
  ⟨h.1.trans (fun _ _ _ e e' => e.trans e') h'.1,
    h'.2.trans (fun _ _ _ e e' => e'.trans e) h.2⟩

/-- A 3.0 → Lime compiler is **correct on `S`**: each output, read in Core 3.0, is exactly
export-equivalent to its input in `S`, at every profile and code-parametric host. -/
def CorrectOn (S : Module → Prop) (c : Module → Option Lime1.Module) : Prop :=
  ∀ (H : Type) (P : Profile) (host : HostSemantics H), Execution.Core.Sim.HostParametric host →
    ∀ m l, S m → c m = some l → ExportEquiv (· = ·) P host m l.toCore

/-- **The direct compiler is correct on valid modules.** -/
theorem direct_correctOn : CorrectOn (fun m => ∃ mt, ModuleOk m mt) compile :=
  fun _ _ _ hhost _ _ hm h => compile_correct hhost h hm

/-- **Agreement**: on a valid input in `S` that both compile, the direct compiler and any
compiler correct on `S` give exactly export-equivalent Lime1 modules. -/
theorem agree {S : Module → Prop} {c : Module → Option Lime1.Module} (hc : CorrectOn S c)
    (hhost : Execution.Core.Sim.HostParametric host) {m : Module} {l l' : Lime1.Module}
    (hm : ∃ mt, ModuleOk m mt) (hS : S m) (hd : compile m = some l) (hc' : c m = some l') :
    ExportEquiv (· = ·) P host l.toCore l'.toCore :=
  exportEquiv_trans (exportEquiv_symm (compile_correct hhost hd hm)) (hc H P host hhost m l' hS hc')

end Silmaril.Wasm.LimeCompile.DirectAgree
