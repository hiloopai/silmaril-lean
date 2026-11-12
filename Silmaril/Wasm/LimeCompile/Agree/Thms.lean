module

public import Silmaril.Wasm.LimeCompile.Container.Thms
public import Silmaril.Wasm.LimeCompile.DirectAgree.Thms
public import Silmaril.Wasm.LimeCompile.Preserve.Thms

/-!
# The three pass-1 routes of the 3.0 → Lime compiler, related

Integration of the container (`Container.compile`), the direct translation (`Direct.compile`)
and the Lime-preserving variant (`Preserve.limePres`):

* `container_limePreserving`, `direct_limePreserving`: both compilers are Lime-preserving in the
  sense of `Preserve.LimePreserving`, so `limePres` leaves each of them unchanged
  (`limePres_container`, `limePres_direct`);
* `direct_correct'`: the direct compiler is `Preserve.Correct` for `ExactOnValid` (exact export
  equivalence of valid inputs at every profile and code-parametric host), a reflexive relation,
  so `limePres` of it is correct as well (`limePres_direct_correct`);
* **`container_direct_agree`**: on the container's fragment, whenever the direct compiler also
  succeeds, the two Lime1 outputs are exactly export-equivalent in Core 3.0, at every profile
  and every host that both respects `select` erasure and is code-parametric (for instance the
  closed host, `closedHost_parametric`).

New statements; the proofs are compositions of the tracks' headers.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Agree

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.LimeCompile.Preserve (LimePreserving Correct limePres)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The container compiler is the identity on Lime-only code. -/
theorem container_limePreserving : LimePreserving Container.compile :=
  Container.compile_toCore

/-- The direct compiler is the identity on Lime-only code. -/
theorem direct_limePreserving : LimePreserving Direct.compile :=
  Direct.compile_lime

theorem limePres_container : limePres Container.compile = Container.compile :=
  (Preserve.limePres_eq_self_iff _).2 container_limePreserving

theorem limePres_direct : limePres Direct.compile = Direct.compile :=
  (Preserve.limePres_eq_self_iff _).2 direct_limePreserving

/-- Exact export equivalence of a valid input, at every profile and code-parametric host. -/
def ExactOnValid (m m' : Module) : Prop :=
  (∃ mt, ModuleOk m mt) → ∀ (H : Type) (P : Profile) (host : HostSemantics H),
    Sim.HostParametric host → ExportEquiv (· = ·) P host m m'

theorem exactOnValid_refl (m : Module) : ExactOnValid m m :=
  fun _ _ _ _ _ => DirectAgree.exportEquiv_refl m

/-- The direct compiler's correctness as a `Preserve.Correct` statement. -/
theorem direct_correct' : Correct ExactOnValid Direct.compile :=
  fun _ _ h hm _ _ _ hh => Direct.compile_correct hh h hm

theorem limePres_direct_correct : Correct ExactOnValid (limePres Direct.compile) :=
  Preserve.limePres_correct exactOnValid_refl direct_correct'

/-- The closed host is code-parametric (it has no interactions). -/
theorem closedHost_parametric : Sim.HostParametric (closedHost (H := H)) :=
  fun _ _ _ _ _ _ _ _ h => h.elim

/-- **Container and direct translation agree.** On the container's fragment, if the direct
compiler also succeeds, the two Lime1 outputs are exactly export-equivalent in Core 3.0. -/
theorem container_direct_agree (hr : Select.HostResp host) (hp : Sim.HostParametric host)
    {m : Module} {l : Lime1.Module} (hF : Container.Frag m) (hd : Direct.compile m = some l) :
    ∃ L, Container.compile m = some L ∧ Lime1.Validation.ModuleValid L ∧
      ExportEquiv (· = ·) P host L.toCore l.toCore := by
  obtain ⟨L, hc, hL, he⟩ := Container.compile_correct (P := P) hr hF
  exact ⟨L, hc, hL, DirectAgree.exportEquiv_trans he (Direct.compile_correct hp hd hF.1)⟩

/-- The agreement at the closed host. -/
theorem container_direct_agree_closed {m : Module} {l : Lime1.Module} (hF : Container.Frag m)
    (hd : Direct.compile m = some l) :
    ∃ L, Container.compile m = some L ∧ Lime1.Validation.ModuleValid L ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) L.toCore l.toCore :=
  container_direct_agree Select.hostResp_closed closedHost_parametric hF hd

/-- info: 'Silmaril.Wasm.LimeCompile.Agree.container_direct_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms container_direct_agree

end Silmaril.Wasm.LimeCompile.Agree
