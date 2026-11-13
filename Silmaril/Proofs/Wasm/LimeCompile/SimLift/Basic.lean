module

public import Silmaril.Wasm.LimeCompile.SimLift.Defs

/-!
# Lifting run transport to export refinement: proofs

Sessions transport along `SessTransport` by induction on the session (`session_transport`), and
module observations along `InstTransport` (`exportRefines_of_instTransport`). The shape follows
silmaril-lean's `exportRefines_of_bodiesRel`, with the store relation as a parameter.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.SimLift

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (exportFunc? ExportRefines ExportEquiv Session SessionRel Call
  moduleObs)
open Silmaril.Wasm.LimeCompile.SimLift

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Session transport.** -/
theorem session_transport {S : Store H → Store H → Prop} {mi mi' : ModuleInst}
    (T : SessTransport P host S mi mi') {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (hs : Session P host mi s script bs) :
    ∀ {t : Store H}, S s t → Session P host mi' t script bs := by
  induction hs with
  | nil => exact fun _ => .nil
  | @stop s x vs rest h =>
    intro t hst
    refine .stop fun a ha hok => ?_
    rw [T.exports] at ha
    exact h a ha ((T.invokeOk hst ha).mpr hok)
  | @done s x vs rest a c r bs ha hok run hr _ ih =>
    intro t hst
    obtain ⟨d, hd, hdc, hst'⟩ := T.run hst ha hok c r run hr
    exact .done (by rw [T.exports]; exact ha) ((T.invokeOk hst ha).mp hok) hd hdc (ih hst')
  | diverge ha hok hd =>
    intro t hst
    exact .diverge (by rw [T.exports]; exact ha) ((T.invokeOk hst ha).mp hok)
      (T.diverges hst ha hok hd)

/-- **Export refinement from instantiation transport.** -/
theorem exportRefines_of_instTransport {m m' : Module} (T : InstTransport P host m m') :
    ExportRefines (· = ·) P host m m' := by
  refine ⟨fun s xas d hs hI => T.back s xas d hs hI, fun s xas script hs bs hbs => ?_⟩
  obtain ⟨c, hI, hcase⟩ := hbs
  obtain ⟨d, S, hI', hrun, hdiv, hT⟩ := T.fwd s xas c hs hI
  refine ⟨bs, ⟨d, hI', ?_⟩, SessionRel.refl (fun _ => rfl) bs⟩
  rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ | ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
  · obtain ⟨d₁, hd₁, hdc, hst⟩ := hrun c₁ (.values []) hS (by simpa [Result.toAdmin, vals] using hcode)
    exact Or.inl ⟨d₁, bs', hd₁, by simpa [Result.toAdmin, vals] using hdc,
      session_transport hT hsess hst, rfl⟩
  · obtain ⟨d₁, hd₁, hdc, -⟩ := hrun c₁ r hS hcode
    exact Or.inr (Or.inl ⟨d₁, r, hd₁, hdc, hr, rfl⟩)
  · exact Or.inr (Or.inr ⟨hdiv hd, rfl⟩)

/-- **Export equivalence from transport in both directions.** -/
theorem exportEquiv_of_instTransport {m m' : Module} (T : InstTransport P host m m')
    (T' : InstTransport P host m' m) : ExportEquiv (· = ·) P host m m' :=
  ⟨exportRefines_of_instTransport T, (exportRefines_of_instTransport T').mono fun _ _ h => h.symm⟩

end Silmaril.Proofs.Wasm.LimeCompile.SimLift
