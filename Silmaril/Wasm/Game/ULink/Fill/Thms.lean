module

public import Silmaril.Wasm.Game.ULink.Defs
import Silmaril.Proofs.Wasm.Game.ULink.Fill

/-!
# Steps of a function call in an evaluation context

Exported specialisations of the context lemmas of `Silmaril.Proofs.Wasm.Game.ULink.Fill`, for a
pending call `vals vs ++ [ref.func a, c]` (`c` a `call_ref`-like instruction, `a` a function of
the store with `vs.length` parameters) in an arbitrary context `E`, at **every** profile:

* `step_fill_call`: every host-free step of `E.fill (vals vs ++ [ref.func a, c])` is a step of the
  call (under the empty frame) in the hole of `E`;
* `decompose_fill_call`: a call with no host-call redex has none in any context;
* `fill_call_ne_result`: the filled code is not a result.

New theorems (statements only; proofs in `Silmaril.Proofs.Wasm.Game.ULink.Fill`).
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.ULink

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

section
variable {s : Store Nat} {vs : List Val} {a : Nat} {c : Admin} {fi : FuncInst Nat}
  {ps rs : Ty (.list .val)}

/-- **A host-free step of a call in a context is a step of the call in the hole.** -/
theorem step_fill_call {P : Profile} (E : Ctx) {f : Frame} {d : Config Nat} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length)
    (h : Step P (Det.noHost (H := Nat)) ⟨s, f, E.fill (vals vs ++ [.ref (.func a), c])⟩ d) :
    ∃ s' Y', d = ⟨s', f, E.fill Y'⟩ ∧
      Step P (Det.noHost (H := Nat)) ⟨s, {}, vals vs ++ [.ref (.func a), c]⟩ ⟨s', {}, Y'⟩ := by
  obtain ⟨s', Y', hd, -, hst⟩ := Silmaril.Proofs.Wasm.Game.ULink.step_fill_inv E
    (.inr (.inl ⟨vs, a, c, fi, ps, rs, rfl, hc, hf, he, hn⟩)) h
  exact ⟨s', Y', hd, hst⟩

/-- **A call with no callout has no callout in any context.** -/
theorem decompose_fill_call (E : Ctx) (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length)
    (h : decompose? s (vals vs ++ [.ref (.func a), c]) = none) :
    decompose? s (E.fill (vals vs ++ [.ref (.func a), c])) = none := by
  rw [Silmaril.Proofs.Wasm.Game.ULink.decompose_fill
    (.inr (.inl ⟨vs, a, c, fi, ps, rs, rfl, hc, hf, he, hn⟩)) E, h]
  rfl

/-- A call in a context is not a result. -/
theorem fill_call_ne_result (E : Ctx) (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) (r : Result) :
    E.fill (vals vs ++ [.ref (.func a), c]) ≠ r.toAdmin :=
  Silmaril.Proofs.Wasm.Game.ULink.fill_ne_result
    (.inr (.inl ⟨vs, a, c, fi, ps, rs, rfl, hc, hf, he, hn⟩)) E r

end

end Silmaril.Wasm.Game.ULink
