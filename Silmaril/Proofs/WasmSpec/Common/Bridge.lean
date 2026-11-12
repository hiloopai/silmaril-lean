module

public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.WasmSpec.Common.Defs

/-!
# From body-level to call-level specifications

`Computes.funcSpec`: if the body of `fn` computes `resOf x` from `argsOf x` for
every input `x`, then the function at address `a`, whose instance runs `fn` with
a type of the right arity in every store satisfying `Inv`, satisfies
`PureSpec … argsOf resOf`. The proof is `FuncSpec.of_body`. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Logic.Core

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- `funcPost` is monotone in its result predicate. -/
theorem funcPost_mono {n : Nat} {K K' : Store H → List Val → Prop}
    (hK : ∀ s r, K s r → K' s r) {s : Store H} {F : Frame} {o : Outcome}
    (h : funcPost P host n K s F o) : funcPost P host n K' s F o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | _ | ⟨vs, b, c⟩
  · exact ⟨h.1, hK _ _ h.2⟩
  · obtain ⟨vs₁, r, he, hl, hr⟩ := h
    exact ⟨vs₁, r, he, hl, hK _ _ hr⟩
  · exact h.elim
  · obtain ⟨vs₁, r, he, hl, hr⟩ := h
    exact ⟨vs₁, r, he, hl, hK _ _ hr⟩
  · exact h.elim
  · exact h.elim
  · obtain ⟨vs₁, args, fn, ps, rs, he, hf, hx, hl, hk⟩ := h
    refine ⟨vs₁, args, fn, ps, rs, he, hf, hx, hl, fun g => ?_⟩
    obtain ⟨s', r, hs, hr⟩ := hk g
    exact ⟨s', r, hs, hK _ _ hr⟩

/-- A body-level specification for every input gives the call-level one. -/
theorem Computes.funcSpec {α : Type} {fn : Func} {argsOf resOf : α → List Val}
    (h : ∀ x, Computes fn (argsOf x) (resOf x)) {a : Nat} {fi : FuncInst H}
    {Inv : Store H → Prop} {ps rs : Ty (.list .val)}
    (hfi : ∀ s, Inv s → s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (he : Expand fi.type (.func ps rs)) (hargs : ∀ x, (argsOf x).length = ps.length)
    (hres : ∀ x, (resOf x).length = rs.length) :
    PureSpec P host a Inv argsOf resOf := by
  refine FuncSpec.of_body (fun s _ hp => hfi s hp.1) hcode he ?_ ?_
  · rintro s _ ⟨_, x, rfl⟩
    exact hargs x
  · rintro s _ ⟨_, x, rfl⟩
    have hb : WP P host s (Frame.forCall fi.module (argsOf x) fn.locals) (expression fn.body)
        (funcPost P host rs.length (fun s' r => s' = s ∧ r = resOf x)) := by
      simpa only [hres x] using h x P host s fi.module
    exact hb.mono fun _ _ _ hq => funcPost_mono (fun _ _ hr => ⟨hr.1, x, rfl, hr.2⟩) hq

end Silmaril.WasmSpec
