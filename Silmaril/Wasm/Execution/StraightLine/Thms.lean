module

public import Silmaril.Wasm.Execution.StraightLine.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Execution.StraightLine

/-!
# Every run of a straight-line numeric function, at any profile

For a straight-line numeric function `fi` (`Fn fi args.length op`: no declared locals, one
result, body `local.get 0 … local.get (k-1); op` with `op` a scalar numeric instruction) at the
address `a` of the store `s`, and **any** profile `P` (for instance the specification profile
`Profile.spec nd r`, whose float operators return the sets `floatUnOpRel`/`floatBinOpRel`/
`convertRel`), the host-free runs of `$invoke(s, a, args)` are exactly:

* `nf`: **every normal form** is `⟨s, {}, is'⟩` for some result `is'` of the numeric step
  `NumericStep P (vals args ++ [op]) is'` (if there is one: `hex`);
* `reaches`: **every** such `is'` is reached;
* `not_diverges`: **no run is infinite**; `extends_nf`: every finite run extends to a normal
  form;
* `numericStep_result`: `is'` is one value or a trap, and `not_step_result`: it is a normal form.

`fn?_sound` turns the checker `fn?` into `Fn`. The proofs (`Silmaril.Proofs.Wasm.Execution.
StraightLine`) invert every step through the profile-independent head decomposition
`Det.Step.decomp`; only the numeric step depends on `P`, and it is kept as the relation.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.StraightLine

open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {s : Store H} {a : Nat} {fi : FuncInst H} {args : List Val}
  {op : Instr}

theorem fn?_sound {k : Nat} (h : fn? fi k = some op) : Fn fi k op :=
  Silmaril.Proofs.Wasm.Execution.StraightLine.fn?_sound h

/-- The result of a numeric step is one value or a trap. -/
theorem numericStep_result {l is' : List Admin} (h : NumericStep P l is') :
    (∃ v : Val, is' = [v.toAdmin]) ∨ is' = [.trap] :=
  Silmaril.Proofs.Wasm.Execution.StraightLine.numericStep_result h

/-- The result of a numeric step is a normal form. -/
theorem not_step_result {l is' : List Admin} (h : NumericStep P l is') {f : Frame}
    {c : Config H} : ¬ Step P noHost ⟨s, f, is'⟩ c :=
  Silmaril.Proofs.Wasm.Execution.StraightLine.not_step_result h

/-- **Every normal form** of the invocation is `⟨s, {}, is'⟩` for a result `is'` of the numeric
step. -/
theorem nf (hf : s.funcs[a]? = some fi) (hfn : Fn fi args.length op)
    (hex : ∃ is', NumericStep P (vals args ++ [.plain op]) is') {c : Config H}
    (h : Steps P noHost (invoke s a args) c) (hnf : ∀ x, ¬ Step P noHost c x) :
    ∃ is', NumericStep P (vals args ++ [.plain op]) is' ∧ c = ⟨s, {}, is'⟩ := by
  obtain ⟨code, ps, rs, D⟩ := Silmaril.Proofs.Wasm.Execution.StraightLine.data_of_fn hf hfn
  exact Silmaril.Proofs.Wasm.Execution.StraightLine.nf D hex h hnf

/-- **Every result** of the numeric step is reached. -/
theorem reaches (hf : s.funcs[a]? = some fi) (hfn : Fn fi args.length op) {is' : List Admin}
    (hn : NumericStep P (vals args ++ [.plain op]) is') :
    Steps P noHost (invoke s a args) ⟨s, {}, is'⟩ := by
  obtain ⟨code, ps, rs, D⟩ := Silmaril.Proofs.Wasm.Execution.StraightLine.data_of_fn hf hfn
  exact Silmaril.Proofs.Wasm.Execution.StraightLine.steps_done D hn

/-- **No run is infinite.** -/
theorem not_diverges (hf : s.funcs[a]? = some fi) (hfn : Fn fi args.length op) :
    ¬ Diverges P noHost (invoke s a args) := by
  obtain ⟨code, ps, rs, D⟩ := Silmaril.Proofs.Wasm.Execution.StraightLine.data_of_fn hf hfn
  exact Silmaril.Proofs.Wasm.Execution.StraightLine.not_diverges D

/-- **Every finite run extends to a normal form.** -/
theorem extends_nf (hf : s.funcs[a]? = some fi) (hfn : Fn fi args.length op) {c : Config H}
    (h : Steps P noHost (invoke s a args) c) :
    ∃ c', Steps P noHost c c' ∧ ∀ x, ¬ Step P noHost c' x := by
  obtain ⟨code, ps, rs, D⟩ := Silmaril.Proofs.Wasm.Execution.StraightLine.data_of_fn hf hfn
  exact Silmaril.Proofs.Wasm.Execution.StraightLine.extends_nf D h

end Silmaril.Wasm.Execution.Core.StraightLine

end
