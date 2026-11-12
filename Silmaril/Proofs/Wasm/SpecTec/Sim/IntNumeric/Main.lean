module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Typing
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Parametric

/-!
# Integer numerics: the family's results, with the typing interface discharged
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String}

/-- **`Forward.numeric` in `simEnv B`**: every integer constructor of `NumericStep` is simulated,
for any `B` extending the integer primitives; the float and conversion constructors are the
hypothesis `OtherNumericFwd`. -/
theorem fwd_numeric_simEnv {B : Silmaril.SpecTec.Sem.Builtins} {P : Silmaril.Wasm.Numerics.Profile}
    (hB : IntB B) (T : TypingFacts (simEnv B) hn) (O : OtherNumericFwd (simEnv B) hn P) :
    ∀ {s : Store H} {f : Frame} {is is' : List Admin} (_ : NumericStep P is is'),
      FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  fwd_numeric hB (intTyping_simEnv B) T O

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
