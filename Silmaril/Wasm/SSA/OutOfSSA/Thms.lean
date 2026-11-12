module

public import Silmaril.Wasm.SSA.OutOfSSA.Defs
import Silmaril.Proofs.Wasm.SSA.OutOfSSA.Complete

/-!
# Out of SSA: correctness

If `decompileFunc f = some g`, every terminating outcome (return value or
trap) of the SSA function `f` on some arguments is an outcome of the fragment
function `g` on the same arguments, and `g` has `f`'s parameter and result
types.

The proof (`Silmaril.Proofs.Wasm.SSA.OutOfSSA`) is a forward simulation by
induction on lambda-SSA evaluation: every SSA variable in scope reads its value
from the Wasm locals; a jump to a `cfg` block copies its argument into the
block's locals and branches to the Wasm `block` or `loop`; the frame
condition of a jump says that locals allocated before the target `cfg`
(other than the block's own parameter locals) are unchanged. A dead block
(whose label the entry does not mention) is never reached, because a region
exits only through labels it mentions.

Conversely (`decompileFunc_complete`), every terminating outcome of `g` is an
outcome of `f`: if the decompiled code terminates, the region evaluates
(`Silmaril.Proofs.Wasm.SSA.OutOfSSA.term`, by induction on the region with an
inner induction on the Wasm `loop` derivation), and by the forward simulation
and determinism of the fragment its exit is the code's outcome. Hence
`decompileFunc_iff`: the two functions have the same terminating outcomes on
every argument list, so `f` has none (diverges or is stuck) exactly when `g`
has none. This needs the decompiler's static checks: operator `let₁`s only for
operators that cannot trap there (`opSafe`), and trap exits only with `()`. The emitted code's Wasm validity (local types, block types) is
not proved; local types come from the decompiler's type inference.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

/-- **Out-of-SSA soundness**: terminating SSA outcomes are outcomes of the
decompiled function. -/
theorem decompileFunc_sound {f : SFunc} {g : FragFunc} (hd : decompileFunc f = some g)
    {args : List WVal} {o : FOut} (h : f.Run args o) : g.Run args o :=
  Silmaril.Proofs.Wasm.SSA.OutOfSSA.decompileFunc_sound hd h

/-- The decompiled function has the same parameter and result types. -/
theorem decompileFunc_params {f : SFunc} {g : FragFunc} (hd : decompileFunc f = some g) :
    g.params = f.params ∧ g.result = f.result :=
  Silmaril.Proofs.Wasm.SSA.OutOfSSA.decompileFunc_params hd

/-- **Out-of-SSA completeness**: terminating outcomes of the decompiled function are
outcomes of the SSA function. -/
theorem decompileFunc_complete {f : SFunc} {g : FragFunc} (hd : decompileFunc f = some g)
    {args : List WVal} {o : FOut} (h : g.Run args o) : f.Run args o :=
  Silmaril.Proofs.Wasm.SSA.OutOfSSA.decompileFunc_complete hd h

/-- **Out-of-SSA is exact**: the decompiled function has the same terminating
outcomes as the SSA function. -/
theorem decompileFunc_iff {f : SFunc} {g : FragFunc} (hd : decompileFunc f = some g)
    {args : List WVal} {o : FOut} : g.Run args o ↔ f.Run args o :=
  ⟨decompileFunc_complete hd, decompileFunc_sound hd⟩

end Silmaril.Wasm.SSA
