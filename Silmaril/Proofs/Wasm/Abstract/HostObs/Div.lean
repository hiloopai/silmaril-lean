module

public import Silmaril.Wasm.Abstract.HostObs.Defs
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Thms
public import Silmaril.Wasm.Abstract.DivO.Thms

/-!
# Divergent Core invocations against the host observations (proofs)

`core_div_wasmHostObs` (deterministic profile): a divergent Core run of a typed invocation is a
`hostDiv` observation of `wasmHostObs` (a logged pending call the host may diverge on, after a
consistent log), or diverges natively: local divergence (`LocalCallDivO (hostCall host)`)
after a finite descent, or an infinite descent chain. The latter two are not observations of
`wasmHostObs`, whose closing omits divergence.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostObs

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- **Every Core divergence of a typed invocation is a `hostDiv` observation, or native
divergence** (deterministic profile). -/
theorem core_div_wasmHostObs {o : GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hd : Diverges (profile o) host (invoke s a vs)) :
    (∃ (cs : List (Call (wasmHostSig H))) (m : (wasmHostSig H).Op),
        HObs.hostDiv cs m ∈ wasmHostObs host s a vs) ∨
      (∃ z, (z = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ z) ∧
        LocalCallDivO (hostCall host) z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = ⟨a, (vs, s)⟩ ∧
        ∀ n, BodyReachO (hostCall host) (g n) (g (n + 1)) := by
  rcases invoke_div_decomp hT hH hs hS hok hd with ⟨y, fi, hh, hy, hf, hcode, hdiv⟩ | h | h
  · obtain ⟨cs, hmem, hcs⟩ :=
      (wasmEvPend_iff (host := host) (m := (hh, y.2.2, y.2.1))).mpr ⟨y, fi, hh, hy, hf, hcode, rfl⟩
    exact .inl ⟨cs, _, .inr (.inl ⟨cs, _, rfl, hmem, hcs, hdiv⟩)⟩
  · exact .inr (.inl h)
  · exact .inr (.inr h)

end Silmaril.Proofs.Wasm.Abstract.HostObs
