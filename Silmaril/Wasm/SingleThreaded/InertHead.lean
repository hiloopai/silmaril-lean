module

public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.HeadInversion

@[expose] public section

/-! # Inert heads under arbitrary hosts

An inert active instruction cannot select a host call. Its host-free head
inversion therefore applies without restricting later numerical or host choices.
-/

namespace Silmaril.Wasm.SingleThreaded

open Execution.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- Inert plain heads cannot select a host call, so host-free inversion applies
under every host relation as well. -/
theorem inert_head_inv {s : Store H} {f : Frame} {W : List Val}
    {i : Instr} {rest : List Admin} {c' : Config H}
    (he : (Admin.plain i).val? = none) (ht : i ≠ .throwRef)
    (hi : (Admin.plain i).isCallRef = false)
    (h : Step P host ⟨s, f, vals W ++ .plain i :: rest⟩ c') :
    ∃ vs args c₀, W = vs ++ args ∧ Det.Head P s f args (.plain i) c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ := by
  rcases Step.split_host h with h | ⟨E, a, hh, args, hd, -⟩
  · exact hostFree_head_inv he (by simp) (by simpa using ht) h
  · have hn : decompose? s (vals W ++ .plain i :: rest) = none :=
      decompose?_vals_cons_none he (fun _ _ => decompHead_plain hi)
    rw [hn] at hd
    cases hd

end Silmaril.Wasm.SingleThreaded
