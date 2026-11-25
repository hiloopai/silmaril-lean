module

public import Silmaril.Wasm.Abstract.BackInv.Defs
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Div
import Silmaril.Wasm.Interp.Thms

/-!
# Divergence passes through host-free steps, for every invariant with closed-valid principal
types (proofs)

`HostCall.diverges_through` proves, for `Sim.ContextTyped` configurations in the deterministic
profile, that a divergent run passes through every host-free step: host-free steps join within
one step, and every other successor than the interpreter's shrinks the code
(`Silmaril.Wasm.Interp.step?_lag_at`). The proof reads only two things of typing: the
interpreter's exactness at the configuration's store, which holds as soon as the store's
principal types are closed-valid (`StoreTy`; `SingleThreaded.Exec.interpHead_exact_of_ty`, of
which `interpHead_exact` at `StoreOk` is the corollary), and the cast side conditions of the
code (`DeepAll IHeadInv`). Here it is proved for every invariant `I` kept by host-free steps
whose configurations have a store with closed-valid principal types and the cast side
conditions (`diverges_through_of`).

* `diverges_through_of`;
* `storeTy_of_storeOk`, `storeTy_deepAll_of_ctx`: `Sim.ContextTyped` configurations satisfy the
  hypotheses.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BackInv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec.Interp
open Silmaril.Wasm.Abstract (StoreTy)

variable {H : Type}

theorem storeTy_of_storeOk {s : Store H} (hs : StoreOk s) : StoreTy s :=
  fun _ _ e => Ref.type?_tyOk hs e

theorem storeTy_deepAll_of_ctx {c : Config H} (h : Sim.ContextTyped c) :
    StoreTy c.store ∧ DeepAll IHeadInv c.frame c.code :=
  ⟨storeTy_of_storeOk (HostCall.contextTyped_storeOk h), HostCall.contextTyped_deepAll h⟩

/-! ## Divergence passes through host-free steps -/

section Through

variable {o : GrowOracle} {host : HostSemantics H} {I : Config H → Prop}

theorem through_aux_of (hI : ∀ c, I c → StoreTy c.store ∧ DeepAll IHeadInv c.frame c.code)
    (hstep : ∀ c c', I c → Det.DStep o c c' → I c') :
    ∀ (n : Nat) (K : Config H), sizeOf K.code = n → I K →
      Diverges (profile o) host K → ∀ d, Det.DStep o K d →
        ∃ d', Step (profile o) host d d' ∧ (Diverges (profile o) host d' ∨
          ∃ K', I K' ∧ Diverges (profile o) host K' ∧ Det.DStep o K' d') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hn ht hK d hd
  obtain ⟨b, hb, hdb⟩ := hK.unfold
  have hb' := HostCall.dstep_of_step hd hb
  obtain ⟨hs, hi⟩ := hI K ht
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
    (step?_complete (interpHead_complete_of_ty hs) rfl hi hd : (stepI o K).isSome)
  have hlb := Silmaril.Wasm.Interp.step?_lag_at (interpHead_exact_of_ty hs) _ K b x rfl rfl hi hb' hx
  have htb : I b := hstep K b ht hb'
  rcases step?_maximal_at (interpHead_exact_of_ty hs) _ K d x rfl rfl hi hd hx with _ | hdx
  · rcases step?_maximal_at (interpHead_exact_of_ty hs) _ K b _ rfl rfl hi hb' hx with _ | hbx
    · obtain ⟨d', h', hd'⟩ := hdb.unfold
      exact ⟨d', h', .inl hd'⟩
    · rcases hlb with rfl | ⟨hlt, -⟩
      · obtain ⟨d', h', hd'⟩ := hdb.unfold
        exact ⟨d', h', .inl hd'⟩
      · exact ih _ (hn ▸ hlt) b rfl htb hdb _ hbx
  · refine ⟨x, Step.of_noHost host hdx, ?_⟩
    rcases step?_maximal_at (interpHead_exact_of_ty hs) _ K b x rfl rfl hi hb' hx with _ | hbx
    · exact .inl hdb
    · exact .inr ⟨b, htb, hdb, hbx⟩

/-- **A divergent run passes through every host-free step** of a configuration in an invariant
kept by host-free steps, whose stores have closed-valid principal types and whose code meets the
cast side conditions (deterministic profile). -/
theorem diverges_through_of (hI : ∀ c, I c → StoreTy c.store ∧ DeepAll IHeadInv c.frame c.code)
    (hstep : ∀ c c', I c → Det.DStep o c c' → I c') {K d : Config H} (ht : I K)
    (hK : Diverges (profile o) host K) (hd : Det.DStep o K d) : Diverges (profile o) host d := by
  refine Silmaril.InfiniteTrace.coinduct (fun d => Diverges (profile o) host d ∨
    ∃ K', I K' ∧ Diverges (profile o) host K' ∧ Det.DStep o K' d) ?_ (.inr ⟨K, ht, hK, hd⟩)
  rintro c (hc | ⟨K, ht, hK, hd⟩)
  · obtain ⟨d', h', hd'⟩ := hc.unfold
    exact ⟨d', h', .inl hd'⟩
  · exact through_aux_of hI hstep _ K rfl ht hK c hd

end Through

end Silmaril.Proofs.Wasm.Abstract.BackInv
