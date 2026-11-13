module

public import Silmaril.Proofs.X86.Sep.List.Basic
public import Silmaril.X86.Sep.SysV.Thms

/-!
# Proofs: System V specs from contracts indexed by the precondition's fragment

`FnSpec.sat_of_fnContract` takes one state-level contract for every call. A loop over a
heap structure is easier to certify against a contract that names the fragment `hu` the
caller hands over (its loop invariant is an assertion on `memFrag hu mem`). `sat_of_family`
lets the contract depend on the call: on the logical arguments and on `hu`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.List

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86 (FnContract)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)

theorem sat_of_family {S : FnSpec} {C : SProp} {entry : Word}
    (hmo : ∀ x f, S.pre x f → MemOnly f)
    (h : ∀ x sp ret (m : MState) (hc ht hu : Frag), FnSpec.EntryAligned sp →
      S.stack ≤ sp.toNat → C hc → S.SysVEntry x entry sp ret ht → S.pre x hu →
      Disjoint hc (union ht hu) → Disjoint ht hu → Le (union hc (union ht hu)) (toFrag m) →
      ∃ K : FnContract.Spec MState, K.Total Silmaril.X86.Open.isa ∧ K.entry m ∧
        (∀ a, K.footprint m a → memDom hu a) ∧
        ∀ fin, K.post m fin → S.post x (fin.core.read .rax) (memFrag hu fin.memory)) :
    S.Sat Silmaril.X86.Open.isa C entry := by
  apply FnSpec.satWith_of_runs
  intro x sp ret m hc ht hu _ hA hst hcP htP huP hd1 hd2 hl
  obtain ⟨K, hK, hent, hfoot, hpost⟩ := h x sp ret m hc ht hu hA hst hcP htP huP hd1 hd2 hl
  have hlt : Le ht (toFrag m) := le_union_left (le_union_right hd1 hl)
  have ersp := FnSpec.sysVEntry_rsp htP hlt
  have eret := FnSpec.sysVEntry_ret htP hlt
  rw [← ersp] at eret
  have hretOf := FnContract.retOf_of_readBytes eret
  have habi : FnContract.AbiEntry m.core m.memory :=
    ⟨by rw [ersp]; exact hA, by rw [hretOf]; exact eret⟩
  obtain ⟨t, hrun, res⟩ := hK m trivial habi hent
  refine ⟨t, hrun, ?_, ?_, res.abi.calleeSaved, res.frame.mono fun a ha => ?_, ?_⟩
  · have := res.abi.pc
    simp only at this
    rw [this, hretOf]
  · have := res.abi.stack
    simp only at this
    rw [this, ersp]
  · exact isSome_union.mpr (.inr (hfoot a ha))
  · show S.post x _ (reval hu (toFrag t))
    rw [reval_eq_memFrag (hmo x hu huP)]
    exact hpost t res.post

end Silmaril.Proofs.X86.Sep.List
