module

public import Silmaril.X86.BlockCert.Defs
public import Silmaril.Proofs.X86.BlockCert.Bridge
public import Silmaril.X86.Open.Thms

/-!
# Assembling a function contract from block certificates

`from_block`: under `FunCert.VC Q` and checked listings, from every annotated block the open
machine reaches a state satisfying the exit condition `Q` (strong induction on the block
measure). `total`: with `Q` the contract's result and an entry block whose annotation the
contract's precondition implies, the spec is totally correct on the open machine.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86
open Silmaril.X86.BlockCert

theorem checked_mem {F : FunCert} (hc : F.checked = true) {b : Blk} (hb : b ∈ F.blocks) :
    listingAt F.code b.off b.instrs = true :=
  List.all_eq_true.mp hc b hb

theorem from_block {F : FunCert} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) (m0 : MState) :
    ∀ (w : Nat) (b : Blk) (m : MState), F.measure b.off m0 m = w → b ∈ F.blocks →
      F.ann b.off m0 m → m.core.rip = F.base + BitVec.ofNat 64 b.off →
      Loaded m.memory F.base F.code → ∃ t, Reaches Open.step m t ∧ Q m0 t := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b m hw hb ha hrip hl
    obtain ⟨m', hrun, hnext⟩ := hvc b hb m0 m ha hrip hl
    obtain ⟨hr, hmem⟩ := runL_open (checked_mem hc hb) hl hrip hrun
    rcases hnext with hq | ⟨b', hb', hrip', ha', hlt⟩
    · exact ⟨m', hr, hq⟩
    · have hl' : Loaded m'.memory F.base F.code := by rw [hmem]; exact hl
      obtain ⟨t, hr', hq⟩ := ih _ (hw ▸ hlt) b' m' rfl hb' ha' hrip' hl'
      exact ⟨t, hr.trans hr', hq⟩

theorem total {F : FunCert} (S : FnContract.Spec MState) {entry : Blk} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa := by
  intro m _ hab he
  obtain ⟨hl, hrip, ha⟩ := hpre m hab he
  exact from_block hc hvc m _ entry m rfl hentry ha hrip hl

end Silmaril.Proofs.X86.BlockCert
