module

public import Silmaril.Machine.X86.BlockCert.Ext8.Defs
import Silmaril.Machine.X86.Open.Thms

/-!
# `Ext8` block certificates are runs of the open machine

`run8_open`: a listing that `listing8` accepts at the program counter of a loaded image and
whose checked run succeeds is a run of `Open.step`, with the memory unchanged. `from_block` and
`total`: the assembly of a total System V contract, by strong induction on the block measure.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.BlockCert8

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.BlockCert8

theorem run8_open {code : List Byte} {base : Word} :
    ∀ (L : List LI) (o : Nat) (m m' : MState),
      listing8 code o L = true → Loaded m.memory base code →
      m.core.rip = base + BitVec.ofNat 64 o → run8 L m = some m' →
      Reaches Open.step m m' ∧ m'.memory = m.memory
  | [], _, m, m', _, _, _, h => by
    simp only [run8, Option.some.injEq] at h
    subst h; exact ⟨Reaches.refl _ _, rfl⟩
  | (i, l) :: rest, o, m, m', hok, hl, hrip, h => by
    simp only [listing8, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hdec, hfit⟩, hrest⟩ := hok
    simp only [run8] at h
    split at h
    · rename_i c mem hx
      split at h
      · rename_i hc
        obtain ⟨hmem, hnext⟩ := hc
        subst hmem
        have hs : Open.step m = some ⟨c, m.memory⟩ :=
          Open.step_of_listed (m := m) hl hrip hfit hdec hx
        cases rest with
        | nil =>
          simp only [run8, Option.some.injEq] at h
          subst h
          exact ⟨Silmaril.X86.SegVC.reaches_head (I := Open.isa) hs, rfl⟩
        | cons nx rest' =>
          have hrip1 : c.rip = base + BitVec.ofNat 64 (o + l) := by
            rcases hnext with h0 | h1
            · cases h0
            · rw [h1, hrip, BitVec.ofNat_add, BitVec.add_assoc]
          obtain ⟨hr, hm⟩ := run8_open (nx :: rest') (o + l) ⟨c, m.memory⟩ m' hrest hl hrip1 h
          exact ⟨Silmaril.X86.SegVC.reaches_cons (I := Open.isa) hs hr, hm⟩
      · cases h
    · cases h

theorem checked_mem {F : Cert} (hc : F.checked = true) {b : Blk} (hb : b ∈ F.blocks) :
    listing8 F.code b.off b.instrs = true :=
  List.all_eq_true.mp hc b hb

theorem from_block {F : Cert} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) (m0 : MState) :
    ∀ (w : Nat) (b : Blk) (m : MState), F.measure b.off m0 m = w → b ∈ F.blocks →
      F.ann b.off m0 m → m.core.rip = F.base + BitVec.ofNat 64 b.off →
      Loaded m.memory F.base F.code → ∃ t, Reaches Open.step m t ∧ Q m0 t := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b m hw hb ha hrip hl
    obtain ⟨m', hrun, hnext⟩ := hvc b hb m0 m ha hrip hl
    obtain ⟨hr, hmem⟩ := run8_open _ _ _ _ (checked_mem hc hb) hl hrip hrun
    rcases hnext with hq | ⟨b', hb', hrip', ha', hlt⟩
    · exact ⟨m', hr, hq⟩
    · have hl' : Loaded m'.memory F.base F.code := by rw [hmem]; exact hl
      obtain ⟨t, hr', hq⟩ := ih _ (hw ▸ hlt) b' m' rfl hb' ha' hrip' hl'
      exact ⟨t, hr.trans hr', hq⟩

theorem total {F : Cert} (S : FnContract.Spec MState) {entry : Blk} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa := by
  intro m _ hab he
  obtain ⟨hl, hrip, ha⟩ := hpre m hab he
  exact from_block hc hvc m _ entry m rfl hentry ha hrip hl

end Silmaril.Proofs.Machine.X86.BlockCert8
