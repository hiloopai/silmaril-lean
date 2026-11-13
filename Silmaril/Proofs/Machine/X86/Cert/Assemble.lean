module

public import Silmaril.Machine.X86.Cert.Defs
public import Silmaril.Machine.X86.FnContract.Thms

/-!
# The generic block certificate: assembly, once

`from_block`: under `Cert.VCIn R Q` and checked blocks, from every annotated block the
machine runs inside `R s0` to a state satisfying the exit condition `Q s0` (strong induction
on the block measure; the kind's `sound` runs one block). `totalIn`, `total`, `strict`: the
three readings of a function certificate.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Cert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.FnContract (RunsIn InCode AbiEntry Spec Returned runsIn_trans runsIn_live)

variable {σ : Type} {I : Isa σ} {K : BlockKind I}

theorem checked_mem {F : Cert I K} (hc : F.checked = true) {b : CBlock K} (hb : b ∈ F.blocks) :
    K.check F.code b.off b.blk = true :=
  List.all_eq_true.mp hc b hb

theorem from_block {F : Cert I K} {R Q : σ → σ → Prop} (hc : F.checked = true)
    (hvc : F.VCIn R Q) (s0 : σ) (hadm : K.Admits F.base F.code.length (R s0)) :
    ∀ (w : Nat) (b : CBlock K) (m : σ), F.measure b.off s0 m = w → b ∈ F.blocks →
      F.ann b.off s0 m → I.live m → (I.core m).rip = F.base + BitVec.ofNat 64 b.off →
      Loaded (I.mem m) F.base F.code → ∃ t, RunsIn I (R s0) m t ∧ Q s0 t := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b m hw hb ha hlv hrip hl
    obtain ⟨m', hr, hnext⟩ :=
      K.sound (checked_mem hc hb) hlv hl hrip hadm (hvc b hb s0 m ha hlv hrip hl)
    rcases hnext with hq | ⟨b', hb', hrip', hl', ha', hlt⟩
    · exact ⟨m', hr, hq⟩
    · obtain ⟨t, hr', hq⟩ :=
        ih _ (hw ▸ hlt) b' m' rfl hb' ha' (runsIn_live hr hlv) hrip' hl'
      exact ⟨t, runsIn_trans hr hr', hq⟩

theorem totalIn {F : Cert I K} (S : Spec σ) {R : σ → σ → Prop} {entry : CBlock K}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VCIn R fun s0 t => S.Result I s0 t)
    (hadm : ∀ s, I.live s → AbiEntry (I.core s) (I.mem s) → S.entry s →
      K.Admits F.base F.code.length (R s))
    (hpre : ∀ s, AbiEntry (I.core s) (I.mem s) → S.entry s →
      Loaded (I.mem s) F.base F.code ∧ (I.core s).rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    S.TotalIn I R := by
  intro s hlv hab he
  obtain ⟨hl, hrip, ha⟩ := hpre s hab he
  exact from_block hc hvc s (hadm s hlv hab he) _ entry s rfl hentry ha hlv hrip hl

/-! ## Combinators -/

namespace Combinators

open Silmaril.Machine.X86.FnContract (runsIn_mono)

/-- Soundness of a call block: the block before the callee (the `call` instruction), then the
callee's `TotalIn` run, which the WP asks to stay inside `R`. -/
theorem call_sound {code : List Byte} {base : Word} {o : Nat} {b : K.B} {C : FnContract I}
    {P : σ → σ → Prop} (hC : C.toSpec.TotalIn I P) {R : σ → Prop} {s : σ} {Q : σ → Prop}
    (hok : K.check code o b = true) (hlv : I.live s) (hl : Loaded (I.mem s) base code)
    (hrip : (I.core s).rip = base + BitVec.ofNat 64 o) (hadm : K.Admits base code.length R)
    (hwp : K.WP b R s fun m1 => AbiEntry (I.core m1) (I.mem m1) ∧ C.entry m1 ∧
      (∀ m, P m1 m → R m) ∧ ∀ t, C.Result m1 t → Q t) :
    ∃ t, RunsIn I R s t ∧ Q t := by
  obtain ⟨m1, hr, hab, he, hin, hq⟩ := K.sound hok hlv hl hrip hadm hwp
  obtain ⟨t, hr', res⟩ := hC m1 (runsIn_live hr hlv) hab he
  exact ⟨t, runsIn_trans hr (runsIn_mono hin hr'), hq t res⟩

end Combinators

end Silmaril.Proofs.Machine.X86.Cert
