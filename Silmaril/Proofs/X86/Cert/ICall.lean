module

public import Silmaril.X86.Cert.ICall.Defs

/-!
# Indirect-call blocks: proofs

The proofs behind `Silmaril.X86.Cert.ICall.Thms`: a `Post` gives a callee run (`post_runs`),
one `Ext9` instruction block is sound (`insn9_sound`), the push of a return word from an aligned
stack establishes the System V entry obligations (`push_abiEntry`), and the WP of `call r/m64`
through a code environment (`callInd_wp`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Cert.ICall

open Silmaril.X86
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Loaded RM Stored readRM)
open Silmaril.X86.FnContract (RunsIn AbiEntry runsIn_mono)
open Silmaril.X86.Link.Env (Env FnPtr)
open Silmaril.X86.Cert.ICall
open Silmaril.X86.Cert.Kinds (insn9Check insn9WP)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- From `Post`: the Γ entry's callee runs from `m1` inside `R` to a state in `Q`. -/
theorem post_runs {σ : Type} {I : Isa σ} {Code : Type} {J : Env Code → Code → Req σ}
    {Γ : Env Code} (hΓ : ∀ a c, Γ a c → (J Γ c).Valid I) {T : Req σ} {R Q : σ → Prop} {m1 : σ}
    (hlv : I.live m1) (h : Post (I := I) J Γ T R Q m1) : ∃ t, RunsIn I R m1 t ∧ Q t := by
  obtain ⟨⟨c, hc, hsub⟩, hab, he, hin, hq⟩ := h
  have hv : T.Valid I := (hΓ _ c hc).sub hsub
  obtain ⟨t, hr, res⟩ := hv m1 hlv hab he
  exact ⟨t, runsIn_mono hin hr, hq t res⟩

/-- Soundness of a one-instruction block on `Open9.isa`. -/
theorem insn9_sound {code : List Byte} {base : Word} {o : Nat} {b : Ext9.Instr × Nat}
    {R : MState → Prop} {s : MState} {Q : MState → Prop} (hok : insn9Check code o b = true)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o)
    (hadm : BlockKind.Local Open9.isa base code.length R) (hwp : insn9WP b s Q) :
    ∃ t, RunsIn Open9.isa R s t ∧ Q t := by
  obtain ⟨i, l⟩ := b
  simp only [insn9Check, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hdec, hfit⟩ := hok
  obtain ⟨c, mem, hx, hq⟩ := hwp
  have hpos : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0
      simp only [List.take_zero] at hdec
      have h0 : Open9.decode [] = none := by decide
      rw [h0] at hdec
      cases hdec
    · exact h0
  have hin : R s := hadm s ⟨o, by omega, hrip⟩
  exact ⟨⟨c, mem⟩, .step hin (Open9.step_of_listed hl hrip hfit hdec hx) (.refl _), hq⟩

/-- After pushing the return address `ret` from a 16-byte-aligned stack pointer whose slot is
readable, the System V entry obligations hold and the return address is `ret`. -/
theorem push_abiEntry {c0 : State} {mem mem' : Memory} {target ret : Word}
    (hal : (c0.read .rsp).toNat % 16 = 0) (h8 : 8 ≤ (c0.read .rsp).toNat)
    (hr : mem.Permitted .read (c0.read .rsp - 8#64).toNat 8)
    (hs : Stored mem mem' (c0.read .rsp - 8#64).toNat (encodeWords [ret])) :
    let c : State := { c0.write .rsp (c0.read .rsp - 8#64) with rip := target }
    AbiEntry c mem' ∧ FnContract.retOf c mem' = ret := by
  intro c
  have hread : mem'.readBytes (c.read .rsp).toNat 8 = some (encodeWords [ret]) := by
    have := hs.readWith_self (access := .read)
      (by simpa [Silmaril.Machine.LittleEndian.encodeWords] using hr)
    simpa [c, Memory.readBytes, Silmaril.Machine.LittleEndian.encodeWords] using this
  have hret := FnContract.retOf_of_readBytes hread
  refine ⟨⟨?_, ?_⟩, hret⟩
  · have hc : c.read .rsp = c0.read .rsp - 8#64 :=
      Silmaril.X86.State.read_write_same c0 .rsp _
    rw [hc]
    have : (c0.read .rsp - 8#64).toNat = (c0.read .rsp).toNat - 8 := by bv_omega
    omega
  · rw [hret]; exact hread

/-- The WP of `call r/m64` (`FF /2`) through Γ, as a one-instruction WP into `Post`. -/
theorem callInd_wp {Code : Type} (J : Env Code → Code → Req MState) (Γ : Env Code)
    {src : RM} {l : Nat} {T : Req MState} {R Q : MState → Prop} {s : MState}
    {v : Word} (hv : readRM .q src s.core s.memory (s.core.rip + BitVec.ofNat 64 l) = some v)
    (hfp : FnPtr (logic Open9.isa) J Γ v T)
    (hal : (s.core.read .rsp).toNat % 16 = 0) (h8 : 8 ≤ (s.core.read .rsp).toNat)
    (hw : s.memory.Permitted .write (s.core.read .rsp - 8#64).toNat 8)
    (hr : s.memory.Permitted .read (s.core.read .rsp - 8#64).toNat 8)
    (hpost : ∀ mem', Stored s.memory mem' (s.core.read .rsp - 8#64).toNat
        (encodeWords [s.core.rip + BitVec.ofNat 64 l]) →
      let m1 : MState := ⟨{ s.core.write .rsp (s.core.read .rsp - 8#64) with rip := v }, mem'⟩
      FnContract.retOf m1.core m1.memory = s.core.rip + BitVec.ofNat 64 l →
      T.spec.entry m1 ∧ (∀ m, T.P m1 m → R m) ∧ ∀ t, T.spec.Result Open9.isa m1 t → Q t) :
    insn9WP (.new (.callInd src), l) s (Post (I := Open9.isa) J Γ T R Q) := by
  obtain ⟨mem', hpush, hs⟩ :=
    Silmaril.X86.Ext.pushWord_isSome (v := s.core.rip + BitVec.ofNat 64 l) hw
  obtain ⟨hab, hret⟩ := push_abiEntry (target := v) hal h8 hr hs
  obtain ⟨he, hin, hq⟩ := hpost mem' hs hret
  refine ⟨_, mem', ?_, hfp, hab, he, hin, hq⟩
  simp only [Ext9.exec, Ext9.execNew, hv, hpush]

end Silmaril.Proofs.X86.Cert.ICall
