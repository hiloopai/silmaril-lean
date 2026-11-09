module

public import Silmaril.Proofs.X86.Sep.SysV
public import Silmaril.X86.FnContract.Thms

/-!
# Proofs: System V specs and function contracts

* `sat_of_fnContract`: a `FnContract` on any segment-VC machine gives a System V spec, when
  its entry condition, footprint and postcondition are implied by the spec's;
* `total_of_sat`: on a `Flat` machine, a System V spec gives a total `FnContract` spec,
  provided the precondition's fragment owns neither the mapping list nor a callee-saved
  register.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepContract

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86 (FnContract)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.Proofs.X86.SepSysV (satWith_of_runs)

variable {σ : Type} {I : Isa σ}

theorem sysVEntry_rsp {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag} {m : MState}
    (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) : m.core.read .rsp = sp := by
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hT hl
  obtain ⟨a, _, ha, _, hla, _, -⟩ := sep_le hb hlb
  exact regPt_le ha hla

theorem sysVEntry_ret {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag} {m : MState}
    (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) :
    m.memory.readBytes sp.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [ret]) := by
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hT hl
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hb hlb
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hb hlb
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hb hlb
  obtain ⟨a, _, ha, _, hla, _, -⟩ := sep_le hb hlb
  exact readBytes_of_wordPt ha hla

theorem regsWith_le : ∀ {rs : List Reg} {vs : List Word} {h : Frag} {m : MState},
    regsWith rs vs h → Le h (toFrag m) →
      ∀ i (h₁ : i < rs.length) (h₂ : i < vs.length), m.core.read rs[i] = vs[i]
  | [], _, _, _, _, _, i, h₁, _ => absurd h₁ (Nat.not_lt_zero i)
  | _ :: _, [], _, _, _, _, i, _, h₂ => absurd h₂ (Nat.not_lt_zero i)
  | r :: rs, v :: vs, h, m, hp, hl, i, h₁, h₂ => by
    obtain ⟨a, b, ha, hb, hla, hlb, -⟩ := sep_le hp hl
    cases i with
    | zero => exact regPt_le ha hla
    | succ i => exact regsWith_le hb hlb i (by simpa using h₁) (by simpa using h₂)

theorem sysVEntry_args {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag} {m : MState}
    (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) (i : Nat)
    (h₁ : i < argRegs.length) (h₂ : i < (S.args x).length) :
    m.core.read argRegs[i] = (S.args x)[i] := by
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hT hl
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le hb hlb
  obtain ⟨a, _, ha, _, hla, _, -⟩ := sep_le hb hlb
  obtain ⟨a, _, ha, _, hla, _, -⟩ := sep_le ha hla
  exact regsWith_le ha hla i h₁ h₂

theorem sysVEntry_rip {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag} {m : MState}
    (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m)) : m.core.rip = entry := by
  obtain ⟨a, _, ha, _, hla, _, -⟩ := sep_le hT hl
  exact ripPt_le ha hla

theorem sysVPost_le {S : FnSpec} {C : SProp} {x : S.Arg} {sp ret : Word} {h : Frag}
    {m : MState} (hq : (C ∗ S.SysVPost x sp ret) h) (hl : Le h (toFrag m)) :
    ∃ v, m.core.rip = ret ∧ m.core.read .rsp = sp + 8#64 ∧ m.core.read .rax = v ∧
      Holds (S.post x v) m := by
  obtain ⟨_, p, _, hp, _, hlp, -⟩ := sep_le hq hl
  obtain ⟨v, hp⟩ := hp
  obtain ⟨e, u, he, hu, hle, hlu, -⟩ := sep_le hp hlp
  obtain ⟨a1, r1, ha1, hr1, hla1, hlr1, -⟩ := sep_le he hle
  obtain ⟨a2, r2, ha2, hr2, hla2, hlr2, -⟩ := sep_le hr1 hlr1
  obtain ⟨a3, _, ha3, _, hla3, _, -⟩ := sep_le hr2 hlr2
  obtain ⟨a4, _, ha4, _, hla4, _, -⟩ := sep_le ha3 hla3
  exact ⟨v, ripPt_le ha1 hla1, regPt_le ha2 hla2, regPt_le ha4 hla4, u, hu, hlu⟩

theorem sat_of_fnContract {S : FnSpec} {C : SProp} {entry : Word} (K : FnContract I)
    (h : ∀ x sp ret (m : σ) (hc ht hu : Frag), FnSpec.EntryAligned sp →
      S.stack ≤ sp.toNat → C hc → S.SysVEntry x entry sp ret ht → S.pre x hu →
      Disjoint hc (union ht hu) → Disjoint ht hu → Le (union hc (union ht hu)) (frag I m) →
      K.entry m ∧ (∀ a, K.footprint m a → (union ht hu (.mem a)).isSome) ∧
        ∀ fin, K.post m fin → S.post x ((I.core fin).read .rax) (reval hu (frag I fin))) :
    S.Sat I C entry := by
  apply satWith_of_runs
  intro x sp ret m hc ht hu hlive hA hst hcP htP huP hd1 hd2 hl
  obtain ⟨hent, hfoot, hpost⟩ := h x sp ret m hc ht hu hA hst hcP htP huP hd1 hd2 hl
  have hlt : Le ht (toFrag ⟨I.core m, I.mem m⟩) :=
    Silmaril.Proofs.X86.Sep.Frag.Le.trans
      (Silmaril.Proofs.X86.Sep.Frag.le_union_left ht hu)
      (Silmaril.Proofs.X86.Sep.Frag.Le.trans
        (Silmaril.Proofs.X86.Sep.Frag.le_union_right hd1) hl)
  have ersp : (I.core m).read .rsp = sp := sysVEntry_rsp htP hlt
  have eret : (I.mem m).readBytes sp.toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [ret]) := sysVEntry_ret htP hlt
  rw [← ersp] at eret
  have hretOf := FnContract.retOf_of_readBytes eret
  have habi : FnContract.AbiEntry (I.core m) (I.mem m) :=
    ⟨by rw [ersp]; exact hA, by rw [hretOf]; exact eret⟩
  obtain ⟨t, hrun, res⟩ := K.total m hlive habi hent
  refine ⟨t, hrun, ?_, ?_, res.abi.calleeSaved, res.frame.mono hfoot, hpost t res.post⟩
  · rw [res.abi.pc, hretOf]
  · rw [res.abi.stack, ersp]

theorem exit_of_post {S : FnSpec} {C : SProp} {x : S.Arg} {sp ret : Word} {h : Frag}
    {m : MState} (hq : (C ∗ S.SysVPost x sp ret) h) (hl : Le h (toFrag m)) :
    m.core.rip = ret ∧ m.core.read .rsp = sp + 8#64 := by
  obtain ⟨_, b, _, ⟨v, hb⟩, _, hlb, -⟩ := sep_le hq hl
  obtain ⟨b, _, hb, _, hlb, _, -⟩ := sep_le hb hlb
  obtain ⟨a, b, ha, hb, hla, hlb, -⟩ := sep_le hb hlb
  obtain ⟨c, _, hc, _, hlc, _, -⟩ := sep_le hb hlb
  exact ⟨ripPt_le ha hla, regPt_le hc hlc⟩

theorem total_of_sat {S : FnSpec} {C : SProp} {entry : Word} (hflat : Flat I)
    (hS : S.Sat I C entry) : (S.contractSpec I C entry).Total I := by
  intro m hlive habi ⟨x, h, hP, hl, hst, hav⟩
  obtain ⟨fin, h', hrun, hq, hl', hsame⟩ :=
    Triple.run (hS x _ _ habi.aligned hst) hlive hP hl
  obtain ⟨erip, ersp⟩ := exit_of_post (m := ⟨I.core fin, I.mem fin⟩) hq hl'
  have hreg : ∀ r ∈ sysv64.calleeSaved, (I.core fin).read r = (I.core m).read r := by
    intro r hr
    have := hsame (.reg r) (hav.2 r hr)
    simpa [frag, toFrag] using this
  refine ⟨fin, hrun, hflat m fin, ⟨erip, ersp, hreg⟩, ⟨?_, ?_⟩, ⟨x, h', hq, hl'⟩⟩
  · have := hsame .regions hav.1
    simpa [frag, toFrag] using this
  · intro a ha
    have hn : h (.mem a) = none := by
      cases e : h (.mem a) with
      | none => rfl
      | some v => exact absurd ⟨x, h, ⟨hP, hl, hst, hav⟩, by simp [e]⟩ ha
    have := hsame (.mem a) hn
    simp only [frag, toFrag, Option.some.injEq, Val.cell.injEq, Cell.mk.injEq] at this
    exact this.1

end Silmaril.Proofs.X86.SepContract
