module

public import Silmaril.Proofs.X86.Safe.Stable
public import Silmaril.Proofs.X86.Safe.Stable.RightRotRun

/-!
# Proofs: `right_rot` as a stable triple on the open machine

Non-vacuity for `TripleS`: the `clang -O0` leaf `right_rot`
(`Silmaril.X86.Decompile.RightRot`, 15 instructions, 37 bytes) meets a stable triple on
`Open.step`. The precondition owns the code, `rip`, `rsp`, **`rbp`**, the two argument
registers, the three registers the body writes (`rax`, `rcx`, `rdx`), the flags, the sixteen
frame bytes below `rsp` and the return slot. Every other location may be in the frame `F`,
and `strue ∗ F` holds at each of the fifteen intermediate states (`run_stable`).

`rbp` must be owned: the function overwrites it with the post-push `rsp` and restores it only
at the `pop`. With `rbp` in the frame (as in the System V template `FnSpec.SysVPre`, where
callee-saved registers are the caller's), the triple holds but is not stable.

The arithmetic side conditions of the decompilation certificate (the frame does not wrap and
does not overlap the code, `0 < count < 32`) are hypotheses of `rightRot_tripleS`.
-/

@[expose] public section

namespace Silmaril.X86.Safe.RightRot

open Silmaril.X86 (MState Word Reg)
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86.Decompile.RightRot (code rightRotSpec)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)

/-- `rax` holds a value whose low 32 bits are `v`. -/
def raxLow32 (v : BitVec 32) : SProp := fun h => ∃ w : Word, w.setWidth 32 = v ∧ regPt .rax w h

/-- **The precondition**: `right_rot` at `e`, called with return address `ret` at `[sp]`,
`rbp = bp`, `rdi = vdi`, `rsi = vsi`. -/
def pre (e ret sp bp vdi vsi : Word) : SProp :=
  codePt e.toNat code ∗ ripPt e ∗ regPt .rsp sp ∗ regPt .rbp bp ∗ regPt .rdi vdi ∗
    regPt .rsi vsi ∗ regAny .rax ∗ regAny .rcx ∗ regAny .rdx ∗ flagsAny ∗
    blockAny (sp.toNat - 16) 16 ∗ wordPt sp.toNat ret

/-- **The postcondition**: returned to `ret` with `rsp` popped, `rbp` and the arguments
unchanged, and `eax` the decompiled function of `edi` and `esi`. -/
def post (e ret sp bp vdi vsi : Word) : SProp :=
  codePt e.toNat code ∗ ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ regPt .rbp bp ∗ regPt .rdi vdi ∗
    regPt .rsi vsi ∗ raxLow32 (rightRotSpec (vdi.setWidth 32) (vsi.setWidth 32).toNat) ∗
    regAny .rcx ∗ regAny .rdx ∗ flagsAny ∗ blockAny (sp.toNat - 16) 16 ∗ wordPt sp.toNat ret

/-! ## Fragment lemmas -/

theorem union_isSome_left {a b : Frag} {l : Loc} (h : (a l).isSome) : (union a b l).isSome := by
  cases e : a l with
  | none => rw [e] at h; cases h
  | some v => simp [union, e]

theorem union_isSome_right {a b : Frag} {l : Loc} (h : (b l).isSome) :
    (union a b l).isSome := by
  cases e : a l with
  | none => simp [union, e, h]
  | some v => simp [union, e]

theorem reval_union (a b s : Frag) : reval (union a b) s = union (reval a s) (reval b s) := by
  funext l
  cases e : a l <;> cases e' : b l <;> simp [reval, union, e, e'] <;> cases s l <;> rfl

theorem reval_disjoint {a b : Frag} (hd : Disjoint a b) (s : Frag) :
    Disjoint (reval a s) (reval b s) := by
  intro l
  rcases hd l with e | e
  · left; simp [reval, e]
  · right; simp [reval, e]

theorem single_isSome (l : Loc) (v : Val) : (Frag.single l v l).isSome := by
  simp [Frag.single]

theorem ripPt_reval' {v : Word} {h : Frag} (m : MState) (hp : ripPt v h) :
    ripPt m.core.rip (reval h (toFrag m)) := by
  subst hp
  funext l
  cases l <;> simp [reval, Frag.single, toFrag]

theorem flagsAny_reval {h : Frag} (m : MState) (hp : flagsAny h) :
    flagsAny (reval h (toFrag m)) := by
  obtain ⟨f, hf⟩ := hp
  refine ⟨m.core.flags, ?_⟩
  subst hf
  funext l
  cases l <;> simp [reval, Frag.single, toFrag]

theorem regAny_reval {r : Reg} {h : Frag} (m : MState) (hp : regAny r h) :
    regAny r (reval h (toFrag m)) := by
  obtain ⟨v, hv⟩ := hp
  exact ⟨_, regPt_reval m hv⟩

theorem permsAt_eq {a b : Silmaril.Process.Memory} (hr : b.regions = a.regions) (x : Nat) :
    permsAt b x = permsAt a x := by
  simp [permsAt, Silmaril.Process.Memory.permits, hr]

/-! ## The leaf -/

open Silmaril.Proofs.X86.SafeStable.RightRot (Within run_stable)

/-- The footprint of a state of the run, in fragment terms: if the fragment owns `rsp`,
`rbp`, `rax`, `rcx`, `rdx`, `rip`, the flags and the frame bytes, the state agrees with the
entry state outside it. -/
theorem unchanged_of_within {m mk : MState} {h : Frag} (hW : Within m mk)
    (hrsp : (h (.reg .rsp)).isSome) (hrbp : (h (.reg .rbp)).isSome)
    (hrax : (h (.reg .rax)).isSome) (hrcx : (h (.reg .rcx)).isSome)
    (hrdx : (h (.reg .rdx)).isSome) (hrip : (h .rip).isSome) (hfl : (h .flags).isSome)
    (hfr : ∀ i < 16, (h (.mem ((m.core.read .rsp).toNat - 16 + i))).isSome) :
    Safe.Unchanged h m mk := by
  intro l hl
  cases l with
  | reg r =>
    by_cases e1 : r = .rsp
    · subst e1; rw [hl] at hrsp; cases hrsp
    by_cases e2 : r = .rbp
    · subst e2; rw [hl] at hrbp; cases hrbp
    by_cases e3 : r = .rax
    · subst e3; rw [hl] at hrax; cases hrax
    by_cases e4 : r = .rcx
    · subst e4; rw [hl] at hrcx; cases hrcx
    by_cases e5 : r = .rdx
    · subst e5; rw [hl] at hrdx; cases hrdx
    simp [toFrag, hW.1 r e1 e2 e3 e4 e5]
  | rip => rw [hl] at hrip; cases hrip
  | flags => rw [hl] at hfl; cases hfl
  | mem a =>
    have hout : a < (m.core.read .rsp).toNat - 16 ∨
        (m.core.read .rsp).toNat - 16 + 16 ≤ a := by
      by_contra hc
      have := hfr (a - ((m.core.read .rsp).toNat - 16)) (by omega)
      rw [show (m.core.read .rsp).toNat - 16 + (a - ((m.core.read .rsp).toNat - 16)) = a by
        omega, hl] at this
      cases this
    simp only [toFrag, hW.2.2 a hout, permsAt_eq hW.2.1]
  | regions => simp [toFrag, hW.2.1]

theorem sep_reval_split {P Q : SProp} {a b s : Frag} (hd : Disjoint a b) (hp : P (reval a s))
    (hq : Q (reval b s)) : (P ∗ Q) (reval (union a b) s) :=
  ⟨_, _, reval_disjoint hd s, reval_union a b s, hp, hq⟩

set_option maxHeartbeats 1000000 in
/-- **`right_rot` as a stable triple on the open machine.** -/
theorem rightRot_tripleS (e ret sp bp vdi vsi : Word) (hsp : 16 ≤ sp.toNat)
    (hapart : e.toNat + 37 ≤ sp.toNat - 16 ∨ sp.toNat ≤ e.toNat)
    (hpos : 0 < (vsi.setWidth 32).toNat) (hlt : (vsi.setWidth 32).toNat < 32) :
    Safe.TripleS Silmaril.X86.Open.step (pre e ret sp bp vdi vsi)
      (post e ret sp bp vdi vsi) := by
  apply Safe.TripleS.of_local
  intro m h₁ hP hl
  obtain ⟨h0, r0, hc, r0P, hl0, hlr0, hd0, rfl⟩ := sep_le hP hl
  obtain ⟨h1, r1, hrip, r1P, hl1, hlr1, hd1, rfl⟩ := sep_le r0P hlr0
  obtain ⟨h2, r2, hrsp, r2P, hl2, hlr2, hd2, rfl⟩ := sep_le r1P hlr1
  obtain ⟨h3, r3, hrbp, r3P, hl3, hlr3, hd3, rfl⟩ := sep_le r2P hlr2
  obtain ⟨h4, r4, hrdi, r4P, hl4, hlr4, hd4, rfl⟩ := sep_le r3P hlr3
  obtain ⟨h5, r5, hrsi, r5P, hl5, hlr5, hd5, rfl⟩ := sep_le r4P hlr4
  obtain ⟨h6, r6, hrax, r6P, -, hlr6, hd6, rfl⟩ := sep_le r5P hlr5
  obtain ⟨h7, r7, hrcx, r7P, -, hlr7, hd7, rfl⟩ := sep_le r6P hlr6
  obtain ⟨h8, r8, hrdx, r8P, -, hlr8, hd8, rfl⟩ := sep_le r7P hlr7
  obtain ⟨h9, r9, hfl, r9P, -, hlr9, hd9, rfl⟩ := sep_le r8P hlr8
  obtain ⟨h10, h11, hblk, hword, hl10, hl11, hd10, rfl⟩ := sep_le r9P hlr9
  -- The entry state.
  have erip : m.core.rip = e := ripPt_le hrip hl1
  have ersp : m.core.read .rsp = sp := regPt_le hrsp hl2
  have erbp : m.core.read .rbp = bp := regPt_le hrbp hl3
  have erdi : m.core.read .rdi = vdi := regPt_le hrdi hl4
  have ersi : m.core.read .rsi = vsi := regPt_le hrsi hl5
  have hcl : code.length = 37 := by decide
  have hentry : Silmaril.X86.Decompile.RightRot.Entry e ret m :=
    { rip := erip
      image := fetchBytes_of_codePt (by decide) hc hl0
      ret := by rw [ersp]; exact readBytes_of_wordPt hword hl11
      frameWrite := by rw [ersp]; exact permitted_of_blockAny (.inr rfl) (by decide) hblk hl10
      frameRead := by rw [ersp]; exact permitted_of_blockAny (.inl rfl) (by decide) hblk hl10
      spLow := by rw [ersp]; exact hsp
      apart := by rw [ersp]; exact hapart
      countPos := by simp only [Silmaril.X86.Ext.Sz.read, ersi]; exact hpos
      countLt := by simp only [Silmaril.X86.Ext.Sz.read, ersi]; exact hlt }
  obtain ⟨fin, hrun, hfrip, hpost, hW⟩ := run_stable hentry
  have hWf : Within m fin := hW 15 (Nat.le_refl _) fin hrun
  have hwo := hpost.2.2.2
  -- The precondition's fragment owns everything the run writes.
  have dsome : ∀ {l : Loc} {v : Val} {h : Frag}, h = Frag.single l v → (h l).isSome := by
    intro l v h e; subst e; exact single_isSome l v
  obtain ⟨v6, hv6⟩ := hrax
  obtain ⟨v7, hv7⟩ := hrcx
  obtain ⟨v8, hv8⟩ := hrdx
  obtain ⟨f9, hf9⟩ := hfl
  have hU : ∀ mk, Within m mk → Safe.Unchanged (union h0 (union h1 (union h2 (union h3
      (union h4 (union h5 (union h6 (union h7 (union h8 (union h9 (union h10 h11))))))))))) m mk :=
    fun mk hw => unchanged_of_within hw
      (union_isSome_right (union_isSome_right (union_isSome_left (dsome hrsp))))
      (union_isSome_right (union_isSome_right (union_isSome_right
        (union_isSome_left (dsome hrbp)))))
      (union_isSome_right (union_isSome_right (union_isSome_right (union_isSome_right
        (union_isSome_right (union_isSome_right (union_isSome_left (dsome hv6))))))))
      (union_isSome_right (union_isSome_right (union_isSome_right (union_isSome_right
        (union_isSome_right (union_isSome_right (union_isSome_right
          (union_isSome_left (dsome hv7)))))))))
      (union_isSome_right (union_isSome_right (union_isSome_right (union_isSome_right
        (union_isSome_right (union_isSome_right (union_isSome_right (union_isSome_right
          (union_isSome_left (dsome hv8))))))))))
      (union_isSome_right (union_isSome_left (dsome hrip)))
      (union_isSome_right (union_isSome_right (union_isSome_right (union_isSome_right
        (union_isSome_right (union_isSome_right (union_isSome_right (union_isSome_right
          (union_isSome_right (union_isSome_left (dsome hf9)))))))))))
      (fun i hi => by
        rw [ersp]
        exact union_isSome_right (union_isSome_right (union_isSome_right (union_isSome_right
          (union_isSome_right (union_isSome_right (union_isSome_right (union_isSome_right
            (union_isSome_right (union_isSome_right
              (union_isSome_left (blockAny_dom hblk i hi))))))))))))
  refine ⟨15, fin, hrun, hU fin hWf, ?_, fun k hk mk hrk => hU mk (hW k (by omega) mk hrk)⟩
  -- The postcondition on the re-valued fragment, atom by atom.
  have hperm := permsAt_eq hwo.1
  refine sep_reval_split hd0 ?_ (sep_reval_split hd1 ?_ (sep_reval_split hd2 ?_
    (sep_reval_split hd3 ?_ (sep_reval_split hd4 ?_ (sep_reval_split hd5 ?_
    (sep_reval_split hd6 ?_ (sep_reval_split hd7 ?_ (sep_reval_split hd8 ?_
    (sep_reval_split hd9 ?_ (sep_reval_split hd10 ?_ ?_))))))))))
  · -- code
    refine bytesAt_reval hc rfl fun i hi => ?_
    have hm := bytesAt_le hc hl0 i hi
    have hout : e.toNat + i < (m.core.read .rsp).toNat - 16 ∨
        (m.core.read .rsp).toNat - 16 + 16 ≤ e.toNat + i := by
      rw [ersp]; rw [hcl] at hi; omega
    exact ⟨by rw [hwo.2 _ hout]; exact hm.2.1, by rw [hperm]; exact hm.2.2⟩
  · -- rip
    exact hfrip ▸ ripPt_reval' fin hrip
  · -- rsp
    have := regPt_reval fin hrsp
    rwa [hpost.2.1, ersp] at this
  · -- rbp
    have := regPt_reval fin hrbp
    rwa [hpost.2.2.1 .rbp ((Silmaril.X86.sysv64_mem_calleeSaved _).mpr (.inr (.inl rfl))),
      erbp] at this
  · -- rdi
    have := regPt_reval fin hrdi
    rwa [hWf.1 .rdi (by decide) (by decide) (by decide) (by decide) (by decide), erdi] at this
  · -- rsi
    have := regPt_reval fin hrsi
    rwa [hWf.1 .rsi (by decide) (by decide) (by decide) (by decide) (by decide), ersi] at this
  · -- rax
    refine ⟨fin.core.read .rax, ?_, regPt_reval fin hv6⟩
    have h1 := hpost.1
    simp only [Silmaril.X86.Decompile.RightRot.args, Silmaril.X86.Ext.Sz.read, erdi,
      ersi] at h1
    exact h1
  · exact regAny_reval fin ⟨v7, hv7⟩
  · exact regAny_reval fin ⟨v8, hv8⟩
  · exact flagsAny_reval fin ⟨f9, hf9⟩
  · exact blockAny_reval hblk fun i hi => by rw [hperm]; exact (blockAny_le hblk hl10 i hi).2
  · -- the return slot
    refine bytesAt_reval (need := RW) hword rfl fun i hi => ?_
    have hm := bytesAt_le (need := RW) hword hl11 i hi
    have h8 : i < 8 := by simpa using hi
    have hout : sp.toNat + i < (m.core.read .rsp).toNat - 16 ∨
        (m.core.read .rsp).toNat - 16 + 16 ≤ sp.toNat + i := by
      rw [ersp]; omega
    exact ⟨by rw [hwo.2 _ hout]; exact hm.2.1, by rw [hperm]; exact hm.2.2⟩

end Silmaril.X86.Safe.RightRot
