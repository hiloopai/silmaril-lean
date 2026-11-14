module

public import Silmaril.Proofs.Machine.Link.FnSpec.Logic
public import Silmaril.X86.Ext.SymExec

/-!
# Proofs: the `op $imm8, %r64` triple on the open machine

`aluI8_step`: one `83 /digit ib` instruction with a 64-bit register destination (`add`,
`sub`, … but not `cmp`) as a total triple owning its code, `rip`, the register and the
flags. The run is `Silmaril.X86.Ext.stepOpt_aluI8_reg_mk` carried to the open machine through
`Ext8.stepOpt_of_ext` and `Open.step_of_ext8_stepOpt`, as the separation-logic layer carries `call`/`ret`
(`Silmaril.Proofs.Machine.X86.Sep.Call`). The small fragment lemmas (`union_none`,
`reval_union`, …) restate facts of A's `Sep.Algebra`, which its header does not export.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Link.FnSpec

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Sep.Frag (union Disjoint Le reval)

theorem union_none {a b : Frag} {l : Loc} (h : union a b l = none) : a l = none ∧ b l = none := by
  simp only [union] at h
  cases ha : a l with
  | none => rw [ha] at h; exact ⟨rfl, h⟩
  | some v => rw [ha] at h; cases h

theorem reval_union' (a b s : Frag) : reval (union a b) s = union (reval a s) (reval b s) := by
  funext l
  cases ha : a l with
  | none => simp [reval, union, ha]
  | some v =>
    simp only [reval, union, ha, Option.isSome_some, ite_true]
    cases s l <;> simp

theorem reval_disjoint' {a b : Frag} (h : Disjoint a b) (s : Frag) :
    Disjoint (reval a s) (reval b s) := by
  intro l
  rcases h l with e | e
  · exact .inl (by simp [reval, e])
  · exact .inr (by simp [reval, e])

theorem reval_eq_self {h s : Frag} (hl : Le h s) : reval h s = h := by
  funext l
  simp only [reval]
  cases e : h l with
  | none => simp
  | some v => simp [hl l v e]

theorem reval_agree {h s s' : Frag} (hl : Le h s) (hag : ∀ l, (h l).isSome → s' l = s l) :
    reval h s' = h := by
  funext l
  simp only [reval]
  cases e : h l with
  | none => simp
  | some v =>
    simp only [Option.isSome_some, ite_true]
    rw [hag l (by simp [e]), hl l v e]

theorem isSome_of_disjoint {a b : Frag} (hd : Disjoint a b) {l : Loc} (hb : (b l).isSome) :
    a l = none := by
  rcases hd l with e | e
  · exact e
  · rw [e] at hb; cases hb

theorem ripPt_reval' {v : Word} {h : Frag} (m : MState) (hp : ripPt v h) :
    ripPt m.core.rip (reval h (toFrag m)) := by
  subst hp
  funext l
  by_cases e : l = .rip
  · subst e; simp [reval, Frag.single, toFrag]
  · simp [reval, Frag.single, e]

theorem flagsAny_reval {h : Frag} (m : MState) (hp : flagsAny h) :
    flagsAny (reval h (toFrag m)) := by
  obtain ⟨f, rfl⟩ := hp
  refine ⟨m.core.flags, ?_⟩
  funext l
  by_cases e : l = .flags
  · subst e; simp [reval, Frag.single, toFrag]
  · simp [reval, Frag.single, e]

theorem ripPt_isSome {v : Word} {h : Frag} (hp : ripPt v h) : (h .rip).isSome := by
  subst hp; simp [Frag.single]

theorem regPt_isSome {r : Reg} {v : Word} {h : Frag} (hp : regPt r v h) : (h (.reg r)).isSome := by
  subst hp; simp [Frag.single]

theorem flagsAny_isSome {h : Frag} (hp : flagsAny h) : (h .flags).isSome := by
  obtain ⟨f, rfl⟩ := hp; simp [Frag.single]

theorem codePt_mem {a : Nat} {bs : List Byte} {h : Frag} {l : Loc} (hp : codePt a bs h)
    (hl : (h l).isSome) : ∃ x, l = .mem x := by
  induction bs generalizing a h with
  | nil => subst hp; simp [Frag.empty] at hl
  | cons b bs ih =>
    obtain ⟨h₁, h₂, -, rfl, ⟨-, p, -, rfl⟩, hrest⟩ := hp
    simp only [union] at hl
    by_cases e : l = .mem a
    · exact ⟨a, e⟩
    · simp only [Frag.single, e, ite_false] at hl
      exact ih hrest hl

/-- **`op $imm8, %r64`** (`op ≠ cmp`), four bytes. -/
theorem aluI8_step {pc pc' v : Word} {r : Reg} {op : Silmaril.X86.AluOp} {imm : BitVec 8}
    {bytes : List Byte}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.aluI8 .q op (.reg r) imm, 4))
    (hlen : bytes.length = 4) (hop : op ≠ .cmp) (hnext : pc + 4#64 = pc') :
    Triple (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r v ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗
        regPt r (Silmaril.X86.Ext.AluOp.resultN op v (imm.signExtend 64)) ∗ flagsAny) := by
  apply Triple.of_local
  intro m h₁ hP hl
  obtain ⟨hc, r1, hcP, hr1, hlc, hlr1, hd1, rfl⟩ := sep_le hP hl
  obtain ⟨hrip, r2, hripP, hr2, hlrip, hlr2, hd2, rfl⟩ := sep_le hr1 hlr1
  obtain ⟨hreg, hf, hregP, hfP, hlreg, hlf, hd3, rfl⟩ := sep_le hr2 hlr2
  have erip := ripPt_le hripP hlrip
  have ereg := regPt_le hregP hlreg
  have fetch := fetchBytes_of_codePt (by intro e; rw [e] at hlen; cases hlen) hcP hlc
  have loaded : Silmaril.X86.Ext.Loaded m.memory pc bytes := fetch
  have hstepE := Silmaril.X86.Ext.stepOpt_aluI8_reg_mk (exit := 0) (offset := 0) (len := 4)
    (result := Silmaril.X86.Ext.AluOp.resultN op v (imm.signExtend 64))
    loaded (by rw [erip]; simp) (by omega)
    (by rw [List.drop_zero, List.take_of_length_le (by omega)]; exact hdec) hop
    (by simp [Silmaril.X86.Ext.Sz.read, ereg])
  have hstep := Silmaril.Machine.X86.Open.step_of_ext8_stepOpt
    (Silmaril.X86.Ext8.stepOpt_of_ext hstepE)
  set m' : MState := ⟨{ m.core.write r (Silmaril.X86.Ext.AluOp.resultN op v (imm.signExtend 64)) with
    flags := Silmaril.X86.Ext.AluOp.flagsN op (Silmaril.X86.Ext.Sz.q.read m.core r)
      (imm.signExtend Silmaril.X86.Ext.Sz.q.bits),
    rip := pc + BitVec.ofNat 64 (0 + 4) }, m.memory⟩ with hm'
  have agree : ∀ l, l ≠ .rip → l ≠ .reg r → l ≠ .flags → toFrag m' l = toFrag m l := by
    intro l h1 h2 h3
    cases l with
    | reg q =>
      have hq : q ≠ r := fun e => h2 (e ▸ rfl)
      simp only [toFrag, hm']
      show some (Val.word ((m.core.write r _).read q)) = _
      rw [State.read_write_other _ _ _ _ hq]
    | rip => exact absurd rfl h1
    | flags => exact absurd rfl h3
    | mem a => rfl
    | regions => rfl
  have dom : ∀ l, union hrip (union hreg hf) l = none → l ≠ .rip ∧ l ≠ .reg r ∧ l ≠ .flags := by
    intro l hl0
    obtain ⟨n1, n23⟩ := union_none hl0
    obtain ⟨n2, n3⟩ := union_none n23
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
    · exact absurd (ripPt_isSome hripP) (by simp [n1])
    · exact absurd (regPt_isSome hregP) (by simp [n2])
    · exact absurd (flagsAny_isSome hfP) (by simp [n3])
  refine ⟨m', ⟨1, by simp [run, hstep, m']⟩, fun l hl0 => ?_, ?_⟩
  · obtain ⟨-, hrest⟩ := union_none hl0
    obtain ⟨d1, d2, d3⟩ := dom l hrest
    exact agree l d1 d2 d3
  -- the postcondition, atom by atom
  have hcode : reval hc (toFrag m') = hc := by
    refine reval_agree hlc fun l hs => ?_
    have hn := isSome_of_disjoint (fun l => (hd1 l).symm) hs
    obtain ⟨x, rfl⟩ := codePt_mem hcP hs
    rfl
  rw [reval_union', reval_union', reval_union', hcode]
  refine ⟨_, _, ?_, rfl, hcP, _, _, ?_, rfl, ?_, _, _, ?_, rfl, ?_, ?_⟩
  · rw [← hcode, ← reval_union', ← reval_union']
    exact reval_disjoint' hd1 _
  · rw [← reval_union']; exact reval_disjoint' hd2 _
  · have := ripPt_reval' m' hripP
    have e : m'.core.rip = pc' := by
      show pc + BitVec.ofNat 64 (0 + 4) = pc'
      rw [← hnext]
    rwa [e] at this
  · exact reval_disjoint' hd3 _
  · have := regPt_reval m' hregP
    have e : m'.core.read r = Silmaril.X86.Ext.AluOp.resultN op v (imm.signExtend 64) := by
      show (m.core.write r _).read r = _
      rw [State.read_write_same]
    rwa [e] at this
  · exact flagsAny_reval m' hfP

end Silmaril.Proofs.Machine.Link.FnSpec
