module

public import Silmaril.X86.Sep.Ind.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Safe.Thms
public import Silmaril.Proofs.X86.Sep.Bridge
public import Silmaril.Proofs.X86.Sep.Call

/-!
# Proofs: indirect `call`/`jmp` step laws on `Open9`

* Decoding: every encoder of `Sep/Ind/Defs.lean` decodes through `Open9.decode` to the
  `Ext9` form `callInd`/`jmpInd` with the expected operand (`decode_encCallR`, …), by `rfl`
  after a case split on the register (the displacement stays symbolic).
* `progress_of_local`: a one-step `Progress` from a local step, on any machine;
  `progress_of_local_mstate` on a machine over `MState` (`Open9.isa`).
* `callInd_progress`, `jmpInd_progress`: the step laws for any operand `op` and any assertion
  `X` that pins the value read at `op`; `callR_open9`, `callM_open9`, `jmpR_open9` and
  `jmpM_open9` are their instances with `X := regPt r p` and
  `X := regPt base v ∗ wordAt need (ea v d).toNat p`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.Ind

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (RM Mem readRM)
open Silmaril.Process (Memory Permissions)
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Ind
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Safe (Progress)
open Silmaril.Proofs.X86.Sep (toFrag_agree none_of_disjoint ne_of_isSome_none
  toNat_sub_eight)

/-! ## Decoding -/

theorem decode_encCallR (r : Reg) :
    Open9.decode (encCallR r) = some (.new (.callInd (.reg r)), (encCallR r).length) := by
  cases r <;> with_unfolding_all rfl

theorem decode_encJmpR (r : Reg) :
    Open9.decode (encJmpR r) = some (.new (.jmpInd (.reg r)), (encJmpR r).length) := by
  cases r <;> with_unfolding_all rfl

theorem decode_encCallM (base : Reg) (d : BitVec 8) :
    Open9.decode (encCallM base d) =
      some (.new (.callInd (memOp base d)), (encCallM base d).length) := by
  revert d; cases base <;> decide +kernel

theorem decode_encJmpM (base : Reg) (d : BitVec 8) :
    Open9.decode (encJmpM base d) =
      some (.new (.jmpInd (memOp base d)), (encJmpM base d).length) := by
  revert d; cases base <;> decide +kernel

theorem encR_ne_nil (digit : Nat) (r : Reg) : encR digit r ≠ [] := by
  simp [encR]

theorem encM_ne_nil (digit : Nat) (base : Reg) (d : BitVec 8) : encM digit base d ≠ [] := by
  simp [encM]

/-! ## Reading the operand -/

theorem signExtend_8_32_64 (d : BitVec 8) :
    (d.signExtend 32).signExtend 64 = d.signExtend 64 := by
  revert d; decide

set_option maxRecDepth 8000 in
theorem leBytes_eight (v : Word) : Silmaril.X86.Ext.leBytes v 8 = encodeWords [v] := by
  rw [Silmaril.X86.encodeWords_singleton]
  simp [Silmaril.X86.Ext.leBytes, List.ofFn_succ]

theorem readRM_reg {r : Reg} {p : Word} {h : Frag} {m : MState} (hp : regPt r p h)
    (hl : Le h (toFrag m)) (next : Word) :
    readRM .q (.reg r) m.core m.memory next = some p := by
  have e := regPt_le hp hl
  simp only [readRM]
  rw [← e]
  simp [Silmaril.X86.Ext.Sz.read]

theorem readRM_memOp {need : Permissions → Prop} (hneed : ∀ q, need q → RO q)
    {base : Reg} {d : BitVec 8} {v p : Word} {h : Frag} {m : MState}
    (hp : (regPt base v ∗ wordAt need (ea v d).toNat p) h) (hl : Le h (toFrag m))
    (next : Word) : readRM .q (memOp base d) m.core m.memory next = some p := by
  obtain ⟨hr, hw, hrP, hwP, hlr, hlw, -, -⟩ := sep_le hp hl
  have ev := regPt_le hrP hlr
  have hread : m.memory.readBytes (ea v d).toNat 8 = some (encodeWords [p]) := by
    have := Silmaril.Proofs.X86.Sep.readWith_of_bytesAt (access := .read)
      (fun q hq => by
        have : q.read = true := hneed q hq
        simpa [Silmaril.Process.Permissions.allows] using this)
      (by simp [encodeWords]) hwP hlw
    simpa [Memory.readBytes] using this
  have haddr : (Mem.ofReg base none (d.signExtend 32)).addr m.core next = ea v d := by
    simp [Mem.addr, Mem.ofReg, Silmaril.X86.Ext.Base.value, ev, ea, signExtend_8_32_64]
  have hload : Silmaril.X86.Ext.loadN m.memory (ea v d) 8 = some p := by
    apply Silmaril.X86.Ext.loadN_of_holdsLE_eight
    rw [Silmaril.X86.Ext.HoldsLE, leBytes_eight]
    exact hread
  have hq : Silmaril.X86.Ext.Sz.q.bytes = 8 := rfl
  simp only [readRM, memOp, haddr, hq, hload, Option.map_some]
  simp

/-! ## One step as a `Progress` -/

/-- A local step: the machine takes one step from every live state containing `P`'s fragment,
keeps every location outside it, and re-valued the fragment satisfies `Q`. -/
theorem progress_of_local {σ : Type} {I : Isa σ} {P Q : SProp}
    (h : ∀ m h₁, I.live m → P h₁ → Le h₁ (frag I m) →
      ∃ m', I.step m = some m' ∧ (∀ l, h₁ l = none → frag I m' l = frag I m l) ∧
        Q (reval h₁ (frag I m'))) :
    Progress I P Q := by
  intro F m hlive ⟨h₁, h₂, hd, he, hp, hf⟩
  have hl : Le h₁ (frag I m) := by rw [he]; exact Frag.le_union_left h₁ h₂
  obtain ⟨m', hs, hsame, hq⟩ := h m h₁ hlive hp hl
  refine ⟨0, m', by simp [run, hs], reval h₁ (frag I m'), h₂, ?_, ?_, hq, hf⟩
  · intro l
    rcases hd l with e | e
    · left; simp [reval, e]
    · right; exact e
  · funext l
    cases e : h₁ l with
    | none =>
      rw [hsame l e, he, Frag.union_of_none e, Frag.union_of_none]
      simp [reval, e]
    | some v =>
      rw [Frag.union_of_some (v := (frag I m' l).get (Silmaril.X86.Sep.frag_isSome m' l))]
      · simp
      · simp [reval, e]

/-- `progress_of_local` on a machine over `MState` whose core and memory are the state's. -/
theorem progress_of_local_mstate {I : Isa MState} {P Q : SProp} (hc : ∀ m, I.core m = m.core)
    (hm : ∀ m, I.mem m = m.memory)
    (h : ∀ m h₁, P h₁ → Le h₁ (toFrag m) →
      ∃ m', I.step m = some m' ∧ (∀ l, h₁ l = none → toFrag m' l = toFrag m l) ∧
        Q (reval h₁ (toFrag m'))) :
    Progress I P Q := by
  apply progress_of_local
  intro m h₁ _ hp hl
  simp only [frag_eq_toFrag hc hm] at hl ⊢
  exact h m h₁ hp hl

/-! ## The generic laws -/

/-- **`call r/m64`** on `Open9`, for any operand `op` whose value is pinned to `p` by `X`. -/
theorem callInd_progress {X : SProp} {bs : List Byte} {op : RM} {pc s p : Word}
    (hs : 8 ≤ s.toNat) (hne : bs ≠ [])
    (hdec : Open9.decode bs = some (.new (.callInd op), bs.length))
    (hread : ∀ (m : MState) hx, X hx → Le hx (toFrag m) → ∀ next,
      readRM .q op m.core m.memory next = some p) :
    Progress Open9.isa
      (codePt pc.toNat bs ∗ ripPt pc ∗ X ∗ regPt .rsp s ∗ blockAny (s.toNat - 8) 8)
      (codePt pc.toNat bs ∗ ripPt p ∗ X ∗ regPt .rsp (s - 8#64) ∗
        wordPt (s.toNat - 8) (nextPc pc bs)) := by
  apply progress_of_local_mstate (fun _ => rfl) (fun _ => rfl)
  intro m h₁ hP hl
  obtain ⟨hc, r1, hcP, hr1, hlc, hlr1, hd1, rfl⟩ := sep_le hP hl
  obtain ⟨hrip, r2, hripP, hr2, hlrip, hlr2, hd2, rfl⟩ := sep_le hr1 hlr1
  obtain ⟨hx, r3, hxP, hr3, hlx, hlr3, hd3, rfl⟩ := sep_le hr2 hlr2
  obtain ⟨hsp, hb, hspP, hbP, hlsp, hlb, hd4, rfl⟩ := sep_le hr3 hlr3
  have erip := ripPt_le hripP hlrip
  have ersp := regPt_le hspP hlsp
  have fetch := fetchBytes_of_codePt hne hcP hlc
  have perm := permitted_of_blockAny (.inr rfl) (by omega) hbP hlb
  have hsub := toNat_sub_eight hs
  have hperm : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8 := by
    rw [ersp, hsub]; exact perm
  obtain ⟨core1, mem1, hpush⟩ : ∃ c mm, Silmaril.X86.pushWord m.core m.memory
      (m.core.rip + BitVec.ofNat 64 bs.length) = some (c, mm) :=
    ⟨_, _, Silmaril.X86.pushWord_eq_some hperm⟩
  have hexec : Ext9.execNew (.callInd op) m.core m.memory
      (m.core.rip + BitVec.ofNat 64 bs.length) = .ok { core1 with rip := p } mem1 := by
    simp only [Ext9.execNew, hread m hx hxP hlx, hpush]
  have hstep := Open9.step_of_fetch_new (by rw [erip]; exact fetch) hdec hexec
  have hcore1 := Silmaril.X86.pushWord_state hpush
  have hwo := Silmaril.X86.pushWord_writesOnly hpush
  have hget := Silmaril.X86.pushWord_get hpush
  rw [ersp, hsub] at hwo hget
  set m' : MState := ⟨{ core1 with rip := p }, mem1⟩ with hm'
  have hregions : m'.memory.regions = m.memory.regions := hwo.1
  have hperms : ∀ a, permsAt m'.memory a = permsAt m.memory a := by
    intro a; simp [permsAt, Memory.permits, hregions]
  -- every location outside `rip`, `rsp` and the pushed bytes is unchanged
  have unchanged : ∀ l, hrip l = none → hsp l = none → hb l = none →
      toFrag m' l = toFrag m l := by
    intro l e1 e2 e3
    refine toFrag_agree (m := m) (m' := m')
      (W := fun a => s.toNat - 8 ≤ a ∧ a < s.toNat - 8 + 8)
      (fun r hr => ?_) ?_ hregions (fun a ha => hwo.2 a (by omega)) ?_ ?_ ?_
    · show core1.read r = _
      rw [hcore1]
      exact State.read_write_other _ _ _ _ hr
    · show core1.flags = _
      rw [hcore1]; rfl
    · exact ne_of_isSome_none e1 (ripPt_dom hripP)
    · exact ne_of_isSome_none e2 (regPt_dom hspP)
    · rintro a rfl ⟨h1, h2⟩
      have := blockAny_dom hbP (a - (s.toNat - 8)) (by omega)
      rw [show s.toNat - 8 + (a - (s.toNat - 8)) = a by omega] at this
      exact ne_of_isSome_none e3 this rfl
  refine ⟨m', hstep, fun l hl0 => ?_, ?_⟩
  · simp only [Frag.union_eq_none] at hl0
    exact unchanged l hl0.2.1 hl0.2.2.2.1 hl0.2.2.2.2
  have d1 := Frag.reval_disjoint hd1 (toFrag m')
  have d2 := Frag.reval_disjoint hd2 (toFrag m')
  have d3 := Frag.reval_disjoint hd3 (toFrag m')
  have d4 := Frag.reval_disjoint hd4 (toFrag m')
  rw [Frag.reval_union] at d1 d2 d3 ⊢
  rw [Frag.reval_union] at d1 d2 ⊢
  rw [Frag.reval_union] at d1 ⊢
  rw [Frag.reval_union]
  refine ⟨_, _, d1, rfl, ?_, _, _, d2, rfl, ?_, _, _, d3, rfl, ?_, _, _, d4, rfl, ?_, ?_⟩
  · -- the code
    rw [Frag.reval_eq_of_agree hlc (fun l hl' => by
      have e := none_of_disjoint hd1 hl'
      simp only [Frag.union_eq_none] at e
      exact unchanged l e.1 e.2.2.1 e.2.2.2)]
    exact hcP
  · exact ripPt_reval m' hripP
  · -- the operand's frame `X`
    rw [Frag.reval_eq_of_agree hlx (fun l hl' => by
      have e1 := none_of_disjoint (Frag.Disjoint.symm hd2)
        (Frag.isSome_union.mpr (.inl hl'))
      have e := none_of_disjoint hd3 hl'
      simp only [Frag.union_eq_none] at e
      exact unchanged l e1 e.1 e.2)]
    exact hxP
  · have := regPt_reval m' hspP
    have e : m'.core.read .rsp = s - 8#64 := by
      show core1.read .rsp = _
      rw [hcore1, State.read_write_same, ersp]
    rwa [e] at this
  · refine blockAny_reval_bytes hbP (by simp) (fun i hi => ⟨?_, ?_⟩)
    · have := hget i (by simpa using hi)
      rw [this, erip]; rfl
    · rw [hperms]
      exact (blockAny_le hbP hlb i (by simpa using hi)).2

/-- **`jmp r/m64`** on `Open9`, for any operand `op` whose value is pinned to `p` by `X`. -/
theorem jmpInd_progress {X : SProp} {bs : List Byte} {op : RM} {pc p : Word}
    (hne : bs ≠ [])
    (hdec : Open9.decode bs = some (.new (.jmpInd op), bs.length))
    (hread : ∀ (m : MState) hx, X hx → Le hx (toFrag m) → ∀ next,
      readRM .q op m.core m.memory next = some p) :
    Progress Open9.isa (codePt pc.toNat bs ∗ ripPt pc ∗ X)
      (codePt pc.toNat bs ∗ ripPt p ∗ X) := by
  apply progress_of_local_mstate (fun _ => rfl) (fun _ => rfl)
  intro m h₁ hP hl
  obtain ⟨hc, r1, hcP, hr1, hlc, hlr1, hd1, rfl⟩ := sep_le hP hl
  obtain ⟨hrip, hx, hripP, hxP, hlrip, hlx, hd2, rfl⟩ := sep_le hr1 hlr1
  have erip := ripPt_le hripP hlrip
  have fetch := fetchBytes_of_codePt hne hcP hlc
  have hexec : Ext9.execNew (.jmpInd op) m.core m.memory
      (m.core.rip + BitVec.ofNat 64 bs.length) = .ok { m.core with rip := p } m.memory := by
    simp only [Ext9.execNew, hread m hx hxP hlx]
  have hstep := Open9.step_of_fetch_new (by rw [erip]; exact fetch) hdec hexec
  set m' : MState := ⟨{ m.core with rip := p }, m.memory⟩ with hm'
  have unchanged : ∀ l, hrip l = none → toFrag m' l = toFrag m l := by
    intro l e1
    cases l with
    | rip => exact absurd (ripPt_dom hripP) (by rw [e1]; simp)
    | _ => rfl
  refine ⟨m', hstep, fun l hl0 => ?_, ?_⟩
  · simp only [Frag.union_eq_none] at hl0
    exact unchanged l hl0.2.1
  have d1 := Frag.reval_disjoint hd1 (toFrag m')
  have d2 := Frag.reval_disjoint hd2 (toFrag m')
  rw [Frag.reval_union] at d1 ⊢
  rw [Frag.reval_union]
  refine ⟨_, _, d1, rfl, ?_, _, _, d2, rfl, ?_, ?_⟩
  · rw [Frag.reval_eq_of_agree hlc (fun l hl' => by
      have e := none_of_disjoint hd1 hl'
      simp only [Frag.union_eq_none] at e
      exact unchanged l e.1)]
    exact hcP
  · exact ripPt_reval m' hripP
  · rw [Frag.reval_eq_of_agree hlx (fun l hl' =>
      unchanged l (none_of_disjoint (Frag.Disjoint.symm hd2) hl'))]
    exact hxP

/-! ## The class fields on `Open9` -/

theorem callR_open9 (r : Reg) (pc s p : Word) (hs : 8 ≤ s.toNat) :
    Progress Open9.isa
      (codePt pc.toNat (encCallR r) ∗ ripPt pc ∗ regPt r p ∗ regPt .rsp s ∗
        blockAny (s.toNat - 8) 8)
      (codePt pc.toNat (encCallR r) ∗ ripPt p ∗ regPt r p ∗ regPt .rsp (s - 8#64) ∗
        wordPt (s.toNat - 8) (nextPc pc (encCallR r))) :=
  callInd_progress hs (encR_ne_nil _ _) (decode_encCallR r)
    (fun _ _ hp hl next => readRM_reg hp hl next)

theorem callM_open9 {need : Permissions → Prop} (hneed : ∀ q, need q → RO q) (base : Reg)
    (d : BitVec 8) (pc s v p : Word) (hs : 8 ≤ s.toNat) :
    Progress Open9.isa
      (codePt pc.toNat (encCallM base d) ∗ ripPt pc ∗ regPt base v ∗
        wordAt need (ea v d).toNat p ∗ regPt .rsp s ∗ blockAny (s.toNat - 8) 8)
      (codePt pc.toNat (encCallM base d) ∗ ripPt p ∗ regPt base v ∗
        wordAt need (ea v d).toNat p ∗ regPt .rsp (s - 8#64) ∗
        wordPt (s.toNat - 8) (nextPc pc (encCallM base d))) := by
  have := callInd_progress (X := regPt base v ∗ wordAt need (ea v d).toNat p)
    (bs := encCallM base d) (pc := pc) hs
    (encM_ne_nil _ _ _) (decode_encCallM base d)
    (fun _ _ hp hl next => readRM_memOp hneed hp hl next)
  simpa only [sep_assoc] using this

theorem jmpR_open9 (r : Reg) (pc p : Word) :
    Progress Open9.isa (codePt pc.toNat (encJmpR r) ∗ ripPt pc ∗ regPt r p)
      (codePt pc.toNat (encJmpR r) ∗ ripPt p ∗ regPt r p) :=
  jmpInd_progress (encR_ne_nil _ _) (decode_encJmpR r)
    (fun _ _ hp hl next => readRM_reg hp hl next)

theorem jmpM_open9 {need : Permissions → Prop} (hneed : ∀ q, need q → RO q) (base : Reg)
    (d : BitVec 8) (pc v p : Word) :
    Progress Open9.isa
      (codePt pc.toNat (encJmpM base d) ∗ ripPt pc ∗ regPt base v ∗ wordAt need (ea v d).toNat p)
      (codePt pc.toNat (encJmpM base d) ∗ ripPt p ∗ regPt base v ∗
        wordAt need (ea v d).toNat p) :=
  jmpInd_progress (encM_ne_nil _ _ _) (decode_encJmpM base d)
    (fun _ _ hp hl next => readRM_memOp hneed hp hl next)

end Silmaril.Proofs.X86.Sep.Ind
