module

public import Silmaril.Proofs.X86.Pool.Par
public import Silmaril.Proofs.X86.Pool.Tso
public import Silmaril.Proofs.X86.Pool.Fetch
public import Silmaril.X86.Open.Thms
public import Silmaril.X86.Sep.Thms
public import Silmaril.X86.Sep.List.Thms
public import Silmaril.X86.Ext.Machine

/-!
# Proofs: a non-vacuous two-thread pool

Two threads run the **same** one-byte code `c3` (`ret`) at `0x400000`, which neither owns: it
is the shared read-only context. Each thread owns `rip`, `rsp` and the eight-byte return slot
of its own stack (`0x7000` holding `0x401000` for thread `true`, `0x8000` holding `0x402000`
for thread `false`). A thread has finished when `rip` is its return address.

* `ret_lstep`: one `Open.step` of `ret` from **every** state consistent with the owned
  fragment and the code; it changes only owned locations.
* `ret_ltriple`: the frame-requantified triple of `ret` with the code as read-only context,
  at every step index.
* `two_ownershipSafe`: the concrete two-thread pool is `OwnershipSafe` (the hypothesis of
  `Task.drfTso`).
* `two_poolSafe`: `par_shared_ro` applied to it: every schedule of every length is safe, and
  when both threads have returned both postconditions, the code and the rest of the pool
  hold.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Pool.Example

open Silmaril.X86 (State MState Word Byte Reg Insn)
open Silmaril.Process (Memory Region Permissions addressLimit)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.MemEvent (ChangesWithin)
open Silmaril.X86.Pool
open Silmaril.Proofs.X86.Pool

/-! ## `ret` as a frame-requantified triple -/

/-- An instruction of the base machine that executes is one open step (copied from
`Silmaril/Proofs/X86/Sep/Call.lean`, which this topic may not import). -/
theorem open_step_of_insn {m : MState} {i : Insn} {core : State} {mem : Memory}
    (f : m.memory.fetchBytes m.core.rip.toNat i.encode.length = some i.encode)
    (e : i.exec m.core m.memory = some (core, mem)) :
    Silmaril.X86.Open.step m = some ⟨core, mem⟩ := by
  have h : Silmaril.X86.MState.stepOpt (core.rip + 1#64) m = some ⟨core, mem⟩ :=
    Silmaril.X86.MState.stepOpt_of_exec f (Silmaril.X86.Insn.decode_encode i) e (by
      rintro ⟨-, h⟩
      exact absurd h (by bv_omega))
  exact Silmaril.X86.Open.step_of_ext8_stepOpt
    (Silmaril.X86.Ext8.stepOpt_of_ext (Silmaril.X86.Ext.stepOpt_of_x86 h))

/-- The code: `ret`. -/
def retCode : List Byte := Insn.encode .ret

/-- The owned precondition: at `e`, `rsp = s`, return address `ret` at `[s]`. -/
def retPre (e s ret : Word) : SProp := ripPt e ∗ regPt .rsp s ∗ wordPt s.toNat ret

/-- The owned postcondition: returned to `ret`, `rsp` popped. -/
def retPost (s ret : Word) : SProp := ripPt ret ∗ regPt .rsp (s + 8#64) ∗ wordPt s.toNat ret

/-- Finished: `rip` is the return address. -/
def retFin (ret : Word) (c : State) : Prop := c.rip = ret

theorem ripPt_reval_core {v : Word} {h : Frag} (m : MState) (hp : ripPt v h) :
    ripPt m.core.rip (reval h (toFrag m)) := by
  subst hp
  funext l
  cases l <;> simp [reval, Frag.single, toFrag]

theorem fragUnion_eq_none {a b : Frag} {l : Loc} : union a b l = none ↔ a l = none ∧ b l = none := by
  cases e : a l <;> simp [union, e]

theorem reval_union_eq (a b s : Frag) : reval (union a b) s = union (reval a s) (reval b s) := by
  funext l
  cases e : a l <;> cases e' : b l <;> simp [reval, union, e, e'] <;> cases s l <;> rfl

theorem disjoint_reval_left' {a b : Frag} {m : MState} (hd : Disjoint a b) :
    Disjoint (reval a (toFrag m)) (reval b (toFrag m)) := by
  intro l
  rcases hd l with e | e
  · exact .inl (reval_none e)
  · exact .inr (reval_none e)

/-- **One step of `ret`** from every state consistent with the owned fragment and the code. -/
theorem ret_lstep {e s ret : Word} {m : MState} {h r : Frag} (hp : retPre e s ret h)
    (hr : codePt e.toNat retCode r) (hd : Disjoint h r) (hle : Le (union h r) (toFrag m)) :
    ∃ m', Silmaril.X86.Open.step m = some m' ∧ ChangesWithin h m m' ∧
      m'.core.rip = ret ∧ retPost s ret (reval h (toFrag m')) := by
  have hlh : Le h (toFrag m) := Frag.le_of_union_left hle
  have hlc : Le r (toFrag m) := Frag.le_of_union_right hd hle
  obtain ⟨hrip, r2, hripP, hr2, hlrip, hlr2, hd2, rfl⟩ := sep_le hp hlh
  obtain ⟨hsp, hw, hspP, hwP, hlsp, hlw, hd3, rfl⟩ := sep_le hr2 hlr2
  have erip := ripPt_le hripP hlrip
  have ersp := regPt_le hspP hlsp
  have fetch := fetchBytes_of_codePt (by simp [retCode, Insn.encode]) hr hlc
  have hread := readBytes_of_wordPt hwP hlw
  have hpop := Silmaril.X86.popWord_of_readBytes (s := m.core) (by rw [ersp]; exact hread)
  have hexec : Insn.ret.exec m.core m.memory =
      some ({ m.core.write .rsp (m.core.read .rsp + 8#64) with rip := ret }, m.memory) := by
    simp only [Insn.exec, hpop, Option.map_some]
  have hstep := open_step_of_insn (by rw [erip]; exact fetch) hexec
  set m' : MState :=
    ⟨{ m.core.write .rsp (m.core.read .rsp + 8#64) with rip := ret }, m.memory⟩ with hm'
  have hagree : ∀ l, l ≠ .rip → l ≠ .reg .rsp → toFrag m' l = toFrag m l := by
    intro l h1 h2
    cases l with
    | reg q =>
      have hq : q ≠ .rsp := fun e' => h2 (e' ▸ rfl)
      simp [m', toFrag, State.read_write_other _ _ _ _ hq]
    | rip => exact absurd rfl h1
    | flags => rfl
    | mem a => rfl
    | regions => rfl
  have hripS : (hrip .rip).isSome := by rw [hripP]; simp [Frag.single]
  have hspS : (hsp (.reg .rsp)).isSome := by rw [hspP]; simp [Frag.single]
  have hw_rip : hw .rip = none := by
    rcases hd2 .rip with e' | e'
    · rw [e'] at hripS; cases hripS
    · exact (fragUnion_eq_none.mp e').2
  have hw_rsp : hw (.reg .rsp) = none := by
    rcases hd3 (.reg .rsp) with e' | e'
    · rw [e'] at hspS; cases hspS
    · exact e'
  refine ⟨m', hstep, ?_, rfl, ?_⟩
  · -- Only `rip` and `rsp` change, and both are owned.
    intro l hl
    apply hagree
    · rintro rfl
      rw [fragUnion_eq_none] at hl
      rw [hl.1] at hripS; cases hripS
    · rintro rfl
      rw [fragUnion_eq_none, fragUnion_eq_none] at hl
      rw [hl.2.1] at hspS; cases hspS
  · have hw' : reval hw (toFrag m') = hw := by
      funext l
      cases e' : hw l with
      | none => exact reval_none e'
      | some v =>
        rw [reval_of_some (by simp [e']), hagree l (by rintro rfl; rw [hw_rip] at e'; cases e')
          (by rintro rfl; rw [hw_rsp] at e'; cases e'), hlw l v e']
    have hrsp' : regPt .rsp (s + 8#64) (reval hsp (toFrag m')) := by
      have := regPt_reval m' hspP
      have e' : m'.core.read .rsp = s + 8#64 := by
        show (m.core.write .rsp (m.core.read .rsp + 8#64)).read .rsp = _
        rw [State.read_write_same, ersp]
      rwa [e'] at this
    have d2 : Disjoint (reval hrip (toFrag m')) (union (reval hsp (toFrag m')) hw) := by
      have := disjoint_reval_left' (m := m') hd2
      rwa [reval_union_eq, hw'] at this
    have d3 : Disjoint (reval hsp (toFrag m')) hw := disjoint_reval_left hd3
    rw [reval_union_eq, reval_union_eq, hw']
    exact ⟨_, _, d2, rfl, ripPt_reval_core m' hripP, _, _, d3, rfl, hrsp', hwP⟩

/-- **`ret` as a frame-requantified triple**, with the code as read-only context, at every
step index. -/
theorem ret_ltriple (e s ret : Word) (hne : e ≠ ret) (n : Nat) :
    LTriple Silmaril.X86.Open.step (retFin ret) (codePt e.toNat retCode) (retPre e s ret)
      (retPost s ret) n := by
  intro c h r hr hp hd
  cases n with
  | zero => trivial
  | succ n =>
    intro mem hle
    obtain ⟨m', hstep, hcw, hrip', hq⟩ := ret_lstep hp hr hd hle
    have erip : c.rip = e := by
      obtain ⟨hrip, -, hripP, -, hlrip, -, -, -⟩ := sep_le hp (Frag.le_of_union_left hle)
      exact ripPt_le hripP hlrip
    refine .inr ⟨fun hf => hne (erip.symm.trans hf), m', hstep, hcw, ?_⟩
    cases n with
    | zero => trivial
    | succ n => exact fun _ _ => .inl ⟨hrip', hq⟩

/-! ## `HoldsIn` (copied from `Silmaril/Proofs/X86/Safe/Stable/NonVacuity.lean`) -/

/-- `P` holds of a part of `s` whose domain lies in `D`. -/
def HoldsIn (P : SProp) (s : Frag) (D : Loc → Prop) : Prop :=
  ∃ h, P h ∧ Le h s ∧ ∀ l, (h l).isSome → D l

theorem emp_in (s : Frag) : HoldsIn emp s (fun _ => False) :=
  ⟨Frag.empty, rfl, fun _ _ e => by simp [Frag.empty] at e, fun _ e => by simp [Frag.empty] at e⟩

theorem sep_in {P Q : SProp} {s : Frag} {D₁ D₂ : Loc → Prop} (hp : HoldsIn P s D₁)
    (hq : HoldsIn Q s D₂) (hd : ∀ l, D₁ l → D₂ l → False) :
    HoldsIn (P ∗ Q) s (fun l => D₁ l ∨ D₂ l) := by
  obtain ⟨h₁, hP, hl₁, hD₁⟩ := hp
  obtain ⟨h₂, hQ, hl₂, hD₂⟩ := hq
  have disj : Disjoint h₁ h₂ := by
    intro l
    cases e₁ : h₁ l with
    | none => exact .inl rfl
    | some v =>
      cases e₂ : h₂ l with
      | none => exact .inr rfl
      | some w => exact absurd (hd l (hD₁ l (by simp [e₁])) (hD₂ l (by simp [e₂]))) id
  refine ⟨union h₁ h₂, ⟨h₁, h₂, disj, rfl, hP, hQ⟩, ?_, ?_⟩
  · intro l v e
    simp only [Frag.union] at e
    cases e₁ : h₁ l with
    | none => rw [e₁] at e; exact hl₂ l v e
    | some u => rw [e₁] at e; cases e; exact hl₁ l _ e₁
  · intro l e
    simp only [Frag.union] at e
    cases e₁ : h₁ l with
    | none => rw [e₁] at e; exact .inr (hD₂ l e)
    | some u => exact .inl (hD₁ l (by simp [e₁]))

theorem mono_in {P : SProp} {s : Frag} {D D' : Loc → Prop} (hp : HoldsIn P s D)
    (hD : ∀ l, D l → D' l) : HoldsIn P s D' := by
  obtain ⟨h, a, b, c⟩ := hp; exact ⟨h, a, b, fun l e => hD l (c l e)⟩

theorem single_le {l : Loc} {v : Val} {s : Frag} (e : s l = some v) :
    Le (Frag.single l v) s := by
  intro l' w h; simp only [Frag.single] at h; split at h <;> simp_all

theorem single_dom {l : Loc} {v : Val} : ∀ l', (Frag.single l v l').isSome → l' = l := by
  intro l' h; simp only [Frag.single] at h; split at h <;> simp_all

theorem regPt_in (m : MState) (r : Reg) :
    HoldsIn (regPt r (m.core.read r)) (toFrag m) (· = .reg r) :=
  ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

theorem ripPt_in (m : MState) : HoldsIn (ripPt m.core.rip) (toFrag m) (· = .rip) :=
  ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

theorem bytesAt_in {need : Permissions → Prop} (m : MState) :
    ∀ (a : Nat) (bs : List Byte), (∀ i (hi : i < bs.length), a + i < addressLimit ∧
      m.memory.bytes.get? (a + i) = some bs[i] ∧ need (permsAt m.memory (a + i))) →
      HoldsIn (bytesAt need a bs) (toFrag m) (fun l => ∃ i < bs.length, l = .mem (a + i))
  | a, [], _ => mono_in (emp_in _) (fun _ h => h.elim)
  | a, b :: bs, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hb : HoldsIn (byteAt need a b) (toFrag m) (· = .mem a) := by
      refine ⟨Frag.single (.mem a) (.cell ⟨some b, permsAt m.memory a⟩),
        ⟨h0.1, _, h0.2.2, rfl⟩, single_le ?_, single_dom⟩
      simp only [toFrag, h0.2.1]
    have ht := bytesAt_in m (a + 1) bs (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    refine mono_in (sep_in hb ht ?_) ?_
    · rintro l rfl ⟨i, -, e⟩; simp at e; omega
    · rintro l (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by simp; omega, by simp; omega⟩

theorem disjoint_of_dom {a b : Frag} {D₁ D₂ : Loc → Prop} (ha : ∀ l, (a l).isSome → D₁ l)
    (hb : ∀ l, (b l).isSome → D₂ l) (hd : ∀ l, D₁ l → D₂ l → False) : Disjoint a b := by
  intro l
  cases e₁ : a l with
  | none => exact .inl rfl
  | some v =>
    cases e₂ : b l with
    | none => exact .inr rfl
    | some w => exact absurd (hd l (ha l (by simp [e₁])) (hb l (by simp [e₂]))) id

/-! ## The concrete pool -/

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩
def codeAt : Word := 0x400000
def spT : Word := 0x7000
def spF : Word := 0x8000
def retT : Word := 0x401000
def retF : Word := 0x402000

/-- Thread `t`'s stack pointer. -/
def sp (t : Bool) : Word := if t then spT else spF
/-- Thread `t`'s return address. -/
def retOf (t : Bool) : Word := if t then retT else retF

/-- The code `c3` at `0x400000`; `0x401000` at `0x7000`, `0x402000` at `0x8000`; one region
mapping every address read/write/execute. -/
def mem : Memory :=
  ⟨[allRegion],
    Memory.install (Memory.install (Memory.install ∅ spT.toNat (encodeWords [retT]))
      spF.toNat (encodeWords [retF])) codeAt.toNat retCode⟩

/-- Thread `t` at the code, with its own stack pointer. -/
def core (t : Bool) : State :=
  ⟨fun r => match r with
    | .rsp => sp t | _ => 0,
    codeAt, ⟨none, none, none, none, none, none⟩, 0⟩

/-- The two-thread pool. -/
def pool : Pool Bool := ⟨fun t => some (core t), mem⟩

/-- A thread has finished when it has returned. -/
def fin (t : Bool) (c : State) : Prop := retFin (retOf t) c

theorem perms_all (a : Nat) (ha : a < 2 ^ 64) : permsAt mem a = ⟨true, true, true⟩ := by
  have : a < 18446744073709551616 := ha
  simp [permsAt, Memory.permits, mem, allRegion, Region.Contains, Permissions.allows, this]

theorem retCode_eq : retCode = [0xc3] := by decide

theorem get_code : mem.bytes.get? (codeAt.toNat + 0) = some (retCode[0]'(by decide)) :=
  Memory.install_get _ _ _ 0 (by decide)

theorem get_word (t : Bool) (i : Nat) (hi : i < 8) : mem.bytes.get? ((sp t).toNat + i) =
    (encodeWords [retOf t])[i]? := by
  have eT : spT.toNat = 0x7000 := rfl
  have eF : spF.toNat = 0x8000 := rfl
  have eC : codeAt.toNat = 0x400000 := rfl
  have hl : i < (encodeWords [retOf t]).length := by simp; omega
  dsimp only [mem]
  cases t with
  | true =>
    simp only [sp, retOf, ite_true] at hl ⊢
    rw [Memory.install_outside _ _ _ _ (by rw [eC, eT, retCode_eq]; simp; omega),
      Memory.install_outside _ _ _ _ (by rw [eF, eT]; simp; omega),
      Memory.install_get _ _ _ i hl, List.getElem?_eq_getElem hl]
  | false =>
    simp only [sp, retOf, Bool.false_eq_true, ite_false] at hl ⊢
    rw [Memory.install_outside _ _ _ _ (by rw [eC, eF, retCode_eq]; simp; omega),
      Memory.install_get _ _ _ i hl, List.getElem?_eq_getElem hl]

/-- The owned domain of thread `t`. -/
def dom (t : Bool) (l : Loc) : Prop :=
  (l = .rip ∨ l = .reg .rsp) ∨ ∃ i < 8, l = .mem ((sp t).toNat + i)

theorem sp_toNat (t : Bool) : (sp t).toNat = if t then 0x7000 else 0x8000 := by
  cases t <;> rfl

theorem thread_holds (t : Bool) :
    HoldsIn (retPre codeAt (sp t) (retOf t)) (toFrag ⟨core t, mem⟩) (dom t) := by
  have hrip := ripPt_in ⟨core t, mem⟩
  have hrsp := regPt_in ⟨core t, mem⟩ .rsp
  have hword := bytesAt_in (need := RW) ⟨core t, mem⟩ (sp t).toNat (encodeWords [retOf t])
    (fun i hi => by
      have hi' : i < 8 := by simpa using hi
      refine ⟨by rw [sp_toNat]; simp only [addressLimit]; split <;> omega, ?_, ?_⟩
      · show mem.bytes.get? _ = _
        rw [get_word t i hi', List.getElem?_eq_getElem hi]
      · show RW (permsAt mem _)
        rw [perms_all _ (by rw [sp_toNat]; split <;> omega)]; exact ⟨rfl, rfl⟩)
  have := sep_in hrip (sep_in hrsp hword (by
    rintro l rfl ⟨i, -, e⟩; cases e)) (by
    rintro l rfl (e | ⟨i, -, e⟩) <;> cases e)
  have e1 : (core t).rip = codeAt := rfl
  have e2 : (core t).read .rsp = sp t := rfl
  have h' := mono_in this (D' := dom t) (fun l h => by
    rcases h with h | h | ⟨i, hi, h⟩
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr ⟨i, by simpa using hi, h⟩)
  simp only [e1, e2] at h'
  exact h'

/-- The code's domain. -/
def cdom (l : Loc) : Prop := l = .mem (codeAt.toNat + 0)

theorem code_holds (c : State) : HoldsIn (codePt codeAt.toNat retCode) (toFrag ⟨c, mem⟩) cdom := by
  have := bytesAt_in (need := EX) ⟨c, mem⟩ codeAt.toNat retCode (fun i hi => by
    have hi0 : i = 0 := by rw [retCode_eq] at hi; simp at hi; omega
    subst hi0
    refine ⟨by simp only [addressLimit]; decide, get_code, ?_⟩
    show EX (permsAt mem _)
    rw [perms_all _ (by decide)]; rfl)
  refine mono_in this (fun l ⟨i, hi, h⟩ => ?_)
  have : i = 0 := by rw [retCode_eq] at hi; simp at hi; omega
  subst this; exact h

theorem dom_cdom (t : Bool) (l : Loc) (h₁ : dom t l) (h₂ : cdom l) : False := by
  unfold cdom at h₂; subst h₂
  rcases h₁ with (h | h) | ⟨i, hi, h⟩
  · cases h
  · cases h
  · simp only [Loc.mem.injEq, sp_toNat] at h
    have : codeAt.toNat = 0x400000 := rfl
    rw [this] at h
    split at h <;> omega

theorem dom_dom (l : Loc) (hl : l.isLocal = false) (h₁ : dom true l) (h₂ : dom false l) :
    False := by
  rcases h₁ with (h | h) | ⟨i, hi, h⟩
  · subst h; cases hl
  · subst h; cases hl
  · rcases h₂ with (h' | h') | ⟨j, hj, h'⟩
    · subst h'; cases h
    · subst h'; cases h
    · rw [h] at h'
      simp only [Loc.mem.injEq, sp_toNat, ite_true, Bool.false_eq_true, ite_false] at h'
      omega

theorem shared_disjoint_dom {hT hF : Frag} (dT : ∀ l, (hT l).isSome → dom true l)
    (dF : ∀ l, (hF l).isSome → dom false l) (l : Loc) (hl : l.isLocal = false) :
    hT l = none ∨ hF l = none := by
  cases e₁ : hT l with
  | none => exact .inl rfl
  | some v =>
    cases e₂ : hF l with
    | none => exact .inr rfl
    | some w => exact (dom_dom l hl (dT l (by simp [e₁])) (dF l (by simp [e₂]))).elim

/-- The owned fragments of the two threads and the shared code fragment. -/
theorem parts : ∃ hT hF r : Frag,
    retPre codeAt (sp true) (retOf true) hT ∧ retPre codeAt (sp false) (retOf false) hF ∧
    codePt codeAt.toNat retCode r ∧ SharedOnly r ∧
    Le hT (toFrag ⟨core true, mem⟩) ∧ Le hF (toFrag ⟨core false, mem⟩) ∧
    Le r (toFrag ⟨core true, mem⟩) ∧ Disjoint hT r ∧ Disjoint hF r ∧
    PFrag.Disjoint (embed true hT) (embed false hF) := by
  obtain ⟨hT, pT, lT, dT⟩ := thread_holds true
  obtain ⟨hF, pF, lF, dF⟩ := thread_holds false
  obtain ⟨r, pr, lr, dr⟩ := code_holds (core true)
  have hrS : SharedOnly r := by
    intro l hl
    cases e : r l with
    | none => rfl
    | some v =>
      have := dr l (by simp [e])
      unfold cdom at this; subst this; cases hl
  exact ⟨hT, hF, r, pT, pF, pr, hrS, lT, lF, lr, disjoint_of_dom dT dr (dom_cdom true),
    disjoint_of_dom dF dr (dom_cdom false),
    disjoint_embed_ne (by decide) (shared_disjoint_dom dT dF)⟩

theorem codeAt_ne (t : Bool) : codeAt ≠ retOf t := by cases t <;> decide

/-- **The concrete two-thread pool is ownership-safe**: both threads run the same `ret` at
`0x400000` (shared read-only) on disjoint stacks. This is the hypothesis of `Task.drfTso`. -/
theorem two_ownershipSafe : OwnershipSafe Silmaril.X86.Open.step fin pool := by
  obtain ⟨hT, hF, r, pT, pF, pr, hrS, lT, lF, lr, drT, drF, dTF⟩ := parts
  have hdr : ∀ t : Bool, Disjoint (if t then hT else hF) r := by
    intro t; cases t
    · exact drF
    · exact drT
  refine ⟨fun t => if t then hT else hF, r, fun t => retPost (sp t) (retOf t), hrS,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; simp [pool] at ht
  · intro t t' htt
    cases t <;> cases t'
    · exact absurd rfl htt
    · exact PF.disjoint_symm dTF
    · exact dTF
    · exact absurd rfl htt
  · intro t; exact disjoint_embed_embedS (hdr t)
  · intro t
    apply embed_le_poolFrag (c := core t) rfl
    cases t
    · exact lF
    · exact lT
  · exact embedS_le_poolFrag (c := core true) lr
  · intro t c ht n
    simp only [pool, Option.some.injEq] at ht
    subst ht
    have hp : retPre codeAt (sp t) (retOf t) (if t then hT else hF) := by
      cases t
      · exact pF
      · exact pT
    exact ret_ltriple codeAt (sp t) (retOf t) (codeAt_ne t) n (core t) _ r pr hp (hdr t)

/-! ## Footprints: `ret` is `LSafeEv` on `openEv` -/

theorem union_isSome_left {a b : Frag} {l : Loc} (h : (a l).isSome) : (union a b l).isSome := by
  cases e : a l with
  | none => rw [e] at h; cases h
  | some v => simp [union, e]

theorem union_isSome_right {a b : Frag} {l : Loc} (h : (b l).isSome) : (union a b l).isSome := by
  cases e : a l with
  | none => simp [union, e, h]
  | some v => simp [union, e]

/-- The fetch of `openEv` at the code: `ret`, one byte. -/
theorem ret_fetch {e : Word} {m : MState} {h r : Frag} (hr : codePt e.toNat retCode r)
    (hd : Disjoint h r) (hle : Le (union h r) (toFrag m)) :
    Silmaril.X86.MemEvent.openFetch m.memory e.toNat = some (.base .ret, 1) := by
  have hlc : Le r (toFrag m) := Frag.le_of_union_right hd hle
  have fetch := fetchBytes_of_codePt (by simp [retCode, Insn.encode]) hr hlc
  rw [retCode_eq] at fetch
  have hx : Silmaril.X86.Ext.fetch m.memory e.toNat = .decoded .ret 1 :=
    Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨_, fetch, by decide⟩
  have h8 := Silmaril.X86.Ext8.fetch_of_ne_undecodable (memory := m.memory)
    (address := e.toNat) (by rw [hx]; simp)
  simp only [Silmaril.X86.MemEvent.openFetch, h8, hx]
  rfl

/-- The footprint of `ret`: the fetched byte is the code, the popped word is owned, nothing
is written. -/
theorem ret_footprint {e s ret : Word} {m : MState} {h r : Frag} (hp : retPre e s ret h)
    (hr : codePt e.toNat retCode r) (hd : Disjoint h r) (hle : Le (union h r) (toFrag m)) :
    InFootprint h r e.toNat 1 (Silmaril.X86.MemEvent.ext8Accesses (.base .ret) m.core 1) := by
  have hlh : Le h (toFrag m) := Frag.le_of_union_left hle
  obtain ⟨hrip, r2, -, hr2, -, hlr2, -, rfl⟩ := sep_le hp hlh
  obtain ⟨hsp, hw, hspP, hwP, hlsp, -, -, rfl⟩ := sep_le hr2 hlr2
  have ersp := regPt_le hspP hlsp
  refine ⟨fun j hj => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have hj0 : j = 0 := by omega
    subst hj0
    exact union_isSome_right (bytesAt_dom hr 0 (by rw [retCode_eq]; decide))
  · obtain ⟨ev, hev, -, hcov⟩ := ha
    simp only [Silmaril.X86.MemEvent.ext8Accesses, Silmaril.X86.MemEvent.extAccesses,
      Silmaril.X86.MemEvent.popEv, List.mem_singleton] at hev
    subst hev
    obtain ⟨h1, h2⟩ := hcov
    simp only [ersp] at h1 h2
    have := bytesAt_dom hwP (a - s.toNat) (by simp [encodeWords]; omega)
    rw [show s.toNat + (a - s.toNat) = a by omega] at this
    exact union_isSome_left (union_isSome_right (union_isSome_right this))
  · obtain ⟨ev, hev, hw', -⟩ := ha
    simp only [Silmaril.X86.MemEvent.ext8Accesses, Silmaril.X86.MemEvent.extAccesses,
      Silmaril.X86.MemEvent.popEv, List.mem_singleton] at hev
    subst hev
    cases hw'

/-- **`ret` as a footprint triple** on `openEv` (its step is `Open.step`), every index. -/
theorem ret_ltripleEv (e s ret : Word) (hne : e ≠ ret) (n : Nat) :
    LTripleEv openEv (retFin ret) (codePt e.toNat retCode) (retPre e s ret)
      (retPost s ret) n := by
  intro c h r hr hp hd
  cases n with
  | zero => trivial
  | succ n =>
    intro mem hle
    obtain ⟨m', hstep, hcw, hrip', hq⟩ := ret_lstep hp hr hd hle
    have erip : c.rip = e := by
      obtain ⟨hrip, -, hripP, -, hlrip, -, -, -⟩ := sep_le hp (Frag.le_of_union_left hle)
      exact ripPt_le hripP hlrip
    refine .inr ⟨fun hf => hne (erip.symm.trans hf), .base .ret, 1, m', ?_, ?_, ?_, ?_, hcw, ?_⟩
    · rw [erip]; exact ret_fetch (m := ⟨c, mem⟩) hr hd hle
    · rw [erip]; exact openFetch_stable (ret_fetch (m := ⟨c, mem⟩) hr hd hle)
    · rw [erip]; exact ret_footprint (m := ⟨c, mem⟩) hp hr hd hle
    · rw [openEv_step]; exact hstep
    · cases n with
      | zero => trivial
      | succ n => exact fun _ _ => .inl ⟨hrip', hq⟩

/-- **The concrete two-thread pool is footprint-ownership-safe** on `openEv`: the hypothesis
of `Task.drfTso`, discharged. -/
theorem two_ownershipSafeEv : OwnershipSafeEv openEv fin pool := by
  obtain ⟨hT, hF, r, pT, pF, pr, hrS, lT, lF, lr, drT, drF, dTF⟩ := parts
  have hdr : ∀ t : Bool, Disjoint (if t then hT else hF) r := by
    intro t; cases t
    · exact drF
    · exact drT
  refine ⟨fun t => if t then hT else hF, r, fun t => retPost (sp t) (retOf t), hrS,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; simp [pool] at ht
  · intro t t' htt
    cases t <;> cases t'
    · exact absurd rfl htt
    · exact PF.disjoint_symm dTF
    · exact dTF
    · exact absurd rfl htt
  · intro t; exact disjoint_embed_embedS (hdr t)
  · intro t
    apply embed_le_poolFrag (c := core t) rfl
    cases t
    · exact lF
    · exact lT
  · exact embedS_le_poolFrag (c := core true) lr
  · intro t c ht n
    simp only [pool, Option.some.injEq] at ht
    subst ht
    have hp : retPre codeAt (sp t) (retOf t) (if t then hT else hF) := by
      cases t
      · exact pF
      · exact pT
    exact ret_ltripleEv codeAt (sp t) (retOf t) (codeAt_ne t) n (core t) _ r pr hp (hdr t)

/-! ## Every schedule, via `par_shared_ro` -/

/-- The part of `S` outside the domain of `H`. -/
def pdiff (S H : PFrag Bool) : PFrag Bool := fun L => if (H L).isSome then none else S L

theorem split_le {H S : PFrag Bool} (hle : PFrag.Le H S) :
    S = PFrag.union H (pdiff S H) ∧ PFrag.Disjoint H (pdiff S H) := by
  refine ⟨funext fun L => ?_, fun L => ?_⟩
  · cases e : H L with
    | none => simp [PFrag.union, pdiff, e]
    | some v => simp [PFrag.union, e, hle L v e]
  · cases e : H L with
    | none => exact .inl rfl
    | some v => exact .inr (by simp [pdiff, e])

theorem le_pdiff {A B S : PFrag Bool} (hB : PFrag.Le B S) (hd : PFrag.Disjoint A B) :
    PFrag.Le B (pdiff S A) := by
  intro L v e
  rcases hd L with e' | e'
  · simp [pdiff, e', hB L v e]
  · rw [e'] at e; cases e

/-- **Both threads run in parallel under every schedule** (`par_shared_ro`): the pool's
fragment splits as thread `true`'s `retPre`, thread `false`'s `retPre`, the shared code and a
frame `F`; for every step bound no unfinished thread is stuck, and when both have returned,
both `retPost`s, the code and `F` hold. -/
theorem two_poolSafe : ∃ F : PProp Bool,
    (atThread true (retPre codeAt spT retT) ∗ₚ atThread false (retPre codeAt spF retF) ∗ₚ
      atShared (codePt codeAt.toNat retCode) ∗ₚ F) (poolFrag pool) ∧
    ∀ n, PoolSafe Silmaril.X86.Open.step fin
      (fun p' => (atThread true (retPost spT retT) ∗ₚ atThread false (retPost spF retF) ∗ₚ
        atShared (codePt codeAt.toNat retCode) ∗ₚ F) (poolFrag p')) n pool := by
  obtain ⟨hT, hF, r, pT, pF, pr, hrS, lT, lF, lr, drT, drF, dTF⟩ := parts
  have leT : PFrag.Le (embed true hT) (poolFrag pool) := embed_le_poolFrag (c := core true) rfl lT
  have leF : PFrag.Le (embed false hF) (poolFrag pool) :=
    embed_le_poolFrag (c := core false) rfl lF
  have leR : PFrag.Le (embedS r : PFrag Bool) (poolFrag pool) :=
    embedS_le_poolFrag (c := core true) lr
  obtain ⟨e1, d1⟩ := split_le leT
  have leF' := le_pdiff leF dTF
  obtain ⟨e2, d2⟩ := split_le leF'
  have leR' := le_pdiff (le_pdiff leR (disjoint_embed_embedS (t := true) drT))
    (disjoint_embed_embedS (t := false) drF)
  obtain ⟨e3, d3⟩ := split_le leR'
  let X₁ := pdiff (poolFrag pool) (embed true hT)
  let X₂ := pdiff X₁ (embed false hF)
  let X₃ := pdiff X₂ (embedS r)
  have hpre : (atThread true (retPre codeAt spT retT) ∗ₚ atThread false (retPre codeAt spF retF) ∗ₚ
      atShared (codePt codeAt.toNat retCode) ∗ₚ (fun H => H = X₃)) (poolFrag pool) :=
    ⟨_, _, d1, e1, ⟨hT, pT, rfl⟩, _, _, d2, e2, ⟨hF, pF, rfl⟩, _, _, d3, e3, ⟨r, pr, hrS, rfl⟩,
      rfl⟩
  refine ⟨fun H => H = X₃, hpre, fun n => ?_⟩
  exact par_shared_ro Silmaril.X86.Open.step fin true false
    (codePt codeAt.toNat retCode) (retPre codeAt spT retT) (retPost spT retT)
    (retPre codeAt spF retF) (retPost spF retF) (fun H => H = X₃) (by decide)
    (ret_ltriple codeAt spT retT (by decide) n) (ret_ltriple codeAt spF retF (by decide) n)
    ⟨_, rfl⟩ ⟨_, rfl⟩ (fun t h1 h2 => by cases t <;> contradiction) hpre

end Silmaril.Proofs.X86.Pool.Example
