module

public import Silmaril.Machine.X86.BlockCert9.Defs
public import Silmaril.Machine.X86.BlockCert.Thms
public import Silmaril.Machine.X86.Open9.Thms

/-!
# `Ext9` block certificates are runs of `Open9.step`

* `execNew_rip`, `execNew_mem`: a retired new form that falls through continues at the next
  instruction; one that writes no memory keeps it (case analysis over `Ext9.execNew`);
* `runX_open9`: a checked `Ext9` listing that runs is an `Open9` run, memory unchanged;
* `Code.run_open9`: the same for both kinds of block code (Bir blocks through
  `BlockCert.runL_open` and `Open9.reaches_of_open`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.BlockCert9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM retire writeRM writeNarrow readRM readNarrow)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.BlockCert9

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem retire_ok {next : Word} {o : Option (State × Memory)} {s : State} {m : Memory}
    (h : retire next o = .ok s m) :
    s.rip = next ∧ ∃ t, o = some (t, m) ∧ s = { t with rip := next } := by
  cases o with
  | none => cases h
  | some p => obtain ⟨t, m'⟩ := p; cases h; exact ⟨rfl, t, rfl, rfl⟩

theorem map_snd {α : Type} {f : α → State × Memory} {o : Option α} {t : State}
    {mem mem' : Memory} (hf : ∀ a, (f a).2 = mem) (h : Option.map f o = some (t, mem')) :
    mem' = mem := by
  cases o with
  | none => cases h
  | some a =>
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← hf a, h]

theorem carryStep_ok {sz : Silmaril.X86.Ext.Sz} {sub : Bool} {d : RM} {y : BitVec sz.bits}
    {s : State} {mem : Memory} {next : Word} {s' : State} {mem' : Memory}
    (h : Ext9.carryStep sz sub d y s mem next = .ok s' mem') :
    s'.rip = next ∧ (BlockCert.rmIsReg d = true → mem' = mem) := by
  unfold Ext9.carryStep at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨hr, t, ho, -⟩ := retire_ok h
      refine ⟨hr, fun hd => ?_⟩
      cases d with
      | mem => cases hd
      | reg r => simp [writeRM] at ho; exact ho.2.symm

theorem alu16_reg {op : Silmaril.X86.AluOp} {d : RM} {y : BitVec 16} {s t : State}
    {mem mem' : Memory} {next : Word} (hd : BlockCert.rmIsReg d = true)
    (h : Ext9.alu16 op d y s mem next = some (t, mem')) : mem' = mem := by
  cases d with
  | mem => cases hd
  | reg r =>
    unfold Ext9.alu16 at h
    simp only [readNarrow] at h
    split at h
    · cases h; rfl
    · simp [writeNarrow] at h; exact h.2.symm

theorem test16_mem {d : RM} {y : BitVec 16} {s t : State} {mem mem' : Memory} {next : Word}
    (h : Ext9.test16 d y s mem next = some (t, mem')) : mem' = mem := by
  unfold Ext9.test16 at h
  exact map_snd (fun _ => rfl) h

/-- A retired new form that falls through continues at the next instruction. -/
theorem execNew_rip {i : Ext9.New} (hf : fallsThroughNew i = true) {s : State} {mem : Memory}
    {next : Word} {s' : State} {mem' : Memory} (h : Ext9.execNew i s mem next = .ok s' mem') :
    s'.rip = next := by
  cases i
  case callInd => cases hf
  case jmpInd => cases hf
  case repRet => cases hf
  case adc => exact (carryStep_ok h).1
  case adcI => exact (carryStep_ok h).1
  case adcR =>
    simp only [Ext9.execNew] at h
    split at h
    · cases h
    · exact (carryStep_ok h).1
  all_goals simp only [Ext9.execNew] at h
  all_goals (repeat' (first | (cases h; done) | exact (retire_ok h).1 | split at h))

/-- A retired new form that writes no memory leaves it unchanged. -/
theorem execNew_mem {i : Ext9.New} (hf : noWriteNew i = true) {s : State} {mem : Memory}
    {next : Word} {s' : State} {mem' : Memory} (h : Ext9.execNew i s mem next = .ok s' mem') :
    mem' = mem := by
  cases i
  case callInd => cases hf
  case pushI => cases hf
  case repRet => exact BlockCert.exec_mem (i := .ret) (len := 2) rfl h
  case adc => exact (carryStep_ok h).2 hf
  case adcI => exact (carryStep_ok h).2 hf
  case adcR =>
    simp only [Ext9.execNew] at h
    split at h
    · cases h
    · exact (carryStep_ok h).2 rfl
  case jmpInd =>
    simp only [Ext9.execNew] at h
    split at h
    · cases h
    · cases h; rfl
  case alu16 =>
    simp only [Ext9.execNew] at h
    obtain ⟨-, t, ho, -⟩ := retire_ok h
    exact alu16_reg hf ho
  case alu16I =>
    simp only [Ext9.execNew] at h
    obtain ⟨-, t, ho, -⟩ := retire_ok h
    exact alu16_reg hf ho
  case alu16A =>
    simp only [Ext9.execNew] at h
    obtain ⟨-, t, ho, -⟩ := retire_ok h
    exact alu16_reg rfl ho
  case alu16R =>
    simp only [Ext9.execNew] at h
    split at h
    · cases h
    · obtain ⟨-, t, ho, -⟩ := retire_ok h
      exact alu16_reg rfl ho
  case test16 =>
    simp only [Ext9.execNew] at h
    obtain ⟨-, t, ho, -⟩ := retire_ok h
    exact test16_mem ho
  case test16I =>
    simp only [Ext9.execNew] at h
    obtain ⟨-, t, ho, -⟩ := retire_ok h
    exact test16_mem ho
  case test16A =>
    simp only [Ext9.execNew] at h
    obtain ⟨-, t, ho, -⟩ := retire_ok h
    exact test16_mem ho
  all_goals simp only [Ext9.execNew] at h
  all_goals (repeat' (first
    | (cases h; done)
    | (obtain ⟨-, t, ho, -⟩ := retire_ok h; exact map_snd (fun _ => rfl) ho)
    | (obtain ⟨-, t, ho, -⟩ := retire_ok h; cases ho; rfl)
    | split at h))

theorem exec9_rip {i : Ext9.Instr} (hf : fallsThrough9 i = true) {s : State} {mem : Memory}
    {len : Nat} {s' : State} {mem' : Memory} (h : Ext9.exec i s mem len = .ok s' mem') :
    s'.rip = s.rip + BitVec.ofNat 64 len := by
  cases i with
  | ext8 i =>
    cases i with
    | base e => exact BlockCert.exec_rip hf h
    | new _ => cases hf
  | new n => exact execNew_rip hf h

theorem exec9_mem {i : Ext9.Instr} (hf : noWrite9 i = true) {s : State} {mem : Memory}
    {len : Nat} {s' : State} {mem' : Memory} (h : Ext9.exec i s mem len = .ok s' mem') :
    mem' = mem := by
  cases i with
  | ext8 i =>
    cases i with
    | base e => exact BlockCert.exec_mem hf h
    | new _ => cases hf
  | new n => exact execNew_mem hf h

/-- **The bridge for `Ext9` listings.** -/
theorem runX_open9 {code : List Byte} {base : Word} :
    ∀ (L : List (Ext9.Instr × Nat)) (o : Nat) (m m' : MState),
      listingAt9 code o L = true → Loaded m.memory base code →
      m.core.rip = base + BitVec.ofNat 64 o → runX L m = some m' →
      Reaches Open9.step m m' ∧ m'.memory = m.memory
  | [], _, m, m', _, _, _, h => by
    simp only [runX, Option.some.injEq] at h
    subst h
    exact ⟨Reaches.refl _ _, rfl⟩
  | (i, l) :: rest, o, m, m', hok, hl, hrip, h => by
    simp only [listingAt9, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hdec, hfit⟩, hnw⟩, hft⟩, hrest⟩ := hok
    simp only [runX] at h
    split at h
    · rename_i c1 m1 hx
      have hm1 : m1 = m.memory := exec9_mem hnw hx
      have hs : Open9.step m = some ⟨c1, m1⟩ := Open9.step_of_listed hl hrip hfit hdec hx
      cases rest with
      | nil =>
        simp only [runX, Option.some.injEq] at h
        subst h
        exact ⟨Silmaril.X86.SegVC.reaches_head (I := Open9.isa) hs, hm1⟩
      | cons nx rest' =>
        simp only [List.isEmpty_cons, Bool.false_or] at hft
        have hrip1 : c1.rip = base + BitVec.ofNat 64 (o + l) := by
          rw [exec9_rip hft hx, hrip, BitVec.ofNat_add, BitVec.add_assoc]
        have hl1 : Loaded (⟨c1, m1⟩ : MState).memory base code := by
          show Loaded m1 base code; rw [hm1]; exact hl
        obtain ⟨hr, hm⟩ := runX_open9 (nx :: rest') (o + l) ⟨c1, m1⟩ m' hrest hl1 hrip1 h
        exact ⟨Silmaril.X86.SegVC.reaches_cons (I := Open9.isa) hs hr, hm.trans hm1⟩
    · cases h

/-- **The bridge for block code.** -/
theorem code_run_open9 {code : List Byte} {base : Word} {c : Code} {o : Nat} {m m' : MState}
    (hok : c.check code o = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : c.run m = some m') :
    Reaches Open9.step m m' ∧ m'.memory = m.memory := by
  cases c with
  | bir L =>
    obtain ⟨hr, hm⟩ := BlockCert.runL_open hok hl hrip h
    exact ⟨Open9.reaches_of_open hr, hm⟩
  | x9 L => exact runX_open9 L o m m' hok hl hrip h

theorem checked_mem {F : FunCert9} (hc : F.checked = true) {b : Blk} (hb : b ∈ F.blocks) :
    b.code.check F.code b.off = true :=
  List.all_eq_true.mp hc b hb

theorem from_block {F : FunCert9} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) (m0 : MState) :
    ∀ (w : Nat) (b : Blk) (m : MState), F.measure b.off m0 m = w → b ∈ F.blocks →
      F.ann b.off m0 m → m.core.rip = F.base + BitVec.ofNat 64 b.off →
      Loaded m.memory F.base F.code → ∃ t, Reaches Open9.step m t ∧ Q m0 t := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b m hw hb ha hrip hl
    obtain ⟨m', hrun, hnext⟩ := hvc b hb m0 m ha hrip hl
    obtain ⟨hr, hmem⟩ := code_run_open9 (checked_mem hc hb) hl hrip hrun
    rcases hnext with hq | ⟨b', hb', hrip', ha', hlt⟩
    · exact ⟨m', hr, hq⟩
    · have hl' : Loaded m'.memory F.base F.code := by rw [hmem]; exact hl
      obtain ⟨t, hr', hq⟩ := ih _ (hw ▸ hlt) b' m' rfl hb' ha' hrip' hl'
      exact ⟨t, hr.trans hr', hq⟩

theorem total {F : FunCert9} (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open9.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open9.isa := by
  intro m _ hab he
  obtain ⟨hl, hrip, ha⟩ := hpre m hab he
  exact from_block hc hvc m _ entry m rfl hentry ha hrip hl

end Silmaril.Proofs.Machine.X86.BlockCert9
