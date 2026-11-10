module

public import Silmaril.X86.BlockCert9.Defs
public import Silmaril.X86.Bir9.Thms
public import Silmaril.X86.Open9.Thms

/-!
# Checked block code is a run of `Open9.step`

* `exec_rip`, `exec_mem`: a retired `Ext` instruction that falls through sets `rip` to the
  next instruction; one that writes no memory leaves the memory unchanged (case analysis
  over `Ext.exec`);
* `execNew_rip`, `execNew_mem`: the same for the new `Ext9` forms (case analysis over
  `Ext9.execNew`);
* `runX_open9`: a checked `Ext9` listing that runs is an `Open9` run, memory unchanged;
* `runX_execBlock`: a Bir9 listing of `Ext` and `Ext9` forms runs as the `Ext9` listing it
  denotes;
* `code_run_open9`, `from_block`, `total`: block code, and the assembly of block VCs into a
  total function spec.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.BlockCert9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM retire writeRM writeRM8 writeNarrow aluStep aluStepR readRM
  readNarrow)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86
open Silmaril.X86.BlockCert9

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem map_some {α β : Type} {f : α → β} {x : Option α} {p : β}
    (h : Option.map f x = some p) : ∃ a, f a = p := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, Option.some.inj h⟩

theorem retire_ok {next : Word} {o : Option (State × Memory)} {s : State} {m : Memory}
    (h : retire next o = .ok s m) :
    s.rip = next ∧ ∃ t, o = some (t, m) ∧ s = { t with rip := next } := by
  cases o with
  | none => cases h
  | some p => obtain ⟨t, m'⟩ := p; cases h; exact ⟨rfl, t, rfl, rfl⟩

/-- A retired fall-through instruction continues at the next instruction. -/
theorem exec_rip {i : Silmaril.X86.Ext.Instr} (hf : fallsThrough i = true) {s : State}
    {mem : Memory} {len : Nat} {s' : State} {mem' : Memory}
    (h : Silmaril.X86.Ext.exec i s mem len = .ok s' mem') :
    s'.rip = s.rip + BitVec.ofNat 64 len := by
  cases i
  case unary sz op dst =>
    cases op <;> simp only [Silmaril.X86.Ext.exec] at h <;>
      (repeat' (first | (cases h; done) | exact (retire_ok h).1 | (cases h; rfl) | split at h))
  case cxe sz =>
    cases sz <;> simp only [Silmaril.X86.Ext.exec] at h <;>
      (repeat' (first | (cases h; done) | exact (retire_ok h).1 | (cases h; rfl) | split at h))
  all_goals first | (cases hf; done) | skip
  all_goals simp only [Silmaril.X86.Ext.exec] at h
  all_goals
    (repeat' (first | (cases h; done) | exact (retire_ok h).1 | (cases h; rfl) | split at h))

/-- A retired instruction that writes no memory leaves the memory unchanged. -/
theorem exec_mem {i : Silmaril.X86.Ext.Instr} (hf : noWrite i = true) {s : State}
    {mem : Memory} {len : Nat} {s' : State} {mem' : Memory}
    (h : Silmaril.X86.Ext.exec i s mem len = .ok s' mem') : mem' = mem := by
  cases i
  case unary sz op dst =>
    cases dst with
    | mem => cases hf
    | reg =>
    cases op <;>
      simp only [Silmaril.X86.Ext.exec] at h <;>
      (repeat' (first | (cases h; done) | (cases h; rfl) | split at h)) <;>
      (obtain ⟨_, ho, _⟩ := (retire_ok h).2; simp_all [writeRM])
  case cxe sz =>
    cases sz <;> simp only [Silmaril.X86.Ext.exec] at h <;>
      (obtain ⟨_, ho, _⟩ := (retire_ok h).2; simp_all)
  case' mov sz dst src => cases dst
  case' movI sz dst imm => cases dst
  case' movI16 dst imm => cases dst
  case' movI8 dst imm => cases dst
  case' store n dst src => cases dst
  case' alu sz op dst src => cases dst
  case' aluI sz op dst imm => cases dst
  case' aluI8 sz op dst imm => cases dst
  case' incdec sz dec dst => cases dst
  case' shift sz op dst count => cases dst
  case' setcc c dst => cases dst
  all_goals first | (cases hf; done) | skip
  all_goals simp only [Silmaril.X86.Ext.exec] at h
  all_goals
    (repeat' (first
      | (cases h; done)
      | (cases h; rfl)
      | (obtain ⟨_, ho, _⟩ := (retire_ok h).2
         simp_all [writeRM, writeRM8, aluStep, aluStepR]; done)
      | (obtain ⟨_, ho, _⟩ := (retire_ok h).2
         obtain ⟨_, hh⟩ := map_some ho
         injection hh with _ hm; exact hm.symm)
      | (obtain ⟨_, ho, _⟩ := (retire_ok h).2
         simp only [aluStep, aluStepR, readRM, writeRM, Option.map_some] at ho
         (repeat' split at ho) <;> simp_all; done)
      | split at h))

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
    s'.rip = next ∧ (rmIsReg d = true → mem' = mem) := by
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
    {mem mem' : Memory} {next : Word} (hd : rmIsReg d = true)
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
  case repRet => exact exec_mem (i := .ret) (len := 2) rfl h
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
    | base e => exact exec_rip hf h
    | new _ => cases hf
  | new n => exact execNew_rip hf h

theorem exec9_mem {i : Ext9.Instr} (hf : noWrite9 i = true) {s : State} {mem : Memory}
    {len : Nat} {s' : State} {mem' : Memory} (h : Ext9.exec i s mem len = .ok s' mem') :
    mem' = mem := by
  cases i with
  | ext8 i =>
    cases i with
    | base e => exact exec_mem hf h
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

/-! ## Bir9 listings are `Ext9` listings -/

theorem runX_execBlock (x : Bir9.Xmm) : ∀ (L : List (Bir9.LInstr × Nat))
    (L9 : List (Ext9.Instr × Nat)), Bir9.toX9L L = some L9 → ∀ (m : MState),
    runX L9 m = Bir9.ofX (Bir9.execBlock L ⟨m.core, x⟩ m.memory)
  | [], L9, h, m => by cases h; rfl
  | (i, l) :: rest, L9, h, m => by
    simp only [Bir9.toX9L] at h
    cases hi : Bir9.toX9 i with
    | none => simp [hi] at h
    | some j =>
      cases hr : Bir9.toX9L rest with
      | none => simp [hi, hr] at h
      | some r =>
        simp only [hi, hr, Option.some.injEq] at h
        subst h
        have hexec : ∀ c mem, (i.exec ⟨c, x⟩ mem l) =
            Bir9.liftR x (Ext9.exec j c mem l) := by
          intro c mem
          cases i <;> simp only [Bir9.toX9, reduceCtorEq, Option.some.injEq] at hi <;>
            subst hi <;> rfl
        simp only [runX, Bir9.execBlock, hexec]
        cases Ext9.exec j m.core m.memory l with
        | ok c mem => exact runX_execBlock x rest r hr ⟨c, mem⟩
        | _ => rfl

theorem runX_eq_runL9 {L : List (Bir9.LInstr × Nat)} {L9 : List (Ext9.Instr × Nat)}
    (h : Bir9.toX9L L = some L9) (m : MState) : runX L9 m = Bir9.runL9 L m :=
  runX_execBlock _ L L9 h m

/-- **The bridge for block code.** -/
theorem code_run_open9 {code : List Byte} {base : Word} {c : Code} {o : Nat} {m m' : MState}
    (hok : c.check code o = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : c.run m = some m') :
    Reaches Open9.step m m' ∧ m'.memory = m.memory := by
  cases c with
  | bir L =>
    simp only [Code.check] at hok
    split at hok
    · rename_i L9 h9
      simp only [Code.run, ← runX_eq_runL9 h9] at h
      exact runX_open9 L9 o m m' hok hl hrip h
    · cases hok
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

end Silmaril.Proofs.X86.BlockCert9
