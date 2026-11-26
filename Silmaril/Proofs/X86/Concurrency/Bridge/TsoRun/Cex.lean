module

public import Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Run
public import Silmaril.X86.Litmus.Domain.Thms

/-!
# Gap 1 with `CellsOk` is false (the counterexample, in Lean)

`not_tsoRunCirCells : ¬ tsoRunCirCells`. One thread runs `mov eax, dword
[0x10004]` in a test with no locations, with the condition `exists 0:rax = 5`.

* `tvRun` accepts it with the certificate `load rax, 4, [0x10004]` (`cex_tvOk`), `CondInit`
  holds (no memory atoms), and `CellsOk` holds: every extracted trace has the one-load
  skeleton, so each thread has one footprint (`cex_cellsOk`, by `extract_skel`).
* On the machine (`cex_final`): a test memory may hold `5` at `0x10004`, a byte no location
  fixes; one buffered TSO step loads it, and the drained final state has `rax = 5`.
* In CIR (`cex_cir`): the only unit is the read, so a well-formed candidate takes it from the
  initial memory, which is `0` off the locations; the load returns `0` and `rax = 0`.

The cell check `cellsB` that replaces `CellsOk` in `Task.tsoRunCir` rejects this test: the read
byte is not initialised (`cex_not_cellsB`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Cex

open Silmaril.X86 (State Byte Word)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemoryModel.Litmus (Test Final Atom Cond XTrace finalOf)
open Silmaril.X86.Pool (TPool TsoStep TsoReach overlay atomic9Ev)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (TvTest Cert)
open Silmaril.X86.Concurrency.Bridge

/-- `mov eax, dword [0x10004]`. -/
def code : List Byte := [0x8B, 0x04, 0x25, 0x04, 0x00, 0x01, 0x00]

/-- The test: one thread, no locations, `exists 0:rax = 5`. -/
def cexTest : Test where
  name := "cex-uninit-read"
  source := ""
  doc := ""
  locs := []
  threads := [⟨[⟨"mov eax, dword [0x10004]", code, none⟩], []⟩]
  quant := .exists_
  cond := .atom (.reg 0 .rax 64 5)
  coverage := .tso
  tso := none
  xl := .allowed
  sc := none
  basis := ""

/-- The certificate: one 4-byte CIR load. -/
def cexCert : Cert := ⟨[], [⟨7, [.load .rax .rlx 4 .wb (.lit 0x10004)]⟩]⟩

def cex : TvTest := ⟨cexTest, [cexCert]⟩

theorem cex_tvOk : cex.tvOk = true := by decide +kernel

theorem cex_condInit : CondInit cex.test := by
  intro a n v h
  simp [cex, cexTest, Cond.atoms] at h

theorem cex_not_cellsB : cellsB cex.test = false := by decide +kernel

/-- The thread, as the litmus extractor extracts it. -/
def th : Silmaril.X86.MemoryModel.Litmus.Thread := ⟨[⟨"mov eax, dword [0x10004]", code, none⟩], []⟩

/-- The load event. -/
def ldEv : MemEvent.Event := ⟨.load, 0x10004, 4, false⟩

theorem skel : (cexTest.xthread 0 th).skel 1 = some [[ldEv]] := by decide +kernel

/-- **The cell condition holds**: every extracted trace is one load. -/
theorem cex_cellsOk : CellsOk cex.test := by
  intro D T hT trs hF
  have h0 := mapM_id_get hT 0
  have h1 := mapM_id_get hT 1
  simp only [cex, cexTest, List.mapIdx_cons, List.mapIdx_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.getElem?_nil] at h0 h1
  cases hT0 : T[0]? with
  | none => rw [hT0] at h0; cases h0
  | some trs0 =>
    rw [hT0] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    have hlen : T.length = 1 := by
      have : T.length ≤ 1 := by
        by_contra hc
        have := List.getElem?_eq_getElem (l := T) (i := 1) (by omega)
        rw [this] at h1; cases h1
      have : 0 < T.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hT0; cases hT0
      omega
    obtain ⟨T0, rfl⟩ : ∃ T0, T = [T0] := by
      match T, hlen with
      | [T0], _ => exact ⟨T0, rfl⟩
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hT0
    subst hT0
    obtain ⟨tr, rfl, htr⟩ : ∃ tr, trs = [tr] ∧ tr ∈ T0 := by
      cases hF with
      | cons h t => cases t; exact ⟨_, rfl, h⟩
    have hsk := Silmaril.X86.Litmus.extract_skel h0 skel tr htr
    obtain ⟨r, hr⟩ : ∃ r, tr.steps = [r] := by
      rcases hs : tr.steps with _ | ⟨r, _ | ⟨r', rs⟩⟩
      · rw [hs] at hsk; simp at hsk
      · exact ⟨r, rfl⟩
      · rw [hs] at hsk; simp at hsk
    rw [hr] at hsk
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsk
    obtain ⟨a, ha, hae⟩ : ∃ a, r.acts = [a] ∧ a.ev = ldEv := by
      rcases hs : r.acts with _ | ⟨a, _ | ⟨a', as⟩⟩
      · rw [hs] at hsk; simp at hsk
      · rw [hs] at hsk; exact ⟨a, rfl, by simpa using hsk⟩
      · rw [hs] at hsk; simp at hsk
    intro i es hes ev₁ h₁ ev₂ h₂ p₁ hp₁ p₂ hp₂ _
    cases i with
    | succ i => simp at hes
    | zero =>
      simp only [List.mapIdx_cons, List.mapIdx_nil, List.getElem?_cons_zero,
        Option.some.injEq] at hes
      subst hes
      have hx : Silmaril.X86.MemoryModel.Litmus.traceX 0 tr =
          [.load 0 0x10004 a.rd] := by
        simp [Silmaril.X86.MemoryModel.Litmus.traceX, Silmaril.X86.Litmus.Trace.acts, hr, ha,
          Silmaril.X86.MemoryModel.Litmus.actX, hae, ldEv]
      rw [hx] at h₁ h₂
      simp only [List.mem_singleton] at h₁ h₂
      subst h₁ h₂
      simp only [Silmaril.X86.MemoryModel.OpAx.footOf, List.mem_singleton] at hp₁ hp₂
      rw [hp₁, hp₂]

/-! ## The machine side: the load reads `5` -/

/-- The data page: `5` at `0x10004`, zeros elsewhere. -/
def dataPage : List (BitVec 8) := [0, 0, 0, 0, 5, 0, 0, 0] ++ List.replicate 4088 0

/-- The code page. -/
def codePage : List (BitVec 8) := code ++ List.replicate 4089 0

/-- A one-thread test memory. -/
def mem : Memory := ⟨Silmaril.X86.Litmus.testRegions 1,
  Memory.install (Memory.install ∅ 0x400000 codePage) 0x10000 dataPage⟩

/-- The operand `[0x10004]`. -/
def dMem : Silmaril.X86.Ext.Mem :=
  { base := .none, index := none, disp := 0x10004#32, rip_no_index := by decide }

/-- The instruction. -/
def insn : Atomic9.Instr := .open9 (.ext8 (.base (.load .d .rax dMem)))

/-- The thread's initial core. -/
def init : State := (cexTest.xthread 0 th).init

/-- The core after the load. -/
def post : State :=
  { Silmaril.X86.Ext.Sz.write .d init .rax
      ((BitVec.ofNat 64 (Silmaril.X86.Ext.leValue [5, 0, 0, 0])).setWidth
        Silmaril.X86.Ext.Sz.d.bits) with
    rip := init.rip + BitVec.ofNat 64 7 }

theorem dataPage_len : dataPage.length = 4096 := by
  rw [dataPage, List.length_append, List.length_replicate]; rfl

theorem codePage_len : codePage.length = 4096 := by
  rw [codePage, List.length_append, List.length_replicate]; rfl

theorem get_code (i : Nat) (hi : i < 4096) :
    mem.bytes.get? (0x400000 + i) = some (codePage[i]'(by rw [codePage_len]; exact hi)) := by
  show (Memory.install (Memory.install ∅ 0x400000 codePage) 0x10000 dataPage).get? _ = _
  rw [Memory.install_outside _ _ _ _ (.inr (by rw [dataPage_len]; omega)),
    Memory.install_get _ _ _ _ (by rw [codePage_len]; exact hi)]

theorem get_data (i : Nat) (hi : i < 4096) :
    mem.bytes.get? (0x10000 + i) = some (dataPage[i]'(by rw [dataPage_len]; exact hi)) := by
  show (Memory.install (Memory.install ∅ 0x400000 codePage) 0x10000 dataPage).get? _ = _
  rw [Memory.install_get _ _ _ _ (by rw [dataPage_len]; exact hi)]

theorem backed : Backed mem := by
  intro a ha
  simp only [Memory.permits, mem] at ha
  simp [Silmaril.X86.Litmus.testRegions, Silmaril.Process.Region.Contains,
    Silmaril.X86.Litmus.dataBase, Silmaril.X86.Litmus.dataSize,
    Silmaril.Process.Permissions.allows] at ha
  rcases ha with ha | ha
  · have := of_decide_eq_true ha
    have := get_data (a - 0x10000) (by omega)
    rw [show 0x10000 + (a - 0x10000) = a by omega] at this
    rw [this]; rfl
  · have := of_decide_eq_true ha
    have := get_code (a - 0x400000) (by omega)
    rw [show 0x400000 + (a - 0x400000) = a by omega] at this
    rw [this]; rfl

theorem rb_code (n i : Nat) (h : i + n ≤ 4096) :
    Memory.readBacking mem.bytes (0x400000 + i) n = some ((codePage.drop i).take n) := by
  induction n generalizing i with
  | zero => simp [Memory.readBacking]
  | succ n ih =>
    simp only [Memory.readBacking, get_code i (by omega), Option.bind_eq_bind, Option.bind_some]
    rw [show 0x400000 + i + 1 = 0x400000 + (i + 1) by omega, ih (i + 1) (by omega)]
    rw [List.drop_eq_getElem_cons (i := i) (by rw [codePage_len]; omega)]
    rfl

theorem rb_data (n i : Nat) (h : i + n ≤ 4096) :
    Memory.readBacking mem.bytes (0x10000 + i) n = some ((dataPage.drop i).take n) := by
  induction n generalizing i with
  | zero => simp [Memory.readBacking]
  | succ n ih =>
    simp only [Memory.readBacking, get_data i (by omega), Option.bind_eq_bind, Option.bind_some]
    rw [show 0x10000 + i + 1 = 0x10000 + (i + 1) by omega, ih (i + 1) (by omega)]
    rw [List.drop_eq_getElem_cons (i := i) (by rw [dataPage_len]; omega)]
    rfl

theorem loaded : Loaded mem (cexTest.xthread 0 th).base (cexTest.xthread 0 th).code := by
  simp only [Loaded, Memory.fetchBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  exact rb_code 7 0 (by omega)

theorem read : mem.readBytes 0x10004 4 = some [5, 0, 0, 0] := by
  simp only [Memory.readBytes, Memory.readWith]
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  exact rb_data 4 4 (by omega)

theorem exec : Atomic9.exec insn init mem 7 = .ok post mem := by
  simp only [insn, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.loadN]
  rw [show (Silmaril.X86.Ext.Mem.addr dMem init (init.rip + BitVec.ofNat 64 7)).toNat = 0x10004 by
      decide +kernel,
    show Silmaril.X86.Ext.Sz.d.bytes = 4 from rfl, read]
  rfl

theorem fetch : MemEvent.atomic9Fetch mem init.rip.toNat = some (insn, 7) :=
  Atomic9.fetch_of_listed_base (o := 0) loaded (by decide +kernel) (by decide) (by decide +kernel)

/-- The pool after the load: thread `0` at `post`, nothing buffered. -/
def p1 : TPool Nat where
  threads := Function.update (testPool cexTest mem).threads 0 (some post)
  memory := (testPool cexTest mem).memory
  buffer := Function.update (testPool cexTest mem).buffer 0
    ((testPool cexTest mem).buffer 0 ++
      Silmaril.X86.Pool.storeEntries (atomic9Ev.accesses insn init 7) mem)

theorem hnf : ¬ TestFin cexTest 0 init := fun h => absurd (h th rfl) (by decide +kernel)

theorem syncs_false :
    Silmaril.X86.Pool.syncs (atomic9Ev.accesses insn init 7) = false := by decide +kernel

theorem tsoStep : TsoStep atomic9Ev (TestFin cexTest) (testPool cexTest mem) 0 p1 :=
  @TsoStep.buffered Nat _ atomic9Ev (TestFin cexTest) (testPool cexTest mem) 0 init post insn 7 mem
    rfl hnf fetch syncs_false exec

theorem entries_nil :
    Silmaril.X86.Pool.storeEntries (atomic9Ev.accesses insn init 7) mem = [] := by
  simp [Silmaril.X86.Pool.storeEntries, atomic9Ev, insn,
    MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses, MemEvent.extAccesses,
    MemEvent.memEv, MemEvent.Kind.writes]

/-- **The machine reaches `rax = 5`.** -/
theorem cex_final : TsoFinal cex.test (poolFinal p1) := by
  refine ⟨mem, p1, ⟨rfl, ?_, ?_, backed⟩, Relation.ReflTransGen.single (.inl ⟨0, tsoStep⟩),
    ?_, ?_, rfl⟩
  · intro k th' h
    cases k with
    | zero =>
      simp only [cex, cexTest, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact loaded
    | succ k => simp [cex, cexTest] at h
  · intro a b h
    simp [cex, cexTest, Test.initMem, Silmaril.X86.MemoryModel.Litmus.initByte] at h
  · intro t
    by_cases ht : t = 0
    · subst ht
      simp [p1, entries_nil, testPool]
    · simp [p1, ht, testPool]
  · intro k s h th' hth
    cases k with
    | zero =>
      simp only [p1, Function.update_self, Option.some.injEq] at h
      subst h
      simp only [cex, cexTest, List.getElem?_cons_zero, Option.some.injEq] at hth
      subst hth
      decide +kernel
    | succ k => simp [cex, cexTest] at hth

theorem cex_witness : cex.test.witness.eval (poolFinal p1) = true := by
  simp only [Test.witness, cex, cexTest, Cond.eval, Atom.eval, poolFinal, p1,
    Function.update_self, Option.map_some, Option.getD_some]
  decide +kernel

/-! ## The CIR side: the load reads `0` -/

theorem cex_cir {f' : Final} (h : Behav cex.prog Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso f') :
    cex.test.witness.eval f' = false := by
  obtain ⟨D, trs, hF, x, hev, -, -, hro, -, rfl⟩ := h
  have ht : cex.prog.traces D =
      [(run D cexCert.body Regs.zero).map (Thread.xtrace ⟨cexCert.body, false⟩ 0)] := rfl
  rw [ht] at hF
  obtain ⟨tr, rfl, htr⟩ : ∃ tr, trs = [tr] ∧
      tr ∈ (run D cexCert.body Regs.zero).map (Thread.xtrace ⟨cexCert.body, false⟩ 0) := by
    cases hF with
    | cons h t => cases t; exact ⟨_, rfl, h⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp htr
  simp [cexCert, Cert.body, Cert.ops, Cert.proOps, Silmaril.X86.Concurrency.Cir.Tv.chain, run,
    Res.bind, pick] at hq
  obtain ⟨v, ⟨hvD, hv⟩, rfl⟩ := hq
  simp [Silmaril.X86.MemoryModel.Litmus.units, Silmaril.X86.MemoryModel.Litmus.accUnits,
    Silmaril.X86.MemoryModel.Litmus.threadUnits, Silmaril.X86.MemoryModel.Litmus.actUnits,
    Thread.xtrace, Thread.acts, Lab.acts, ldAct, Silmaril.X86.Litmus.Trace.acts,
    Silmaril.X86.MemoryModel.Litmus.tearAcc, Expr.eval, Silmaril.X86.MemoryModel.Axiomatic.Ev.isM,
    Silmaril.X86.MemoryModel.Axiomatic.Ev.isR, Silmaril.X86.MemoryModel.Axiomatic.Ev.isW,
    Silmaril.X86.MemoryModel.Axiomatic.Ev.singleCopy] at hev hro
  have hb : ∀ y, x.readByte cex.prog.memTest.initB 0 y = 0 := by
    intro y
    unfold Silmaril.X86.MemoryModel.Axiomatic.Exec.readByte
    cases x.rf 0 y with
    | none =>
      simp [Test.initB, Prog.memTest, Test.initMem, Silmaril.X86.MemoryModel.Litmus.initByte, cex,
        TvTest.prog, cexTest]
    | some w =>
      cases w <;>
        simp [Silmaril.X86.MemoryModel.Axiomatic.Exec.evN, hev, Silmaril.X86.MemoryModel.Axiomatic.Ev.byte]
  have h0 := hro 0 (by simp [Silmaril.X86.MemoryModel.Axiomatic.Exec.n, hev])
    (by simp [Silmaril.X86.MemoryModel.Axiomatic.Exec.evN, hev, Silmaril.X86.MemoryModel.Axiomatic.Ev.isR])
  simp only [Silmaril.X86.MemoryModel.Axiomatic.Exec.readBytes, List.getD_cons_zero] at h0
  simp [Silmaril.X86.MemoryModel.Axiomatic.Exec.evN, hev, Silmaril.X86.MemoryModel.Axiomatic.Ev.bytes,
    natBytes, List.range', List.range_succ, hb] at h0
  have hv0 : v = 0 := by
    obtain ⟨e0, e1, e2, e3⟩ := h0
    have t0 := congrArg BitVec.toNat e0
    have t1 := congrArg BitVec.toNat e1
    have t2 := congrArg BitVec.toNat e2
    have t3 := congrArg BitVec.toNat e3
    simp only [BitVec.toNat_ofNat] at t0 t1 t2 t3
    omega
  subst hv0
  simp [Test.witness, cex, cexTest, Cond.eval, Atom.eval, Silmaril.X86.MemoryModel.Litmus.finalAx,
    finalOf, Thread.xtrace, coreOf, Regs.set, Silmaril.X86.State.read]

/-- **The statement of gap 1 is false** (the counterexample). -/
theorem not_tsoRunCirCells : ¬ tsoRunCirCells := by
  intro hT
  obtain ⟨f', hb, heq⟩ := hT cex cex_tvOk cex_cellsOk cex_condInit _ cex_final
  rw [cex_cir hb, cex_witness] at heq
  cases heq

end Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Cex
