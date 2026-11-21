module

public import Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Cells
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
public import Silmaril.X86.Concurrency.Cir.Tv.Corpus.Defs

/-!
# Gap 1: concurrent x86 runs are CIR behaviours (`Bridge.Task.tsoRunCir`)

`tsoRunCir_holds`. A final state of the TSO pool over a validated test's bytes
(`TsoFinal`):

1. the run is recorded, keeps the memory invariant, and every thread's history is a symbolic
   run of the thread from its initial core (`reach_inv`, `tvRunDefined_holds` and
   `xstep_of_step` on each view);
2. every thread has finished, so each history is a run of the CIR thread over the values read
   (`tvRun_xrun`);
3. the cell check `cellsB` places every access at a skeleton event (`xrun_skel`), which gives
   `ThreadCells`, `NoTear` and `InitReads`;
4. `axReach_of_runA` (with `run_explains_tso_paired`) makes the final state an
   x86-TSO `AxReach` state of the threads' traces, and `axReach_pick` moves it to the CIR
   traces (`threadUnits_normActs`), i.e. a CIR behaviour (`BehavIn`);
5. the witness agrees: observed registers are not clobbered (`condAvoids`), observed bytes are
   initialised (`CondInit`), so an unwritten one holds its initial value on both sides.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun

open Silmaril.X86 (State Byte Word)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (Act)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test actX threadUnits Atom finalOf)
open Silmaril.X86.Pool (TPool TsoReach atomic9Ev)
open Silmaril.X86.Concurrency.Bridge
open Silmaril.X86.Concurrency.Bridge.PoolRun
open Silmaril.X86.Concurrency.Cir.TvCfg (XStep XRun)
open Silmaril.X86.Concurrency.Cir.Tv (XThread TvTest)

theorem leValue_congr {g g' : Nat → Option Byte} :
    ∀ (n a : Nat), (∀ j < n, g (a + j) = g' (a + j)) →
      Silmaril.X86.MemoryModel.Litmus.leValue g a n = Silmaril.X86.MemoryModel.Litmus.leValue g' a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have ih := leValue_congr (g := g) (g' := g') n (a + 1) fun j hj => by
      have := h (j + 1) (by omega)
      rw [show a + (j + 1) = a + 1 + j by omega] at this
      exact this
    simp only [Silmaril.X86.MemoryModel.Litmus.leValue, h0, ih]

theorem trace_acts (os : List Obs) (fin : State) :
    (Obs.trace os fin).acts = (os.map Obs.acts).flatten := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [Obs.trace, Silmaril.X86.Litmus.Trace.acts, List.map_cons, List.flatMap_cons,
      List.flatten_cons] at ih ⊢
    rw [ih]

theorem forall₂_singletons {α : Type} : ∀ l : List α, List.Forall₂ (· ∈ ·) l (l.map fun x => [x])
  | [] => .nil
  | a :: l => .cons (by simp) (forall₂_singletons l)

theorem avoids {cond : Silmaril.X86.MemoryModel.Litmus.Cond} {Ks : List (List Silmaril.X86.Reg)}
    (h : Silmaril.X86.Concurrency.Cir.Tv.condAvoids cond Ks = true) {i : Nat}
    {r : Silmaril.X86.Reg} {b v : Nat} (ha : Atom.reg i r b v ∈ cond.atoms) : r ∉ Ks.getD i [] := by
  unfold Silmaril.X86.Concurrency.Cir.Tv.condAvoids at h
  have := List.all_eq_true.mp h _ ha
  simpa using this

/-- A memory unit of the litmus units of a choice of traces is at a memory action's footprint. -/
theorem unit_acc {trs : List XTrace} {u : Silmaril.X86.MemoryModel.Axiomatic.Ev × List Byte}
    (hu : u ∈ Silmaril.X86.MemoryModel.Litmus.accUnits trs) (hm : u.1.isM = true) :
    ∃ tr ∈ trs, ∃ a ∈ tr.acts, u.1.addr = a.ev.addr ∧ u.1.size = a.ev.size ∧
      u.1.accAddr = a.ev.addr ∧ u.1.accSize = a.ev.size ∧
      (a.ev.kind.reads || a.ev.kind.writes) = true := by
  obtain ⟨l, hl, hu⟩ := List.mem_flatten.mp hu
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hl
  exact ⟨trs[i], List.getElem_mem hi, unit_of_threadUnits hu hm⟩

/-- **Gap 1** (`Bridge.Task.tsoRunCir`, as restated here). -/
theorem tsoRunCir_holds : Task.tsoRunCir := by
  intro c hok hcb hci f hf
  obtain ⟨m₀, p, hm, hreach, hd, hfin, rfl⟩ := hf
  obtain ⟨H, hr, -, hti⟩ := reach_inv hok hm hreach
  obtain ⟨Ks, -, havoid, hlen, hKs⟩ := tvRun_of_tvOk hok
  obtain ⟨Ss, hP⟩ := cellsP_of hcb
  let fin : Nat → State := fun k =>
    (p.threads k).getD (Silmaril.X86.Concurrency.Cir.coreOf Silmaril.X86.Concurrency.Cir.Regs.zero)
  have hthr : ∀ k th, c.test.threads[k]? = some th → p.threads k = some (fin k) ∧
      XRun (c.test.xthread k th) (c.test.xthread k th).init ((H k).map Obs.acts) (fin k) ∧
      (fin k).rip = (c.test.xthread k th).endRip := by
    intro k th hth
    obtain ⟨s, hs, hx⟩ := hti.run k th hth
    have hfk : fin k = s := by simp [fin, hs]
    rw [hfk]
    exact ⟨hs, hx, hfin k s hs th hth⟩
  have hnone : ∀ k, c.test.threads.length ≤ k → p.threads k = none := fun k hk =>
    hti.none k (List.getElem?_eq_none hk)
  let N := c.test.threads.length
  let trs := poolTraces N H fin
  have hlenT : trs.length = N := by simp [trs, poolTraces]
  have hget : ∀ k (hk : k < N), trs[k]? = some (Obs.trace (H k) (fin k)) := by
    intro k hk; simp [trs, poolTraces, hk]
  have hok' : TracesOk trs := tracesOk_pool hr N fin
  -- every memory action is at a skeleton event
  have hacts : ∀ tr ∈ trs, ∀ a ∈ tr.acts, (a.ev.kind.reads || a.ev.kind.writes) = true →
      a.ev ∈ memEvs Ss := by
    intro tr htr a ha hm'
    simp only [trs, poolTraces, List.mem_map, List.mem_range] at htr
    obtain ⟨k, hk, rfl⟩ := htr
    have hth : c.test.threads[k]? = some c.test.threads[k] := List.getElem?_eq_getElem hk
    obtain ⟨-, hx, he⟩ := hthr k _ hth
    obtain ⟨S, hS, hsk⟩ := skel_get hP.skels hth
    have := xrun_skel (Bridge.tvRun_len (hKs k _ hth)) hx he hsk
    rw [trace_acts] at ha
    exact act_memEvs hS this ha hm'
  -- (5) cells within each thread
  have hC : Silmaril.X86.MemoryModel.OpAx.ThreadCells (poolProg N H) := by
    rw [poolProg_eq N H fin]
    intro i es hes ev₁ h₁ ev₂ h₂ p₁ hp₁ p₂ hp₂ hov
    rw [List.getElem?_mapIdx] at hes
    cases htr : trs[i]? with
    | none => simp [trs, htr] at hes
    | some tr =>
      simp only [trs] at htr
      rw [htr] at hes
      simp only [Option.map_some, Option.some.injEq] at hes
      subst hes
      have htm : tr ∈ trs := List.mem_of_getElem? htr
      simp only [Silmaril.X86.MemoryModel.Litmus.traceX] at h₁ h₂
      obtain ⟨a₁, ha₁, he₁⟩ := List.mem_flatMap.mp h₁
      obtain ⟨a₂, ha₂, he₂⟩ := List.mem_flatMap.mp h₂
      obtain ⟨rfl, hm₁⟩ := foot_of_actX (hok' tr htm a₁ ha₁) he₁ hp₁
      obtain ⟨rfl, hm₂⟩ := foot_of_actX (hok' tr htm a₂ ha₂) he₂ hp₂
      obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := hov
      rcases hP.disj _ (hacts tr htm a₁ ha₁ hm₁) _ (hacts tr htm a₂ ha₂ hm₂) with
        ⟨e₁, e₂⟩ | h | h
      · simp [e₁, e₂]
      · simp only at hy₁ hy₂ hy₃ hy₄; omega
      · simp only at hy₁ hy₂ hy₃ hy₄; omega
  -- no access tears
  have hnt : NoTear trs := by
    intro u hu
    unfold Silmaril.X86.MemoryModel.Litmus.tearAcc
    cases hM : u.1.isM
    · rfl
    obtain ⟨tr, htr, a, ha, h1, h2, h3, h4, hma⟩ := unit_acc hu hM
    have hae := hacts tr htr a ha hma
    obtain ⟨h0, h8, hal⟩ := hP.sc _ hae
    rw [Bool.true_and, Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · simp [Silmaril.X86.MemoryModel.Axiomatic.Ev.singleCopy, h3, h4, h8, hal]
    · rw [List.any_eq_false]
      intro v hv hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hvM, hov⟩, hne⟩ := hc
      obtain ⟨tr', htr', b, hb, g1, g2, g3, g4, hmb⟩ := unit_acc hv hvM
      have hbe := hacts tr' htr' b hb hmb
      simp only [Silmaril.X86.MemoryModel.Axiomatic.Ev.accOverlap, Bool.and_eq_true,
        decide_eq_true_eq] at hov
      rcases hP.disj _ hae _ hbe with ⟨e₁, e₂⟩ | h | h
      · rw [h1, g1, e₁, h2, g2, e₂] at hne
        simp at hne
      · rw [h3, h4, g3, g4] at hov; omega
      · rw [h3, h4, g3, g4] at hov; omega
  -- reads see the test's initial bytes
  have hI : InitReads c.prog.memTest (fun a => (testPool c.test m₀).memory.bytes[a]?) trs := by
    intro tr htr a ha hrd y hy₁ hy₂
    have hm' := hacts tr htr a ha (by simp [hrd])
    have := hP.init _ hm' hrd (y - a.ev.addr) (by omega)
    rw [show a.ev.addr + (y - a.ev.addr) = y by omega] at this
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp this
    have hmb := hm.2.2.1 y b hb
    show (m₀.bytes[y]?).getD 0 = (Silmaril.X86.MemoryModel.Litmus.initByte c.test.locs y).getD 0
    rw [← Std.ExtHashMap.get?_eq_getElem?, hmb,
      show Silmaril.X86.MemoryModel.Litmus.initByte c.test.locs y = c.test.initMem y from rfl, hb]
  -- (4)-(6): an x86-TSO state of the threads' traces
  have hN0 : ∀ t, N ≤ t → (testPool c.test m₀).threads t = none := by
    intro t ht; simp [testPool, List.getElem?_eq_none ht]
  obtain ⟨m, hax, hmem⟩ := axReach_of_runA hr (fun _ => rfl) hN0 hd hC fin
    (forall₂_singletons trs) hnt hI
  -- the CIR traces
  let D := (List.range N).flatMap fun k =>
    Silmaril.X86.Concurrency.Cir.Tv.actVals ((H k).map Obs.acts)
  have hl : (trs.map fun tr => [tr]).length = (c.prog.traces D).length := by
    simp [hlenT, Silmaril.X86.Concurrency.Cir.Prog.traces, TvTest.prog, hlen, N]
  obtain ⟨f', hf', hfm, hfr⟩ := Silmaril.X86.Concurrency.Cir.Tv.axReach_pick (Ks := Ks) hl
    (fun k h₁ h₂ a ha => by
      have hk : k < N := by simpa [hlenT] using h₁
      have hkc : k < c.certs.length := hlen ▸ hk
      have hth : c.test.threads[k]? = some c.test.threads[k] := List.getElem?_eq_getElem hk
      have hak : a = Obs.trace (H k) (fin k) := by
        have := hget k hk
        simp only [List.getElem_map, List.mem_singleton] at ha
        rw [ha]
        exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
      subst hak
      obtain ⟨-, hx, he⟩ := hthr k _ hth
      obtain ⟨q, hq, hnorm, hreg⟩ := Silmaril.X86.Concurrency.Cir.Tv.tvRun_xrun (hKs k _ hth)
        hx he (D := D) fun acts hacts a ha hrd =>
          List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_map.mpr
            ⟨a, List.mem_filter.mpr ⟨List.mem_flatten.mpr ⟨acts, hacts, ha⟩, hrd⟩, rfl⟩⟩
      have hcert : c.cert k = c.certs[k] := by
        simp [TvTest.cert, List.getD_eq_getElem?_getD, hkc]
      rw [hcert] at hq
      refine ⟨Silmaril.X86.Concurrency.Cir.Thread.xtrace ⟨c.certs[k].body, false⟩ k q, ?_, ?_, ?_⟩
      · simp only [Silmaril.X86.Concurrency.Cir.Prog.traces, TvTest.prog, List.getElem_mapIdx,
          List.getElem_map]
        exact List.mem_map_of_mem hq
      · rw [trace_acts]
        simp only [Silmaril.X86.Concurrency.Cir.Thread.xtrace, Silmaril.X86.Litmus.Trace.acts,
          Silmaril.X86.Concurrency.Cir.Thread.acts, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, Bool.false_eq_true, ite_false, List.nil_append]
        rw [← hnorm, Silmaril.X86.Concurrency.Cir.Tv.threadUnits_normActs]
      · intro r hr
        exact hreg r hr) hax
  refine ⟨f', ⟨D, hf'⟩, ?_⟩
  -- the witness
  apply Silmaril.X86.Concurrency.Cir.Tv.cond_eval_congr
  intro at' hat
  rw [Silmaril.X86.Concurrency.Cir.Tv.witness_atoms] at hat
  cases at' with
  | reg i r bits v =>
    simp only [Atom.eval]
    rw [hfr i r (avoids havoid hat)]
    simp only [finalOf, poolFinal]
    by_cases hi : i < N
    · rw [hget i hi, (hthr i _ (List.getElem?_eq_getElem hi)).1]
      rfl
    · have h1 : trs[i]? = none := List.getElem?_eq_none (by omega)
      rw [h1, hnone i (by omega)]
      rfl
  | mem a n v =>
    simp only [Atom.eval]
    rw [hfm]
    simp only [finalOf, poolFinal]
    rw [leValue_congr n a fun j hj => ?_]
    rcases hmem (a + j) with h | ⟨h, h'⟩
    · rw [h, Std.ExtHashMap.get?_eq_getElem?]
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hci a n v hat j hj)
      have hmb := hm.2.2.1 _ b hb
      rw [Std.ExtHashMap.get?_eq_getElem?, h']
      show _ = m₀.bytes[a + j]?
      rw [← Std.ExtHashMap.get?_eq_getElem?, hmb, h]
      exact hb

/-- **Every corpus test passes the cell check** (all 60 translation-validated tests). -/
theorem corpus_cellsB :
    ∀ c ∈ Silmaril.X86.Concurrency.Cir.Tv.Corpus.all, cellsB c.test = true := by
  have h : Silmaril.X86.Concurrency.Cir.Tv.Corpus.all.all (fun c => cellsB c.test) = true := by
    decide +kernel
  intro c hc
  exact List.all_eq_true.mp h c hc

end Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun
