module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Parts
public import Silmaril.X86.Concurrency.Cir.Litmus.Thms

/-!
# Localisation: the earlier statement is false

`Tv.Task.cirLocalize` as first stated (`CirLocalizeFirst`, with its
`avoidsFirst`, which compared literal addresses without reducing them modulo `2 ^ 64`) is refuted
three ways; each counterexample breaks exactly one added hypothesis:

* `not_cirLocalizeFirst_ghost`: a location at the futex queue byte `qAddr 0`; another thread's
  `futexWake 0 1` empties it between the fragment's store and load (cells below `ctlAddr 0`);
* `not_cirLocalizeFirst_wrap`: another thread stores at `x + 2 ^ 64`, which is `x` (exact
  `Stmt.avoids`);
* `not_cirLocalizeFirst_xlWeak`: `load rax z; [load rbx x]; sfence; store.nt y 1` against
  `store y 2; store z 1`: XL allows `rax = 1, rbx = 0, y = 2`; with the fragment replaced by a
  block that writes `x` back, the block's write orders the load of `z` before the non-temporal
  store (`ppoXl` then `sfenceXl`), and XL forbids it (write-back stores after the fragment,
  under XL).

In the first two, the program has an SC behaviour with `rax = 0` (the CIR enumerator,
`CTest.check`), while every run of the localised thread ends with `rax = 1` (the block's
contract). In the third, both verdicts come from the enumerator, and every localised behaviour
with the same final registers is one over the test's domain (`weak_restrict`).
`ghost_breaks_only_ctl`, `wrap_breaks_only_avoids` and `weak_breaks_only_wb` check that each
counterexample breaks only the hypothesis it is about.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (chain cellsDisjoint)
open Silmaril.X86.MemoryModel.Litmus (Final Loc Model Test Cond Atom Verdict XTrace finalAx finalOf
  AxReach)

/-- The first `Stmt.avoids`: literal addresses compared as they are. -/
def avoidsFirst (cs : List (Nat × Nat)) : Stmt → Bool
  | .load _ _ sz _ (.lit a) | .store _ sz _ (.lit a) _ | .rmw _ _ sz _ (.lit a) _ =>
    cs.all (cellsDisjoint (a, sz))
  | .futexWait _ (.lit a) _ => cs.all (cellsDisjoint (a, 4))
  | .load .. | .store .. | .rmw .. | .futexWait .. => false
  | .local b => (b.ins ++ b.outs).all fun c => cs.all (cellsDisjoint c)
  | .seq s t | .ite _ s t => avoidsFirst cs s && avoidsFirst cs t
  | .loop _ _ b => avoidsFirst cs b
  | _ => true

/-- `Tv.Task.cirLocalize` as first stated. -/
def CirLocalizeFirst : Prop :=
  ∀ (P : Prog) (i : Nat) (pre ops post : List Stmt) (B : Block),
    P.threads[i]? = some ⟨chain (pre ++ ops ++ post), false⟩ →
    B.cellsOk = true →
    (ops.all fun s => s.onCells (B.ins ++ B.outs) && s.storesWithin B.outs && s.threadFree &&
      s.futexFree) = true →
    (∀ c ∈ B.ins ++ B.outs, ∃ l ∈ P.locs, l.addr ≤ c.1 ∧ c.1 + c.2 ≤ l.addr + l.size) →
    ((pre ++ post).all (avoidsFirst (B.ins ++ B.outs))) = true →
    (∀ j th, j ≠ i → P.threads[j]? = some th → avoidsFirst (B.ins ++ B.outs) th.body = true) →
    (∀ s ∈ ops, ∀ r ∈ s.writes, r ∈ B.rout) →
    (∀ rs m tr rs' m', SeqRun (chain ops) rs m tr rs' m' →
      B.spec (B.rin.map (fun r => (rs r).toNat) ++ B.ins.map fun c => (m.val c.1 c.2).getD 0)
        (B.rout.map (fun r => (rs' r).toNat) ++ B.outs.map fun c => (m'.val c.1 c.2).getD 0)) →
    ∀ (M : Model) (f : Final), Behav P M.Holds f →
      ∃ f', Behav ⟨P.locs, P.threads.set i ⟨chain (pre ++ [.local B] ++ post), false⟩⟩ M.Holds f' ∧
        f'.mem = f.mem ∧ f'.regs = f.regs

/-! ## The shared shape: store `1`, load it back -/

/-- The block of `store a 1; load rax a` (`sz` bytes): `rax` and the cell end as `1`. -/
def oneBlk (a sz : Nat) : Block where
  name := "one"
  ins := [(a, sz)]
  outs := [(a, sz)]
  rin := []
  rout := [.rax]
  spec := fun _ o => o = [1, 1]
  dec := fun _ _ => inferInstance

/-- The fragment. -/
def oneOps (a sz : Nat) : List Stmt :=
  [.store .rlx sz .wb (.lit a) (.lit 1), .load .rax .rlx sz .wb (.lit a)]

theorem oneOps_spec (a sz : Nat) (ha : a < 2 ^ 64) (hsz : 0 < sz) :
    ∀ rs m tr rs' m', SeqRun (chain (oneOps a sz)) rs m tr rs' m' →
      (oneBlk a sz).spec ((oneBlk a sz).rin.map (fun r => (rs r).toNat) ++
        (oneBlk a sz).ins.map fun c => (m.val c.1 c.2).getD 0)
        ((oneBlk a sz).rout.map (fun r => (rs' r).toNat) ++
          (oneBlk a sz).outs.map fun c => (m'.val c.1 c.2).getD 0) := by
  intro rs m tr rs' m' ⟨⟨dom, hrun⟩, hrep⟩
  simp only [oneOps, chain, run, Res.bind, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.mem_flatMap, List.mem_map, List.mem_singleton,
    Prod.mk.injEq] at hrun
  obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, htr, hrs⟩ := hrun
  subst htr hrs
  have hv' := mem_pick hv
  have h1 : (1 : Nat) % 2 ^ (8 * sz) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have ha' : a % 2 ^ 64 = a := Nat.mod_eq_of_lt ha
  have h1' : (1 : Nat) % 2 ^ 64 = 1 := by decide
  simp only [Expr.eval, BitVec.toNat_ofNat, ha', h1', h1, List.singleton_append, replay,
    Lab.replay, Option.bind_some] at hrep
  split at hrep
  · rename_i hval
    simp only [Option.bind_some, Option.some.injEq] at hrep
    subst hrep
    have hv1 : v = 1 := by
      have := (val_iff (m.put a sz 1) a sz 1 (Nat.one_lt_two_pow (by omega))).mpr
        (by
          simp only [Seq.bytesAt, Mem.put, natBytes]
          apply List.ext_getElem (by simp)
          intro j hj _
          simp at hj
          simp [show a ≤ a + j by omega, show a + j < a + sz by omega])
      rw [this] at hval; cases hval; rfl
    subst hv1
    have := (val_iff (m.put a sz 1) a sz 1 (Nat.one_lt_two_pow (by omega))).mpr
      (by
        simp only [Seq.bytesAt, Mem.put, natBytes]
        apply List.ext_getElem (by simp)
        intro j hj _
        simp at hj
        simp [show a ≤ a + j by omega, show a + j < a + sz by omega])
    simp [oneBlk, Regs.set, this]
  · cases hrep

/-- Every behaviour of a program whose thread `0` is `local (oneBlk a sz)` has `rax = 1` in
thread `0`. -/
theorem rax_one {P : Prog} {a sz : Nat}
    (hP : P.threads[0]? = some ⟨chain ([] ++ [.local (oneBlk a sz)] ++ []), false⟩)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} (hb : Behav P M f) :
    f.regs 0 .rax = 1 := by
  obtain ⟨dom, trs, hF, x, -, -, -, -, -, rfl⟩ := hb
  have h0 : 0 < P.threads.length := (List.getElem?_eq_some_iff.mp hP).1
  have hth := (List.getElem?_eq_some_iff.mp hP).2
  have hl : trs.length = P.threads.length := by rw [hF.length_eq, length_traces]
  obtain ⟨hk, p, hp, htr⟩ := trace_run hF 0 (by omega)
  have hpr : p.2 .rax = 1 := by
    simp only [hth, List.nil_append, List.append_nil, chain, run] at hp
    obtain ⟨a', ha', b', hb', rfl⟩ := bind_mem hp
    simp only [List.mem_singleton] at hb'
    subst hb'
    simp only [runBlock, oneBlk, List.mem_flatMap, List.mem_filterMap] at ha'
    obtain ⟨ivs, -, rvs, hrvs, ovs, -, hq⟩ := ha'
    split at hq
    · rename_i hspec
      cases hq
      have hr : rvs = [1] := by
        have := mem_seqL _ _ _ hrvs
        cases this with
        | cons _ h => cases h; simp at hspec; exact congrArg (fun v => [v]) hspec.1
      subst hr
      simp [Regs.setMany, Regs.set]
    · cases hq
  simp only [finalAx, finalOf, List.getElem?_eq_getElem (show 0 < trs.length by omega),
    Option.map_some, Option.getD_some]
  rw [htr]
  simp [Thread.xtrace, coreOf, Silmaril.X86.State.read, hpr]

/-- A two-thread test observing thread `0`'s `rax`. -/
def raxShell (name : String) (locs : List Loc) (v : Nat) : Test where
  name := name
  source := "cir"
  doc := "localisation example"
  locs := locs
  threads := []
  quant := .exists_
  cond := .atom (.reg 0 .rax 64 v)
  coverage := .tso
  tso := some .allowed
  xl := .allowed
  sc := some .allowed
  basis := "CIR semantics"

/-- **Ghost bytes**: a location at the queue byte of the futex word `0`; thread `1` wakes it. -/
def ghostTest : CTest :=
  ⟨raxShell "ghost" [⟨"q", qAddr 0, 1, 0⟩] 0,
    [⟨chain ([] ++ oneOps (qAddr 0) 1 ++ []), false⟩, ⟨.futexWake (.lit 0) (.lit 1), false⟩]⟩

/-- **Address wrap**: thread `1` stores at `x + 2 ^ 64`. -/
def wrapTest : CTest :=
  ⟨raxShell "wrap" [⟨"x", 0x10000, 4, 0⟩] 0,
    [⟨chain ([] ++ oneOps 0x10000 4 ++ []), false⟩,
      ⟨.store .rlx 4 .wb (.lit (0x10000 + 2 ^ 64)) (.lit 0), false⟩]⟩

theorem check_ghost : ghostTest.check = true := by decide +kernel

theorem check_wrap : wrapTest.check = true := by decide +kernel

/-- The SC behaviour with `rax = 0` refutes the statement, given its hypotheses. -/
theorem refute_rax0 (c : CTest) (hc : c.check = true) (a sz : Nat)
    (hcond : c.test.witness = .atom (.reg 0 .rax 64 0)) (hv : c.verdict .sc = .allowed)
    (h0 : c.prog.threads[0]? = some ⟨chain ([] ++ oneOps a sz ++ []), false⟩)
    (hst : ∀ (M : Model) (f : Final), Behav c.prog M.Holds f →
      ∃ f', Behav ⟨c.prog.locs, c.prog.threads.set 0
        ⟨chain ([] ++ [.local (oneBlk a sz)] ++ []), false⟩⟩ M.Holds f' ∧
        f'.mem = f.mem ∧ f'.regs = f.regs) : False := by
  have hall := (Silmaril.X86.Concurrency.Cir.verdicts_of_check hc).allowed .sc hv
  obtain ⟨f, hf, hw⟩ := hall
  rw [hcond] at hw
  simp only [Cond.eval, Atom.eval, beq_iff_eq] at hw
  have hf0 : (f.regs 0 .rax).toNat = 0 := by
    have := Nat.mod_eq_of_lt (f.regs 0 .rax).isLt; omega
  obtain ⟨f', hf', -, hr⟩ := hst .sc f hf
  have h1 := rax_one (P := ⟨c.prog.locs, c.prog.threads.set 0
    ⟨chain ([] ++ [.local (oneBlk a sz)] ++ []), false⟩⟩) (a := a) (sz := sz) (by
      have : 0 < c.prog.threads.length := (List.getElem?_eq_some_iff.mp h0).1
      simp [this]) hf'
  rw [hr] at h1
  rw [h1] at hf0
  simp at hf0

/-- **The first statement is false (ghost bytes).** -/
theorem not_cirLocalizeFirst_ghost : ¬ CirLocalizeFirst := by
  intro h
  refine refute_rax0 ghostTest check_ghost (qAddr 0) 1 rfl rfl rfl
    (h ghostTest.prog 0 [] (oneOps (qAddr 0) 1) [] (oneBlk (qAddr 0) 1) rfl (by decide) (by decide)
      (fun c hc => ⟨⟨"q", qAddr 0, 1, 0⟩, by simp [ghostTest, CTest.prog, raxShell], by
        simp [oneBlk] at hc; subst hc; simp⟩) (by decide) ?_ ?_ (oneOps_spec _ _
        (by simp [qAddr]) (by decide)))
  · intro j th hj hth
    match j, hj, hth with
    | 1, _, hth =>
      simp [ghostTest, CTest.prog] at hth; subst hth; rfl
    | k + 2, _, hth => simp [ghostTest, CTest.prog] at hth
  · intro s hs r hr
    simp [oneOps] at hs
    rcases hs with rfl | rfl
    · simp [Stmt.writes] at hr
    · simp only [Stmt.writes, List.mem_singleton] at hr; simp [oneBlk, hr]

/-- **The first statement is false (address wrap).** -/
theorem not_cirLocalizeFirst_wrap : ¬ CirLocalizeFirst := by
  intro h
  refine refute_rax0 wrapTest check_wrap 0x10000 4 rfl rfl rfl
    (h wrapTest.prog 0 [] (oneOps 0x10000 4) [] (oneBlk 0x10000 4) rfl (by decide) (by decide)
      (fun c hc => ⟨⟨"x", 0x10000, 4, 0⟩, by simp [wrapTest, CTest.prog, raxShell], by
        simp [oneBlk] at hc; subst hc; simp⟩) (by decide) ?_ ?_ (oneOps_spec _ _
        (by decide) (by decide)))
  · intro j th hj hth
    match j, hj, hth with
    | 1, _, hth =>
      simp [wrapTest, CTest.prog] at hth; subst hth; decide
    | k + 2, _, hth => simp [wrapTest, CTest.prog] at hth
  · intro s hs r hr
    simp [oneOps] at hs
    rcases hs with rfl | rfl
    · simp [Stmt.writes] at hr
    · simp only [Stmt.writes, List.mem_singleton] at hr; simp [oneBlk, hr]

/-- The ghost counterexample satisfies the corrected statement's other hypotheses: its thread `1`
avoids the cell under the exact `avoids`; only the footprint bound fails. -/
theorem ghost_breaks_only_ctl :
    (Stmt.futexWake (.lit 0) (.lit 1)).avoids [(qAddr 0, 1), (qAddr 0, 1)] = true ∧
      ¬ (qAddr 0 + 1 ≤ ctlAddr 0) := by
  decide

/-- The wrap counterexample satisfies the footprint bound; only the exact `avoids` fails. -/
theorem wrap_breaks_only_avoids :
    0x10000 + 4 ≤ ctlAddr 0 ∧
      avoidsFirst [(0x10000, 4), (0x10000, 4)] (.store .rlx 4 .wb (.lit (0x10000 + 2 ^ 64)) (.lit 0)) =
        true ∧
      (Stmt.store .rlx 4 .wb (.lit (0x10000 + 2 ^ 64)) (.lit 0)).avoids [(0x10000, 4), (0x10000, 4)] =
        false := by
  decide

/-! ## Weak stores under XL -/

/-- The block of `load rbx x`: `rbx` and the cell keep the cell's value. -/
def copyBlk : Block where
  name := "copy"
  ins := [(0x10000, 4)]
  outs := [(0x10000, 4)]
  rin := []
  rout := [.rbx]
  spec := fun i o => o = i ++ i
  dec := fun _ _ => inferInstance

/-- `load rax z`. -/
def wPre : List Stmt := [.load .rax .rlx 4 .wb (.lit 0x10080)]
/-- `load rbx x`. -/
def wOps : List Stmt := [.load .rbx .rlx 4 .wb (.lit 0x10000)]
/-- `sfence; store.nt y 1`. -/
def wPost : List Stmt := [.fence .sfence, .store .rlx 4 .nt (.lit 0x10040) (.lit 1)]

/-- The test shell: `rax = 1`, `rbx = 0`, `y = 2` at the end. -/
def weakShell (name : String) (sc tso xl : Verdict) : Test where
  name := name
  source := "cir"
  doc := "localisation example"
  locs := [⟨"x", 0x10000, 4, 0⟩, ⟨"y", 0x10040, 4, 0⟩, ⟨"z", 0x10080, 4, 0⟩]
  threads := []
  quant := .exists_
  cond := .and (.atom (.reg 0 .rax 64 1)) (.and (.atom (.reg 0 .rbx 64 0)) (.atom (.mem 0x10040 4 2)))
  coverage := .tso
  tso := some tso
  xl := xl
  sc := some sc
  basis := "CIR semantics"

/-- The writer thread: `store y 2; store z 1`. -/
def wWriter : Thread := ⟨chain [.store .rlx 4 .wb (.lit 0x10040) (.lit 2),
  .store .rlx 4 .wb (.lit 0x10080) (.lit 1)], false⟩

/-- **Weak stores**: XL allows the outcome. -/
def weakTest : CTest :=
  ⟨weakShell "weak" .forbidden .forbidden .allowed,
    [⟨chain (wPre ++ wOps ++ wPost), false⟩, wWriter]⟩

/-- The localised program forbids it under XL. -/
def weakLocTest : CTest :=
  ⟨weakShell "weak-local" .forbidden .forbidden .forbidden,
    [⟨chain (wPre ++ [.local copyBlk] ++ wPost), false⟩, wWriter]⟩

theorem check_weak : weakTest.check = true := by decide +kernel

theorem check_weakLoc : weakLocTest.check = true := by decide +kernel

theorem copy_spec : ∀ rs m tr rs' m', SeqRun (chain wOps) rs m tr rs' m' →
    copyBlk.spec (copyBlk.rin.map (fun r => (rs r).toNat) ++
      copyBlk.ins.map fun c => (m.val c.1 c.2).getD 0)
      (copyBlk.rout.map (fun r => (rs' r).toNat) ++ copyBlk.outs.map fun c => (m'.val c.1 c.2).getD 0) := by
  intro rs m tr rs' m' ⟨⟨dom, hrun⟩, hrep⟩
  simp only [wOps, chain] at hrun
  obtain ⟨q, hq, q', hq', he⟩ := bind_mem hrun
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [run, List.mem_singleton] at hq'
  subst hq'
  simp only [run, List.mem_map] at hq
  obtain ⟨v, hv, rfl⟩ := hq
  have hv' := mem_pick hv
  simp only [List.append_nil, replay, Lab.replay, Expr.eval, BitVec.toNat_ofNat] at hrep
  split at hrep
  · rename_i hval
    simp only [Option.bind_some, Option.some.injEq] at hrep
    subst hrep
    have h64 : (65536 : Nat) % 2 ^ 64 = 65536 := by decide
    simp only [h64] at hval
    have hv32 : v < 4294967296 := by simpa using hv'
    simp [copyBlk, Regs.set, hval]
    omega
  · cases hrep

theorem weak_dom : (1 : Nat) ∈ weakLocTest.domain ∧ (0 : Nat) ∈ weakLocTest.domain := by
  decide +kernel

/-- The localised program's runs of thread `0` with `rax = 1` and `rbx = 0` are runs over the
test's domain. -/
theorem weak_restrict {D : List Nat} {p : List Lab × Regs}
    (hp : p ∈ run D (chain (wPre ++ [.local copyBlk] ++ wPost)) Regs.zero)
    (h1 : p.2 .rax = 1) (h0 : p.2 .rbx = 0) :
    p ∈ run weakLocTest.domain (chain (wPre ++ [.local copyBlk] ++ wPost)) Regs.zero := by
  obtain ⟨d1, d0⟩ := weak_dom
  simp only [wPre, wPost, List.cons_append, List.nil_append, chain, run] at hp ⊢
  obtain ⟨q1, hq1, q2, hq2, rfl⟩ := bind_mem hp
  obtain ⟨q3, hq3, q4, hq4, rfl⟩ := bind_mem hq2
  simp only [List.mem_map] at hq1
  obtain ⟨v1, hv1, rfl⟩ := hq1
  have hq4' : q4.2 = q3.2 := by
    simp [Res.bind] at hq4; rw [hq4]
  simp only [runBlock, copyBlk, List.mem_flatMap, List.mem_filterMap] at hq3
  obtain ⟨ivs, hivs, rvs, hrvs, ovs, hovs, hq⟩ := hq3
  split at hq
  · rename_i hspec
    cases hq
    have hs := @of_decide_eq_true _ (copyBlk.dec _ _) hspec
    have hi := mem_seqL _ _ _ hivs
    have hr := mem_seqL _ _ _ hrvs
    have ho := mem_seqL _ _ _ hovs
    obtain ⟨iv, rfl, hiv⟩ : ∃ iv, ivs = [iv] ∧ iv ∈ pick D 4 := by
      cases hi with | cons h t => cases t; exact ⟨_, rfl, h⟩
    obtain ⟨rv, rfl, -⟩ : ∃ rv, rvs = [rv] ∧ rv ∈ D := by
      cases hr with | cons h t => cases t; exact ⟨_, rfl, h⟩
    obtain ⟨ov, rfl, -⟩ : ∃ ov, ovs = [ov] ∧ ov ∈ pick D 4 := by
      cases ho with | cons h t => cases t; exact ⟨_, rfl, h⟩
    simp only [copyBlk, List.map_nil, List.nil_append, List.cons_append, List.cons.injEq,
      and_true] at hs
    obtain ⟨hrv, hov⟩ := hs
    have hivl : iv < 4294967296 := by simpa using mem_pick hiv
    have hv1l : v1 < 4294967296 := by simpa using mem_pick hv1
    simp only [hq4', Regs.setMany, Regs.set] at h1 h0
    simp at h1 h0
    have e1 : v1 = 1 := by
      have := congrArg BitVec.toNat h1
      simp at this; omega
    have e0 : rv = 0 := by
      have := congrArg BitVec.toNat h0
      simp at this; omega
    have ei : iv = 0 := hrv ▸ e0
    have eo : ov = 0 := hov.trans ei
    subst e1 e0 ei eo
    refine mem_bind (List.mem_map.mpr ⟨1, pick_of d1 (by decide), rfl⟩) ?_
    refine mem_bind ?_ hq4
    simp only [runBlock, copyBlk, List.mem_flatMap, List.mem_filterMap]
    refine ⟨[0], ?_, [0], ?_, [0], ?_, ?_⟩
    · simp [Silmaril.X86.MemoryModel.Litmus.seqL, pick_of d0]
    · simp [Silmaril.X86.MemoryModel.Litmus.seqL, d0]
    · simp [Silmaril.X86.MemoryModel.Litmus.seqL, pick_of d0]
    · simp
  · cases hq

theorem regs_of_witness {f : Final}
    (hw : (weakShell "weak" .forbidden .forbidden .allowed).witness.eval f = true) :
    f.regs 0 .rax = 1 ∧ f.regs 0 .rbx = 0 := by
  simp only [Test.witness, weakShell, Cond.eval, Atom.eval, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨h1, h2, -⟩ := hw
  have e1 := Nat.mod_eq_of_lt (f.regs 0 .rax).isLt
  have e2 := Nat.mod_eq_of_lt (f.regs 0 .rbx).isLt
  exact ⟨BitVec.eq_of_toNat_eq (by simp; omega), BitVec.eq_of_toNat_eq (by simp; omega)⟩

theorem writer_run {D D' : List Nat} {rs : Regs} {p : List Lab × Regs}
    (h : p ∈ run D wWriter.body rs) : p ∈ run D' wWriter.body rs := by
  simpa [wWriter, chain, run, Res.bind] using h

/-- **The first statement is false (weak stores under XL).** -/
theorem not_cirLocalizeFirst_xlWeak : ¬ CirLocalizeFirst := by
  intro h
  obtain ⟨f, hf, hw⟩ := (Silmaril.X86.Concurrency.Cir.verdicts_of_check check_weak).allowed .xl rfl
  have hoth : ∀ j th, j ≠ 0 → weakTest.prog.threads[j]? = some th →
      avoidsFirst (copyBlk.ins ++ copyBlk.outs) th.body = true := by
    intro j th hj hth
    match j, hj, hth with
    | 1, _, hth => simp [weakTest, CTest.prog] at hth; subst hth; decide
    | k + 2, _, hth => simp [weakTest, CTest.prog] at hth
  have hwr : ∀ s ∈ wOps, ∀ r ∈ s.writes, r ∈ copyBlk.rout := by
    intro s hs r hr
    simp only [wOps, List.mem_singleton] at hs
    subst hs
    simp only [Stmt.writes, List.mem_singleton] at hr
    simp [copyBlk, hr]
  obtain ⟨f', hf', hmem, hregs⟩ := h weakTest.prog 0 wPre wOps wPost copyBlk rfl (by decide)
    (by decide)
    (fun c hc => ⟨⟨"x", 0x10000, 4, 0⟩, by simp [weakTest, CTest.prog, weakShell], by
      simp [copyBlk] at hc; subst hc; simp⟩) (by decide) hoth hwr copy_spec .xl f hf
  have hfe : f' = f := by
    cases f; cases f'; simp only at hmem hregs; subst hmem hregs; rfl
  subst hfe
  obtain ⟨hrax, hrbx⟩ := regs_of_witness hw
  -- the localised behaviour is one over the test's domain
  obtain ⟨D, trs, hF, x, h1, h2, h3, h4, h5, h6⟩ := hf'
  have hl : trs.length = 2 := by rw [hF.length_eq, length_traces]; rfl
  have hF' : List.Forall₂ (· ∈ ·) trs (weakLocTest.prog.traces weakLocTest.domain) := by
    refine List.forall₂_iff_get.mpr ⟨by rw [length_traces, hl]; rfl, fun k hk1 hk2 => ?_⟩
    simp only [List.get_eq_getElem]
    obtain ⟨hk', p, hp, htr⟩ := trace_run hF k hk1
    rw [traces_get _ _ k hk2, htr]
    match k, hk1, hk2, hk', hp, htr with
    | 0, _, _, _, hp, htr =>
      have hpr : ∀ r, f'.regs 0 r = p.2 r := by
        intro r
        rw [h6]
        simp only [finalAx, finalOf, List.getElem?_eq_getElem (show 0 < trs.length by omega),
          htr, Option.map_some, Option.getD_some]
        simp [Thread.xtrace, coreOf, Silmaril.X86.State.read]
      refine List.mem_map.mpr ⟨p, ?_, rfl⟩
      exact weak_restrict hp (by rw [← hpr, hrax]) (by rw [← hpr, hrbx])
    | 1, _, _, _, hp, htr => exact List.mem_map.mpr ⟨p, writer_run hp, rfl⟩
  have hb : BehavIn weakLocTest.prog weakLocTest.domain Silmaril.X86.MemoryModel.Axiomatic.Exec.Xl f' :=
    ⟨trs, hF', x, h1, h2, h3, h4, h5, h6⟩
  exact ((Silmaril.X86.Concurrency.Cir.verdicts_of_check check_weakLoc).holds .xl) ⟨f', hb, hw⟩

/-- The weak-store counterexample satisfies the corrected statement's other hypotheses
(cells below the ghost bytes, exact `avoids` for `pre`, `post` and thread `1`); only `post`'s
write-back stores fail, which the corrected statement asks for under XL alone. -/
theorem weak_breaks_only_wb :
    (copyBlk.ins ++ copyBlk.outs).all (fun c => decide (c.1 + c.2 ≤ ctlAddr 0)) = true ∧
      (wPre ++ wPost).all (Stmt.avoids (copyBlk.ins ++ copyBlk.outs)) = true ∧
      wWriter.body.avoids (copyBlk.ins ++ copyBlk.outs) = true ∧
      wPost.all Stmt.wbStores = false := by
  decide

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
