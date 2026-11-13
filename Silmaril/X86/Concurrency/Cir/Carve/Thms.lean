module

public import Silmaril.X86.Concurrency.Cir.Carve.Defs
public import Silmaril.X86.Concurrency.Cir.Localize.Thms
public import Silmaril.X86.Concurrency.Cir.Litmus.Thms

/-!
# Carving: what is proved

All statements are PROVED (standard axioms):

* `carve_stmts`: carving loses and reorders nothing: the regions' statements, in order, are
  the input list;
* `carve_seq_local`, `carve_conc_not_local`: every statement of a sequential region is local,
  and every concurrent statement is not (so the regions are maximal up to adjacency);
* `withContext_stmts`: each region with its context reassembles the thread;
* `localize_of_footOk`: a sequential region that passes `footOk` and whose contract holds of
  its sequential runs can be replaced by its `local` block, with the same final memory and
  registers (under XL: when the statements after it use write-back stores). Unconditional, as
  `Tv.Task.cirLocalize` is proved (`Cir.cirLocalize`);
* `carve_localize`: the same for a region found by `carveThread`, stated on the uncut thread;
* `ex_carve`, `ex_withContext`, `ex_localize`: the example; `ex_localize` applies
  `carve_localize` to a concrete region, under every model;
* `ex_localize_weak` (non-vacuity): the `SB` example has a TSO behaviour with both
  result slots `0` (SC forbids it over the test's domain, `Ex.check_sb`), and through
  `ex_localize` the localised program has one too: the hypotheses are satisfiable and
  localisation keeps the TSO-weak outcome.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Carve

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv

theorem pushSeq_stmts (s : Stmt) (rs : List Region) :
    (pushSeq s rs).flatMap Region.stmts = s :: rs.flatMap Region.stmts := by
  rcases rs with _ | ⟨_ | _, rs⟩ <;> rfl

theorem mem_pushSeq {s : Stmt} {rs : List Region} {r : Region} (h : r ∈ pushSeq s rs) :
    r ∈ rs ∨ ∃ ops, r = .seq (s :: ops) ∧ (ops = [] ∨ Region.seq ops ∈ rs) := by
  rcases rs with _ | ⟨_ | _, rs⟩ <;> simp only [pushSeq, List.mem_cons, List.not_mem_nil, or_false] at h
  · exact Or.inr ⟨[], h, Or.inl rfl⟩
  · rename_i ops
    rcases h with h | h
    · exact Or.inr ⟨ops, h, Or.inr List.mem_cons_self⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
  · rcases h with h | h | h
    · exact Or.inr ⟨[], h, Or.inl rfl⟩
    · exact Or.inl (h ▸ List.mem_cons_self)
    · exact Or.inl (List.mem_cons_of_mem _ h)

/-- **Carving reassembles to its input.** -/
theorem carve_stmts (priv : List (Nat × Nat)) (l : List Stmt) :
    (carve priv l).flatMap Region.stmts = l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    simp only [carve]
    split
    · rw [pushSeq_stmts, ih]
    · simp only [List.flatMap_cons, Region.stmts, ih, List.singleton_append]

/-- **Sequential regions contain only local statements.** -/
theorem carve_seq_local (priv : List (Nat × Nat)) (l : List Stmt) :
    ∀ ops, Region.seq ops ∈ carve priv l → ∀ s ∈ ops, Stmt.isLocalIn priv s = true := by
  induction l with
  | nil => intro ops h; simp [carve] at h
  | cons s l ih =>
    intro ops h
    simp only [carve] at h
    split at h <;> rename_i hs
    · rcases mem_pushSeq h with h | ⟨ops', he, h'⟩
      · exact ih ops h
      · cases he
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs
        · rcases h' with rfl | h'
          · simp at hx
          · exact ih ops' h' x hx
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih ops h

/-- **Concurrent statements are not local.** -/
theorem carve_conc_not_local (priv : List (Nat × Nat)) (l : List Stmt) :
    ∀ s, Region.conc s ∈ carve priv l → Stmt.isLocalIn priv s = false := by
  induction l with
  | nil => intro s h; simp [carve] at h
  | cons s l ih =>
    intro x h
    simp only [carve] at h
    split at h <;> rename_i hs
    · rcases mem_pushSeq h with h | ⟨_, he, _⟩
      · exact ih x h
      · cases he
    · rcases List.mem_cons.mp h with h | h
      · cases h; simpa using hs
      · exact ih x h

/-- **Each region with its context reassembles the thread.** -/
theorem withContext_stmts (rs : List Region) :
    ∀ p ∈ withContext rs, p.1 ++ p.2.1.stmts ++ p.2.2 = rs.flatMap Region.stmts := by
  induction rs with
  | nil => intro p h; simp [withContext] at h
  | cons r rs ih =>
    intro p h
    simp only [withContext, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · simp
    · have := ih q hq
      simp only [List.flatMap_cons, List.append_assoc] at this ⊢
      rw [← this]

/-- **Localisation of a checked region.** -/
theorem localize_of_footOk {P : Prog} {i : Nat}
    {pre ops post : List Stmt} {B : Block}
    (hth : P.threads[i]? = some ⟨chain (pre ++ ops ++ post), false⟩)
    (h : footOk P i pre ops post B = true)
    (hspec : ∀ rs m tr rs' m', SeqRun (chain ops) rs m tr rs' m' →
      B.spec (B.rin.map (fun r => (rs r).toNat) ++ B.ins.map fun c => (m.val c.1 c.2).getD 0)
        (B.rout.map (fun r => (rs' r).toNat) ++ B.outs.map fun c => (m'.val c.1 c.2).getD 0))
    (M : Silmaril.X86.MemoryModel.Litmus.Model) (f : Silmaril.X86.MemoryModel.Litmus.Final)
    (hwb : M = .xl → post.all Stmt.wbStores = true)
    (hb : Behav P M.Holds f) :
    ∃ f', Behav ⟨P.locs, P.threads.set i ⟨chain (pre ++ [.local B] ++ post), false⟩⟩ M.Holds f' ∧
      f'.mem = f.mem ∧ f'.regs = f.regs := by
  simp only [footOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hc, hops⟩, hloc⟩, hctl⟩, hpp⟩, hoth⟩, hw⟩ := h
  refine cirLocalize P i pre ops post B hth hc hops ?_ ?_ hpp ?_ ?_ hspec M f hwb hb
  · intro c hcm
    have := List.all_eq_true.mp hloc c hcm
    simpa only [List.any_eq_true, decide_eq_true_eq] using this
  · intro c hcm
    have := List.all_eq_true.mp hctl c hcm
    simpa only [decide_eq_true_eq] using this
  · intro j th hj hj'
    have hlt : j < P.threads.length := (List.getElem?_eq_some_iff.mp hj').1
    have := List.all_eq_true.mp hoth j (List.mem_range.mpr hlt)
    simp only [Bool.or_eq_true, beq_iff_eq, hj, false_or, hj', Option.all_some] at this
    exact this
  · intro s hs r hr
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp hw s hs) r hr)

/-- **Localisation of a carved region**: carve thread `i` (body `chain ops`); a sequential region
found there, which passes `footOk` with a block `B` whose contract holds of the region's
sequential runs, can be replaced by `local B` (under XL: when the statements after it use
write-back stores). -/
theorem carve_localize {P : Prog} {i : Nat} {ops : List Stmt}
    (hth : P.threads[i]? = some ⟨chain ops, false⟩) {pre seg post : List Stmt}
    (hp : (pre, Region.seq seg, post) ∈ withContext (carveThread P i ops)) {B : Block}
    (h : footOk P i pre seg post B = true)
    (hspec : ∀ rs m tr rs' m', SeqRun (chain seg) rs m tr rs' m' →
      B.spec (B.rin.map (fun r => (rs r).toNat) ++ B.ins.map fun c => (m.val c.1 c.2).getD 0)
        (B.rout.map (fun r => (rs' r).toNat) ++ B.outs.map fun c => (m'.val c.1 c.2).getD 0))
    (M : Silmaril.X86.MemoryModel.Litmus.Model) (f : Silmaril.X86.MemoryModel.Litmus.Final)
    (hwb : M = .xl → post.all Stmt.wbStores = true)
    (hb : Behav P M.Holds f) :
    ∃ f', Behav ⟨P.locs, P.threads.set i ⟨chain (pre ++ [.local B] ++ post), false⟩⟩ M.Holds f' ∧
      f'.mem = f.mem ∧ f'.regs = f.regs := by
  have he := withContext_stmts _ _ hp
  rw [carveThread, carve_stmts] at he
  simp only [Region.stmts] at he
  rw [← he] at hth
  exact localize_of_footOk hth h hspec M f hwb hb

/-- **Example (non-vacuity)**: carving thread `0` of the `SB` example keeps the two flag
accesses concurrent and makes the result store a sequential region, whose footprint passes the
localisation check (the private cell is `r0`); summarising the load of the shared `y` instead
fails the check (thread `1` writes `y`). -/
theorem ex_carve :
    (carveThread Ex.prog 0 (Ex.ops Ex.x Ex.y Ex.r0)).map Region.isSeq = [false, false, true] ∧
      privCells Ex.prog 0 (Ex.ops Ex.x Ex.y Ex.r0) = [(Ex.r0, 4)] ∧
      footOk Ex.prog 0 [.store .rlx 4 .wb (.lit Ex.x) (.lit 1)] [.load .rax .rlx 4 .wb (.lit Ex.y)]
        [.store .na 4 .wb (.lit Ex.r0) (.reg .rax)] (footBlock [.load .rax .rlx 4 .wb (.lit Ex.y)]) =
        false ∧
      footOk Ex.prog 0 ((Ex.ops Ex.x Ex.y Ex.r0).take 2)
        [.store .na 4 .wb (.lit Ex.r0) (.reg .rax)] []
        (footBlock [.store .na 4 .wb (.lit Ex.r0) (.reg .rax)]) = true := by
  decide +kernel

/-- The carved region of `ex_carve`, with its context, is found by `carveThread`. -/
theorem ex_withContext :
    ((Ex.ops Ex.x Ex.y Ex.r0).take 2, Region.seq [.store .na 4 .wb (.lit Ex.r0) (.reg .rax)],
      ([] : List Stmt)) ∈ withContext (carveThread Ex.prog 0 (Ex.ops Ex.x Ex.y Ex.r0)) := by
  have h : withContext (carveThread Ex.prog 0 (Ex.ops Ex.x Ex.y Ex.r0)) =
      [([], .conc (.store .rlx 4 .wb (.lit Ex.x) (.lit 1)),
          [.load .rax .rlx 4 .wb (.lit Ex.y), .store .na 4 .wb (.lit Ex.r0) (.reg .rax)]),
        ([.store .rlx 4 .wb (.lit Ex.x) (.lit 1)], .conc (.load .rax .rlx 4 .wb (.lit Ex.y)),
          [.store .na 4 .wb (.lit Ex.r0) (.reg .rax)]),
        ((Ex.ops Ex.x Ex.y Ex.r0).take 2, .seq [.store .na 4 .wb (.lit Ex.r0) (.reg .rax)], [])] := by
    rfl
  rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **Example (non-vacuity of `carve_localize`)**: on the `SB` example, the result-store region
and its footprint block with the trivial contract (the coarsest summary) satisfy every
hypothesis of `carve_localize`, so every behaviour of `SB` under SC, TSO or XL is one of the
localised program (unconditional). -/
theorem ex_localize (M : Silmaril.X86.MemoryModel.Litmus.Model)
    (f : Silmaril.X86.MemoryModel.Litmus.Final) (hb : Behav Ex.prog M.Holds f) :
    ∃ f', Behav ⟨Ex.prog.locs, Ex.prog.threads.set 0
        ⟨chain ((Ex.ops Ex.x Ex.y Ex.r0).take 2 ++
          [.local (footBlock [.store .na 4 .wb (.lit Ex.r0) (.reg .rax)])] ++ []), false⟩⟩ M.Holds f' ∧
      f'.mem = f.mem ∧ f'.regs = f.regs :=
  carve_localize rfl ex_withContext ex_carve.2.2.2 (fun _ _ _ _ _ _ => trivial) M f
    (fun _ => rfl) hb

/-- `SB` as a CIR litmus test: both result slots end `0`. Allowed by TSO and XL, forbidden by
SC (the CIR enumerator). -/
def Ex.sbTest : CTest :=
  ⟨{ name := "carve-sb", source := "cir", doc := "localisation example", locs := Ex.prog.locs,
     threads := [], quant := .exists_,
     cond := .and (.atom (.mem Ex.r0 4 0)) (.atom (.mem Ex.r1 4 0)),
     coverage := .tso, tso := some .allowed, xl := .allowed, sc := some .forbidden,
     basis := "CIR semantics" }, Ex.prog.threads⟩

theorem Ex.check_sb : Ex.sbTest.check = true := by decide +kernel

open Silmaril.X86.MemoryModel.Litmus (Test Cond Atom leValue) in
/-- **Example (non-vacuity of `ex_localize` under TSO)**: `SB` has a TSO behaviour
with both result slots `0`, and the program with thread `0`'s result store localised has a TSO
behaviour with the same final memory, so localisation keeps the weak outcome. -/
theorem ex_localize_weak :
    ∃ f, Behav Ex.prog Silmaril.X86.MemoryModel.Litmus.Model.tso.Holds f ∧
      leValue f.mem Ex.r0 4 = some 0 ∧ leValue f.mem Ex.r1 4 = some 0 ∧
      ∃ f', Behav ⟨Ex.prog.locs, Ex.prog.threads.set 0
          ⟨chain ((Ex.ops Ex.x Ex.y Ex.r0).take 2 ++
            [.local (footBlock [.store .na 4 .wb (.lit Ex.r0) (.reg .rax)])] ++ []), false⟩⟩
          Silmaril.X86.MemoryModel.Litmus.Model.tso.Holds f' ∧
        leValue f'.mem Ex.r0 4 = some 0 ∧ leValue f'.mem Ex.r1 4 = some 0 := by
  obtain ⟨f, hf, hw⟩ := (verdicts_of_check Ex.check_sb).allowed .tso rfl
  simp [Test.witness, Cond.eval, Atom.eval, Ex.sbTest] at hw
  obtain ⟨f', hf', hm, -⟩ := ex_localize .tso f hf
  exact ⟨f, hf, hw.1, hw.2, f', hf', by rw [hm]; exact hw.1, by rw [hm]; exact hw.2⟩

end Silmaril.X86.Concurrency.Cir.Carve
