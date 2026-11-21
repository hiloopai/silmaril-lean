module

public import Silmaril.X86.Concurrency.Cir.Tv.Marked.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Thms

/-!
# Translation validation of marked C threads: soundness

`mwalk_sound` composes `walk_sound` over the segments of a
marked thread: each marker call is the CIR `spawn`/`join` between the segments, with the same
control action, and the register relation flows through it (the marker keeps every register).
`CTest.refines` lifts this to tests with `axReach_pick`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvMarked

open Silmaril.X86 (State)
open Silmaril.X86.Litmus (Trace StepRec explore)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Model outsBy threadUnits AxReach Final Atom)

/-! ## Straight-line runs -/

theorem mem_run_seq {dom : List Nat} {s t : Stmt} {rs : Regs} {p : List Lab × Regs} :
    p ∈ run dom (.seq s t) rs ↔
      ∃ a ∈ run dom s rs, ∃ b ∈ run dom t a.2, p = (a.1 ++ b.1, b.2) := by
  simp only [run, Res.bind, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

theorem run_chain_append {dom : List Nat} :
    ∀ (l₁ l₂ : List Stmt) {rs : Regs} {p q : List Lab × Regs},
      p ∈ run dom (chain l₁) rs → q ∈ run dom (chain l₂) p.2 →
        (p.1 ++ q.1, q.2) ∈ run dom (chain (l₁ ++ l₂)) rs
  | [], l₂, rs, p, q, hp, hq => by
    simp only [chain, run, List.mem_singleton] at hp
    subst hp
    simpa using hq
  | x :: l, l₂, rs, p, q, hp, hq => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_run_seq.mp hp
    have := run_chain_append l l₂ hb hq
    simp only [List.cons_append, chain]
    exact mem_run_seq.mpr ⟨a, ha, _, this, by simp⟩

theorem run_pro {dom : List Nat} :
    ∀ (pro : List (Reg × Nat)) (rs : Regs),
      ([], pro.foldl (fun rs p => rs.set p.1 (BitVec.ofNat 64 p.2)) rs) ∈
        run dom (chain (pro.map fun p => .assign p.1 (.lit p.2))) rs
  | [], rs => by simp [chain, run]
  | p :: l, rs => by
    simp only [List.map_cons, chain, List.foldl_cons]
    exact mem_run_seq.mpr ⟨([], rs.set p.1 (BitVec.ofNat 64 p.2)), by simp [run, Expr.eval], _,
      run_pro l _, by simp⟩

theorem mark_run {dom : List Nat} (m : Mark) (rs : Regs) : ([m.lab], rs) ∈ run dom m.stmt rs := by
  cases m <;> simp [Mark.stmt, Mark.lab, run]

theorem mark_acts (m : Mark) : m.lab.acts = [m.act] := by cases m <;> rfl

theorem normActs_append (a b : List XAct) : normActs (a ++ b) = normActs a ++ normActs b := by
  simp [normActs]

theorem normActs_ctl (t o n : Nat) : normActs [ctlAct t o n] = [ctlAct t o n] := by
  simp [normActs, Act.norm, ctlAct, rmwAct]

theorem normActs_end (t o n : Nat) : normActs [endAct t o n] = [endAct t o n] := by
  simp [normActs, Act.norm, endAct, rmwAct]

theorem normActs_mark (m : Mark) : normActs [m.act] = [m.act] := by
  cases m
  · exact normActs_ctl _ _ _
  · exact normActs_end _ _ _

/-! ## Lists -/

theorem mapM_mem {α β : Type} {f : α → Option (List β)} :
    ∀ {l : List α} {rss : List (List β)}, l.mapM f = some rss → ∀ {y : β}, y ∈ rss.flatten →
      ∃ x ∈ l, ∃ ys, f x = some ys ∧ y ∈ ys
  | [], rss, h, y, hy => by
    simp at h; subst h; simp at hy
  | x :: l, rss, h, y, hy => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ys, hx, rs, hl, rfl⟩ := h
    simp only [List.flatten_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ⟨x, by simp, ys, hx, hy⟩
    · obtain ⟨x', hx', ys', h', hy'⟩ := mapM_mem hl hy
      exact ⟨x', by simp [hx'], ys', h', hy'⟩

theorem mapM_id_spec {α : Type} :
    ∀ {l : List (Option α)} {L : List α}, l.mapM id = some L →
      L.length = l.length ∧ ∀ k (h₁ : k < l.length) (h₂ : k < L.length), l[k] = some L[k]
  | [], L, h => by simp at h; subst h; simp
  | x :: l, L, h => by
    rw [List.mapM_cons] at h
    simp only [id, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, L', hl, rfl⟩ := h
    obtain ⟨hlen, hget⟩ := mapM_id_spec hl
    refine ⟨by simp [hlen], ?_⟩
    intro k h₁ h₂
    cases k with
    | zero => simpa using ha
    | succ k => simpa using hget k (by simpa using h₁) (by simpa using h₂)

/-! ## The segments -/

theorem glue_acts (tr : Trace) (m : Mark) (tr' : Trace) :
    (glue tr m tr').acts = tr.acts ++ m.act :: tr'.acts := by
  simp [glue, Trace.acts]

/-- **The segments are sound**: every trace of `mexplore` is a run of the segments' statements
with the marks between them. -/
theorem mwalk_sound {dom : List Nat} :
    ∀ (ts : List XThread) (ms : List Mark) (iss : List (List Item)) (K Z Kf : List Reg),
      (iss.any (fun its => its.any fun it => it.ops.any Stmt.reads) = true →
        ∀ v ∈ dom, v < 2 ^ 32) →
      mwalk ts ms iss K Z = some Kf → ∀ (fuel : Nat) (s : State) (rs : Regs),
        (∀ t ∈ ts.head?, s.rip = t.base) → Rel K Z rs s → ∀ trs,
          mexplore dom fuel ts ms s = some trs →
          ∀ tr ∈ trs, ∃ p ∈ run dom (chain (mops iss ms)) rs,
            p.1.flatMap Lab.acts = normActs tr.acts ∧ ∀ r, r ∉ Kf → tr.final.read r = p.2 r
  | [], _, _, _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [mwalk] at hw
  | [t], [], [its], K, Z, Kf, hdom, hw, fuel, s, rs, hrip, hrel, trs, hx => by
    simp only [mwalk] at hw
    split at hw
    · rename_i hlen
      simp only [mexplore] at hx
      intro tr htr
      exact walk_sound hlen (fun h => hdom (by simp [h])) hw (hrip t (by simp)) hrel hx tr htr
    · cases hw
  | [_], [], [], _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [mwalk] at hw
  | [_], [], _ :: _ :: _, _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [mwalk] at hw
  | [_], _ :: _, _, _, _, _, _, hw, _, _, _, _, _, _, _ => by
    simp [mwalk] at hw
  | _ :: _ :: _, [], _, _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [mwalk] at hw
  | _ :: _ :: _, _ :: _, [], _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [mwalk] at hw
  | t :: t' :: ts, m :: ms, its :: iss, K, Z, Kf, hdom, hw, fuel, s, rs, hrip, hrel, trs, hx => by
    simp only [mwalk] at hw
    split at hw
    · rename_i hlen
      split at hw
      · rename_i K' hw1
        simp only [mexplore, Option.bind_eq_some_iff] at hx
        obtain ⟨trs1, hx1, hx2⟩ := hx
        obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hx2
        intro tr htr
        obtain ⟨tr1, htr1, ys, hys, hy⟩ := mapM_mem hL htr
        obtain ⟨trs2, hx2', rfl⟩ := Option.map_eq_some_iff.mp hys
        obtain ⟨tr2, htr2, rfl⟩ := List.mem_map.mp hy
        obtain ⟨p1, hp1, hpa1, hpr1⟩ := walk_sound hlen
          (fun h => hdom (by simp [h])) hw1 (hrip t (by simp)) hrel hx1 tr1 htr1
        have hrel1 : Rel K' [] p1.2 { tr1.final with rip := t'.base } :=
          ⟨fun r hr => hpr1 r hr, fun r hr => by cases hr⟩
        obtain ⟨p2, hp2, hpa2, hpr2⟩ := mwalk_sound (t' :: ts) ms iss K' [] Kf
          (fun h => hdom (by simp [h])) hw fuel _ p1.2 (by simp) hrel1 trs2 hx2' tr2 htr2
        have hrun := run_chain_append (its.flatMap Item.ops) (m.stmt :: mops iss ms) hp1
          (mem_run_seq.mpr ⟨_, mark_run m p1.2, p2, hp2, rfl⟩)
        refine ⟨_, (by rw [mops]; exact hrun), ?_, ?_⟩
        · simp only [List.flatMap_append, glue_acts, normActs_append, hpa1]
          rw [show m.act :: tr2.acts = [m.act] ++ tr2.acts from rfl, normActs_append,
            normActs_mark]
          simp [mark_acts, hpa2]
        · intro r hr
          simpa [glue] using hpr2 r hr
      · cases hw
    · cases hw

theorem split_head {th : CThread} {st : Stubs} :
    ∀ {lo : Nat} {cs : List Nat} {ts : List XThread} {ms : List Mark},
      th.split st lo cs = some (ts, ms) → ∃ t ∈ ts.head?, t.base = th.base + BitVec.ofNat 64 lo
  | lo, [], ts, ms, h => by
    simp only [CThread.split] at h
    split at h
    · cases h; exact ⟨_, rfl, rfl⟩
    · cases h
  | lo, c :: cs, ts, ms, h => by
    simp only [CThread.split] at h
    split at h
    · split at h
      · rename_i m ts' ms' _ _; cases h; exact ⟨_, rfl, rfl⟩
      · cases h
    · cases h

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> simp [allRegs]

theorem wrap_final (i : Nat) (sp : Bool) (tr : Trace) : (wrap i sp tr).final = tr.final := by
  cases sp <;> rfl

theorem wrap_acts (i : Nat) (sp : Bool) (tr : Trace) :
    (wrap i sp tr).acts =
      (if sp then [ctlAct i 1 2] else []) ++ tr.acts ++ (if sp then [endAct i 0 1] else []) := by
  cases sp <;> simp [wrap, Trace.acts]

/-- **A marked thread is sound**: every x86 trace is a run of the CIR thread over the same
domain, with the same actions (start and end events included) up to `normActs`, and the same
final registers outside the clobber set. -/
theorem mtvRun_sound {th : CThread} {st : Stubs} {c : MCert} {K : List Reg}
    (h : mtvRun th st c = some K) {dom : List Nat} (hdom : c.reads = true → ∀ v ∈ dom, v < 2 ^ 32)
    {i fuel : Nat} {trs : List Trace} (hx : th.traces st i dom fuel = some trs) :
    ∀ tr ∈ trs, ∃ p ∈ run dom (c.body (th.marks st)) Regs.zero,
      normActs tr.acts = (⟨c.body (th.marks st), th.spawned⟩ : Thread).acts i p.1 ∧
        ∀ r, r ∉ K → tr.final.read r = p.2 r := by
  unfold mtvRun at h
  unfold CThread.traces at hx
  unfold CThread.marks
  split at h
  · rename_i ts ms hsp
    rw [hsp] at hx
    dsimp only at h hx
    split at h
    · rename_i hok
      obtain ⟨hrip, hregs⟩ := hok
      simp only [List.all_eq_true, beq_iff_eq] at hregs
      let pc : Cert := ⟨c.pro, []⟩
      have hrel : Rel [] (allRegs.filter fun r => decide ((pc.proRegs r).toNat < 2 ^ 32))
          pc.proRegs th.init := by
        constructor
        · intro r _; exact hregs r (mem_allRegs r)
        · intro r hr
          simp only [List.mem_filter, decide_eq_true_eq] at hr
          rw [hregs r (mem_allRegs r)]; exact hr.2
      obtain ⟨t0, ht0, hb0⟩ := split_head hsp
      have hrip0 : ∀ t ∈ ts.head?, th.init.rip = t.base := by
        intro t ht
        rw [ht0] at ht; cases ht
        rw [hb0, hrip]; simp
      obtain ⟨trs0, hx0, rfl⟩ := Option.map_eq_some_iff.mp hx
      intro tr htr
      obtain ⟨tr0, htr0, rfl⟩ := List.mem_map.mp htr
      obtain ⟨p, hp, hpa, hpr⟩ := mwalk_sound ts ms c.segs [] _ K
        (fun hr => hdom (by simpa [MCert.reads] using hr)) h fuel th.init pc.proRegs hrip0 hrel
        trs0 hx0 tr0 htr0
      have hrun := run_chain_append (c.pro.map fun p => .assign p.1 (.lit p.2)) (mops c.segs ms)
        (run_pro (dom := dom) c.pro Regs.zero) hp
      refine ⟨_, hrun, ?_, fun r hr => by rw [wrap_final]; simpa using hpr r hr⟩
      rw [wrap_acts]
      simp only [normActs_append, Thread.acts, List.nil_append, hpa]
      cases th.spawned <;> simp [normActs, Act.norm, ctlAct, endAct, rmwAct]
    · cases h
  · cases h

/-! ## Tests -/

theorem cond_avoids {cond : Silmaril.X86.MemoryModel.Litmus.Cond} {Ks : List (List Reg)}
    (h : condAvoids cond Ks = true) {f f' : Final} (hm : f'.mem = f.mem)
    (hr : ∀ i r, r ∉ Ks.getD i [] → f'.regs i r = f.regs i r) {w : Silmaril.X86.MemoryModel.Litmus.Cond}
    (hw : w.atoms = cond.atoms) : w.eval f' = w.eval f := by
  apply cond_eval_congr
  intro a ha
  rw [hw] at ha
  cases a with
  | mem ad sz v => simp [Atom.eval, hm]
  | reg i r bits v =>
    have hav : !(Ks.getD i []).contains r = true := by
      have := List.all_eq_true.mp h _ ha
      simpa using this
    have hr' : r ∉ Ks.getD i [] := by simpa using hav
    simp [Atom.eval, hr i r hr']

/-- **Refinement of a validated C test.** -/
theorem CTest.refines {c : CTest} (h : c.tvOk = true) (hd : c.domOk = true)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} (hf : c.XBehav M f) :
    ∃ f', BehavIn c.prog c.dom M f' ∧ c.test.witness.eval f' = c.test.witness.eval f := by
  obtain ⟨T, hT, hf⟩ := hf
  simp only [CTest.tvOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hK⟩ := h
  split at hK
  swap
  · cases hK
  rename_i Ks hKs
  obtain ⟨hKl, hKg⟩ := mapM_id_spec hKs
  obtain ⟨hTl, hTg⟩ := mapM_id_spec hT
  simp only [List.length_mapIdx] at hKl hTl
  let U := c.prog.traces c.dom
  have hUl : U.length = c.threads.length := by simp [U, Prog.traces, CTest.prog]
  obtain ⟨f', hf', hmem, hregs⟩ := axReach_pick (t := c.prog.memTest) (U := U) (Ks := Ks)
    (by omega) (fun k h₁ h₂ a ha => by
      have hk : k < c.threads.length := by omega
      have hx := hTg k (by simpa using hk) (by omega)
      simp only [List.getElem_mapIdx] at hx
      have htv := hKg k (by simpa using hk) (by omega)
      simp only [List.getElem_mapIdx] at htv
      have hkc : k < c.certs.length := by omega
      have hdom : (c.cert k).reads = true → ∀ v ∈ c.dom, v < 2 ^ 32 := by
        intro hr
        simp only [CTest.domOk, Bool.or_eq_true, List.all_eq_true, Bool.not_eq_true',
          decide_eq_true_eq] at hd
        rcases hd with hd | hd
        · have : c.cert k = c.certs[k] := by simp [CTest.cert, hkc]
          rw [this, hd _ (List.getElem_mem hkc)] at hr
          cases hr
        · exact hd
      obtain ⟨p, hp, hacts, hregs⟩ := mtvRun_sound htv hdom hx a ha
      refine ⟨(⟨(c.cert k).body (c.threads[k].marks c.stubs), c.threads[k].spawned⟩ : Thread).xtrace
        k p, ?_, ?_, ?_⟩
      · simp only [U, Prog.traces, CTest.prog, List.getElem_mapIdx]
        exact List.mem_map_of_mem hp
      · rw [← threadUnits_normActs, hacts]
        simp [Thread.xtrace, Trace.acts]
      · intro r hr
        have : Ks.getD k [] = Ks[k] := by simp [hKl, hk]
        rw [hregs r (by rwa [← this])]
        rfl) hf
  exact ⟨f', hf', cond_avoids hK hmem hregs (witness_atoms c.test)⟩

/-- A passing CIR check gives the CIR verdicts, the operational TSO verdict, and an SC
behaviour. -/
theorem CTest.cir_of_check {c : CTest} (h : c.cirCheck = true) :
    (∀ M : Model, (c.verdict M).Holds c.test (BehavIn c.prog c.dom M.Holds)) ∧
      (c.verdict .tso).Holds c.test (OpBehavIn c.prog c.dom) ∧
      ∃ f, BehavIn c.prog c.dom Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f := by
  unfold CTest.cirCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hax, hop⟩ := h
  split at hop
  swap
  · cases hop
  rename_i os hos
  have hop' : c.verdict .tso = c.test.verdictOf os := by simpa using hop
  split at hax
  swap
  · cases hax
  rename_i js hjs
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hax
  obtain ⟨⟨⟨hsc, htso⟩, hxl⟩, hne⟩ := hax
  have hv : ∀ M : Model, c.verdict M = c.test.verdictOf (outsBy js M.sel) := by
    intro M; cases M
    · exact hsc
    · exact htso
    · exact hxl
  refine ⟨fun M => ?_, ?_, ?_⟩
  · rw [hv M]
    exact Silmaril.X86.MemoryModel.Litmus.verdictOf_holds fun o =>
      Silmaril.X86.MemoryModel.Litmus.axJudge_spec hjs M o
  · rw [hop']
    refine Silmaril.X86.MemoryModel.Litmus.verdictOf_holds fun o => ?_
    rw [Silmaril.X86.MemoryModel.Litmus.opOut_spec hos o]
    -- `opOut` uses `c.opT`'s outcome (the test's condition) and initial memory (the locations
    -- and the control bytes), which are those of `OpBehavIn`
    rfl
  · obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (by simpa using hne)
    obtain ⟨f, hf, _⟩ := (Silmaril.X86.MemoryModel.Litmus.axJudge_spec hjs Model.sc o).mp ho
    exact ⟨f, hf⟩

/-- **Everything a validated C test gives.** -/
theorem CTest.transfer_of_allOk {c : CTest} (h : c.allOk = true) : c.Transfer := by
  simp only [CTest.allOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨htv, hd⟩, hc⟩, -⟩ := h
  obtain ⟨hcir, hop, hsc⟩ := CTest.cir_of_check hc
  refine ⟨fun M f hf => CTest.refines htv hd hf, hcir, hop, hsc, ?_⟩
  intro M hM
  have := hcir M
  rw [hM] at this
  rintro ⟨f, hf, hw⟩
  obtain ⟨f', hb, he⟩ := CTest.refines htv hd hf
  exact this ⟨f', hb, he ▸ hw⟩

end Silmaril.Proofs.X86.Concurrency.Cir.TvMarked
