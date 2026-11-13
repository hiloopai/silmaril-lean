module

public import Silmaril.Compiler.Core.Verified.TyCfgSim.Defs
/-! # `main` as a control-flow graph over typed slots: the proof

`Seg.run` is `Cfg.Seg.run` over typed slots: from a related pair, one `LoopSimAbort.Iteration`
follows. Each node runs its statement in both machines (`TyLoopStep.assign_step`,
`TyLoopStep.init_step`, `TyStmt.uninit_runs`, `TyLoopCondition.test_step`,
`TyDoCondition.runs`), the pending statements are popped and pushed as Core does, a `save` is
entered in place, `return e;` halts with the value Lir returns (`TyRun.ret_halts`), `exit(n)`
and `abort()` halt as in `Cfg`, and `run l(…)` reaches the label's body as Lir jumps to the
first block of the label's tree (`jump_iter`). `LoopSimAbort.allowed` then covers every Lir
behaviour, divergence included, from the entry of `main`'s block (`recognize_entry`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyCfg

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Machine
open TyExpr (Key Term values close zero)
open TyMem (Local Inv Fresh Defined defsOf update ptr)
open TyStmt (Vars Keys isLocal isFresh typedIn)
open TyLoopStep (Layout Registers)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open LoopMain (regOf)
open Cfg (find symArgs labelDefs iteration_pre jump_steps)
open Relation

variable {file : Program} {labels : Labels}

/-- Selecting slots by key keeps the correspondence of symbols and slots. -/
theorem keys_filter {ls : List Local} {xs : Vars} (h : Keys ls xs) (p : Key → Bool) :
    Keys (ls.filter fun l => p l.sym.key) (xs.filter fun x => p x.1.key) := by
  unfold Keys at h ⊢
  have := congrArg (List.filter fun q : Key × IntegerType => p q.1) h
  simpa only [List.filter_map, Function.comp_def] using this

section run

variable {ret : Sym} {xs : Vars} {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key}
  {T : List Key} {bs : List (Lir.Block Mir.Reg)} {idx : Key → Nat} {mem : Lir.Memory}

/-- **One macro-step from the root of a node**: undefined behaviour, or the return in both
machines, or nonempty paths in both to the root of a label's tree. -/
theorem Seg.run (hret : ReturnLabel labels ret) (nodup : (xs.map (·.1.key)).Nodup)
    (hlook : ∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b))
    (hcodes : ∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
      ∃ c, Seg file ret xs tbl D T (D s.key) b [] c ∧
        At bs (regOf (xs.map (·.1.key))) xs.length idx (idx s.key) c)
    (obs : ∀ (w : Lir.Word) (o : Spec.Obs), LirObs (.returned [w] mem) o →
      o = .exit (w.toNat % 256) [])
    (hsize : mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize)
    (abortObs : ∀ (mem' : Lir.Memory) (o : Spec.Obs),
      mem.store .b8 (Spec.ctlAddr + 40) (BitVec.ofNat 64 2) = some mem' → LirObs (.trapped mem') o →
        o = .abort [])
    {dk : List Key} {e : EE} {P : List EE} {c : Code} (seg : Seg file ret xs tbl D T dk e P c) :
    ∀ {i : Nat} {env : Env} {m : Mem.Concrete.State} {ls : List Local}
      {ds : Key → Option Term} {F : List Frame} {fr : Lir.Frame Mir.Reg},
    At bs (regOf (xs.map (·.1.key))) xs.length idx i c → Pends ls P F → Inv env m ls ds →
    Keys ls xs → Covers dk ds → Registers (regOf (xs.map (·.1.key))) ds fr → m.stdout = "" →
    ExitCall.Budget m →
    LoopSimAbort.Iteration (LoopLink.link bs).prog file labels (Rel file ret xs tbl D T bs idx mem)
      ⟨⟨0, i, 0⟩, fr, [], mem⟩ ⟨.effectExpr e env, F, m⟩ := by
  let regs := regOf (xs.map (·.1.key))
  let d := xs.length
  let p := (LoopLink.link bs).prog
  induction seg with
  | @retn dk e P t ht hc =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    obtain ⟨hcov, htyped, hwf⟩ := usable_spec hc
    have blk : p.block? 0 i = some ⟨(TyInput.ops regs d t).map .op, .ret [.reg d]⟩ :=
      (LoopLink.link_block bs i).trans hat
    have defined := cov.defined hcov
    have lay := layout keys
    let kp := fun q => (CfgGlobals.returnKeys e).contains q
    have ks := keys_filter keys kp
    have nd : ((xs.filter fun x => kp x.1.key).map (·.1.key)).Nodup := by
      simpa only [List.filter_map, Function.comp_def] using nodup.filter kp
    rcases TyRun.ret_halts hret ht inv keys ks (fun _ h => (List.mem_filter.mp h).1) nd defined htyped
      pends.noBoundary with ⟨m₄, hout, reach⟩ | ⟨s', reach, halt⟩
    · let σ := values (defsOf ds)
      obtain ⟨fr₄, exec₄, res₄, -⟩ := TyInput.ops_exec regs σ t hwf d fr mem
        (TyLoopStep.reads lay inv matched defined)
      let w := BitVec.ofInt 64 (t.val σ)
      have steps := Lir.steps_execOps (p := p) (os := TyInput.ops regs d t)
        (s := ⟨⟨0, i, 0⟩, fr, [], mem⟩) (rest := []) blk (by simp) exec₄
      have fetch := Lir.Prog.fetch_eq_term (p := p)
        (pt := ⟨0, i, (TyInput.ops regs d t).length⟩) blk (by simp)
      have res' : fr₄.regs d = some w := res₄
      have final : Lir.step p ⟨⟨0, i, 0 + (TyInput.ops regs d t).length⟩, fr₄, [], mem⟩ =
          .returned [w] mem := by
        simp [Lir.step, fetch, Lir.Frame.readAll, Lir.Frame.read, res']
      have hv : (close (defsOf ds) t).val zero = t.val σ := TyExpr.close_val _ t
      rw [hv] at reach
      refine .inr (.inr ⟨.returned [w] mem, ⟨.halt (.defined (IntExpr.spec (t.val σ))), [], m₄⟩,
        trivial, ⟨_, steps, final⟩, reach, fun o ho => ?_⟩)
      rw [obs w o ho]
      have st : w.toNat % 256 = (t.val σ % 256).toNat := Fragment.status_ofInt _
      have e : m₄.stdout = "" := by rw [hout, out]
      have fin := Sim.Final.exit (c := ⟨.halt (.defined (IntExpr.spec (t.val σ))), [], m₄⟩)
        (v := IntExpr.spec (t.val σ)) (k := (t.val σ % 256).toNat) rfl rfl
      rw [st]
      simpa [e, Spec.coreBytes] using fin
    · exact .inl ⟨s', _, _, reach, halt⟩
  | @op dk dk' e b P a c ha seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    have lay := layout keys
    unfold atom at ha
    split at ha
    · rename_i x ity t hx
      split at ha
      · rename_i hc
        cases ha
        obtain ⟨blk, hat'⟩ := hat
        obtain ⟨l, hl, key, hty⟩ := keys.mem_of_local hc.1
        obtain ⟨hcov, htyped, hwf⟩ := usable_spec hc.2
        have blk' : p.block? 0 i = some (TyLoopStep.assignBlock regs d l.sym.key ity t (i + 1)) := by
          rw [← key]; exact (LoopLink.link_block bs i).trans blk
        rcases TyLoopStep.assign_step hx inv hl key hty (cov.defined hcov) (keys.typed htyped) hwf F
            regs d lay fr matched p 0 i (i + 1) blk' [] mem with
          ub | ⟨m', fr', out', alloc, inv', matched', src, tgt⟩
        · exact .inl (LoopMain.overflows_ub ub)
        obtain ⟨envb, F', henv, pends', pop⟩ := Pends.pop (file := file) (labels := labels) F pends m'
        have cov₁ : Covers (x.key :: dk)
            (update ds l.sym.key (some (close (defsOf ds) (TyStmt.convT ity t)))) := by
          intro q hq
          simp only [update]
          split
          · rfl
          · rename_i hne
            exact cov q ((List.mem_cons.mp hq).resolve_left (fun e => hne (e.trans key)))
        exact iteration_pre tgt.to_reflTransGen (src.trans pop)
          (ih hat' pends' (TyRun.inv_withEnv inv' henv) keys cov₁ matched' (out'.trans out)
            (TyRun.budget_same hb alloc))
      · cases ha
    · split at ha
      · rename_i x ity t hx
        split at ha
        · rename_i hc
          cases ha
          obtain ⟨blk, hat'⟩ := hat
          obtain ⟨l, hl, key, hty⟩ := keys.mem_of_local hc.1
          obtain ⟨hcov, htyped, hwf⟩ := usable_spec hc.2
          have blk' : p.block? 0 i = some (TyLoopStep.assignBlock regs d l.sym.key ity t (i + 1)) := by
            rw [← key]; exact (LoopLink.link_block bs i).trans blk
          rcases TyLoopStep.init_step hx inv hl key hty (cov.defined hcov) (keys.typed htyped) hwf F
              regs d lay fr matched p 0 i (i + 1) blk' [] mem with
            ub | ⟨m', fr', ys, out', alloc, inv', matched', src, tgt⟩
          · exact .inl (LoopMain.overflows_ub ub)
          obtain ⟨envb, F', henv, pends', pop⟩ :=
            Pends.pop (file := file) (labels := labels) _ (.ann ys pends) m'
          have cov₁ : Covers (x.key :: dk)
              (update ds l.sym.key (some (close (defsOf ds) (TyStmt.convT ity t)))) := by
            intro q hq
            simp only [update]
            split
            · rfl
            · rename_i hne
              exact cov q ((List.mem_cons.mp hq).resolve_left (fun e => hne (e.trans key)))
          exact iteration_pre tgt.to_reflTransGen (src.trans pop)
            (ih hat' pends' (TyRun.inv_withEnv inv' henv) keys cov₁ matched' (out'.trans out)
              (TyRun.budget_same hb alloc))
        · cases ha
      · split at ha
        · rename_i x ity hx
          split at ha
          · rename_i hc
            cases ha
            obtain ⟨blk, hat'⟩ := hat
            obtain ⟨l, hl, key, hty⟩ := keys.mem_of_local hc
            obtain ⟨m', ys, out', alloc, inv', src⟩ := TyStmt.uninit_runs (labels := labels) hx inv hl key
              hty F
            obtain ⟨envb, F', henv, pends', pop⟩ :=
              Pends.pop (file := file) (labels := labels) _ (.ann ys pends) m'
            have cov₁ : Covers (dk.filter (· != x.key)) (update ds l.sym.key none) := by
              intro q hq
              simp only [List.mem_filter, bne_iff_ne, ne_eq] at hq
              simp only [update]
              split
              · rename_i he; exact absurd (he.trans key.symm) hq.2
              · exact cov q hq.1
            have blk' : p.block? 0 i = some ⟨([] : List (Lir.Op Mir.Reg)).map .op, .jump (i + 1)⟩ :=
              (LoopLink.link_block bs i).trans blk
            exact iteration_pre (jump_steps blk' (fr := fr) (mem := mem) rfl).to_reflTransGen
              (src.trans pop) (ih hat' pends' (TyRun.inv_withEnv inv' henv) keys cov₁
                (TyLoopStep.registers_clear matched _) (out'.trans out) (TyRun.budget_same hb alloc))
          · cases ha
        · cases ha
  | @test dk e yes no P t cy cn ht hc hbool sy sn ihy ihn =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    obtain ⟨blk, haty, hatn⟩ := hat
    obtain ⟨hcov, htyped, hwf⟩ := usable_spec hc
    have lay := layout keys
    rcases TyLoopCondition.test_step ht inv keys (cov.defined hcov) htyped hwf hbool F regs d lay fr
        matched p 0 i (i + 1 + cy.size) (i + 1) ((LoopLink.link_block bs i).trans blk) [] mem with
      ub | ⟨env', m', fr', out', alloc, inv', match', src, tgt⟩
    · exact .inl (LoopMain.overflows_ub ub)
    · by_cases hv : t.val (values (defsOf ds)) = 1
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihy haty pends inv' keys cov match'
          (out'.trans out) (TyRun.budget_same hb alloc))
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihn hatn pends inv' keys cov match'
          (out'.trans out) (TyRun.budget_same hb alloc))
  | @dtest dk e yes no P t cy cn ht hc hbool sy sn ihy ihn =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    obtain ⟨blk, haty, hatn⟩ := hat
    obtain ⟨hcov, htyped, hwf⟩ := usable_spec hc
    have lay := layout keys
    have defined := cov.defined hcov
    rcases TyDoCondition.runs (labels := labels) ht inv keys defined htyped F with
      ub | ⟨env', m', tch, inv', src⟩
    · exact .inl (LoopMain.overflows_ub ub)
    · obtain ⟨fr', tgt, below⟩ := TyLoopCondition.test_steps regs (values (defsOf ds)) d t hwf hbool
        (i + 1 + cy.size) (i + 1) p 0 i ((LoopLink.link_block bs i).trans blk) fr [] mem
        (TyLoopStep.reads lay inv matched defined)
      have match' : Registers regs ds fr' := by
        intro q a ha
        obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
        rw [below _ (by rw [← hk]; exact lay.below l hl)]
        exact matched q a ha
      rcases TyState.Term.bool01_val hbool (values (defsOf ds)) with hv | hv
      · simp only [hv, ↓reduceIte, zero_ne_one] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihn hatn pends inv' keys cov match'
          (tch.stdout.trans out) (StateExitMem.budget_touched hb tch))
      · simp only [hv, ↓reduceIte, one_ne_zero] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihy haty pends inv' keys cov match'
          (tch.stdout.trans out) (StateExitMem.budget_touched hb tch))
  | @voidCall dk e b P c hc seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    obtain ⟨m', touched, run⟩ := VoidCall.recognize_runs (labels := labels) hc env F m
    obtain ⟨envb, F', henv, pends', pop⟩ := Pends.pop (file := file) (labels := labels) F pends m'
    exact iteration_pre .refl (run.trans pop)
      (ih hat pends' (TyRun.inv_withEnv (inv.touched touched) henv) keys cov matched
        (touched.stdout.trans out) (StateExitMem.budget_touched hb touched))
  | @seq dk P c ann pann ty a b seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    exact iteration_pre .refl (ReturnConst.sequence_reaches file labels ann _ a b env F m)
      (ih hat (.bind pann ty b env inv.env pends) inv keys cov matched out hb)
  | @unit dk b P c ann pann seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    obtain ⟨envb, F', henv, pends', pop⟩ :=
      Pends.pop (file := file) (labels := labels) F pends (focusMemory ann m)
    exact iteration_pre .refl ((StateStmt.pure_unit_reaches ann pann env F m).trans pop)
      (ih hat pends' (TyRun.inv_withEnv (inv.focus ann) henv) keys cov matched (by simpa using out)
        (hb.focus ann))
  | @save dk P c ann l lty ps body hs seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    obtain ⟨vs, ev, rel⟩ := selfParams_evals (file := file) (labels := labels) inv keys ps hs
    have src := LoopReach.save_reaches (file := file) (labels := labels) ann (l, lty) ps body env vs ev F m
    exact iteration_pre .refl src
      (ih hat pends (rebinds (inv.focus ann) rel) keys cov matched (by simpa using out) (hb.focus ann))
  | @goto dk P ann l args hj =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    have blk : p.block? 0 i = some ⟨([] : List (Lir.Op Mir.Reg)).map .op, .jump (idx l.key)⟩ :=
      (LoopLink.link_block bs i).trans hat
    exact .inr (.inl (jump_iter hlook hcodes hj inv keys cov pends.noBoundary matched out hb
      (jump_steps blk (fr := fr) (mem := mem) rfl)))
  | @abort dk e P hab =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    have blk : p.block? 0 i = some ⟨StateExitLink.abortOps.map .op, .trap⟩ :=
      (LoopLink.link_block bs i).trans hat
    obtain ⟨m', reach, hout⟩ := AbortCall.abortStmt_reaches (labels := labels) hab env F m
    obtain ⟨fr', mem', hx, hst⟩ := StateExitLink.abort_exec fr hsize
    have steps := Lir.steps_execOps (p := p) (os := StateExitLink.abortOps)
      (s := ⟨⟨0, i, 0⟩, fr, [], mem⟩) (rest := []) blk (by simp) hx
    have fetch := Lir.Prog.fetch_eq_term (p := p)
      (pt := ⟨0, i, StateExitLink.abortOps.length⟩) blk (by simp)
    have final : Lir.step p ⟨⟨0, i, 0 + StateExitLink.abortOps.length⟩, fr', [], mem'⟩ =
        .trapped mem' := by
      simp [Lir.step, fetch]
    refine .inr (.inr ⟨.trapped mem', ⟨.halt .aborted, [], m'⟩, trivial, ⟨_, steps, final⟩, reach,
      fun o ho => ?_⟩)
    rw [abortObs mem' o hst ho]
    have e : m'.stdout = "" := by rw [hout, out]
    have fin := Sim.Final.abort (c := ⟨.halt .aborted, [], m'⟩) rfl
    simpa [e, Spec.coreBytes] using fin
  | @exit dk e P v hr hv =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hb
    have blk : p.block? 0 i = some ⟨(TyInput.ops regs d (.lit v)).map .op, .ret [.reg d]⟩ :=
      (LoopLink.link_block bs i).trans hat
    obtain ⟨m', reach, hout⟩ := StateExit.exit_reaches (file := file) (labels := labels) e hr env F m hb
    obtain ⟨fr₄, exec₄, res₄, -⟩ := TyInput.ops_exec regs (values (defsOf ds)) (.lit v) trivial d fr
      mem (by intro q hq; simp [Term.vars] at hq)
    let w := BitVec.ofInt 64 v
    have steps := Lir.steps_execOps (p := p) (os := TyInput.ops regs d (.lit v))
      (s := ⟨⟨0, i, 0⟩, fr, [], mem⟩) (rest := []) blk (by simp) exec₄
    have fetch := Lir.Prog.fetch_eq_term (p := p)
      (pt := ⟨0, i, (TyInput.ops regs d (.lit v)).length⟩) blk (by simp)
    have res' : fr₄.regs d = some w := res₄
    have final : Lir.step p ⟨⟨0, i, 0 + (TyInput.ops regs d (.lit v)).length⟩, fr₄, [], mem⟩ =
        .returned [w] mem := by
      simp [Lir.step, fetch, Lir.Frame.readAll, Lir.Frame.read, res']
    refine .inr (.inr ⟨.returned [w] mem, ⟨.halt (.defined (.loaded (.specified (.integer v)))), [], m'⟩,
      trivial, ⟨_, steps, final⟩, reach, fun o ho => ?_⟩)
    rw [obs w o ho]
    have st : w.toNat % 256 = (v % 256).toNat := Fragment.status_ofInt _
    have e : m'.stdout = "" := by rw [hout, out]
    have fin := Sim.Final.exit (c := ⟨.halt (.defined (.loaded (.specified (.integer v)))), [], m'⟩)
      (v := .loaded (.specified (.integer v))) (k := (v % 256).toNat) rfl rfl
    rw [st]
    simpa [e, Spec.coreBytes] using fin

end run

/-! ## The recognised document -/

theorem labelCodes_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : Vars}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} {T : List Key} :
    (zs : List (Sym × (List Sym × EE))) →
    (∀ kc ∈ labelCodes file ret xs tbl D T zs, ∃ z ∈ zs, z.1.key = kc.1 ∧
      Seg file ret xs tbl D T (D z.1.key) z.2.2 [] kc.2) ∧
      List.Sublist ((labelCodes file ret xs tbl D T zs).map (·.1)) (zs.map (·.1.key))
  | [] => by simp [labelCodes]
  | z :: zs => by
    obtain ⟨all, sub⟩ := labelCodes_spec (file := file) (ret := ret) (xs := xs) (tbl := tbl) (D := D)
      (T := T) zs
    unfold labelCodes
    split
    · rcases hw : walk file ret xs tbl D T Cfg.fuel (D z.1.key) z.2.2 [] [] with _ | ⟨c, rest⟩
      · exact ⟨fun kc hkc => by
          obtain ⟨z', hz', h⟩ := all kc hkc
          exact ⟨z', List.mem_cons_of_mem _ hz', h⟩, sub.cons _⟩
      · refine ⟨fun kc hkc => ?_, by simpa using sub.cons_cons z.1.key⟩
        rcases List.mem_cons.mp hkc with rfl | hkc
        · exact ⟨z, List.mem_cons_self, rfl, walk_seg _ hw⟩
        · obtain ⟨z', hz', h⟩ := all kc hkc
          exact ⟨z', List.mem_cons_of_mem _ hz', h⟩
    · exact ⟨fun kc hkc => by
        obtain ⟨z', hz', h⟩ := all kc hkc
        exact ⟨z', List.mem_cons_of_mem _ hz', h⟩, sub.cons _⟩

theorem stable_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : Vars}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} :
    (n : Nat) → {T₀ T : List Key} → {cs : List (Key × Code)} →
    stable file ret xs tbl D n T₀ = some (T, cs) →
    cs = labelCodes file ret xs tbl D T tbl ∧ cs.map (·.1) = T
  | 0, _, _, _, h => by simp [stable] at h
  | n + 1, T₀, T, cs, h => by
    unfold stable at h
    dsimp only at h
    split at h
    · rename_i heq
      cases h
      exact ⟨rfl, heq⟩
    · exact stable_spec n h

/-- **From the start to `main`'s tree**: the globals are placed and the locals created, and the
two runs are related at the root of the tree of `main`'s block; the facts `Seg.run` needs about
the labels hold. -/
theorem recognize_entry (doc : Codec.Document) (P : Plan) (h : recognize doc = some P)
    (args : List String) (mem : Lir.Memory) (fr : Lir.Frame Mir.Reg) :
    ∃ s labels ret tbl T, Spec.coreStart doc args = .ok (s, labels) ∧ ReturnLabel labels ret ∧
      (P.xs.map (·.1.key)).Nodup ∧
      (∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b)) ∧
      (∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
        ∃ c, Seg doc.file ret P.xs tbl P.D T (P.D s.key) b [] c ∧
          At P.blocks (regOf (P.xs.map (·.1.key))) P.xs.length P.idx (P.idx s.key) c) ∧
      ∃ cs fr', Reaches doc.file labels s cs ∧
        Lir.execOps (seedOps (regOf (P.xs.map (·.1.key))) P.xs.length P.globals) fr mem =
          some (fr', mem) ∧
        Rel doc.file ret P.xs tbl P.D T P.blocks P.idx mem ⟨⟨0, 1, 0⟩, fr', [], mem⟩ cs := by
  unfold recognize at h
  cases hgs : TyGlobals.inits doc.file (Globals.definitions doc.file) with
  | none => simp [hgs] at h
  | some gs =>
    simp only [hgs, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i gcond
      cases main : doc.file.main with
      | none => simp [main] at h
      | some sym =>
        cases decl : doc.file.funs.lookup sym with
        | none => simp [main, decl] at h
        | some entry =>
          cases entry <;> try { simp [main, decl] at h }
          case procedure loc marker ty ps body =>
            cases ps with
            | cons p ps => simp [main, decl] at h
            | nil =>
              have hbody : recognizeBody doc.file body gs = some P := by simpa [main, decl] using h
              obtain ⟨s, m, env, xsA, lg, hinit, hout, hkeys, inv₀, fresh₀, hentry⟩ :=
                TyGlobals.initial_reaches_state doc.file (Map.ofList (doc.enumBindings.getD [])) args
                  hgs gcond.1 gcond.2 main decl
              let labels : Labels := Map.ofList (saves body).reverse
              have hlabels : labels = Map.ofList (saves body).reverse := rfl
              unfold recognizeBody at hbody
              split at hbody
              swap
              · cases hbody
              rename_i ann pann bt0 a sann ret bt r info bann pann' r'
              split at hbody
              · rename_i cond
                obtain ⟨hr, unique, gwf⟩ := cond
                split at hbody
                · rename_i xs e hcr
                  split at hbody
                  · rename_i nodup
                    dsimp only at hbody
                    split at hbody
                    · rename_i c0 f0 seen hw1
                      split at hbody
                      · rename_i T codes hstable
                        split at hbody
                        · rename_i entry f2 hentryw
                          cases hbody
                          obtain ⟨hcs, hT⟩ := stable_spec _ hstable
                          let tbl := Cfg.labelTable (.mk ann (.sseq (.mk pann (.base (none, bt0))) a
                            (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r'))))))))
                          let SAVE : EE :=
                            .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
                          have htbl : tbl = saves (.mk ann (.sseq (.mk pann (.base (none, bt0))) a SAVE)) :=
                            Cfg.labelTable_eq _
                          have hret : ReturnLabel labels ret := by
                            refine ⟨r, bann, pann', r', hr, ?_⟩
                            rw [hlabels]
                            exact LoopMain.lookup_saves unique (LoopMain.mem_saves_right (by simp [saves]))
                          have hlook : ∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b) := by
                            intro s qs b hz
                            rw [hlabels]
                            rw [htbl] at hz
                            exact LoopMain.lookup_saves unique hz
                          have tblKeys : (tbl.map (·.1.key)).Nodup := by
                            rw [htbl]
                            have := LoopMain.saves_keys (.mk ann (.sseq (.mk pann (.base (none, bt0))) a SAVE))
                            rw [this]
                            exact unique
                          let g := gs.map (·.1.key)
                          let D := labelDefs (grow doc.file ret xs tbl
                            ((tbl.filter fun z => z.1.key != ret.key).map (·.1.key)) g tbl.length seen) g
                          obtain ⟨allCodes, sub⟩ := labelCodes_spec (file := doc.file) (ret := ret) (xs := xs)
                            (tbl := tbl) (D := D) (T := T) tbl
                          rw [← hcs] at allCodes sub
                          let P : Plan := ⟨xs, entry, codes, D, gs⟩
                          let regs := regOf (xs.map (·.1.key))
                          have codesNodup : (codes.map (·.1)).Nodup := sub.nodup tblKeys
                          refine ⟨s, labels, ret, tbl, T, hinit, hret, nodup, hlook, ?_, ?_⟩
                          · intro s' qs b hz hsT
                            rw [← hT] at hsT
                            obtain ⟨⟨k', c⟩, hm, hk'⟩ := List.mem_map.mp hsT
                            simp only at hk'
                            subst hk'
                            obtain ⟨z, hz', hzk, hseg⟩ := allCodes _ hm
                            have hzs : z = (s', qs, b) :=
                              List.inj_on_of_nodup_map tblKeys hz' hz hzk
                            subst hzs
                            refine ⟨c, hseg, ?_⟩
                            simpa [P, Plan.blocks, Plan.idx, regs, List.cons_append] using
                            emitAll_at regs xs.length P.idx codes codesNodup (entry.size + 1)
                              (⟨(seedOps regs xs.length gs).map .op, .jump 1⟩ ::
                                entry.emit regs xs.length P.idx 1) (by simp [emit_length]) _ c hm
                          · let gv : Vars := gs.map fun g => (g.1, g.2.1)
                            have keys₀ : Keys lg gv := by
                              unfold Keys
                              have := congrArg (List.map fun p : Sym × IntegerType => (p.1.key, p.2)) hkeys
                              simpa [gv, List.map_map, Function.comp_def] using this
                            let k₀ : List Frame :=
                              [.strongBind (.mk pann (.base (none, bt0))) SAVE env, .annotations xsA]
                            have hk₀ : NoBoundary k₀ := by simp [k₀, NoBoundary, hasBoundary]
                            obtain ⟨env₁, m₁, ls₁, reach₁, inv₁, keys₁, out₁, fresh₁⟩ :=
                              creates_reaches_fresh (file := doc.file) (labels := labels)
                                gv a hcr env m lg inv₀ keys₀ fresh₀ k₀
                            have hb₁ : ExitCall.Budget m₁ := by
                              have hlen : ls₁.length = xs.length := by
                                have := congrArg List.length keys₁; simpa using this
                              refine TyRun.budget_of_fresh fresh₁ ?_
                              rw [hlen]
                              refine creates_length gv a hcr ?_
                              have := TyGlobals.inits_length hgs
                              simp only [gv, List.length_map]; omega
                            have gpre : gv <+: xs := creates_prefix gv a hcr
                            have gkeys : ∀ g ∈ gs, g.1.key ∈ xs.map (·.1.key) := by
                              intro g hg
                              exact List.mem_map.mpr ⟨(g.1, g.2.1), gpre.subset
                                (List.mem_map_of_mem (f := fun g => (g.1, g.2.1)) hg), rfl⟩
                            have hgwf : ∀ g ∈ gs, g.2.2.Wf ∧ g.2.2.vars = [] := by
                              intro g hg
                              have := List.all_eq_true.mp gwf g hg
                              simp only [Bool.and_eq_true, List.isEmpty_iff] at this
                              exact ⟨TyState.Term.wf_spec _ this.1, this.2⟩
                            obtain ⟨fr', seed, matched⟩ := seed_exec (xs.map (·.1.key)) xs.length (by simp)
                              gs gkeys (fun g hg => (hgwf g hg).1) (fun g hg => (hgwf g hg).2) fr mem
                            have pre := hentry.trans
                              ((ReturnConst.sequence_reaches doc.file labels ann _ a SAVE env _ m).trans reach₁)
                            refine ⟨_, fr', pre, seed, g, e, [], k₀, entry, 1, env₁, m₁, ls₁,
                              TyGlobals.defs gs, fr', walk_seg _ hentryw, ?_, rfl, rfl, .base hk₀, inv₁,
                              keys₁, ?_, matched, out₁.trans hout, hb₁⟩
                            · have := emit_at regs xs.length P.idx entry 1
                                [⟨(seedOps regs xs.length gs).map .op, .jump 1⟩]
                                (emitAll regs xs.length P.idx (entry.size + 1) codes) rfl
                              simpa [P, Plan.blocks, regs, List.append_assoc] using this
                            · intro q hq
                              obtain ⟨g', hg, hk⟩ := List.mem_map.mp hq
                              unfold TyGlobals.defs
                              cases hf : gs.find? (fun g => g.1.key == q) with
                              | some v => rfl
                              | none =>
                                have hn := List.find?_eq_none.mp hf g' hg
                                simp [hk] at hn
                        · cases hbody
                      · cases hbody
                    · cases hbody
                  · cases hbody
                · cases hbody
              · cases hbody
    · cases h

/-! ## The compiler -/

/-- The artifact of a recognised `main` (`LoopLink.link P.blocks`). -/
def compile (doc : Codec.Document) : Option Spec.Artifact :=
  match recognize doc with
  | some P => (Backend.artifactOf (LoopLink.link P.blocks)).toOption
  | none => none

/-- **Soundness**: every observation of a compiled `main` is allowed by Core. -/
theorem compile_sound (doc : Codec.Document) (a : Spec.Artifact) (h : compile doc = some a) :
    ArtifactSound doc a := by
  unfold compile at h
  split at h
  · rename_i P hP
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    refine LoopLink.link_sound ha ?_ hl hb
    let fr₀ : Lir.Frame Mir.Reg :=
      (Lir.Frame.empty.set 1 (BitVec.ofNat 64 args.length)).set 2 (BitVec.ofNat 64 a.argBase)
    obtain ⟨s, labels, ret, tbl, T, hinit, hret, nodup, hlook, hcodes, cs, fr', reach, seed, rel⟩ :=
      recognize_entry doc P hP args (a.lmem args) fr₀
    right
    have blk : (LoopLink.link P.blocks).prog.block? 0 0 =
        some ⟨(seedOps (regOf (P.xs.map (·.1.key))) P.xs.length P.globals).map .op, .jump 1⟩ := by
      rw [LoopLink.link_block]; rfl
    have toEntry := (jump_steps blk (fr := fr₀) (mem := a.lmem args) seed).to_reflTransGen
    have obs : ∀ (w : Lir.Word) (o : Spec.Obs), LirObs (.returned [w] (a.lmem args)) o →
        o = .exit (w.toNat % 256) [] := fun w o ho => LoopLink.exit_obs ha ho
    have hsize : (a.lmem args).size = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
      simp [Spec.Artifact.lmem, ArgvAbortLink.artifact_memSize ha]
    have abortObs : ∀ (mem' : Lir.Memory) (o : Spec.Obs),
        (a.lmem args).store .b8 (Spec.ctlAddr + 40) (BitVec.ofNat 64 2) = some mem' →
          LirObs (.trapped mem') o → o = .abort [] := by
      intro mem' o hst ho
      obtain ⟨hbase, -, himg⟩ := ConstLink.artifact_layout ha
      simpa [Spec.coreBytes] using
        (CfgOut.initial (by simpa [LoopLink.link] using himg) hbase args hsize).abortObs hst ho
    have step : ∀ ts cs, Rel doc.file ret P.xs tbl P.D T P.blocks P.idx (a.lmem args) ts cs →
        LoopSimAbort.Iteration (LoopLink.link P.blocks).prog doc.file labels
          (Rel doc.file ret P.xs tbl P.D T P.blocks P.idx (a.lmem args)) ts cs := by
      rintro ts cs ⟨dk, e, Pd, F, c, i, env, m, ls, ds, fr, seg, hat, rfl, rfl, pends, inv, keys, cov,
        matched, out, hb⟩
      exact Seg.run hret nodup hlook hcodes obs hsize abortObs seg hat
        pends inv keys cov matched out hb
    refine ⟨s, labels, cs, hinit, reach, ?_, ?_⟩
    · intro b o beh hobs
      exact LoopSimAbort.allowed step rel (LoopSim.behaves_of_steps toEntry beh) hobs
    · intro beh
      exact LoopSimAbort.stuck_ub step rel (LoopSim.behaves_of_steps toEntry beh)
  · cases h

end Silmaril.Compile.Core.Verified.TyCfg
