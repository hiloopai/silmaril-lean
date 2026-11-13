module

public import Silmaril.Compiler.Core.Verified.DoMain.Defs
public import Silmaril.Compiler.Core.Verified.LoopMainSound.Defs
/-! # Soundness of body-first integer loops

The header relation is at the beginning of the body, so even an initially
false test executes that body once. Each productive iteration executes the
body, tests its updated registers and slots, and either returns to the header
or exits. `LoopSim` supplies finite and divergent behaviour soundness.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.DoMain

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Machine
open StateExpr (Key Term term values close)
open StateMem (Local Inv Fresh Defined defsOf update ptr)
open StateStmt (assignStmt initStmt uninitStmt retStmt isLocal isFresh Keys Overflows)
open StateLoopStep (Layout Registers)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open Relation
open LoopMain (Pre classifyPre covered stmtAfter isUnit Plan creates labelKeys regOf
  Covers EnvOk layout stmtAfter_ready mem_saves_left mem_saves_right lookup_saves
  creates_reaches creates_saves classifyPre_assign classifyPre_init classifyPre_uninit
  overflows_ub isUnit_inv)

/-- The syntax of a recognised loop that the proofs follow. -/
structure Syn where
  cond : EE
  patB : Pattern Sym
  brk : EE
  patS : Pattern Sym
  rest : EE
  ctx : LoopContext.Context
  label : Sym
  x : Sym
  dk : List Key

/-- What the proofs know about the syntax of the loop of `P`. -/
structure Syn.Ok (syn : Syn) (file : Program) (labels : Labels) (ret : Sym) (P : Plan) : Prop where
  condition : ∃ (ann patann : List Annot) (ty : BaseType) (body cond : EE)
      (rann pann : List Annot) (no : EE),
    syn.cond = .mk ann (.sseq (.mk patann (.base (none, ty))) body cond) ∧
    DoCondition.recognize file P.xs cond = some (P.test,
      .mk rann (.run () syn.label [.mk pann () (.sym syn.x)]), no) ∧
    LoopFallthrough.Shape file body P.body ∧ isUnit no = true
  brk : LoopFallthrough.Shape file syn.brk P.brk
  wildB : ∃ a ty, syn.patB = .mk a (.base (none, ty))
  wildS : ∃ a ty, syn.patS = .mk a (.base (none, ty))
  rest : ∃ (ann pann : List Annot) (ty : BaseType) (r glue : EE),
    syn.rest = .mk ann (.sseq (.mk pann (.base (none, ty))) r glue) ∧ retStmt file ret P.xs r = some P.ret
  frames : ∀ env, ∃ K0, syn.ctx.frames env [] =
    .strongBind syn.patB syn.brk env :: .strongBind syn.patS syn.rest env :: K0 ∧ NoBoundary K0
  lookup : labels.lookup syn.label = some ([syn.x], syn.ctx.fill syn.cond)
  hret : ReturnLabel labels ret
  isLocal : isLocal P.xs syn.x = true
  body : ∃ dB, stmtAfter P.xs syn.dk P.body = some dB ∧ covered dB P.test = true ∧
    ∃ dK, stmtAfter P.xs dB P.brk = some dK ∧ covered dK P.ret = true
  nodup : (P.xs.map (·.key)).Nodup

/-- The two runs at the loop header: Core at the label's body with its continuations, Lir at
block 1, the slots and the registers holding the same definitions. -/
def Header (file : Program) (labels : Labels) (ret : Sym) (P : Plan) (mem : Lir.Memory)
    (ts : Lir.State Mir.Reg) (cs : Spec.CState) : Prop :=
  ∃ syn : Syn, syn.Ok file labels ret P ∧
    ∃ (env envB envS : Env) (m : Mem.Concrete.State) (ls : List Local)
      (ds : Key → Option IntExpr.Term) (fr : Lir.Frame Mir.Reg) (K0 : List Frame),
      cs = ⟨.effectExpr syn.cond env,
        .strongBind syn.patB syn.brk envB :: .strongBind syn.patS syn.rest envS :: K0, m⟩ ∧
      ts = ⟨⟨0, 1, 0⟩, fr, [], mem⟩ ∧ Inv env m ls ds ∧ Keys ls P.xs ∧ Covers syn.dk ds ∧
      Registers (regOf (P.xs.map (·.key))) ds fr ∧ EnvOk envB ls ∧ EnvOk envS ls ∧
      NoBoundary K0 ∧ m.stdout = ""

theorem entry_block (P : Plan) : (LoopLink.link (blocks P)).prog.block? 0 0 =
    some ⟨(P.pre.flatMap (Pre.ops (regOf (P.xs.map (·.key))) P.xs.length)).map .op, .jump 1⟩ := rfl

theorem body_block (P : Plan) : (LoopLink.link (blocks P)).prog.block? 0 1 =
    some (LoopIteration.bodyBlock (regOf (P.xs.map (·.key))) P.xs.length P.body 2) := rfl

theorem test_block (P : Plan) : (LoopLink.link (blocks P)).prog.block? 0 2 =
    some (LoopBlocks.testBlock (regOf (P.xs.map (·.key))) P.xs.length P.test 1 3) := rfl

theorem exit_block (P : Plan) : (LoopLink.link (blocks P)).prog.block? 0 3 =
    some ⟨(P.brk.ops (regOf (P.xs.map (·.key))) P.xs.length ++
      StateExprLir.ops (regOf (P.xs.map (·.key))) P.xs.length P.ret).map .op, .ret [.reg P.xs.length]⟩ :=
  rfl

variable {file : Program} {labels : Labels}

/-- A body-first iteration either returns, jumps back productively, or reaches UB. -/
theorem iteration {ret : Sym} {P : Plan} {mem : Lir.Memory}
    (obs : ∀ (w : Lir.Word) (o : Spec.Obs), LirObs (.returned [w] mem) o →
      o = .exit (w.toNat % 256) [])
    (ts : Lir.State Mir.Reg) (cs : Spec.CState) (h : Header file labels ret P mem ts cs) :
    LoopSim.Iteration (LoopLink.link (blocks P)).prog file labels (Header file labels ret P mem) ts cs := by
  obtain ⟨⟨head, patB, brk, patS, rest, ctx, label, x, dk⟩, ok, env, envB, envS, m, ls, ds, fr, K0,
    rfl, rfl, inv, keys, cov, matched, hB, hS, hK0, out⟩ := h
  obtain ⟨ann, patann, ty, body, cond, rann, pann, no, hhead, hcond, hshape, hno⟩ := ok.condition
  obtain ⟨aB, tyB, hpB⟩ := ok.wildB
  obtain ⟨aS, tyS, hpS⟩ := ok.wildS
  dsimp only at hpB hpS hhead
  subst hpB hpS
  let regs := regOf (P.xs.map (·.key))
  let d := P.xs.length
  let p := (LoopLink.link (blocks P)).prog
  let k : List Frame := .strongBind (.mk aB (.base (none, tyB))) brk envB ::
    .strongBind (.mk aS (.base (none, tyS))) rest envS :: K0
  have hk : NoBoundary k := noBoundary_cons (noBoundary_cons hK0 trivial) trivial
  obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys ok.isLocal
  have lay := layout keys
  obtain ⟨dB, hdB, htB, dK, hdK, hretK⟩ := ok.body
  obtain ⟨ready, covB⟩ := stmtAfter_ready keys P.body hdB cov
  let KB := Frame.strongBind (.mk patann (.base (none, ty))) cond env :: k
  have enter : Reaches file labels ⟨.effectExpr head env, k, m⟩
      ⟨.effectExpr body env, KB, m⟩ := by
    rw [hhead]
    exact ReturnConst.sequence_reaches file labels ann _ body cond env k m
  rcases hshape.exec inv ready KB regs d lay fr matched mem with
    ub | ⟨mB, frB, outBody, invB, matchedB, runBody, execBody⟩
  · exact .inl (overflows_ub (Overflows.pre enter ub))
  have next := ReturnConst.wildcard_sequence_reaches file labels patann ty .unit cond env k mB
  have srcBody := enter.trans (runBody.trans next)
  have tgtBody := LoopIteration.body_steps regs d P.body 2 p 0 1 (body_block P)
    fr frB [] mem execBody
  have defined := covB.defined htB
  by_cases active : P.test.val (values (defsOf (P.body.defs ds))) = 0
  · rcases DoCondition.test_step hcond invB keys defined k regs d lay frB matchedB p 0 2 1 3
        (test_block P) [] mem with ub | ⟨env₁, m₁, fr₁, out₁, inv₁, match₁, src₁, tgt₁⟩
    · exact .inl (overflows_ub (Overflows.pre srcBody ub))
    rw [ite_eq_left_of_eq_true _ _ (eq_true active)] at src₁ tgt₁
    obtain ⟨a, b, rfl⟩ := isUnit_inv hno
    let m₂ := focusMemory a m₁
    have s₂ := StateStmt.pure_unit_reaches (file := file) (labels := labels) a b env₁ k m₁
    have s₃ := ReturnConst.wildcard_sequence_reaches file labels aB tyB .unit brk envB
      (.strongBind (.mk aS (.base (none, tyS))) rest envS :: K0) m₂
    have invB : Inv envB m₂ ls (P.body.defs ds) := { inv₁.focus a with env := hB }
    obtain ⟨readyK, covK⟩ := stmtAfter_ready keys P.brk hdK covB
    have pre₃ := srcBody.trans (src₁.trans (s₂.trans s₃))
    rcases ok.brk.exec invB readyK (.strongBind (.mk aS (.base (none, tyS))) rest envS :: K0) regs d lay
        fr₁ match₁ mem with ub | ⟨m₃, fr₃, out₃, inv₃, match₃, src₄, tgt₄⟩
    · exact .inl (overflows_ub (Overflows.pre pre₃ ub))
    obtain ⟨annR, pannR, tyR, r, glue, hrest, hr⟩ := ok.rest
    dsimp only at hrest
    subst hrest
    have s₅ := ReturnConst.wildcard_sequence_reaches file labels aS tyS .unit
      (.mk annR (.sseq (.mk pannR (.base (none, tyR))) r glue)) envS K0 m₃
    have s₆ := ReturnConst.sequence_reaches file labels annR (.mk pannR (.base (none, tyR))) r glue
      envS K0 m₃
    have pre₆ := pre₃.trans (src₄.trans (s₅.trans s₆))
    have invS : Inv envS m₃ ls (P.brk.defs (P.body.defs ds)) := { inv₃ with env := hS }
    have hk' : NoBoundary (.strongBind (.mk pannR (.base (none, tyR))) glue envS :: K0) :=
      noBoundary_cons hK0 trivial
    have definedR := covK.defined hretK
    rcases StateStmt.ret_halts ok.hret hr invS keys ok.nodup definedR hk' with
      ⟨okc, m₄, hout, reach⟩ | ⟨s', reach, halt⟩
    · let σ := values (defsOf (P.brk.defs (P.body.defs ds)))
      have okT : P.ret.Ok σ := StateExpr.ok_of_close _ P.ret (invS.defs_ok definedR) okc
      obtain ⟨fr₄, w, exec₄, res₄, val₄, -⟩ := StateExprLir.ops_exec regs σ P.ret d fr₃ mem
        (StateLoopStep.reads lay invS match₃ definedR)
      have hw : w = BitVec.ofInt 64 (P.ret.val σ) := val₄ okT
      let os := P.brk.ops regs d ++ StateExprLir.ops regs d P.ret
      have execAll : Lir.execOps os fr₁ mem = some (fr₄, mem) := by
        simp only [os, Lir.execOps_append, tgt₄, Option.bind_some]
        exact exec₄
      have steps := Lir.steps_execOps (p := p) (os := os) (s := ⟨⟨0, 3, 0⟩, fr₁, [], mem⟩) (rest := [])
        (exit_block P) (by simp [os, regs, d]) execAll
      have fetch := Lir.Prog.fetch_eq_term (p := p) (pt := ⟨0, 3, os.length⟩) (exit_block P)
        (by simp [os, regs, d])
      have res' : fr₄.regs P.xs.length = some w := res₄
      have final : Lir.step p ⟨⟨0, 3, 0 + os.length⟩, fr₄, [], mem⟩ = .returned [w] mem := by
        simp [Lir.step, fetch, Lir.Frame.readAll, Lir.Frame.read, res']
      refine .inr (.inr ⟨_, [w], mem, ⟨.halt (.defined (IntExpr.spec ((close (defsOf (P.brk.defs (P.body.defs ds)))
        P.ret).val 0))), [], m₄⟩, (tgtBody.trans tgt₁).to_reflTransGen.trans steps, final, pre₆.trans reach,
        fun o ho => ?_⟩)
      rw [obs w o ho]
      have st : w.toNat % 256 = ((close (defsOf (P.brk.defs (P.body.defs ds))) P.ret).val 0 % 256).toNat := by
        rw [hw, StateExpr.close_val, Fragment.status_ofInt]
      have e : m₄.stdout = "" := by
        rw [hout, out₃]
        simpa only [m₂, ReturnConst.focusMemory_stdout, out₁] using outBody.trans out
      have fin := Sim.Final.exit (c := ⟨.halt (.defined (IntExpr.spec ((close (defsOf (P.brk.defs (P.body.defs ds)))
        P.ret).val 0))), [], m₄⟩) (v := IntExpr.spec ((close (defsOf (P.brk.defs (P.body.defs ds))) P.ret).val 0))
        (k := ((close (defsOf (P.brk.defs (P.body.defs ds))) P.ret).val 0 % 256).toNat) rfl rfl
      rw [st]
      simpa [e, Spec.coreBytes] using fin
    · exact .inl ⟨s', _, _, pre₆.trans reach, halt⟩
  · rcases DoCondition.test_step hcond invB keys defined k regs d lay frB matchedB p 0 2 1 3
        (test_block P) [] mem with ub | ⟨env₁, m₁, fr₁, out₁, inv₁, match₁, src₁, tgt₁⟩
    · exact .inl (overflows_ub (Overflows.pre srcBody ub))
    simp only [ite_eq_right active] at src₁ tgt₁
    have context := ReturnLit.procedureContext_noBoundary hk labels
    obtain ⟨inv', back⟩ := LoopContext.backedge (file := file) (labels := labels)
      ctx head rann pann label x inv₁ hl key k [] context ok.lookup
    let env' := extendEnv [(x, ptr l)] env₁
    let m' := focusMemory rann m₁
    obtain ⟨K0', hframes, hK0'⟩ := ok.frames env'
    dsimp only at hframes
    refine .inr (.inl ⟨_, ⟨.effectExpr head env', ctx.frames env' [], m'⟩, tgtBody.trans tgt₁, ?_,
      ⟨head, _, brk, _, rest, ctx, label, x, dk⟩, ok, env', env', env', m', ls,
      P.body.defs ds, fr₁, K0', ?_, rfl, inv', keys, cov.defs P.body,
      match₁, inv'.env, inv'.env, hK0', ?_⟩)
    · apply Relation.TransGen.trans_left _ (runBody.trans (next.trans (src₁.trans back)))
      apply Relation.TransGen.single
      refine ⟨.tau, Step.respond (by intro o; simp) ?_⟩
      rw [hhead]
      have req : request file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk patann (.base (none, ty))) body cond)) env, k, m⟩ =
          .next (.effectExpr body env) KB := by simp [request, requestAux, awaitsScheduling, KB]
      rw [req]
      exact Respond.next
    · dsimp only; rw [hframes]
    · simpa only [m', ReturnConst.focusMemory_stdout] using out₁.trans (outBody.trans out)

theorem loopStmt_inv {f : File Codec.wireModel Unit Unit} {xs : List Sym} {s : Eff} {t : Term}
    {sb sk : LoopFallthrough.Stmt} (h : loopStmt f xs s = some (t, sb, sk)) :
    ∃ (aS : List Annot) (pB : List Annot) (tyB : BaseType) (aw : List Annot) (label : Sym) (lty : BaseType)
      (x : Sym) (info : BaseType × Option (Ctype × PassBy)) (xa : List Annot) (head brk : EE)
      (ann patann : List Annot) (ty : BaseType) (rann pann : List Annot) (body cond no : EE),
      s = .mk aS (.sseq (.mk pB (.base (none, tyB)))
        (.mk aw (.save (label, lty) [(x, (info, .mk xa () (.sym x)))] head)) brk) ∧
      head = .mk ann (.sseq (.mk patann (.base (none, ty))) body cond) ∧
      isLocal xs x = true ∧
      DoCondition.recognize f xs cond = some (t,
        .mk rann (.run () label [.mk pann () (.sym x)]), no) ∧
      isUnit no = true ∧ LoopFallthrough.recognize f body = some sb ∧
      LoopFallthrough.recognize f brk = some sk := by
  unfold loopStmt at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, hx⟩ := hc
      split at h
      · split at h
        · rename_i hc'
          obtain ⟨rfl, rfl, hno⟩ := hc'
          split at h
          · cases h
            exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl,
              hx, by assumption, hno, by assumption, by assumption⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **The statements up to the loop**: Core reaches undefined behaviour, or it enters the
loop's label as Lir reaches the test, the two related by `Header`. -/
theorem stmts_entry {ret : Sym} (P : Plan) {mem : Lir.Memory} (hret : ReturnLabel labels ret)
    (nodup : (P.xs.map (·.key)).Nodup) {annM : List Annot} {patM : Pattern Sym} {SAVE : EE}
    (dk : List Key) (e : Eff) {ps : List Pre}
    (h : stmts file ret P.xs dk e = some (ps, P.test, P.body, P.brk, P.ret))
    (lift : ∀ s qs b, (s, qs, b) ∈ saves e → labels.lookup s = some (qs, .mk annM (.sseq patM b SAVE)))
    (env : Env) (m : Mem.Concrete.State) (ls : List Local) (ds : Key → Option IntExpr.Term)
    (inv : Inv env m ls ds) (keys : Keys ls P.xs) (cov : Covers dk ds) (k : List Frame)
    (hk : NoBoundary k) (fr : Lir.Frame Mir.Reg)
    (matched : Registers (regOf (P.xs.map (·.key))) ds fr) (out : m.stdout = "") :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ cs fr', Reaches file labels ⟨.effectExpr e env, k, m⟩ cs ∧
        Lir.execOps (ps.flatMap (Pre.ops (regOf (P.xs.map (·.key))) P.xs.length)) fr mem = some (fr', mem) ∧
        Header file labels ret P mem ⟨⟨0, 1, 0⟩, fr', [], mem⟩ cs := by
  let regs := regOf (P.xs.map (·.key))
  let d := P.xs.length
  have lay := layout keys
  unfold stmts at h
  split at h
  next ann pann ty s rest =>
    let K := Frame.strongBind (.mk pann (.base (none, ty))) rest env :: k
    have enter := ReturnConst.sequence_reaches file labels ann (.mk pann (.base (none, ty))) s rest env k m
    have lift' : ∀ s qs b, (s, qs, b) ∈ saves rest →
        labels.lookup s = some (qs, .mk annM (.sseq patM b SAVE)) :=
      fun s qs b hz => lift s qs b (mem_saves_right hz)
    split at h
    next st hst =>
      split at h
      next dk' hafter =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨ps', r⟩, hrest, eq⟩ := h
        simp only [Prod.mk.injEq] at eq
        obtain ⟨rfl, rfl⟩ := eq
        cases st with
        | assign x t =>
          simp only [Pre.after] at hafter
          split at hafter
          next hc =>
            cases hafter
            obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc.1
            have defined := cov.defined hc.2
            rcases StateStmt.assign_runs (classifyPre_assign hst) inv hl key defined K with
              ub | ⟨ok, m', out', inv', run⟩
            · exact .inl (Overflows.pre enter ub)
            obtain ⟨fr₁, exec₁, res₁, other₁⟩ := StateExprLir.assignOps_exec regs _ d l.sym.key t fr mem ok
              (StateLoopStep.reads lay inv matched defined)
            have matched₁ := StateLoopStep.registers_assign lay inv matched hl res₁ other₁
            have cov₁ : Covers (x.key :: dk) (update ds l.sym.key (some (close (defsOf ds) t))) := by
              intro q hq
              simp only [update]
              split
              · rfl
              · rename_i hne
                exact cov q ((List.mem_cons.mp hq).resolve_left (fun e => hne (e.trans key)))
            have next := enter.trans (run.trans
              (ReturnConst.wildcard_sequence_reaches file labels pann ty .unit rest env k m'))
            rcases stmts_entry P hret nodup _ rest hrest lift' env m' ls _ inv' keys cov₁ k hk fr₁
                matched₁ (out'.trans out) with ub | ⟨cs, fr', reach, exec, header⟩
            · exact .inl (Overflows.pre next ub)
            · refine .inr ⟨cs, fr', next.trans reach, ?_, header⟩
              simp only [List.flatMap_cons, Lir.execOps_append, Pre.ops]
              rw [show x.key = l.sym.key from key, exec₁]
              exact exec
          next => cases hafter
        | init x t =>
          simp only [Pre.after] at hafter
          split at hafter
          next hc =>
            cases hafter
            obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc.1
            have defined := cov.defined hc.2
            rcases StateStmt.init_runs (classifyPre_init hst) inv hl key defined K with
              ub | ⟨ok, m', ys, out', inv', run⟩
            · exact .inl (Overflows.pre enter ub)
            obtain ⟨fr₁, exec₁, res₁, other₁⟩ := StateExprLir.assignOps_exec regs _ d l.sym.key t fr mem ok
              (StateLoopStep.reads lay inv matched defined)
            have matched₁ := StateLoopStep.registers_assign lay inv matched hl res₁ other₁
            have cov₁ : Covers (x.key :: dk) (update ds l.sym.key (some (close (defsOf ds) t))) := by
              intro q hq
              simp only [update]
              split
              · rfl
              · rename_i hne
                exact cov q ((List.mem_cons.mp hq).resolve_left (fun e => hne (e.trans key)))
            have next := enter.trans (run.trans
              (Locals.annotations_bind_reaches ys pann ty .unit rest env k m'))
            rcases stmts_entry P hret nodup _ rest hrest lift' env m' ls _ inv' keys cov₁
                (.annotations ys :: k) (noBoundary_cons hk trivial) fr₁ matched₁ (out'.trans out) with
              ub | ⟨cs, fr', reach, exec, header⟩
            · exact .inl (Overflows.pre next ub)
            · refine .inr ⟨cs, fr', next.trans reach, ?_, header⟩
              simp only [List.flatMap_cons, Lir.execOps_append, Pre.ops]
              rw [show x.key = l.sym.key from key, exec₁]
              exact exec
          next => cases hafter
        | uninit x =>
          simp only [Pre.after] at hafter
          split at hafter
          next hc =>
            cases hafter
            obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc
            obtain ⟨m', ys, out', inv', run⟩ := StateStmt.uninit_runs (classifyPre_uninit hst) inv hl key K
            have matched₁ : Registers regs (update ds l.sym.key none) fr := by
              intro q a ha
              simp only [update] at ha
              split at ha
              · cases ha
              · exact matched q a ha
            have cov₁ : Covers (dk.filter (· != x.key)) (update ds l.sym.key none) := by
              intro q hq
              simp only [List.mem_filter, bne_iff_ne, ne_eq] at hq
              simp only [update]
              split
              · rename_i he; exact absurd (he.trans key.symm) hq.2
              · exact cov q hq.1
            have next := enter.trans (run.trans
              (Locals.annotations_bind_reaches ys pann ty .unit rest env k m'))
            rcases stmts_entry P hret nodup _ rest hrest lift' env m' ls _ inv' keys cov₁
                (.annotations ys :: k) (noBoundary_cons hk trivial) fr matched₁ (out'.trans out) with
              ub | ⟨cs, fr', reach, exec, header⟩
            · exact .inl (Overflows.pre next ub)
            · refine .inr ⟨cs, fr', next.trans reach, ?_, header⟩
              simpa only [List.flatMap_cons, Pre.ops, List.nil_append] using exec
          next => cases hafter
      next => cases h
    next =>
      split at h
      next t sb sk aR pR tyR r glue hloop =>
        split at h
        next dB hdB =>
          split at h
          next dk' tr hdK hr =>
           split at h
           next hc =>
             simp only [Option.some.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, ht, hb, hk', htr⟩ := h
             subst ht hb hk' htr
             obtain ⟨aS, pB, tyB, aw, label, lty, x, info, xa, cond, brk, ann', patann, ty', rann, pann',
               body, condTest, no, rfl, hhead, hx, hcond, hno, hbody, hbrk⟩ := loopStmt_inv hloop
             obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hx
             let patB : Pattern Sym := .mk pB (.base (none, tyB))
             let patS : Pattern Sym := .mk pann (.base (none, ty))
             let REST : EE := .mk aR (.sseq (.mk pR (.base (none, tyR))) r glue)
             let ctx : LoopContext.Context := .strong annM patM SAVE (.strong ann patS REST (.strong aS patB brk .hole))
             have s₁ := ReturnConst.sequence_reaches file labels aS patB
               (.mk aw (.save (label, lty) [(x, (info, .mk xa () (.sym x)))] cond)) brk env K m
             have s₂ := LoopReach.save_reaches (file := file) (labels := labels) aw (label, lty)
               [(x, (info, .mk xa () (.sym x)))] cond env [ptr l]
               (.cons (SeqReach.pure_symbol xa x env _ (inv.lookup hl key)) .nil)
               (.strongBind patB brk env :: K) m
             have hmem : (label, [x], .mk ann (.sseq patS (.mk aS (.sseq patB cond brk)) REST)) ∈
                 saves (.mk ann (.sseq patS (.mk aS (.sseq patB
                   (.mk aw (.save (label, lty) [(x, (info, .mk xa () (.sym x)))] cond)) brk)) REST)) := by
               apply mem_saves_left
               apply mem_saves_left
               simp [saves]
             refine .inr ⟨_, fr, enter.trans (s₁.trans s₂), by simp, ⟨cond, patB, brk, patS, REST, ctx,
               label, x, dk⟩, ?_, extendEnv [(x, ptr l)] env, env, env, focusMemory aw m, ls, ds, fr, k, rfl,
               rfl, LoopTransfer.rebind (inv.focus aw) hl x key, keys, cov, matched, inv.env, inv.env, hk,
               by simpa only [ReturnConst.focusMemory_stdout] using out⟩
             exact {
               condition := ⟨_, _, _, _, _, _, _, _, hhead, hcond, LoopFallthrough.recognize_shape hbody, hno⟩
               brk := LoopFallthrough.recognize_shape hbrk
               wildB := ⟨_, _, rfl⟩
               wildS := ⟨_, _, rfl⟩
               rest := ⟨_, _, _, _, _, rfl, hr⟩
               frames := fun env => ⟨[.strongBind patM SAVE env], rfl, noBoundary_cons rfl trivial⟩
               lookup := lift label [x] _ hmem
               hret := hret
               isLocal := hx
               body := ⟨dB, hdB, hc.1, dk', hdK, hc.2⟩
               nodup := nodup }
           next => cases h
          next => cases h
        next => cases h
      next => cases h
  next => cases h
termination_by sizeOf e

/-- **The whole document up to the loop**, for every argument list and every entry frame. -/
theorem recognize_header (doc : Codec.Document) (P : Plan) (h : recognize doc = some P)
    (args : List String) (mem : Lir.Memory) (fr : Lir.Frame Mir.Reg) :
    ∃ s labels ret, Spec.coreStart doc args = .ok (s, labels) ∧
      (Overflows (file := doc.file) (labels := labels) s ∨
        ∃ cs fr', Reaches doc.file labels s cs ∧
          Lir.execOps (P.pre.flatMap (Pre.ops (regOf (P.xs.map (·.key))) P.xs.length)) fr mem =
            some (fr', mem) ∧
          Header doc.file labels ret P mem ⟨⟨0, 1, 0⟩, fr', [], mem⟩ cs) := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
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
          have hbody : recognizeBody doc.file body = some P := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xsA, hinit, hout, hlast, hdead, hentry⟩ :=
            StartupMem.initial_reaches_body_mem doc.file (Map.ofList (doc.enumBindings.getD [])) args
              hdefs main decl
          have hlabels : labels = Map.ofList (saves body).reverse := by
            simp [initial, main, decl] at hinit
            exact hinit.2.symm
          unfold recognizeBody at hbody
          split at hbody
          swap
          · cases hbody
          rename_i ann pann bt0 a sann ret bt r info bann pann' r'
          split at hbody
          · rename_i cond
            obtain ⟨hr, unique⟩ := cond
            split at hbody
            · rename_i xs e hcr
              split at hbody
              · rename_i nodup
                simp only [Option.map_eq_some_iff] at hbody
                obtain ⟨⟨ps, t, sb, sk, tr⟩, hstmts, rfl⟩ := hbody
                let SAVE : EE :=
                  .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
                have hret : ReturnLabel labels ret := by
                  refine ⟨r, bann, pann', r', hr, ?_⟩
                  rw [hlabels]
                  exact lookup_saves unique (mem_saves_right (by simp [saves]))
                have lift : ∀ s qs b, (s, qs, b) ∈ saves e →
                    labels.lookup s = some (qs, .mk ann (.sseq (.mk pann (.base (none, bt0))) b SAVE)) := by
                  intro s qs b hz
                  rw [hlabels]
                  exact lookup_saves unique (mem_saves_left (creates_saves [] a hcr _ hz))
                have inv₀ : Inv (∅ : Env) m [] (fun _ => none) :=
                  ⟨by simp, by simp, by simp, fun _ _ hd => by cases hd⟩
                have fresh₀ : Fresh m [] := ⟨hdead, by simp, by simp, by simp [hlast]⟩
                let k₀ : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xsA]
                have hk₀ : NoBoundary k₀ := by simp [k₀, NoBoundary, hasBoundary]
                obtain ⟨env₁, m₁, ls₁, reach₁, inv₁, keys₁, out₁⟩ :=
                  creates_reaches (file := doc.file) (labels := labels) [] a hcr ∅ m [] inv₀ rfl fresh₀ k₀
                have pre := hentry.trans ((ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m).trans
                  reach₁)
                refine ⟨s, labels, ret, hinit, ?_⟩
                rcases stmts_entry (file := doc.file) (labels := labels) ⟨xs, ps, t, sb, sk, tr⟩ (mem := mem)
                    hret nodup [] e hstmts lift env₁ m₁ ls₁ (fun _ => none) inv₁ keys₁ (fun _ h => by cases h)
                    k₀ hk₀ fr (fun _ _ h => by simp at h) (out₁.trans hout) with
                  ub | ⟨cs, fr', reach, exec, header⟩
                · exact .inl (Overflows.pre pre ub)
                · exact .inr ⟨cs, fr', pre.trans reach, exec, header⟩
              · cases hbody
            · cases hbody
          · cases hbody

/-! ## The compiler -/

/-- The artifact of a recognised `main` (`LoopLink.link (blocks P)`). -/
def compile (doc : Codec.Document) : Option Spec.Artifact :=
  match recognize doc with
  | some P => (Backend.artifactOf (LoopLink.link (blocks P))).toOption
  | none => none

/-- **Soundness**: every observation of a compiled `main` with a loop is allowed by Core. -/
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
    obtain ⟨s, labels, ret, hinit, rest⟩ := recognize_header doc P hP args (a.lmem args) fr₀
    rcases rest with ub | ⟨cs, fr', reach, exec, header⟩
    · obtain ⟨s', reach, halt⟩ := ub
      exact .inl (.inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩)
    right
    let p := (LoopLink.link (blocks P)).prog
    let os := P.pre.flatMap (Pre.ops (regOf (P.xs.map (·.key))) P.xs.length)
    have steps := Lir.steps_execOps (p := p) (os := os) (s := LoopLink.entryState a args) (rest := [])
      (entry_block P) (by simp [os, LoopLink.entryState]) exec
    have fetch := Lir.Prog.fetch_eq_term (p := p) (pt := ⟨0, 0, os.length⟩) (entry_block P)
      (by simp [os])
    have jump : Lir.Step p ⟨⟨0, 0, 0 + os.length⟩, fr', [], a.lmem args⟩ ⟨⟨0, 1, 0⟩, fr', [], a.lmem args⟩ := by
      change Lir.step p _ = .running _
      simp [Lir.step, fetch]
    have toHeader : Lir.Steps p (LoopLink.entryState a args) ⟨⟨0, 1, 0⟩, fr', [], a.lmem args⟩ :=
      steps.tail jump
    have obs : ∀ (w : Lir.Word) (o : Spec.Obs), LirObs (.returned [w] (a.lmem args)) o →
        o = .exit (w.toNat % 256) [] := fun w o ho => LoopLink.exit_obs ha ho
    refine ⟨s, labels, cs, hinit, reach, ?_, ?_⟩
    · intro b o beh hobs
      exact LoopSim.allowed (iteration obs) header (LoopSim.behaves_of_steps toHeader beh) hobs
    · intro beh
      exact LoopSim.stuck_ub (iteration obs) header (LoopSim.behaves_of_steps toHeader beh)
  · cases h

end Silmaril.Compile.Core.Verified.DoMain
