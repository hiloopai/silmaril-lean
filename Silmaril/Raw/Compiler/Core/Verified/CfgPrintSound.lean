module

public import Silmaril.Compiler.Core.Verified.CfgSound.Defs
public import Silmaril.Compiler.Core.Verified.CfgPotential.Defs
/-! # `main` as a control-flow graph with `printf` statements

The file's global definitions are string literals (`StrLit.litsOf`); `main`'s block creates its
`int` locals below them, and its trees may print (`Cfg.walk` with the literals). The output is
bounded: each label gets a potential (`CfgPotential.infer`), `Cfg.check` accepts every label's tree
against its potential and the entry tree against the room of Lir's output buffer
(`Target.argBase - PrintLink.outBase`). Nothing of the program is run by the compiler: the check
is a walk over the trees' paths with symbolic slot values.

`recognize_entry`: the startup allocates the literals, the block creates the locals, and the two
runs are related at the root of `main`'s tree with the print context of the literals and the
potentials. `compile_sound` is then `Cfg.compile_sound` with that context.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgPrint

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Machine
open StateExpr (Key Term values)
open StateMem (Local Inv defsOf)
open StateStmt (Keys)
open StateLoopStep (Registers)
open ReturnLit (NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open LoopMain (regOf Covers)
open Cfg
open Relation

/-- The room of Lir's output buffer: the most output a compiled `main` may write. -/
def room : Nat := Silmaril.Compile.Forks.CoreComp.Target.argBase - PrintLink.outBase

/-- A recognised `main` with prints: the plan, the literals and the labels' potentials. -/
structure PPlan where
  plan : Plan
  lits : List (Sym × List Int)
  pots : List (Key × Pot)

/-- The potential of a label (`0` for a label without one). -/
def PPlan.pot (pp : PPlan) (l : Key) : Pot := (pp.pots.lookup l).getD ⟨none, 0, 0, 0⟩

/-- The literals' symbols differ from the locals'. -/
def apart (ls : List (Sym × List Int)) (xs : List Sym) : Bool :=
  ls.all fun z => xs.all fun x => z.1.key != x.key

/-- Every label's tree is paid for by its potential, and the entry tree by the buffer's room. -/
def bounded (P : Plan) (pot : Key → Pot) : Bool :=
  P.codes.all (fun z => check pot (pot z.1) rootStore none 0 z.2) &&
    check pot ⟨none, 0, 0, room⟩ (fun _ => .const 0) none 0 P.entry

/-- String literals, then a block of locals with a control-flow graph that prints, its output
bounded by potentials. -/
def recognize (doc : Codec.Document) : Option PPlan := do
  let ls ← StrLit.litsOf doc.file
  let s ← doc.file.main
  let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
  let P ← recognizeBody doc.file body [] (some ls)
  let pots := CfgPotential.infer P
  if apart ls P.xs = true ∧ bounded P (fun l => (pots.lookup l).getD ⟨none, 0, 0, 0⟩) = true then
    some ⟨P, ls, pots⟩
  else none

theorem recognize_parts {doc : Codec.Document} {pp : PPlan} (h : recognize doc = some pp) :
    ∃ sym body, StrLit.litsOf doc.file = some pp.lits ∧ doc.file.main = some sym ∧
      (∃ loc marker ty, doc.file.funs.lookup sym = some (.procedure loc marker ty [] body)) ∧
      recognizeBody doc.file body [] (some pp.lits) = some pp.plan ∧
      apart pp.lits pp.plan.xs = true ∧ bounded pp.plan pp.pot = true := by
  unfold recognize at h
  cases hls : StrLit.litsOf doc.file with
  | none => simp [hls] at h
  | some ls =>
    simp only [hls, Option.bind_eq_bind, Option.bind_some] at h
    cases main : doc.file.main with
    | none => simp [main] at h
    | some sym =>
      simp only [main, Option.bind_some] at h
      cases decl : doc.file.funs.lookup sym with
      | none => simp [decl] at h
      | some entry =>
        cases entry <;> try { simp [decl] at h }
        case procedure loc marker ty ps body =>
          cases ps with
          | cons p ps => simp [decl] at h
          | nil =>
            simp only [decl] at h
            cases hb : recognizeBody doc.file body [] (some ls) with
            | none => simp [hb] at h
            | some P =>
              simp only [hb, Option.bind_some] at h
              split at h
              · rename_i cond
                cases h
                exact ⟨sym, body, rfl, rfl, ⟨loc, marker, ty, by first | exact decl⟩, hb, cond.1, cond.2⟩
              · cases h

theorem room_le : room ≤ 2 ^ 30 := by
  unfold room Silmaril.Compile.Forks.CoreComp.Target.argBase Silmaril.Compile.Forks.CoreComp.Target.memSize
  omega

theorem outBase_le : PrintLink.outBase ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase := by
  unfold PrintLink.outBase Spec.ctlAddr Silmaril.Compile.Forks.CoreComp.Target.argBase Silmaril.Compile.Forks.CoreComp.Target.memSize Silmaril.Compile.Forks.CoreComp.Target.stackSize Silmaril.Compile.Forks.CoreComp.Target.argSize
  omega

theorem values_none : values (defsOf (GlobalsState.defs [])) = fun _ => 0 := by
  funext q
  simp [values, defsOf, GlobalsState.defs, IntExpr.Term.val]

/-- The print context of a recognised plan, with the literals' objects `L`. -/
def ctxOf (pp : PPlan) (L : List PrintMem.Lit) : PrintCtx := ⟨L, Pot.bound pp.pot⟩

/-- **From the start to `main`'s tree**: the literals are allocated, the locals created below
them, and the two runs are related at the root of the tree of `main`'s block with the print
context; the facts `Seg.run` needs about the labels hold. -/
theorem recognize_entry (doc : Codec.Document) (pp : PPlan) (h : recognize doc = some pp)
    (args : List String) (mem : Lir.Memory) (fr : Lir.Frame Mir.Reg)
    (O : Nat → Lir.Memory → String → Prop) (hO : O 1 mem "") :
    ∃ s labels ret tbl T L, Spec.coreStart doc args = .ok (s, labels) ∧ ReturnLabel labels ret ∧
      (pp.plan.xs.map (·.key)).Nodup ∧
      (∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b)) ∧
      (∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
        ∃ c, Seg doc.file ret pp.plan.xs tbl pp.plan.D T (litsOf (some (ctxOf pp L))) (pp.plan.D s.key)
            b [] c ∧
          At pp.plan.blocks (regOf (pp.plan.xs.map (·.key))) pp.plan.xs.length pp.plan.idx
            (pp.plan.idx s.key) c ∧
          LOk (some (ctxOf pp L)) s.key c) ∧
      LitsApart (some (ctxOf pp L)) pp.plan.xs ∧
      ∃ cs fr', Reaches doc.file labels s cs ∧
        Lir.execOps (CfgGlobals.seedOps (regOf (pp.plan.xs.map (·.key))) pp.plan.globals) fr mem =
          some (fr', mem) ∧
        Rel doc.file ret pp.plan.xs tbl pp.plan.D T pp.plan.blocks pp.plan.idx O (some (ctxOf pp L))
          ⟨⟨0, 1, 0⟩, fr', [], mem⟩ cs := by
  obtain ⟨sym, body, hls, main, ⟨loc, marker, ty, decl⟩, hbody, hapart, hbound⟩ := recognize_parts h
  obtain ⟨s, m, env, xsA, hinit, hout, hlit, hdead, hlast, hentry⟩ :=
    StrLit.initial_reaches_body doc.file (Map.ofList (doc.enumBindings.getD [])) args hls main decl
  obtain ⟨L, hL, look, hmem⟩ := PrintMem.of_litEnv pp.lits hlit
  let labels : Labels := Map.ofList (saves body).reverse
  have hlabels : labels = Map.ofList (saves body).reverse := rfl
  simp only [bounded, Bool.and_eq_true, List.all_eq_true] at hbound
  obtain ⟨hcodesB, hentryB⟩ := hbound
  have apartL : LitsApart (some (ctxOf pp L)) pp.plan.xs := by
    intro c hc o ho x hx
    cases hc
    simp only [apart, List.all_eq_true, bne_iff_ne, ne_eq] at hapart
    have := hapart (o.sym, o.cs) (by rw [← hL]; exact List.mem_map.mpr ⟨o, ho, rfl⟩) x hx
    exact this
  have hlitsL : litsOf (some (ctxOf pp L)) = some pp.lits := by
    simp [litsOf, ctxOf, hL]
  generalize hP : pp.plan = P at hbody hcodesB hentryB apartL ⊢
  unfold recognizeBody at hbody
  split at hbody
  swap
  · cases hbody
  rename_i ann pann bt0 a sann ret bt r info bann pann' r'
  split at hbody
  swap
  · cases hbody
  rename_i cond
  obtain ⟨hr, unique⟩ := cond
  split at hbody
  swap
  · cases hbody
  rename_i xs e hcr
  split at hbody
  swap
  · cases hbody
  rename_i nodup
  dsimp only at hbody
  split at hbody
  swap
  · cases hbody
  rename_i c0 f0 seen hw1
  split at hbody
  swap
  · cases hbody
  rename_i T codes hstable
  split at hbody
  swap
  · cases hbody
  rename_i entry f2 hentryw
  cases hbody
  obtain ⟨hcs, hT⟩ := stable_spec _ hstable
  let tbl := labelTable (.mk ann (.sseq (.mk pann (.base (none, bt0))) a
    (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r'))))))))
  let SAVE : EE :=
    .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
  have htbl : tbl = saves (.mk ann (.sseq (.mk pann (.base (none, bt0))) a SAVE)) :=
    labelTable_eq _
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
  let D := labelDefs (grow doc.file ret xs tbl ((tbl.filter fun z => z.1.key != ret.key).map (·.1.key))
    (List.map (fun x : Sym × Int => x.1.key) []) (some pp.lits) tbl.length seen)
    (List.map (fun x : Sym × Int => x.1.key) [])
  obtain ⟨allCodes, sub⟩ := labelCodes_spec (file := doc.file) (ret := ret) (xs := xs)
    (lits := some pp.lits) (tbl := tbl) (D := D) (T := T) tbl
  rw [← hcs] at allCodes sub
  let P : Plan := ⟨xs, entry, codes, D, []⟩
  let regs := regOf (xs.map (·.key))
  have codesNodup : (codes.map (·.1)).Nodup := sub.nodup tblKeys
  refine ⟨s, labels, ret, tbl, T, L, hinit, hret, nodup, hlook, ?_, apartL, ?_⟩
  · intro s' qs b hz hsT
    rw [← hT] at hsT
    obtain ⟨⟨k', c⟩, hm, hk'⟩ := List.mem_map.mp hsT
    simp only at hk'
    subst hk'
    obtain ⟨z, hz', hzk, hseg⟩ := allCodes _ hm
    have hzs : z = (s', qs, b) :=
      List.inj_on_of_nodup_map tblKeys hz' hz hzk
    subst hzs
    refine ⟨c, by rw [hlitsL]; exact hseg, ?_, ?_⟩
    · simpa [P, D, Plan.blocks, Plan.idx, regs, List.cons_append] using
        emitAll_at regs xs.length P.idx codes codesNodup (entry.size + 1)
          (⟨(CfgGlobals.seedOps regs []).map .op, .jump 1⟩ :: entry.emit regs xs.length P.idx 1)
          (by simp [emit_length]) _ c hm
    · intro ctx hc
      cases hc
      exact label_bound (hcodesB _ hm)
  · let k₀ : List Frame :=
      [.strongBind (.mk pann (.base (none, bt0))) SAVE env, .annotations xsA]
    have hk₀ : NoBoundary k₀ := by simp [k₀, NoBoundary, hasBoundary]
    have inv₀ : Inv env m [] (GlobalsState.defs []) :=
      ⟨(fun l hl => by cases hl), (fun l hl => by cases hl), (fun a ha => by cases ha),
        (fun q d hd => by simp [GlobalsState.defs] at hd)⟩
    have apartC : ∀ o ∈ L, ∀ y ∈ xs, o.sym.key ≠ y.key := fun o ho y hy =>
      apartL _ rfl o ho y hy
    obtain ⟨env₁, m₁, ls₁, reach₁, inv₁, keys₁, out₁, look₁, dead₁, earlier₁, lits₁, above₁, room₁⟩ :=
      CfgPrintStart.creates_reaches (file := doc.file) (labels := labels) [] a hcr L env m [] inv₀
        (by simp [Keys]) look apartC hdead ⟨(fun l hl => by cases hl), (fun l hl => by cases hl)⟩ hmem
        (fun o _ l hl => by cases hl) (by simp; omega) k₀
    have hlen : ls₁.length ≤ 1024 := by
      have := congrArg List.length keys₁
      simp only [List.length_map] at this
      rw [this]
      exact LoopMain.creates_length [] a hcr (by simp)
    obtain ⟨fr', seed, matched⟩ := CfgGlobals.seed_exec (xs.map (·.key)) [] (by simp) fr mem
    have pre := hentry.trans
      ((ReturnConst.sequence_reaches doc.file labels ann _ a SAVE env _ m).trans reach₁)
    have centry : entry.cost (Pot.bound pp.pot) (values (defsOf (GlobalsState.defs []))) ≤ room := by
      rw [values_none]; exact entry_bound hentryB
    have rl := room_le
    have ob := outBase_le
    refine ⟨_, fr', pre, seed, [], e, [], k₀, entry, 1, env₁, m₁, ls₁,
      GlobalsState.defs [], fr', mem, ?_, ?_, rfl, rfl, .base hk₀, ?_, inv₁,
      keys₁, (fun q hq => by cases hq), matched, (out₁.trans hout) ▸ hO, ?_,
      (fun c hc => by cases hc; exact look₁), ?_⟩
    · rw [hlitsL]; exact walk_seg _ hentryw
    · have := emit_at regs xs.length P.idx entry 1
        [⟨(CfgGlobals.seedOps regs []).map .op, .jump 1⟩]
        (emitAll regs xs.length P.idx (entry.size + 1) codes) rfl
      simpa [P, D, Plan.blocks, regs, List.append_assoc] using this
    · intro p b env' hm c hc
      cases hc
      simp only [k₀, List.mem_cons, Frame.strongBind.injEq,
        reduceCtorEq, or_false, List.not_mem_nil] at hm
      obtain ⟨-, -, rfl⟩ := hm
      exact look
    · refine ⟨?_, by rw [dead₁]; simp⟩
      unfold Mem.Concrete.nextIntAddress
      omega
    · intro c hc
      cases hc
      refine ⟨⟨(fun j hj => by rw [dead₁] at hj; cases hj), earlier₁, lits₁, above₁, ?_⟩, ?_⟩
      · show 64 + 32 * ((entry.cost (Pot.bound pp.pot) (values (defsOf (GlobalsState.defs []))) : Nat) : Int) ≤ m₁.lastAddress
        omega
      · rw [out₁, hout]
        simp only [Spec.coreBytes, String.toList_empty, List.map_nil, List.length_nil, Nat.add_zero]
        show PrintLink.outBase + entry.cost (Pot.bound pp.pot) (values (defsOf (GlobalsState.defs []))) ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase
        unfold room at centry
        omega

/-! ## The compiler -/

/-- The artifact of a recognised `main` (`LoopLink.link P.blocks`). -/
def compile (doc : Codec.Document) : Option Spec.Artifact :=
  match recognize doc with
  | some pp => (Backend.artifactOf (LoopLink.link pp.plan.blocks)).toOption
  | none => none

/-- **Soundness**: every observation of a compiled `main` is allowed by Core. -/
theorem compile_sound (doc : Codec.Document) (a : Spec.Artifact) (h : compile doc = some a) :
    ArtifactSound doc a := by
  unfold compile at h
  split at h
  · rename_i pp hP
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    refine LoopLink.link_sound ha ?_ hl hb
    let fr₀ : Lir.Frame Mir.Reg :=
      (Lir.Frame.empty.set 1 (BitVec.ofNat 64 args.length)).set 2 (BitVec.ofNat 64 a.argBase)
    let O : Nat → Lir.Memory → String → Prop := fun _ mem s => CfgOut.OutMem mem s
    have hO : O 1 (a.lmem args) "" := by
      obtain ⟨hbase, -, himg⟩ := ConstLink.artifact_layout ha
      exact CfgOut.initial (by simpa [LoopLink.link] using himg) hbase args
        (by simp [Spec.Artifact.lmem, ArgvAbortLink.artifact_memSize ha])
    obtain ⟨s, labels, ret, tbl, T, L, hinit, hret, nodup, hlook, hcodes, apartL, cs, fr', reach, seed,
      rel⟩ := recognize_entry doc pp hP args (a.lmem args) fr₀ O hO
    right
    have blk : (LoopLink.link pp.plan.blocks).prog.block? 0 0 =
        some ⟨(CfgGlobals.seedOps (regOf (pp.plan.xs.map (·.key))) pp.plan.globals).map .op, .jump 1⟩ := by
      rw [LoopLink.link_block]; rfl
    have toEntry := (jump_steps blk (fr := fr₀) (mem := a.lmem args) seed).to_reflTransGen
    have obs : ∀ i mem s (w : Lir.Word) (o : Spec.Obs), O i mem s → LirObs (.returned [w] mem) o →
        o = .exit (w.toNat % 256) (Spec.coreBytes s) := fun _ _ _ _ _ h ho => h.obs ho
    have hsize : ∀ i mem s, O i mem s → mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := fun _ _ _ h => h.size
    have abortObs : ∀ i mem s (mem' : Lir.Memory) (o : Spec.Obs), O i mem s →
        mem.store .b8 (Spec.ctlAddr + 40) (BitVec.ofNat 64 2) = some mem' → LirObs (.trapped mem') o →
          o = .abort (Spec.coreBytes s) := fun _ _ _ _ _ h hst ho => h.abortObs hst ho
    have step : ∀ ts cs, Rel doc.file ret pp.plan.xs tbl pp.plan.D T pp.plan.blocks pp.plan.idx O
        (some (ctxOf pp L)) ts cs →
        LoopSimAbort.Iteration (LoopLink.link pp.plan.blocks).prog doc.file labels
          (Rel doc.file ret pp.plan.xs tbl pp.plan.D T pp.plan.blocks pp.plan.idx O (some (ctxOf pp L)))
          ts cs := by
      rintro ts cs ⟨dk, e, Pd, F, c, i, env, m, ls, ds, fr, mem, seg, hat, rfl, rfl, pends, fok, inv,
        keys, cov, matched, out, hb, henv, hm⟩
      exact Seg.run hret nodup hlook hcodes (fun _ _ _ _ _ h => h) obs hsize abortObs
        (fun _ _ _ => Iff.rfl) apartL seg hat pends fok inv keys cov matched out hb henv hm
    refine ⟨s, labels, cs, hinit, reach, ?_, ?_⟩
    · intro b o beh hobs
      exact LoopSimAbort.allowed step rel (LoopSim.behaves_of_steps toEntry beh) hobs
    · intro beh
      exact LoopSimAbort.stuck_ub step rel (LoopSim.behaves_of_steps toEntry beh)
  · cases h

end Silmaril.Compile.Core.Verified.CfgPrint
