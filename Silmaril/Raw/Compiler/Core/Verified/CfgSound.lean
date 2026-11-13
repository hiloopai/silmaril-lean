module

public import Silmaril.Compiler.Core.Verified.Cfg.Defs
public import Silmaril.Compiler.Core.Verified.LoopMainSound.Defs
public import Silmaril.Compiler.Core.Verified.RmwSound.Defs
public import Silmaril.Compiler.Core.Verified.LoopSimAbort.Defs
public import Silmaril.Compiler.Core.Verified.CfgOut.Defs
public import Silmaril.Compiler.Core.Verified.CfgPrintBound.Defs
public import Silmaril.Compiler.Core.Verified.CfgPrintStart.Defs
public import Silmaril.Compiler.Core.Verified.CfgBound.Defs
/-! # `main` as a control-flow graph of its saved labels: the proof

`Seg dk e P c` is the derivation that `walk` found: `c` is the code of the Core expression `e`
followed by the pending statements `P`, with the locals `dk` defined. Its Core side is a state
`⟨e, F⟩` whose frames `F` hold `P` as wildcard strong sequences, among annotation frames and
above frames without a procedure boundary (`Pends`). Its Lir side is the block of each node
of `c` (`At`).

`Seg.run`: from a related pair, one `LoopSimAbort.Iteration` follows. Each node runs its statement
in both machines (`StateStmt`, `LoopCondition.test_step`), the pending statements are popped and
pushed as Core does, a `save` is entered in place, `return e;` halts with the value Lir
returns, `exit(n)` halts with `n` (its argument object needs the allocation budget that `Rel`
carries), `abort()` halts aborted as Lir traps after storing the abort word, and `run l(…)` reaches the label's body with its right continuations and empty frames,
as Lir jumps to the first block of the label's tree, where the pair is again related (`Rel`).
The paths to a label are nonempty in both machines: the `run` itself is a Core step and the
jump a Lir step. `LoopSimAbort.allowed` then covers every Lir behaviour, divergence included, from
the entry of `main`'s block (`recognize_entry`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Cfg

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Machine
open StateExpr (Key Term term values close)
open StateMem (Local Inv Fresh Defined defsOf update ptr)
open StateStmt (assignStmt initStmt uninitStmt isLocal isFresh Keys Overflows)
open StateLoopStep (Layout Registers)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open LoopMain (covered regOf Covers EnvOk)
open Relation

/-! ## The label table -/

mutual
theorem labelTable_eq : (e : EE) → labelTable e = saves e
  | .mk _ (.pure _) => by simp [labelTable, saves]
  | .mk _ (.memop _ _) => by simp [labelTable, saves]
  | .mk _ (.action _) => by simp [labelTable, saves]
  | .mk _ (.case_ _ bs) => by simp only [labelTable, saves]; exact labelTableCases_eq bs
  | .mk _ (.let_ _ _ b) => by simp only [labelTable, saves]; exact labelTable_eq b
  | .mk _ (.if_ _ a b) => by simp only [labelTable, saves, labelTable_eq a, labelTable_eq b]
  | .mk _ (.ccall _ _ _ _) => by simp [labelTable, saves]
  | .mk _ (.proc _ _ _) => by simp [labelTable, saves]
  | .mk _ (.unseq es) => by simp only [labelTable, saves]; exact labelTableList_eq es
  | .mk _ (.wseq _ a b) => by
    simp only [labelTable, saves, labelTable_eq a, labelTable_eq b]
  | .mk _ (.sseq _ a b) => by
    simp only [labelTable, saves, labelTable_eq a, labelTable_eq b]
  | .mk _ (.bound _) => by simp [labelTable, saves]
  | .mk _ (.nd _) => by simp [labelTable, saves]
  | .mk _ (.save (s, _) _ b) => by simp only [labelTable, saves, labelTable_eq b]
  | .mk _ (.run _ _ _) => by simp [labelTable, saves]
  | .mk _ (.par _) => by simp [labelTable, saves]
  | .mk _ (.wait _) => by simp [labelTable, saves]
  | .mk _ (.annot _ _) => by simp [labelTable, saves]
  | .mk _ (.excluded _ _) => by simp [labelTable, saves]

theorem labelTableList_eq : (es : List EE) → labelTableList es = savesList es
  | [] => by simp [labelTableList, savesList]
  | e :: es => by simp only [labelTableList, savesList, labelTable_eq e, labelTableList_eq es]

theorem labelTableCases_eq : (bs : List (Pattern Sym × EE)) → labelTableCases bs = savesCases bs
  | [] => by simp [labelTableCases, savesCases]
  | (_, e) :: bs => by simp only [labelTableCases, savesCases, labelTable_eq e, labelTableCases_eq bs]
end

theorem find_mem {tbl : List (Sym × (List Sym × EE))} {l : Sym} {qs : List Sym} {b : EE}
    (h : find tbl l = some (qs, b)) : ∃ s, (s, qs, b) ∈ tbl ∧ s.key = l.key := by
  unfold find at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨s, qs', b'⟩, hf, eq⟩ := h
  cases eq
  exact ⟨s, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-! ## Pending statements -/

/-- The frames `F` hold the pending statements `P` as wildcard strong sequences whose
environments point every local to its object, among annotation frames, above frames without a
procedure boundary. -/
inductive Pends (ls : List Local) : List EE → List Frame → Prop where
  | base {F : List Frame} : NoBoundary F → Pends ls [] F
  | ann {P : List EE} {F : List Frame} (xs : List Access) : Pends ls P F →
      Pends ls P (.annotations xs :: F)
  | bind {P : List EE} {F : List Frame} (pann : List Annot) (ty : BaseType) (b : EE) (env : Env) :
      EnvOk env ls → Pends ls P F →
      Pends ls (b :: P) (.strongBind (.mk pann (.base (none, ty))) b env :: F)

theorem Pends.noBoundary {ls : List Local} {P : List EE} {F : List Frame} (h : Pends ls P F) :
    NoBoundary F := by
  induction h with
  | base h => exact h
  | ann xs _ ih => exact noBoundary_cons ih trivial
  | bind pann ty b env _ _ ih => exact noBoundary_cons ih trivial

variable {file : Program} {labels : Labels}

/-- **The value `unit` pops the next pending statement**, merging and floating annotation
frames as Core does. -/
theorem Pends.pop {ls : List Local} {b : EE} {P : List EE} :
    (F : List Frame) → Pends ls (b :: P) F → (m : Mem.Concrete.State) →
    ∃ env F', EnvOk env ls ∧ Pends ls P F' ∧
      Reaches file labels ⟨.value .unit, F, m⟩ ⟨.effectExpr b env, F', m⟩
  | [], h, _ => by cases h
  | f :: F, h, m => by
    cases h with
    | bind pann ty b env hb h =>
      exact ⟨env, F, hb, h, ReturnConst.wildcard_sequence_reaches file labels pann ty .unit b env F m⟩
    | ann xs h =>
      cases h with
      | bind pann ty b env hb h' =>
        exact ⟨env, _, hb, .ann xs h', Locals.annotations_bind_reaches xs pann ty .unit b env _ m⟩
      | ann ys h' =>
        obtain ⟨env, F', hb, hp, r⟩ := Pends.pop (.annotations (xs ++ ys) :: _) (.ann (xs ++ ys) h') m
        exact ⟨env, F', hb, hp, (Locals.annotations_merge_reaches xs ys .unit _ m).trans r⟩
termination_by F => F.length

/-- Every environment saved in a frame of `F` satisfies `E`. -/
def FramesOk (E : Env → Prop) (F : List Frame) : Prop :=
  ∀ p b env, Frame.strongBind p b env ∈ F → E env

/-- `Pends.pop` for any value (a statement's result is discarded), keeping a property of the
saved environments. -/
theorem Pends.popE {ls : List Local} {b : EE} {P : List EE} (E : Env → Prop) (v : Val) :
    (F : List Frame) → Pends ls (b :: P) F → FramesOk E F → (m : Mem.Concrete.State) →
    ∃ env F', EnvOk env ls ∧ E env ∧ Pends ls P F' ∧ FramesOk E F' ∧
      Reaches file labels ⟨.value v, F, m⟩ ⟨.effectExpr b env, F', m⟩
  | [], h, _, _ => by cases h
  | f :: F, h, hE, m => by
    cases h with
    | bind pann ty b env hb h =>
      exact ⟨env, F, hb, hE _ _ _ List.mem_cons_self, h,
        fun p b' e hm => hE p b' e (List.mem_cons_of_mem _ hm),
        ReturnConst.wildcard_sequence_reaches file labels pann ty v b env F m⟩
    | ann xs h =>
      cases h with
      | bind pann ty b env hb h' =>
        refine ⟨env, _, hb, hE (.mk pann (.base (none, ty))) b env (by simp), .ann xs h', ?_,
          Locals.annotations_bind_reaches xs pann ty v b env _ m⟩
        intro p b' e hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm
        · exact hE p b' e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
      | ann ys h' =>
        obtain ⟨env, F', hb, he, hp, hf, r⟩ :=
          Pends.popE E v (.annotations (xs ++ ys) :: _) (.ann (xs ++ ys) h') (by
            intro p b' e hm
            rcases List.mem_cons.mp hm with hm | hm
            · cases hm
            · exact hE p b' e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))) m
        exact ⟨env, F', hb, he, hp, hf, (Locals.annotations_merge_reaches xs ys v _ m).trans r⟩
termination_by F => F.length

theorem FramesOk.bind {E : Env → Prop} {F : List Frame} (h : FramesOk E F) {env : Env} (he : E env)
    (p : Pattern Sym) (b : EE) : FramesOk E (.strongBind p b env :: F) := by
  intro p' b' e hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm; exact he
  · exact h p' b' e hm

/-! ## Rebinding locals -/

theorem extendEnv_cons (b : Sym × Val) (bs : Bindings) (env : Env) :
    extendEnv (b :: bs) env = extendEnv [b] (extendEnv bs env) := by
  simp [extendEnv]

/-- Rebinding parameters to the objects of their locals keeps `Inv`. -/
theorem rebinds {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) {qs : List Sym} {vs : List Val}
    (h : List.Forall₂ (fun (q : Sym) (v : Val) => ∃ l ∈ ls, q.key = l.sym.key ∧ v = ptr l) qs vs) :
    Inv (extendEnv (qs.zip vs) env) m ls ds := by
  induction h with
  | nil => simpa [extendEnv] using inv
  | cons hqv _ ih =>
    obtain ⟨l, hl, key, hv⟩ := hqv
    subst hv
    rw [List.zip_cons_cons, extendEnv_cons]
    exact LoopTransfer.rebind ih hl _ key

theorem forall₂_keys {ls : List Local} : (qs ys : List Sym) → (vs : List Val) →
    qs.map (·.key) = ys.map (·.key) →
    List.Forall₂ (fun (y : Sym) (v : Val) => ∃ l ∈ ls, y.key = l.sym.key ∧ v = ptr l) ys vs →
    List.Forall₂ (fun (q : Sym) (v : Val) => ∃ l ∈ ls, q.key = l.sym.key ∧ v = ptr l) qs vs
  | [], [], [], _, .nil => .nil
  | q :: qs, y :: ys, v :: vs, h, .cons ⟨l, hl, key, hv⟩ rest => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons ⟨l, hl, h.1.trans key, hv⟩ (forall₂_keys qs ys vs h.2 rest)
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

theorem symArgs_cons {p : PE} {ps : List PE} {ys : List Sym} (h : symArgs (p :: ps) = some ys) :
    ∃ a y ys', p = .mk a () (.sym y) ∧ symArgs ps = some ys' ∧ ys = y :: ys' := by
  rcases p with ⟨a, u, node⟩
  cases u
  cases node <;> simp_all [symArgs]
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨x, h1, h2.symm⟩

/-- The symbol arguments of a `run` evaluate to the objects of their locals. -/
theorem symArgs_evals {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) {xs : List Sym} (keys : Keys ls xs) :
    (args : List PE) → (ys : List Sym) → symArgs args = some ys → ys.all (isLocal xs) = true →
    ∃ vs, List.Forall₂ (fun p v => SeqReach.PureEval file labels p env v) args vs ∧
      List.Forall₂ (fun (y : Sym) (v : Val) => ∃ l ∈ ls, y.key = l.sym.key ∧ v = ptr l) ys vs
  | [], ys, h, _ => by
    simp only [symArgs, Option.some.injEq] at h
    subst h
    exact ⟨[], .nil, .nil⟩
  | p :: ps, ys, h, hl => by
    obtain ⟨a, y, ys', rfl, h', rfl⟩ := symArgs_cons h
    simp only [List.all_cons, Bool.and_eq_true] at hl
    obtain ⟨l, hlm, key⟩ := State.Keys.mem_of_local keys hl.1
    obtain ⟨vs, ev, rel⟩ := symArgs_evals inv keys ps ys' h' hl.2
    exact ⟨ptr l :: vs, .cons (SeqReach.pure_symbol a y env _ (inv.lookup hlm key)) ev,
      .cons ⟨l, hlm, key, rfl⟩ rel⟩

theorem selfParams_evals {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) {xs : List Sym} (keys : Keys ls xs) :
    (ps : List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE))) → selfParams xs ps = true →
    ∃ vs, List.Forall₂ (fun p v => SeqReach.PureEval file labels p env v) (ps.map (fun x => x.2.2)) vs ∧
      List.Forall₂ (fun (q : Sym) (v : Val) => ∃ l ∈ ls, q.key = l.sym.key ∧ v = ptr l)
        (ps.map Prod.fst) vs
  | [], _ => ⟨[], .nil, .nil⟩
  | (x, (i, p)) :: ps, h => by
    rcases p with ⟨a, u, node⟩
    cases u
    cases node <;> simp [selfParams] at h
    rename_i x'
    obtain ⟨⟨hk, hloc⟩, hrest⟩ := h
    obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hloc
    obtain ⟨vs, ev, rel⟩ := selfParams_evals inv keys ps hrest
    exact ⟨ptr l :: vs, .cons (SeqReach.pure_symbol a x' env _ (inv.lookup hl (hk.trans key))) ev,
      .cons ⟨l, hl, key, rfl⟩ rel⟩

/-- **A jump**: the `run` is a Core step, then the arguments and the transfer to the label's
body with its right continuations, under no frames. -/
theorem run_strict (ann : List Annot) (s : Sym) (env : Env) (p : PE) (ps : List PE) (v : Val)
    (vs : List Val) (hp : SeqReach.PureEval file labels p env v)
    (rest : List.Forall₂ (fun p v => SeqReach.PureEval file labels p env v) ps vs)
    (k : List Frame) (hk : NoBoundary k) (params : List Sym) (body : EE)
    (lookup : labels.lookup s = some (params, body)) (arity : params.length = (v :: vs).length)
    (m : Mem.Concrete.State) :
    TransGen (Spec.coreStep file labels) ⟨.effectExpr (.mk ann (.run () s (p :: ps))) env, k, m⟩
      ⟨.effectExpr body (extendEnv (params.zip (v :: vs)) env), [], focusMemory ann m⟩ := by
  have context := ReturnLit.procedureContext_noBoundary hk labels
  have first := Straight.focus_reaches (file := file) (labels := labels) (ann := ann)
    (e := .run () s (p :: ps)) (env := env) (k := k) (m := m) Straight.request_run
  have strict : TransGen (Spec.coreStep file labels)
      ⟨.effectExpr (.mk ann (.run () s (p :: ps))) env, k, m⟩
      ⟨.pureExpr p env, .runLabel s [] ps env :: k, focusMemory ann m⟩ := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp first with eq | h
    · cases eq
    · exact h
  exact strict.trans_left ((hp _ _).trans (LoopReach.run_arguments_reaches rest [] v k []
    (focusMemory ann m) labels params body context lookup arity))

/-- Zero-argument labels also transfer productively, including loops over globals only. -/
theorem run_nil_strict (ann : List Annot) (s : Sym) (env : Env)
    (k : List Frame) (hk : NoBoundary k) (body : EE)
    (lookup : labels.lookup s = some ([], body)) (m : Mem.Concrete.State) :
    TransGen (Spec.coreStep file labels) ⟨.effectExpr (.mk ann (.run () s [])) env, k, m⟩
      ⟨.effectExpr body env, [], focusMemory ann m⟩ := by
  have context := ReturnLit.procedureContext_noBoundary hk labels
  have resolved := LoopReach.jump_resolves (vs := []) (env := env) context lookup rfl
  have hm : ({m with currentLocation := (focusMemory ann m).currentLocation} : Mem.Concrete.State) =
      focusMemory ann m := by
    unfold focusMemory
    split
    · split <;> rfl
    · rfl
  have hboundary : hasBoundary k = false := hk
  have request_nil : request file labels ⟨.effectExpr (.mk ann (.run () s [])) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.effectExpr body env) []
      else .next (.setLocation (focusMemory ann m).currentLocation (.jumping s [] env)) k := by
    simp only [request, requestAux, awaitsScheduling, requestJump, hboundary,
      Bool.false_eq_true, ↓reduceIte]
    change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.jumping s [] env) k
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.jumping s [] env)) k) with
      | .next (.jumping t vs env') k' => Dynamics.jump labels t vs env' k'
      | r => r) = _
    by_cases he : (focusMemory ann m).currentLocation == m.currentLocation
    · simp [he, resolved, extendEnv]
    · simp [he]
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation
  · have same : focusMemory ann m = m := by
      have he : (focusMemory ann m).currentLocation = m.currentLocation := by simpa using equal
      rw [← hm, he]
    rw [same]
    apply TransGen.single
    refine ⟨.tau, Step.respond (by intro o h; cases h) ?_⟩
    have req : request file labels ⟨.effectExpr (.mk ann (.run () s [])) env, k, m⟩ =
        .next (.effectExpr body env) [] := by
      simpa [equal] using request_nil
    rw [req]
    exact Respond.next
  · have first : Spec.coreStep file labels ⟨.effectExpr (.mk ann (.run () s [])) env, k, m⟩
        ⟨.setLocation (focusMemory ann m).currentLocation (.jumping s [] env), k, m⟩ := by
      refine ⟨.tau, Step.respond (by intro o h; cases h) ?_⟩
      have req : request file labels ⟨.effectExpr (.mk ann (.run () s [])) env, k, m⟩ =
          .next (.setLocation (focusMemory ann m).currentLocation (.jumping s [] env)) k := by
        simpa [equal] using request_nil
      rw [req]
      exact Respond.next
    have update : Reaches file labels
        ⟨.setLocation (focusMemory ann m).currentLocation (.jumping s [] env), k, m⟩
        ⟨.jumping s [] env, k, focusMemory ann m⟩ := by
      apply Straight.update_reaches (by intro o h; cases h)
      simp [request, requestAux, awaitsScheduling, hm]
    have transfer : Spec.coreStep file labels ⟨.jumping s [] env, k, focusMemory ann m⟩
        ⟨.effectExpr body env, [], focusMemory ann m⟩ := by
      refine ⟨.tau, Step.respond (by intro o h; cases h) ?_⟩
      have req : request file labels ⟨.jumping s [] env, k, focusMemory ann m⟩ =
          .next (.effectExpr body env) [] := by
        simp [request, requestAux, awaitsScheduling, requestJump, hboundary, resolved, extendEnv]
      rw [req]
      exact Respond.next
    exact (TransGen.single first).trans_left (update.tail transfer)

/-! ## Blocks -/

/-- Flattened operations then a jump: a nonempty Lir path. -/
theorem jump_steps {p : Lir.Prog Mir.Reg} {i j : Nat} {os : List (Lir.Op Mir.Reg)}
    (block : p.block? 0 i = some ⟨os.map .op, .jump j⟩) {fr fr' : Lir.Frame Mir.Reg}
    {mem : Lir.Memory} (exec : Lir.execOps os fr mem = some (fr', mem)) :
    TransGen (Lir.Step p) ⟨⟨0, i, 0⟩, fr, [], mem⟩ ⟨⟨0, j, 0⟩, fr', [], mem⟩ := by
  have path := Lir.steps_execOps (p := p) (os := os) (s := ⟨⟨0, i, 0⟩, fr, [], mem⟩) (rest := [])
    block (by simp) exec
  have fetch := Lir.Prog.fetch_eq_term (p := p) (pt := ⟨0, i, os.length⟩) block (by simp)
  apply Relation.TransGen.tail' path
  change Lir.step p _ = .running _
  simp [Lir.step, fetch]

/-- A block that changes output memory, followed by its jump. -/
theorem jump_steps_mem {p : Lir.Prog Mir.Reg} {i j : Nat} {os : List (Lir.Op Mir.Reg)}
    (block : p.block? 0 i = some ⟨os.map .op, .jump j⟩) {fr fr' : Lir.Frame Mir.Reg}
    {mem mem' : Lir.Memory} (exec : Lir.execOps os fr mem = some (fr', mem')) :
    TransGen (Lir.Step p) ⟨⟨0, i, 0⟩, fr, [], mem⟩ ⟨⟨0, j, 0⟩, fr', [], mem'⟩ := by
  have path := Lir.steps_execOps (p := p) (os := os) (s := ⟨⟨0, i, 0⟩, fr, [], mem⟩) (rest := [])
    block (by simp) exec
  have fetch := Lir.Prog.fetch_eq_term (p := p) (pt := ⟨0, i, os.length⟩) block (by simp)
  apply Relation.TransGen.tail' path
  change Lir.step p _ = .running _
  simp [Lir.step, fetch]

/-- The blocks of the nodes of a tree whose root is block `i`. -/
def At (bs : List (Lir.Block Mir.Reg)) (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) :
    Nat → Code → Prop
  | i, .atom (.set q t) c =>
    bs[i]? = some ⟨(StateExprLir.assignOps regs d q t).map .op, .jump (i + 1)⟩ ∧
      At bs regs d idx (i + 1) c
  | i, .atom (.clear _) c => bs[i]? = some ⟨[], .jump (i + 1)⟩ ∧ At bs regs d idx (i + 1) c
  | i, .print pre suf t c =>
    bs[i]? = some ⟨(CfgPrintStmt.ops regs d pre suf t).map .op, .jump (i + 1)⟩ ∧
      At bs regs d idx (i + 1) c
  | i, .test direct t y n =>
    bs[i]? = some (LoopBlocks.testBlock regs d (if direct then t else LoopBlocks.coreTest t) (i + 1)
      (i + 1 + y.size)) ∧
      At bs regs d idx (i + 1) y ∧ At bs regs d idx (i + 1 + y.size) n
  | i, .goto l => bs[i]? = some ⟨[], .jump (idx l)⟩
  | i, .ret t => bs[i]? = some ⟨(StateExprLir.ops regs d t).map .op, .ret [.reg d]⟩
  | i, .abort => bs[i]? = some ⟨StateExitLink.abortOps.map .op, .trap⟩

theorem emit_length (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) :
    (c : Code) → (i : Nat) → (c.emit regs d idx i).length = c.size
  | .atom (.set _ _) c, i => by simp [Code.emit, Code.size, emit_length regs d idx c (i + 1)]
  | .atom (.clear _) c, i => by simp [Code.emit, Code.size, emit_length regs d idx c (i + 1)]
  | .print _ _ _ c, i => by simp [Code.emit, Code.size, emit_length regs d idx c (i + 1)]
  | .test _ _ y n, i => by
    simp [Code.emit, Code.size, emit_length regs d idx y, emit_length regs d idx n]
  | .goto _, _ => rfl
  | .ret _, _ => rfl
  | .abort, _ => rfl

/-- The emitted tree is where `At` says, wherever it is placed. -/
theorem emit_at (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) :
    (c : Code) → (i : Nat) → (pre post : List (Lir.Block Mir.Reg)) → pre.length = i →
    At (pre ++ c.emit regs d idx i ++ post) regs d idx i c
  | .atom (.set q t) c, i, pre, post, h => by
    refine ⟨?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d idx c (i + 1)
        (pre ++ [⟨(StateExprLir.assignOps regs d q t).map .op, .jump (i + 1)⟩]) post (by simp [h])
      simpa [Code.emit, List.append_assoc] using this
  | .atom (.clear q) c, i, pre, post, h => by
    refine ⟨?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d idx c (i + 1) (pre ++ [⟨[], .jump (i + 1)⟩]) post (by simp [h])
      simpa [Code.emit, List.append_assoc] using this
  | .print a b t c, i, pre, post, h => by
    refine ⟨?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d idx c (i + 1)
        (pre ++ [⟨(CfgPrintStmt.ops regs d a b t).map .op, .jump (i + 1)⟩]) post (by simp [h])
      simpa [Code.emit, List.append_assoc] using this
  | .test direct t y n, i, pre, post, h => by
    let tb := LoopBlocks.testBlock regs d (if direct then t else LoopBlocks.coreTest t) (i + 1)
      (i + 1 + y.size)
    refine ⟨?_, ?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d idx y (i + 1) (pre ++ [tb]) (n.emit regs d idx (i + 1 + y.size) ++ post)
        (by simp [h])
      simpa [Code.emit, List.append_assoc, tb] using this
    · have := emit_at regs d idx n (i + 1 + y.size) (pre ++ [tb] ++ y.emit regs d idx (i + 1)) post
        (by simp [h, emit_length]; omega)
      simpa [Code.emit, List.append_assoc, tb] using this
  | .goto l, i, pre, post, h => by subst h; simp [Code.emit, At]
  | .ret t, i, pre, post, h => by subst h; simp [Code.emit, At]
  | .abort, i, pre, post, h => by subst h; simp [Code.emit, At]

/-- Each label's tree is at its first block. -/
theorem emitAll_at (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) :
    (cs : List (Key × Code)) → (cs.map (·.1)).Nodup → (i : Nat) → (pre : List (Lir.Block Mir.Reg)) →
    pre.length = i → ∀ l c, (l, c) ∈ cs → At (pre ++ emitAll regs d idx i cs) regs d idx (pos i cs l) c
  | [], _, _, _, _, _, _, hm => by cases hm
  | (l', c') :: cs, nd, i, pre, h, l, c, hm => by
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp hm with eq | hm
    · simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      have := emit_at regs d idx c i pre (emitAll regs d idx (i + c.size) cs) h
      simpa [pos, emitAll, List.append_assoc] using this
    · have hne : l' ≠ l := by
        rintro rfl
        exact nd.1 (List.mem_map.mpr ⟨(l', c), hm, rfl⟩)
      have := emitAll_at regs d idx cs nd.2 (i + c'.size) (pre ++ c'.emit regs d idx i)
        (by simp [h, emit_length]) l c hm
      simpa [pos, hne, emitAll, List.append_assoc] using this

/-! ## The derivations of `walk` -/

/-- `c` is the code of `e` followed by the pending statements `P`, with `dk` defined. -/
inductive Seg (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key)
    (lits : Option (List (Sym × List Int))) :
    List Key → EE → List EE → Code → Prop where
  | retn {dk : List Key} {e : EE} {P : List EE} {t : Term} :
      retStmt file ret xs e = some t → covered dk t = true → Seg file ret xs tbl D T lits dk e P (.ret t)
  | print {dk : List Key} {e b : EE} {P : List EE} {pre suf : List Char} {t : Term} {c : Code} :
      printStmt file lits e = some (pre, suf, t) → covered dk t = true → xs.length < 10 →
      Seg file ret xs tbl D T lits dk b P c →
      Seg file ret xs tbl D T lits dk e (b :: P) (.print pre suf t c)
  | op {dk dk' : List Key} {e b : EE} {P : List EE} {a : Atom} {c : Code} :
      atom file xs dk e = some (a, dk') → Seg file ret xs tbl D T lits dk' b P c →
      Seg file ret xs tbl D T lits dk e (b :: P) (.atom a c)
  | voidCall {dk : List Key} {e b : EE} {P : List EE} {c : Code} :
      VoidCall.recognize file e = true → Seg file ret xs tbl D T lits dk b P c →
      Seg file ret xs tbl D T lits dk e (b :: P) c
  | test {dk : List Key} {e yes no : EE} {P : List EE} {t : Term} {cy cn : Code} :
      LoopCondition.recognize file xs e = some (t, yes, no) → covered dk t = true →
      litFresh lits (LoopCondition.binders e) = true →
      Seg file ret xs tbl D T lits dk yes P cy → Seg file ret xs tbl D T lits dk no P cn →
      Seg file ret xs tbl D T lits dk e P (.test false t cy cn)
  | dtest {dk : List Key} {e yes no : EE} {P : List EE} {t : Term} {cy cn : Code} :
      DoCondition.recognize file xs e = some (t, yes, no) → covered dk t = true →
      litFresh lits (DoCondition.binders e) = true →
      Seg file ret xs tbl D T lits dk yes P cy → Seg file ret xs tbl D T lits dk no P cn →
      Seg file ret xs tbl D T lits dk e P (.test true t cy cn)
  | seq {dk : List Key} {P : List EE} {c : Code} (ann pann : List Annot) (ty : BaseType) (a b : EE) :
      Seg file ret xs tbl D T lits dk a (b :: P) c →
      Seg file ret xs tbl D T lits dk (.mk ann (.sseq (.mk pann (.base (none, ty))) a b)) P c
  | unit {dk : List Key} {b : EE} {P : List EE} {c : Code} (ann pann : List Annot) :
      Seg file ret xs tbl D T lits dk b P c →
      Seg file ret xs tbl D T lits dk (.mk ann (.pure (.mk pann () (.val .unit)))) (b :: P) c
  | save {dk : List Key} {P : List EE} {c : Code} (ann : List Annot) (l : Sym) (lty : BaseType)
      (ps : List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE))) (body : EE) :
      selfParams xs ps = true → Seg file ret xs tbl D T lits dk body P c →
      Seg file ret xs tbl D T lits dk (.mk ann (.save (l, lty) ps body)) P c
  | goto {dk : List Key} {P : List EE} (ann : List Annot) (l : Sym) (args : List PE) :
      jump ret xs tbl D T dk l args = true →
      Seg file ret xs tbl D T lits dk (.mk ann (.run () l args)) P (.goto l.key)
  | abort {dk : List Key} {e : EE} {P : List EE} :
      AbortCall.abortStmt file e = true → Seg file ret xs tbl D T lits dk e P .abort
  | exit {dk : List Key} {e : EE} {P : List EE} {v : Int} :
      ExitCall.recognizeBody file e = some v → -2147483648 ≤ v ∧ v ≤ 2147483647 →
      Seg file ret xs tbl D T lits dk e P (.ret (.lit v))
  | switch {dk : List Key} {e : EE} {P : List EE} {t : Term} {cs : List (Int × Switch.Jump)}
      {d : Switch.Jump} :
      Switch.recognize file xs e = some (t, cs, d) → covered dk t = true →
      litFresh lits (Switch.binders e) = true →
      (d :: cs.map (·.2)).all (fun j => jump ret xs tbl D T dk j.1 j.2) = true →
      Seg file ret xs tbl D T lits dk e P (dispatch t cs d)

theorem walk_seg {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : List Sym}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} {T : List Key}
    {lits : Option (List (Sym × List Int))} :
    (fuel : Nat) → {dk : List Key} → {e : EE} → {P : List EE} → {seen : List (Key × List Key)} →
    {c : Code} → {f : Nat} → {s : List (Key × List Key)} →
    walk file ret xs tbl D T lits fuel dk e P seen = some (c, f, s) →
      Seg file ret xs tbl D T lits dk e P c
  | 0, _, _, _, _, _, _, _, h => by simp [walk] at h
  | fuel + 1, dk, e, P, seen, c, f, s, h => by
    unfold walk at h
    split at h
    · rename_i hab
      cases h
      exact .abort hab
    split at h
    · rename_i v hv
      split at h
      · rename_i hr
        cases h
        exact .exit hv hr
      · cases h
    split at h
    · rename_i t ht
      split at h
      · rename_i hc
        cases h
        exact .retn ht hc
      · cases h
    split at h
    · rename_i pre suf t hp
      split at h
      · rename_i hc
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨c', r⟩, h', eq⟩ := h
          cases eq
          exact .print hp hc.1 hc.2 (walk_seg fuel h')
        · cases h
      · cases h
    · split at h
      · rename_i a dk' ha
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨c', r⟩, h', eq⟩ := h
          cases eq
          exact .op ha (walk_seg fuel h')
        · cases h
      · split at h
        · rename_i hv
          split at h
          · exact .voidCall hv (walk_seg fuel h)
          · cases h
        · split at h
          · rename_i t yes no ht
            split at h
            · rename_i hc
              split at h
              · rename_i cy f' s' hy
                split at h
                · rename_i hlt
                  simp only [Option.map_eq_some_iff] at h
                  obtain ⟨⟨cn, r⟩, hn, eq⟩ := h
                  cases eq
                  exact .test ht hc.1 hc.2 (walk_seg fuel hy) (walk_seg f' hn)
                · cases h
              · cases h
            · cases h
          · split at h
            · rename_i t yes no ht
              split at h
              · rename_i hc
                split at h
                · rename_i cy f' s' hy
                  split at h
                  · rename_i hlt
                    simp only [Option.map_eq_some_iff] at h
                    obtain ⟨⟨cn, r⟩, hn, eq⟩ := h
                    cases eq
                    exact .dtest ht hc.1 hc.2 (walk_seg fuel hy) (walk_seg f' hn)
                  · cases h
                · cases h
              · cases h
            · split at h
              · rename_i t cs d hs
                split at h
                · rename_i hc
                  cases h
                  exact .switch hs hc.1 hc.2.1 hc.2.2
                · cases h
              split at h
              all_goals first
                | cases h
                | exact .seq _ _ _ _ _ (walk_seg fuel h)
                | (split at h
                   all_goals first
                    | exact .unit _ _ (walk_seg fuel h)
                    | (rename_i hs; exact .save _ _ _ _ _ hs (walk_seg fuel h))
                    | (rename_i hj; cases h; exact .goto _ _ _ hj)
                    | cases h)
termination_by fuel => fuel
decreasing_by all_goals omega

/-! ## The simulation -/

/-- Block `i` is one of the blocks of a node that writes no memory (an assignment, a `clear`, a
jump, a test), and continues at block `j`. The output invariant of `Rel` is kept along these
edges; a block that writes output is not one of them. -/
def Edge (regs : Key → Mir.Reg) (d : Nat) (bs : List (Lir.Block Mir.Reg)) (i j : Nat) : Prop :=
  (∃ q t, bs[i]? = some ⟨(StateExprLir.assignOps regs d q t).map .op, .jump j⟩) ∨
    bs[i]? = some ⟨[], .jump j⟩ ∨
    ∃ t y n, bs[i]? = some (LoopBlocks.testBlock regs d t y n) ∧ (j = y ∨ j = n)

/-! ## Printing: the literals and the output still to write -/

/-- What a tree with print nodes needs: the string literals the startup allocated, and a bound
`Φ l σ` on the output (in bytes) still to be written from the root of label `l`'s tree with the
slots `σ`. -/
structure PrintCtx where
  L : List PrintMem.Lit
  Φ : Key → (Key → Int) → Nat

/-- The literals the walk was given. -/
def litsOf : Option PrintCtx → Option (List (Sym × List Int))
  | none => none
  | some c => some (PrintMem.lits c.L)

/-- The environment binds every literal's symbol to its object. -/
def EOk (pc : Option PrintCtx) (env : Env) : Prop :=
  ∀ c : PrintCtx, pc = some c → PrintMem.LookOk c.L env

/-- The tree `c` of the label `l` writes at most `Φ l` before its next jump. -/
def LOk (pc : Option PrintCtx) (l : Key) (c : Code) : Prop :=
  ∀ ctx : PrintCtx, pc = some ctx → ∀ σ, c.cost ctx.Φ σ ≤ ctx.Φ l σ

/-- At the node `c` with the slots `σ`: the literals' objects and the slots' allocation facts,
room for one `printf` allocation per byte still to write, and room in Lir's output buffer. -/
def MOk (pc : Option PrintCtx) (c : Code) (σ : Key → Int) (ls : List Local)
    (m : Mem.Concrete.State) : Prop :=
  ∀ ctx : PrintCtx, pc = some ctx →
    PrintMem.Facts ctx.L ls (64 + 32 * (c.cost ctx.Φ σ : Int)) m ∧
    PrintLink.outBase + (Spec.coreBytes m.stdout).length + c.cost ctx.Φ σ ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase

/-- No literal has the key of a local. -/
def LitsApart (pc : Option PrintCtx) (xs : List Sym) : Prop :=
  ∀ c : PrintCtx, pc = some c → ∀ o ∈ c.L, ∀ x ∈ xs, o.sym.key ≠ x.key

theorem values_set (ds : Key → Option IntExpr.Term) (q : Key) (t : Term) :
    values (defsOf (update ds q (some (close (defsOf ds) t)))) =
      Function.update (values (defsOf ds)) q (t.val (values (defsOf ds))) := by
  funext q'
  by_cases h : q' = q
  · subst h; simp [values, defsOf, update, StateExpr.close_val]
  · simp [values, defsOf, update, h, Function.update]

theorem values_clear (ds : Key → Option IntExpr.Term) (q : Key) :
    values (defsOf (update ds q none)) = Function.update (values (defsOf ds)) q 0 := by
  funext q'
  by_cases h : q' = q
  · subst h; simp [values, defsOf, update, IntExpr.Term.val]
  · simp [values, defsOf, update, h, Function.update]

/-- The Core facts statements keep: the allocation budget of `exit`, and the print facts at a
fixed room. -/
def Keep (pc : Option PrintCtx) (c : Code) (σ : Key → Int) (ls : List Local)
    (m : Mem.Concrete.State) : Prop :=
  ExitCall.Budget m ∧ ∀ ctx : PrintCtx, pc = some ctx →
    PrintMem.Facts ctx.L ls (64 + 32 * (c.cost ctx.Φ σ : Int)) m

theorem keep_closed (pc : Option PrintCtx) (c : Code) (σ : Key → Int) (ls : List Local) :
    PrintMem.Closed (Keep pc c σ ls) ls where
  touched := fun h t => ⟨StateExitMem.budget_touched h.1 t,
    fun x hx => (PrintMem.facts_closed _ _ _).touched (h.2 x hx) t⟩
  excluded := fun n h => ⟨StateExitMem.budget_nextExcluded h.1 n,
    fun x hx => (PrintMem.facts_closed _ _ _).excluded n (h.2 x hx)⟩
  stored := fun v hl h => ⟨StateExitMem.budget_store h.1 _ _ v,
    fun x hx => (PrintMem.facts_closed _ _ _).stored v hl (h.2 x hx)⟩
  unstored := fun hl h => ⟨⟨h.1.room, h.1.fresh⟩,
    fun x hx => (PrintMem.facts_closed _ _ _).unstored hl (h.2 x hx)⟩

/-- `MOk` after a statement that keeps the facts and the output, at a node costing no more. -/
theorem MOk.next {pc : Option PrintCtx} {c c' : Code} {σ σ' : Key → Int} {ls : List Local}
    {m m' : Mem.Concrete.State} (h : MOk pc c σ ls m)
    (keep : ∀ ctx : PrintCtx, pc = some ctx →
      PrintMem.Facts ctx.L ls (64 + 32 * (c.cost ctx.Φ σ : Int)) m')
    (out : m'.stdout = m.stdout)
    (dec : ∀ ctx : PrintCtx, pc = some ctx → c'.cost ctx.Φ σ' ≤ c.cost ctx.Φ σ) :
    MOk pc c' σ' ls m' := by
  intro x hx
  have d := dec x hx
  refine ⟨(keep x hx).mono (by omega), ?_⟩
  rw [out]
  have := (h x hx).2
  omega

theorem MOk.keep {pc : Option PrintCtx} {c : Code} {σ : Key → Int} {ls : List Local}
    {m : Mem.Concrete.State} (h : MOk pc c σ ls m) (hb : ExitCall.Budget m) : Keep pc c σ ls m :=
  ⟨hb, fun x hx => (h x hx).1⟩

/-- Rebinding the parameters of a label to locals keeps the literals' bindings. -/
theorem EOk.rebinds {pc : Option PrintCtx} {env : Env} (h : EOk pc env) {ls : List Local}
    (apart : ∀ c : PrintCtx, pc = some c → ∀ o ∈ c.L, ∀ l ∈ ls, o.sym.key ≠ l.sym.key)
    {qs : List Sym} {vs : List Val}
    (rel : List.Forall₂ (fun (q : Sym) (v : Val) => ∃ l ∈ ls, q.key = l.sym.key ∧ v = ptr l) qs vs) :
    EOk pc (extendEnv (qs.zip vs) env) := by
  intro c hc
  induction rel with
  | nil => simpa [extendEnv] using h c hc
  | cons hqv _ ih =>
    obtain ⟨l, hl, key, -⟩ := hqv
    rw [List.zip_cons_cons, extendEnv_cons]
    exact PrintMem.LookOk.extend ih (fun o ho e => apart c hc o ho l hl (e.trans key)) _

/-- A test's temporaries, fresh for the literals, keep their bindings. -/
theorem EOk.binders {pc : Option PrintCtx} {env env' : Env} (h : EOk pc env) {ys : List Sym}
    (fresh : litFresh (litsOf pc) ys = true)
    (look : ∀ y : Sym, (∀ z ∈ ys, z.key ≠ y.key) → env'.lookup y = env.lookup y) : EOk pc env' := by
  intro c hc o ho
  subst hc
  rw [look o.sym ?_]
  · exact h _ rfl o ho
  · intro z hz e
    simp only [litFresh, litsOf, List.all_eq_true, bne_iff_ne, ne_eq] at fresh
    exact fresh z hz (o.sym, o.cs) (List.mem_map.mpr ⟨o, ho, rfl⟩) e.symm

theorem apart_locals {pc : Option PrintCtx} {xs : List Sym} {ls : List Local} (h : LitsApart pc xs)
    (keys : Keys ls xs) : ∀ c : PrintCtx, pc = some c → ∀ o ∈ c.L, ∀ l ∈ ls, o.sym.key ≠ l.sym.key := by
  intro c hc o ho l hl e
  have hm : l.sym.key ∈ xs.map (·.key) := by
    rw [← keys]; exact List.mem_map_of_mem hl
  obtain ⟨x, hx, hk⟩ := List.mem_map.mp hm
  exact h c hc o ho x hx (e.trans hk.symm)

theorem memOk_of_litEnv {L : List PrintMem.Lit} {env : Env} {m : Mem.Concrete.State}
    (look : PrintMem.LookOk L env) (h : StrLit.LitEnv (PrintMem.lits L) env m) : PrintMem.MemOk L m := by
  intro o ho
  obtain ⟨id, addr, hl, obj, h0, h1⟩ := h o.sym o.cs (List.mem_map.mpr ⟨o, ho, rfl⟩)
  rw [look o ho] at hl
  cases Option.some.inj hl
  exact ⟨obj, h0, h1⟩

theorem coreBytes_append (a b : String) :
    Spec.coreBytes (a ++ b) = Spec.coreBytes a ++ Spec.coreBytes b := by
  simp [Spec.coreBytes]

/-- The two runs at the root of a node: Lir at its block `i`, Core at an expression it is the
code of, with the pending statements in the frames, the slots and registers holding the
definitions `ds` of the defined locals, and the output invariant `O i` relating Lir's memory to
the output Core has written. `O` is a parameter: `compile_sound` uses `CfgOut.OutMem`. With a
print context, the literals stay bound (`EOk`, in the frames too), and the memory holds them and
room for the output still to write from the node (`MOk`, by `Code.cost`). -/
def Rel (file : Program) (ret : Sym) (xs : List Sym)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key)
    (bs : List (Lir.Block Mir.Reg)) (idx : Key → Nat) (O : Nat → Lir.Memory → String → Prop)
    (pc : Option PrintCtx) (ts : Lir.State Mir.Reg) (cs : Spec.CState) : Prop :=
  ∃ (dk : List Key) (e : EE) (P : List EE) (F : List Frame) (c : Code) (i : Nat) (env : Env)
    (m : Mem.Concrete.State) (ls : List Local) (ds : Key → Option IntExpr.Term)
    (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory),
    Seg file ret xs tbl D T (litsOf pc) dk e P c ∧ At bs (regOf (xs.map (·.key))) xs.length idx i c ∧
    ts = ⟨⟨0, i, 0⟩, fr, [], mem⟩ ∧ cs = ⟨.effectExpr e env, F, m⟩ ∧ Pends ls P F ∧
    FramesOk (EOk pc) F ∧
    Inv env m ls ds ∧ Keys ls xs ∧ Covers dk ds ∧ Registers (regOf (xs.map (·.key))) ds fr ∧
    O i mem m.stdout ∧ ExitCall.Budget m ∧ EOk pc env ∧ MOk pc c (values (defsOf ds)) ls m

theorem iteration_pre {p : Lir.Prog Mir.Reg} {I : Lir.State Mir.Reg → Spec.CState → Prop}
    {ts ts' : Lir.State Mir.Reg} {cs cs' : Spec.CState}
    (lir : Lir.Steps p ts ts') (core : Reaches file labels cs cs')
    (h : LoopSimAbort.Iteration p file labels I ts' cs') : LoopSimAbort.Iteration p file labels I ts cs := by
  rcases h with ub | ⟨ts'', cs'', l, c, rel⟩ | ⟨b, c, term, beh, path, fin⟩
  · exact .inl (Sim.UBFrom.prefix core ub)
  · exact .inr (.inl ⟨ts'', cs'', Relation.TransGen.trans_right lir l,
      Relation.TransGen.trans_right core c, rel⟩)
  · exact .inr (.inr ⟨b, c, term, LoopSimAbort.Terminal.behaves_pre lir term beh, core.trans path, fin⟩)

/-! ## Allocation budgets through tests and `x++;` -/

/-- `LoopCondition.test_step`, keeping the memory relation of the source run. -/
theorem loop_test_step {xs : List Sym} {e yes no : EE} {t : Term}
    (shape : LoopCondition.recognize file xs e = some (t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label yesLabel noLabel : Lir.Label)
    (block : p.block? f label =
      some (LoopBlocks.testBlock regs d (LoopBlocks.coreTest t) yesLabel noLabel))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ env' m' fr', LoadTask.Touched m m' ∧ Inv env' m' ls ds ∧ Registers regs ds fr' ∧
        (∀ y : Sym, (∀ z ∈ LoopCondition.binders e, z.key ≠ y.key) → env'.lookup y = env.lookup y) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 1 then no else yes) env', k, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
          ⟨⟨f, if t.val (values (defsOf ds)) = 1 then noLabel else yesLabel, 0⟩, fr', stack, mem⟩ := by
  rcases LoopCondition.runs (labels := labels) shape inv keys defined k with
    ub | ⟨ok, env', m', touched, inv', look, source⟩
  · exact .inl ub
  · obtain ⟨fr', target, below⟩ := LoopBlocks.core_test_steps regs (values (defsOf ds)) d t
      yesLabel noLabel p f label block fr stack mem ok (StateLoopStep.reads layout inv matched defined)
    refine .inr ⟨env', m', fr', touched, inv', ?_, look, source, target⟩
    intro q a ha
    obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
    rw [below _ (by rw [← hk]; exact layout.below l hl)]
    exact matched q a ha

/-- `DoCondition.test_step`, keeping the memory relation of the source run. -/
theorem do_test_step {xs : List Sym} {e yes no : EE} {t : Term}
    (shape : DoCondition.recognize file xs e = some (t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label yesLabel noLabel : Lir.Label)
    (block : p.block? f label = some (LoopBlocks.testBlock regs d t yesLabel noLabel))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ env' m' fr', LoadTask.Touched m m' ∧ Inv env' m' ls ds ∧ Registers regs ds fr' ∧
        (∀ y : Sym, (∀ z ∈ DoCondition.binders e, z.key ≠ y.key) → env'.lookup y = env.lookup y) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 0 then no else yes) env', k, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
          ⟨⟨f, if t.val (values (defsOf ds)) = 0 then noLabel else yesLabel, 0⟩, fr', stack, mem⟩ := by
  rcases DoCondition.runs (labels := labels) shape inv keys defined k with
    ub | ⟨ok, env', m', touched, inv', look, source⟩
  · exact .inl ub
  · obtain ⟨fr', target, below⟩ := LoopBlocks.test_steps regs (values (defsOf ds)) d t
      yesLabel noLabel p f label block fr stack mem ok (StateLoopStep.reads layout inv matched defined)
    refine .inr ⟨env', m', fr', touched, inv', ?_, look, source, target⟩
    intro q a ha
    obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
    rw [below _ (by rw [← hk]; exact layout.below l hl)]
    exact matched q a ha

/-! ## The dispatch of a `switch` -/

theorem cmp_val (t : Term) (k : Int) (σ : Key → Int) :
    (Term.cmp .eq 1 0 t (.lit k)).val σ = if t.val σ = k then 1 else 0 := by
  simp [StateExpr.Term.val, Guard.compare, Guard.holds]

/-- The tests of the dispatch run in Lir to the first block of the label `Switch.select` picks,
reading the registers and keeping every local register. -/
theorem dispatch_steps {bs : List (Lir.Block Mir.Reg)} {regs : Key → Mir.Reg} {d : Nat}
    {idx : Key → Nat} {mem : Lir.Memory} (σ : Key → Int) (t : Term) (ok : t.Ok σ) :
    (cs : List (Int × Switch.Jump)) → (dl : Switch.Jump) → (∀ c ∈ cs, ConvInt.IsInt c.1) → (i : Nat) →
    (fr : Lir.Frame Mir.Reg) →
    (∀ q ∈ t.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q))) →
    At bs regs d idx i (dispatch t cs dl) →
    ∃ fr', TransGen (Lir.Step (LoopLink.link bs).prog) ⟨⟨0, i, 0⟩, fr, [], mem⟩
        ⟨⟨0, idx (Switch.select (t.val σ) cs dl).1.key, 0⟩, fr', [], mem⟩ ∧
      ∀ r < d, fr'.get r = fr.get r
  | [], dl, _, i, fr, _, hat => by
    have blk : (LoopLink.link bs).prog.block? 0 i =
        some ⟨([] : List (Lir.Op Mir.Reg)).map .op, .jump (idx dl.1.key)⟩ :=
      (LoopLink.link_block bs i).trans hat
    exact ⟨fr, jump_steps blk rfl, fun _ _ => rfl⟩
  | (k, l, args) :: cs, dl, hint, i, fr, reads, hat => by
    obtain ⟨blk, hatl, hatn⟩ := hat
    have hk : ConvInt.IsInt k := hint (k, l, args) List.mem_cons_self
    have ok' : (Term.cmp .eq 1 0 t (.lit k)).Ok σ := by
      change t.Ok σ ∧ ConvInt.IsInt k ∧ ConvInt.IsInt 1 ∧ ConvInt.IsInt 0
      exact ⟨ok, hk, by constructor <;> decide, by constructor <;> decide⟩
    have reads' : ∀ q ∈ (Term.cmp .eq 1 0 t (.lit k)).vars,
        regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) := by
      simpa [StateExpr.Term.vars] using reads
    have tb : (LoopLink.link bs).prog.block? 0 i =
        some (LoopBlocks.testBlock regs d (.cmp .eq 1 0 t (.lit k)) (i + 1) (i + 1 + 1)) := by
      simpa [Code.size] using (LoopLink.link_block bs i).trans blk
    obtain ⟨fr₁, test, below⟩ := LoopBlocks.test_steps regs σ d _ (i + 1) (i + 1 + 1)
      (LoopLink.link bs).prog 0 i tb fr [] mem ok' reads'
    rw [cmp_val] at test
    by_cases hv : t.val σ = k
    · simp only [hv, ↓reduceIte, one_ne_zero] at test
      have gb : (LoopLink.link bs).prog.block? 0 (i + 1) =
          some ⟨([] : List (Lir.Op Mir.Reg)).map .op, .jump (idx l.key)⟩ :=
        (LoopLink.link_block bs (i + 1)).trans hatl
      have sel : Switch.select (t.val σ) ((k, l, args) :: cs) dl = (l, args) := by
        simp [Switch.select, hv]
      rw [sel]
      exact ⟨fr₁, test.trans (jump_steps gb rfl), below⟩
    · simp only [hv, ↓reduceIte] at test
      have sel : Switch.select (t.val σ) ((k, l, args) :: cs) dl = Switch.select (t.val σ) cs dl := by
        simp [Switch.select, hv]
      rw [sel]
      have reads₁ : ∀ q ∈ t.vars, regs q < d ∧ fr₁.get (regs q) = some (BitVec.ofInt 64 (σ q)) := by
        intro q hq
        obtain ⟨lt, hr⟩ := reads q hq
        exact ⟨lt, by rw [below _ lt]; exact hr⟩
      obtain ⟨fr', rest, below'⟩ := dispatch_steps σ t ok cs dl (fun c hc => hint c (List.mem_cons_of_mem _ hc))
        (i + 1 + 1) fr₁ reads₁ hatn
      exact ⟨fr', test.trans rest, fun r hr => (below' r hr).trans (below r hr)⟩

/-- A dispatch costs what the label it selects is bounded by. -/
theorem dispatch_cost (Φ : Key → (Key → Int) → Nat) (σ : Key → Int) (t : Term) :
    (cs : List (Int × Switch.Jump)) → (dl : Switch.Jump) →
    (dispatch t cs dl).cost Φ σ = Φ (Switch.select (t.val σ) cs dl).1.key σ
  | [], dl => rfl
  | (k, l, a) :: cs, dl => by
    simp only [dispatch, Code.cost, takesNo, cmp_val, Switch.select]
    by_cases hv : t.val σ = k
    · simp [hv]
    · simp [hv, dispatch_cost Φ σ t cs dl]

section run

variable {ret : Sym} {xs : List Sym} {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key}
  {T : List Key} {bs : List (Lir.Block Mir.Reg)} {idx : Key → Nat}
  {O : Nat → Lir.Memory → String → Prop} {mem : Lir.Memory} {pc : Option PrintCtx}

/-- The output invariant along an edge, with the output unchanged. -/
theorem Edge.keep {regs : Key → Mir.Reg} {d i j : Nat} {mem : Lir.Memory} {s s' : String}
    (mono : ∀ i j mem s, Edge regs d bs i j → O i mem s → O j mem s) (e : Edge regs d bs i j)
    (h : O i mem s) (hs : s' = s) : O j mem s' := hs ▸ mono i j mem s e h

/-- Every path through a switch dispatch preserves the block-indexed output invariant. -/
theorem dispatch_keep {regs : Key → Mir.Reg} {d : Nat}
    (mono : ∀ i j mem s, Edge regs d bs i j → O i mem s → O j mem s)
    (v : Int) (t : Term) : (cs : List (Int × Switch.Jump)) → (dl : Switch.Jump) → (i : Nat) →
    At bs regs d idx i (dispatch t cs dl) → ∀ {s}, O i mem s →
      O (idx (Switch.select v cs dl).1.key) mem s
  | [], dl, i, hat, _, h => mono _ _ _ _ (.inr (.inl hat)) h
  | (k, l, args) :: cs, dl, i, hat, s, h => by
    obtain ⟨blk, hy, hn⟩ := hat
    by_cases hv : v = k
    · simp only [Switch.select, hv, ↓reduceIte]
      exact mono _ _ _ _ (.inr (.inl hy))
        (mono _ _ _ _ (.inr (.inr ⟨_, _, _, blk, .inl rfl⟩)) h)
    · simp only [Switch.select, hv, ↓reduceIte]
      exact dispatch_keep mono v t cs dl _ hn
        (mono _ _ _ _ (.inr (.inr ⟨_, _, _, blk, .inr rfl⟩)) h)

/-- **A jump** to a label of the stable set: the `run` is a nonempty Core path to the label's body
under no frames, and a Lir path that reaches the label's first block relates the two runs again. -/
theorem jump_iter
    (hlook : ∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b))
    (hcodes : ∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
      ∃ c, Seg file ret xs tbl D T (litsOf pc) (D s.key) b [] c ∧
        At bs (regOf (xs.map (·.key))) xs.length idx (idx s.key) c ∧ LOk pc s.key c)
    (apart : LitsApart pc xs)
    {dk : List Key} {l : Sym} {args : List PE} (hj : jump ret xs tbl D T dk l args = true)
    {ann : List Annot} {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {F : List Frame} {fr : Lir.Frame Mir.Reg}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (cov : Covers dk ds) (hF : NoBoundary F)
    (matched : Registers (regOf (xs.map (·.key))) ds fr) (out : O (idx l.key) mem m.stdout)
    (hb : ExitCall.Budget m) (henv : EOk pc env)
    (hm : MOk pc (.goto l.key) (values (defsOf ds)) ls m) {ts : Lir.State Mir.Reg}
    (lir : TransGen (Lir.Step (LoopLink.link bs).prog) ts ⟨⟨0, idx l.key, 0⟩, fr, [], mem⟩) :
    ∃ ts' cs', TransGen (Lir.Step (LoopLink.link bs).prog) ts ts' ∧
      TransGen (Spec.coreStep file labels) ⟨.effectExpr (.mk ann (.run () l args)) env, F, m⟩ cs' ∧
      Rel file ret xs tbl D T bs idx O pc ts' cs' := by
  unfold jump at hj
  split at hj
  · rename_i ys qs b' hys hf
    obtain ⟨-, hT, hkeys, hloc, hdef⟩ := of_decide_eq_true hj
    obtain ⟨s, hmem, hsk⟩ := find_mem hf
    have hlk : labels.lookup l = some (qs, b') := by
      rw [ReturnLit.lookup_key hsk.symm]; exact hlook s qs b' hmem
    obtain ⟨c', seg', hat', lok⟩ := hcodes s qs b' hmem (by rw [hsk]; exact hT)
    obtain ⟨vs, ev, rel⟩ := symArgs_evals (file := file) (labels := labels) inv keys args ys hys hloc
    have relq := forall₂_keys qs ys vs hkeys rel
    have arity : qs.length = vs.length := relq.length_eq
    have core : TransGen (Spec.coreStep file labels)
        ⟨.effectExpr (.mk ann (.run () l args)) env, F, m⟩
        ⟨.effectExpr b' (extendEnv (qs.zip vs) env), [], focusMemory ann m⟩ := by
      cases ev with
      | nil =>
        have hqs : qs = [] := List.eq_nil_of_length_eq_zero arity
        subst qs
        simpa [extendEnv] using run_nil_strict ann l env F hF b' hlk m
      | @cons p0 v ps vs' hp rest =>
        exact run_strict ann l env p0 ps v vs' hp rest F hF qs b' hlk arity m
    refine ⟨_, _, lir, core, ?_⟩
    refine ⟨D l.key, b', [], [], c', idx l.key, _, _, ls, ds, fr, mem, ?_, ?_, rfl, rfl, .base rfl,
      (fun _ _ _ h => by cases h), rebinds (inv.focus ann) relq, keys, ?_, matched, (by simpa using out),
      hb.focus ann, henv.rebinds (apart_locals apart keys) relq,
      hm.next (fun c hc => (PrintMem.facts_closed _ _ _).focus ann (hm c hc).1) (by simp)
        (fun c hc => by have := lok c hc (values (defsOf ds)); rw [hsk] at this; exact this)⟩
    · rw [← hsk]; exact seg'
    · rw [← hsk]; exact hat'
    · intro q hq; exact cov q (hdef q hq)
  · cases hj

/-- **One macro-step from the root of a node**: undefined behaviour, or the return in both
machines, or nonempty paths in both to the root of a label's tree. The output invariant `O` is
kept along the edges of the nodes (`mono`), and gives the size of Lir's memory and the output of
a return (`obs`) and of an abort (`abortObs`); it is Lir's output buffer (`hO`). With a print
context, a print node appends its text in both machines, paid for by the output still to write. -/
theorem Seg.run (hret : ReturnLabel labels ret) (nodup : (xs.map (·.key)).Nodup)
    (hlook : ∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b))
    (hcodes : ∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
      ∃ c, Seg file ret xs tbl D T (litsOf pc) (D s.key) b [] c ∧
        At bs (regOf (xs.map (·.key))) xs.length idx (idx s.key) c ∧ LOk pc s.key c)
    (mono : ∀ i j mem s, Edge (regOf (xs.map (·.key))) xs.length bs i j → O i mem s → O j mem s)
    (obs : ∀ i mem s (w : Lir.Word) (o : Spec.Obs), O i mem s → LirObs (.returned [w] mem) o →
      o = .exit (w.toNat % 256) (Spec.coreBytes s))
    (hsize : ∀ i mem s, O i mem s → mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize)
    (abortObs : ∀ i mem s (mem' : Lir.Memory) (o : Spec.Obs), O i mem s →
      mem.store .b8 (Spec.ctlAddr + 40) (BitVec.ofNat 64 2) = some mem' → LirObs (.trapped mem') o →
        o = .abort (Spec.coreBytes s))
    (hO : ∀ i mem s, O i mem s ↔ CfgOut.OutMem mem s) (apart : LitsApart pc xs)
    {dk : List Key} {e : EE} {P : List EE} {c : Code}
    (seg : Seg file ret xs tbl D T (litsOf pc) dk e P c) :
    ∀ {i : Nat} {env : Env} {m : Mem.Concrete.State} {ls : List Local}
      {ds : Key → Option IntExpr.Term} {F : List Frame} {fr : Lir.Frame Mir.Reg} {mem : Lir.Memory},
    At bs (regOf (xs.map (·.key))) xs.length idx i c → Pends ls P F →
    FramesOk (EOk pc) F → Inv env m ls ds →
    Keys ls xs → Covers dk ds → Registers (regOf (xs.map (·.key))) ds fr → O i mem m.stdout →
    ExitCall.Budget m → EOk pc env → MOk pc c (values (defsOf ds)) ls m →
    LoopSimAbort.Iteration (LoopLink.link bs).prog file labels (Rel file ret xs tbl D T bs idx O pc)
      ⟨⟨0, i, 0⟩, fr, [], mem⟩ ⟨.effectExpr e env, F, m⟩ := by
  let regs := regOf (xs.map (·.key))
  let d := xs.length
  let p := (LoopLink.link bs).prog
  induction seg with
  | @retn dk e P t ht hc =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    have blk : p.block? 0 i = some ⟨(StateExprLir.ops regs d t).map .op, .ret [.reg d]⟩ :=
      (LoopLink.link_block bs i).trans hat
    have defined := cov.defined hc
    have lay := LoopMain.layout keys
    have ks := CfgGlobals.keys_filter keys (fun q => (CfgGlobals.returnKeys e).contains q)
    have nd : ((xs.filter fun x => (CfgGlobals.returnKeys e).contains x.key).map (·.key)).Nodup := by
      simpa only [List.filter_map, Function.comp_def] using
        nodup.filter (fun q => (CfgGlobals.returnKeys e).contains q)
    rcases StateGlobals.ret_halts hret ht inv keys ks
      (fun _ h => (List.mem_filter.mp h).1) nd defined pends.noBoundary with
      ⟨okc, m₄, hout, reach⟩ | ⟨s', reach, halt⟩
    · let σ := values (defsOf ds)
      have okT : t.Ok σ := StateExpr.ok_of_close _ t (inv.defs_ok defined) okc
      obtain ⟨fr₄, w, exec₄, res₄, val₄, -⟩ := StateExprLir.ops_exec regs σ t d fr mem
        (StateLoopStep.reads lay inv matched defined)
      have hw : w = BitVec.ofInt 64 (t.val σ) := val₄ okT
      have steps := Lir.steps_execOps (p := p) (os := StateExprLir.ops regs d t)
        (s := ⟨⟨0, i, 0⟩, fr, [], mem⟩) (rest := []) blk (by simp) exec₄
      have fetch := Lir.Prog.fetch_eq_term (p := p)
        (pt := ⟨0, i, (StateExprLir.ops regs d t).length⟩) blk (by simp)
      have res' : fr₄.regs d = some w := res₄
      have final : Lir.step p ⟨⟨0, i, 0 + (StateExprLir.ops regs d t).length⟩, fr₄, [], mem⟩ =
          .returned [w] mem := by
        simp [Lir.step, fetch, Lir.Frame.readAll, Lir.Frame.read, res']
      refine .inr (.inr ⟨.returned [w] mem, ⟨.halt (.defined (IntExpr.spec ((close (defsOf ds) t).val 0))),
        [], m₄⟩, trivial, ⟨_, steps, final⟩, reach, fun o ho => ?_⟩)
      rw [obs i mem m.stdout w o out ho]
      have st : w.toNat % 256 = ((close (defsOf ds) t).val 0 % 256).toNat := by
        rw [hw, StateExpr.close_val, Fragment.status_ofInt]
      have e : m₄.stdout = m.stdout := hout
      have fin := Sim.Final.exit (c := ⟨.halt (.defined (IntExpr.spec ((close (defsOf ds) t).val 0))),
        [], m₄⟩) (v := IntExpr.spec ((close (defsOf ds) t).val 0))
        (k := ((close (defsOf ds) t).val 0 % 256).toNat) rfl rfl
      rw [st]
      simpa [e, Spec.coreBytes] using fin
    · exact .inl ⟨s', _, _, reach, halt⟩
  | @print dk e b P pre suf t c hp hc hd seg' ih =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    obtain ⟨blk, hat'⟩ := hat
    obtain ⟨ann, e0, lsl, rfl, hlits, shape⟩ := printStmt_some hp
    cases pc with
    | none => cases hlits
    | some ctx =>
      simp only [litsOf, Option.some.injEq] at hlits
      subst hlits
      have lay := LoopMain.layout keys
      have defined := cov.defined hc
      obtain ⟨facts, room⟩ := hm ctx rfl
      have hcost : (Code.print pre suf t c).cost ctx.Φ (values (defsOf ds)) =
          CfgPrintStmt.room pre suf + c.cost ctx.Φ (values (defsOf ds)) := rfl
      rw [hcost] at room
      have hroom : 11 ≤ CfgPrintStmt.room pre suf := by simp only [CfgPrintStmt.room]; omega
      have flast := facts.room
      rw [hcost] at flast
      rcases CfgPrintStmt.step (labels := labels) shape inv facts.earlier defined
          (PrintMem.litEnv (henv ctx rfl) facts.lits) facts.dead (c.cost ctx.Φ (values (defsOf ds)))
          (by push_cast at flast ⊢; omega) lay hd matched ((hO i mem _).mp out) (by omega) ann F with
        ub | ⟨m', fr', mem', ok, src, exec, hout, out', inv', matched', early', lit', dead', frontier⟩
      · exact .inl (LoopMain.overflows_ub ub)
      · obtain ⟨envb, F', henv', hE', pends', fok', pop⟩ :=
          Pends.popE (file := file) (labels := labels) (EOk (some ctx)) _ F pends fok m'
        have blk' : p.block? 0 i =
            some ⟨(CfgPrintStmt.ops regs d pre suf t).map .op, .jump (i + 1)⟩ :=
          (LoopLink.link_block bs i).trans blk
        have hlen : (Spec.coreBytes (PrintfIntStmt.text pre suf (t.val (values (defsOf ds))))).length ≤
            CfgPrintStmt.room pre suf := by
          rw [CfgPrintStmt.items_render, ← CfgPrintStmt.items_room pre suf (t.val (values (defsOf ds)))]
          exact PrintLink.render_length _ (CfgPrintStmt.items_small (t.int_of_ok ok) pre suf)
        have hb' : ExitCall.Budget m' :=
          ⟨by unfold Mem.Concrete.nextIntAddress; omega,
            fun h => lt_irrefl _ (dead' _ h)⟩
        have hm' : MOk (some ctx) c (values (defsOf ds)) ls m' := by
          intro x hx
          cases hx
          refine ⟨⟨dead', early', memOk_of_litEnv (henv ctx rfl) lit', facts.above, frontier⟩, ?_⟩
          rw [hout, coreBytes_append, List.length_append]
          omega
        exact iteration_pre (jump_steps_mem blk' exec).to_reflTransGen (src.trans pop)
          (ih hat' pends' fok' { inv' with env := henv' } keys cov
            matched' ((hO (i + 1) mem' _).mpr out') hb' hE' hm')
  | @op dk dk' e b P a c ha seg' ih =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    have lay := LoopMain.layout keys
    unfold atom at ha
    split at ha
    · rename_i x t hx
      split at ha
      · rename_i hc
        cases ha
        obtain ⟨blk, hat'⟩ := hat
        obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc.1
        have defined := cov.defined hc.2
        rcases PrintMem.assign_runs hx inv hl key defined F (keep_closed pc _ _ ls) (hm.keep hb) with
          ub | ⟨ok, m', out', inv', ⟨hb', facts'⟩, src⟩
        · exact .inl (LoopMain.overflows_ub ub)
        obtain ⟨envb, F', henv', hE', pends', fok', pop⟩ :=
          Pends.popE (file := file) (labels := labels) (EOk pc) .unit F pends fok m'
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
        have blk' : p.block? 0 i =
            some ⟨(StateExprLir.assignOps regs d l.sym.key t).map .op, .jump (i + 1)⟩ := by
          rw [← key]; exact (LoopLink.link_block bs i).trans blk
        have hm' : MOk pc c (values (defsOf (update ds l.sym.key (some (close (defsOf ds) t))))) ls m' :=
          hm.next facts' out' (fun c hc => by rw [values_set, ← key]; simp only [Code.cost, le_refl])
        exact iteration_pre (jump_steps blk' exec₁).to_reflTransGen (src.trans pop)
          (ih hat' pends' fok' { inv' with env := henv' } keys cov₁ matched₁
            (Edge.keep mono (.inl ⟨_, _, blk⟩) out out') hb' hE' hm')
      · cases ha
    · split at ha
      · rename_i x t hx
        split at ha
        · rename_i hc
          cases ha
          obtain ⟨blk, hat'⟩ := hat
          obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc.1
          have defined := cov.defined hc.2
          rcases PrintMem.init_runs hx inv hl key defined F (keep_closed pc _ _ ls) (hm.keep hb) with
            ub | ⟨ok, m', ys, out', inv', ⟨hb', facts'⟩, src⟩
          · exact .inl (LoopMain.overflows_ub ub)
          obtain ⟨envb, F', henv', hE', pends', fok', pop⟩ :=
            Pends.popE (file := file) (labels := labels) (EOk pc) .unit _ (.ann ys pends)
              (fun p b' e hm => fok p b' e ((List.mem_cons.mp hm).resolve_left (by intro h; cases h))) m'
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
          have blk' : p.block? 0 i =
              some ⟨(StateExprLir.assignOps regs d l.sym.key t).map .op, .jump (i + 1)⟩ := by
            rw [← key]; exact (LoopLink.link_block bs i).trans blk
          have hm' : MOk pc c (values (defsOf (update ds l.sym.key (some (close (defsOf ds) t))))) ls m' :=
            hm.next facts' out' (fun c hc => by rw [values_set, ← key]; simp only [Code.cost, le_refl])
          exact iteration_pre (jump_steps blk' exec₁).to_reflTransGen (src.trans pop)
            (ih hat' pends' fok' { inv' with env := henv' } keys cov₁
              matched₁ (Edge.keep mono (.inl ⟨_, _, blk⟩) out out') hb' hE' hm')
        · cases ha
      · split at ha
        · rename_i x hx
          split at ha
          · rename_i hc
            cases ha
            obtain ⟨blk, hat'⟩ := hat
            obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc
            obtain ⟨m', ys, out', inv', ⟨hb', facts'⟩, src⟩ :=
              PrintMem.uninit_runs hx inv hl key F (keep_closed pc _ _ ls) (hm.keep hb)
            obtain ⟨envb, F', henv', hE', pends', fok', pop⟩ :=
              Pends.popE (file := file) (labels := labels) (EOk pc) .unit _ (.ann ys pends)
                (fun p b' e hm => fok p b' e ((List.mem_cons.mp hm).resolve_left (by intro h; cases h))) m'
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
            have blk' : p.block? 0 i = some ⟨([] : List (Lir.Op Mir.Reg)).map .op, .jump (i + 1)⟩ :=
              (LoopLink.link_block bs i).trans blk
            have hm' : MOk pc c (values (defsOf (update ds l.sym.key none))) ls m' :=
              hm.next facts' out' (fun c hc => by rw [values_clear, ← key]; simp only [Code.cost, le_refl])
            exact iteration_pre (jump_steps blk' (fr := fr) (mem := mem) rfl).to_reflTransGen
              (src.trans pop) (ih hat' pends' fok' { inv' with env := henv' }
                keys cov₁ matched₁ (Edge.keep mono (.inr (.inl blk)) out out') hb' hE' hm')
          · cases ha
        · split at ha
          · rename_i x op hx
            split at ha
            · rename_i hc
              cases ha
              obtain ⟨blk, hat'⟩ := hat
              obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc.1
              have defined := cov.defined hc.2
              have hdx : (ds x.key).isSome := by
                simpa [StateMem.Defined, Term.vars] using defined
              rcases Rmw.rmw_runs_closed (labels := labels) hx inv hdx F with
                ub | ⟨ok, m', out', -, closes, inv', src⟩
              · exact .inl (LoopMain.overflows_ub ub)
              have cl := keep_closed pc (.atom (.set x.key (.bin op (.var x.key) (.lit 1))) c)
                (values (defsOf ds)) ls
              have kept := closes _ cl.touched cl.excluded (fun l v hl h => cl.stored v hl h) (hm.keep hb)
              obtain ⟨envb, F', henv', hE', pends', fok', pop⟩ :=
                Pends.popE (file := file) (labels := labels) (EOk pc) .unit F pends fok m'
              obtain ⟨fr₁, exec₁, res₁, other₁⟩ := StateExprLir.assignOps_exec regs _ d l.sym.key
                (.bin op (.var x.key) (.lit 1)) fr mem ok (StateLoopStep.reads lay inv matched defined)
              have matched₁ := StateLoopStep.registers_assign lay inv matched hl res₁ other₁
              rw [← key] at matched₁
              have cov₁ : Covers (x.key :: dk)
                  (update ds x.key (some (close (defsOf ds) (.bin op (.var x.key) (.lit 1))))) := by
                intro q hq
                simp only [update]
                split
                · rfl
                · rename_i hne
                  exact cov q ((List.mem_cons.mp hq).resolve_left hne)
              have blk' : p.block? 0 i = some ⟨(StateExprLir.assignOps regs d l.sym.key
                  (.bin op (.var x.key) (.lit 1))).map .op, .jump (i + 1)⟩ := by
                rw [← key]; exact (LoopLink.link_block bs i).trans blk
              have hm' : MOk pc c (values (defsOf (update ds x.key
                  (some (close (defsOf ds) (.bin op (.var x.key) (.lit 1))))))) ls m' :=
                hm.next kept.2 out' (fun c hc => by rw [values_set]; simp only [Code.cost, le_refl])
              exact iteration_pre (jump_steps blk' exec₁).to_reflTransGen (src.trans pop)
                (ih hat' pends' fok' { inv' with env := henv' } keys cov₁
                  matched₁ (Edge.keep mono (.inl ⟨_, _, blk⟩) out out') kept.1 hE' hm')
            · cases ha
          · cases ha
  | @test dk e yes no P t cy cn ht hc hf sy sn ihy ihn =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    obtain ⟨blk, haty, hatn⟩ := hat
    have lay := LoopMain.layout keys
    rcases loop_test_step ht inv keys (cov.defined hc) F regs d lay fr matched p 0 i (i + 1)
        (i + 1 + cy.size) ((LoopLink.link_block bs i).trans blk) [] mem with
      ub | ⟨env', m', fr', tch, inv', match', look, src, tgt⟩
    · exact .inl (LoopMain.overflows_ub ub)
    · have henv' := henv.binders hf look
      have facts' : ∀ c : PrintCtx, pc = some c →
          PrintMem.Facts c.L ls (64 + 32 * ((Code.test _ t cy cn).cost c.Φ (values (defsOf ds)) : Int)) m' :=
        fun c hc => (PrintMem.facts_closed _ _ _).touched (hm c hc).1 tch
      by_cases hv : t.val (values (defsOf ds)) = 1
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihn hatn pends fok
          inv' keys cov match' (Edge.keep mono (.inr (.inr ⟨_, _, _, blk, .inr rfl⟩)) out tch.stdout)
          (StateExitMem.budget_touched hb tch) henv'
          (hm.next facts' tch.stdout (fun c hc => by simp [Code.cost, takesNo, hv])))
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihy haty pends fok
          inv' keys cov match' (Edge.keep mono (.inr (.inr ⟨_, _, _, blk, .inl rfl⟩)) out tch.stdout)
          (StateExitMem.budget_touched hb tch) henv'
          (hm.next facts' tch.stdout (fun c hc => by simp [Code.cost, takesNo, hv])))
  | @dtest dk e yes no P t cy cn ht hc hf sy sn ihy ihn =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    obtain ⟨blk, haty, hatn⟩ := hat
    have lay := LoopMain.layout keys
    rcases do_test_step ht inv keys (cov.defined hc) F regs d lay fr matched p 0 i (i + 1)
        (i + 1 + cy.size) ((LoopLink.link_block bs i).trans blk) [] mem with
      ub | ⟨env', m', fr', tch, inv', match', look, src, tgt⟩
    · exact .inl (LoopMain.overflows_ub ub)
    · have henv' := henv.binders hf look
      have facts' : ∀ c : PrintCtx, pc = some c →
          PrintMem.Facts c.L ls (64 + 32 * ((Code.test _ t cy cn).cost c.Φ (values (defsOf ds)) : Int)) m' :=
        fun c hc => (PrintMem.facts_closed _ _ _).touched (hm c hc).1 tch
      by_cases hv : t.val (values (defsOf ds)) = 0
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihn hatn pends fok
          inv' keys cov match' (Edge.keep mono (.inr (.inr ⟨_, _, _, blk, .inr rfl⟩)) out tch.stdout)
          (StateExitMem.budget_touched hb tch) henv'
          (hm.next facts' tch.stdout (fun c hc => by simp [Code.cost, takesNo, hv])))
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihy haty pends fok
          inv' keys cov match' (Edge.keep mono (.inr (.inr ⟨_, _, _, blk, .inl rfl⟩)) out tch.stdout)
          (StateExitMem.budget_touched hb tch) henv'
          (hm.next facts' tch.stdout (fun c hc => by simp [Code.cost, takesNo, hv])))
  | @voidCall dk e b P c hc seg' ih =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    obtain ⟨m', touched, run⟩ := VoidCall.recognize_runs (labels := labels) hc env F m
    obtain ⟨envb, F', henv', hE', pends', fok', pop⟩ :=
      Pends.popE (file := file) (labels := labels) (EOk pc) .unit F pends fok m'
    exact iteration_pre .refl (run.trans pop)
      (ih hat pends' fok' { inv.touched touched with env := henv' } keys cov matched
        (by rw [touched.stdout]; exact out) (StateExitMem.budget_touched hb touched) hE'
        (hm.next (fun c hc => (PrintMem.facts_closed _ _ _).touched (hm c hc).1 touched)
          touched.stdout (fun _ _ => le_refl _)))
  | @seq dk P c ann pann ty a b seg' ih =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    exact iteration_pre .refl (ReturnConst.sequence_reaches file labels ann _ a b env F m)
      (ih hat (.bind pann ty b env inv.env pends) (fok.bind henv _ b) inv keys cov matched out hb
        henv hm)
  | @unit dk b P c ann pann seg' ih =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    obtain ⟨envb, F', henv', hE', pends', fok', pop⟩ :=
      Pends.popE (file := file) (labels := labels) (EOk pc) .unit F pends fok (focusMemory ann m)
    exact iteration_pre .refl ((StateStmt.pure_unit_reaches ann pann env F m).trans pop)
      (ih hat pends' fok' { inv.focus ann with env := henv' } keys cov matched (by simpa using out)
        (hb.focus ann) hE'
        (hm.next (fun c hc => (PrintMem.facts_closed _ _ _).focus ann (hm c hc).1) (by simp)
          (fun _ _ => le_refl _)))
  | @save dk P c ann l lty ps body hs seg' ih =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    obtain ⟨vs, ev, rel⟩ := selfParams_evals (file := file) (labels := labels) inv keys ps hs
    have src := LoopReach.save_reaches (file := file) (labels := labels) ann (l, lty) ps body env vs ev F m
    exact iteration_pre .refl src
      (ih hat pends fok (rebinds (inv.focus ann) rel) keys cov matched (by simpa using out)
        (hb.focus ann) (henv.rebinds (apart_locals apart keys) rel)
        (hm.next (fun c hc => (PrintMem.facts_closed _ _ _).focus ann (hm c hc).1) (by simp)
          (fun _ _ => le_refl _)))
  | @goto dk P ann l args hj =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    have blk : p.block? 0 i = some ⟨([] : List (Lir.Op Mir.Reg)).map .op, .jump (idx l.key)⟩ :=
      (LoopLink.link_block bs i).trans hat
    exact .inr (.inl (jump_iter hlook hcodes apart hj inv keys cov pends.noBoundary matched
      (Edge.keep mono (.inr (.inl hat)) out (by simp)) hb henv hm
      (jump_steps blk (fr := fr) (mem := mem) rfl)))
  | @switch dk e P t cs dl hs hc hf hj =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    have lay := LoopMain.layout keys
    have defined := cov.defined hc
    rcases Switch.runs (labels := labels) hs inv keys defined F pends.noBoundary with
      ub | ⟨ok, env', m', ann, k', tch, inv', hk', look, src⟩
    · exact .inl (LoopMain.overflows_ub ub)
    · obtain ⟨fr', lir, below⟩ := dispatch_steps (bs := bs) (idx := idx) (mem := mem)
        (values (defsOf ds)) t ok cs dl (Switch.recognize_int hs) i fr
        (StateLoopStep.reads lay inv matched defined) hat
      have matched' : Registers regs ds fr' := by
        intro q a ha
        obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
        rw [below _ (by rw [← hk]; exact lay.below l hl)]
        exact matched q a ha
      have hjl : jump ret xs tbl D T dk (Switch.select (t.val (values (defsOf ds))) cs dl).1
          (Switch.select (t.val (values (defsOf ds))) cs dl).2 = true := by
        have hall := List.all_eq_true.mp hj
        rcases Switch.select_mem (t.val (values (defsOf ds))) cs dl with h | h
        · rw [h]; exact hall _ List.mem_cons_self
        · exact hall _ (List.mem_cons_of_mem _ h)
      obtain ⟨ts', cs', l1, c1, rel⟩ := jump_iter (ann := ann) hlook hcodes apart hjl inv' keys cov hk'
        matched' (by rw [tch.stdout]; exact dispatch_keep mono _ t cs dl i hat out)
        (StateExitMem.budget_touched hb tch) (henv.binders hf look)
        (hm.next (fun c hc => (PrintMem.facts_closed _ _ _).touched (hm c hc).1 tch) tch.stdout
          (fun c _ => (dispatch_cost c.Φ _ t cs dl).ge)) lir
      exact .inr (.inl ⟨ts', cs', l1, TransGen.trans_right src c1, rel⟩)
  | @abort dk e P hab =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    have blk : p.block? 0 i = some ⟨StateExitLink.abortOps.map .op, .trap⟩ :=
      (LoopLink.link_block bs i).trans hat
    obtain ⟨m', reach, hout⟩ := AbortCall.abortStmt_reaches (labels := labels) hab env F m
    obtain ⟨fr', mem', hx, hst⟩ := StateExitLink.abort_exec fr (hsize i mem _ out)
    have steps := Lir.steps_execOps (p := p) (os := StateExitLink.abortOps)
      (s := ⟨⟨0, i, 0⟩, fr, [], mem⟩) (rest := []) blk (by simp) hx
    have fetch := Lir.Prog.fetch_eq_term (p := p)
      (pt := ⟨0, i, StateExitLink.abortOps.length⟩) blk (by simp)
    have final : Lir.step p ⟨⟨0, i, 0 + StateExitLink.abortOps.length⟩, fr', [], mem'⟩ =
        .trapped mem' := by
      simp [Lir.step, fetch]
    refine .inr (.inr ⟨.trapped mem', ⟨.halt .aborted, [], m'⟩, trivial, ⟨_, steps, final⟩, reach,
      fun o ho => ?_⟩)
    rw [abortObs i mem _ mem' o out hst ho]
    have e : m'.stdout = m.stdout := hout
    have fin := Sim.Final.abort (c := ⟨.halt .aborted, [], m'⟩) rfl
    simpa [e, Spec.coreBytes] using fin
  | @exit dk e P v hr hv =>
    intro i env m ls ds F fr mem hat pends fok inv keys cov matched out hb henv hm
    have blk : p.block? 0 i = some ⟨(StateExprLir.ops regs d (.lit v)).map .op, .ret [.reg d]⟩ :=
      (LoopLink.link_block bs i).trans hat
    have lay := LoopMain.layout keys
    obtain ⟨m', reach, hout⟩ := StateExit.exit_reaches (file := file) (labels := labels) e hr env F m hb
    let σ := values (defsOf ds)
    have okT : (Term.lit v).Ok σ := ⟨hv.1, hv.2⟩
    obtain ⟨fr₄, w, exec₄, res₄, val₄, -⟩ := StateExprLir.ops_exec regs σ (.lit v) d fr mem
      (StateLoopStep.reads lay inv matched (by simp [StateMem.Defined, Term.vars]))
    have hw : w = BitVec.ofInt 64 v := val₄ okT
    have steps := Lir.steps_execOps (p := p) (os := StateExprLir.ops regs d (.lit v))
      (s := ⟨⟨0, i, 0⟩, fr, [], mem⟩) (rest := []) blk (by simp) exec₄
    have fetch := Lir.Prog.fetch_eq_term (p := p)
      (pt := ⟨0, i, (StateExprLir.ops regs d (.lit v)).length⟩) blk (by simp)
    have res' : fr₄.regs d = some w := res₄
    have final : Lir.step p ⟨⟨0, i, 0 + (StateExprLir.ops regs d (.lit v)).length⟩, fr₄, [], mem⟩ =
        .returned [w] mem := by
      simp [Lir.step, fetch, Lir.Frame.readAll, Lir.Frame.read, res']
    refine .inr (.inr ⟨.returned [w] mem, ⟨.halt (.defined (.loaded (.specified (.integer v)))), [], m'⟩,
      trivial, ⟨_, steps, final⟩, reach, fun o ho => ?_⟩)
    rw [obs i mem m.stdout w o out ho]
    have st : w.toNat % 256 = (v % 256).toNat := by rw [hw, Fragment.status_ofInt]
    have e : m'.stdout = m.stdout := hout
    have fin := Sim.Final.exit (c := ⟨.halt (.defined (.loaded (.specified (.integer v)))), [], m'⟩)
      (v := .loaded (.specified (.integer v))) (k := (v % 256).toNat) rfl rfl
    rw [st]
    simpa [e, Spec.coreBytes] using fin

end run

/-! ## The recognised document -/

theorem labelCodes_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : List Sym}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} {T : List Key}
    {lits : Option (List (Sym × List Int))} :
    (zs : List (Sym × (List Sym × EE))) →
    (∀ kc ∈ labelCodes file ret xs tbl D T lits zs, ∃ z ∈ zs, z.1.key = kc.1 ∧
      Seg file ret xs tbl D T lits (D z.1.key) z.2.2 [] kc.2) ∧
      List.Sublist ((labelCodes file ret xs tbl D T lits zs).map (·.1)) (zs.map (·.1.key))
  | [] => by simp [labelCodes]
  | z :: zs => by
    obtain ⟨all, sub⟩ := labelCodes_spec (file := file) (ret := ret) (xs := xs) (tbl := tbl) (D := D)
      (T := T) (lits := lits) zs
    unfold labelCodes
    split
    · rcases hw : walk file ret xs tbl D T lits fuel (D z.1.key) z.2.2 [] [] with _ | ⟨c, rest⟩
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

theorem stable_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : List Sym}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} {lits : Option (List (Sym × List Int))} :
    (n : Nat) → {T₀ T : List Key} → {cs : List (Key × Code)} →
    stable file ret xs tbl D lits n T₀ = some (T, cs) →
    cs = labelCodes file ret xs tbl D T lits tbl ∧ cs.map (·.1) = T
  | 0, _, _, _, h => by simp [stable] at h
  | n + 1, T₀, T, cs, h => by
    unfold stable at h
    dsimp only at h
    split at h
    · rename_i heq
      cases h
      exact ⟨rfl, heq⟩
    · exact stable_spec n h

/-- **From the start to `main`'s tree**: the locals are created, and the two runs are related at
the root of the tree of `main`'s block; the facts `Seg.run` needs about the labels hold. -/
theorem recognize_entry (doc : Codec.Document) (P : Plan) (h : recognize doc = some P)
    (args : List String) (mem : Lir.Memory) (fr : Lir.Frame Mir.Reg)
    (O : Nat → Lir.Memory → String → Prop) (hO : O 1 mem "") :
    ∃ s labels ret tbl T, Spec.coreStart doc args = .ok (s, labels) ∧ ReturnLabel labels ret ∧
      (P.xs.map (·.key)).Nodup ∧
      (∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b)) ∧
      (∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
        ∃ c, Seg doc.file ret P.xs tbl P.D T (litsOf none) (P.D s.key) b [] c ∧
          At P.blocks (regOf (P.xs.map (·.key))) P.xs.length P.idx (P.idx s.key) c ∧
          LOk none s.key c) ∧
      ∃ cs fr', Reaches doc.file labels s cs ∧
        Lir.execOps (CfgGlobals.seedOps (regOf (P.xs.map (·.key))) P.globals) fr mem = some (fr', mem) ∧
        Rel doc.file ret P.xs tbl P.D T P.blocks P.idx O none ⟨⟨0, 1, 0⟩, fr', [], mem⟩ cs := by
  unfold recognize at h
  cases hgs : Globals.inits doc.file (Globals.definitions doc.file) with
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
              have hbody : recognizeBody doc.file body gs none = some P := by simpa [main, decl] using h
              obtain ⟨s, m, env, xsA, lg, hinit, hout, hkeys, inv₀, fresh₀, hentry⟩ :=
                GlobalsState.initial_reaches_state doc.file (Map.ofList (doc.enumBindings.getD [])) args
                  hgs gcond.1 (by omega) main decl
              let labels : Labels := Map.ofList (saves body).reverse
              have hlabels : labels = Map.ofList (saves body).reverse := rfl
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
                    dsimp only at hbody
                    split at hbody
                    · rename_i c0 f0 seen hw1
                      split at hbody
                      · rename_i T codes hstable
                        split at hbody
                        · rename_i entry f2 hentryw
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
                          obtain ⟨allCodes, sub⟩ := labelCodes_spec (file := doc.file) (ret := ret) (xs := xs)
                            (lits := none) (tbl := tbl) (D := labelDefs (grow doc.file ret xs tbl ((tbl.filter fun z => z.1.key != ret.key).map (·.1.key)) (gs.map (·.1.key)) none tbl.length seen) (gs.map (·.1.key))) (T := T) tbl
                          rw [← hcs] at allCodes sub
                          let P : Plan := ⟨xs, entry, codes, labelDefs (grow doc.file ret xs tbl ((tbl.filter fun z => z.1.key != ret.key).map (·.1.key)) (gs.map (·.1.key)) none tbl.length seen) (gs.map (·.1.key)), gs⟩
                          let regs := regOf (xs.map (·.key))
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
                            refine ⟨c, hseg, ?_, (fun _ h => by cases h)⟩
                            simpa [P, Plan.blocks, Plan.idx, regs, List.cons_append] using
                            emitAll_at regs xs.length P.idx codes codesNodup (entry.size + 1)
                              (⟨(CfgGlobals.seedOps regs gs).map .op, .jump 1⟩ :: entry.emit regs xs.length P.idx 1) (by simp [emit_length]) _ c hm
                          · have keys₀ : Keys lg (gs.map (·.1)) := by
                              unfold Keys
                              simpa [List.map_map, Function.comp_def] using congrArg (List.map (fun x : Sym => x.key)) hkeys
                            let k₀ : List Frame :=
                              [.strongBind (.mk pann (.base (none, bt0))) SAVE env, .annotations xsA]
                            have hk₀ : NoBoundary k₀ := by simp [k₀, NoBoundary, hasBoundary]
                            obtain ⟨env₁, m₁, ls₁, reach₁, inv₁, keys₁, out₁, fresh₁⟩ :=
                              CfgGlobals.creates_reaches_fresh (file := doc.file) (labels := labels)
                                (gs.map (·.1)) a hcr env m lg inv₀ keys₀ fresh₀ k₀
                            have hb₁ : ExitCall.Budget m₁ := by
                              have hlen : ls₁.length = xs.length := by
                                have := congrArg List.length keys₁; simpa using this
                              have hxs := LoopMain.creates_length (gs.map (·.1)) a hcr (by
                                have := GlobalsState.inits_length hgs
                                simp only [List.length_map]; omega)
                              refine ⟨?_, by rw [fresh₁.dead]; simp⟩
                              rw [fresh₁.nextIntAddress, fresh₁.last, hlen]
                              simp only [StartupReach.errnoAddr]
                              omega
                            have gkeys : ∀ g ∈ gs, g.1.key ∈ xs.map (·.key) := by
                              intro g hg
                              exact List.mem_map.mpr ⟨g.1, (CfgGlobals.creates_sublist _ _ hcr).subset
                                (List.mem_map_of_mem hg), rfl⟩
                            obtain ⟨fr', seed, matched⟩ := CfgGlobals.seed_exec (xs.map (·.key)) gs gkeys fr mem
                            have pre := hentry.trans
                              ((ReturnConst.sequence_reaches doc.file labels ann _ a SAVE env _ m).trans reach₁)
                            refine ⟨_, fr', pre, seed, gs.map (·.1.key), e, [], k₀, entry, 1, env₁, m₁, ls₁,
                              GlobalsState.defs gs, fr', mem, walk_seg (lits := none) _ hentryw, ?_,
                              rfl, rfl, .base hk₀, (fun _ _ _ _ _ h => by cases h), inv₁,
                              keys₁, ?_, matched, (out₁.trans hout) ▸ hO, hb₁, (fun _ h => by cases h),
                              (fun _ h => by cases h)⟩
                            · have := emit_at regs xs.length P.idx entry 1
                                [⟨(CfgGlobals.seedOps regs gs).map .op, .jump 1⟩]
                                (emitAll regs xs.length P.idx (entry.size + 1) codes) rfl
                              simpa [P, Plan.blocks, regs, List.append_assoc] using this
                            · intro q hq
                              obtain ⟨g, hg, hk⟩ := List.mem_map.mp hq
                              unfold GlobalsState.defs
                              cases hf : gs.find? (fun g => g.1.key == q) with
                              | some v => rfl
                              | none =>
                                have hn := List.find?_eq_none.mp hf g hg
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
    let O : Nat → Lir.Memory → String → Prop := fun _ mem s => CfgOut.OutMem mem s
    have hO : O 1 (a.lmem args) "" := by
      obtain ⟨hbase, -, himg⟩ := ConstLink.artifact_layout ha
      exact CfgOut.initial (by simpa [LoopLink.link] using himg) hbase args
        (by simp [Spec.Artifact.lmem, ArgvAbortLink.artifact_memSize ha])
    obtain ⟨s, labels, ret, tbl, T, hinit, hret, nodup, hlook, hcodes, cs, fr', reach, seed, rel⟩ :=
      recognize_entry doc P hP args (a.lmem args) fr₀ O hO
    right
    have blk : (LoopLink.link P.blocks).prog.block? 0 0 =
        some ⟨(CfgGlobals.seedOps (regOf (P.xs.map (·.key))) P.globals).map .op, .jump 1⟩ := by
      rw [LoopLink.link_block]; rfl
    have toEntry := (jump_steps blk (fr := fr₀) (mem := a.lmem args) seed).to_reflTransGen
    have obs : ∀ i mem s (w : Lir.Word) (o : Spec.Obs), O i mem s → LirObs (.returned [w] mem) o →
        o = .exit (w.toNat % 256) (Spec.coreBytes s) := fun _ _ _ _ _ h ho => h.obs ho
    have hsize : ∀ i mem s, O i mem s → mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := fun _ _ _ h => h.size
    have abortObs : ∀ i mem s (mem' : Lir.Memory) (o : Spec.Obs), O i mem s →
        mem.store .b8 (Spec.ctlAddr + 40) (BitVec.ofNat 64 2) = some mem' → LirObs (.trapped mem') o →
          o = .abort (Spec.coreBytes s) := fun _ _ _ _ _ h hst ho => h.abortObs hst ho
    have step : ∀ ts cs, Rel doc.file ret P.xs tbl P.D T P.blocks P.idx O none ts cs →
        LoopSimAbort.Iteration (LoopLink.link P.blocks).prog doc.file labels
          (Rel doc.file ret P.xs tbl P.D T P.blocks P.idx O none) ts cs := by
      rintro ts cs ⟨dk, e, Pd, F, c, i, env, m, ls, ds, fr, mem, seg, hat, rfl, rfl, pends, fok, inv,
        keys, cov, matched, out, hb, henv, hm⟩
      exact Seg.run hret nodup hlook hcodes (fun _ _ _ _ _ h => h) obs hsize abortObs
        (fun _ _ _ => Iff.rfl) (fun _ h => by cases h) seg hat pends fok inv keys cov matched out
        hb henv hm
    refine ⟨s, labels, cs, hinit, reach, ?_, ?_⟩
    · intro b o beh hobs
      exact LoopSimAbort.allowed step rel (LoopSim.behaves_of_steps toEntry beh) hobs
    · intro beh
      exact LoopSimAbort.stuck_ub step rel (LoopSim.behaves_of_steps toEntry beh)
  · cases h

end Silmaril.Compile.Core.Verified.Cfg
