module

public import Silmaril.Compiler.Core.Verified.CfgArgv.Defs
public import Silmaril.Compiler.Core.Verified.CfgSound.Defs
public import Silmaril.Compiler.Core.Verified.CfgArgvMem.Defs
public import Silmaril.Compiler.Core.Verified.ArgvStart.Defs
/-! # `main(argc, argv)` as a control-flow graph: the proof

`CfgSound`'s simulation, for the machine of `CfgArgv`. `Seg dk sb e P c` is the derivation that
`walk` found, now with the slots `sb` below their string's length. `Rel` relates the two runs at
the root of a node as `Cfg.Rel` does, and also: the memory holds the argument objects apart from
the slots (`CfgArgvMem.Mem`), `argv` is bound to its parameter object (in the current environment
and in those of the pending statements, `Pends`), register `R` holds the base of the argument
block, and every slot that indexes an argument is within its string (`Bounds`).

`Seg.run`: each node runs as in `Cfg.Seg.run`; a statement keeps `Mem` (it is closed under the
statements, `CfgArgvMem.closed`), the bound discipline of `CfgArgv.atom` keeps `Bounds`, and the
test of a character (`ArgvTest.runs`, `ArgvTest.steps`) reads, in both machines, the byte of
the argument at the slot's value, which `Bounds` puts within the string.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgArgv

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Machine
open StateExpr (Key Term term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt (assignStmt initStmt uninitStmt isLocal isFresh Keys Overflows)
open StateLoopStep (Layout Registers)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open LoopMain (covered regOf Covers EnvOk)
open Cfg (labelTable find selfParams symArgs Atom labelDefs jump find_mem rebinds forall₂_keys
  symArgs_evals selfParams_evals run_strict run_nil_strict jump_steps iteration_pre labelTable_eq)
open Relation

/-! ## Pending statements -/

/-- `Cfg.Pends`, with a fact `E` about the environments of the pending statements. -/
inductive Pends (ls : List Local) (E : Env → Prop) : List EE → List Frame → Prop where
  | base {F : List Frame} : NoBoundary F → Pends ls E [] F
  | ann {P : List EE} {F : List Frame} (xs : List Access) : Pends ls E P F →
      Pends ls E P (.annotations xs :: F)
  | bind {P : List EE} {F : List Frame} (pann : List Annot) (ty : BaseType) (b : EE) (env : Env) :
      EnvOk env ls → E env → Pends ls E P F →
      Pends ls E (b :: P) (.strongBind (.mk pann (.base (none, ty))) b env :: F)

theorem Pends.noBoundary {ls : List Local} {E : Env → Prop} {P : List EE} {F : List Frame}
    (h : Pends ls E P F) : NoBoundary F := by
  induction h with
  | base h => exact h
  | ann xs _ ih => exact noBoundary_cons ih trivial
  | bind pann ty b env _ _ _ ih => exact noBoundary_cons ih trivial

variable {file : Program} {labels : Labels}

theorem Pends.pop {ls : List Local} {E : Env → Prop} {b : EE} {P : List EE} :
    (F : List Frame) → Pends ls E (b :: P) F → (m : Mem.Concrete.State) →
    ∃ env F', EnvOk env ls ∧ E env ∧ Pends ls E P F' ∧
      Reaches file labels ⟨.value .unit, F, m⟩ ⟨.effectExpr b env, F', m⟩
  | [], h, _ => by cases h
  | f :: F, h, m => by
    cases h with
    | bind pann ty b env hb he h =>
      exact ⟨env, F, hb, he, h, ReturnConst.wildcard_sequence_reaches file labels pann ty .unit b env F m⟩
    | ann xs h =>
      cases h with
      | bind pann ty b env hb he h' =>
        exact ⟨env, _, hb, he, .ann xs h', Locals.annotations_bind_reaches xs pann ty .unit b env _ m⟩
      | ann ys h' =>
        obtain ⟨env, F', hb, he, hp, r⟩ := Pends.pop (.annotations (xs ++ ys) :: _) (.ann (xs ++ ys) h') m
        exact ⟨env, F', hb, he, hp, (Locals.annotations_merge_reaches xs ys .unit _ m).trans r⟩
termination_by F => F.length

/-- Rebinding locals keeps the binding of a symbol that is not a local. -/
theorem lookup_zip_other {ls : List Local} {y : Sym} (hy : ∀ l ∈ ls, l.sym.key ≠ y.key) :
    {qs : List Sym} → {vs : List Val} →
    List.Forall₂ (fun (q : Sym) (v : Val) => ∃ l ∈ ls, q.key = l.sym.key ∧ v = ptr l) qs vs →
    (env : Env) → (extendEnv (qs.zip vs) env).lookup y = env.lookup y
  | [], [], .nil, env => by simp [extendEnv]
  | q :: qs, v :: vs, .cons ⟨l, hl, hk, _⟩ rest, env => by
    simp only [List.zip_cons_cons]
    rw [Cfg.extendEnv_cons, ConvInt.lookup_one_other (by rw [hk]; exact fun e => hy l hl e.symm)]
    exact lookup_zip_other hy rest env

/-! ## Blocks -/

/-- The blocks of the nodes of a tree whose root is block `i`. -/
def At (bs : List (Lir.Block Mir.Reg)) (regs : Key → Mir.Reg) (d R : Nat) (argv : Key)
    (idx : Key → Nat) : Nat → Code → Prop
  | i, .atom (.set q t) c =>
    bs[i]? = some ⟨(StateExprLir.assignOps regs d q t).map .op, .jump (i + 1)⟩ ∧
      At bs regs d R argv idx (i + 1) c
  | i, .atom (.clear _) c => bs[i]? = some ⟨[], .jump (i + 1)⟩ ∧ At bs regs d R argv idx (i + 1) c
  | i, .test t y n =>
    bs[i]? = some (LoopBlocks.testBlock regs d (LoopBlocks.coreTest t) (i + 1) (i + 1 + y.size)) ∧
      At bs regs d R argv idx (i + 1) y ∧ At bs regs d R argv idx (i + 1 + y.size) n
  | i, .atest a q t y n =>
    bs[i]? = some (ArgvTest.block regs d R argv a q t (i + 1) (i + 1 + y.size)) ∧
      At bs regs d R argv idx (i + 1) y ∧ At bs regs d R argv idx (i + 1 + y.size) n
  | i, .goto l => bs[i]? = some ⟨[], .jump (idx l)⟩
  | i, .ret t => bs[i]? = some ⟨(StateExprLir.ops regs d t).map .op, .ret [.reg d]⟩

theorem emit_length (regs : Key → Mir.Reg) (d R : Nat) (argv : Key) (idx : Key → Nat) :
    (c : Code) → (i : Nat) → (c.emit regs d R argv idx i).length = c.size
  | .atom (.set _ _) c, i => by simp [Code.emit, Code.size, emit_length regs d R argv idx c (i + 1)]
  | .atom (.clear _) c, i => by simp [Code.emit, Code.size, emit_length regs d R argv idx c (i + 1)]
  | .test _ y n, i => by
    simp [Code.emit, Code.size, emit_length regs d R argv idx y, emit_length regs d R argv idx n]
  | .atest _ _ _ y n, i => by
    simp [Code.emit, Code.size, emit_length regs d R argv idx y, emit_length regs d R argv idx n]
  | .goto _, _ => rfl
  | .ret _, _ => rfl

/-- The emitted tree is where `At` says, wherever it is placed. -/
theorem emit_at (regs : Key → Mir.Reg) (d R : Nat) (argv : Key) (idx : Key → Nat) :
    (c : Code) → (i : Nat) → (pre post : List (Lir.Block Mir.Reg)) → pre.length = i →
    At (pre ++ c.emit regs d R argv idx i ++ post) regs d R argv idx i c
  | .atom (.set q t) c, i, pre, post, h => by
    refine ⟨?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d R argv idx c (i + 1)
        (pre ++ [⟨(StateExprLir.assignOps regs d q t).map .op, .jump (i + 1)⟩]) post (by simp [h])
      simpa [Code.emit, List.append_assoc] using this
  | .atom (.clear q) c, i, pre, post, h => by
    refine ⟨?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d R argv idx c (i + 1) (pre ++ [⟨[], .jump (i + 1)⟩]) post (by simp [h])
      simpa [Code.emit, List.append_assoc] using this
  | .test t y n, i, pre, post, h => by
    let tb := LoopBlocks.testBlock regs d (LoopBlocks.coreTest t) (i + 1) (i + 1 + y.size)
    refine ⟨?_, ?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d R argv idx y (i + 1) (pre ++ [tb])
        (n.emit regs d R argv idx (i + 1 + y.size) ++ post) (by simp [h])
      simpa [Code.emit, List.append_assoc, tb] using this
    · have := emit_at regs d R argv idx n (i + 1 + y.size) (pre ++ [tb] ++ y.emit regs d R argv idx (i + 1))
        post (by simp [h, emit_length]; omega)
      simpa [Code.emit, List.append_assoc, tb] using this
  | .atest a q t y n, i, pre, post, h => by
    let tb := ArgvTest.block regs d R argv a q t (i + 1) (i + 1 + y.size)
    refine ⟨?_, ?_, ?_⟩
    · subst h; simp [Code.emit]
    · have := emit_at regs d R argv idx y (i + 1) (pre ++ [tb])
        (n.emit regs d R argv idx (i + 1 + y.size) ++ post) (by simp [h])
      simpa [Code.emit, List.append_assoc, tb] using this
    · have := emit_at regs d R argv idx n (i + 1 + y.size) (pre ++ [tb] ++ y.emit regs d R argv idx (i + 1))
        post (by simp [h, emit_length]; omega)
      simpa [Code.emit, List.append_assoc, tb] using this
  | .goto l, i, pre, post, h => by subst h; simp [Code.emit, At]
  | .ret t, i, pre, post, h => by subst h; simp [Code.emit, At]

/-- Each label's tree is at its first block. -/
theorem emitAll_at (regs : Key → Mir.Reg) (d R : Nat) (argv : Key) (idx : Key → Nat) :
    (cs : List (Key × Code)) → (cs.map (·.1)).Nodup → (i : Nat) → (pre : List (Lir.Block Mir.Reg)) →
    pre.length = i → ∀ l c, (l, c) ∈ cs →
      At (pre ++ emitAll regs d R argv idx i cs) regs d R argv idx (posA i cs l) c
  | [], _, _, _, _, _, _, hm => by cases hm
  | (l', c') :: cs, nd, i, pre, h, l, c, hm => by
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp hm with eq | hm
    · simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      have := emit_at regs d R argv idx c i pre (emitAll regs d R argv idx (i + c.size) cs) h
      simpa [posA, emitAll, List.append_assoc] using this
    · have hne : l' ≠ l := by
        rintro rfl
        exact nd.1 (List.mem_map.mpr ⟨(l', c), hm, rfl⟩)
      have := emitAll_at regs d R argv idx cs nd.2 (i + c'.size) (pre ++ c'.emit regs d R argv idx i)
        (by simp [h, emit_length]) l c hm
      simpa [posA, hne, emitAll, List.append_assoc] using this

/-! ## The derivations of `walk` -/

/-- `c` is the code of `e` followed by the pending statements `P`, with `dk` defined and the
slots `sb` below their string's length. -/
inductive Seg (file : File Codec.wireModel Unit Unit) (ret argv : Sym) (xs : List Sym) (bnd : Bnd)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key) :
    List Key → List Key → EE → List EE → Code → Prop where
  | retn {dk sb : List Key} {e : EE} {P : List EE} {t : Term} :
      Cfg.retStmt file ret xs e = some t → covered dk t = true →
      Seg file ret argv xs bnd tbl D T dk sb e P (.ret t)
  | op {dk dk' sb sb' : List Key} {e b : EE} {P : List EE} {a : Atom} {c : Code} :
      atom file xs bnd sb dk e = some (a, dk', sb') → Seg file ret argv xs bnd tbl D T dk' sb' b P c →
      Seg file ret argv xs bnd tbl D T dk sb e (b :: P) (.atom a c)
  | test {dk sb : List Key} {e yes no : EE} {P : List EE} {t : Term} {cy cn : Code} :
      LoopCondition.recognize file xs e = some (t, yes, no) → covered dk t = true →
      bindersOk argv e = true →
      Seg file ret argv xs bnd tbl D T dk sb yes P cy → Seg file ret argv xs bnd tbl D T dk sb no P cn →
      Seg file ret argv xs bnd tbl D T dk sb e P (.test t cy cn)
  | atest {dk sb : List Key} {e yes no : EE} {P : List EE} {i : Nat} {x : Sym} {t : IntExpr.Term}
      {cy cn : Code} :
      ArgvTest.recognize file xs argv e = some (i, x, t, yes, no) → i ≤ 1 → isLocal xs x = true →
      x.key ∈ dk → (x.key, i) ∈ bnd →
      Seg file ret argv xs bnd tbl D T dk (if zeroTest t then x.key :: sb else sb) yes P cy →
      Seg file ret argv xs bnd tbl D T dk sb no P cn →
      Seg file ret argv xs bnd tbl D T dk sb e P (.atest i x.key t cy cn)
  | seq {dk sb : List Key} {P : List EE} {c : Code} (ann pann : List Annot) (ty : BaseType) (a b : EE) :
      Seg file ret argv xs bnd tbl D T dk sb a (b :: P) c →
      Seg file ret argv xs bnd tbl D T dk sb (.mk ann (.sseq (.mk pann (.base (none, ty))) a b)) P c
  | unit {dk sb : List Key} {b : EE} {P : List EE} {c : Code} (ann pann : List Annot) :
      Seg file ret argv xs bnd tbl D T dk sb b P c →
      Seg file ret argv xs bnd tbl D T dk sb (.mk ann (.pure (.mk pann () (.val .unit)))) (b :: P) c
  | save {dk sb : List Key} {P : List EE} {c : Code} (ann : List Annot) (l : Sym) (lty : BaseType)
      (ps : List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE))) (body : EE) :
      selfParams xs ps = true → Seg file ret argv xs bnd tbl D T dk sb body P c →
      Seg file ret argv xs bnd tbl D T dk sb (.mk ann (.save (l, lty) ps body)) P c
  | goto {dk sb : List Key} {P : List EE} (ann : List Annot) (l : Sym) (args : List PE) :
      jump ret xs tbl D T dk l args = true →
      Seg file ret argv xs bnd tbl D T dk sb (.mk ann (.run () l args)) P (.goto l.key)

theorem walk_seg {file : File Codec.wireModel Unit Unit} {ret argv : Sym} {xs : List Sym} {bnd : Bnd}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} {T : List Key} :
    (fuel : Nat) → {dk sb : List Key} → {e : EE} → {P : List EE} → {seen : List (Key × List Key)} →
    {c : Code} → {f : Nat} → {s : List (Key × List Key)} →
    walk file ret argv xs bnd tbl D T fuel dk sb e P seen = some (c, f, s) →
    Seg file ret argv xs bnd tbl D T dk sb e P c
  | 0, _, _, _, _, _, _, _, _, h => by simp [walk] at h
  | fuel + 1, dk, sb, e, P, seen, c, f, s, h => by
    unfold walk at h
    split at h
    · rename_i t ht
      split at h
      · rename_i hc
        cases h
        exact .retn ht hc
      · cases h
    · split at h
      · rename_i a dk' sb' ha
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨c', r⟩, h', eq⟩ := h
          cases eq
          exact .op ha (walk_seg fuel h')
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
          · rename_i i x t yes no ht
            split at h
            · rename_i hc
              split at h
              · rename_i cy f' s' hy
                split at h
                · rename_i hlt
                  simp only [Option.map_eq_some_iff] at h
                  obtain ⟨⟨cn, r⟩, hn, eq⟩ := h
                  cases eq
                  exact .atest ht hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (walk_seg fuel hy) (walk_seg f' hn)
                · cases h
              · cases h
            · cases h
          · split at h
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

/-- The length of argument `i` (`0` past the arguments). -/
def slen (args : List String) (i : Nat) : Int := if h : i < args.length then args[i].length else 0

/-- Every defined slot that indexes argument `i` is within its string, and below its length when
in `sb`. -/
def Bounds (args : List String) (bnd : Bnd) (ds : Key → Option IntExpr.Term) (sb : List Key) : Prop :=
  ∀ q i, (q, i) ∈ bnd → ∀ dq, ds q = some dq →
    0 ≤ dq.val 0 ∧ dq.val 0 ≤ slen args i ∧ (q ∈ sb → dq.val 0 < slen args i)

/-- The static facts of a run: the artifact, the argument vector and its objects. -/
structure Ctx where
  a : Spec.Artifact
  args : List String
  idV : Int
  V : Int
  idA : Int
  B : Int
  qs : List Mem.Concrete.Pointer

/-- `argv` is bound to its parameter object. -/
def ArgvEnv (argv : Sym) (X : Ctx) (env : Env) : Prop :=
  env.lookup argv = some (.object (.pointer (.allocated X.idV X.V)))

/-- The two runs at the root of a node. -/
def Rel (file : Program) (ret argv : Sym) (xs : List Sym) (bnd : Bnd)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key)
    (bs : List (Lir.Block Mir.Reg)) (idx : Key → Nat) (X : Ctx) (ts : Lir.State Mir.Reg)
    (cs : Spec.CState) : Prop :=
  ∃ (dk sb : List Key) (e : EE) (P : List EE) (F : List Frame) (c : Code) (i : Nat) (env : Env)
    (m : Mem.Concrete.State) (ls : List Local) (ds : Key → Option IntExpr.Term)
    (fr : Lir.Frame Mir.Reg),
    Seg file ret argv xs bnd tbl D T dk sb e P c ∧
    At bs (regOf (xs.map (·.key))) (xs.length + 1) xs.length argv.key idx i c ∧
    ts = ⟨⟨0, i, 0⟩, fr, [], X.a.lmem X.args⟩ ∧ cs = ⟨.effectExpr e env, F, m⟩ ∧
    Pends ls (ArgvEnv argv X) P F ∧
    Inv env m ls ds ∧ Keys ls xs ∧ Covers dk ds ∧ Registers (regOf (xs.map (·.key))) ds fr ∧
    m.stdout = "" ∧ CfgArgvMem.Mem X.args X.idV X.V X.idA X.B X.qs ls m ∧ ArgvEnv argv X env ∧
    fr.get xs.length = some (BitVec.ofNat 64 X.a.argBase) ∧ Bounds X.args bnd ds sb

/-- The statement test of `LoopCondition`, keeping the binding of `argv`. -/
theorem loop_test_step {xs : List Sym} {argv : Sym} {e yes no : EE} {t : Term}
    (shape : LoopCondition.recognize file xs e = some (t, yes, no)) (hb : bindersOk argv e = true)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ env' m',
        LoadTask.Touched m m' ∧ Inv env' m' ls ds ∧ env'.lookup argv = env.lookup argv ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 1 then no else yes) env', k, m'⟩ := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl,
    hb', hcb, hfc, hfb, htc⟩ := LoopCondition.recognize_inv shape
  have hca : c.key ≠ argv.key ∧ b.key ≠ argv.key := by
    simpa [bindersOk, ifBinders] using hb
  let σ := values (defsOf ds)
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) yes no)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  by_cases ok : t.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, _, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      t htc ok (.bound :: K) m (inv.locs defined)
    let cv := t.val σ
    let env₁ := extendEnv [(c, IntExpr.spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := StateStmt.boolSource_touched (file := file) (labels := labels) hcb env₁ KB
      m₁ cv (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then yes else no) env₂, k, SeqReach.focusMemory a5 m₂⟩ :=
      (Interleave.reaches_of_local file labels run).trans ((StateStmt.bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have touched := tch.trans (tch₂.trans (StateStmt.seqFocus_touched a5 m₂))
    refine ⟨ok, env₂, _, touched,
      ((inv.touched touched).extend (keys.fresh hfc)).extend (keys.fresh hfb), ?_, ?_⟩
    · rw [ConvInt.lookup_one_other (Ne.symm hca.2), ConvInt.lookup_one_other (Ne.symm hca.1)]
    · have select : (if flag then yes else no) =
          (if t.val (values (defsOf ds)) = 1 then no else yes) := by
        change (if flag then yes else no) = (if cv = 1 then no else yes)
        by_cases h : cv = 1 <;> simp [flag, h]
      rw [select] at enter
      exact pre.trans enter
  · left
    exact Overflows.pre pre (StateStmt.fails_overflows (StateExpr.term_fails (file := file) (labels := labels)
      t htc ok (.bound :: K) m (inv.locs defined)))

theorem slen_nonneg (args : List String) (i : Nat) : 0 ≤ slen args i := by
  unfold slen; split <;> omega

theorem slen_lt {args : List String} {i : Nat} (h : i < args.length) : slen args i = args[i].length := by
  simp [slen, h]

theorem not_mem_of_inBnd {bnd : Bnd} {q : Key} (h : inBnd bnd q = false) (i : Nat) : (q, i) ∉ bnd := by
  intro hm
  have : inBnd bnd q = true := List.any_eq_true.mpr ⟨(q, i), hm, by simp⟩
  simp_all

/-- Assigning `q₀` a value within every string it indexes keeps `Bounds`, forgetting `q₀` in
`sb`. -/
theorem Bounds.update {args : List String} {bnd : Bnd} {ds : Key → Option IntExpr.Term} {sb : List Key}
    (h : Bounds args bnd ds sb) (q₀ : Key) (d₀ : Option IntExpr.Term)
    (hq : ∀ i, (q₀, i) ∈ bnd → ∀ dq, d₀ = some dq → 0 ≤ dq.val 0 ∧ dq.val 0 ≤ slen args i) :
    Bounds args bnd (update ds q₀ d₀) (sb.filter (· != q₀)) := by
  intro q i hm dq hd
  unfold StateMem.update at hd
  split at hd
  · rename_i he
    subst he
    obtain ⟨h0, h1⟩ := hq i hm dq hd
    exact ⟨h0, h1, fun hs => by simp at hs⟩
  · obtain ⟨h0, h1, h2⟩ := h q i hm dq hd
    exact ⟨h0, h1, fun hs => h2 (List.mem_filter.mp hs).1⟩

theorem Bounds.mono {args : List String} {bnd : Bnd} {ds : Key → Option IntExpr.Term} {sb sb' : List Key}
    (h : Bounds args bnd ds sb) (hs : ∀ q ∈ sb', q ∈ sb) : Bounds args bnd ds sb' := fun q i hm dq hd =>
  let ⟨h0, h1, h2⟩ := h q i hm dq hd; ⟨h0, h1, fun hq => h2 (hs q hq)⟩

theorem layout1 {xs : List Sym} {ls : List Local} (keys : Keys ls xs) :
    Layout (regOf (xs.map (·.key))) (xs.length + 1) ls :=
  ⟨fun l hl => Nat.lt_succ_of_lt ((LoopMain.layout keys).below l hl), (LoopMain.layout keys).apart⟩

theorem isZero_inv {t : Term} (h : isZero t = true) : t = .lit 0 := by
  unfold isZero at h; split at h
  · rfl
  · cases h

theorem isAdd_inv {op : IntOp} (h : isAdd op = true) : op = .add := by
  cases op <;> simp [isAdd] at h ⊢

/-- The yes successor of `while (c)` has a character that is not `0`. -/
theorem zeroTest_ne {t : IntExpr.Term} (h : zeroTest t = true) {c : Int} (hv : ¬ t.val c = 1) : c ≠ 0 := by
  unfold zeroTest at h
  split at h
  · intro hc
    subst hc
    exact hv (by simp [IntExpr.Term.val, Guard.compare, Guard.holds])
  · cases h

section run

variable {ret argv : Sym} {xs : List Sym} {bnd : Bnd} {tbl : List (Sym × (List Sym × EE))}
  {D : Key → List Key} {T : List Key} {bs : List (Lir.Block Mir.Reg)} {idx : Key → Nat} {X : Ctx}

theorem jump_iter (hfresh : isFresh xs argv = true)
    (hlook : ∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b))
    (hcodes : ∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
      ∃ c, Seg file ret argv xs bnd tbl D T (D s.key) [] b [] c ∧
        At bs (regOf (xs.map (·.key))) (xs.length + 1) xs.length argv.key idx (idx s.key) c)
    {dk sb : List Key} {l : Sym} {args : List PE} (hj : jump ret xs tbl D T dk l args = true)
    {ann : List Annot} {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {F : List Frame} {fr : Lir.Frame Mir.Reg}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (cov : Covers dk ds) (hF : NoBoundary F)
    (matched : Registers (regOf (xs.map (·.key))) ds fr) (out : m.stdout = "")
    (hm : CfgArgvMem.Mem X.args X.idV X.V X.idA X.B X.qs ls m) (he : ArgvEnv argv X env)
    (hR : fr.get xs.length = some (BitVec.ofNat 64 X.a.argBase)) (hbd : Bounds X.args bnd ds sb)
    {ts : Lir.State Mir.Reg}
    (lir : TransGen (Lir.Step (LoopLink.link bs).prog) ts ⟨⟨0, idx l.key, 0⟩, fr, [], X.a.lmem X.args⟩) :
    ∃ ts' cs', TransGen (Lir.Step (LoopLink.link bs).prog) ts ts' ∧
      TransGen (Spec.coreStep file labels) ⟨.effectExpr (.mk ann (.run () l args)) env, F, m⟩ cs' ∧
      Rel file ret argv xs bnd tbl D T bs idx X ts' cs' := by
  unfold Cfg.jump at hj
  split at hj
  · rename_i ys qs b' hys hf
    obtain ⟨-, hT, hkeys, hloc, hdef⟩ := of_decide_eq_true hj
    obtain ⟨s, hmem, hsk⟩ := find_mem hf
    have hlk : labels.lookup l = some (qs, b') := by
      rw [ReturnLit.lookup_key hsk.symm]; exact hlook s qs b' hmem
    obtain ⟨c', seg', hat'⟩ := hcodes s qs b' hmem (by rw [hsk]; exact hT)
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
    have hfa : ∀ l ∈ ls, l.sym.key ≠ argv.key := keys.fresh hfresh
    refine ⟨_, _, lir, core, ?_⟩
    refine ⟨D l.key, [], b', [], [], c', idx l.key, _, _, ls, ds, fr, ?_, ?_, rfl, rfl, .base rfl,
      rebinds (inv.focus ann) relq, keys, ?_, matched, by simpa using out, hm.focus ann, ?_, hR, ?_⟩
    · rw [← hsk]; exact seg'
    · rw [← hsk]; exact hat'
    · intro q hq; exact cov q (hdef q hq)
    · unfold ArgvEnv; rw [lookup_zip_other hfa relq]; exact he
    · intro q i hq dq hd
      obtain ⟨h0, h1, -⟩ := hbd q i hq dq hd
      exact ⟨h0, h1, fun h => by simp at h⟩
  · cases hj

/-- **One macro-step from the root of a node**: undefined behaviour, or the return in both
machines, or nonempty paths in both to the root of a label's tree. -/
theorem Seg.run (hret : ReturnLabel labels ret) (nodup : (xs.map (·.key)).Nodup)
    (hfresh : isFresh xs argv = true)
    (hlook : ∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b))
    (hcodes : ∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
      ∃ c, Seg file ret argv xs bnd tbl D T (D s.key) [] b [] c ∧
        At bs (regOf (xs.map (·.key))) (xs.length + 1) xs.length argv.key idx (idx s.key) c)
    (obs : ∀ (w : Lir.Word) (o : Spec.Obs), LirObs (.returned [w] (X.a.lmem X.args)) o →
      o = .exit (w.toNat % 256) [])
    (hbase : X.a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase) (hsize : X.a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize)
    (himg : X.a.image = .empty) (ha : Spec.ArgsOk X.args) (hstr : CfgArgvMem.StrAbove X.args X.B X.qs)
    (hbnd : (bnd.map (·.1)).Nodup)
    {dk sb : List Key} {e : EE} {P : List EE} {c : Code}
    (seg : Seg file ret argv xs bnd tbl D T dk sb e P c) :
    ∀ {i : Nat} {env : Env} {m : Mem.Concrete.State} {ls : List Local}
      {ds : Key → Option IntExpr.Term} {F : List Frame} {fr : Lir.Frame Mir.Reg},
    At bs (regOf (xs.map (·.key))) (xs.length + 1) xs.length argv.key idx i c →
    Pends ls (ArgvEnv argv X) P F → Inv env m ls ds →
    Keys ls xs → Covers dk ds → Registers (regOf (xs.map (·.key))) ds fr → m.stdout = "" →
    CfgArgvMem.Mem X.args X.idV X.V X.idA X.B X.qs ls m → ArgvEnv argv X env →
    fr.get xs.length = some (BitVec.ofNat 64 X.a.argBase) → Bounds X.args bnd ds sb →
    LoopSimAbort.Iteration (LoopLink.link bs).prog file labels (Rel file ret argv xs bnd tbl D T bs idx X)
      ⟨⟨0, i, 0⟩, fr, [], X.a.lmem X.args⟩ ⟨.effectExpr e env, F, m⟩ := by
  let regs := regOf (xs.map (·.key))
  let d := xs.length + 1
  let p := (LoopLink.link bs).prog
  let mem := X.a.lmem X.args
  induction seg with
  | @retn dk sb e P t ht hc =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hm he hR hbd
    have blk : p.block? 0 i = some ⟨(StateExprLir.ops regs d t).map .op, .ret [.reg d]⟩ :=
      (LoopLink.link_block bs i).trans hat
    have defined := cov.defined hc
    have lay := layout1 keys
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
      rw [obs w o ho]
      have st : w.toNat % 256 = ((close (defsOf ds) t).val 0 % 256).toNat := by
        rw [hw, StateExpr.close_val, Fragment.status_ofInt]
      have e : m₄.stdout = "" := by rw [hout, out]
      have fin := Sim.Final.exit (c := ⟨.halt (.defined (IntExpr.spec ((close (defsOf ds) t).val 0))),
        [], m₄⟩) (v := IntExpr.spec ((close (defsOf ds) t).val 0))
        (k := ((close (defsOf ds) t).val 0 % 256).toNat) rfl rfl
      rw [st]
      simpa [e, Spec.coreBytes] using fin
    · exact .inl ⟨s', _, _, reach, halt⟩
  | @op dk dk' sb sb' e b P a c ha seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hm he hR hbd
    have lay := layout1 keys
    have cl := CfgArgvMem.closed (idV := X.idV) (V := X.V) (idA := X.idA) ls hstr
    unfold atom at ha
    split at ha
    · rename_i x t hx
      split at ha
      · rename_i hc
        cases ha
        obtain ⟨blk, hat'⟩ := hat
        obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc.1
        have defined := cov.defined hc.2.1
        rcases PrintMem.assign_runs hx inv hl key defined F cl hm with ub | ⟨ok, m', out', inv', hm', src⟩
        · exact .inl (LoopMain.overflows_ub ub)
        obtain ⟨envb, F', henv, heb, pends', pop⟩ := Pends.pop (file := file) (labels := labels) F pends m'
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
        have hR₁ : fr₁.get xs.length = some (BitVec.ofNat 64 X.a.argBase) := by
          rw [other₁ _ (Nat.lt_succ_self _) (Nat.ne_of_gt ((LoopMain.layout keys).below l hl))]; exact hR
        have hbd₁ := hbd.update l.sym.key (some (close (defsOf ds) t)) (fun i hi dq hdq => by
          cases hdq
          rcases hc.2.2 with hn | hz
          · exact absurd hi (not_mem_of_inBnd (by rw [← key]; exact hn) i)
          · rw [isZero_inv hz]; exact ⟨le_rfl, slen_nonneg _ _⟩)
        replace hbd₁ : Bounds X.args bnd (update ds l.sym.key (some (close (defsOf ds) t)))
            (sb.filter (· != x.key)) := by rw [key]; exact hbd₁
        have blk' : p.block? 0 i =
            some ⟨(StateExprLir.assignOps regs d l.sym.key t).map .op, .jump (i + 1)⟩ := by
          rw [← key]; exact (LoopLink.link_block bs i).trans blk
        exact iteration_pre (jump_steps blk' exec₁).to_reflTransGen (src.trans pop)
          (ih hat' pends' { inv' with env := henv } keys cov₁ matched₁ (out'.trans out) hm' heb hR₁ hbd₁)
      · cases ha
    · split at ha
      · rename_i x t hx
        split at ha
        · rename_i hc
          cases ha
          obtain ⟨blk, hat'⟩ := hat
          obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc.1
          have defined := cov.defined hc.2.1
          rcases PrintMem.init_runs hx inv hl key defined F cl hm with ub | ⟨ok, m', ys, out', inv', hm', src⟩
          · exact .inl (LoopMain.overflows_ub ub)
          obtain ⟨envb, F', henv, heb, pends', pop⟩ :=
            Pends.pop (file := file) (labels := labels) _ (.ann ys pends) m'
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
          have hR₁ : fr₁.get xs.length = some (BitVec.ofNat 64 X.a.argBase) := by
            rw [other₁ _ (Nat.lt_succ_self _) (Nat.ne_of_gt ((LoopMain.layout keys).below l hl))]; exact hR
          have hbd₁ := hbd.update l.sym.key (some (close (defsOf ds) t)) (fun i hi dq hdq => by
            cases hdq
            rcases hc.2.2 with hn | hz
            · exact absurd hi (not_mem_of_inBnd (by rw [← key]; exact hn) i)
            · rw [isZero_inv hz]; exact ⟨le_rfl, slen_nonneg _ _⟩)
          replace hbd₁ : Bounds X.args bnd (update ds l.sym.key (some (close (defsOf ds) t)))
              (sb.filter (· != x.key)) := by rw [key]; exact hbd₁
          have blk' : p.block? 0 i =
              some ⟨(StateExprLir.assignOps regs d l.sym.key t).map .op, .jump (i + 1)⟩ := by
            rw [← key]; exact (LoopLink.link_block bs i).trans blk
          exact iteration_pre (jump_steps blk' exec₁).to_reflTransGen (src.trans pop)
            (ih hat' pends' { inv' with env := henv } keys cov₁ matched₁ (out'.trans out) hm' heb hR₁ hbd₁)
        · cases ha
      · split at ha
        · rename_i x hx
          split at ha
          · rename_i hc
            cases ha
            obtain ⟨blk, hat'⟩ := hat
            obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc
            obtain ⟨m', ys, out', inv', hm', src⟩ := PrintMem.uninit_runs hx inv hl key F cl hm
            obtain ⟨envb, F', henv, heb, pends', pop⟩ :=
              Pends.pop (file := file) (labels := labels) _ (.ann ys pends) m'
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
            have hbd₁ := hbd.update l.sym.key none (fun i hi dq hdq => by cases hdq)
            replace hbd₁ : Bounds X.args bnd (update ds l.sym.key none) (sb.filter (· != x.key)) := by
              rw [key]; exact hbd₁
            have blk' : p.block? 0 i = some ⟨([] : List (Lir.Op Mir.Reg)).map .op, .jump (i + 1)⟩ :=
              (LoopLink.link_block bs i).trans blk
            exact iteration_pre (jump_steps blk' (fr := fr) (mem := mem) rfl).to_reflTransGen
              (src.trans pop) (ih hat' pends' { inv' with env := henv } keys cov₁ matched₁ (out'.trans out)
                hm' heb hR hbd₁)
          · cases ha
        · split at ha
          · rename_i x op hx
            split at ha
            · rename_i hc
              cases ha
              obtain ⟨blk, hat'⟩ := hat
              obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hc.1
              have defined := cov.defined hc.2.1
              have hdx : (ds x.key).isSome := by
                simpa [StateMem.Defined, Term.vars] using defined
              rcases Rmw.rmw_runs_closed (labels := labels) hx inv hdx F with
                ub | ⟨ok, m', out', -, keep, inv', src⟩
              · exact .inl (LoopMain.overflows_ub ub)
              have hm' := (CfgArgvMem.stmtClosed ls hstr).closes keep hm
              obtain ⟨envb, F', henv, heb, pends', pop⟩ := Pends.pop (file := file) (labels := labels) F pends m'
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
              have hR₁ : fr₁.get xs.length = some (BitVec.ofNat 64 X.a.argBase) := by
                rw [other₁ _ (Nat.lt_succ_self _) (Nat.ne_of_gt ((LoopMain.layout keys).below l hl))]; exact hR
              have hbd₁ := hbd.update x.key (some (close (defsOf ds) (.bin op (.var x.key) (.lit 1))))
                (fun i hi dq hdq => by
                  cases hdq
                  rcases hc.2.2 with hn | ⟨hadd, hsb⟩
                  · exact absurd hi (not_mem_of_inBnd hn i)
                  · obtain rfl := isAdd_inv hadd
                    obtain ⟨dx, hdx'⟩ := Option.isSome_iff_exists.mp hdx
                    obtain ⟨h0, -, h2⟩ := hbd x.key i hi dx hdx'
                    have hv : (close (defsOf ds) (.bin .add (.var x.key) (.lit 1))).val 0 = dx.val 0 + 1 := by
                      rw [StateExpr.close_val]
                      simp [Term.val, values, defsOf, hdx', Guard.apply]
                    rw [hv]
                    have := h2 hsb
                    omega)
              have blk' : p.block? 0 i = some ⟨(StateExprLir.assignOps regs d l.sym.key
                  (.bin op (.var x.key) (.lit 1))).map .op, .jump (i + 1)⟩ := by
                rw [← key]; exact (LoopLink.link_block bs i).trans blk
              exact iteration_pre (jump_steps blk' exec₁).to_reflTransGen (src.trans pop)
                (ih hat' pends' { inv' with env := henv } keys cov₁ matched₁ (out'.trans out) hm' heb hR₁ hbd₁)
            · cases ha
          · cases ha
  | @test dk sb e yes no P t cy cn ht hc hbo sy sn ihy ihn =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hm he hR hbd
    obtain ⟨blk, haty, hatn⟩ := hat
    have lay := layout1 keys
    have defined := cov.defined hc
    rcases loop_test_step (file := file) (labels := labels) ht hbo inv keys defined F with
      ub | ⟨ok, env', m', tch, inv', hlk, src⟩
    · exact .inl (LoopMain.overflows_ub ub)
    · obtain ⟨fr', tgt, below⟩ := LoopBlocks.core_test_steps regs (values (defsOf ds)) d t (i + 1)
        (i + 1 + cy.size) p 0 i ((LoopLink.link_block bs i).trans blk) fr [] mem ok
        (StateLoopStep.reads lay inv matched defined)
      have match' : Registers regs ds fr' := by
        intro q a ha
        obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
        rw [below _ (by rw [← hk]; exact lay.below l hl)]
        exact matched q a ha
      have hR' : fr'.get xs.length = some (BitVec.ofNat 64 X.a.argBase) := by
        rw [below _ (Nat.lt_succ_self _)]; exact hR
      have he' : ArgvEnv argv X env' := by unfold ArgvEnv; rw [hlk]; exact he
      by_cases hv : t.val (values (defsOf ds)) = 1
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihn hatn pends inv' keys cov match'
          (tch.stdout.trans out) (hm.touched tch) he' hR' hbd)
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihy haty pends inv' keys cov match'
          (tch.stdout.trans out) (hm.touched tch) he' hR' hbd)
  | @atest dk sb e yes no P a x t cy cn ht hi1 hxl hxd hxb sy sn ihy ihn =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hm he hR hbd
    have hI : ArgvChar.Stable (CfgArgvMem.Mem X.args X.idV X.V X.idA X.B X.qs ls) :=
      fun _ _ h g => h.reads g
    obtain ⟨blk, haty, hatn⟩ := hat
    have lay := layout1 keys
    obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp (cov x.key hxd)
    have hlen : 1 ≤ X.args.length := List.length_pos_of_ne_nil ha.1
    obtain ⟨b0, b1, -⟩ := hbd x.key a hxb dx hdx
    rcases Nat.lt_or_ge a X.args.length with hlt | hge
    · have hj : ∀ h : a < X.args.length, 0 ≤ dx.val 0 ∧ dx.val 0 ≤ X.args[a].length :=
        fun h => ⟨b0, by rw [← slen_lt h]; exact b1⟩
      rcases ArgvTest.runs (file := file) (labels := labels) ht inv keys ha hI (fun _ h => h.2.1) hm he
          hxl hdx (by omega) hj F with ub | ⟨ok, env', m', g, hm', inv', hlk, src⟩
      · exact .inl ub
      obtain ⟨l, hl, key⟩ := State.Keys.mem_of_local keys hxl
      have hreg : regs x.key < xs.length + 1 := by rw [key]; exact lay.below l hl
      have hv0 : ((dx.val 0).toNat : Int) = dx.val 0 := Int.toNat_of_nonneg b0
      obtain ⟨fr', tgt, below⟩ := ArgvTest.steps hbase hsize himg ha hlt (j := (dx.val 0).toNat)
        (by have := hj hlt; omega) regs d xs.length argv.key x.key t (i + 1) (i + 1 + cy.size)
        p 0 i ((LoopLink.link_block bs i).trans blk) fr [] (by omega) hreg hR
        (by rw [hv0]; exact matched x.key dx hdx) ok
      have match' : Registers regs ds fr' := by
        intro q a ha
        obtain ⟨_, l, hl, hk, _⟩ := inv'.defs q a ha
        rw [below _ (by rw [← hk]; exact lay.below l hl)]
        exact matched q a ha
      have hR' : fr'.get xs.length = some (BitVec.ofNat 64 X.a.argBase) := by
        rw [below _ (Nat.lt_succ_self _)]; exact hR
      have he' : ArgvEnv argv X env' := by unfold ArgvEnv; rw [hlk]; exact he
      by_cases hv : t.val (ArgvChar.charOfArgs X.args a (dx.val 0).toNat) = 1
      · simp only [hv, ↓reduceIte] at src tgt
        exact iteration_pre tgt.to_reflTransGen src (ihn hatn pends inv' keys cov match'
          (g.stdout.trans out) hm' he' hR' hbd)
      · simp only [hv, ↓reduceIte] at src tgt
        refine iteration_pre tgt.to_reflTransGen src (ihy haty pends inv' keys cov match'
          (g.stdout.trans out) hm' he' hR' ?_)
        by_cases hz : zeroTest t = true
        · simp only [hz, ↓reduceIte]
          unfold Bounds
          intro q i hq dq hd
          obtain ⟨h0, h1, h2⟩ := hbd q i hq dq hd
          refine ⟨h0, h1, fun hs => ?_⟩
          rcases List.mem_cons.mp hs with heq | hs
          · subst heq
            have hpair : (x.key, i) = (x.key, a) := List.inj_on_of_nodup_map hbnd hq hxb rfl
            obtain rfl : i = a := (Prod.mk.inj hpair).2
            rw [hdx] at hd
            cases hd
            have hne := zeroTest_ne hz hv
            rw [slen_lt hlt] at h1 ⊢
            rcases lt_or_eq_of_le h1 with h | h
            · exact h
            · exfalso
              apply hne
              rw [h]
              simpa using ArgvChar.charOfArgs_nul hlt
          · exact h2 hs
        · simp only [hz, Bool.false_eq_true, ↓reduceIte]
          exact hbd
    · obtain rfl : a = X.args.length := by omega
      exact .inl (ArgvTest.runs_null (file := file) (labels := labels) ht inv keys ha hI (fun _ h => h.2.1)
        hm he hxl hdx F)
  | @seq dk sb P c ann pann ty a b seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hm he hR hbd
    exact iteration_pre .refl (ReturnConst.sequence_reaches file labels ann _ a b env F m)
      (ih hat (.bind pann ty b env inv.env he pends) inv keys cov matched out hm he hR hbd)
  | @unit dk sb b P c ann pann seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hm he hR hbd
    obtain ⟨envb, F', henv, heb, pends', pop⟩ :=
      Pends.pop (file := file) (labels := labels) F pends (focusMemory ann m)
    exact iteration_pre .refl ((StateStmt.pure_unit_reaches ann pann env F m).trans pop)
      (ih hat pends' { inv.focus ann with env := henv } keys cov matched (by simpa using out) (hm.focus ann)
        heb hR hbd)
  | @save dk sb P c ann l lty ps body hs seg' ih =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hm he hR hbd
    obtain ⟨vs, ev, rel⟩ := selfParams_evals (file := file) (labels := labels) inv keys ps hs
    have src := LoopReach.save_reaches (file := file) (labels := labels) ann (l, lty) ps body env vs ev F m
    have he' : ArgvEnv argv X (extendEnv ((ps.map Prod.fst).zip vs) env) := by
      unfold ArgvEnv; rw [lookup_zip_other (keys.fresh hfresh) rel]; exact he
    exact iteration_pre .refl src
      (ih hat pends (rebinds (inv.focus ann) rel) keys cov matched (by simpa using out) (hm.focus ann)
        he' hR hbd)
  | @goto dk sb P ann l args hj =>
    intro i env m ls ds F fr hat pends inv keys cov matched out hm he hR hbd
    have blk : p.block? 0 i = some ⟨([] : List (Lir.Op Mir.Reg)).map .op, .jump (idx l.key)⟩ :=
      (LoopLink.link_block bs i).trans hat
    exact .inr (.inl (jump_iter hfresh hlook hcodes hj inv keys cov pends.noBoundary matched out hm he hR hbd
      (jump_steps blk (fr := fr) (mem := mem) rfl)))

end run


/-! ## The recognised document -/

theorem labelCodes_spec {file : File Codec.wireModel Unit Unit} {ret argv : Sym} {xs : List Sym} {bnd : Bnd}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} {T : List Key} :
    (zs : List (Sym × (List Sym × EE))) →
    (∀ kc ∈ labelCodes file ret argv xs bnd tbl D T zs, ∃ z ∈ zs, z.1.key = kc.1 ∧
      Seg file ret argv xs bnd tbl D T (D z.1.key) [] z.2.2 [] kc.2) ∧
      List.Sublist ((labelCodes file ret argv xs bnd tbl D T zs).map (·.1)) (zs.map (·.1.key))
  | [] => by simp [labelCodes]
  | z :: zs => by
    obtain ⟨all, sub⟩ := labelCodes_spec (file := file) (ret := ret) (argv := argv) (xs := xs) (bnd := bnd)
      (tbl := tbl) (D := D) (T := T) zs
    unfold labelCodes
    split
    · rcases hw : walk file ret argv xs bnd tbl D T Cfg.fuel (D z.1.key) [] z.2.2 [] [] with _ | ⟨c, rest⟩
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

theorem stable_spec {file : File Codec.wireModel Unit Unit} {ret argv : Sym} {xs : List Sym} {bnd : Bnd}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} :
    (n : Nat) → {T₀ T : List Key} → {cs : List (Key × Code)} →
    stable file ret argv xs bnd tbl D n T₀ = some (T, cs) →
    cs = labelCodes file ret argv xs bnd tbl D T tbl ∧ cs.map (·.1) = T
  | 0, _, _, _, h => by simp [stable] at h
  | n + 1, T₀, T, cs, h => by
    unfold stable at h
    dsimp only at h
    split at h
    · rename_i heq
      cases h
      exact ⟨rfl, heq⟩
    · exact stable_spec n h

theorem recognize_cases {doc : Codec.Document} {P : Plan} (h : recognize doc = some P) :
    (∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e) ∧ doc.file.callingConvention = .normal ∧
    ∃ s loc marker ty argc tc argv tv body, doc.file.main = some s ∧
      doc.file.funs.lookup s = some (.procedure loc marker ty [(argc, tc), (argv, tv)] body) ∧
      recognizeBody doc.file argc argv body = some P := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
  have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
    rintro ⟨x, g⟩ hx bt e rfl
    exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
  split at h
  · rename_i normal
    cases main : doc.file.main with
    | none => simp [main] at h
    | some sym =>
      cases decl : doc.file.funs.lookup sym with
      | none => simp [main, decl] at h
      | some entry =>
        cases entry <;> try { simp [main, decl] at h }
        case procedure loc marker ty ps body =>
          match ps, h with
          | [(argc, tc), (argv, tv)], h =>
            simp only [main, decl, bind, Option.bind] at h
            exact ⟨hdefs, normal, sym, loc, marker, ty, argc, tc, argv, tv, body, rfl, decl, h⟩
          | [], h => simp [main, decl] at h
          | [_], h => simp [main, decl] at h
          | _ :: _ :: _ :: _, h => simp [main, decl] at h
  · cases h

/-- **From the start to `main`'s tree**: `argc`'s slot is defined, the locals are created, block 0
copies `argc` and the argument block's base, and the two runs are related at the root of the tree
of `main`'s block; the facts `Seg.run` needs about the labels and the arguments hold. -/
theorem recognize_entry (doc : Codec.Document) (P : Plan) (h : recognize doc = some P)
    (args : List String) (ha : Spec.ArgsOk args) (a : Spec.Artifact) (fr : Lir.Frame Mir.Reg)
    (hr1 : fr.get 1 = some (BitVec.ofNat 64 args.length))
    (hr2 : fr.get 2 = some (BitVec.ofNat 64 a.argBase)) :
    ∃ s labels ret tbl T, ∃ X : Ctx, X.a = a ∧ X.args = args ∧
      Spec.coreStart doc args = .ok (s, labels) ∧ ReturnLabel labels ret ∧
      (P.xs.map (·.key)).Nodup ∧ isFresh P.xs P.argv = true ∧ (P.bnd.map (·.1)).Nodup ∧
      CfgArgvMem.StrAbove X.args X.B X.qs ∧
      (∀ s qs b, (s, qs, b) ∈ tbl → labels.lookup s = some (qs, b)) ∧
      (∀ s qs b, (s, qs, b) ∈ tbl → s.key ∈ T →
        ∃ c, Seg doc.file ret P.argv P.xs P.bnd tbl P.D T (P.D s.key) [] b [] c ∧
          At P.blocks (regOf (P.xs.map (·.key))) (P.xs.length + 1) P.xs.length P.argv.key P.idx
            (P.idx s.key) c) ∧
      ∃ cs fr', Reaches doc.file labels s cs ∧
        Lir.execOps ([.move (P.xs.length + 1 + 3) 1, .move (P.xs.length + 1 + 4) 2,
          .move (regOf (P.xs.map (·.key)) P.argc.key) (P.xs.length + 1 + 3),
          .move P.xs.length (P.xs.length + 1 + 4)] : List (Lir.Op Mir.Reg)) fr (a.lmem args) =
          some (fr', a.lmem args) ∧
        Rel doc.file ret P.argv P.xs P.bnd tbl P.D T P.blocks P.idx X ⟨⟨0, 1, 0⟩, fr', [], a.lmem args⟩ cs := by
  obtain ⟨hdefs, normal, sym, loc, marker, ty, argc, tc, argv, tv, body, main, decl, hbody⟩ :=
    recognize_cases h
  obtain ⟨s, labels, xsA, qs, V, C, B, m, hinit, hreach, out₀, objs₀, slotC, dead₀, next₀, lastV, hV8, hC4,
    habove, big₀, mod₀⟩ :=
    ArgvStart.initial_reaches_slots doc.file (Map.ofList (doc.enumBindings.getD [])) args ha hdefs main decl
      normal
  have hlabels : labels = Map.ofList (saves body).reverse := by
    simp [initial, main, decl] at hinit
    exact hinit.2.symm
  unfold recognizeBody at hbody
  split at hbody
  swap
  · cases hbody
  rename_i ann pann bt0 a' sann ret bt r info bann pann' r'
  split at hbody
  swap
  · cases hbody
  rename_i cond
  obtain ⟨hr, unique, hne⟩ := cond
  split at hbody
  swap
  · cases hbody
  rename_i xs e hcr
  dsimp only at hbody
  split at hbody
  swap
  · cases hbody
  rename_i cond₂
  obtain ⟨nodup, hfresh, hsmall, hbnd, hargc⟩ := cond₂
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
  let SAVE : EE := .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
  let BODY : EE := .mk ann (.sseq (.mk pann (.base (none, bt0))) a' SAVE)
  let tbl := labelTable BODY
  have htbl : tbl = saves BODY := labelTable_eq _
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
    have := LoopMain.saves_keys BODY
    rw [this]
    exact unique
  let bnd := (charVars argv BODY).eraseDups
  let D := labelDefs (grow doc.file ret argv xs bnd tbl ((tbl.filter fun z => z.1.key != ret.key).map (·.1.key))
    [argc.key] tbl.length seen) [argc.key]
  obtain ⟨allCodes, sub⟩ := labelCodes_spec (file := doc.file) (ret := ret) (argv := argv) (xs := xs)
    (bnd := bnd) (tbl := tbl) (D := D) (T := T) tbl
  rw [← hcs] at allCodes sub
  let P : Plan := ⟨argc, argv, xs, entry, codes, D, bnd⟩
  let regs := regOf (xs.map (·.key))
  have codesNodup : (codes.map (·.1)).Nodup := sub.nodup tblKeys
  let X : Ctx := ⟨a, args, args.length + 2, V, args.length, B, qs⟩
  refine ⟨s, labels, ret, tbl, T, X, rfl, rfl, hinit, hret, nodup, hfresh, hbnd, habove, hlook, ?_, ?_⟩
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
      emitAll_at regs (xs.length + 1) xs.length argv.key P.idx codes codesNodup (entry.size + 1)
        (⟨([.move (xs.length + 1 + 3) 1, .move (xs.length + 1 + 4) 2, .move (regs argc.key) (xs.length + 1 + 3),
          .move xs.length (xs.length + 1 + 4)] : List (Lir.Op Mir.Reg)).map .op, .jump 1⟩ ::
          entry.emit regs (xs.length + 1) xs.length argv.key P.idx 1) (by simp [emit_length]) _ c hm
  · -- the slot of `argc`, then the locals
    let env₀ : Env := extendEnv [(argc, .object (.pointer (.allocated (args.length + 1) C))),
      (argv, .object (.pointer (.allocated (args.length + 2) V)))] ∅
    have hargv₀ : env₀.lookup argv = some (.object (.pointer (.allocated (args.length + 2) V))) :=
      ConvInt.lookup_two_second rfl (fun e => hne e.symm)
    let lc : Local := ⟨argc, args.length + 1, C⟩
    let ds₀ : Key → Option IntExpr.Term := fun q => if q = argc.key then some (.lit args.length) else none
    have hrange := Argc.argc_range ha
    have inv₀ : Inv env₀ m [lc] ds₀ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro l hl y hy
        obtain rfl := List.mem_singleton.mp hl
        exact StateStmt.lookup_two_fst hy
      · intro l hl
        obtain rfl := List.mem_singleton.mp hl
        exact slotC.live
      · intro x hx y hy ne
        obtain rfl := List.mem_singleton.mp hx
        obtain rfl := List.mem_singleton.mp hy
        exact absurd rfl ne
      · intro q d hd
        simp only [ds₀] at hd
        split at hd
        · rename_i hq
          cases hd
          exact ⟨hrange, lc, List.mem_singleton_self _, hq.symm, slotC⟩
        · cases hd
    have keys₀ : Keys [lc] [argc] := rfl
    have room₀ : ArgvStart.Room m [lc] 1024 := by
      refine ⟨dead₀, ?_, ?_, mod₀, ?_⟩
      · intro l hl; obtain rfl := List.mem_singleton.mp hl; show (args.length : Int) + 1 < m.nextId; omega
      · intro l hl; obtain rfl := List.mem_singleton.mp hl; show m.lastAddress ≤ C; omega
      · simp only [List.length_singleton]; push_cast; omega
    let k₀ : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE env₀, .annotations xsA]
    have hk₀ : NoBoundary k₀ := by simp [k₀, NoBoundary, hasBoundary]
    obtain ⟨env₁, m₁, ls₁, reach₁, inv₁, keys₁, out₁, room₁, below₁, news₁, keeps₁, look₁⟩ :=
      ArgvStart.creates_reaches_room (file := doc.file) (labels := labels) [argc] a' hcr env₀ m [lc] inv₀
        keys₀ room₀ (by omega) k₀
    have pre := hreach.trans ((ReturnConst.sequence_reaches doc.file labels ann _ a' SAVE env₀ _ m).trans reach₁)
    -- the memory
    have grows₁ : StartupArgs.Grows m m₁ :=
      ⟨keeps₁.last, keeps₁.nextId, by rw [room₁.dead, dead₀], keeps₁.enums, out₁, keeps₁.alloc,
        fun x hx => ⟨keeps₁.bytes x hx, keeps₁.pbytes x hx⟩⟩
    have objs₁ := ArgvStore.objs_grows objs₀ grows₁ (by omega) (by omega) (by omega) lastV (by omega)
    have mem₁ : CfgArgvMem.Mem args (args.length + 2) V args.length B qs ls₁ m₁ := by
      refine ⟨⟨?_, by rw [room₁.dead]; simp⟩, objs₁, ?_⟩
      · have := room₁.room
        have := room₁.aligned
        simp only [Mem.Concrete.nextIntAddress]
        have hlen₁ : (ls₁.length : Int) ≤ 1024 := by
          have := congrArg List.length keys₁; simp at this; omega
        omega
      · intro l hl
        rcases news₁ l hl with hl | hl
        · obtain rfl := List.mem_singleton.mp hl
          exact ⟨by show C + 4 ≤ B; omega, .inr (by show V + 8 ≤ C; omega)⟩
        · exact ⟨by omega, .inl (by omega)⟩
    -- the registers
    have hlenxs : xs.length = ls₁.length := by have := congrArg List.length keys₁; simpa using this.symm
    have hargc_xs : argc.key ∈ xs.map (·.key) :=
      List.mem_map.mpr ⟨argc, (CfgGlobals.creates_sublist [argc] a' hcr).subset (by simp), rfl⟩
    have hreg : regs argc.key < xs.length := by simpa using LoopMain.regOf_lt hargc_xs
    let fr' := (((fr.set (xs.length + 1 + 3) (BitVec.ofNat 64 args.length)).set (xs.length + 1 + 4)
      (BitVec.ofNat 64 a.argBase)).set (regs argc.key) (BitVec.ofNat 64 args.length)).set xs.length
      (BitVec.ofNat 64 a.argBase)
    have seed : Lir.execOps ([.move (xs.length + 1 + 3) 1, .move (xs.length + 1 + 4) 2,
        .move (regs argc.key) (xs.length + 1 + 3), .move xs.length (xs.length + 1 + 4)] :
          List (Lir.Op Mir.Reg)) fr (a.lmem args) = some (fr', a.lmem args) := by
      have h1 : (2 : Nat) ≠ xs.length + 1 + 3 := by omega
      have h2 : xs.length + 1 + 4 ≠ regs argc.key := Nat.ne_of_gt (Nat.lt_of_lt_of_le hreg (by omega))
      simp [Lir.execOps, Lir.Op.exec, hr1, hr2, fr', Lir.Frame.get_set, h2]
    refine ⟨_, fr', pre, seed, [argc.key], [], e, [], k₀, entry, 1, env₁, m₁, ls₁, ds₀, fr',
      walk_seg _ hentryw, ?_, rfl, rfl, .base hk₀, inv₁, keys₁, ?_, ?_, out₁.trans out₀, mem₁, ?_, ?_, ?_⟩
    · have := emit_at regs (xs.length + 1) xs.length argv.key P.idx entry 1
        [⟨([.move (xs.length + 1 + 3) 1, .move (xs.length + 1 + 4) 2, .move (regs argc.key) (xs.length + 1 + 3),
          .move xs.length (xs.length + 1 + 4)] : List (Lir.Op Mir.Reg)).map .op, .jump 1⟩]
        (emitAll regs (xs.length + 1) xs.length argv.key P.idx (entry.size + 1) codes) rfl
      simpa [P, Plan.blocks, regs, List.append_assoc] using this
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      simp [ds₀]
    · intro q t hd
      simp only [ds₀] at hd
      split at hd
      · rename_i hq
        cases hd
        subst hq
        have : regOf (xs.map (·.key)) argc.key ≠ xs.length := Nat.ne_of_lt hreg
        simp [fr', regs, Lir.Frame.get_set, this, IntExpr.Term.val]
      · cases hd
    · unfold ArgvEnv
      rw [look₁ argv hfresh]
      exact hargv₀
    · simp [fr', X]
    · intro q i hq dq hd
      simp only [ds₀] at hd
      split at hd
      · rename_i he
        subst he
        exact absurd hq (not_mem_of_inBnd hargc i)
      · cases hd

/-! ## The compiler -/

/-- The artifact of a recognised `main(argc, argv)` (`LoopLink.link P.blocks`). -/
def compile (doc : Codec.Document) : Option Spec.Artifact :=
  match recognize doc with
  | some P => (Backend.artifactOf (LoopLink.link P.blocks)).toOption
  | none => none

/-- **Soundness**: every observation of a compiled `main(argc, argv)` is allowed by Core. -/
theorem compile_sound (doc : Codec.Document) (a : Spec.Artifact) (h : compile doc = some a) :
    ArtifactSound doc a := by
  unfold compile at h
  split at h
  · rename_i P hP
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args hargs saved init o hb
    refine LoopLink.link_sound ha ?_ hl hb
    let fr₀ : Lir.Frame Mir.Reg :=
      (Lir.Frame.empty.set 1 (BitVec.ofNat 64 args.length)).set 2 (BitVec.ofNat 64 a.argBase)
    obtain ⟨s, labels, ret, tbl, T, X, hXa, hXargs, hinit, hret, nodup, hfresh, hbnd, hstr, hlook, hcodes,
      cs, fr', reach, seed, rel⟩ :=
      recognize_entry doc P hP args hargs a fr₀ (by simp [fr₀]) (by simp [fr₀])
    subst hXa hXargs
    right
    have blk : (LoopLink.link P.blocks).prog.block? 0 0 =
        some ⟨([.move (P.xs.length + 1 + 3) 1, .move (P.xs.length + 1 + 4) 2,
          .move (regOf (P.xs.map (·.key)) P.argc.key) (P.xs.length + 1 + 3),
          .move P.xs.length (P.xs.length + 1 + 4)] : List (Lir.Op Mir.Reg)).map .op, .jump 1⟩ := by
      rw [LoopLink.link_block]; rfl
    have toEntry := (jump_steps blk (fr := fr₀) (mem := X.a.lmem X.args) seed).to_reflTransGen
    have obs : ∀ (w : Lir.Word) (o : Spec.Obs), LirObs (.returned [w] (X.a.lmem X.args)) o →
        o = .exit (w.toNat % 256) [] := fun w o ho => LoopLink.exit_obs ha ho
    obtain ⟨hbase, -, himg⟩ := ConstLink.artifact_layout ha
    have img : X.a.image = .empty := by simpa [LoopLink.link] using himg
    have hsize := ArgvAbortLink.artifact_memSize ha
    have step : ∀ ts cs, Rel doc.file ret P.argv P.xs P.bnd tbl P.D T P.blocks P.idx X ts cs →
        LoopSimAbort.Iteration (LoopLink.link P.blocks).prog doc.file labels
          (Rel doc.file ret P.argv P.xs P.bnd tbl P.D T P.blocks P.idx X) ts cs := by
      rintro ts cs ⟨dk, sb, e, Pd, F, c, i, env, m, ls, ds, fr, seg, hat, rfl, rfl, pends, inv, keys, cov,
        matched, out, hm, he, hR, hbd⟩
      exact Seg.run hret nodup hfresh hlook hcodes obs hbase hsize img hargs hstr hbnd seg hat pends inv keys
        cov matched out hm he hR hbd
    refine ⟨s, labels, cs, hinit, reach, ?_, ?_⟩
    · intro b o beh hobs
      exact LoopSimAbort.allowed step rel (LoopSim.behaves_of_steps toEntry beh) hobs
    · intro beh
      exact LoopSimAbort.stuck_ub step rel (LoopSim.behaves_of_steps toEntry beh)
  · cases h

end Silmaril.Compile.Core.Verified.CfgArgv
