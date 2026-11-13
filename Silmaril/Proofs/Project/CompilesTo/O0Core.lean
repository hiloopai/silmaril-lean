module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Compiler.Core.Verified.StateProc.Defs
public import Silmaril.Compiler.Core.Verified.StateExitMem.Defs
public import Silmaril.Compiler.Core.Verified.LocalsStmt.Defs
public import Silmaril.Cerberus.Core.LoopReach.Defs

/-!
# The Core side of gcc `-O0` statement segments

Runs of the Cerberus Core dynamics between the statement boundaries of a procedure body, from
the verified Core library's statement lemmas (`Silmaril.Compile.Core.Verified`): creating the
body's `int` locals (`create_extends`), an initialisation `int x = e;` up to the next statement
(`init_next`), and a `return e;` up to the body of the procedure's return label (`ret_jumps`,
which is `StateProc.ret_returns` stopped at the label). `Safe.not_overflows` turns the library's
`Overflows` alternative into a contradiction with `Source.Safe`.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Core.PureEval (Eval Reaches tagsOf)
open StateMem (Inv Defined defsOf update ptr)
open StateExpr (Term values close)
open ExitCall (Budget)
open ConvInt (IsInt)
open IntExpr (spec)
open Mem.Concrete (LiveInt nextIntAddress)

variable {file : Program} {labels : Labels}

/-! ## Runs and safety -/

/-- A source that may overflow is not safe. -/
theorem Safe.not_overflows {F : FnData} {k0 : List Frame} {s : State}
    (hs : (F.source k0).Safe s) :
    ¬ StateStmt.Overflows (file := F.file) (labels := F.labels) s := by
  rintro ⟨t, ht, hhalt⟩
  exact hs.1 t ht ⟨_, hhalt, fun v h => by cases h⟩

/-- A run between distinct states takes a step. -/
theorem transGen_of_reaches {s t : State} (h : Reaches file labels s t) (hne : s ≠ t) :
    Relation.TransGen (fun s t => ∃ a, Step file labels s a t) s t := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with h | h
  · exact absurd h.symm hne
  · exact h

/-- Two states with stacks of different lengths differ. -/
theorem state_ne_of_length {s t : State} (h : s.stack.length ≠ t.stack.length) : s ≠ t := by
  rintro rfl; exact h rfl

/-! ## Environments and boundaries -/

/-- `Inv` only reads the environment at the locals' symbols. -/
theorem inv_rebind {env env' : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Defs}
    (h : Inv env m ls ds)
    (he : ∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env'.lookup y = env.lookup y) :
    Inv env' m ls ds :=
  haveI := h.ptrs
  { env := fun l hl y hy => (he l hl y hy).trans (h.env l hl y hy)
    live := h.live
    apart := h.apart
    defs := h.defs }

/-- Frames without a boundary above the procedure's frame: the procedure's context. -/
theorem context_of {L : Labels} {k0 : List Frame} :
    ∀ (K : List Frame), (∀ f ∈ K, ¬ FnData.Boundary f) →
      StateProc.Context (labels := labels) L k0 (K ++ .procedureReturn L :: k0)
  | [], _ => by simp [StateProc.Context, procedureContext]
  | f :: K, h => by
    refine StateProc.context_cons (context_of K (fun g hg => h g (by simp [hg]))) ?_
    have hf := h f (by simp)
    cases f <;> simp_all [ReturnLit.NoBoundary, hasBoundary, FnData.Boundary]

/-! ## Creating the body's locals -/

/-- The allocator below the locals `ls`, without the room bound. -/
structure Alloc (m : Mem.Concrete.State) (ls : List Local) : Prop where
  dead : ∀ id ∈ m.dead, id < m.nextId
  ids : ∀ l ∈ ls, l.id < m.nextId
  addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr
  aligned : m.lastAddress % 4 = 0

theorem Alloc.nextIntAddress {m : Mem.Concrete.State} {ls : List Local} (h : Alloc m ls) :
    nextIntAddress m = m.lastAddress - 4 := by
  simp only [Mem.Concrete.nextIntAddress]
  have := h.aligned
  omega

theorem Alloc.budget {m : Mem.Concrete.State} {ls : List Local} (h : Alloc m ls)
    (hroom : 4 < m.lastAddress) : Budget m :=
  ⟨by rw [h.nextIntAddress]; omega, fun hd => by have := h.dead _ hd; omega⟩

theorem AllocRoom.alloc {m : Mem.Concrete.State} {ls : List Local} (h : Silmaril.Project.Shapes.C.CFn.AllocRoom m ls) :
    Alloc m ls :=
  ⟨h.dead, h.ids, h.addrs, h.aligned⟩

/-- **Creating an `int` local** (`create(Ivalignof(int), int)` bound to `x`): the new object
joins the locals, with no definition, below the others. -/
theorem create_extends {ann p : List Annot} {x : Sym} {ty : BaseType} {cr rest : EE}
    (hcr : Locals.createInt cr = true) {env : Env} {k : List Frame} {m : Mem.Concrete.State}
    {ls : List Local} {ds : Defs} (inv : Inv env m ls ds) (al : Alloc m ls)
    (hroom : 4 < m.lastAddress) (hfx : ∀ l ∈ ls, l.sym.key ≠ x.key) :
    ∃ m', Reaches file labels
        ⟨.effectExpr (.mk ann (.sseq (.mk p (.base (some x, ty))) cr rest)) env, k, m⟩
        ⟨.effectExpr rest (extendEnv [(x, ptr ⟨x, m.nextId, nextIntAddress m⟩)] env), k, m'⟩ ∧
      Inv (extendEnv [(x, ptr ⟨x, m.nextId, nextIntAddress m⟩)] env) m'
        (ls ++ [⟨x, m.nextId, nextIntAddress m⟩]) ds ∧
      Alloc m' (ls ++ [⟨x, m.nextId, nextIntAddress m⟩]) ∧ m'.lastAddress = m.lastAddress - 4 := by
  obtain ⟨cann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := State.createInt_inv hcr
  have hnext : nextIntAddress m = m.lastAddress - 4 := al.nextIntAddress
  have hpos : 0 < nextIntAddress m := by rw [hnext]; omega
  have create := Locals.create_reaches (file := file) (labels := labels) cann a1 a2 a3 c1 c2 lc u
    pref env (.strongBind (.mk p (.base (some x, ty))) rest env :: k) m hpos
  rw [State.focus_nextId] at create
  let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
  let m₁ := Actions.created pref c2 (ReturnConst.focusMemory cann m)
  have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) rest env k m₁
  have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
    rw [Locals.created_lastAddress, Locals.nextIntAddress_focus, hnext]
  refine ⟨m₁, (ReturnConst.sequence_reaches file labels ann _ _ rest env k m).trans
    (create.trans bind), ?_, ?_, last₁⟩
  · have := inv.ptrs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl y hy
      rcases List.mem_append.mp hl with hl | hl
      · rw [ConvInt.lookup_one_other (by rw [hy]; exact hfx l hl)]
        exact inv.env l hl y hy
      · obtain rfl := List.mem_singleton.mp hl
        exact ConvInt.lookup_one hy
    · intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · refine StateMem.live_created (Locals.liveInt_focus cann (inv.live l hl)) pref c2 ?_
        rw [State.focus_nextId]; exact Int.ne_of_lt (al.ids l hl)
      · obtain rfl := List.mem_singleton.mp hl
        have := Locals.created_live pref c2 (ReturnConst.focusMemory cann m)
          (by
            rw [State.focus_dead, State.focus_nextId]
            intro hd
            have := al.dead m.nextId hd
            omega)
        rwa [Locals.nextIntAddress_focus, State.focus_nextId] at this
    · intro a ha b hb ne
      rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
      · exact inv.apart a ha b hb ne
      · obtain rfl := List.mem_singleton.mp hb
        refine ⟨Int.ne_of_lt (al.ids a ha), ?_⟩
        have := al.addrs a ha
        show a.addr + 4 ≤ nextIntAddress m ∨ nextIntAddress m + 4 ≤ a.addr
        omega
      · obtain rfl := List.mem_singleton.mp ha
        refine ⟨Int.ne_of_gt (al.ids b hb), ?_⟩
        have := al.addrs b hb
        show nextIntAddress m + 4 ≤ b.addr ∨ b.addr + 4 ≤ nextIntAddress m
        omega
      · obtain rfl := List.mem_singleton.mp ha
        obtain rfl := List.mem_singleton.mp hb
        exact absurd rfl ne
    · intro q d hd
      obtain ⟨ok, l, hl, hk, slot⟩ := inv.defs q d hd
      refine ⟨ok, l, List.mem_append_left _ hl, hk, ?_⟩
      have ha := al.addrs l hl
      refine Slots.slot_created (Locals.slot_focus cann slot) pref c2 ?_ ?_
      · rw [State.focus_nextId]; exact Int.ne_of_lt (al.ids l hl)
      · rw [Locals.nextIntAddress_focus]
        show nextIntAddress m + 4 ≤ l.addr ∨ l.addr + 4 ≤ nextIntAddress m
        omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro id hd
      rw [Locals.created_dead, State.focus_dead] at hd
      have := al.dead id hd
      rw [State.created_nextId, State.focus_nextId]
      omega
    · intro l hl
      rw [State.created_nextId, State.focus_nextId]
      rcases List.mem_append.mp hl with hl | hl
      · have := al.ids l hl; omega
      · obtain rfl := List.mem_singleton.mp hl
        show m.nextId < m.nextId + 1
        omega
    · intro l hl
      rw [last₁]
      rcases List.mem_append.mp hl with hl | hl
      · have := al.addrs l hl; omega
      · obtain rfl := List.mem_singleton.mp hl
        show m.lastAddress - 4 ≤ nextIntAddress m
        omega
    · rw [last₁]; have := al.aligned; omega

/-! ## `int x = e;` up to the next statement -/

/-- **An initialisation, then the next statement**: `int x = e;` stores the value of the closed
term into `x`'s object (or overflows), its sequence frame continues with the statement `e'` of
the next sequence in the frame's environment `env₀`. -/
theorem init_next {e : EE} {x : Sym} {t : Term} (h : StateStmt.initStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Defs}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (hb : Budget m)
    (pann : List Annot) (ty : BaseType) (env₀ : Env) (J : List Frame)
    (ann : List Annot) (p' : Pattern Sym) (e' rest : EE) :
    StateStmt.Overflows (file := file) (labels := labels)
        ⟨.effectExpr e env, .strongBind (.mk pann (.base (none, ty)))
          (.mk ann (.sseq p' e' rest)) env₀ :: J, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m' xs,
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧ Budget m' ∧
        Reaches file labels
          ⟨.effectExpr e env, .strongBind (.mk pann (.base (none, ty)))
            (.mk ann (.sseq p' e' rest)) env₀ :: J, m⟩
          ⟨.effectExpr e' env₀, .strongBind p' rest env₀ :: .annotations xs :: J, m'⟩ := by
  rcases StateExitMem.init_runs (labels := labels) h inv hl hx hd _ hb with
    ub | ⟨ok, m', xs, -, inv', hb', reach⟩
  · exact .inl ub
  · exact .inr ⟨ok, m', xs, inv', hb', reach.trans
      ((Locals.annotations_bind_reaches xs pann ty .unit _ env₀ J m').trans
        (ReturnConst.sequence_reaches file labels ann p' e' rest env₀ _ m'))⟩

/-! ## `return e;` up to the return label -/

/-- `run ret(v)` reaches the body of the label, in the run's environment with the label's
parameter bound, above the procedure's frame. -/
theorem jump_body {L : Labels} {caller : List Frame} {ret l r : Sym} {lb : EE}
    (hl : l.key = ret.key) (hlook : L.lookup ret = some ([r], lb)) (v : Val) (env : Env)
    {k : List Frame} (hk : StateProc.Context (labels := labels) L caller k)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .runLabel l [] [] env :: k, m⟩
      ⟨.effectExpr lb (extendEnv [(r, v)] env), .procedureReturn L :: caller, m⟩ := by
  have hlook' : L.lookup l = some ([r], lb) := by rw [ReturnLit.lookup_key hl]; exact hlook
  exact LoopReach.run_arguments_reaches .nil [] v _ _ m L [r] _ hk hlook' rfl

/-- `StateProc.killsRun_returns`, stopped at the body of the return label. -/
theorem killsRun_jumps {L : Labels} {caller : List Frame} {ret u r : Sym} {lb : EE}
    (hlook : L.lookup ret = some ([r], lb)) :
    (xs : List Sym) → (ls : List Local) → StateStmt.Keys ls xs → (xs.map (·.key)).Nodup →
    {e : EE} → StateStmt.killsRun file ret u xs e = true → (env : Env) → {k : List Frame} →
    StateProc.Context (labels := labels) L caller k → (m : Mem.Concrete.State) →
    (∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ ls, LiveInt m l.id l.addr) →
    (∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    {v : Int} → IsInt v → env.lookup u = some (spec v) →
    ∃ m', Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.effectExpr lb (extendEnv [(r, spec v)] env), .procedureReturn L :: caller, m'⟩
  | [], ls, hls, _, e, h, env, k, hk, m, _, _, _, v, hv, hu => by
    obtain ⟨rann, l, cann, a3, c3, a4, s, u', rfl, hl, hu', hs⟩ := StateStmt.killsRun_nil h
    have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m)) env
        (.inl (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])))
        (.inl (spec v)) :=
      ConvInt.convLoadedInt_eval (ann := c3) hs hv
        (.cons .val (.cons (.sym (by rw [ReturnLit.lookup_key hu']; exact hu)) .nil))
    refine ⟨ReturnConst.focusMemory rann m, ?_⟩
    refine (Straight.focus_reaches (m := m) Straight.request_run).trans ?_
    exact ((PureEval.Eval.sound file _ heval) labels _ _ rfl).trans
      (jump_body hl hlook (spec v) env hk (ReturnConst.focusMemory rann m))
  | x :: xs, ls, hls, nodup, e, h, env, k, hk, m, henv, hlive, hids, v, hv, hu => by
    cases ls with
    | nil => cases hls
    | cons l ls =>
      simp only [StateStmt.Keys, List.map_cons, List.cons.injEq] at hls
      obtain ⟨hxl, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := StateStmt.killsRun_cons h
      obtain ⟨kann, kill⟩ := WrapObj.killAny_reaches (file := file) (labels := labels) hkl env
        (.strongBind (.mk pann (.base (none, ty))) rest env :: k) m
        (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) (hlive l (by simp))
      let m₁ := Locals.killed (ReturnConst.focusMemory kann m) l.id
      have ne : ∀ l' ∈ ls, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ ls.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls, e, hxl] at hm
        exact hm
      obtain ⟨m', reach⟩ := killsRun_jumps hlook xs ls hls nodup hrest env hk m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => StateMem.live_killed (Locals.liveInt_focus kann (hlive l' (by simp [hl'])))
          l.id (ne l' hl'))
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb])) hv hu
      refine ⟨m', ?_⟩
      exact (ReturnConst.sequence_reaches file labels ann _ _ rest env k m).trans (kill.trans
        ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit rest env k m₁).trans reach))

/-- **`return e;`, up to the return label**: the term's value (or an overflow), the kills of
the block's locals `lk` (keys `xs`, among the locals `ls` of the invariant), and the jump to the
label's body with its parameter bound to the value, above the procedure's frame. -/
theorem ret_jumps {L : Labels} {caller : List Frame} {ret r : Sym} {lb : EE}
    (hlook : L.lookup ret = some ([r], lb)) {xs : List Sym} {e : EE} {t : Term}
    (h : StateStmt.retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State}
    {ls : List Local} {ds : Defs} (inv : Inv env m ls ds)
    {lk : List Local} (hlk : StateStmt.Keys lk xs) (hsub : ∀ l ∈ lk, l ∈ ls)
    (nodup : (xs.map (·.key)).Nodup) (hd : Defined ds t = true) {k : List Frame}
    (hk : StateProc.Context (labels := labels) L caller k) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ env' m', Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.effectExpr lb (extendEnv [(r, spec (t.val (values (defsOf ds))))] env'),
          .procedureReturn L :: caller, m'⟩ := by
  unfold StateStmt.retStmt at h
  split at h
  · rename_i ann pann u ty bann e' kr
    split at h
    · rename_i cond
      obtain ⟨hfresh, hkr⟩ := cond
      let σ := values (defsOf ds)
      let K := Frame.strongBind (.mk pann (.base (some u, ty))) kr env :: k
      have pre : Reaches file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr))
            env, k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
        (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
          (ReturnLit.bound_reaches bann _ env _ m)
      have locs := inv.locs hd
      by_cases ok : t.Ok σ
      · right
        refine ⟨ok, ?_⟩
        obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file)
          (labels := labels) t h ok (.bound :: K) m locs
        let v := spec (t.val σ)
        have inv₁ := inv.touched tch
        have henv : ∀ l ∈ lk, ∀ y : Sym, y.key = l.sym.key →
            (extendEnv [(u, v)] env).lookup y = some (ptr l) := by
          intro l hl y hy
          rw [ConvInt.lookup_one_other (by rw [hy]; exact hlk.fresh hfresh l hl)]
          exact inv₁.env l (hsub l hl) y hy
        obtain ⟨m', reach⟩ := killsRun_jumps hlook xs lk hlk nodup hkr (extendEnv [(u, v)] env)
          hk m₁ henv (fun l hl => inv₁.live l (hsub l hl))
          (fun a ha b hb ne => (inv₁.apart a (hsub a ha) b (hsub b hb) ne).1)
          (StateExpr.Term.int_of_ok t ok) (ConvInt.lookup_one rfl)
        exact ⟨_, m', pre.trans ((Interleave.reaches_of_local file labels run).trans
          ((StateStmt.bound_pop hfr v K m₁).trans
            ((ReturnLit.bind_reaches pann u ty v kr env k m₁).trans reach)))⟩
      · left
        exact StateStmt.Overflows.pre pre (StateStmt.fails_overflows (StateExpr.term_fails
          (file := file) (labels := labels) t h ok (.bound :: K) m locs))
    · cases h
  · cases h

end Silmaril.Project.CompilesTo

end
