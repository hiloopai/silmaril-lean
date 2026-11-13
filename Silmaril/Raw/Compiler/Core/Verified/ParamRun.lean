module

public import Silmaril.Compiler.Core.Verified.ParamAlloc.Defs
public import Silmaril.Compiler.Core.Verified.StateGlobals.Defs
/-! # Mutable parameter bodies with conditionals and locals

`StateParam.stmts` accepts straight assignments and a return. `run` also accepts
`if (c) A else B` (with or without `else`) whose arms are any accepted statements:
both arms continue with the pending right sides of strong sequences (`todo`), so the
callee's term selects between the two arms' terms (`StmtIf.choose`) and the target
computes the test at run time. Sequencing and `pure(unit)` glue are accepted wherever
they occur, and so are `int x = e;` and `int x;` of the callee's own locals.

`block` first creates up to `J` `int` locals (`J = 0` for callers without an
allocation reserve). As in `StateParam`, the argument objects belong to the caller
and survive the return; a return kills the callee's locals. `Keeps` says that the
statements allocate nothing and kill only older objects; `Uses J` that the whole
body allocated at most `J` objects.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamRun

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Mem.Concrete (LiveInt nextIntAddress)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open ConvInt (IsInt)
open StateExpr (Key Term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt (retStmt assignStmt initStmt uninitStmt isLocal isFresh Keys seqFocus_touched
  killsRun_nil killsRun_cons)
open StateGlobals (ifParts ifParts_inv seqParts seqParts_inv isUnit isUnit_inv termSize EnvOk
  inv_withEnv)
open StateProc (Context context_cons)
open IntExpr (spec)
open LoadTask (Touched)

/-- The statements of a parameter body over the slots `ys` (parameters and locals), whose
returns kill the locals `xs`: `fuel` bounds the nesting, `todo` holds the pending right sides
of strong sequences. Each arm of a conditional runs the pending statements. -/
def run (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : List Sym) :
    Nat → (Key → Option IntExpr.Term) → (Key → Nat) → Eff → List Eff → Option IntExpr.Term
  | 0, _, _, _, _ => none
  | n + 1, ds, sz, e, todo =>
    match retStmt file ret xs e with
    | some t =>
      if Defined ds t = true ∧ State.closeSize sz t ≤ State.maxSize then
        some (close (defsOf ds) t) else none
    | none => match ifParts file ys e with
      | some (tc, ea, eb) =>
        if Defined ds tc = true ∧ State.closeSize sz tc ≤ State.maxSize then
          match run file ret ys xs n ds sz ea todo, run file ret ys xs n ds sz eb todo with
          | some a, some b =>
            if termSize (StmtIf.choose (close (defsOf ds) tc) a b) ≤ State.maxSize then
              some (StmtIf.choose (close (defsOf ds) tc) a b) else none
          | _, _ => none
        else none
      | none => match assignStmt file e with
        | some (x, t) =>
          if isLocal ys x = true ∧ Defined ds t = true ∧ State.closeSize sz t ≤ State.maxSize then
            match todo with
            | [] => none
            | r :: todo =>
              run file ret ys xs n (update ds x.key (some (close (defsOf ds) t)))
                (fun q => if q = x.key then State.closeSize sz t else sz q) r todo
          else none
        | none => match initStmt file e with
          | some (x, t) =>
            if isLocal ys x = true ∧ Defined ds t = true ∧ State.closeSize sz t ≤ State.maxSize then
              match todo with
              | [] => none
              | r :: todo =>
                run file ret ys xs n (update ds x.key (some (close (defsOf ds) t)))
                  (fun q => if q = x.key then State.closeSize sz t else sz q) r todo
            else none
          | none => match uninitStmt e with
            | some x =>
              if isLocal ys x = true then
                match todo with
                | [] => none
                | r :: todo => run file ret ys xs n (update ds x.key none) sz r todo
              else none
            | none => match seqParts e with
              | some (s, rest) => run file ret ys xs n ds sz s (rest :: todo)
              | none =>
                if isUnit e = true then
                  match todo with
                  | [] => none
                  | r :: todo => run file ret ys xs n ds sz r todo
                else none

/-- How deeply a parameter body may nest its statements. -/
def fuel : Nat := 4096

/-- The creation of an `int` local, and the rest of the block. -/
def creation : Eff → Option (Sym × Eff)
  | .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    if Locals.createInt cr = true then some (x, rest) else none
  | _ => none

/-- The block of a parameter body over the parameters `ps`: at most `j` more creations of
`int` locals (the locals `xs` so far), then the statements. -/
def block (file : File Codec.wireModel Unit Unit) (ret : Sym) (ps : List Sym) :
    Nat → List Sym → (Key → Option IntExpr.Term) → Eff → Option IntExpr.Term
  | 0, xs, ds, e => match creation e with
    | some _ => none
    | none =>
      if ((ps ++ xs).map (·.key)).Nodup then run file ret (ps ++ xs) xs fuel ds (fun _ => 1) e []
      else none
  | j + 1, xs, ds, e => match creation e with
    | some (x, rest) => if isFresh (ps ++ xs) x = true then block file ret ps j (xs ++ [x]) ds rest else none
    | none =>
      if ((ps ++ xs).map (·.key)).Nodup then run file ret (ps ++ xs) xs fuel ds (fun _ => 1) e []
      else none

/-- The most `int` locals of a callee whose caller reserves room for them. -/
def maxLocals : Nat := 8

/-- One symbolic parameter, as in `StateParam.body`, with conditionals and at most `J` locals. -/
def body (file : File Codec.wireModel Unit Unit) (x : Sym) (e : Eff) (J : Nat := 0) :
    Option IntExpr.Term :=
  match e with
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then
        block file ret [x] J [] (StateParam.paramDefs x) a else none
  | _ => none

/-! ## Substitution -/

theorem termSize_subst (c : Int) : (t : IntExpr.Term) →
    termSize (StateSubst.subst (.lit c) t) = termSize t
  | .lit _ => rfl
  | .var => rfl
  | .bin _ a b => by simp [StateSubst.subst, termSize, termSize_subst c a, termSize_subst c b]
  | .cmp _ _ _ a b => by simp [StateSubst.subst, termSize, termSize_subst c a, termSize_subst c b]
  | .cond d a b => by
    simp [StateSubst.subst, termSize, termSize_subst c d, termSize_subst c a, termSize_subst c b]
  | .bit _ a b => by simp [StateSubst.subst, termSize, termSize_subst c a, termSize_subst c b]
  | .divpos _ _ a => by simp [StateSubst.subst, termSize, termSize_subst c a]

/-- Instantiating the input changes the result only by substitution. -/
theorem run_subst (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : List Sym) (c : Int) :
    (n : Nat) → (ds : Key → Option IntExpr.Term) → (sz : Key → Nat) → (e : Eff) → (todo : List Eff) →
    run file ret ys xs n (StateSubst.defs (.lit c) ds) sz e todo =
      (run file ret ys xs n ds sz e todo).map (StateSubst.subst (.lit c))
  | 0, _, _, _, _ => rfl
  | n + 1, ds, sz, e, todo => by
    simp only [run, StateSubst.defined_defs, StateSubst.close_defs]
    split
    next => split <;> rfl
    split
    next tc ea eb _ =>
      split
      next =>
        rw [run_subst file ret ys xs c n ds sz ea todo, run_subst file ret ys xs c n ds sz eb todo]
        cases run file ret ys xs n ds sz ea todo <;> cases run file ret ys xs n ds sz eb todo <;>
          simp only [Option.map_some, Option.map_none]
        rw [← StateSubst.subst_choose, termSize_subst]
        split <;> rfl
      next => rfl
    split
    next x t _ =>
      split
      next =>
        split
        next => rfl
        next r todo' =>
          simpa only [StateSubst.defs_update, Option.map_some] using run_subst file ret ys xs c n
            (update ds x.key (some (close (defsOf ds) t)))
            (fun q => if q = x.key then State.closeSize sz t else sz q) r todo'
      next => rfl
    split
    next x t _ =>
      split
      next =>
        split
        next => rfl
        next r todo' =>
          simpa only [StateSubst.defs_update, Option.map_some] using run_subst file ret ys xs c n
            (update ds x.key (some (close (defsOf ds) t)))
            (fun q => if q = x.key then State.closeSize sz t else sz q) r todo'
      next => rfl
    split
    next x _ =>
      split
      next =>
        split
        next => rfl
        next r todo' =>
          simpa only [StateSubst.defs_update, Option.map_none] using
            run_subst file ret ys xs c n (update ds x.key none) sz r todo'
      next => rfl
    split
    next s rest _ => exact run_subst file ret ys xs c n ds sz s (rest :: todo)
    split
    next =>
      split
      next => rfl
      next r todo' => exact run_subst file ret ys xs c n ds sz r todo'
    next => rfl

theorem block_subst (file : File Codec.wireModel Unit Unit) (ret : Sym) (ps : List Sym) (c : Int) :
    (j : Nat) → (xs : List Sym) → (ds : Key → Option IntExpr.Term) → (e : Eff) →
    block file ret ps j xs (StateSubst.defs (.lit c) ds) e =
      (block file ret ps j xs ds e).map (StateSubst.subst (.lit c))
  | 0, xs, ds, e => by
    simp only [block]
    split
    next => rfl
    next => split <;> simp [run_subst]
  | j + 1, xs, ds, e => by
    simp only [block]
    split
    next x rest _ => split <;> simp [block_subst file ret ps c j]
    next => split <;> simp [run_subst]

/-! ## Allocation metadata -/

/-- The statements allocate nothing; only objects older than the fresh id die. -/
structure Keeps (m m' : Mem.Concrete.State) : Prop where
  next : m'.nextId = m.nextId
  last : m'.lastAddress = m.lastAddress
  dead : ∀ d ∈ m'.dead, d ∈ m.dead ∨ d < m.nextId

theorem Keeps.refl (m : Mem.Concrete.State) : Keeps m m := ⟨rfl, rfl, fun _ h => .inl h⟩

theorem Keeps.trans {m₁ m₂ m₃ : Mem.Concrete.State} (a : Keeps m₁ m₂) (b : Keeps m₂ m₃) :
    Keeps m₁ m₃ := by
  refine ⟨b.next.trans a.next, b.last.trans a.last, fun d hd => ?_⟩
  rcases b.dead d hd with h | h
  · exact a.dead d h
  · exact .inr (a.next ▸ h)

theorem keeps_same {m m' : Mem.Concrete.State} (h : Rmw.Same m m') : Keeps m m' :=
  ⟨h.1, h.2.2, fun _ hd => .inl (h.2.1 ▸ hd)⟩

theorem same_touched {m m' : Mem.Concrete.State} (h : Touched m m') : Rmw.Same m m' := by
  obtain ⟨l, u, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩

theorem keeps_killed (m : Mem.Concrete.State) (ann : List Annot) {id : Int} (hid : id < m.nextId) :
    Keeps m (Locals.killed (focusMemory ann m) id) := by
  refine ⟨State.focus_nextId ann m, State.focus_lastAddress ann m, fun d hd => ?_⟩
  simp only [Locals.killed, List.mem_cons] at hd
  rcases hd with rfl | hd
  · exact .inr hid
  · exact .inl (by rwa [State.focus_dead] at hd)

/-- A body allocated at most `J` `int` objects below its entry's last address. -/
structure Uses (J : Nat) (m m' : Mem.Concrete.State) : Prop where
  next : m.nextId ≤ m'.nextId
  last : m.lastAddress - 4 * J ≤ m'.lastAddress
  aligned : m'.lastAddress % 4 = m.lastAddress % 4
  dead : ∀ d ∈ m'.dead, d ∈ m.dead ∨ d < m'.nextId

theorem Uses.of_keeps {J : Nat} {m m' : Mem.Concrete.State} (h : Keeps m m') : Uses J m m' := by
  refine ⟨h.next.ge, by rw [h.last]; omega, by rw [h.last], fun d hd => ?_⟩
  rcases h.dead d hd with h' | h'
  · exact .inl h'
  · exact .inr (h.next ▸ h')

/-! ## Core side -/

variable {file : Program} {labels L : Labels} {caller : List Frame}

/-- Successful local return with the parameter objects `ps` live, the allocation metadata
related by `R`, or a local overflow. -/
def Returns (R : Mem.Concrete.State → Mem.Concrete.State → Prop) (ps : List Local) (s : State)
    (t : IntExpr.Term) (out : String) : Prop :=
  (t.Ok 0 ∧ ∃ m', m'.stdout = out ∧ R s.memory m' ∧ (∀ l ∈ ps, LiveInt m' l.id l.addr) ∧
    LocalReaches file labels false s ⟨.value (spec (t.val 0)), .procedureReturn L :: caller, m'⟩) ∨
  ArenaFail.Fails file labels false s IntExpr.overflow

theorem Returns.pre {R R' : Mem.Concrete.State → Mem.Concrete.State → Prop} {ps : List Local}
    {s s' : State} {t : IntExpr.Term} {out : String}
    (h : LocalReaches file labels false s s') (hR : ∀ m', R s'.memory m' → R' s.memory m')
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) R ps s' t out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) R' ps s t out := by
  rcases o with ⟨ok, m', hout, rel, live, r⟩ | ub
  · exact .inl ⟨ok, m', hout, hR m' rel, live, h.trans r⟩
  · exact .inr (ArenaFail.Fails.pre file labels h ub)

/-- `Returns.pre` over statements that keep the allocation metadata. -/
theorem Returns.keep {ps : List Local} {s s' : State} {t : IntExpr.Term} {out : String}
    (h : LocalReaches file labels false s s') (k : Keeps s.memory s'.memory)
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) Keeps ps s' t out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) Keeps ps s t out :=
  o.pre h fun _ h' => k.trans h'

/-- The pending statements: wildcard strong binds and annotation frames above the procedure's
own frames. -/
inductive Pend (ls : List Local) : List Eff → List Frame → Prop
  | base {k : List Frame} : Context (labels := labels) L caller k → Pend ls [] k
  | ann {todo : List Eff} {k : List Frame} (xs : List Access) :
      Pend ls todo k → Pend ls todo (.annotations xs :: k)
  | bind {todo : List Eff} {k : List Frame} {env : Env} (pann : List Annot) (ty : BaseType)
      (rest : Eff) : EnvOk env ls → Pend ls todo k →
      Pend ls (rest :: todo) (.strongBind (.mk pann (.base (none, ty))) rest env :: k)

theorem Pend.context {ls : List Local} {todo : List Eff} {k : List Frame}
    (p : Pend (labels := labels) (L := L) (caller := caller) ls todo k) :
    Context (labels := labels) L caller k := by
  induction p with
  | base hk => exact hk
  | ann _ _ ih => exact context_cons ih (by simp [NoBoundary, hasBoundary])
  | bind _ _ _ _ _ ih => exact context_cons ih (by simp [NoBoundary, hasBoundary])

theorem annotations_merge (xs ys : List Access) (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.value v, .annotations xs :: .annotations ys :: k, m⟩
      ⟨.value v, .annotations (xs ++ ys) :: k, m⟩ :=
  .single (.next (by simp [requestAux, awaitsScheduling]) (LoadTask.plain_value _))

/-- A finished statement, over at most one annotation frame, resumes the next pending
statement. -/
theorem Pend.resume {ls : List Local} {todo : List Eff} {k : List Frame}
    (p : Pend (labels := labels) (L := L) (caller := caller) ls todo k) (v : Val) :
    ∀ (fr : Option (List Access)) (m : Mem.Concrete.State) (r : Eff) (todo' : List Eff),
      todo = r :: todo' → ∃ env k', EnvOk env ls ∧
        Pend (labels := labels) (L := L) (caller := caller) ls todo' k' ∧
        LocalReaches file labels false ⟨.value v, (fr.map .annotations).toList ++ k, m⟩
          ⟨.effectExpr r env, k', m⟩ := by
  induction p with
  | base _ => intro _ _ _ _ h; cases h
  | ann xs p ih =>
    intro fr m r todo' h
    cases fr with
    | none => exact ih (some xs) m r todo' h
    | some a =>
      obtain ⟨env, k', he, p', reach⟩ := ih (some (a ++ xs)) m r todo' h
      exact ⟨env, k', he, p', (annotations_merge a xs v _ m).trans reach⟩
  | bind pann ty rest₀ he p _ =>
    intro fr m r todo' h
    cases h
    cases fr with
    | none => exact ⟨_, _, he, p, StateReturnLocal.wildcard pann ty v rest₀ _ _ m⟩
    | some a => exact ⟨_, _, he, .ann a p, StateActionsLocal.annotations_bind a pann ty v rest₀ _ _ m⟩

/-! ## Statements -/

theorem init_keeps {e : Eff} {x : Sym} {t : Term} (h : initStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) :
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ IntExpr.overflow ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Rmw.Same m m' ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, a1, t₀, ty, a2, e', a3, lc, u, b1, c1, b2, b3, b4, c3, b5, s, t', rfl, ht', htx, hs,
    he⟩ := StateStmt.initStmt_inv h
  let σ := values (defsOf ds)
  let ST : EE := .mk a3 (.action (.mk .pos (.mk lc u (.store false (Locals.intVal b1 c1)
    (.mk b2 () (.sym x)) (.mk b3 () (.call (.sym s) [Locals.intVal b4 c3, .mk b5 () (.sym t')])) .na))))
  let K := Frame.strongBind (.mk a1 (.base (some t₀, ty))) ST env :: k
  have pre : LocalReaches file labels false ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some t₀, ty)))
      (.mk a2 (.bound e')) ST)) env, k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
    (CallLocal.sequence a0 _ _ _ env k m).trans (CallLocal.bound a2 _ env _ m)
  have locs := inv.locs hd
  by_cases ok : t.Ok σ
  · right
    refine ⟨ok, ?_⟩
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      t he ok (.bound :: K) m locs
    let v := t.val σ
    have hv : IsInt v := StateExpr.Term.int_of_ok t ok
    let env₁ := extendEnv [(t₀, spec v)] env
    have inv₁ : Inv env m₁ ls ds := inv.touched tch
    have hx₁ : env₁.lookup x = some (ptr l) := by
      rw [ConvInt.lookup_one_other (fun e => htx e.symm)]; exact inv.lookup hl hx
    obtain ⟨ys, hst⟩ := StateActionsLocal.store (file := file) (labels := labels) a3 b1 b2 b3 b4 b5 c1 c3
      lc u x s t' hs env₁ k m₁ hx₁ (ConvInt.lookup_one ht') hv (inv₁.live l hl)
    have inv₂ := (inv₁.focus a3).store hl (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
    rw [StateExpr.close_val] at inv₂
    refine ⟨_, ys, ?_, ?_, inv₂, ?_⟩
    · simp [Locals.stored_stdout, tch.stdout]
    · exact (same_touched tch).trans ((Rmw.same_focus a3 m₁).trans (Rmw.same_stored _ _ _ _))
    · exact pre.trans (run.trans ((StateReturnLocal.bound_pop hfr _ K m₁).trans
        ((CallLocal.bind a1 t₀ ty _ ST env k m₁).trans hst)))
  · left
    exact ArenaFail.Fails.pre file labels pre (StateExpr.term_fails (file := file) (labels := labels)
      t he ok (.bound :: K) m locs)

theorem same_uninit (m : Mem.Concrete.State) (id addr : Int) :
    Rmw.Same m (Uninitialized.stored m id addr) := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (List.replicate 4 none)) m
  simp only [Uninitialized.stored, hw]; exact ⟨rfl, rfl, rfl⟩

theorem uninit_keeps {e : Eff} {x : Sym} (h : uninitStmt e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Rmw.Same m m' ∧ Inv env m' ls (update ds l.sym.key none) ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, c1, b2, b3, c3, rfl⟩ := StateStmt.uninitStmt_inv h
  refine ⟨_, _, ?_, (Rmw.same_focus a0 m).trans (same_uninit _ _ _), (inv.focus a0).uninit hl,
    StateActionsLocal.uninitialized (file := file) (labels := labels) a0 b1 c1 b2 b3 c3 lc u x env k m
      (inv.lookup hl hx) (inv.live l hl)⟩
  simp [Uninitialized.stored_stdout]

/-- The kills of a return, then the jump to the return label: the parameter objects `ps`
survive, and only the killed locals (older than the fresh id) die. -/
theorem kills_keep {ret u : Sym} (hret : ReturnLabel L ret) :
    (xs : List Sym) → (lk : List Local) → Keys lk xs → (xs.map (·.key)).Nodup →
    {e : Eff} → StateStmt.killsRun file ret u xs e = true → (env : Env) →
    (loc : List Frame) → NoBoundary loc → (caller : List Frame) →
    (m : Mem.Concrete.State) →
    (∀ l ∈ lk, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ lk, LiveInt m l.id l.addr) →
    (∀ a ∈ lk, ∀ b ∈ lk, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    (∀ l ∈ lk, l.id < m.nextId) → (ps : List Local) → (∀ p ∈ ps, LiveInt m p.id p.addr) →
    (∀ p ∈ ps, ∀ l ∈ lk, p.id ≠ l.id) →
    {v : Int} → IsInt v → env.lookup u = some (spec v) →
    ∃ m', m'.stdout = m.stdout ∧ Keeps m m' ∧ (∀ p ∈ ps, LiveInt m' p.id p.addr) ∧
      LocalReaches file labels false
        ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
        ⟨.value (spec v), .procedureReturn L :: caller, m'⟩
  | [], lk, hls, _, e, h, env, loc, hk, caller, m, _, _, _, _, ps, hps, _, v, hv, hu => by
    obtain ⟨rann, l, cann, a3, c3, a4, s, u', rfl, hl, hu', hs⟩ := killsRun_nil h
    have heval : ∀ tags, Eval file tags env
        (.inl (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])) )
        (.inl (spec v)) := fun _ =>
      ConvInt.convLoadedInt_eval (ann := c3) hs hv
        (.cons .val (.cons (.sym (by rw [ReturnLit.lookup_key hu']; exact hu)) .nil))
    obtain ⟨m', touched, back⟩ := StateParam.jump_return (file := file) (labels := labels)
      hl hret (spec v) env hk caller (focusMemory rann m)
    have T := (LoadTask.focusMemory_touched rann m).trans touched
    refine ⟨m', T.stdout, keeps_same (same_touched T), fun p hp => CallArg.touched_live T (hps p hp), ?_⟩
    refine (CallLocal.focus (c' := .pureExpr
        (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])) env)
      (k' := .runLabel l [] [] env :: (loc ++ .procedureReturn L :: caller))
      rann m (LoadTask.plain_pureExpr _ _) ?_).trans ?_
    · simp [requestAux, awaitsScheduling, focusMemory]; rfl
    · exact (PureLocal.eval_local file _ (heval _) _ _ rfl).trans back
  | x :: xs, lk, hls, nodup, e, h, env, loc, hk, caller, m, henv, hlive, hids, hnext, ps, hps, hpk,
      v, hv, hu => by
    cases lk with
    | nil => cases hls
    | cons l lk =>
      simp only [Keys, List.map_cons, List.cons.injEq] at hls
      obtain ⟨hxl, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := killsRun_cons h
      let K := loc ++ .procedureReturn L :: caller
      obtain ⟨kann, kr⟩ := StateReturnLocal.killAny (file := file) (labels := labels) hkl env
        (.strongBind (.mk pann (.base (none, ty))) rest env :: K) m
        (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) (hlive l (by simp))
      let m₁ := Locals.killed (focusMemory kann m) l.id
      have keep₁ : Keeps m m₁ := keeps_killed m kann (hnext l (by simp))
      have ne : ∀ l' ∈ lk, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ lk.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls, e, hxl] at hm
        exact hm
      obtain ⟨m', out, keep, live, reach⟩ := kills_keep hret xs lk hls nodup hrest env loc hk caller m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => StateMem.live_killed (Locals.liveInt_focus kann (hlive l' (by simp [hl'])))
          l.id (ne l' hl'))
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb]))
        (fun l' hl' => by rw [keep₁.next]; exact hnext l' (by simp [hl']))
        ps (fun p hp => StateMem.live_killed (Locals.liveInt_focus kann (hps p hp)) l.id
          (hpk p hp l (by simp)))
        (fun p hp l' hl' => hpk p hp l' (by simp [hl'])) hv hu
      refine ⟨m', by rw [out]; simp [m₁, Locals.killed], keep₁.trans keep, live, ?_⟩
      exact (CallLocal.sequence ann _ _ rest env K m).trans (kr.trans
        ((StateReturnLocal.wildcard pann ty .unit rest env K m₁).trans reach))

/-- A return kills the locals `lk` and keeps the parameter objects `ps`. -/
theorem ret_keeps {ret : Sym} (hret : ReturnLabel L ret)
    {xs : List Sym} {e : Eff} {t : Term}
    (h : retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State} {ps lk : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m (ps ++ lk) ds) (hlk : Keys lk xs)
    (nodup : (xs.map (·.key)).Nodup) (hd : Defined ds t = true)
    (hnext : ∀ l ∈ lk, l.id < m.nextId) (hpk : ∀ p ∈ ps, ∀ l ∈ lk, p.id ≠ l.id)
    (loc : List Frame) (hk : NoBoundary loc) (caller : List Frame) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) Keeps ps
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩ (close (defsOf ds) t) m.stdout := by
  unfold retStmt at h
  split at h
  · rename_i ann pann u ty bann e' kr
    split at h
    · rename_i cond
      obtain ⟨hfresh, hkr⟩ := cond
      let σ := values (defsOf ds)
      let k := loc ++ .procedureReturn L :: caller
      let K := Frame.strongBind (.mk pann (.base (some u, ty))) kr env :: k
      have pre : LocalReaches file labels false
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr)) env, k, m⟩
          ⟨.effectExpr e' env, .bound :: K, m⟩ :=
        (CallLocal.sequence ann _ _ _ env k m).trans (CallLocal.bound bann _ env K m)
      by_cases ok : t.Ok σ
      · left
        refine ⟨StateExpr.close_ok _ t (inv.defs_ok hd) ok, ?_⟩
        obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
          t h ok (.bound :: K) m (inv.locs hd)
        let v := spec (t.val σ)
        have inv₁ := inv.touched tch
        have fresh : ∀ l ∈ lk, l.sym.key ≠ u.key := hlk.fresh hfresh
        obtain ⟨m', out, keep, live, reach⟩ := kills_keep hret xs lk hlk nodup hkr (extendEnv [(u, v)] env)
          loc hk caller m₁
          (fun l hl y hy => by
            rw [ConvInt.lookup_one_other (by rw [hy]; exact fresh l hl)]
            exact inv₁.env l (List.mem_append_right _ hl) y hy)
          (fun l hl => inv₁.live l (List.mem_append_right _ hl))
          (fun a ha b hb ne => (inv₁.apart a (List.mem_append_right _ ha) b
            (List.mem_append_right _ hb) ne).1)
          (fun l hl => by rw [(same_touched tch).1]; exact hnext l hl)
          ps (fun p hp => inv₁.live p (List.mem_append_left _ hp)) hpk
          (StateExpr.Term.int_of_ok t ok) (ConvInt.lookup_one rfl)
        refine ⟨m', by rw [out, tch.stdout], (keeps_same (same_touched tch)).trans keep, live, ?_⟩
        rw [StateExpr.close_val]
        exact pre.trans (run.trans ((StateReturnLocal.bound_pop hfr v K m₁).trans
          ((CallLocal.bind pann u ty v kr env k m₁).trans reach)))
      · exact .inr (ArenaFail.Fails.pre file labels pre
          (StateExpr.term_fails (file := file) (labels := labels) t h ok (.bound :: K) m (inv.locs hd)))
    · cases h
  · cases h

/-- A local `if` statement: the test runs, and the selected arm follows with the same frames. -/
theorem if_runs {ys : List Sym} {e ea eb : Eff} {tc : Term} (h : ifParts file ys e = some (tc, ea, eb))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (hls : Keys ls ys) (hdc : Defined ds tc = true) (k : List Frame) :
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ IntExpr.overflow ∨
    (tc.Ok (values (defsOf ds)) ∧ ∃ env' m', Touched m m' ∧ Inv env' m' ls ds ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.effectExpr (if tc.val (values (defsOf ds)) = 1 then eb else ea) env', k, m'⟩) := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, hb', hcb, hfc, hfb, htc⟩ :=
    ifParts_inv h
  replace htc : StateExpr.term file ec = some tc := htc.2.2
  let σ := values (defsOf ds)
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea eb)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : LocalReaches file labels false
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (CallLocal.sequence a0 _ _ _ env k m).trans (CallLocal.bound a2 _ env _ m)
  by_cases okc : tc.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc)
    let cv := tc.val σ
    let env₁ := extendEnv [(c, spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := StateActionsLocal.boolSource_touched (file := file) (labels := labels)
      hcb env₁ KB m₁ cv (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : CallArena.LPure (file := file) (labels := labels)
        (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      CallArena.of_eval (fun _ => Eval.sym (ConvInt.lookup_one hb'))
    let m₃ := SeqReach.focusMemory a5 m₂
    have enter : LocalReaches file labels false ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then ea else eb) env₂, k, m₃⟩ :=
      run.trans ((StateReturnLocal.bound_pop hfr _ K m₁).trans
        ((CallLocal.bind a1 c cty _ REST env k m₁).trans
          ((CallLocal.sequence a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((CallLocal.bind a4 b bty _ IF env₁ k m₂).trans
              (CallArena.effect_if a5 flag hp k m₂))))))
    have tch₃ : Touched m m₃ := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    have inv₂ : Inv env₂ m₃ ls ds := ((inv.touched tch₃).extend (hls.fresh hfc)).extend (hls.fresh hfb)
    refine ⟨okc, env₂, m₃, tch₃, inv₂, pre.trans ?_⟩
    have hsel : (if flag then ea else eb) = (if tc.val σ = 1 then eb else ea) := by
      by_cases h1 : tc.val σ = 1 <;> simp [flag, cv, h1]
    rw [← hsel]
    exact enter
  · left
    exact ArenaFail.Fails.pre file labels pre (StateExpr.term_fails (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc))

theorem returns_choose_left {R : Mem.Concrete.State → Mem.Concrete.State → Prop} {ls : List Local}
    {s : State} {C A B : IntExpr.Term} {out : String} (okC : C.Ok 0) (h1 : C.val 0 ≠ 1)
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) R ls s A out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) R ls s (StmtIf.choose C A B) out := by
  rcases o with ⟨okA, m', hout, rel, live, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okA]⟩, m', hout, rel, live, ?_⟩
    rw [StmtIf.choose_val, ite_eq_right h1]; exact r
  · exact .inr ub

theorem returns_choose_right {R : Mem.Concrete.State → Mem.Concrete.State → Prop} {ls : List Local}
    {s : State} {C A B : IntExpr.Term} {out : String} (okC : C.Ok 0) (h1 : C.val 0 = 1)
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) R ls s B out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) R ls s (StmtIf.choose C A B) out := by
  rcases o with ⟨okB, m', hout, rel, live, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okB]⟩, m', hout, rel, live, ?_⟩
    rw [StmtIf.choose_val, ite_eq_left h1]; exact r
  · exact .inr ub

/-- **The statements of a parameter body** over the parameters `ps` and the locals `lk` return
their term with the parameter objects live, allocating nothing, or reach a local overflow. -/
theorem run_returns {ret : Sym} (hret : ReturnLabel L ret) {ys xs : List Sym} {ps lk : List Local}
    (hls : Keys (ps ++ lk) ys) (hlk : Keys lk xs) (nodup : (xs.map (·.key)).Nodup)
    (hpk : ∀ p ∈ ps, ∀ l ∈ lk, p.id ≠ l.id) :
    (n : Nat) → (ds : Key → Option IntExpr.Term) → (sz : Key → Nat) →
    (e : Eff) → (todo : List Eff) → {t : IntExpr.Term} → run file ret ys xs n ds sz e todo = some t →
    ∀ (env : Env) (m : Mem.Concrete.State), Inv env m (ps ++ lk) ds → (∀ l ∈ lk, l.id < m.nextId) →
    ∀ (k : List Frame), Pend (labels := labels) (L := L) (caller := caller) (ps ++ lk) todo k →
    Returns (file := file) (labels := labels) (L := L) (caller := caller) Keeps ps
      ⟨.effectExpr e env, k, m⟩ t m.stdout
  | 0, _, _, _, _, _, h => by simp [run] at h
  | n + 1, ds, sz, e, todo, t, h => by
    intro env m inv hnext k p
    unfold run at h
    split at h
    next tr hc =>
      split at h
      next hd =>
        cases h
        obtain ⟨loc, hl, frames⟩ := StateProcLocal.context_frames p.context
        subst frames
        exact ret_keeps (labels := labels) hret hc inv hlk nodup hd.1 hnext hpk loc hl caller
      next => cases h
    split at h
    next tc ea eb hi =>
      split at h
      next hd =>
        split at h
        next a b ha hb =>
          split at h
          next =>
            cases h
            have okC := fun okc => StateExpr.close_ok (defsOf ds) tc (inv.defs_ok hd.1) okc
            rcases if_runs (labels := labels) hi inv hls hd.1 k with ub | ⟨okc, env', m', tch, inv', reach⟩
            · exact .inr ub
            · have same := same_touched tch
              have hnext' : ∀ l ∈ lk, l.id < m'.nextId := fun l hl => by rw [same.1]; exact hnext l hl
              by_cases h1 : tc.val (values (defsOf ds)) = 1
              · rw [ite_eq_left h1] at reach
                have o := run_returns hret hls hlk nodup hpk n ds sz eb todo hb env' m' inv' hnext' k p
                rw [tch.stdout] at o
                exact returns_choose_right (okC okc) (by rw [StateExpr.close_val]; exact h1)
                  (Returns.keep reach (keeps_same same) o)
              · rw [ite_eq_right h1] at reach
                have o := run_returns hret hls hlk nodup hpk n ds sz ea todo ha env' m' inv' hnext' k p
                rw [tch.stdout] at o
                exact returns_choose_left (okC okc) (by rw [StateExpr.close_val]; exact h1)
                  (Returns.keep reach (keeps_same same) o)
          next => cases h
        next => cases h
      next => cases h
    split at h
    next x tr ha =>
      split at h
      next hd =>
        split at h
        next => cases h
        next r todo' =>
          obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
          rw [State.update_key hx] at h
          rcases ParamAlloc.assign_runs_same ha inv hl hx hd.2.1 k with
            ub | ⟨_, m', out, same, inv', reach⟩
          · exact .inr ub
          · obtain ⟨env', k', henv, p', back⟩ := p.resume .unit none m' r todo' rfl
            have o := run_returns hret hls hlk nodup hpk n _ _ r todo' h env' m' (inv_withEnv inv' henv)
              (fun l hl => by rw [same.1]; exact hnext l hl) k' p'
            rw [out] at o
            exact Returns.keep (reach.trans back) (keeps_same same) o
      next => cases h
    split at h
    next x tr hi =>
      split at h
      next hd =>
        split at h
        next => cases h
        next r todo' =>
          obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
          rw [State.update_key hx] at h
          rcases init_keeps hi inv hl hx hd.2.1 k with ub | ⟨_, m', ys', out, same, inv', reach⟩
          · exact .inr ub
          · obtain ⟨env', k', henv, p', back⟩ := p.resume .unit (some ys') m' r todo' rfl
            have o := run_returns hret hls hlk nodup hpk n _ _ r todo' h env' m' (inv_withEnv inv' henv)
              (fun l hl => by rw [same.1]; exact hnext l hl) k' p'
            rw [out] at o
            exact Returns.keep (reach.trans back) (keeps_same same) o
      next => cases h
    split at h
    next x hu =>
      split at h
      next hd =>
        split at h
        next => cases h
        next r todo' =>
          obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd
          rw [State.update_key hx] at h
          obtain ⟨m', ys', out, same, inv', reach⟩ := uninit_keeps hu inv hl hx k
          obtain ⟨env', k', henv, p', back⟩ := p.resume .unit (some ys') m' r todo' rfl
          have o := run_returns hret hls hlk nodup hpk n _ _ r todo' h env' m' (inv_withEnv inv' henv)
            (fun l hl => by rw [same.1]; exact hnext l hl) k' p'
          rw [out] at o
          exact Returns.keep (reach.trans back) (keeps_same same) o
      next => cases h
    split at h
    next s rest hs =>
      obtain ⟨ann, pann, ty, rfl⟩ := seqParts_inv hs
      have o := run_returns hret hls hlk nodup hpk n ds sz s (rest :: todo) h env m inv hnext _
        (.bind pann ty rest inv.env p)
      exact Returns.keep (CallLocal.sequence ann _ s rest env k m) (Keeps.refl m) o
    split at h
    next hu =>
      obtain ⟨ann, pann, rfl⟩ := isUnit_inv hu
      split at h
      next => cases h
      next r todo' =>
        obtain ⟨env', k', henv, p', back⟩ := p.resume .unit none (focusMemory ann m) r todo' rfl
        have same := Rmw.same_focus ann m
        have o := run_returns hret hls hlk nodup hpk n ds sz r todo' h env' (focusMemory ann m)
          (inv_withEnv (inv.focus ann) henv) (fun l hl => by rw [same.1]; exact hnext l hl) k' p'
        rw [show (focusMemory ann m).stdout = m.stdout from
          (LoadTask.focusMemory_touched ann m).stdout] at o
        exact Returns.keep ((StateActionsLocal.pure_unit ann pann env k m).trans back)
          (keeps_same same) o
    next => cases h

/-- **The block**: the creations of at most `j` more `int` locals, then the statements. The
objects `pl ++ lk` are below the fresh id and at or above the last address; the reserve has room
for `j` more objects. -/
theorem block_returns {ret : Sym} (hret : ReturnLabel L ret) {ps : List Sym} {pl : List Local}
    (hpl : Keys pl ps) :
    (j : Nat) → (xs : List Sym) → (lk : List Local) → (ds : Key → Option IntExpr.Term) → (e : Eff) →
    {t : IntExpr.Term} → block file ret ps j xs ds e = some t →
    ∀ (env : Env) (m : Mem.Concrete.State), Inv env m (pl ++ lk) ds → Keys lk xs →
    (∀ l ∈ pl ++ lk, l.id < m.nextId) → (∀ l ∈ pl ++ lk, m.lastAddress ≤ l.addr) →
    m.lastAddress % 4 = 0 → 4 * ((j : Int) + 1) < m.lastAddress → (∀ d ∈ m.dead, d < m.nextId) →
    ∀ (k : List Frame), Context (labels := labels) L caller k →
    Returns (file := file) (labels := labels) (L := L) (caller := caller) (Uses j) pl
      ⟨.effectExpr e env, k, m⟩ t m.stdout := by
  intro j
  induction j with
  | zero =>
    intro xs lk ds e t h env m inv hlk ids addrs aligned room dead k hk
    simp only [block] at h
    split at h
    next => cases h
    next =>
      split at h
      next nodup =>
        have hls : Keys (pl ++ lk) (ps ++ xs) := by
          simp only [Keys, List.map_append] at hpl hlk ⊢; rw [hpl, hlk]
        have nodupx : (xs.map (·.key)).Nodup := (List.nodup_append.mp (by simpa using nodup)).2.1
        have hpk : ∀ p ∈ pl, ∀ l ∈ lk, p.id ≠ l.id := by
          intro p hp l hl
          refine (inv.apart p (List.mem_append_left _ hp) l (List.mem_append_right _ hl) ?_).1
          intro e
          have hp' : p.sym.key ∈ ps.map (·.key) := hpl ▸ List.mem_map_of_mem hp
          have hl' : l.sym.key ∈ xs.map (·.key) := hlk ▸ List.mem_map_of_mem hl
          rw [List.map_append] at nodup
          exact (List.nodup_append.mp nodup).2.2 _ hp' _ hl' e
        have o := run_returns (labels := labels) (L := L) (caller := caller) hret hls hlk nodupx hpk
          fuel ds _ e [] h env m inv (fun l hl => ids l (List.mem_append_right _ hl)) k (.base hk)
        exact o.pre .refl (fun _ h => Uses.of_keeps h)
      next => cases h
  | succ j ih =>
    intro xs lk ds e t h env m inv hlk ids addrs aligned room dead k hk
    simp only [block] at h
    split at h
    next x rest hc =>
      split at h
      next hfx =>
        unfold creation at hc
        split at hc
        next a p x' ty cr rest' =>
          split at hc
          next hcr =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨hx', hrest'⟩ := hc
            subst x' rest'
            obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := State.createInt_inv hcr
            have hnext : nextIntAddress m = m.lastAddress - 4 := by
              simp only [nextIntAddress]; omega
            have hpos : 0 < nextIntAddress m := by rw [hnext]; push_cast at room; omega
            let K := Frame.strongBind (.mk p (.base (some x, ty))) rest env :: k
            have create := StateActionsLocal.create (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
              pref env K m hpos
            rw [State.focus_nextId] at create
            let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
            let m₁ := Actions.created pref c2 (focusMemory ann m)
            let env₁ := extendEnv [(x, ptr nl)] env
            have bind := CallLocal.bind (file := file) (labels := labels) p x ty (ptr nl) rest env k m₁
            have hls : Keys (pl ++ lk) (ps ++ xs) := by
              simp only [Keys, List.map_append] at hpl hlk ⊢; rw [hpl, hlk]
            have fx : ∀ l ∈ pl ++ lk, l.sym.key ≠ x.key := hls.fresh hfx
            have inv₁ : Inv env₁ m₁ (pl ++ (lk ++ [nl])) ds := by
              rw [← List.append_assoc]
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro l hl y hy
                rcases List.mem_append.mp hl with hl | hl
                · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
                  exact inv.env l hl y hy
                · obtain rfl := List.mem_singleton.mp hl
                  exact ConvInt.lookup_one hy
              · intro l hl
                rcases List.mem_append.mp hl with hl | hl
                · refine StateMem.live_created (Locals.liveInt_focus ann (inv.live l hl)) pref c2 ?_
                  rw [State.focus_nextId]; exact Int.ne_of_lt (ids l hl)
                · obtain rfl := List.mem_singleton.mp hl
                  have := Locals.created_live pref c2 (focusMemory ann m)
                    (by
                      rw [State.focus_dead, State.focus_nextId]
                      intro hd
                      have := dead m.nextId hd
                      omega)
                  rwa [Locals.nextIntAddress_focus, State.focus_nextId] at this
              · intro a ha b hb ne
                rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
                · exact inv.apart a ha b hb ne
                · obtain rfl := List.mem_singleton.mp hb
                  refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
                  have := addrs a ha
                  show a.addr + 4 ≤ nextIntAddress m ∨ nextIntAddress m + 4 ≤ a.addr
                  omega
                · obtain rfl := List.mem_singleton.mp ha
                  refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
                  have := addrs b hb
                  show nextIntAddress m + 4 ≤ b.addr ∨ b.addr + 4 ≤ nextIntAddress m
                  omega
                · obtain rfl := List.mem_singleton.mp ha
                  obtain rfl := List.mem_singleton.mp hb
                  exact absurd rfl ne
              · intro q d hd
                obtain ⟨ok, l, hl, hq, slot⟩ := inv.defs q d hd
                refine ⟨ok, l, List.mem_append_left _ hl, hq, ?_⟩
                refine Slots.slot_created ((LoadTask.focusMemory_touched ann m).slot slot) pref c2
                  (by rw [State.focus_nextId]; exact Int.ne_of_lt (ids l hl)) ?_
                rw [Locals.nextIntAddress_focus]
                have := addrs l hl
                show nextIntAddress m + 4 ≤ l.addr ∨ l.addr + 4 ≤ nextIntAddress m
                omega
            have hlk₁ : Keys (lk ++ [nl]) (xs ++ [x]) := by
              simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hlk ⊢
              rw [hlk]
            have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
              rw [Locals.created_lastAddress, Locals.nextIntAddress_focus, hnext]
            have next₁ : m₁.nextId = m.nextId + 1 := by
              rw [State.created_nextId, State.focus_nextId]
            have dead₁ : m₁.dead = m.dead := by rw [Locals.created_dead, State.focus_dead]
            have o := ih (xs ++ [x]) (lk ++ [nl]) ds rest h env₁ m₁ inv₁ hlk₁
              (by
                intro l hl
                rw [next₁]
                rcases List.mem_append.mp hl with hl | hl
                · have := ids l (List.mem_append_left _ hl); omega
                · rcases List.mem_append.mp hl with hl | hl
                  · have := ids l (List.mem_append_right _ hl); omega
                  · obtain rfl := List.mem_singleton.mp hl
                    show m.nextId < m.nextId + 1
                    omega)
              (by
                intro l hl
                rw [last₁]
                rcases List.mem_append.mp hl with hl | hl
                · have := addrs l (List.mem_append_left _ hl); omega
                · rcases List.mem_append.mp hl with hl | hl
                  · have := addrs l (List.mem_append_right _ hl); omega
                  · obtain rfl := List.mem_singleton.mp hl
                    show m.lastAddress - 4 ≤ nextIntAddress m
                    omega)
              (by rw [last₁]; omega) (by rw [last₁]; push_cast at room ⊢; omega)
              (by intro d hd; rw [dead₁] at hd; rw [next₁]; have := dead d hd; omega) k hk
            have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
            rw [out] at o
            refine o.pre ((CallLocal.sequence a _ _ rest env k m).trans (create.trans bind)) ?_
            intro m' u'
            change Uses j m₁ m' at u'
            show Uses (j + 1) m m'
            refine ⟨by have := u'.next; rw [next₁] at this; omega,
              by have := u'.last; rw [last₁] at this; push_cast; omega,
              by rw [u'.aligned, last₁]; omega, fun d hd => ?_⟩
            rcases u'.dead d hd with h' | h'
            · exact .inl (dead₁ ▸ h')
            · exact .inr h'
          next => cases hc
        next => cases hc
      next => cases h
    next =>
      split at h
      next nodup =>
        have hls : Keys (pl ++ lk) (ps ++ xs) := by
          simp only [Keys, List.map_append] at hpl hlk ⊢; rw [hpl, hlk]
        have nodupx : (xs.map (·.key)).Nodup := (List.nodup_append.mp (by simpa using nodup)).2.1
        have hpk : ∀ p ∈ pl, ∀ l ∈ lk, p.id ≠ l.id := by
          intro p hp l hl
          refine (inv.apart p (List.mem_append_left _ hp) l (List.mem_append_right _ hl) ?_).1
          intro e
          have hp' : p.sym.key ∈ ps.map (·.key) := hpl ▸ List.mem_map_of_mem hp
          have hl' : l.sym.key ∈ xs.map (·.key) := hlk ▸ List.mem_map_of_mem hl
          rw [List.map_append] at nodup
          exact (List.nodup_append.mp nodup).2.2 _ hp' _ hl' e
        have o := run_returns (labels := labels) (L := L) (caller := caller) hret hls hlk nodupx hpk
          fuel ds _ e [] h env m inv (fun l hl => ids l (List.mem_append_right _ hl)) k (.base hk)
        exact o.pre .refl (fun _ h => Uses.of_keeps h)
      next => cases h

/-- The whole recognized parameter body, with an actual runtime input and room for `J` locals
below the argument object. -/
theorem body_returns {x : Sym} {e : EE} {t : IntExpr.Term} {J : Nat} (h : body file x e J = some t)
    (env : Env) (caller : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : IsInt n) (slot : Locals.Slot m id addr n)
    (hid : id < m.nextId) (haddr : m.lastAddress ≤ addr) (aligned : m.lastAddress % 4 = 0)
    (room : 4 * ((J : Int) + 1) < m.lastAddress) (dead : ∀ d ∈ m.dead, d < m.nextId) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ Uses J m m' ∧ LiveInt m' id addr ∧
      LocalReaches file labels false
        ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩
        ⟨.value (spec (t.val n)), .procedureReturn (CallReach.bodyLabels e) :: caller, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩ IntExpr.overflow := by
  unfold body at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      let B : EE := .mk ann (.sseq (.mk pann (.base (none, bt0))) a
        (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))))
      have hret : ReturnLabel (CallReach.bodyLabels B) ret := by
        refine ⟨r, bann, pann', r', hr, ?_⟩
        simp [B, CallReach.bodyLabels, saves, StmtIf.labelFree_saves a hfree, Map.ofList]
      have hs : block file ret [x] J [] (StateSubst.defs (.lit n) (StateParam.paramDefs x)) a =
          some (StateSubst.subst (.lit n) t) := by
        rw [block_subst, h]; rfl
      let SAVE : EE := .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
      let K := Frame.strongBind (.mk pann (.base (none, bt0))) SAVE env ::
        .procedureReturn (CallReach.bodyLabels B) :: caller
      have hK : Context (labels := labels) (CallReach.bodyLabels B) caller K := rfl
      have inv : Inv env m ([⟨x, id, addr⟩] ++ []) (StateSubst.defs (.lit n) (StateParam.paramDefs x)) := by
        simpa using (StateParam.param_at x env m hx hn slot).instantiate hn
      have result := block_returns (labels := labels) hret (ps := [x]) (pl := [⟨x, id, addr⟩]) rfl
        J [] [] _ a hs env m inv rfl
        (by intro l hl; simp only [List.append_nil, List.mem_singleton] at hl; subst hl; exact hid)
        (by intro l hl; simp only [List.append_nil, List.mem_singleton] at hl; subst hl; exact haddr)
        aligned room dead K hK
      have pre := CallLocal.sequence (file := file) (labels := labels) ann (.mk pann (.base (none, bt0))) a SAVE env
        (.procedureReturn (CallReach.bodyLabels B) :: caller) m
      rcases Returns.pre pre (fun _ h => h) result with ⟨ok, m', out, uses, live, run⟩ | fail
      · exact .inl ⟨(StateSubst.subst_ok (.lit n) t 0 hn).mp ok, m', out, uses,
          live ⟨x, id, addr⟩ (by simp), by simpa only [StateSubst.subst_val, IntExpr.Term.val] using run⟩
      · exact .inr fail
    · cases h
  · cases h

/-- Without locals (`J = 0`) a body needs no allocation reserve. -/
theorem body_returns' {x : Sym} {e : EE} {t : IntExpr.Term} (h : body file x e = some t)
    (env : Env) (caller : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : IsInt n) (slot : Locals.Slot m id addr n) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ LiveInt m' id addr ∧
      LocalReaches file labels false
        ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩
        ⟨.value (spec (t.val n)), .procedureReturn (CallReach.bodyLabels e) :: caller, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩ IntExpr.overflow := by
  unfold body at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      let B : EE := .mk ann (.sseq (.mk pann (.base (none, bt0))) a
        (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))))
      have hret : ReturnLabel (CallReach.bodyLabels B) ret := by
        refine ⟨r, bann, pann', r', hr, ?_⟩
        simp [B, CallReach.bodyLabels, saves, StmtIf.labelFree_saves a hfree, Map.ofList]
      have hb : block file ret [x] 0 [] (StateSubst.defs (.lit n) (StateParam.paramDefs x)) a =
          some (StateSubst.subst (.lit n) t) := by
        rw [block_subst, h]; rfl
      have hs : run file ret ([x] ++ []) [] fuel (StateSubst.defs (.lit n) (StateParam.paramDefs x))
          (fun _ => 1) a [] = some (StateSubst.subst (.lit n) t) := by
        simp only [block] at hb
        split at hb
        · cases hb
        · split at hb
          · exact hb
          · cases hb
      let SAVE : EE := .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
      let K := Frame.strongBind (.mk pann (.base (none, bt0))) SAVE env ::
        .procedureReturn (CallReach.bodyLabels B) :: caller
      have hK : Context (labels := labels) (CallReach.bodyLabels B) caller K := rfl
      have inv : Inv env m ([⟨x, id, addr⟩] ++ []) (StateSubst.defs (.lit n) (StateParam.paramDefs x)) := by
        simpa using (StateParam.param_at x env m hx hn slot).instantiate hn
      have result := run_returns (labels := labels) (L := CallReach.bodyLabels B) (caller := caller) hret
        (ps := [⟨x, id, addr⟩]) (lk := []) (ys := [x] ++ []) (xs := []) (by simp [Keys]) (by simp [Keys]) (by simp)
        (by simp) fuel _ _ a [] hs env m inv (by simp) K (.base hK)
      have pre := CallLocal.sequence (file := file) (labels := labels) ann (.mk pann (.base (none, bt0))) a SAVE env
        (.procedureReturn (CallReach.bodyLabels B) :: caller) m
      rcases Returns.pre pre (fun _ h => h) result with ⟨ok, m', out, -, live, run⟩ | fail
      · exact .inl ⟨(StateSubst.subst_ok (.lit n) t 0 hn).mp ok, m', out,
          live ⟨x, id, addr⟩ (by simp), by simpa only [StateSubst.subst_val, IntExpr.Term.val] using run⟩
      · exact .inr fail
    · cases h
  · cases h

/-- `StateParam.body_in_arena` for the wider recognizer. -/
theorem body_in_arena {x : Sym} {e : EE} {t : IntExpr.Term} (h : body file x e = some t)
    (env : Env) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : IsInt n) (slot : Locals.Slot m id addr n)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ LiveInt m' id addr ∧
      CoreReaches file labels
        ⟨.interleave done [(i, .effectExpr e env,
          [.procedureReturn (CallReach.bodyLabels e)])], k, m⟩
        ⟨.interleave ((i, spec (t.val n), []) :: done) [], k, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.interleave done [(i, .effectExpr e env,
        [.procedureReturn (CallReach.bodyLabels e)])], k, m⟩ IntExpr.overflow := by
  have pending : Pending [] i := ⟨by simp, by simp⟩
  rcases body_returns' (labels := labels) h env [] m hx hn slot with ⟨ok, m', out, live, run⟩ | fail
  · left
    refine ⟨ok, m', out, live, reaches_of_local file labels ?_⟩
    apply drive_task file labels pending
    refine ⟨[], ?_, rfl⟩
    have pop : LocalReaches file labels false
        ⟨.value (spec (t.val n)), [.procedureReturn (CallReach.bodyLabels e)], m'⟩
        ⟨.value (spec (t.val n)), [], m'⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (LoadTask.plain_value _))
    simpa [taskFlag] using run.trans pop
  · right
    apply ArenaFail.fail_task file labels pending
    simpa [taskFlag] using fail

end Silmaril.Compile.Core.Verified.ParamRun
