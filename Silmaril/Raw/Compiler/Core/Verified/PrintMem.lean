module

public import Silmaril.Compiler.Core.Verified.StateExitMem.Defs
public import Silmaril.Compiler.Core.Verified.PrintfState.Defs
/-! # Memory through the statements of the print machine

The print machine (`PrintState`) runs `StateGlobals`' statements among `printf` calls, after the
startup allocated the program's string literals. A `printf` reads its format from the literal's
object, so the statements must keep the literals' objects: a store writes a slot of a local,
below every literal (`Above`), and keeps every byte above it.

`Closed P ls` names the memory changes of the statements (touching the location, a fresh
exclusion identifier, a store or an unspecified store at a slot of `ls`); the statement lemmas
are those of `StateExitMem` for any `P` closed under them (`StateExitMem` is the instance for the
exit budget). `Facts` is the instance of the print machine: the dead allocations below the next
identifier, the locals before the frontier, the literal objects (`MemOk`) and a lower bound of
the frontier, the room of the next `printf`s.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.PrintMem

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval Reaches tagsOf)
open Mem.Concrete (LiveInt IntRange)
open Locals (stored Slot)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open ConvInt (IsInt)
open StateExpr (Key Term term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt
open StateGlobals (ifParts ifParts_inv exprStmt)
open IntExpr (spec)
open LoadTask (Touched)
open StrMem (StrObj Keeps)

/-! ## Memory changes of the statements -/

/-- `P` holds after the memory changes of the statements over the slots `ls`. -/
structure Closed (P : Mem.Concrete.State → Prop) (ls : List Local) : Prop where
  touched : ∀ {m m' : Mem.Concrete.State}, P m → Touched m m' → P m'
  excluded : ∀ {m : Mem.Concrete.State} (n : Nat), P m → P {m with nextExcluded := n}
  stored : ∀ {m : Mem.Concrete.State} {l : Local} (v : Int), l ∈ ls → P m → P (stored m l.id l.addr v)
  unstored : ∀ {m : Mem.Concrete.State} {l : Local}, l ∈ ls → P m →
    P (Uninitialized.stored m l.id l.addr)

theorem Closed.focus {P : Mem.Concrete.State → Prop} {ls : List Local} (cl : Closed P ls)
    {m : Mem.Concrete.State} (ann : List Annot) (h : P m) : P (focusMemory ann m) :=
  cl.touched h (LoadTask.focusMemory_touched ann m)

/-- The two binders of an `if` statement's test (`ifParts`). -/
def ifBinders : Eff → Option (Sym × Sym)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) _ (.mk _ (.sseq (.mk _ (.base (some b, _))) _ _))) =>
    some (c, b)
  | _ => none

/-! ## String literals above the slots -/

/-- A string literal object of the startup: its symbol, characters, identifier and address. -/
structure Lit where
  sym : Sym
  cs : List Int
  id : Int
  addr : Int

/-- The literals as `printf`'s recognisers take them. -/
def lits (L : List Lit) : List (Sym × List Int) := L.map fun o => (o.sym, o.cs)

/-- The environment binds each literal's symbol to its object. -/
def LookOk (L : List Lit) (env : Env) : Prop :=
  ∀ o ∈ L, env.lookup o.sym = some (.object (.pointer (.allocated o.id o.addr)))

/-- The memory holds each literal's object. -/
def MemOk (L : List Lit) (m : Mem.Concrete.State) : Prop :=
  ∀ o ∈ L, StrObj m o.id o.addr o.cs ∧ 0 < o.addr ∧ o.addr < 2 ^ 48

/-- Every literal lies above every slot. -/
def Above (L : List Lit) (ls : List Local) : Prop := ∀ o ∈ L, ∀ l ∈ ls, l.addr + 4 ≤ o.addr

theorem litEnv {L : List Lit} {env : Env} {m : Mem.Concrete.State} (hl : LookOk L env)
    (hm : MemOk L m) : StrLit.LitEnv (lits L) env m := by
  intro x cs hx
  obtain ⟨o, ho, he⟩ := List.mem_map.mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨obj, h0, h1⟩ := hm o ho
  exact ⟨o.id, o.addr, hl o ho, obj, h0, h1⟩

theorem of_litEnv {env : Env} {m : Mem.Concrete.State} : ∀ (ls : List (Sym × List Int)),
    StrLit.LitEnv ls env m → ∃ L, lits L = ls ∧ LookOk L env ∧ MemOk L m
  | [], _ => ⟨[], rfl, by simp [LookOk], by simp [MemOk]⟩
  | (x, cs) :: ls, h => by
    obtain ⟨id, addr, look, obj, h0, h1⟩ := h x cs List.mem_cons_self
    obtain ⟨L, hL, hl, hm⟩ := of_litEnv ls (fun y c hy => h y c (List.mem_cons_of_mem _ hy))
    refine ⟨⟨x, cs, id, addr⟩ :: L, by simp [lits, ← hL], ?_, ?_⟩
    · intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact look
      · exact hl o ho
    · intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact ⟨obj, h0, h1⟩
      · exact hm o ho

theorem LookOk.extend {L : List Lit} {env : Env} (h : LookOk L env) {x : Sym}
    (hx : ∀ o ∈ L, o.sym.key ≠ x.key) (v : Val) : LookOk L (extendEnv [(x, v)] env) := by
  intro o ho
  rw [ConvInt.lookup_one_other (hx o ho)]
  exact h o ho

theorem strObj_write {m : Mem.Concrete.State} {id addr : Int} {cs : List Int}
    (h : StrObj m id addr cs) (a : Int) (bs : Mem.Concrete.Representation)
    (hd : a + bs.length ≤ addr) : StrObj (Mem.Concrete.writeRepresentation a bs m) id addr cs := by
  have hw := Mem.Concrete.writeRepresentation_allocations a bs m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw.2.1]; exact h.alive
  · rw [hw.1]; exact h.alloc
  · intro i hi
    have := h.bytes i hi
    unfold Mem.Concrete.readByte at this ⊢
    rw [StrMem.bytes_write_outside _ _ _ _ (.inr (by omega))]
    exact this
  · intro i hi
    rw [Slots.pointerByte_writeRepresentation _ _ _ _ (.inr (by omega))]
    exact h.plain i hi
  · rw [StrMem.wr_nextId]; exact h.below
  · rw [StrMem.wr_lastAddress]; exact h.above

/-- What the print machine keeps through its statements. -/
structure Facts (L : List Lit) (ls : List Local) (R : Int) (m : Mem.Concrete.State) : Prop where
  dead : PrintfStmt.DeadBelow m
  earlier : PrintfState.Earlier m ls
  lits : MemOk L m
  above : Above L ls
  room : R ≤ m.lastAddress

theorem Facts.of {L : List Lit} {ls : List Local} {R : Int} {m m' : Mem.Concrete.State}
    (f : Facts L ls R m) (n : m'.nextId = m.nextId) (d : m'.dead = m.dead)
    (la : m'.lastAddress = m.lastAddress) (hl : MemOk L m') : Facts L ls R m' :=
  ⟨fun j hj => by rw [n]; rw [d] at hj; exact f.dead j hj,
    ⟨fun l hl => by rw [n]; exact f.earlier.ids l hl, fun l hl => by rw [la]; exact f.earlier.addrs l hl⟩,
    hl, f.above, by rw [la]; exact f.room⟩

theorem Facts.write {L : List Lit} {ls : List Local} {R : Int} {m : Mem.Concrete.State}
    (f : Facts L ls R m) {l : Local} (hl : l ∈ ls) (bs : Mem.Concrete.Representation)
    (hlen : bs.length = 4) : Facts L ls R (Mem.Concrete.writeRepresentation l.addr bs m) := by
  have hw := Mem.Concrete.writeRepresentation_allocations l.addr bs m
  refine f.of (StrMem.wr_nextId _ _ _) hw.2.1 (StrMem.wr_lastAddress _ _ _) ?_
  intro o ho
  obtain ⟨obj, h0, h1⟩ := f.lits o ho
  exact ⟨strObj_write obj _ _ (by rw [hlen]; exact f.above o ho l hl), h0, h1⟩

theorem strObj_same {m m' : Mem.Concrete.State} {id addr : Int} {cs : List Int}
    (h : StrObj m id addr cs) (d : m'.dead = m.dead) (a : m'.allocations = m.allocations)
    (b : m'.bytes = m.bytes) (p : m'.pointerBytes = m.pointerBytes) (n : m'.nextId = m.nextId)
    (la : m'.lastAddress = m.lastAddress) : StrObj m' id addr cs :=
  ⟨by rw [d]; exact h.alive, by rw [a]; exact h.alloc, by rw [b]; exact h.bytes,
    by rw [p]; exact h.plain, by rw [n]; exact h.below, by rw [la]; exact h.above⟩

theorem Facts.same {L : List Lit} {ls : List Local} {R : Int} {m m' : Mem.Concrete.State}
    (f : Facts L ls R m) (d : m'.dead = m.dead) (a : m'.allocations = m.allocations)
    (b : m'.bytes = m.bytes) (p : m'.pointerBytes = m.pointerBytes) (n : m'.nextId = m.nextId)
    (la : m'.lastAddress = m.lastAddress) : Facts L ls R m' :=
  f.of n d la fun o ho => ⟨strObj_same (f.lits o ho).1 d a b p n la, (f.lits o ho).2⟩

theorem facts_closed (L : List Lit) (ls : List Local) (R : Int) : Closed (Facts L ls R) ls where
  touched := by
    intro m m' f t
    obtain ⟨l, u, rfl⟩ := t
    exact f.same rfl rfl rfl rfl rfl rfl
  excluded := by
    intro m n f
    exact f.same rfl rfl rfl rfl rfl rfl
  stored := by
    intro m l v hl f
    exact (f.write hl (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 v))
      (by simp [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length])).same rfl rfl rfl rfl rfl rfl
  unstored := by
    intro m l hl f
    exact (f.write hl (Mem.Concrete.plainBytes (List.replicate 4 none))
      (by simp [Mem.Concrete.plainBytes])).same rfl rfl rfl rfl rfl rfl

theorem Facts.mono {L : List Lit} {ls : List Local} {R R' : Int} {m : Mem.Concrete.State}
    (f : Facts L ls R m) (h : R' ≤ R) : Facts L ls R' m :=
  ⟨f.dead, f.earlier, f.lits, f.above, le_trans h f.room⟩

theorem Facts.keeps {L : List Lit} {ls : List Local} {R : Int} {m m' : Mem.Concrete.State}
    (f : Facts L ls R m) (k : Keeps m m') (dead : PrintfStmt.DeadBelow m') {R' : Int}
    (room : R' ≤ m'.lastAddress) : Facts L ls R' m' :=
  ⟨dead, f.earlier.keeps k, fun o ho => ⟨(f.lits o ho).1.keeps k, (f.lits o ho).2⟩, f.above, room⟩

/-! ## The statements, for any closed `P` -/

variable {file : Program} {labels : Labels} {P : Mem.Concrete.State → Prop}

theorem assign_runs {e : Eff} {x : Sym} {t : Term} (h : assignStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) (cl : Closed P ls) (hb : P m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        P m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  obtain ⟨a0, a1, ty0, a2, a3, a4, a5, p, tp, a6, t₀, tt, a7, PX, e', b0, b1, ty1, sann, lc, u,
    b2, c1, b3, p', b4, s, b5, c2, b6, t', b7, b8, s', b9, c3, d0, t'', d1, d2, rfl, hp', ht', ht'',
    htp, hann, hs, hs', he, hdx, hnx⟩ := assignStmt_inv h
  replace hdx : IntWrap.desig file PX = some x :=
    (StateStmt.desigP_inv hdx).resolve_right (by rintro ⟨_, _, h⟩; simp at h)
  let σ := values (defsOf ds)
  let PU : EE := .mk d1 (.pure (.mk d2 () (.val .unit)))
  let K0 := Frame.strongBind (.mk a1 (.base (none, ty0))) PU env :: k
  let PAT : Pattern Sym := .mk a4 (.ctor .tuple [.mk a5 (.base (some p, tp)), .mk a6 (.base (some t₀, tt))])
  let CONV : PE := .mk b8 () (.call (.sym s') [Locals.intVal b9 c3, .mk d0 () (.sym t'')])
  let NEG : EE := .mk sann (.action (.mk .neg (.mk lc u (.store false (Locals.intVal b2 c1)
    (.mk b3 () (.sym p')) (.mk b4 () (.call (.sym s) [Locals.intVal b5 c2, .mk b6 () (.sym t')])) .na))))
  let BODY : EE := .mk b0 (.wseq (.mk b1 (.base (none, ty1))) NEG (.mk b7 (.pure CONV)))
  let KB := Frame.effectBind PAT BODY env :: .bound :: K0
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (none, ty0)))
      (.mk a2 (.bound (.mk a3 (.wseq PAT (.mk a7 (.unseq [PX, e'])) BODY)))) PU)) env, k, m⟩
      ⟨.effectExpr (.mk a7 (.unseq [PX, e'])) env, KB, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      ((ReturnLit.bound_reaches a2 _ env _ m).trans (Locals.wseq_reaches a3 PAT _ BODY env _ m))
  have locs := inv.locs hd
  have hpx : env.lookup x = some (ptr l) := inv.lookup hl hx
  by_cases ok : t.Ok σ
  · right
    refine ⟨ok, ?_⟩
    let I : Mem.Concrete.State → Prop := fun m => StateExpr.Locs env m σ t
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    obtain ⟨xs, m₁, -, tch, s₂⟩ := IntExpr.unseq_pair (file := file) (labels := labels) (k := KB)
      (annots := a7) I hI (IntWrap.desig_readTask I hdx hpx)
      (StateExpr.term_task t he ok I fun _ hm => hm)
      (by intro eq; rw [← eq, hnx] at he; cases he) m locs
    let v := t.val σ
    have hv : IsInt v := StateExpr.Term.int_of_ok t ok
    let env₁ := extendEnv [(p, ptr l), (t₀, spec v)] env
    have s₃ : Reaches file labels ⟨.value (.tuple [ptr l, spec v]), .annotations xs :: KB, m₁⟩
        ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩ :=
      Interleave.reaches_of_local file labels (.single (.next
        (IntExpr.requestAux_tuple_bind m₁ xs a4 a5 a6 p t₀ tp tt _ _ _ env _)
        (LoadTask.plain_effectExpr _ _)))
    let inner := [Frame.effectBind (.mk b1 (.base (none, ty1))) (.mk b7 (.pure CONV)) env₁,
      .annotations xs]
    have s₄ : Reaches file labels ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩
        ⟨.effectExpr NEG env₁, inner ++ .bound :: K0, m₁⟩ :=
      Locals.wseq_reaches b0 _ NEG _ env₁ _ m₁
    have ht₁ : env₁.lookup t'' = some (spec v) := lookup_two_snd ht'' htp
    obtain ⟨m₂, tch₂, resume⟩ := assign_resume (file := file) (labels := labels) b1 ty1 b7 b8 b9 c3 d0
      s' t'' env₁ xs m₁.nextExcluded {m₁ with nextExcluded := m₁.nextExcluded + 1} hv hs' ht₁
    have inv₁ : Inv env m₁ ls ds := inv.touched tch
    have live₁ : LiveInt m₁ l.id l.addr := inv₁.live l hl
    have s₅ := lifted_store_ann (file := file) (labels := labels) sann hann lc u (Locals.intVal b2 c1)
      (.mk b3 () (.sym p')) (.mk b4 () (.call (.sym s) [Locals.intVal b5 c2, .mk b6 () (.sym t')]))
      env₁ inner K0 m₁ c1 live₁ hv
      (fun m' => .cons (Locals.eval_intVal _ env₁ b2 c1) (.cons (.sym (lookup_two_fst hp'))
        (.cons (ConvInt.convLoadedInt_eval (ann := c2) hs hv
          (.cons (Locals.eval_intVal _ env₁ b5 c2) (.cons (.sym (lookup_two_snd ht' htp)) .nil))) .nil)))
      (by simp [inner, List.span, List.span.loop]) resume tch₂
      (by intro a ha; obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha; simp)
      (by simp [activeCall, excludeFrames, inner])
    let m₃ := stored m₂ l.id l.addr v
    have inv₃ : Inv env m₃ ls (update ds l.sym.key (some (close (defsOf ds) t))) := by
      have i₂ : Inv env m₂ ls ds := (inv₁.nextExcluded _).touched tch₂
      have := i₂.store hl (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
      rwa [StateExpr.close_val] at this
    refine ⟨focusMemory d1 m₃, ?_, inv₃.focus d1, cl.focus d1 (cl.stored _ hl (cl.touched (cl.excluded _ (cl.touched hb tch)) tch₂)), ?_⟩
    · simp [m₃, Locals.stored_stdout, tch₂.stdout, tch.stdout]
    · exact pre.trans ((Interleave.reaches_of_local file labels s₂).trans (s₃.trans (s₄.trans
        (s₅.trans ((ReturnConst.wildcard_sequence_reaches file labels a1 ty0 _ PU env k m₃).trans
          (pure_unit_reaches d1 d2 env k m₃))))))
  · left
    refine Overflows.pre pre (fails_overflows (ArenaFail.fail_pair file labels (.inl ?_)))
    have flag : taskFlag false KB [(0, .effectExpr PX env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, IntWrap.desig_noCall hdx]
    rw [flag]
    exact StateExpr.term_fails t he ok [] m locs


theorem init_runs {e : Eff} {x : Sym} {t : Term} (h : initStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) (cl : Closed P ls) (hb : P m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m' xs, m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        P m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, a1, t₀, ty, a2, e', a3, lc, u, b1, c1, b2, b3, b4, c3, b5, s, t', rfl, ht', htx, hs,
    he⟩ := initStmt_inv h
  let σ := values (defsOf ds)
  let ST : EE := .mk a3 (.action (.mk .pos (.mk lc u (.store false (Locals.intVal b1 c1)
    (.mk b2 () (.sym x)) (.mk b3 () (.call (.sym s) [Locals.intVal b4 c3, .mk b5 () (.sym t')])) .na))))
  let K := Frame.strongBind (.mk a1 (.base (some t₀, ty))) ST env :: k
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some t₀, ty)))
      (.mk a2 (.bound e')) ST)) env, k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
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
    obtain ⟨ys, hst⟩ := Locals.store_reaches (file := file) (labels := labels) a3 b1 b2 b3 b4 b5 c1 c3
      lc u x s t' hs env₁ k m₁ hx₁ (ConvInt.lookup_one ht') hv (inv₁.live l hl)
    have inv₂ := (inv₁.focus a3).store hl (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
    rw [StateExpr.close_val] at inv₂
    refine ⟨_, ys, ?_, inv₂, cl.stored _ hl (cl.focus a3 (cl.touched hb tch)), ?_⟩
    · simp [Locals.stored_stdout, tch.stdout]
    · exact pre.trans ((Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 t₀ ty _ ST env k m₁).trans hst)))
  · left
    exact Overflows.pre pre (fails_overflows (StateExpr.term_fails (file := file) (labels := labels)
      t he ok (.bound :: K) m locs))

theorem uninit_runs {e : Eff} {x : Sym} (h : uninitStmt e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame) (cl : Closed P ls) (hb : P m) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls (update ds l.sym.key none) ∧
      P m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, c1, b2, b3, c3, rfl⟩ := uninitStmt_inv h
  refine ⟨_, _, ?_, (inv.focus a0).uninit hl, cl.unstored hl (cl.focus a0 hb), Uninitialized.store_reaches (file := file)
    (labels := labels) a0 b1 c1 b2 b3 c3 lc u x env k m (inv.lookup hl hx) (inv.live l hl)⟩
  simp [Uninitialized.stored_stdout]

theorem uninitAny_runs {e : Eff} {x : Sym} (h : uninitAny file e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame) (cl : Closed P ls) (hb : P m) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls (update ds l.sym.key none) ∧
      P m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  unfold uninitAny at h
  split at h
  · rename_i x' hu
    cases h
    exact uninit_runs hu inv hl hx k cl hb
  · obtain ⟨ann, reach⟩ := WrapObj.uninitWrap_reaches (file := file) (labels := labels) h env k m
      (inv.lookup hl hx) (inv.live l hl)
    exact ⟨_, _, by simp [Uninitialized.stored_stdout], (inv.focus ann).uninit hl,
      cl.unstored hl (cl.focus ann hb), reach⟩

theorem if_runs {ys : List Sym} {e ea eb : Eff} {tc : Term} (h : ifParts file ys e = some (tc, ea, eb))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (hls : Keys ls ys) (hdc : Defined ds tc = true) (k : List Frame) (cl : Closed P ls) (hb : P m)
    {c₀ b₀ : Sym} (hbs : ifBinders e = some (c₀, b₀)) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    (tc.Ok (values (defsOf ds)) ∧ ∃ env' m', m'.stdout = m.stdout ∧ Inv env' m' ls ds ∧ P m' ∧
      (∀ y : Sym, y.key ≠ c₀.key → y.key ≠ b₀.key → env'.lookup y = env.lookup y) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.effectExpr (if tc.val (values (defsOf ds)) = 1 then eb else ea) env', k, m'⟩) := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, hb', hcb, hfc, hfb, htc⟩ :=
    ifParts_inv h
  replace htc : StateExpr.term file ec = some tc := htc.2.2
  have hcb' : (some (c, b) : Option (Sym × Sym)) = some (c₀, b₀) := hbs
  simp only [Option.some.injEq, Prod.mk.injEq] at hcb'
  obtain ⟨rfl, rfl⟩ := hcb'
  let σ := values (defsOf ds)
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea eb)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  by_cases okc : tc.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc)
    let cv := tc.val σ
    let env₁ := extendEnv [(c, spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cv
      (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    let m₃ := SeqReach.focusMemory a5 m₂
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then ea else eb) env₂, k, m₃⟩ :=
      (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have tch₃ : Touched m m₃ := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    have inv₂ : Inv env₂ m₃ ls ds := ((inv.touched tch₃).extend (hls.fresh hfc)).extend (hls.fresh hfb)
    refine ⟨okc, env₂, m₃, tch₃.stdout, inv₂, cl.touched hb tch₃, fun y hc hb => by
      rw [ConvInt.lookup_one_other hb, ConvInt.lookup_one_other hc], pre.trans ?_⟩
    have hsel : (if flag then ea else eb) = (if tc.val σ = 1 then eb else ea) := by
      by_cases h1 : tc.val σ = 1 <;> simp [flag, cv, h1]
    rw [← hsel]
    exact enter
  · left
    exact StateStmt.Overflows.pre pre (fails_overflows (StateExpr.term_fails (file := file)
      (labels := labels) tc htc okc (.bound :: K) m (inv.locs hdc)))

end Silmaril.Compile.Core.Verified.PrintMem
