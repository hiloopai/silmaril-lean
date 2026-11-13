module

public import Silmaril.Compiler.Core.Verified.TyExpr.Defs
public import Silmaril.Compiler.Core.Verified.NegativeStore.Defs
public import Silmaril.Compiler.Core.Verified.StateStmt.Defs
/-! # The memory of several typed locals

`StateMem`, `StoreTask`, `Uninitialized` and the lifted store of `StateStmt` for locals of every
supported integer type. A `Local` records its symbol, allocation id, address and type.
`Inv env m ls ds`: each local of `ls` is pointed to by every symbol with its key and is a live
object of its type's width; locals have distinct keys, ids and disjoint byte ranges; and a local
whose key has a definition `ds q = some d` (the closed term it was last assigned) holds the value
`d.val zero`, a value of its type.

Stores: a positive typed store as a local task (`store_local`), the lifted negative store of an
assignment (`lifted_store`), the store of `Unspecified(T)` (`uninit_reaches`); a store into one
local updates exactly its definition (`Inv.store`, `Inv.uninit`). `Fresh`: the startup memory
with the locals created in order, at most `16` bytes each below `errno`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyMem

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches tagsOf)
open Silmaril.Cerberus.Core.PureEvalExt (Ev)
open Mem.Concrete (LiveSz tyType nextAddress)
open TyActions (supported width signed Fits TSlot stored)
open TyExpr (Key Term zero Loc Locs values)
open LoadTask (Touched)
open Slots (Apart)

variable {file : Program} {labels : Labels}

/-! ## Stores as tasks -/

/-- The access of a store of `w` bytes, including an enclosing lifted action's id. -/
def writeAccess (k : List Frame) (addr : Int) (w : Nat) : Access :=
  ⟨k.findSome? fun f => match f with | .excluded n => some n | _ => none, [], true, addr, w⟩

theorem requestAux_store_apply (ann : List Annot) {ity : IntegerType} (hs : supported ity = true)
    (k : List Frame) {m : Mem.Concrete.State} {id addr n : Int} (live : LiveSz m id addr (width ity))
    (hn : Fits ity n) :
    requestAux file labels m (.apply (.memory .store)
      [.ctype (tyType ann ity), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))]) k false =
      .memory "Store" (stored m id addr (width ity) n) (.value .unit)
        (.annotations [writeAccess k addr (width ity)] :: k) := by
  rw [requestAux.eq_def]
  simp [awaitsScheduling, memoryRequest, toMemory, objectMemory,
    Mem.Concrete.store_ty (TyActions.layout_of hs) _ ann live hn,
    Mem.Concrete.access_ty (TyActions.layout_of hs) _ ann live,
    bind, Except.bind, pure, Except.pure, stored, writeAccess]
  rfl

/-- A positive typed store with pure operands, as local steps. -/
theorem store_local (ann : List Annot) (l : Loc) (u : Unit) (ty p v : PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {ity : IntegerType} (hs : supported ity = true)
    {id addr n : Int} (live : LiveSz m id addr (width ity)) (hn : Fits ity n)
    (eval : Ev file (tagsOf file m) env (.inr [ty, p, v])
      (.inr [.ctype (tyType cann ity), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))])) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env, k, m⟩
      ⟨.value .unit, .annotations [writeAccess k addr (width ity)] :: k,
        stored (ReturnConst.focusMemory ann m) id addr (width ity) n⟩ := by
  have req : requestAux file labels m
      (.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env) k false =
      if (ReturnConst.focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr ty env) (.arguments (.memory .store) [] [p, v] env :: k)
      else .next (.setLocation (ReturnConst.focusMemory ann m).currentLocation (.pureExpr ty env))
        (.arguments (.memory .store) [] [p, v] env :: k) := by
    simp only [requestAux, awaitsScheduling, arguments]
    rfl
  have hf : LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env, k, m⟩
      ⟨.pureExpr ty env, .arguments (.memory .store) [] [p, v] env :: k,
        ReturnConst.focusMemory ann m⟩ := by
    obtain ⟨loc, hfocus⟩ := Locals.focusMemory_eq ann m
    rw [hfocus] at req ⊢
    by_cases same : loc == m.currentLocation
    · have eq : loc = m.currentLocation := by simpa using same
      subst loc
      simpa using Relation.ReflTransGen.single (Interleave.LocalStep.next
        (by simpa using req) (LoadTask.plain_pureExpr ty env))
    · exact .head (.next (by simpa [same] using req) (LoadTask.plain_setLocation _ _))
        (.single (.update (Interleave.requestAux_setLocation file labels m loc _ _ false)))
  have args := PureEvalExt.args_local file (tagsOf file m) (labels := labels) (wc := false) eval
    (.memory .store) [] k (ReturnConst.focusMemory ann m) (Locals.tagsOf_focus ann m)
  simp only [PureEval.argState, List.nil_append] at args
  exact hf.trans (args.tail (.memory
    (requestAux_store_apply cann hs k (TyActions.liveSz_focus ann live) hn)))

/-- No source location among the annotations. -/
abbrev noLoc := StateStmt.noLoc

/-- The lifted negative store of an assignment, for a typed local. -/
theorem lifted_store (sann : List Annot) (hann : noLoc sann = true) (l : Loc) (u : Unit)
    (ty p v : PE) (env : Env) (inner k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {ity : IntegerType} (hs : supported ity = true)
    {id addr n : Int} (live : LiveSz m id addr (width ity)) (hn : Fits ity n)
    (eval : ∀ m', Ev file (tagsOf file m') env (.inr [ty, p, v])
      (.inr [.ctype (tyType cann ity), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))]))
    (boundary : (inner ++ .bound :: k).span (fun f => match f with
      | .strongBind .. | .bound => false | _ => true) = (inner, .bound :: k))
    {result : Val} {xs : List Access} {m₂ : Mem.Concrete.State}
    (resume : TaskRuns file labels false
      ⟨.value .unit, excludeFrames m.nextExcluded inner,
        {m with nextExcluded := m.nextExcluded + 1}⟩ result xs m₂)
    (touched : Touched {m with nextExcluded := m.nextExcluded + 1} m₂)
    (excluded : ∀ a ∈ xs, m.nextExcluded ∈ a.exclusions)
    (idle : activeCall (.value .unit) (excludeFrames m.nextExcluded inner) = false) :
    Reaches file labels
      ⟨.effectExpr (.mk sann (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.value result, k, stored m₂ id addr (width ity) n⟩ := by
  have hno : ∀ a ∈ sann, ∀ l, a ≠ .loc l := by
    intro a ha l e; subst e
    have := List.all_eq_true.mp hann _ ha
    simp at this
  have hfind : (sann.findSome? fun a => match a with | .loc l => some l | _ => none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro a ha
    cases a <;> first | rfl | exact absurd rfl (hno _ ha _)
  let act : EE := .mk [] (.action (.mk .pos (.mk l u (.store false ty p v .na))))
  let m₁ : Mem.Concrete.State := {m with nextExcluded := m.nextExcluded + 1}
  let K := Frame.liftedResult :: .bound :: k
  let a := writeAccess [.excluded m.nextExcluded] addr (width ity)
  let tasks : List (Nat × (Control × List Frame)) :=
    [(0, .effectExpr act env, [.excluded m.nextExcluded]),
     (1, .value .unit, excludeFrames m.nextExcluded inner)]
  let results : List (Nat × (Val × List Access)) := [(0, .unit, [a]), (1, result, xs)]
  have live₂ : LiveSz m₂ id addr (width ity) := by
    obtain ⟨loc, used, eq⟩ := touched
    rw [eq]
    exact TyActions.liveSz_with live rfl rfl
  have store := store_local [] l u ty p v env [.excluded m.nextExcluded] m₂ cann hs
    live₂ hn (eval m₂) (labels := labels)
  have task0 : TaskRuns file labels false
      ⟨.effectExpr act env, [.excluded m.nextExcluded], m₂⟩ .unit [a]
        (stored m₂ id addr (width ity) n) := by
    refine ⟨[.annotations [a]], ?_, rfl⟩
    refine store.tail (.next ?_ (LoadTask.plain_value .unit))
    simp [requestAux, awaitsScheduling, a, ReturnConst.focusMemory]
  have flag0 : taskFlag false K [] = false := by simp [taskFlag]
  have flag1 : taskFlag false K [(0, .effectExpr act env, [.excluded m.nextExcluded])] = false := by
    simp [taskFlag, controlHasCCall, hasCCall, act]
  have run : TasksRun file labels false K tasks m₁ results (stored m₂ id addr (width ity) n) := by
    have r0 : TasksRun file labels false K [(0, .effectExpr act env, [.excluded m.nextExcluded])]
        m₂ [(0, .unit, [a])] (stored m₂ id addr (width ity) n) :=
      .snoc (by rw [flag0]; exact task0) .nil
    exact .snoc (by rw [flag1]; exact resume) r0
  have norace : NoRace results := by
    intro x hx y hy ne aa haa bb hbb
    simp only [results, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (ne rfl)
    · have eq : aa = a := by simpa using haa
      subst aa
      exact NegativeStore.excluded_noRace (by simp [a, writeAccess]) (excluded bb hbb)
    · have eq : bb = a := by simpa using hbb
      subst bb
      exact NegativeStore.excluded_noRace_rev (by simp [a, writeAccess]) (excluded aa haa)
    · exact False.elim (ne rfl)
  have sorted : results.Pairwise fun a b => a.1 ≤ b.1 := by simp [results]
  have arena := interleave_runs file labels run (by simp [tasks]) (by
    intro t ht
    simp only [tasks, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp [activeCall]
    · exact idle) []
  have end_ := LocalStep.next (requestAux_end file labels (stored m₂ id addr (width ity) n) results K
    false norace sorted) (LoadTask.plain_value _)
  have lift : liftAction m (.effectExpr act env) (Control.value .unit).resuming
      (inner ++ .bound :: k) = .update m₁ (.interleave [] tasks) K := by
    dsimp only [liftAction]
    erw [boundary]
    simp [excludePath, m₁, tasks, K]
  have start : Reaches file labels
      ⟨.effectExpr (.mk sann (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.interleave [] tasks, K, m₁⟩ := by
    apply ReturnConst.update_reaches
    · intro o h; cases h
    · simp only [act] at lift
      simp [request, requestAux, awaitsScheduling]
      erw [hfind]
      simp [lift]
  refine start.trans ?_
  have steps := arena.tail end_
  refine (reaches_of_local file labels steps).trans ?_
  have selected : Reaches file labels
      ⟨.value (.tuple [.unit, result]), .annotations (a :: xs) :: K, stored m₂ id addr (width ity) n⟩
      ⟨.value result, .annotations (a :: xs) :: .bound :: k, stored m₂ id addr (width ity) n⟩ :=
    next_reaches (by intro o h; cases h) (by
      simp [request, requestAux, awaitsScheduling, K])
  have finish := selected.trans
    (Locals.annotations_bound_reaches (a :: xs) result k (stored m₂ id addr (width ity) n))
  unfold PureEval.Reaches Spec.coreStep at finish
  simpa [results] using finish

/-! ## Unspecified stores -/

/-- The memory after the store of `Unspecified(T)` into the `w`-byte object at `addr`. -/
def unstored (m : Mem.Concrete.State) (id addr : Int) (w : Nat) : Mem.Concrete.State :=
  {Mem.Concrete.writeRepresentation addr
    (Mem.Concrete.plainBytes (List.replicate w none)) m with lastUsed := some id}

theorem unstored_stdout (m : Mem.Concrete.State) (id addr : Int) (w : Nat) :
    (unstored m id addr w).stdout = m.stdout := by
  simp [unstored, Actions.writeRepresentation_stdout]

theorem store_unspecified {ity : IntegerType} (hs : supported ity = true) (tags : Mem.Concrete.Tags)
    (ann vann : List Annot) {m : Mem.Concrete.State} {id addr : Int}
    (live : LiveSz m id addr (width ity)) :
    Mem.Concrete.storeTyped tags m (tyType ann ity) (.allocated id addr)
      (.unspecified (tyType vann ity)) = .ok ((addr, width ity), unstored m id addr (width ity)) := by
  obtain ⟨a, look, base, size, atomic, ro⟩ := live.found
  simp [Mem.Concrete.storeTyped, Mem.Concrete.access_ty (TyActions.layout_of hs) tags ann live,
    Mem.Concrete.checkWritable, look, ro, Mem.Concrete.represent,
    Mem.Concrete.layout_tyType (TyActions.layout_of hs), unstored, Mem.Concrete.plainBytes,
    bind, Except.bind, pure, Except.pure]

/-- The store of `Unspecified(T)` into a typed local. -/
theorem uninit_reaches (ann a1 c1 a2 a3 c3 : List Annot) (l : Loc) (u : Unit) (x : Sym)
    {ity : IntegerType} (hs : supported ity = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (live : LiveSz m id addr (width ity)) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.store false (TyActions.tyVal a1 c1 ity) (.mk a2 () (.sym x))
          (.mk a3 () (.val (.loaded (.unspecified (tyType c3 ity))))) .na))))) env, k, m⟩
      ⟨.value .unit, .annotations [writeAccess k addr (width ity)] :: k,
        unstored (ReturnConst.focusMemory ann m) id addr (width ity)⟩ := by
  have eval : PureEval.Eval file (tagsOf file m) env
      (.inr [TyActions.tyVal a1 c1 ity, .mk a2 () (.sym x),
        .mk a3 () (.val (.loaded (.unspecified (tyType c3 ity))))])
      (.inr [.ctype (tyType c1 ity), .object (.pointer (.allocated id addr)),
        .loaded (.unspecified (tyType c3 ity))]) :=
    .cons .val (.cons (.sym hx) (.cons .val .nil))
  refine (Locals.action_reaches Locals.request_store eval).trans ?_
  apply Actions.memory_reaches (name := "Store") (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory,
    store_unspecified hs _ c1 c3 (TyActions.liveSz_focus ann live),
    Mem.Concrete.access_ty (TyActions.layout_of hs) _ c1 (TyActions.liveSz_focus ann live),
    writeAccess, bind, Except.bind, pure, Except.pure]
  rfl

theorem live_unstored {m : Mem.Concrete.State} {id addr : Int} {v : Nat} (h : LiveSz m id addr v)
    (wid waddr : Int) (w : Nat) : LiveSz (unstored m wid waddr w) id addr v := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape waddr
    (Mem.Concrete.plainBytes (List.replicate w none)) m
  unfold unstored
  rw [hw]
  exact TyActions.liveSz_with h rfl rfl

theorem slot_unstored {m : Mem.Concrete.State} {id addr value : Int} {v : Nat}
    (h : TSlot m id addr v value) (wid waddr : Int) (w : Nat) (apart : Apart waddr w addr v) :
    TSlot (unstored m wid waddr w) id addr v value := by
  have len : (Mem.Concrete.plainBytes (List.replicate w none)).length = w := by
    simp [Mem.Concrete.plainBytes]
  refine ⟨live_unstored h.live _ _ _, ?_, ?_⟩
  · intro i hi
    change (Mem.Concrete.writeRepresentation waddr
      (Mem.Concrete.plainBytes (List.replicate w none)) m).pointerBytes.lookup (addr + i) = none
    rw [Slots.pointerByte_writeRepresentation _ waddr (addr + i) m (by
      rw [len]
      rcases apart with h | h
      · right; omega
      · left; omega)]
    exact h.plain i hi
  · change Mem.Concrete.fetchBytes v addr (Mem.Concrete.writeRepresentation waddr
      (Mem.Concrete.plainBytes (List.replicate w none)) m).bytes = _
    rw [Slots.fetchBytes_writeRepresentation _ waddr addr v m (by rwa [len])]
    exact h.bytes

/-! ## The invariant -/

/-- A source local: its symbol, allocation id, address and type. -/
structure Local where
  sym : Sym
  id : Int
  addr : Int
  ity : IntegerType

/-- The pointer to a local. -/
abbrev ptr (l : Local) : Dynamics.Val := .object (.pointer (.allocated l.id l.addr))

/-- The closed term of a key, `0` for a key without definition. -/
def defsOf (ds : Key → Option Term) : Key → Term := fun q => (ds q).getD (.lit 0)

/-- Every key a term reads has a definition. -/
def Defined (ds : Key → Option Term) (t : Term) : Bool := t.vars.all fun q => (ds q.1).isSome

/-- The definitions after assigning `d` to `q`. -/
def update (ds : Key → Option Term) (q : Key) (d : Option Term) : Key → Option Term :=
  fun q' => if q' = q then d else ds q'

/-- The environment and memory of the locals `ls` with definitions `ds`. -/
structure Inv (env : Env) (m : Mem.Concrete.State) (ls : List Local) (ds : Key → Option Term) :
    Prop where
  env : ∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)
  live : ∀ l ∈ ls, supported l.ity = true ∧ LiveSz m l.id l.addr (width l.ity)
  uniq : ∀ a ∈ ls, ∀ b ∈ ls, a.sym.key = b.sym.key → a = b
  apart : ∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key →
    a.id ≠ b.id ∧ Apart a.addr (width a.ity) b.addr (width b.ity)
  defs : ∀ q d, ds q = some d → d.Ok zero ∧ ∃ l ∈ ls, l.sym.key = q ∧
    Fits l.ity (d.val zero) ∧ TSlot m l.id l.addr (width l.ity) (d.val zero)

/-- Reads at the types of the locals. -/
def Typed (ls : List Local) (t : Term) : Prop :=
  ∀ q ∈ t.vars, ∃ l ∈ ls, l.sym.key = q.1 ∧ l.ity = q.2

theorem Inv.mono {env : Env} {m m' : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) (hs : ∀ id addr w n, TSlot m id addr w n → TSlot m' id addr w n)
    (hl : ∀ id addr w, LiveSz m id addr w → LiveSz m' id addr w) : Inv env m' ls ds where
  env := h.env
  live l hl' := ⟨(h.live l hl').1, hl _ _ _ (h.live l hl').2⟩
  uniq := h.uniq
  apart := h.apart
  defs q d hd := by
    obtain ⟨ok, l, hl', hk, hf, slot⟩ := h.defs q d hd
    exact ⟨ok, l, hl', hk, hf, hs _ _ _ _ slot⟩

theorem Inv.touched {env : Env} {m m' : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) (t : Touched m m') : Inv env m' ls ds :=
  h.mono (fun _ _ _ _ s => TyActions.Touched.slot t s) (fun _ _ _ lv => TyActions.Touched.live t lv)

theorem Inv.focus {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) (ann : List Annot) : Inv env (ReturnConst.focusMemory ann m) ls ds :=
  h.touched (LoadTask.focusMemory_touched ann m)

theorem Inv.nextExcluded {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option Term} (h : Inv env m ls ds) (n : Nat) :
    Inv env {m with nextExcluded := n} ls ds :=
  h.mono (fun _ _ _ _ s => TyActions.slot_nextExcluded s n)
    (fun _ _ _ lv => TyActions.liveSz_with lv rfl rfl)

theorem Inv.extend {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) {x : Sym} {v : Dynamics.Val} (fresh : ∀ l ∈ ls, l.sym.key ≠ x.key) :
    Inv (extendEnv [(x, v)] env) m ls ds where
  env l hl y hy := by
    rw [ConvInt.lookup_one_other (by rw [hy]; exact fresh l hl)]
    exact h.env l hl y hy
  live := h.live
  uniq := h.uniq
  apart := h.apart
  defs := h.defs

theorem Inv.locs {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) {t : Term} (hd : Defined ds t = true) (ht : Typed ls t) :
    Locs env m (values (defsOf ds)) t := by
  intro q hq
  have hs : (ds q.1).isSome = true := List.all_eq_true.mp hd q hq
  obtain ⟨d, hdq⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨ok, l, hl, hk, hf, slot⟩ := h.defs q.1 d hdq
  obtain ⟨l', hl', hk', hty⟩ := ht q hq
  have e : l' = l := h.uniq l' hl' l hl (hk'.trans hk.symm)
  subst e
  have hv : values (defsOf ds) q.1 = d.val zero := by simp [values, defsOf, hdq]
  rw [hv, ← hty]
  exact ⟨(h.live l' hl).1, hf, l'.id, l'.addr, fun y hy => h.env l' hl y (hy.trans hk.symm), slot⟩

theorem Inv.defs_ok {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) {t : Term} (hd : Defined ds t = true) :
    ∀ q ∈ t.vars, (defsOf ds q.1).Ok zero := by
  intro q hq
  have hs : (ds q.1).isSome = true := List.all_eq_true.mp hd q hq
  obtain ⟨d, hdq⟩ := Option.isSome_iff_exists.mp hs
  simpa [defsOf, hdq] using (h.defs q.1 d hdq).1

theorem Inv.lookup {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) {l : Local} (hl : l ∈ ls) {y : Sym} (hy : y.key = l.sym.key) :
    env.lookup y = some (ptr l) :=
  h.env l hl y hy

/-- **A store into one local** updates exactly its definition. -/
theorem Inv.store {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) {l : Local} (hl : l ∈ ls) {d : Term} (ok : d.Ok zero)
    (hf : Fits l.ity (d.val zero)) :
    Inv env (stored m l.id l.addr (width l.ity) (d.val zero)) ls (update ds l.sym.key (some d)) where
  env := h.env
  live l' hl' := ⟨(h.live l' hl').1, TyActions.live_stored (h.live l' hl').2 _ _ _ _⟩
  uniq := h.uniq
  apart := h.apart
  defs q d' hd := by
    unfold update at hd
    split at hd
    · rename_i hq
      cases hd
      exact ⟨ok, l, hl, hq.symm, hf, TyActions.stored_slot (h.live l hl).2 _⟩
    · rename_i hq
      obtain ⟨ok', l', hl', hk, hf', slot⟩ := h.defs q d' hd
      have ne : l.sym.key ≠ l'.sym.key := fun e => hq (hk.symm.trans e.symm)
      exact ⟨ok', l', hl', hk, hf', TyActions.slot_stored slot _ _ _ _ (h.apart l hl l' hl' ne).2⟩

/-- **An unspecified store** removes exactly the local's definition. -/
theorem Inv.uninit {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (h : Inv env m ls ds) {l : Local} (hl : l ∈ ls) :
    Inv env (unstored m l.id l.addr (width l.ity)) ls (update ds l.sym.key none) where
  env := h.env
  live l' hl' := ⟨(h.live l' hl').1, live_unstored (h.live l' hl').2 _ _ _⟩
  uniq := h.uniq
  apart := h.apart
  defs q d' hd := by
    unfold update at hd
    split at hd
    · cases hd
    · rename_i hq
      obtain ⟨ok', l', hl', hk, hf', slot⟩ := h.defs q d' hd
      have ne : l.sym.key ≠ l'.sym.key := fun e => hq (hk.symm.trans e.symm)
      exact ⟨ok', l', hl', hk, hf', slot_unstored slot _ _ _ (h.apart l hl l' hl' ne).2⟩

/-! ## Creation -/

/-- The startup memory with the locals `ls` created in order: nothing died, ids below the next
one, every local at or above the last address, which is at most `16` bytes per local below
`errno`. -/
structure Fresh (m : Mem.Concrete.State) (ls : List Local) : Prop where
  dead : m.dead = []
  ids : ∀ l ∈ ls, l.id < m.nextId
  addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr
  last : StartupReach.errnoAddr - 16 * ls.length ≤ m.lastAddress

end Silmaril.Compile.Core.Verified.TyMem
