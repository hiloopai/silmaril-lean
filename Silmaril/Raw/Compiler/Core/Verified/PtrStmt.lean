module

public import Silmaril.Compiler.Core.Verified.StateStmt.Defs
public import Silmaril.Compiler.Core.Verified.PrintfStmt.Defs

/-! # Pointer locals: their stores and the memory invariant

A pointer local `int *p` is an 8-byte object (`StrMem.PtrSlot`). The statement machine knows
statically what it holds (`StateExpr.PtsTo`, the map `pts`); `StateMem.Inv`'s pointer part
(`StateMem.PInv`) relates that to the Core memory.

* `storePtr_local`: a positive store of the pointer `allocated pid paddr` into `p`'s object, as
  local steps with one write access (`PrintfStmt.storedPtr`).
* `lifted_store_gen`: `NegativeStore.lifted_store` for any positive store that runs locally
  with one write access tagged by the fresh exclusion id (the assignment `p = &x` lifts a
  pointer store).
* `Inv.ptrStore`: storing the pointer to the `int` local `lq` into the pointer local `l` keeps
  every `int` slot and every other pointer object, and gives `l` the target `lq`;
  `Inv.ptrUninit`: the unspecified store of a declaration removes `l`'s target.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PtrStmt

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval Reaches next_reaches tagsOf argState)
open Mem.Concrete (LiveInt IntRange)
open Locals (Slot)
open StateExpr (Key PtsTo)
open StateMem (Local Inv PInv Holds PFrame ptr)
open LoadTask (plain_value plain_apply plain_pureExpr)
open ReturnLit (Eff)

/-- `pts` with `r`'s target replaced by `t`. -/
def updateP (pts : Key → Option PtsTo) (r : Key) (t : Option PtsTo) : Key → Option PtsTo :=
  fun r' => if r' = r then t else pts r'

/-- A pointer to `int`, with any annotations and qualifiers. -/
abbrev intPtr (ann : List Annot) (q : Qualifiers) (ann' : List Annot) : Ctype :=
  .mk ann (.pointer q (.mk ann' (.basic (.integer (.signed .int)))))

/-! ## Byte frames of a write -/

/-- An `int` slot apart from a representation write keeps its value. -/
theorem slot_write {m : Mem.Concrete.State} {id addr value : Int} (h : Slot m id addr value)
    (a : Int) (bs : Mem.Concrete.Representation) (u : Option Int)
    (apart : Slots.Apart a bs.length addr 4) :
    Slot {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} id addr value := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape a bs m
    change LiveInt {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} id addr
    rw [hw]
    exact Locals.liveInt_with h.live rfl rfl
  · intro i hi
    change (Mem.Concrete.writeRepresentation a bs m).pointerBytes.lookup (addr + i) = none
    rw [Slots.pointerByte_writeRepresentation _ a (addr + i) m (by
      rcases apart with h | h
      · right; omega
      · left; omega)]
    exact h.plain i hi
  · change Mem.Concrete.fetchBytes 4 addr (Mem.Concrete.writeRepresentation a bs m).bytes = _
    rw [Slots.fetchBytes_writeRepresentation _ a addr 4 m apart]
    exact h.bytes

theorem live_write {m : Mem.Concrete.State} {id addr : Int} (h : LiveInt m id addr)
    (a : Int) (bs : Mem.Concrete.Representation) (u : Option Int) :
    LiveInt {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} id addr := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape a bs m
  change LiveInt {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} id addr
  rw [hw]
  exact Locals.liveInt_with h rfl rfl

/-- A pointer object apart from a representation write keeps what it holds. -/
theorem ptrObj_write {m : Mem.Concrete.State} {id addr pid paddr : Int}
    (h : StrMem.PtrObj m id addr pid paddr) (a : Int) (bs : Mem.Concrete.Representation)
    (u : Option Int) (apart : Slots.Apart addr 8 a bs.length) :
    StrMem.PtrObj {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} id addr pid paddr := by
  refine ⟨StateMem.ptrSlot_write h.slot a bs u, ?_, ?_, h.range⟩
  · intro i hi
    have := h.bytes i hi
    show Mem.Concrete.readByte (addr + i) (Mem.Concrete.writeRepresentation a bs m).bytes = _
    unfold Mem.Concrete.readByte at this ⊢
    rw [StrMem.bytes_write_outside a _ bs m (by rcases apart with h | h <;> omega)]
    exact this
  · intro i hi
    show (Mem.Concrete.writeRepresentation a bs m).pointerBytes.lookup (addr + i) = _
    rw [Slots.pointerByte_writeRepresentation bs a _ m (by rcases apart with h | h <;> omega)]
    exact h.prov i hi

/-- A null pointer object apart from a representation write keeps it. -/
theorem ptrNull_write {m : Mem.Concrete.State} {id addr : Int} (h : StrMem.PtrNull m id addr) (a : Int)
    (bs : Mem.Concrete.Representation) (u : Option Int) (apart : Slots.Apart addr 8 a bs.length) :
    StrMem.PtrNull {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} id addr := by
  refine ⟨StateMem.ptrSlot_write h.slot a bs u, fun i hi => ?_⟩
  have := h.bytes i hi
  show Mem.Concrete.readByte (addr + i) (Mem.Concrete.writeRepresentation a bs m).bytes = _
  unfold Mem.Concrete.readByte at this ⊢
  rw [StrMem.bytes_write_outside a _ bs m (by rcases apart with h | h <;> omega)]
  exact this

/-! ## The invariant under pointer stores -/

/-- **Storing the pointer to the `int` local `lq`** into the pointer local `l`. -/
theorem _root_.Silmaril.Compile.Core.Verified.StateMem.Inv.ptrStore {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {l lq : Local} (hl : l ∈ ps) (hlq : lq ∈ ls) {x : Sym}
    (hx : lq.sym.key = x.key) :
    Inv env (PrintfStmt.storedPtr m l.id l.addr lq.id lq.addr) ls ds ps
      (updateP pts l.sym.key (some (.addr x))) := by
  have P := h.ptrs
  have good := P.good (List.ne_nil_of_mem hl) lq hlq
  have len : (StrMem.ptrBytes lq.id lq.addr).length = 8 := by
    simp [StrMem.ptrBytes, Mem.Concrete.encodeInteger_length]
  have hst : StrMem.PtrObj (PrintfStmt.storedPtr m l.id l.addr lq.id lq.addr) l.id l.addr lq.id lq.addr :=
    (StrMem.store_ptr ∅ [] ⟨false, false, false⟩ (.mk [] (.basic (.integer (.signed .int))))
      (P.live l hl) (pid := lq.id) (paddr := lq.addr) ⟨good.1, good.2.1⟩).2
  have : PInv (PrintfStmt.storedPtr m l.id l.addr lq.id lq.addr) ls ps
      (updateP pts l.sym.key (some (.addr x))) :=
    ⟨fun l' hl' => StateMem.ptrSlot_write (P.live l' hl') l.addr (StrMem.ptrBytes lq.id lq.addr) (some l.id),
      P.apart, P.sep, P.good, fun r t hr => by
        unfold updateP at hr
        split at hr
        · rename_i hk
          cases hr
          exact ⟨l, hl, hk.symm, lq, hlq, hx, hst⟩
        · rename_i hk
          obtain ⟨l', hl', hk', hh⟩ := P.pts r t hr
          refine ⟨l', hl', hk', ?_⟩
          have ne : l'.sym.key ≠ l.sym.key := fun e => hk (hk'.symm.trans e)
          have ap := (P.apart l' hl' l hl ne).2
          cases t with
          | null => exact ptrNull_write hh l.addr (StrMem.ptrBytes lq.id lq.addr) (some l.id) (by rw [len]; exact ap)
          | addr q =>
            obtain ⟨lq', hlq', hq', obj⟩ := hh
            exact ⟨lq', hlq', hq', ptrObj_write obj l.addr (StrMem.ptrBytes lq.id lq.addr) (some l.id)
              (by rw [len]; exact ap)⟩⟩
  exact
    { env := h.env
      live := fun l' hl' => live_write (h.live l' hl') l.addr (StrMem.ptrBytes lq.id lq.addr) (some l.id)
      apart := h.apart
      defs := fun q d hd => by
        obtain ⟨ok, l', hl', hk, slot⟩ := h.defs q d hd
        exact ⟨ok, l', hl', hk, slot_write slot l.addr (StrMem.ptrBytes lq.id lq.addr) (some l.id)
          (by rw [len]; exact (P.sep l hl l' hl').2.2)⟩ }

/-- The memory after the unspecified store of a pointer declaration. -/
def uninitPtr (m : Mem.Concrete.State) (id addr : Int) : Mem.Concrete.State :=
  {Mem.Concrete.writeRepresentation addr (Mem.Concrete.plainBytes (List.replicate 8 none)) m with
    lastUsed := some id}

/-- **The unspecified store** into the pointer local `l` removes its target. -/
theorem _root_.Silmaril.Compile.Core.Verified.StateMem.Inv.ptrUninit {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ps) :
    Inv env (uninitPtr m l.id l.addr) ls ds ps (updateP pts l.sym.key none) := by
  have P := h.ptrs
  have len : (Mem.Concrete.plainBytes (List.replicate 8 none)).length = 8 := by
    simp [Mem.Concrete.plainBytes]
  have : PInv (uninitPtr m l.id l.addr) ls ps (updateP pts l.sym.key none) :=
    ⟨fun l' hl' => StateMem.ptrSlot_write (P.live l' hl') l.addr (Mem.Concrete.plainBytes (List.replicate 8 none)) (some l.id),
      P.apart, P.sep, P.good, fun r t hr => by
        unfold updateP at hr
        split at hr
        · cases hr
        · rename_i hk
          obtain ⟨l', hl', hk', hh⟩ := P.pts r t hr
          refine ⟨l', hl', hk', ?_⟩
          have ne : l'.sym.key ≠ l.sym.key := fun e => hk (hk'.symm.trans e)
          have ap := (P.apart l' hl' l hl ne).2
          cases t with
          | null =>
            exact ptrNull_write hh l.addr (Mem.Concrete.plainBytes (List.replicate 8 none)) (some l.id) (by rw [len]; exact ap)
          | addr q =>
            obtain ⟨lq', hlq', hq', obj⟩ := hh
            exact ⟨lq', hlq', hq', ptrObj_write obj l.addr (Mem.Concrete.plainBytes (List.replicate 8 none)) (some l.id)
              (by rw [len]; exact ap)⟩⟩
  exact
    { env := h.env
      live := fun l' hl' => live_write (h.live l' hl') l.addr (Mem.Concrete.plainBytes (List.replicate 8 none)) (some l.id)
      apart := h.apart
      defs := fun q d hd => by
        obtain ⟨ok, l', hl', hk, slot⟩ := h.defs q d hd
        exact ⟨ok, l', hl', hk, slot_write slot l.addr (Mem.Concrete.plainBytes (List.replicate 8 none)) (some l.id)
          (by rw [len]; exact (P.sep l hl l' hl').2.2)⟩ }

/-- The memory after the store of the null pointer into a pointer local. -/
def nullPtr (m : Mem.Concrete.State) (id addr : Int) : Mem.Concrete.State :=
  {Mem.Concrete.writeRepresentation addr (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 8 0)) m with
    lastUsed := some id}

/-- **Storing the null pointer** into the pointer local `l`: its target is `null`. -/
theorem _root_.Silmaril.Compile.Core.Verified.StateMem.Inv.ptrNull {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ps) :
    Inv env (nullPtr m l.id l.addr) ls ds ps (updateP pts l.sym.key (some .null)) := by
  have P := h.ptrs
  have len : (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 8 0)).length = 8 := by
    simp [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length]
  have hst : StrMem.PtrNull (nullPtr m l.id l.addr) l.id l.addr :=
    (StrMem.store_null ∅ [] ⟨false, false, false⟩ (.mk [] (.basic (.integer (.signed .int))))
      (.mk [] (.basic (.integer (.signed .int)))) (P.live l hl)).2
  have : PInv (nullPtr m l.id l.addr) ls ps (updateP pts l.sym.key (some .null)) :=
    ⟨fun l' hl' => StateMem.ptrSlot_write (P.live l' hl') l.addr (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 8 0)) (some l.id),
      P.apart, P.sep, P.good, fun r t hr => by
        unfold updateP at hr
        split at hr
        · rename_i hk
          cases hr
          exact ⟨l, hl, hk.symm, hst⟩
        · rename_i hk
          obtain ⟨l', hl', hk', hh⟩ := P.pts r t hr
          refine ⟨l', hl', hk', ?_⟩
          have ne : l'.sym.key ≠ l.sym.key := fun e => hk (hk'.symm.trans e)
          have ap := (P.apart l' hl' l hl ne).2
          cases t with
          | null =>
            exact ptrNull_write hh l.addr (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 8 0)) (some l.id) (by rw [len]; exact ap)
          | addr q =>
            obtain ⟨lq', hlq', hq', obj⟩ := hh
            exact ⟨lq', hlq', hq', ptrObj_write obj l.addr (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 8 0)) (some l.id)
              (by rw [len]; exact ap)⟩⟩
  exact
    { env := h.env
      live := fun l' hl' => live_write (h.live l' hl') l.addr (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 8 0)) (some l.id)
      apart := h.apart
      defs := fun q d hd => by
        obtain ⟨ok, l', hl', hk, slot⟩ := h.defs q d hd
        exact ⟨ok, l', hl', hk, slot_write slot l.addr (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 8 0)) (some l.id)
          (by rw [len]; exact (P.sep l hl l' hl').2.2)⟩ }

/-! ## The pointer store as local steps -/

variable {file : Program} {labels : Labels}

theorem requestAux_storePtr_apply (ann : List Annot) (q : Qualifiers) (ann' : List Annot)
    (k : List Frame) {m : Mem.Concrete.State} {id addr pid paddr : Int}
    (slot : StrMem.PtrSlot m id addr) (range : 0 < paddr ∧ paddr < 18446744073709551616) :
    requestAux file labels m (.apply (.memory .store)
      [.ctype (intPtr ann q ann'), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.pointer (.allocated pid paddr)))]) k false =
      .memory "Store" (PrintfStmt.storedPtr m id addr pid paddr) (.value .unit)
        (.annotations (PrintfStmt.storeAnn k addr) :: k) := by
  let tags : Mem.Concrete.Tags := ⟨file.tagDefs, m.enumTypes⟩
  obtain ⟨hst, -⟩ := StrMem.store_ptr tags ann q (.mk ann' (.basic (.integer (.signed .int)))) slot range
  have hacc := StrMem.access_ptr tags ann q (.mk ann' (.basic (.integer (.signed .int)))) slot
  rw [requestAux.eq_def]
  simp [awaitsScheduling, memoryRequest, toMemory, objectMemory, Mem.Concrete.unatomic, bind,
    Except.bind, pure, Except.pure]
  erw [hst, hacc]
  rfl

/-- **A positive pointer store** with pure operands, as local steps with one write access. -/
theorem storePtr_local (ann : List Annot) (l : Loc) (u : Unit) (ty p v : PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (tann : List Annot) (q : Qualifiers)
    (ann' : List Annot) {id addr pid paddr : Int} (slot : StrMem.PtrSlot m id addr)
    (range : 0 < paddr ∧ paddr < 18446744073709551616)
    (eval : Eval file (tagsOf file m) env (.inr [ty, p, v])
      (.inr [.ctype (intPtr tann q ann'), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.pointer (.allocated pid paddr)))])) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env, k, m⟩
      ⟨.value .unit, .annotations (PrintfStmt.storeAnn k addr) :: k,
        PrintfStmt.storedPtr (ReturnConst.focusMemory ann m) id addr pid paddr⟩ := by
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
        (by simpa using req) (plain_pureExpr ty env))
    · exact .head (.next (by simpa [same] using req) (LoadTask.plain_setLocation _ _))
        (.single (.update (Interleave.requestAux_setLocation file labels m loc _ _ false)))
  have args := PureLocal.args_local file (tagsOf file m) (labels := labels) (wc := false) eval
    (.memory .store) [] k (ReturnConst.focusMemory ann m) (Locals.tagsOf_focus ann m)
  simp only [argState, List.nil_append] at args
  have slot' : StrMem.PtrSlot (ReturnConst.focusMemory ann m) id addr := by
    obtain ⟨loc, hfocus⟩ := Locals.focusMemory_eq ann m
    rw [hfocus]
    exact ⟨slot.alive, slot.alloc, slot.below, slot.above⟩
  exact hf.trans (args.tail (.memory (requestAux_storePtr_apply tann q ann' k slot' range)))

/-! ## The lifted store, for any positive store -/

/-- `StateStmt.lifted_store_ann` for any positive store: the action (annotations without a
source location) is lifted to the nearest `bound`; the positive store runs by local steps, from
the resumption's memory `m₂`, to `unit` with the single write access `a` (tagged with the fresh
exclusion id) and the memory `M`. -/
theorem lifted_store_gen (sann : List Annot) (hann : StateStmt.noLoc sann = true) (l : Loc) (u : Unit)
    (ty p v : PE) (env : Env) (inner k : List Frame) (m : Mem.Concrete.State) {a : Access}
    (ha : a.negative = some m.nextExcluded)
    (boundary : (inner ++ .bound :: k).span (fun f => match f with
      | .strongBind .. | .bound => false | _ => true) = (inner, .bound :: k))
    {result : Val} {xs : List Access} {m₂ : Mem.Concrete.State}
    (resume : TaskRuns file labels false
      ⟨.value .unit, excludeFrames m.nextExcluded inner,
        {m with nextExcluded := m.nextExcluded + 1}⟩ result xs m₂)
    (excluded : ∀ a ∈ xs, m.nextExcluded ∈ a.exclusions)
    (idle : activeCall (.value .unit) (excludeFrames m.nextExcluded inner) = false)
    {M : Mem.Concrete.State}
    (store : LocalReaches file labels false
      ⟨.effectExpr (.mk [] (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env,
        [.excluded m.nextExcluded], m₂⟩
      ⟨.value .unit, .annotations [a] :: [.excluded m.nextExcluded], M⟩) :
    Reaches file labels
      ⟨.effectExpr (.mk sann (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.value result, k, M⟩ := by
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
  let tasks : List (Nat × (Control × List Frame)) :=
    [(0, .effectExpr act env, [.excluded m.nextExcluded]),
     (1, .value .unit, excludeFrames m.nextExcluded inner)]
  let results : List (Nat × (Val × List Access)) := [(0, .unit, [a]), (1, result, xs)]
  have task0 : TaskRuns file labels false
      ⟨.effectExpr act env, [.excluded m.nextExcluded], m₂⟩ .unit [a] M := by
    refine ⟨[.annotations [a]], ?_, rfl⟩
    refine store.tail (.next ?_ (LoadTask.plain_value .unit))
    simp [requestAux, awaitsScheduling]
  have flag0 : taskFlag false K [] = false := by simp [taskFlag]
  have flag1 : taskFlag false K [(0, .effectExpr act env, [.excluded m.nextExcluded])] = false := by
    simp [taskFlag, controlHasCCall, hasCCall, act]
  have run : TasksRun file labels false K tasks m₁ results M := by
    have r0 : TasksRun file labels false K [(0, .effectExpr act env, [.excluded m.nextExcluded])]
        m₂ [(0, .unit, [a])] M :=
      .snoc (by rw [flag0]; exact task0) .nil
    exact .snoc (by rw [flag1]; exact resume) r0
  have norace : NoRace results := by
    intro x hx y hy ne aa haa bb hbb
    simp only [results, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (ne rfl)
    · have eq : aa = a := by simpa using haa
      subst aa
      exact NegativeStore.excluded_noRace ha (excluded bb hbb)
    · have eq : bb = a := by simpa using hbb
      subst bb
      exact NegativeStore.excluded_noRace_rev ha (excluded aa haa)
    · exact False.elim (ne rfl)
  have sorted : results.Pairwise fun a b => a.1 ≤ b.1 := by simp [results]
  have arena := interleave_runs file labels run (by simp [tasks]) (by
    intro t ht
    simp only [tasks, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp [activeCall]
    · exact idle) []
  have end_ := LocalStep.next (requestAux_end file labels M results K false
    norace sorted) (LoadTask.plain_value _)
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
      ⟨.value (.tuple [.unit, result]), .annotations (a :: xs) :: K, M⟩
      ⟨.value result, .annotations (a :: xs) :: .bound :: k, M⟩ :=
    next_reaches (by intro o h; cases h) (by
      simp [request, requestAux, awaitsScheduling, K])
  have finish := selected.trans
    (Locals.annotations_bound_reaches (a :: xs) result k M)
  unfold PureEval.Reaches Spec.coreStep at finish
  simpa [results] using finish

theorem focus_stdout (ann : List Annot) (m : Mem.Concrete.State) :
    (ReturnConst.focusMemory ann m).stdout = m.stdout := by
  obtain ⟨l, h⟩ := Locals.focusMemory_eq ann m
  rw [h]

/-! ## Pointer statements -/

/-- `int *p;`: the store of `Unspecified(int*)`. -/
def ptrUninitStmt : Eff → Option Sym
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false (.mk _ () (.val (.ctype t))) (.mk _ () (.sym x))
      (.mk _ () (.val (.loaded (.unspecified t')))) .na)))) =>
      if PtrDeref.isIntPtr t = true ∧ PtrDeref.isIntPtr t' = true then some x else none
  | _ => none

theorem ptrUninitStmt_inv {e : Eff} {x : Sym} (h : ptrUninitStmt e = some x) :
    ∃ (a0 : List Annot) (l : Loc) (u : Unit) (b1 : List Annot) (t : Ctype) (b2 b3 : List Annot)
      (t' : Ctype),
      e = .mk a0 (.action (.mk .pos (.mk l u (.store false (.mk b1 () (.val (.ctype t)))
        (.mk b2 () (.sym x)) (.mk b3 () (.val (.loaded (.unspecified t')))) .na)))) ∧
      PtrDeref.isIntPtr t = true ∧ PtrDeref.isIntPtr t' = true := by
  unfold ptrUninitStmt at h
  split at h
  · split at h
    · rename_i hc; cases h; exact ⟨_, _, _, _, _, _, _, _, rfl, hc⟩
    · cases h
  · cases h

/-- `&x`: `let weak a = pure(x) in pure(Specified(a))`. -/
def addrOf : Eff → Option Sym
  | .mk _ (.wseq (.mk _ (.base (some a, _))) (.mk _ (.pure (.mk _ () (.sym x))))
      (.mk _ (.pure (.mk _ () (.ctor .specified [.mk _ () (.sym a')]))))) =>
      if a'.key = a.key then some x else none
  | _ => none

theorem addrOf_inv {e : Eff} {x : Sym} (h : addrOf e = some x) :
    ∃ (a0 pa : List Annot) (a : Sym) (ta : BaseType) (a1 a2 a3 a4 a5 : List Annot) (a' : Sym),
      e = .mk a0 (.wseq (.mk pa (.base (some a, ta))) (.mk a1 (.pure (.mk a2 () (.sym x))))
        (.mk a3 (.pure (.mk a4 () (.ctor .specified [.mk a5 () (.sym a')]))))) ∧ a'.key = a.key := by
  unfold addrOf at h
  split at h
  · split at h
    · rename_i hc; cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, hc⟩
    · cases h
  · cases h

/-- `p = &x;` -/
def ptrAssignStmt : Eff → Option (Sym × Sym)
  | .mk _ (.sseq (.mk _ (.base (none, _)))
      (.mk _ (.bound (.mk _ (.wseq
        (.mk _ (.ctor .tuple [.mk _ (.base (some p, _)), .mk _ (.base (some t, _))]))
        (.mk _ (.unseq [.mk _ (.pure (.mk _ () (.sym r))), ea]))
        (.mk _ (.wseq (.mk _ (.base (none, _)))
          (.mk sann (.action (.mk .neg (.mk _ _ (.store false (.mk _ () (.val (.ctype ty)))
            (.mk _ () (.sym p')) (.mk _ () (.sym t')) .na)))))
          (.mk _ (.pure (.mk _ () (.sym t''))))))))))
      (.mk _ (.pure (.mk _ () (.val .unit))))) =>
      match addrOf ea with
      | some x =>
        if p'.key = p.key ∧ t'.key = t.key ∧ t''.key = t.key ∧ t.key ≠ p.key ∧
            StateStmt.noLoc sann = true ∧ PtrDeref.isIntPtr ty = true then some (r, x)
        else none
      | none => none
  | _ => none

theorem ptrAssignStmt_inv {e : Eff} {r x : Sym} (h : ptrAssignStmt e = some (r, x)) :
    ∃ (a0 a1 : List Annot) (ty0 : BaseType) (a2 a3 a4 a5 : List Annot) (p : Sym) (tp : BaseType)
      (a6 : List Annot) (t : Sym) (tt : BaseType) (a7 a8 a9 : List Annot) (ea : Eff)
      (b0 b1 : List Annot) (ty1 : BaseType) (sann : List Annot) (l : Loc) (u : Unit)
      (b2 : List Annot) (ty : Ctype) (b3 : List Annot) (p' : Sym) (b4 : List Annot) (t' : Sym)
      (b5 b6 : List Annot) (t'' : Sym) (d1 d2 : List Annot),
      e = .mk a0 (.sseq (.mk a1 (.base (none, ty0)))
        (.mk a2 (.bound (.mk a3 (.wseq
          (.mk a4 (.ctor .tuple [.mk a5 (.base (some p, tp)), .mk a6 (.base (some t, tt))]))
          (.mk a7 (.unseq [.mk a8 (.pure (.mk a9 () (.sym r))), ea]))
          (.mk b0 (.wseq (.mk b1 (.base (none, ty1)))
            (.mk sann (.action (.mk .neg (.mk l u (.store false (.mk b2 () (.val (.ctype ty)))
              (.mk b3 () (.sym p')) (.mk b4 () (.sym t')) .na)))))
            (.mk b5 (.pure (.mk b6 () (.sym t''))))))))))
        (.mk d1 (.pure (.mk d2 () (.val .unit))))) ∧
      addrOf ea = some x ∧ p'.key = p.key ∧ t'.key = t.key ∧ t''.key = t.key ∧ t.key ≠ p.key ∧
      StateStmt.noLoc sann = true ∧ PtrDeref.isIntPtr ty = true := by
  unfold ptrAssignStmt at h
  split at h
  · split at h
    · rename_i x' hx
      split at h
      · rename_i hc
        cases h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hx, hc⟩
      · cases h
    · cases h
  · cases h

/-- `int *p = &x;` -/
def ptrInitStmt : Eff → Option (Sym × Sym)
  | .mk _ (.sseq (.mk _ (.base (some t, _))) (.mk _ (.bound ea))
      (.mk _ (.action (.mk .pos (.mk _ _ (.store false (.mk _ () (.val (.ctype ty))) (.mk _ () (.sym p))
        (.mk _ () (.sym t')) .na)))))) =>
      match addrOf ea with
      | some x => if t'.key = t.key ∧ t.key ≠ p.key ∧ PtrDeref.isIntPtr ty = true then some (p, x) else none
      | none => none
  | _ => none

theorem ptrInitStmt_inv {e : Eff} {p x : Sym} (h : ptrInitStmt e = some (p, x)) :
    ∃ (a0 a1 : List Annot) (t : Sym) (tt : BaseType) (a2 : List Annot) (ea : Eff) (a3 : List Annot)
      (l : Loc) (u : Unit) (b1 : List Annot) (ty : Ctype) (b2 b3 : List Annot) (t' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some t, tt))) (.mk a2 (.bound ea))
        (.mk a3 (.action (.mk .pos (.mk l u (.store false (.mk b1 () (.val (.ctype ty)))
          (.mk b2 () (.sym p)) (.mk b3 () (.sym t')) .na)))))) ∧
      addrOf ea = some x ∧ t'.key = t.key ∧ t.key ≠ p.key ∧ PtrDeref.isIntPtr ty = true := by
  unfold ptrInitStmt at h
  split at h
  · split at h
    · rename_i x' hx
      split at h
      · rename_i hc
        cases h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hx, hc⟩
      · cases h
    · cases h
  · cases h

/-! ## Their runs -/

theorem ptrUninit_store (tags : Mem.Concrete.Tags) (ann : List Annot) (q : Qualifiers)
    (ann' : List Annot) (t' : Ctype) (ht' : PtrDeref.isIntPtr t' = true) {m : Mem.Concrete.State}
    {id addr : Int} (slot : StrMem.PtrSlot m id addr) :
    Mem.Concrete.storeTyped tags m (intPtr ann q ann') (.allocated id addr) (.unspecified t') =
      .ok ((addr, 8), uninitPtr m id addr) := by
  obtain ⟨tann, q', ann'', rfl⟩ := PtrDeref.isIntPtr_inv ht'
  have hacc := StrMem.access_ptr tags ann q (.mk ann' (.basic (.integer (.signed .int)))) slot
  obtain ⟨-, ⟨a, look, -, -, -, ro⟩, -, -⟩ := slot
  simp [Mem.Concrete.storeTyped, hacc, Mem.Concrete.checkWritable, look, ro, Mem.Concrete.represent,
    Mem.Concrete.typeLayout, uninitPtr, Mem.Concrete.plainBytes, bind, Except.bind, pure, Except.pure]

/-- **`int *p;`**: the unspecified store, `p` without target. -/
theorem ptrUninit_runs {e : Eff} {x : Sym} (h : ptrUninitStmt e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option PtsTo} (inv : Inv env m ls ds ps pts) {l : Local}
    (hl : l ∈ ps) (hx : x.key = l.sym.key) (k : List Frame) (penv : StateMem.PEnv env ps) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls ds ps (updateP pts l.sym.key none) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, t, b2, b3, t', rfl, ht, ht'⟩ := ptrUninitStmt_inv h
  obtain ⟨tann, q, ann', rfl⟩ := PtrDeref.isIntPtr_inv ht
  have hxl : env.lookup x = some (ptr l) := penv l hl x hx
  have eval : Eval file (tagsOf file m) env
      (.inr [.mk b1 () (.val (.ctype (intPtr tann q ann'))), .mk b2 () (.sym x),
        .mk b3 () (.val (.loaded (.unspecified t')))])
      (.inr [.ctype (intPtr tann q ann'), .object (.pointer (.allocated l.id l.addr)),
        .loaded (.unspecified t')]) :=
    .cons .val (.cons (.sym hxl) (.cons .val .nil))
  have inv₁ := inv.focus a0
  have slot₁ := inv₁.ptrs.live l hl
  have hst := ptrUninit_store ⟨file.tagDefs, (ReturnConst.focusMemory a0 m).enumTypes⟩ tann q ann' t' ht'
    slot₁
  have hacc := StrMem.access_ptr ⟨file.tagDefs, (ReturnConst.focusMemory a0 m).enumTypes⟩ tann q
    (.mk ann' (.basic (.integer (.signed .int)))) slot₁
  refine ⟨uninitPtr (ReturnConst.focusMemory a0 m) l.id l.addr, PrintfStmt.storeAnn k l.addr, ?_,
    inv₁.ptrUninit hl, (Locals.action_reaches Locals.request_store eval).trans
    (Actions.memory_reaches (name := "Store") (by intro o h; cases h) ?_)⟩
  · show (Mem.Concrete.writeRepresentation l.addr _ (ReturnConst.focusMemory a0 m)).stdout = m.stdout
    rw [StrMem.wr_stdout, focus_stdout]
  · simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory,
      bind, Except.bind, pure, Except.pure]
    erw [hst, hacc]
    rfl

/-- `int *p = NULL;`: the store of `Specified(NULL)`. -/
def ptrNullInitStmt : Eff → Option Sym
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false (.mk _ () (.val (.ctype t))) (.mk _ () (.sym x))
      (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.pointer (.null _))))])) .na)))) =>
      if PtrDeref.isIntPtr t = true then some x else none
  | _ => none

theorem ptrNullInitStmt_inv {e : Eff} {x : Sym} (h : ptrNullInitStmt e = some x) :
    ∃ (a0 : List Annot) (l : Loc) (u : Unit) (b1 : List Annot) (t : Ctype) (b2 b3 b4 : List Annot)
      (t' : Ctype),
      e = .mk a0 (.action (.mk .pos (.mk l u (.store false (.mk b1 () (.val (.ctype t)))
        (.mk b2 () (.sym x)) (.mk b3 () (.ctor .specified [.mk b4 () (.val (.object (.pointer (.null t'))))]))
        .na)))) ∧
      PtrDeref.isIntPtr t = true := by
  unfold ptrNullInitStmt at h
  split at h
  · split at h
    · rename_i hc; cases h; exact ⟨_, _, _, _, _, _, _, _, _, rfl, hc⟩
    · cases h
  · cases h

/-- **`int *p = NULL;`**: `p` holds the null pointer. -/
theorem ptrNullInit_runs {e : Eff} {x : Sym} (h : ptrNullInitStmt e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option PtsTo} (inv : Inv env m ls ds ps pts) {l : Local}
    (hl : l ∈ ps) (hx : x.key = l.sym.key) (k : List Frame) (penv : StateMem.PEnv env ps) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls ds ps (updateP pts l.sym.key (some .null)) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, t, b2, b3, b4, t', rfl, ht⟩ := ptrNullInitStmt_inv h
  obtain ⟨tann, q, ann', rfl⟩ := PtrDeref.isIntPtr_inv ht
  have hxl : env.lookup x = some (ptr l) := penv l hl x hx
  have eval : Eval file (tagsOf file m) env
      (.inr [.mk b1 () (.val (.ctype (intPtr tann q ann'))), .mk b2 () (.sym x),
        .mk b3 () (.ctor .specified [.mk b4 () (.val (.object (.pointer (.null t'))))])])
      (.inr [.ctype (intPtr tann q ann'), .object (.pointer (.allocated l.id l.addr)),
        .loaded (.specified (.pointer (.null t')))]) :=
    .cons .val (.cons (.sym hxl) (.cons (.ctor (.cons .val .nil) (by simp [primitive, pure, Except.pure, runtimeValue,
      runtimeObject])) .nil))
  have inv₁ := inv.focus a0
  have slot₁ := inv₁.ptrs.live l hl
  have hst := (StrMem.store_null ⟨file.tagDefs, (ReturnConst.focusMemory a0 m).enumTypes⟩ tann q
    (.mk ann' (.basic (.integer (.signed .int)))) t' slot₁).1
  have hacc := StrMem.access_ptr ⟨file.tagDefs, (ReturnConst.focusMemory a0 m).enumTypes⟩ tann q
    (.mk ann' (.basic (.integer (.signed .int)))) slot₁
  refine ⟨nullPtr (ReturnConst.focusMemory a0 m) l.id l.addr, PrintfStmt.storeAnn k l.addr, ?_,
    inv₁.ptrNull hl, (Locals.action_reaches Locals.request_store eval).trans
    (Actions.memory_reaches (name := "Store") (by intro o h; cases h) ?_)⟩
  · show (Mem.Concrete.writeRepresentation l.addr _ (ReturnConst.focusMemory a0 m)).stdout = m.stdout
    rw [StrMem.wr_stdout, focus_stdout]
  · simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory,
      Mem.Concrete.unatomic, bind, Except.bind, pure, Except.pure]
    erw [hst, hacc]
    rfl

/-- `&x` runs to the pointer that `x` names, the memory `Touched`. -/
theorem addr_runs {e : Eff} {x : Sym} (h : addrOf e = some x) {env : Env} {v : Mem.Concrete.Pointer}
    (hx : env.lookup x = some (.object (.pointer v))) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ m', LoadTask.Touched m m' ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
      ⟨.value (.loaded (.specified (.pointer v))), k, m'⟩ := by
  obtain ⟨a0, pa, a, ta, a1, a2, a3, a4, a5, a', rfl, ha'⟩ := addrOf_inv h
  let E : EE := .mk a3 (.pure (.mk a4 () (.ctor .specified [.mk a5 () (.sym a')])))
  have s₀ := ArgvChar.wseq_enter (file := file) (labels := labels) a0 (.mk pa (.base (some a, ta)))
    (.mk a1 (.pure (.mk a2 () (.sym x)))) E env k m
  obtain ⟨l₁, s₁⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) a1 a2 x env hx
    (.effectBind (.mk pa (.base (some a, ta))) E env :: k) m
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  have s₂ := ArgvChar.value_effectBind (file := file) (labels := labels) (fr := []) (xs := [])
    (.inl ⟨rfl, rfl⟩) (pat := .mk pa (.base (some a, ta))) (v := .object (.pointer v)) rfl E env k m₁
  let env₁ := extendEnv [(a, .object (.pointer v))] env
  obtain ⟨l₂, s₃⟩ := ExitCall.pure_local file labels (wc := false) (env := env₁) (k := k) (m := m₁) a3
    (.mk a4 () (.ctor .specified [.mk a5 () (.sym a')]))
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₂}
  have heval : Eval file (tagsOf file m₂) env₁ (.inl (.mk a4 () (.ctor .specified [.mk a5 () (.sym a')])))
      (.inl (.loaded (.specified (.pointer v)))) :=
    .ctor (.cons (.sym (ConvInt.lookup_one ha')) .nil) (by simp [primitive, pure, Except.pure])
  have s₄ := PureLocal.eval_local file (tagsOf file m₂) (wc := false) (labels := labels) heval
    (.diagnosticLocation m₁.currentLocation :: k) m₂ rfl
  exact ⟨m₂, ⟨l₂, m.lastUsed, rfl⟩, s₀.trans (s₁.trans (s₂.trans (s₃.trans (s₄.tail
    (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _))))))⟩

/-- The resumption of `p = &x`: `pure(t)` with `t` bound to the stored pointer. -/
theorem ptrAssign_resume (b1 : List Annot) (ty1 : BaseType) (an an₁ : List Annot) (t' : Sym)
    (env₁ : Env) (xs : List Access) (n : Nat) (m : Mem.Concrete.State) {v : Val}
    (ht : env₁.lookup t' = some v) :
    ∃ m', LoadTask.Touched m m' ∧ TaskRuns file labels false
      ⟨.value .unit, excludeFrames n [.effectBind (.mk b1 (.base (none, ty1)))
        (.mk an (.pure (.mk an₁ () (.sym t')))) env₁, .annotations xs], m⟩
      v (xs.map fun x => {x with exclusions := n :: x.exclusions}) m' := by
  let ys := xs.map fun x => {x with exclusions := n :: x.exclusions}
  have hex : excludeFrames n [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure (.mk an₁ () (.sym t'))))
      env₁, .annotations xs] = [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure (.mk an₁ () (.sym t'))))
      env₁, .annotations ys] := rfl
  rw [hex]
  have s₁ : LocalReaches file labels false
      ⟨.value .unit, [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure (.mk an₁ () (.sym t')))) env₁,
        .annotations ys], m⟩
      ⟨.effectExpr (.mk an (.pure (.mk an₁ () (.sym t')))) env₁, [.annotations ys], m⟩ :=
    .single (.next (by simp [requestAux, awaitsScheduling, matchPattern, extendEnv])
      (LoadTask.plain_effectExpr _ _))
  obtain ⟨l', s₂⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) an an₁ t' env₁ ht
    [.annotations ys] m
  exact ⟨_, ⟨l', m.lastUsed, rfl⟩, [.annotations ys], s₁.trans s₂, by simp [annotationsOnly, ys]⟩

/-- **`p = &x;`**: `p` holds the pointer to `x`. -/
theorem ptrAssign_runs {e : Eff} {r x : Sym} (h : ptrAssignStmt e = some (r, x))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option PtsTo} (inv : Inv env m ls ds ps pts) {l lq : Local}
    (hl : l ∈ ps) (hr : r.key = l.sym.key) (hlq : lq ∈ ls) (hx : x.key = lq.sym.key)
    (k : List Frame) (penv : StateMem.PEnv env ps) :
    ∃ m', m'.stdout = m.stdout ∧ Inv env m' ls ds ps (updateP pts l.sym.key (some (.addr x))) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  obtain ⟨a0, a1, ty0, a2, a3, a4, a5, p, tp, a6, t₀, tt, a7, a8, a9, ea, b0, b1, ty1, sann, lc, u,
    b2, ty, b3, p', b4, t', b5, b6, t'', d1, d2, rfl, hea, hp', ht', ht'', htp, hann, hty⟩ :=
    ptrAssignStmt_inv h
  obtain ⟨tann, q, ann', rfl⟩ := PtrDeref.isIntPtr_inv hty
  obtain ⟨c0, cpa, ca, cta, c1, c2, c3, c4, c5, ca', rfl, -⟩ := addrOf_inv hea
  let EA : EE := .mk c0 (.wseq (.mk cpa (.base (some ca, cta))) (.mk c1 (.pure (.mk c2 () (.sym x))))
    (.mk c3 (.pure (.mk c4 () (.ctor .specified [.mk c5 () (.sym ca')])))))
  let PU : EE := .mk d1 (.pure (.mk d2 () (.val .unit)))
  let K0 := Frame.strongBind (.mk a1 (.base (none, ty0))) PU env :: k
  let PAT : Pattern Sym := .mk a4 (.ctor .tuple [.mk a5 (.base (some p, tp)), .mk a6 (.base (some t₀, tt))])
  let PX : EE := .mk a8 (.pure (.mk a9 () (.sym r)))
  let NEG : EE := .mk sann (.action (.mk .neg (.mk lc u (.store false (.mk b2 () (.val (.ctype
    (intPtr tann q ann')))) (.mk b3 () (.sym p')) (.mk b4 () (.sym t')) .na))))
  let RES : EE := .mk b5 (.pure (.mk b6 () (.sym t'')))
  let BODY : EE := .mk b0 (.wseq (.mk b1 (.base (none, ty1))) NEG RES)
  let KB := Frame.effectBind PAT BODY env :: .bound :: K0
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (none, ty0)))
      (.mk a2 (.bound (.mk a3 (.wseq PAT (.mk a7 (.unseq [PX, EA])) BODY)))) PU)) env, k, m⟩
      ⟨.effectExpr (.mk a7 (.unseq [PX, EA])) env, KB, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      ((ReturnLit.bound_reaches a2 _ env _ m).trans (Locals.wseq_reaches a3 PAT _ BODY env _ m))
  have hpl : env.lookup r = some (ptr l) := penv l hl r hr
  have hxq : env.lookup x = some (ptr lq) := inv.env lq hlq x hx
  let vq : Val := .loaded (.specified (.pointer (.allocated lq.id lq.addr)))
  let I : Mem.Concrete.State → Prop := fun _ => True
  have taskX : LoadTask.ReadTask (file := file) (labels := labels) I env PX (ptr l) :=
    StateStmt.sym_readTask I env a8 a9 r hpl
  have taskA : LoadTask.ReadTask (file := file) (labels := labels) I env EA vq := by
    refine ⟨by simp [EA, hasCCall], fun m' _ => ?_⟩
    obtain ⟨m'', tch, run⟩ := addr_runs (file := file) (labels := labels) hea hxq [] m'
    exact ⟨[], m'', by simp, tch, [], run, rfl⟩
  obtain ⟨xs, m₁, -, tch, s₂⟩ := IntExpr.unseq_pair (file := file) (labels := labels) (k := KB)
    (annots := a7) I (fun _ _ _ _ => trivial) taskX taskA
    (by intro eq; simp only [PX] at eq; injection eq with _ h; cases h) m trivial
  let env₁ := extendEnv [(p, ptr l), (t₀, vq)] env
  have s₃ : Reaches file labels ⟨.value (.tuple [ptr l, vq]), .annotations xs :: KB, m₁⟩
      ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩ :=
    Interleave.reaches_of_local file labels (.single (.next
      (IntExpr.requestAux_tuple_bind m₁ xs a4 a5 a6 p t₀ tp tt _ _ _ env _)
      (LoadTask.plain_effectExpr _ _)))
  let inner := [Frame.effectBind (.mk b1 (.base (none, ty1))) RES env₁, .annotations xs]
  have s₄ : Reaches file labels ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩
      ⟨.effectExpr NEG env₁, inner ++ .bound :: K0, m₁⟩ :=
    Locals.wseq_reaches b0 _ NEG _ env₁ _ m₁
  have ht₁ : env₁.lookup t'' = some vq := StateStmt.lookup_two_snd ht'' htp
  obtain ⟨m₂, tch₂, resume⟩ := ptrAssign_resume (file := file) (labels := labels) b1 ty1 b5 b6 t'' env₁
    xs m₁.nextExcluded {m₁ with nextExcluded := m₁.nextExcluded + 1} ht₁
  have inv₂ : Inv env m₂ ls ds ps pts := ((inv.touched tch).nextExcluded _).touched tch₂
  have good := inv.ptrs.good (List.ne_nil_of_mem hl) lq hlq
  have eval : Eval file (tagsOf file m₂) env₁ (.inr [.mk b2 () (.val (.ctype (intPtr tann q ann'))),
      .mk b3 () (.sym p'), .mk b4 () (.sym t')])
      (.inr [.ctype (intPtr tann q ann'), .object (.pointer (.allocated l.id l.addr)), vq]) :=
    .cons .val (.cons (.sym (StateStmt.lookup_two_fst hp')) (.cons (.sym (StateStmt.lookup_two_snd ht' htp)) .nil))
  have store := storePtr_local (file := file) (labels := labels) [] lc u _ _ _ env₁
    [.excluded m₁.nextExcluded] m₂ tann q ann' (inv₂.ptrs.live l hl) ⟨good.1, good.2.1⟩ eval
  let M := PrintfStmt.storedPtr (ReturnConst.focusMemory [] m₂) l.id l.addr lq.id lq.addr
  have s₅ : Reaches file labels ⟨.effectExpr NEG env₁, inner ++ .bound :: K0, m₁⟩ ⟨.value vq, K0, M⟩ :=
    lifted_store_gen (file := file) (labels := labels) sann hann lc u _ _ _ env₁ inner K0 m₁
      (a := ⟨some m₁.nextExcluded, [], true, l.addr, 8⟩) rfl
      (by simp [inner, List.span, List.span.loop]) resume
      (by intro a ha; obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha; simp)
      (by simp [activeCall, excludeFrames, inner]) store
  have inv₃ : Inv env M ls ds ps (updateP pts l.sym.key (some (.addr x))) :=
    (inv₂.focus []).ptrStore hl hlq hx.symm
  refine ⟨ReturnConst.focusMemory d1 M, ?_, inv₃.focus d1, ?_⟩
  · rw [focus_stdout]
    show (Mem.Concrete.writeRepresentation l.addr _ (ReturnConst.focusMemory [] m₂)).stdout = m.stdout
    rw [StrMem.wr_stdout, focus_stdout, tch₂.stdout, tch.stdout]
  · exact pre.trans ((Interleave.reaches_of_local file labels s₂).trans (s₃.trans (s₄.trans
      (s₅.trans ((ReturnConst.wildcard_sequence_reaches file labels a1 ty0 _ PU env k M).trans
        (StateStmt.pure_unit_reaches d1 d2 env k M))))))

/-- **`int *p = &x;`**: `p` holds the pointer to `x`. -/
theorem ptrInit_runs {e : Eff} {p x : Sym} (h : ptrInitStmt e = some (p, x))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option PtsTo} (inv : Inv env m ls ds ps pts) {l lq : Local}
    (hl : l ∈ ps) (hp : p.key = l.sym.key) (hlq : lq ∈ ls) (hx : x.key = lq.sym.key)
    (k : List Frame) (penv : StateMem.PEnv env ps) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls ds ps (updateP pts l.sym.key (some (.addr x))) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, a1, t, tt, a2, ea, a3, lc, u, b1, ty, b2, b3, t', rfl, hea, ht', htp, hty⟩ :=
    ptrInitStmt_inv h
  obtain ⟨tann, q, ann', rfl⟩ := PtrDeref.isIntPtr_inv hty
  let ST : EE := .mk a3 (.action (.mk .pos (.mk lc u (.store false (.mk b1 () (.val (.ctype
    (intPtr tann q ann')))) (.mk b2 () (.sym p)) (.mk b3 () (.sym t')) .na))))
  let K := Frame.strongBind (.mk a1 (.base (some t, tt))) ST env :: k
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some t, tt)))
      (.mk a2 (.bound ea)) ST)) env, k, m⟩ ⟨.effectExpr ea env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  have hxq : env.lookup x = some (ptr lq) := inv.env lq hlq x hx
  obtain ⟨m₁, tch, run⟩ := addr_runs (file := file) (labels := labels) hea hxq (.bound :: K) m
  let vq : Val := .loaded (.specified (.pointer (.allocated lq.id lq.addr)))
  let env₁ := extendEnv [(t, vq)] env
  have hp₁ : env₁.lookup p = some (ptr l) := by
    rw [ConvInt.lookup_one_other (fun e => htp e.symm)]; exact penv l hl p hp
  have inv₁ : Inv env m₁ ls ds ps pts := inv.touched tch
  have good := inv.ptrs.good (List.ne_nil_of_mem hl) lq hlq
  have hst := PrintfStmt.storePtr_reaches file labels a3 b1 b2 b3 lc u () () () tann q
    (.mk ann' (.basic (.integer (.signed .int)))) hp₁ (ConvInt.lookup_one ht') (inv₁.ptrs.live l hl)
    ⟨good.1, good.2.1⟩ k
  rw [← PrintfStmt.focus_same] at hst
  have inv₂ := (inv₁.focus a3).ptrStore hl hlq hx.symm
  refine ⟨_, _, ?_, inv₂, pre.trans ((Interleave.reaches_of_local file labels run).trans
    ((StateStmt.bound_pop (.inl ⟨rfl, rfl⟩) _ K m₁).trans
      ((ReturnLit.bind_reaches a1 t tt _ ST env k m₁).trans hst)))⟩
  show (Mem.Concrete.writeRepresentation l.addr _ (ReturnConst.focusMemory a3 m₁)).stdout = m.stdout
  rw [StrMem.wr_stdout, focus_stdout, tch.stdout]

/-! ## Creating pointer locals -/

/-- `create(alignof(int*), int*)`. -/
def createPtrOf : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.create (.mk _ () (.ctor .ivAlignof [.mk _ () (.val (.ctype t₁))]))
      (.mk _ () (.val (.ctype t₂))) _)))) => PtrDeref.isIntPtr t₁ && PtrDeref.isIntPtr t₂
  | _ => false

theorem createPtrOf_inv {e : Eff} (h : createPtrOf e = true) :
    ∃ (ann : List Annot) (l : Loc) (u : Unit) (a1 a2 : List Annot) (t₁ : Ctype) (a3 : List Annot)
      (t₂ : Ctype) (pref : Prefix),
      e = .mk ann (.action (.mk .pos (.mk l u (.create (.mk a1 () (.ctor .ivAlignof
        [.mk a2 () (.val (.ctype t₁))])) (.mk a3 () (.val (.ctype t₂))) pref)))) ∧
      PtrDeref.isIntPtr t₁ = true ∧ PtrDeref.isIntPtr t₂ = true := by
  unfold createPtrOf at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, _, _, _, _, _, _, rfl, h.1, h.2⟩
  · cases h

/-- **Creating a pointer local**: a fresh 8-byte object below every earlier one. -/
theorem createPtrOf_reaches {e : Eff} (h : createPtrOf e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) (hpos : 0 < StrMem.ptrAddr m) :
    ∃ ann pref t, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (StrMem.ptrAddr m)))), k,
        StrMem.createdPtr pref t (ReturnConst.focusMemory ann m)⟩ := by
  obtain ⟨ann, l, u, a1, a2, t₁, a3, t₂, pref, rfl, h₁, h₂⟩ := createPtrOf_inv h
  obtain ⟨tann₁, q₁, ann₁, rfl⟩ := PtrDeref.isIntPtr_inv h₁
  obtain ⟨tann, q, ann', rfl⟩ := PtrDeref.isIntPtr_inv h₂
  refine ⟨ann, pref, intPtr tann q ann', ?_⟩
  have hev : PureEval.Eval file (PureEval.tagsOf file m) env
      (.inr [.mk a1 () (.ctor .ivAlignof [.mk a2 () (.val (.ctype (intPtr tann₁ q₁ ann₁)))]),
        .mk a3 () (.val (.ctype (intPtr tann q ann')))])
      (.inr [.object (.integer 8), .ctype (intPtr tann q ann')]) :=
    .cons (.ctor (.cons .val .nil) (PrintfStmt.alignof_ptr _ tann₁ q₁ _)) (.cons .val .nil)
  refine (Locals.action_reaches Locals.request_create hev).trans ?_
  have hfm : ReturnConst.focusMemory ann m = SeqReach.focusMemory ann m := PrintfStmt.focus_same ann m
  have hpos' : 0 < StrMem.ptrAddr (ReturnConst.focusMemory ann m) := by
    rw [hfm]; unfold StrMem.ptrAddr; simp only [PrintfStd.focus_lastAddress]; exact hpos
  have ha := StrMem.allocate_ptr ⟨file.tagDefs, (ReturnConst.focusMemory ann m).enumTypes⟩
    (ReturnConst.focusMemory ann m) tann q (.mk ann' (.basic (.integer (.signed .int)))) hpos'
  have hid : (ReturnConst.focusMemory ann m).nextId = m.nextId := by
    rw [hfm]; exact PrintfStd.focus_nextId ann m
  have hpa : StrMem.ptrAddr (ReturnConst.focusMemory ann m) = StrMem.ptrAddr m := by
    rw [hfm]; unfold StrMem.ptrAddr; simp only [PrintfStd.focus_lastAddress]
  rw [← hid, ← hpa]
  exact Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest, ha, StrMem.createdPtr, bind, Except.bind,
      pure, Except.pure])

/-! ## What creating an object below keeps -/

theorem liveInt_keeps {m m' : Mem.Concrete.State} {id addr : Int} (h : LiveInt m id addr)
    (k : StrMem.Keeps m m') (hid : id < m.nextId) : LiveInt m' id addr := by
  obtain ⟨alive, found⟩ := h
  exact ⟨by rw [k.dead id hid]; exact alive, by rw [k.alloc id hid]; exact found⟩

theorem slot_keeps {m m' : Mem.Concrete.State} {id addr n : Int} (h : Slot m id addr n)
    (k : StrMem.Keeps m m') (hid : id < m.nextId) (ha : m.lastAddress ≤ addr) : Slot m' id addr n := by
  refine ⟨liveInt_keeps h.live k hid, fun i hi => ?_, ?_⟩
  · rw [k.pbytes _ (by omega)]; exact h.plain i hi
  · rw [← h.bytes]
    have e : ∀ j : Int, addr ≤ j → m'.bytes.lookup j = m.bytes.lookup j := fun j hj => k.bytes j (by omega)
    simp only [Mem.Concrete.fetchBytes, Mem.Concrete.readByte, e addr (le_refl _), e (addr + 1) (by omega),
      e (addr + 1 + 1) (by omega), e (addr + 1 + 1 + 1) (by omega)]

end Silmaril.Compile.Core.Verified.PtrStmt
