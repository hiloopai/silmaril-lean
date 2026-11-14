module

public import Silmaril.Compiler.Core.Verified.StructCell.Defs
public import Silmaril.Compiler.Core.Verified.ArrSyntax.Defs
public import Silmaril.Compiler.Core.Verified.State.Defs
/-! # All-`int` struct objects

A local `struct T s;` of an all-`int` struct (`StructCell.members`) elaborates like `int a[N];`:
`create(alignof(struct T), struct T)`, the store of the unspecified `struct T`, and at the end of
the block `kill(struct T, s)`. Its object has the layout of `int[N]`, so each action has the
same effect as for the array (`createStruct_reaches`, `uninit_runs`, `kill_runs`): an
`ArrDesig.Arr` object of `N` cells, `ArrInit.stored`, `Locals.killed`.

`createAny`, `uninitAny` and `killAny` recognise the array or the struct form, with one
conclusion for both; the constant-index fragment `ArrBlock` uses them.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StructObj

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff)
open ArrDesig (Arr arrAddr)
open Mem.Concrete (Tags typeLayout)

/-! ## Layout -/

/-- `struct T` of an all-`int` struct, with its member count. -/
def structLen (file : Program) : Ctype → Option Nat
  | .mk _ (.struct T) => (StructCell.members file.tagDefs T).map List.length
  | _ => none

theorem structLen_inv {file : Program} {t : Ctype} {N : Nat} (h : structLen file t = some N) :
    ∃ ann T ms, t = .mk ann (.struct T) ∧ StructCell.members file.tagDefs T = some ms ∧
      ms.length = N := by
  obtain ⟨ann, node⟩ := t
  unfold structLen at h
  split at h
  · rename_i a T heq
    cases heq
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨ms, hms, rfl⟩ := h
    exact ⟨_, _, _, rfl, hms, rfl⟩
  · cases h

theorem layout_of {file : Program} {t : Ctype} {N : Nat} (h : structLen file t = some N)
    (enums : Map Sym IntegerType) :
    ∃ ms, typeLayout 64 ⟨file.tagDefs, enums⟩ t = .ok ⟨(N : Int) * 4, 4, ms⟩ := by
  obtain ⟨ann, T, ms, rfl, hms, rfl⟩ := structLen_inv h
  exact ⟨StructCell.offsets ms 0, by
    rw [StructCell.layout (tags := ⟨file.tagDefs, enums⟩) hms 62 ann, Int.mul_comm]⟩

theorem alignof_of {file : Program} {t : Ctype} {N : Nat} (h : structLen file t = some N)
    (enums : Map Sym IntegerType) :
    primitive (.ctor .ivAlignof) [.ctype t] ⟨file.tagDefs, enums⟩ = .ok (.object (.integer 4)) := by
  obtain ⟨ms, hl⟩ := layout_of h enums
  obtain ⟨ann, T, -, rfl, -, -⟩ := structLen_inv h
  simp [primitive, Mem.Concrete.alignment, hl, integer, bind, Except.bind, pure, Except.pure]

/-! ## Accesses of the whole object -/

section Access
open Mem.Concrete

variable {tags : Tags} {ty : Ctype} {N : Nat} {ms : List (Identifier × Ctype × Int)}

theorem access_of (hl : typeLayout 64 tags ty = .ok ⟨(N : Int) * 4, 4, ms⟩)
    {m : Mem.Concrete.State} {id addr : Int} (h : Arr m id addr N) :
    accessTyped tags m ty (.allocated id addr) = .ok (id, addr, 4 * N) := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := h
  simp [accessTyped, hl, alive, look, base, size, checkAtomic, atomic,
    bind, Except.bind, pure, Except.pure, mul_comm]

theorem store_of (hl : typeLayout 64 tags ty = .ok ⟨(N : Int) * 4, 4, ms⟩) {vt : Ctype}
    {ms' : List (Identifier × Ctype × Int)} (hv : typeLayout 64 tags vt = .ok ⟨(N : Int) * 4, 4, ms'⟩)
    {m : Mem.Concrete.State} {id addr : Int} (h : Arr m id addr N) :
    storeTyped tags m ty (.allocated id addr) (.unspecified vt) =
      .ok ((addr, 4 * N), ArrInit.stored m id addr N) := by
  obtain ⟨a, look, _, _, _, ro⟩ := h.found
  simp [storeTyped, access_of hl h, checkWritable, look, ro, represent, hv, ArrInit.stored,
    plainBytes, bind, Except.bind, pure, Except.pure, Int.toNat_mul, mul_comm]

end Access

/-- The actual Store action of the unspecified struct records the whole object's footprint. -/
theorem store_apply {file : Program} {labels : Labels} (k : List Frame) {ty vt : Ctype} {N : Nat}
    (hty : structLen file ty = some N) (hvt : structLen file vt = some N)
    {m : Mem.Concrete.State} {id addr : Int} (h : Arr m id addr N) :
    Interleave.LocalReaches file labels false
      ⟨.apply (.memory .store) [.ctype ty, .object (.pointer (.allocated id addr)),
        .loaded (.unspecified vt)], k, m⟩
      ⟨.value .unit, .annotations [⟨k.findSome? fun f => match f with
        | .excluded n => some n | _ => none, [], true, addr, 4 * N⟩] :: k, ArrInit.stored m id addr N⟩ := by
  obtain ⟨ms, hl⟩ := layout_of hty m.enumTypes
  obtain ⟨ms', hv⟩ := layout_of hvt m.enumTypes
  apply Relation.ReflTransGen.single
  apply Interleave.LocalStep.memory (name := "Store")
  simp [requestAux, awaitsScheduling, memoryRequest, toMemory, store_of hl hv h, access_of hl h,
    bind, Except.bind, pure, Except.pure]
  rfl

/-! ## Creation -/

/-- The memory after allocating a `4 * N`-byte object of type `ty` (`allocateTyped`). -/
def created (ty : Ctype) (N : Nat) (m : Mem.Concrete.State) : Mem.Concrete.State :=
  { Mem.Concrete.writeRepresentation (arrAddr m N)
      (Mem.Concrete.plainBytes (List.replicate (N * 4) none)) m with
    nextId := m.nextId + 1
    lastAddress := arrAddr m N
    allocations := m.allocations.insert m.nextId
      ({base := arrAddr m N, size := (N : Int) * 4, objectType := some ty} : Mem.Concrete.Allocation)
    lastUsed := some m.nextId }

theorem allocate_of (tags : Tags) (m : Mem.Concrete.State) (ann : List Annot) (T : Sym) {N : Nat}
    {ms : List (Identifier × Ctype × Int)}
    (hl : typeLayout 64 tags (.mk ann (.struct T)) = .ok ⟨(N : Int) * 4, 4, ms⟩)
    (hpos : 0 < arrAddr m N) :
    Mem.Concrete.allocateTyped tags m 4 (.mk ann (.struct T)) =
      .ok (.allocated m.nextId (arrAddr m N), created (.mk ann (.struct T)) N m) := by
  unfold arrAddr at hpos
  have hn : ¬ (m.lastAddress - (N : Int) * 4 - (m.lastAddress - (N : Int) * 4) % 4 ≤ 0) := by omega
  simp only [Mem.Concrete.allocateTyped, hl, bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right_of_eq_false _ _ (by simp), ite_eq_right_of_eq_false _ _ (by simpa using hn)]
  rw [show ((N : Int) * 4).toNat = N * 4 by omega]
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape
    (m.lastAddress - (N : Int) * 4 - (m.lastAddress - (N : Int) * 4) % 4)
    (Mem.Concrete.plainBytes (List.replicate (N * 4) none)) m
  simp only [created, arrAddr, h]

/-- The memory after the creation: the allocation, then the prefix's read-only kind on it. -/
def createdP (pref : Prefix) (ty : Ctype) (N : Nat) (m : Mem.Concrete.State) : Mem.Concrete.State :=
  Mem.Concrete.updateLastAllocation (created ty N m)
    fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}

theorem createdP_arr (pref : Prefix) (ty : Ctype) (N : Nat) (m : Mem.Concrete.State)
    (fresh : m.nextId ∉ m.dead) :
    Arr (createdP pref ty N m) m.nextId (arrAddr m N) N := by
  unfold createdP
  rw [StrMem.updateLast_of _ _ rfl (Map.lookup_insert _ _ _)]
  refine ⟨?_, _, Map.lookup_insert _ _ _, rfl, by simp; omega, rfl, rfl⟩
  simpa [created, (Mem.Concrete.writeRepresentation_allocations _ _ m).2.1] using fresh

/-- `create(alignof(struct T), struct T)` of an all-`int` struct. -/
def createStructOf (file : Program) : Eff → Option Nat
  | .mk _ (.action (.mk .pos (.mk _ _ (.create (.mk _ () (.ctor .ivAlignof [.mk _ () (.val (.ctype t₁))]))
      (.mk _ () (.val (.ctype t₂))) _)))) =>
      match structLen file t₁, structLen file t₂ with
      | some a, some b => if a = b then some a else none
      | _, _ => none
  | _ => none

theorem createStructOf_inv {file : Program} {e : Eff} {N : Nat} (h : createStructOf file e = some N) :
    ∃ (ann : List Annot) (l : Loc) (u : Unit) (a1 a2 : List Annot) (t₁ : Ctype) (a3 : List Annot)
      (t₂ : Ctype) (pref : Prefix),
      e = .mk ann (.action (.mk .pos (.mk l u (.create (.mk a1 () (.ctor .ivAlignof
        [.mk a2 () (.val (.ctype t₁))])) (.mk a3 () (.val (.ctype t₂))) pref)))) ∧
      structLen file t₁ = some N ∧ structLen file t₂ = some N := by
  unfold createStructOf at h
  split at h
  · split at h
    · rename_i a b h₁ h₂
      split at h
      · rename_i hab
        cases h; subst hab
        exact ⟨_, _, _, _, _, _, _, _, _, rfl, h₁, h₂⟩
      · cases h
    · cases h
  · cases h

/-- The fields of the memory after a creation that ends the run of an `ArrBlock` creation. -/
structure Created (m m₁ : Mem.Concrete.State) (N : Nat) : Prop where
  arr : Arr m₁ m.nextId (arrAddr m N) N
  stdout : m₁.stdout = m.stdout
  lastAddress : m₁.lastAddress = arrAddr m N
  nextId : m₁.nextId = m.nextId + 1
  dead : m₁.dead = m.dead

theorem lastAllocation_lastAddress (s : Mem.Concrete.State) (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).lastAddress = s.lastAddress := by
  unfold Mem.Concrete.updateLastAllocation; split <;> try split
  all_goals rfl

theorem lastAllocation_nextId (s : Mem.Concrete.State) (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).nextId = s.nextId := by
  unfold Mem.Concrete.updateLastAllocation; split <;> try split
  all_goals rfl

theorem lastAllocation_dead (s : Mem.Concrete.State) (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).dead = s.dead := by
  unfold Mem.Concrete.updateLastAllocation; split <;> try split
  all_goals rfl

theorem lastAllocation_stdout (s : Mem.Concrete.State) (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).stdout = s.stdout := by
  unfold Mem.Concrete.updateLastAllocation; split <;> try split
  all_goals rfl

theorem wr_lastAddress (a : Int) (bs : Mem.Concrete.Representation) (s : Mem.Concrete.State) :
    (Mem.Concrete.writeRepresentation a bs s).lastAddress = s.lastAddress := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape a bs s
  rw [h]

theorem wr_nextId (a : Int) (bs : Mem.Concrete.Representation) (s : Mem.Concrete.State) :
    (Mem.Concrete.writeRepresentation a bs s).nextId = s.nextId := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape a bs s
  rw [h]

variable {file : Program} {labels : Labels}

/-- **Creating an all-`int` struct local**: a fresh `4 * N`-byte object below every earlier one. -/
theorem createStruct_reaches {e : Eff} {N : Nat} (h : createStructOf file e = some N) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < arrAddr m N) :
    ∃ ann pref ty, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (arrAddr m N)))), k,
        createdP pref ty N (ReturnConst.focusMemory ann m)⟩ := by
  obtain ⟨ann, l, u, a1, a2, t₁, a3, t₂, pref, rfl, h₁, h₂⟩ := createStructOf_inv h
  obtain ⟨annT, T, -, rfl, -, -⟩ := structLen_inv h₂
  refine ⟨ann, pref, .mk annT (.struct T), ?_⟩
  have hev : PureEval.Eval file (PureEval.tagsOf file m) env
      (.inr [.mk a1 () (.ctor .ivAlignof [.mk a2 () (.val (.ctype t₁))]),
        .mk a3 () (.val (.ctype (.mk annT (.struct T))))])
      (.inr [.object (.integer 4), .ctype (.mk annT (.struct T))]) :=
    .cons (.ctor (.cons .val .nil) (alignof_of h₁ _)) (.cons .val .nil)
  refine (Locals.action_reaches Locals.request_create hev).trans ?_
  have hfm : ReturnConst.focusMemory ann m = SeqReach.focusMemory ann m := PrintfStmt.focus_same ann m
  have hpa : arrAddr (ReturnConst.focusMemory ann m) N = arrAddr m N := by
    rw [hfm]; unfold arrAddr; simp only [PrintfStd.focus_lastAddress]
  have hpos' : 0 < arrAddr (ReturnConst.focusMemory ann m) N := hpa ▸ hpos
  obtain ⟨ms, hl⟩ := layout_of h₂ (ReturnConst.focusMemory ann m).enumTypes
  have ha := allocate_of ⟨file.tagDefs, (ReturnConst.focusMemory ann m).enumTypes⟩
    (ReturnConst.focusMemory ann m) annT T hl hpos'
  have hid : (ReturnConst.focusMemory ann m).nextId = m.nextId := by
    rw [hfm]; exact PrintfStd.focus_nextId ann m
  rw [← hid, ← hpa]
  exact Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest, ha, createdP, bind, Except.bind,
      pure, Except.pure])

/-- `create` of an `int` array or an all-`int` struct. -/
def createAny (file : Program) (e : Eff) : Option Nat :=
  match ArrCreate.createArrOf e with
  | some N => some N
  | none => createStructOf file e

theorem createAny_reaches {e : Eff} {N : Nat} (h : createAny file e = some N) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < arrAddr m N) (fresh : m.nextId ∉ m.dead) :
    ∃ m₁, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (arrAddr m N)))), k, m₁⟩ ∧ Created m m₁ N := by
  have haddr (ann : List Annot) : arrAddr (ReturnConst.focusMemory ann m) N = arrAddr m N := by
    unfold arrAddr; rw [State.focus_lastAddress]
  have fresh' (ann : List Annot) : (ReturnConst.focusMemory ann m).nextId ∉
      (ReturnConst.focusMemory ann m).dead := by
    rw [State.focus_nextId, State.focus_dead]; exact fresh
  unfold createAny at h
  split at h
  · rename_i N' hc
    cases h
    obtain ⟨ann, pref, annT, annE, run⟩ := ArrCreate.createArrOf_reaches (file := file)
      (labels := labels) hc env k m hpos
    refine ⟨_, run, ?_, ?_, ?_, ?_, ?_⟩
    · have live := ArrCreate.createdArrP_arr pref annT annE N (ReturnConst.focusMemory ann m) (fresh' ann)
      simpa only [State.focus_nextId, haddr] using live
    · simp [ArrCreate.createdArrP, ArrDesig.createdArr, lastAllocation_stdout,
        Actions.writeRepresentation_stdout]
    · simp only [ArrCreate.createdArrP, lastAllocation_lastAddress, ArrDesig.createdArr, haddr]
    · simp only [ArrCreate.createdArrP, lastAllocation_nextId, ArrDesig.createdArr, State.focus_nextId]
    · simp only [ArrCreate.createdArrP, lastAllocation_dead, ArrDesig.createdArr,
        Locals.writeRepresentation_dead, State.focus_dead]
  · obtain ⟨ann, pref, ty, run⟩ := createStruct_reaches (file := file) (labels := labels) h env k m hpos
    refine ⟨_, run, ?_, ?_, ?_, ?_, ?_⟩
    · have live := createdP_arr pref ty N (ReturnConst.focusMemory ann m) (fresh' ann)
      simpa only [State.focus_nextId, haddr] using live
    · simp [createdP, created, lastAllocation_stdout, Actions.writeRepresentation_stdout]
    · simp only [createdP, lastAllocation_lastAddress, created, haddr]
    · simp only [createdP, lastAllocation_nextId, created, State.focus_nextId]
    · simp only [createdP, lastAllocation_dead, created, Locals.writeRepresentation_dead,
        State.focus_dead]

/-! ## The unspecified store and the kill -/

/-- The explicit unspecified store of an all-`int` struct declaration. -/
def uninit (file : Program) (x : Sym) (N : Nat) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false
      (.mk _ () (.val (.ctype ty))) (.mk _ () (.sym r))
      (.mk _ () (.val (.loaded (.unspecified vt)))) .na)))) =>
      decide (r.key = x.key ∧ structLen file ty = some N ∧ structLen file vt = some N)
  | _ => false

/-- A static kill at an all-`int` struct type. -/
def kill (file : Program) (x : Sym) (N : Nat) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.kill (.static ty) (.mk _ () (.sym r)))))) =>
      decide (r.key = x.key ∧ structLen file ty = some N)
  | _ => false

theorem uninit_runs {x : Sym} {N : Nat} {e : Eff} (h : uninit file x N e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ r : Sym, r.key = x.key → env.lookup r = some (.object (.pointer (.allocated id addr))))
    (live : Arr m id addr N) :
    ∃ ann xs, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, .annotations xs :: k, ArrInit.stored (ReturnConst.focusMemory ann m) id addr N⟩ := by
  unfold uninit at h
  split at h
  · rename_i ann l u a1 ty a2 r a3 vt
    simp only [decide_eq_true_eq] at h
    obtain ⟨eq, ht, hv⟩ := h
    have ev : Eval file (tagsOf file m) env
        (.inr [.mk a1 () (.val (.ctype ty)), .mk a2 () (.sym r),
          .mk a3 () (.val (.loaded (.unspecified vt)))])
        (.inr [.ctype ty, .object (.pointer (.allocated id addr)), .loaded (.unspecified vt)]) :=
      .cons .val (.cons (.sym (hx r eq)) (.cons .val .nil))
    exact ⟨ann, _, (Locals.action_reaches Locals.request_store ev).trans
      (Interleave.reaches_of_local file labels (store_apply k ht hv
        (live.touched (StateStmt.seqFocus_touched ann m))))⟩
  · cases h

theorem kill_runs {x : Sym} {N : Nat} {e : Eff} (h : kill file x N e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ r : Sym, r.key = x.key → env.lookup r = some (.object (.pointer (.allocated id addr))))
    (live : Arr m id addr N) :
    ∃ ann, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, k, Locals.killed (ReturnConst.focusMemory ann m) id⟩ := by
  unfold kill at h
  split at h
  · rename_i ann l u ty a2 r
    simp only [decide_eq_true_eq] at h
    obtain ⟨eq, ht⟩ := h
    have ev : Eval file (tagsOf file m) env (.inr [.mk a2 () (.sym r)])
        (.inr [.object (.pointer (.allocated id addr))]) := .cons (.sym (hx r eq)) .nil
    refine ⟨ann, (Locals.action_reaches Locals.request_kill ev).trans ?_⟩
    apply Actions.memory_reaches (name := "Kill") (by intro o h; cases h)
    have live' : Arr (ReturnConst.focusMemory ann m) id addr N :=
      live.touched (StateStmt.seqFocus_touched ann m)
    obtain ⟨ms, hl⟩ := layout_of ht (ReturnConst.focusMemory ann m).enumTypes
    obtain ⟨allocation, look, base, size, atomic, ro⟩ := live'.found
    simp [request, requestAux, awaitsScheduling, memoryRequest, Mem.Concrete.killTyped,
      access_of hl live', look, base, Locals.killed,
      bind, Except.bind, pure, Except.pure]
  · cases h

/-- The unspecified store of an `int` array or an all-`int` struct. -/
def uninitAny (file : Program) (x : Sym) (N : Nat) (e : Eff) : Bool :=
  ArrSyntax.uninit x N e || uninit file x N e

/-- The kill of an `int` array or an all-`int` struct. -/
def killAny (file : Program) (x : Sym) (N : Nat) (e : Eff) : Bool :=
  ArrSyntax.kill x N e || kill file x N e

theorem uninitAny_runs {x : Sym} {N : Nat} {e : Eff} (h : uninitAny file x N e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ r : Sym, r.key = x.key → env.lookup r = some (.object (.pointer (.allocated id addr))))
    (live : Arr m id addr N) :
    ∃ ann xs, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, .annotations xs :: k, ArrInit.stored (ReturnConst.focusMemory ann m) id addr N⟩ := by
  unfold uninitAny at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact ArrSyntax.uninit_runs h env k m hx live
  · exact uninit_runs h env k m hx live

theorem killAny_runs {x : Sym} {N : Nat} {e : Eff} (h : killAny file x N e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ r : Sym, r.key = x.key → env.lookup r = some (.object (.pointer (.allocated id addr))))
    (live : Arr m id addr N) :
    ∃ ann, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, k, Locals.killed (ReturnConst.focusMemory ann m) id⟩ := by
  unfold killAny at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact ArrSyntax.kill_runs h env k m hx live
  · exact kill_runs h env k m hx live

end Silmaril.Compile.Core.Verified.StructObj
