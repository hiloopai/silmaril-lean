module

public import Silmaril.Compiler.Core.Verified.ReturnLit.Defs
public import Silmaril.Cerberus.Mem.IntSlots.Defs

/-! # Core memory actions on `int` objects

The Core machine's `create`, `store`, `load` and `kill` of a C `int` local, as runs of the
machine: operands evaluated (`PureEval`), then one memory transition answered by the
concrete memory (`Mem.IntSlots`). `store` and `load` leave the access annotation frame that
the dynamics keeps for its race check; it is dropped at the enclosing `bound` or merged into
the frame below it.

These are the per-action steps of the int-locals fragment: `create_apply`,
`store_apply`, `load_apply`, `kill_apply`. The statement-level invariant that composes them
(slots, environment, allocation budget, annotation frames) is not built yet; see
`workspace/w756-locals-plan.md`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Actions

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf Sound argState)
open Mem.Concrete (intType LiveInt IntRange PlainAt nextIntAddress)

variable {file : Program} {labels : Labels}

/-- One memory transition. -/
theorem memory_reaches {c c' : Control} {k k' : List Frame} {m m' : Mem.Concrete.State}
    {name : String} (live : ∀ o, c ≠ .halt o)
    (h : request file labels ⟨c, k, m⟩ = .memory name m' c' k') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m'⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.memory name, Step.respond live ?_⟩
  rw [h]
  exact Respond.memory

theorem updateLastAllocation_stdout (s : Mem.Concrete.State) (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).stdout = s.stdout := by
  unfold Mem.Concrete.updateLastAllocation
  split
  · rfl
  · split <;> rfl

theorem writeRepresentation_stdout (a : Int) (bs : Mem.Concrete.Representation) (s : Mem.Concrete.State) :
    (Mem.Concrete.writeRepresentation a bs s).stdout = s.stdout := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape a bs s
  rw [h]

/-- The memory after `create` of an `int` object. -/
def created (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) : Mem.Concrete.State :=
  Mem.Concrete.updateLastAllocation
    { Mem.Concrete.writeRepresentation (nextIntAddress m)
        (Mem.Concrete.plainBytes (List.replicate 4 none)) m with
      nextId := m.nextId + 1
      lastAddress := nextIntAddress m
      allocations := m.allocations.insert m.nextId
        ({base := nextIntAddress m, size := 4, objectType := some (intType ann)} :
          Mem.Concrete.Allocation)
      lastUsed := some m.nextId }
    fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}

/-- `create(alignof(int), int)` allocates a fresh `int` object. -/
theorem create_apply (pref : Prefix) (ann : List Annot) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < nextIntAddress m) :
    Reaches file labels
      ⟨.apply (.memory (.create pref)) [.object (.integer 4), .ctype (intType ann)], k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), k,
        created pref ann m⟩ :=
  memory_reaches (name := "Create") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest,
      Mem.Concrete.allocate_int _ ann m hpos, created])

theorem created_stdout (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    (created pref ann m).stdout = m.stdout := by
  simp [created, updateLastAllocation_stdout, writeRepresentation_stdout]

@[simp] theorem intType_int (ann : List Annot) : Dynamics.intType (intType ann) = some (.signed .int) :=
  rfl

@[simp] theorem unatomic_int (ann : List Annot) : Mem.Concrete.unatomic (intType ann) = intType ann :=
  rfl

/-- `store(int, p, Specified n)` into a live `int` object; the dynamics records the write
access in an annotation frame. -/
theorem store_apply (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State} {id addr : Int}
    (h : LiveInt m id addr) {n : Int} (hn : IntRange n) :
    ∃ xs, Reaches file labels
      ⟨.apply (.memory .store) [.ctype (intType ann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))], k, m⟩
      ⟨.value .unit, .annotations xs :: k,
        {Mem.Concrete.writeRepresentation addr
          (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m with lastUsed := some id}⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, request file labels
      ⟨.apply (.memory .store) [.ctype (intType ann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))], k, m⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory,
    Mem.Concrete.store_int _ ann h hn,
    Mem.Concrete.access_int _ ann h, bind, Except.bind, pure, Except.pure] at hr'
  subst hr'
  exact ⟨_, memory_reaches (by intro o h; cases h) hr⟩

/-- `load(int, p)` of a live `int` object holding `n`. -/
theorem load_apply (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State} {id addr : Int}
    (h : LiveInt m id addr) (plain : PlainAt m addr) {n : Int} (hn : IntRange n)
    (bytes : Mem.Concrete.fetchBytes 4 addr m.bytes = Mem.Concrete.encodeInteger 4 n) :
    ∃ xs, Reaches file labels
      ⟨.apply (.memory .load) [.ctype (intType ann), .object (.pointer (.allocated id addr))], k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), .annotations xs :: k,
        {m with lastUsed := some id}⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, request file labels
      ⟨.apply (.memory .load) [.ctype (intType ann), .object (.pointer (.allocated id addr))], k,
        m⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, fromMemory,
    Mem.Concrete.load_int _ ann h plain hn bytes, Mem.Concrete.access_int _ ann h, bind,
    Except.bind, pure, Except.pure] at hr'
  subst hr'
  exact ⟨_, memory_reaches (by intro o h; cases h) hr⟩

/-- `kill(int, p)` of a live `int` object. -/
theorem kill_apply (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State} {id addr : Int}
    (h : LiveInt m id addr) :
    Reaches file labels
      ⟨.apply (.memory (.kill (intType ann))) [.object (.pointer (.allocated id addr))], k, m⟩
      ⟨.value .unit, k, { m with
        allocations := m.allocations.erase id
        dead := id :: m.dead
        lastUsed := some id }⟩ :=
  memory_reaches (name := "Kill") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest, Mem.Concrete.kill_int _ ann h,
      bind, Except.bind, pure, Except.pure])

end Silmaril.Compile.Core.Verified.Actions
