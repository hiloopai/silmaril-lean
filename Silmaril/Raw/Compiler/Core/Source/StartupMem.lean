module

public import Silmaril.Compiler.Core.Source.StartupReach.Defs

/-! # The memory at the start of `main`

`StartupReach.initial_reaches_body` with what the body's first allocation needs: after the
startup's `errno` allocation the last allocated address is `errnoAddr` (the top of the
address space, aligned), and nothing has been killed. The proof is `startup_errno`'s, with
the memory kept explicit.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.StartupMem

open Silmaril.Cerberus.Core.Dynamics
open StartupReach
open Mem.Concrete (Tags Allocation storeTyped writeRepresentation plainBytes encodeInteger
  updateLastAllocation readonlyKind checkWritable represent registeredIntegerLayout
  registeredInteger integerLayout baseWidth representationBounds)

theorem updateLastAllocation_lastAddress (s : Mem.Concrete.State) (f : Allocation → Allocation) :
    (updateLastAllocation s f).lastAddress = s.lastAddress := by
  unfold updateLastAllocation
  split
  · rfl
  · split <;> rfl

theorem updateLastAllocation_dead (s : Mem.Concrete.State) (f : Allocation → Allocation) :
    (updateLastAllocation s f).dead = s.dead := by
  unfold updateLastAllocation
  split
  · rfl
  · split <;> rfl

theorem writeRepresentation_lastAddress (a : Int) (bs : Mem.Concrete.Representation)
    (s : Mem.Concrete.State) : (writeRepresentation a bs s).lastAddress = s.lastAddress := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape a bs s
  rw [h]

theorem writeRepresentation_dead (a : Int) (bs : Mem.Concrete.Representation)
    (s : Mem.Concrete.State) : (writeRepresentation a bs s).dead = s.dead := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape a bs s
  rw [h]

/-- `startup_errno`, with the memory facts the body needs. -/
theorem startup_errno_mem (file : Program) (labels : Labels) (c : Control) (m : Mem.Concrete.State)
    (hlast : m.lastAddress = 281474976710655) (hdead : m.dead = []) :
    ∃ m' xs, m'.stdout = m.stdout ∧ m'.lastAddress = errnoAddr ∧ m'.dead = [] ∧
      Reaches file labels ⟨.startup c, [], m⟩ ⟨c, [.annotations xs], m'⟩ := by
  obtain ⟨b, pb, halloc⟩ := alloc_errno ⟨file.tagDefs, m.enumTypes⟩ m hlast
  let a : Allocation := {base := errnoAddr, size := 4, objectType := some intTy}
  let m1 : Mem.Concrete.State := updateLastAllocation
    { m with
        bytes := b
        pointerBytes := pb
        nextId := m.nextId + 1
        lastAddress := errnoAddr
        allocations := m.allocations.insert m.nextId a
        lastUsed := some m.nextId }
    fun a => {a with readonlyKind := readonlyKind (.other "errno")}
  have hlook : m1.allocations.lookup m.nextId = some a := by
    simp [m1, updateLastAllocation, a, readonlyKind]
  have hdead1 : m.nextId ∉ m1.dead := by
    simp [m1, updateLastAllocation, a, hdead]
  let m2 : Mem.Concrete.State :=
    {writeRepresentation errnoAddr (plainBytes (encodeInteger 4 0)) m1 with lastUsed := some m.nextId}
  have hstore : storeTyped ∅ m1 intTy (.allocated m.nextId errnoAddr) (.integer (.signed .int) 0) =
      .ok ((errnoAddr, 4), m2) := by
    simp only [storeTyped, access_errno ∅ m1 m.nextId hlook hdead1, bind, Except.bind, pure,
      Except.pure, checkWritable, hlook]
    simp [represent, registeredIntegerLayout, registeredInteger, integerLayout, baseWidth,
      representationBounds, bind, pure, Except.pure, plainBytes, encodeInteger, m2]
  refine ⟨{m2 with currentLocation := .other "Driver.drive"},
    [⟨none, [], true, errnoAddr, 4⟩], ?_, ?_, ?_, ?_⟩
  · obtain ⟨b', pb', h⟩ := writeRepresentation_shape errnoAddr (plainBytes (encodeInteger 4 0)) m1
    have : m1.stdout = m.stdout := by
      simp only [m1]; unfold updateLastAllocation; split
      · rfl
      · split <;> rfl
    simp [m2, h, this]
  · simp [m2, writeRepresentation_lastAddress, m1, updateLastAllocation_lastAddress]
  · simp [m2, writeRepresentation_dead, m1, updateLastAllocation_dead, hdead]
  refine .trans (step_reaches (r := .memory "Create" m1
      (.value (.object (.pointer (.allocated m.nextId errnoAddr)))) [.startupStore c])
      (by intro o; simp) ?_ .memory) ?_
  · simp only [request, requestAux, awaitsScheduling, memoryRequest]
    simp only [show Ctype.mk [] (.basic (.integer (.signed .int))) = intTy from rfl, integer, halloc]
    simp [bind, Except.bind, pure, Except.pure, m1, a]
  refine .trans (step_reaches (r := .memory "Store" m2 (.value .unit)
      [.annotations [⟨none, [], true, errnoAddr, 4⟩], .startupEnter c]) (by intro o; simp) ?_ .memory) ?_
  · simp only [request, requestAux, awaitsScheduling, memoryRequest]
    simp only [show Ctype.mk [] (.basic (.integer (.signed .int))) = intTy from rfl, toMemory, objectMemory,
      Mem.Concrete.unatomic, intType, access_errno ∅ m1 m.nextId hlook hdead1]
    simp only [intTy] at hstore ⊢
    simp [hstore, bind, Except.bind, pure, Except.pure]
  refine step_reaches (r := .update {m2 with currentLocation := .other "Driver.drive"} c
      [.annotations [⟨none, [], true, errnoAddr, 4⟩]]) (by intro o; simp) ?_ .update
  simp [request, requestAux, awaitsScheduling]

/-- **Startup**, with the body's memory: `initial_reaches_body`, and the memory at the body
has `lastAddress = errnoAddr` and no dead allocation. -/
theorem initial_reaches_body_mem (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (nodefs : ∀ x ∈ file.globs, ∀ bt e, x.2 ≠ .definition bt e)
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    ∃ s labels m xs, initial file enums args = .ok (s, labels) ∧ m.stdout = "" ∧
      m.lastAddress = errnoAddr ∧ m.dead = [] ∧
      Reaches file labels s ⟨.effectExpr body ∅, [.annotations xs], m⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  obtain ⟨m', xs, out, hlast, hdead, reach⟩ := startup_errno_mem file labels (.effectExpr body ∅)
    ({enumTypes := enums} : Mem.Concrete.State) rfl rfl
  refine ⟨_, labels, m', xs, ?_, by simpa using out, hlast, hdead,
    (enter_main_reaches file labels args ∅ _ main decl).trans reach⟩
  simp only [initial]
  rw [List.filterMap_eq_nil_iff.mpr]
  · simp [main, decl, labels]
  · rintro ⟨_, _ | _⟩ hx
    · exact absurd rfl (nodefs _ hx _ _)
    · rfl

end Silmaril.Cerberus.Core.StartupMem
