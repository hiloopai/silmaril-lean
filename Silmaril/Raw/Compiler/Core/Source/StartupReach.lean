module

public import Silmaril.Compiler.Core.Spec.Defs

/-! # Startup of a `main` without parameters, in the Core dynamics

The Core dynamics (`Silmaril.Cerberus.Core.Dynamics`) starts a document by evaluating its
global definitions, then enters `main`. For a `main` procedure without parameters it
allocates `errno` (a signed `int`, Cerberus's driver.lem), stores `0` in it and starts the
body with the location `Driver.drive`. `enter_main_reaches` proves that this administrative
startup reaches the body, for every file, label map, argument list, environment and enum
registration, without writing to stdout. Every later fragment of the verified Core compiler
starts its source simulation there.

The memory facts are about the concrete memory model (`Mem.Concrete`): an `int` has the
layout `4, 4` whatever the tags, `writeRepresentation` changes only the byte maps, and the
`errno` object is allocated at `errnoAddr` from a fresh memory and accepts the store.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.StartupReach

open Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete (Tags Allocation Representation typeLayout allocateTyped accessTyped storeTyped
  writeRepresentation plainBytes encodeInteger updateLastAllocation readonlyKind checkAtomic checkWritable
  represent unatomic registeredIntegerLayout registeredInteger integerLayout baseWidth representationBounds)

/-- The source relation of the specification: any transition of the Core LTS. -/
abbrev Reaches (file : Program) (labels : Labels) :=
  Relation.ReflTransGen (Silmaril.Compile.Core.Spec.coreStep file labels)

/-- `int`, the type of `errno`. -/
def intTy : Ctype := Ctype.mk [] (.basic (.integer (.signed .int)))

/-- `int` has size and alignment 4 under every tag map (enums do not matter for it). -/
theorem layout_int (tags : Tags) : typeLayout 64 tags intTy = .ok ⟨4, 4, []⟩ := by
  simp [typeLayout, intTy, registeredIntegerLayout, registeredInteger,
    integerLayout, baseWidth]; rfl

/-- Writing a representation changes only the byte maps. -/
theorem writeRepresentation_shape (a : Int) (bs : Representation) (s : Mem.Concrete.State) :
    ∃ b pb, writeRepresentation a bs s = {s with bytes := b, pointerBytes := pb} := by
  induction bs generalizing a with
  | nil => exact ⟨s.bytes, s.pointerBytes, rfl⟩
  | cons x bs ih =>
    obtain ⟨b, pb, h⟩ := ih (a + 1)
    rcases x with ⟨y, prov⟩
    simp only [writeRepresentation, h]
    exact ⟨_, _, rfl⟩

/-- The address of `errno` in a fresh memory: the top of the address space, aligned. -/
def errnoAddr : Int := 281474976710648

/-- The `errno` allocation in a memory that has allocated nothing yet. -/
theorem alloc_errno (tags : Tags) (s : Mem.Concrete.State) (hlast : s.lastAddress = 281474976710655) :
    ∃ b pb, allocateTyped tags s 4 intTy = .ok (.allocated s.nextId errnoAddr,
      { s with
        bytes := b
        pointerBytes := pb
        nextId := s.nextId + 1
        lastAddress := errnoAddr
        allocations := s.allocations.insert s.nextId
          ({base := errnoAddr, size := 4, objectType := some intTy} : Allocation)
        lastUsed := some s.nextId }) := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape errnoAddr (plainBytes [none, none, none, none]) s
  refine ⟨b, pb, ?_⟩
  simp only [allocateTyped, layout_int, hlast, bind, Except.bind, pure, Except.pure]
  norm_num
  rw [show (281474976710648 : Int) = errnoAddr from rfl]
  simp [h, intTy]

/-- An `int` access at the start of the `errno` object is in bounds. -/
theorem access_errno (tags : Tags) (m : Mem.Concrete.State) (id : Int)
    (hlook : m.allocations.lookup id = some {base := errnoAddr, size := 4, objectType := some intTy})
    (hdead : id ∉ m.dead) :
    accessTyped tags m intTy (.allocated id errnoAddr) = .ok (id, errnoAddr, 4) := by
  simp [accessTyped, layout_int, hlook, hdead, bind, Except.bind, pure, Except.pure, checkAtomic]

/-- Storing `0` into `errno` succeeds and keeps stdout. -/
theorem store_errno (tags : Tags) (m : Mem.Concrete.State) (id : Int)
    (hlook : m.allocations.lookup id = some {base := errnoAddr, size := 4, objectType := some intTy})
    (hdead : id ∉ m.dead) :
    ∃ m', storeTyped tags m intTy (.allocated id errnoAddr) (.integer (.signed .int) 0) =
      .ok ((errnoAddr, 4), m') ∧ m'.stdout = m.stdout := by
  obtain ⟨b, pb, h⟩ := writeRepresentation_shape errnoAddr
    (plainBytes (encodeInteger 4 0)) m
  refine ⟨{writeRepresentation errnoAddr (plainBytes (encodeInteger 4 0)) m with lastUsed := some id}, ?_, ?_⟩
  · simp only [storeTyped, access_errno tags m id hlook hdead, bind, Except.bind, pure, Except.pure,
      checkWritable, hlook]
    simp [represent, registeredIntegerLayout, registeredInteger, integerLayout, baseWidth,
      representationBounds, bind, pure, Except.pure, plainBytes, encodeInteger]
  · simp [h]

/-- One transition from a computed request. -/
theorem step_reaches {file : Program} {labels : Labels} {s t : State} {a : Label} {r : Request}
    (live : ∀ o, s.control ≠ .halt o) (h : request file labels s = r) (hr : Respond s.memory r a t) :
    Reaches file labels s t := .single ⟨a, Step.respond live (h ▸ hr)⟩

/-- `startup c` from a fresh memory: create `errno`, store `0`, set the location and continue
with `c` under the store's annotation frame. -/
theorem startup_errno (file : Program) (labels : Labels) (c : Control) (m : Mem.Concrete.State)
    (hlast : m.lastAddress = 281474976710655) (hdead : m.dead = []) :
    ∃ m' xs, m'.stdout = m.stdout ∧
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
  obtain ⟨m2, hstore, hout2⟩ := store_errno ∅ m1 m.nextId hlook hdead1
  refine ⟨{m2 with currentLocation := .other "Driver.drive"},
    [⟨none, [], true, errnoAddr, 4⟩], ?_, ?_⟩
  · simp [hout2, m1, updateLastAllocation, a]
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
      unatomic, intType, access_errno ∅ m1 m.nextId hlook hdead1]
    simp only [intTy] at hstore ⊢
    simp [hstore, bind, Except.bind, pure, Except.pure]
  refine step_reaches (r := .update {m2 with currentLocation := .other "Driver.drive"} c
      [.annotations [⟨none, [], true, errnoAddr, 4⟩]]) (by intro o; simp) ?_ .update
  simp [request, requestAux, awaitsScheduling]

/-- Global initialisation without definitions enters `main`; a `main` procedure without
parameters starts with the `errno` allocation. -/
theorem enter_main_reaches (file : Program) (labels : Labels) (args : List String) (env : Env)
    (m : Mem.Concrete.State) {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    Reaches file labels ⟨.globals [] args env, [], m⟩ ⟨.startup (.effectExpr body env), [], m⟩ := by
  refine .trans (step_reaches (r := .next (.enterMain args env) []) (by intro o; simp) ?_ .next) ?_
  · simp [request, requestAux, awaitsScheduling]
  refine step_reaches (r := .next (.startup (.effectExpr body env)) []) (by intro o; simp) ?_ .next
  simp [request, requestAux, awaitsScheduling, main, decl]

/-- **Startup.** From the initial state of a file without global definitions whose `main`
is a procedure without parameters, the dynamics reaches `main`'s body in the empty
environment, under one annotation frame (the `errno` store), with empty stdout. -/
theorem initial_reaches_body (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (nodefs : ∀ x ∈ file.globs, ∀ bt e, x.2 ≠ .definition bt e)
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    ∃ s labels m xs, initial file enums args = .ok (s, labels) ∧ m.stdout = "" ∧
      Reaches file labels s ⟨.effectExpr body ∅, [.annotations xs], m⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  obtain ⟨m', xs, out, reach⟩ := startup_errno file labels (.effectExpr body ∅)
    ({enumTypes := enums} : Mem.Concrete.State) rfl rfl
  refine ⟨_, labels, m', xs, ?_, by simpa using out,
    (enter_main_reaches file labels args ∅ _ main decl).trans reach⟩
  simp only [initial]
  rw [List.filterMap_eq_nil_iff.mpr]
  · simp [main, decl, labels]
  · rintro ⟨_, _ | _⟩ hx
    · exact absurd rfl (nodefs _ hx _ _)
    · rfl

end Silmaril.Cerberus.Core.StartupReach
