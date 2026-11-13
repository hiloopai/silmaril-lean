module

public import Silmaril.Compiler.Core.Source.StartupReach.Defs

/-! # Startup of `main(argc, argv)` in the Core dynamics

For a `main` with two parameters, the dynamics (`Dynamics.requestAux`, `enterMain` and
`mainArgs`) creates and initialises the objects of `Startup.objects`: one `char` array per
argument string, the `argv` array of `char *`, and (normal calling convention) the `int` and
`char **` parameter objects. `createStore` and `startObjects` say what this does to the memory as
functions of the concrete memory model; `mainArgs_reaches` proves that the dynamics follows
them, for every file, label map, continuation and memory.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.StartupArgs

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.StartupReach (Reaches step_reaches)
open Mem.Concrete (Tags Pointer MemoryValue Failure typeLayout allocateTyped storeTyped accessTyped
  updateLastAllocation readonlyKind unatomic)

/-- One startup object, as `mainArgs` creates it (`Create` with the type's alignment) and
initialises it (`Store` of its contents). -/
def createStore (tags : Tags) (m : Mem.Concrete.State) (obj : Startup.Object) (value : MemoryValue) :
    Except Failure (Pointer × Mem.Concrete.State) := do
  let l ← typeLayout 64 tags obj.type
  let (p, m1) ← allocateTyped tags m l.align obj.type
  let m1 := updateLastAllocation m1 fun a => {a with readonlyKind := readonlyKind obj.allocationPrefix}
  let n ← toMemory (unatomic obj.type) (fromMemory value)
  let (_, m2) ← storeTyped tags m1 obj.type p n
  pure (p, m2)

/-- The startup objects in order; each one's contents may point at the earlier ones. -/
def startObjects (tags : Tags) : Mem.Concrete.State → List Startup.Object → List Pointer →
    Except Failure (List Pointer × Mem.Concrete.State)
  | m, [], ptrs => pure (ptrs, m)
  | m, obj :: rest, ptrs => do
    let v ← Startup.contents ptrs obj.contents
    let (p, m') ← createStore tags m obj v
    startObjects tags m' rest (ptrs ++ [p])

/-- One startup object: `Create`, `Store`, then the next object, under one more annotation frame. -/
theorem mainArgs_step (file : Program) (labels : Labels) (obj : Startup.Object)
    (rest : List Startup.Object) (ptrs : List Pointer) (ps : List Sym) (c : Control)
    (k : List Frame) (m : Mem.Concrete.State) {v : MemoryValue} {p : Pointer} {m' : Mem.Concrete.State}
    (hv : Startup.contents ptrs obj.contents = .ok v)
    (h : createStore file.tagDefs m obj v = .ok (p, m')) :
    ∃ xs, Reaches file labels ⟨.mainArgs (obj :: rest) ptrs ps c, k, m⟩
      ⟨.mainArgs rest (ptrs ++ [p]) ps c, .annotations xs :: k, m'⟩ := by
  simp only [createStore, bind, Except.bind, pure, Except.pure] at h
  split at h; · exact absurd h (by simp)
  rename_i l hl
  split at h; · exact absurd h (by simp)
  rename_i pm1 halloc
  obtain ⟨p1, m1⟩ := pm1
  split at h; · exact absurd h (by simp)
  rename_i n hn
  split at h; · exact absurd h (by simp)
  rename_i r2 hstore
  obtain ⟨fp, m2⟩ := r2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  dsimp only at hstore
  let m1' := updateLastAllocation m1 fun a => {a with readonlyKind := readonlyKind obj.allocationPrefix}
  obtain ⟨⟨id, addr, size⟩, hacc⟩ : ∃ r, accessTyped file.tagDefs m1' obj.type p1 = .ok r := by
    simp only [storeTyped, bind, Except.bind] at hstore
    split at hstore
    · simp at hstore
    · exact ⟨_, by assumption⟩
  obtain ⟨xs, hreq⟩ : ∃ xs, request file labels
      ⟨.value (.object (.pointer p1)), .mainObject obj.type v (.mainArgs rest ptrs ps c) :: k, m1'⟩ =
      .memory "Store" m2 (.value .unit) (.annotations xs :: .mainNext p1 (.mainArgs rest ptrs ps c) :: k) := by
    have hstore' : storeTyped file.tagDefs m1' obj.type p1 n = .ok (fp, m2) := hstore
    simp [request, requestAux, awaitsScheduling, memoryRequest, hn, hacc, hstore', bind, Except.bind,
      pure, Except.pure]
  refine ⟨xs, .trans (step_reaches (r := .memory "Create" m1' (.value (.object (.pointer p1)))
      (.mainObject obj.type v (.mainArgs rest ptrs ps c) :: k)) (by intro o; simp) ?_ .memory)
    (.trans (step_reaches (by intro o; simp) hreq .memory)
    (step_reaches (r := .next (.mainArgs rest (ptrs ++ [p1]) ps c) (.annotations xs :: k))
      (by intro o; simp) ?_ .next))⟩
  · simp only [request, requestAux, awaitsScheduling, memoryRequest, hv, hl, integer, halloc]
    simp [bind, Except.bind, pure, Except.pure, m1']
  · simp [request, requestAux, awaitsScheduling]

/-- All startup objects, in order. -/
theorem mainArgs_reaches (file : Program) (labels : Labels) (ps : List Sym) (c : Control) :
    ∀ (objs : List Startup.Object) (ptrs : List Pointer) (k : List Frame) (m : Mem.Concrete.State)
      {ptrs' : List Pointer} {m' : Mem.Concrete.State},
      startObjects file.tagDefs m objs ptrs = .ok (ptrs', m') →
      ∃ fs, Reaches file labels ⟨.mainArgs objs ptrs ps c, k, m⟩ ⟨.mainArgs [] ptrs' ps c, fs ++ k, m'⟩
  | [], ptrs, k, m, ptrs', m', h => by
    simp only [startObjects, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], .refl⟩
  | obj :: rest, ptrs, k, m, ptrs', m', h => by
    simp only [startObjects, bind, Except.bind] at h
    split at h; · exact absurd h (by simp)
    rename_i v hv
    split at h; · exact absurd h (by simp)
    rename_i r hr
    obtain ⟨p, m1⟩ := r
    obtain ⟨xs, reach⟩ := mainArgs_step file labels obj rest ptrs ps c k m hv hr
    obtain ⟨fs, reach'⟩ := mainArgs_reaches file labels ps c rest (ptrs ++ [p]) _ m1 h
    exact ⟨fs ++ [.annotations xs], by simpa using reach.trans reach'⟩

/-- The parameter values of a `main(argc, argv)` with the normal calling convention: pointers
to the last two startup objects. -/
def paramValues (ptrs : List Pointer) : List Val :=
  (ptrs.drop (ptrs.length - 2)).map fun p => .object (.pointer p)

/-- After the last startup object, `main`'s body starts with its parameters bound. -/
theorem mainArgs_done (file : Program) (labels : Labels) (ptrs : List Pointer) (ps : List Sym)
    (body : EE) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    (normal : file.callingConvention = .normal) :
    Reaches file labels ⟨.mainArgs [] ptrs ps (.effectExpr body env), k, m⟩
      ⟨.startup (.effectExpr body (extendEnv (ps.zip (paramValues ptrs)) env)), k, m⟩ :=
  step_reaches (r := .next (.startup (.effectExpr body (extendEnv (ps.zip (paramValues ptrs)) env))) k)
    (by intro o; simp) (by simp [request, requestAux, awaitsScheduling, normal, paramValues]) .next

/-- The `errno` object as `Dynamics.startup` creates it (with the file's tags and the memory's
enum registrations) and sets it to `0` (with empty tags). -/
def createErrno (tags : Tags) (m : Mem.Concrete.State) : Except Failure (Pointer × Mem.Concrete.State) := do
  let (p, m1) ← allocateTyped tags m 4 StartupReach.intTy
  let m1 := updateLastAllocation m1 fun a => {a with readonlyKind := readonlyKind (.other "errno")}
  let (_, m2) ← storeTyped ∅ m1 StartupReach.intTy p (.integer (.signed .int) 0)
  pure (p, m2)

/-- `startup c` from any memory in which `errno` can be created and set to `0`: the stack is
replaced by the store's annotation frame, and the location is `Driver.drive`. -/
theorem startup_reaches (file : Program) (labels : Labels) (c : Control) (k : List Frame)
    (m : Mem.Concrete.State) {p : Pointer} {m' : Mem.Concrete.State}
    (h : createErrno ⟨file.tagDefs, m.enumTypes⟩ m = .ok (p, m')) :
    ∃ xs, Reaches file labels ⟨.startup c, k, m⟩
      ⟨c, [.annotations xs], {m' with currentLocation := .other "Driver.drive"}⟩ := by
  simp only [createErrno, bind, Except.bind, pure, Except.pure] at h
  split at h; · exact absurd h (by simp)
  rename_i pm1 halloc
  obtain ⟨p1, m1⟩ := pm1
  split at h; · exact absurd h (by simp)
  rename_i r2 hstore
  obtain ⟨fp, m2⟩ := r2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  dsimp only at hstore
  let m1' := updateLastAllocation m1 fun a => {a with readonlyKind := readonlyKind (.other "errno")}
  have hstore' : storeTyped ∅ m1' StartupReach.intTy p1 (.integer (.signed .int) 0) = .ok (fp, m2) :=
    hstore
  obtain ⟨⟨id, addr, size⟩, hacc⟩ : ∃ r, accessTyped ∅ m1' StartupReach.intTy p1 = .ok r := by
    simp only [storeTyped, bind, Except.bind] at hstore'
    split at hstore'
    · simp at hstore'
    · exact ⟨_, by assumption⟩
  obtain ⟨xs, hreq⟩ : ∃ xs, request file labels ⟨.value (.object (.pointer p1)), [.startupStore c], m1'⟩ =
      .memory "Store" m2 (.value .unit) [.annotations xs, .startupEnter c] := by
    have hacc' : accessTyped ∅ m1' (Ctype.mk [] (.basic (.integer (.signed .int)))) p1 =
      .ok (id, addr, size) := hacc
    have hstore'' : storeTyped ∅ m1' (Ctype.mk [] (.basic (.integer (.signed .int)))) p1
      (.integer (.signed .int) 0) = .ok (fp, m2) := hstore'
    simp [request, requestAux, awaitsScheduling, memoryRequest, hacc', hstore'', bind, Except.bind,
      pure, Except.pure, toMemory, objectMemory, unatomic, intType]
  refine ⟨xs, .trans (step_reaches (r := .memory "Create" m1' (.value (.object (.pointer p1)))
      [.startupStore c]) (by intro o; simp) ?_ .memory)
    (.trans (step_reaches (by intro o; simp) hreq .memory)
    (step_reaches (r := .update {m2 with currentLocation := .other "Driver.drive"} c [.annotations xs])
      (by intro o; simp) ?_ .update))⟩
  · have halloc' : allocateTyped ⟨file.tagDefs, m.enumTypes⟩ m 4
        (Ctype.mk [] (.basic (.integer (.signed .int)))) = .ok (p1, m1) := halloc
    simp [request, requestAux, awaitsScheduling, memoryRequest, integer, halloc', bind, Except.bind,
      pure, Except.pure, m1']
  · simp [request, requestAux, awaitsScheduling]

/-- **Startup of `main(argc, argv)`.** From the initial state of a file without global
definitions whose `main` is a procedure with two parameters (normal calling convention), the
dynamics creates the startup objects (`startObjects`), then `errno` (`createErrno`), and reaches
`main`'s body with `argc` and `argv` bound to pointers to the last two objects, under one
annotation frame. -/
theorem initial_reaches_body_args (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {argc argv : Sym}
    {tc tv : BaseType} {body : EE}
    (nodefs : ∀ x ∈ file.globs, ∀ bt e, x.2 ≠ .definition bt e)
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [(argc, tc), (argv, tv)] body))
    (normal : file.callingConvention = .normal)
    {objs : List Startup.Object} (hobjs : Startup.objects args false loc sym argc argv = .ok objs)
    {ptrs : List Pointer} {m1 : Mem.Concrete.State}
    (hstart : startObjects file.tagDefs {enumTypes := enums} objs [] = .ok (ptrs, m1))
    {pe : Pointer} {m2 : Mem.Concrete.State}
    (herrno : createErrno ⟨file.tagDefs, m1.enumTypes⟩ m1 = .ok (pe, m2)) :
    ∃ s labels xs, initial file enums args = .ok (s, labels) ∧
      Reaches file labels s ⟨.effectExpr body (extendEnv ([argc, argv].zip (paramValues ptrs)) ∅),
        [.annotations xs], {m2 with currentLocation := .other "Driver.drive"}⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  have hinit : initial file enums args =
      .ok (⟨.globals [] args ∅, [], {enumTypes := enums}⟩, labels) := by
    simp only [initial]
    rw [List.filterMap_eq_nil_iff.mpr]
    · simp [main, decl, labels]
    · rintro ⟨_, _ | _⟩ hx
      · exact absurd rfl (nodefs _ hx _ _)
      · rfl
  obtain ⟨fs, hargs⟩ := mainArgs_reaches file labels [argc, argv] (.effectExpr body ∅) objs [] [] _ hstart
  obtain ⟨xs, herr⟩ := startup_reaches file labels
    (.effectExpr body (extendEnv ([argc, argv].zip (paramValues ptrs)) ∅)) (fs ++ []) m1 herrno
  refine ⟨_, labels, xs, hinit, ?_⟩
  refine .trans (step_reaches (r := .next (.enterMain args ∅) []) (by intro o; simp) ?_ .next) ?_
  · simp [request, requestAux, awaitsScheduling]
  refine .trans (step_reaches (r := .next (.mainArgs objs [] [argc, argv] (.effectExpr body ∅)) [])
    (by intro o; simp) ?_ .next) ?_
  · simp [request, requestAux, awaitsScheduling, main, decl, normal, hobjs]
  exact hargs.trans ((mainArgs_done file labels ptrs [argc, argv] body ∅ _ m1 normal).trans herr)

end Silmaril.Cerberus.Core.StartupArgs
