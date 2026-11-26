import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame FuncAddr Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat
open Silmaril.Wasm.Institution.Operational.CallContinuation
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private abbrev t32 : NumType := .int .i32
private abbrev t64 : NumType := .int .i64
private abbrev spec := Numerics.Profile.spec

private def signature : V1.FuncType := ⟨[t32, t32], [t32, t32]⟩
private def ownerType : V1.FuncType := ⟨[t32, t32, t32, t32, t32], [t64, t32, t32]⟩
private def decl : Declaration := ⟨{ types := [signature] }, ⟨0⟩, signature.params, [], signature.results⟩
private def first : Graph.Function := ⟨decl, 0, [i32 1], [.numeric (.get ⟨1⟩)]⟩
private def second : Graph.Function := ⟨decl, 0, [i32 0, i32 77], []⟩
private def owner : Graph.Function :=
  ⟨⟨{ types := [ownerType, signature], tables := [⟨0⟩] }, ⟨0⟩, ownerType.params, [], ownerType.results⟩,
    0, [i64 42], [.unreachable]⟩
private def program : Graph.Program := ⟨[some first, some second, some owner]⟩
private def refs : List (Option FuncAddr) := [some ⟨0⟩, some ⟨1⟩, none]
private def tables : Source.Tables := [⟨refs, some 3⟩]
private def outer : Frame := ⟨[i32 99], { funcs := [⟨2⟩] }⟩
private def locals (restart choose selector next : BitVec 32) : List Value :=
  [i32 restart, i32 0, i32 choose, i32 selector, i32 next]
private def args (next : BitVec 32) : List Value := locals 1 1 0 next
private def indices : List LocalIdx := [⟨3⟩, ⟨2⟩]
private def entry : Loop.Entry :=
  { address := ⟨2⟩, owner, result := none, restart := ⟨0⟩, nextRestart := ⟨1⟩, branchTypes := [],
    choose := ⟨2⟩, op := ⟨⟨1⟩, signature⟩, before := [.get ⟨3⟩, .get ⟨4⟩, .get ⟨3⟩],
    insideTail := indices.map Graph.Op.set ++ [.br ⟨1⟩ []],
    tail := [.numeric (.get ⟨3⟩), .numeric (.get ⟨2⟩)] }

private def repeatGuard : Guard entry program tables := ⟨indices, [], rfl, rfl, rfl, rfl, rfl⟩
private theorem checked (next : BitVec 32) : entry.Checked program tables outer ⟨0⟩ (args next) :=
  ⟨rfl, rfl, rfl, rfl⟩

example : { entry with insideTail := indices.map Graph.Op.set ++ [Graph.Op.br ⟨3⟩ []] }.check program tables = false := rfl
example : { entry with insideTail := indices.map Graph.Op.set ++ [Graph.Op.br ⟨1⟩ [t32]] }.check program tables = false := rfl

private theorem iteration (r choose selector next : BitVec 32) :
    Loop.Runs entry ⟨locals r choose selector next, .enter⟩
      ⟨locals 0 choose selector next, if r = 0 then .readChoice else .branch⟩ := by
  have write := Locals.fact (.set (locals r choose selector next) entry.restart (i32 0) (by change 0 < 5; decide))
  have read : Loop.Runs entry ⟨locals r choose selector next, .enter⟩
      ⟨locals r choose selector next, .writeRestart r 0⟩ :=
    ((Relation.ReflTransGen.single Loop.Edge.enter).tail (.readRestart rfl)).tail (.readNext rfl)
  exact (read.tail (.writeRestart write)).tail .testRestart

private theorem route (selector next : BitVec 32) :
    Loop.Runs entry ⟨locals 0 1 selector next, .enter⟩ ⟨locals 0 1 selector next, .site⟩ :=
  (((iteration 0 1 selector next).tail (.readChoice rfl)).tail .testChoice).tail .enterSite

private theorem exits :
    Loop.Runs entry ⟨locals 0 0 77 1, .enter⟩ ⟨locals 0 0 77 1, .caller⟩ :=
  (((((iteration 0 0 77 1).tail (.readChoice rfl)).tail .testChoice).tail .enterEmpty).tail .leaveEmpty).tail .leaveLoop

private def active (selector next : BitVec 32) : Source.Activation :=
  ⟨entry.frame (locals 0 1 selector next), ⟨⟨0⟩, ⟨⟨refs, some 3⟩, ⟨1⟩, signature⟩⟩,
    ⟨[], [i32 selector, i32 next], selector⟩⟩
private theorem prepared (selector next : BitVec 32) :
    entry.op.prepare program tables (entry.frame (locals 0 1 selector next)) [i32 selector, i32 next, i32 selector] =
      some (active selector next) := rfl
private theorem operands (selector next : BitVec 32) :
    OperandTrace (locals 0 1 selector next) [] entry.before
      [([], entry.before), ([i32 selector], [.get ⟨4⟩, .get ⟨3⟩]), ([i32 selector, i32 next], [.get ⟨3⟩])]
      (.values [i32 selector, i32 next, i32 selector]) :=
  .value (.get rfl) (.value (.get rfl) (.value (.get rfl) (.done _)))

private def firstCall (next : BitVec 32) : Context.Invocation :=
  ⟨(active 0 next).binding.site, (active 0 next).caller, 0, [], [i32 0, i32 next], ⟨0⟩, first⟩
private def secondCall : Context.Invocation :=
  ⟨(active 1 1).binding.site, (active 1 1).caller, 1, [], [i32 1, i32 1], ⟨1⟩, second⟩
private def firstSite (next : BitVec 32) : Site entry program tables (locals 0 1 0 next) :=
  .call (call := firstCall next) (operands 0 next) (prepared 0 next) rfl
private def secondSite : Site entry program tables (locals 0 1 1 1) :=
  .call (call := secondCall) (operands 1 1) (prepared 1 1) rfl
private def nullSite : Site entry program tables (locals 0 1 2 2) :=
  .lookupTrap (operands 2 2) (prepared 2 2) rfl .null

-- The changed local reaches both the operand vector and the table selector.
example : (active 0 1).invocation program = some (firstCall 1) := rfl
example : (active 1 1).invocation program = some secondCall := rfl
example : (firstCall 1).args = [i32 0, i32 1] := rfl
example : secondCall.args = [i32 1, i32 1] := rfl
example : (active 2 2).resolve program = some .null := rfl

private theorem firstDone (next : BitVec 32) :
    program.FrameRuns (firstCall next).address (firstCall next).entered (.done (.values [i32 1, i32 next])) := by
  have edge {a b : Graph.Phase} :=
    (program.frameEdge_iff (a := a) (b := b) (fn := first) (address := ⟨0⟩) rfl).mpr
  have read := Relation.ReflTransGen.single (edge (.numeric (locals := [i32 0, i32 next]) (rest := [])
    (.get (stack := [i32 1]) (i := ⟨1⟩) (v := i32 next) rfl)))
  exact (read.tail (edge (.leaveValues _ _))).tail (edge (.leaveFrame _ _ rfl))

private theorem secondDone :
    program.FrameRuns secondCall.address secondCall.entered (.done (.values [i32 0, i32 77])) := by
  have edge {a b : Graph.Phase} :=
    (program.frameEdge_iff (a := a) (b := b) (fn := second) (address := ⟨1⟩) rfl).mpr
  exact (Relation.ReflTransGen.single (edge (.leaveValues _ _))).tail (edge (.leaveFrame _ _ rfl))

private def result : List Value := [i64 42, i32 77, i32 0]
private theorem finishes :
    program.FrameRuns entry.address (entry.callerPhase (locals 0 0 77 1)) (.done (.values result)) := by
  have edge {a b : Graph.Phase} :=
    (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨2⟩) rfl).mpr
  have read := Relation.ReflTransGen.single (edge (.numeric (locals := locals 0 0 77 1) (rest := entry.tail.drop 1)
    (.get (stack := [i64 42]) (i := ⟨3⟩) (v := i32 77) rfl)))
  have thenRead := read.tail (edge (.numeric (rest := [])
    (.get (stack := [i64 42, i32 77]) (i := ⟨2⟩) (v := i32 0) rfl)))
  exact (thenRead.tail (edge (.leaveValues _ result))).tail (edge (.leaveFrame _ _ rfl))

private theorem trapped :
    program.FrameRuns entry.address (Loop.Resume.entryPhase entry (locals 0 1 2 2) true) (.done .trap) := by
  have edge {a b : Graph.Phase} :=
    (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨2⟩) rfl).mpr
  have cut : Prefix.Discard [i64 42] entry.tail [] [] := by
    simpa only [List.nil_append, List.append_nil] using
      Prefix.Discard.cut [] [i64 42] entry.tail [] (.inl (by simp))
  have discard := Relation.ReflTransGen.single (edge (.discard (locals := locals 0 1 2 2) cut))
  exact (discard.tail (edge (.leaveTrap _))).tail (edge (.leaveFrame _ .trap trivial))

section Witness

variable {A C : Type} {recipes : List Value → Recipe A C → Prop}
private abbrev Path (recipes : List Value → Recipe A C → Prop) :=
  Runs entry program indices recipes

private theorem underControl {a b : Loop.State} (walk : Loop.Runs entry a b) :
    Path recipes (.control a) (.control b) := by
  induction walk with
  | refl => exact .refl
  | tail _ move ih => exact ih.tail (.control move)

private theorem underCallee {call : Context.Invocation} {b : Graph.Phase}
    (found : program.lookup call.address = some call.callee)
    (walk : program.FrameRuns call.address call.entered b) :
    Path recipes (.callee call call.entered) (.callee call b) := by
  suffices Path recipes (.callee call call.entered) (.callee call b) ∧
      (b.LabelOutcome ∨ ∃ out, b = .done out) from this.1
  induction walk with
  | refl => exact ⟨.refl, .inl trivial⟩
  | tail _ move ih =>
    obtain ⟨path, live | ⟨_, rfl⟩⟩ := ih
    · exact ⟨path.tail (.callee live move), Context.entered_frame_edge found live move⟩
    · cases (program.frameEdge_iff found).mp move

private theorem prefixTail (next : Handoff A) (rest : List C) :
    Path recipes (.advance next rest) (.resume next) := by
  induction rest with
  | nil => exact .refl
  | cons _ _ ih => exact ih.head .pending

private theorem throughSite {ls : List Value} {path : Recipe A C}
    (recipe : recipes ls path) (nonempty : path.before ≠ []) :
    Path recipes (.control ⟨ls, .site⟩) (.resume path.next) := by
  rcases path with ⟨before, next⟩
  cases before with
  | nil => exact (nonempty rfl).elim
  | cons head rest => exact (prefixTail next rest).head (.site recipe)

private theorem firstRound (next : BitVec 32)
    (site : Path recipes (.control ⟨locals 0 1 0 next, .site⟩) (.callee (firstCall next) (firstCall next).entered)) :
    Path recipes (.control (entry.initial (args next))) (.control ⟨locals 0 1 next next, .enter⟩) := by
  have boot := underControl (recipes := recipes) ((iteration 1 1 0 next).tail .restart)
  have walked := ((boot.trans (underControl (route 0 next))).trans site).trans
    (underCallee (recipes := recipes) rfl (firstDone next))
  have one : Edge entry program indices recipes (.write (locals 0 1 0 next) [i32 1, i32 next] indices)
      (.write (locals 0 1 next next) [i32 1] [⟨2⟩]) :=
    .write rfl (Locals.fact (.set (locals 0 1 0 next) ⟨3⟩ (i32 next) (by change 3 < 5; decide)))
  have two : Edge entry program indices recipes (.write (locals 0 1 next next) [i32 1] [⟨2⟩])
      (.write (locals 0 1 next next) [] []) :=
    .write rfl (Locals.fact (.set (locals 0 1 next next) ⟨2⟩ (i32 1) (by change 2 < 5; decide)))
  exact (((walked.tail (.return_ one)).tail two).tail .armBranch).tail .restart

private theorem secondRound
    (site : Path recipes (.control ⟨locals 0 1 1 1, .site⟩) (.callee secondCall secondCall.entered)) :
    Path recipes (.control ⟨locals 0 1 1 1, .enter⟩) (.control ⟨locals 0 0 77 1, .caller⟩) := by
  have walked := ((underControl (route 1 1)).trans site).trans (underCallee rfl secondDone)
  have one : Edge entry program indices recipes (.write (locals 0 1 1 1) [i32 0, i32 77] indices)
      (.write (locals 0 1 77 1) [i32 0] [⟨2⟩]) :=
    .write rfl (Locals.fact (.set (locals 0 1 1 1) ⟨3⟩ (i32 77) (by decide)))
  have two : Edge entry program indices recipes (.write (locals 0 1 77 1) [i32 0] [⟨2⟩])
      (.write (locals 0 0 77 1) [] []) :=
    .write rfl (Locals.fact (.set (locals 0 1 77 1) ⟨2⟩ (i32 0) (by decide)))
  exact ((((walked.tail (.return_ one)).tail two).tail .armBranch).tail .restart).trans (underControl exits)

private theorem cleanup (rest : List A) :
    Loop.Resume.Runs (.armTrap (locals 0 1 2 2) [i32 2, i32 2] rest) (.caller (locals 0 1 2 2) true) := by
  have cut : Prefix.Discard [i32 2, i32 2] rest [] [] := by
    simpa only [List.nil_append, List.append_nil] using
      Prefix.Discard.cut [] [i32 2, i32 2] rest [] (.inl (by simp))
  exact ((Relation.ReflTransGen.single (.discard cut)).tail (.leaveTrapArm _)).tail (.leaveLoop _ true)

end Witness

private def coreStore : Core.Store Unit :=
  { funcs := [first.coreInstance, second.coreInstance, entry.coreInstance], tables := tables.map Runtime.TableInst.toCore }
private def limeStore : Lime1.Execution.Store Unit :=
  { funcs := [.wasm decl.type decl.module first.limeFunc, .wasm decl.type decl.module second.limeFunc, entry.limeInstance], tables }

private theorem noTargets (address : FuncAddr) (fn : Graph.Function)
    (found : program.lookup address = some fn) : fn.targets = [] := by
  rcases address with ⟨_ | _ | _ | _⟩ <;> first | cases found; rfl | cases found

private theorem coreLinks : program.CoreLinksAllocated coreStore :=
  fun a fn found _ used => (List.not_mem_nil (noTargets a fn found ▸ used)).elim
private theorem limeLinks : program.LimeLinksAllocated limeStore :=
  fun a fn found _ used => (List.not_mem_nil (noTargets a fn found ▸ used)).elim
private theorem coreTable : Source.Tables.CoreAllocated tables coreStore := by
  intro a table found
  simp [coreStore, List.getElem?_map, found]
private theorem limeTable : Source.Tables.LimeAllocated tables limeStore := fun _ _ found => found

private theorem checkedRefs (active : Source.Activation) (ready : active.Checked program tables) :
    active.binding.site.table.refs = refs := by
  have lookup := ready.table
  have only : active.binding.address.value = 0 := by
    cases index : active.binding.address.value with
    | zero => rfl
    | succ n => simp [tables, index] at lookup
  rw [only] at lookup
  exact congrArg Runtime.TableInst.refs (Option.some.inj lookup).symm

private theorem usedAddr {addr : FuncAddr} (used : some addr ∈ refs) : addr = ⟨0⟩ ∨ addr = ⟨1⟩ := by
  simpa [refs] using used

private theorem coreTargets (active : Source.Activation) (ready : active.Checked program tables) :
    active.binding.site.CoreAllocated program coreStore := by
  intro address fn used found
  rw [checkedRefs active ready] at used
  rcases usedAddr used with rfl | rfl <;> cases found <;> rfl
private theorem limeTargets (active : Source.Activation) (ready : active.Checked program tables) :
    active.binding.site.LimeAllocated program limeStore := by
  intro address fn used found
  rw [checkedRefs active ready] at used
  rcases usedAddr used with rfl | rfl <;> cases found <;> rfl

private abbrev corePaths := coreRecipes entry program tables coreStore outer

private theorem coreFirst (next : BitVec 32) :
    Path corePaths (.control (entry.initial (args next))) (.control ⟨locals 0 1 next next, .enter⟩) :=
  firstRound next (throughSite (path := coreRecipe coreStore outer (firstSite next)) ⟨_, rfl⟩ (List.cons_ne_nil _ _))

private theorem coreSecond :
    Path corePaths (.control ⟨locals 0 1 1 1, .site⟩) (.callee secondCall secondCall.entered) :=
  throughSite (path := coreRecipe coreStore outer secondSite) ⟨_, rfl⟩ (List.cons_ne_nil _ _)

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1))
    (Loop.Resume.coreCallee entry coreStore outer secondCall secondCall.entered) :=
  (Loop.Repeat.core_run_iff (P := spec) (checked 1) repeatGuard rfl coreTable coreTargets coreLinks).mpr
    (.inr (.inl ⟨_, ((coreFirst 1).trans (underControl (route 1 1))).trans coreSecond, rfl⟩))

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1))
    ⟨coreStore, outer.toCore, coreValues result⟩ :=
  (Loop.Repeat.core_run_iff (P := spec) (checked 1) repeatGuard rfl coreTable coreTargets coreLinks).mpr
    (.inr (.inr ⟨.control ⟨locals 0 0 77 1, .caller⟩, (coreFirst 1).trans (secondRound coreSecond), id, _, finishes, rfl⟩))

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 2))
    ⟨coreStore, outer.toCore, [.trap]⟩ := by
  have failed : Path corePaths (.control ⟨locals 0 1 2 2, .site⟩) (.trap (Loop.Resume.coreTrap entry (active 2 2) .null)) :=
    throughSite (path := coreRecipe coreStore outer nullSite) ⟨_, rfl⟩ (List.cons_ne_nil _ _)
  have walk := ((coreFirst 2).trans (underControl (route 2 2))).trans failed
  exact (Loop.Repeat.core_run_iff (P := spec) (checked 2) repeatGuard rfl coreTable coreTargets coreLinks).mpr
    (.inr (.inr ⟨_, walk, id, .inr ⟨_, true, cleanup _, _, trapped, rfl⟩⟩))

private abbrev limePaths := limeRecipes entry program tables limeStore outer

private theorem limeFirst (next : BitVec 32) :
    Path limePaths (.control (entry.initial (args next))) (.control ⟨locals 0 1 next next, .enter⟩) :=
  firstRound next (throughSite (path := limeRecipe limeStore outer (firstSite next)) ⟨_, rfl⟩ (List.cons_ne_nil _ _))

private theorem limeSecond :
    Path limePaths (.control ⟨locals 0 1 1 1, .site⟩) (.callee secondCall secondCall.entered) :=
  throughSite (path := limeRecipe limeStore outer secondSite) ⟨_, rfl⟩ (List.cons_ne_nil _ _)

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1))
    (Loop.Resume.limeCallee entry limeStore outer secondCall secondCall.entered) :=
  (Loop.Repeat.lime_run_iff (checked 1) repeatGuard rfl limeTable limeTargets limeLinks).mpr
    (.inr (.inl ⟨_, ((limeFirst 1).trans (underControl (route 1 1))).trans limeSecond, rfl⟩))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1))
    ⟨limeStore, outer, Lime1.Execution.values result⟩ :=
  (Loop.Repeat.lime_run_iff (checked 1) repeatGuard rfl limeTable limeTargets limeLinks).mpr
    (.inr (.inr ⟨.control ⟨locals 0 0 77 1, .caller⟩, (limeFirst 1).trans (secondRound limeSecond), id, _, finishes, rfl⟩))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 2))
    ⟨limeStore, outer, [.trap]⟩ := by
  have failed : Path limePaths (.control ⟨locals 0 1 2 2, .site⟩) (.trap (Loop.Resume.limeTrap entry (active 2 2))) :=
    throughSite (path := limeRecipe limeStore outer nullSite) ⟨_, rfl⟩ (List.cons_ne_nil _ _)
  have walk := ((limeFirst 2).trans (underControl (route 2 2))).trans failed
  exact (Loop.Repeat.lime_run_iff (checked 2) repeatGuard rfl limeTable limeTargets limeLinks).mpr
    (.inr (.inr ⟨_, walk, id, .inr ⟨_, true, cleanup _, _, trapped, rfl⟩⟩))
