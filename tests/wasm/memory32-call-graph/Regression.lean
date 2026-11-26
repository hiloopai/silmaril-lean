module

import Silmaril.Wasm.Institution.Operational.Memory32Graph.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Value Frame FuncAddr MemAddr MemInst)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall (Declaration CallTarget)
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix (Discard)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

namespace Silmaril.Wasm.Institution.Operational.Memory32Graph

private abbrev word := Value.int .i32
private def before : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩
private def after : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def mem : MemInst := ⟨before, some 1⟩
private def other : MemInst := ⟨⟨#[19]⟩, none⟩
private def memAddr : MemAddr := ⟨1⟩
private def leafAddr : FuncAddr := ⟨0⟩
private def midAddr : FuncAddr := ⟨1⟩
private def rootAddr : FuncAddr := ⟨2⟩

private def declaration (funcs : List FuncAddr) (results : List NumType) : Declaration :=
  ⟨{ funcs, memories := [memAddr] }, ⟨0⟩, [], [], results⟩

private def leaf (trap : Bool) : Function :=
  ⟨declaration [] [], (if trap then [Value.int .i64 9, word 3] else []) ++ [word 1, word 0x11223344],
    if trap then [.store, .load, .unreachable] else [.store]⟩

private def leafCall (trap : Bool) : CallTarget := ⟨⟨0⟩, leafAddr, (leaf trap).decl⟩
private def mid (trap : Bool) : Function := ⟨declaration [leafAddr] [], [], [.call (leafCall trap)]⟩
private def midCall (trap : Bool) : CallTarget := ⟨⟨0⟩, midAddr, (mid trap).decl⟩

private def callerBody (trap : Bool) : Function :=
  ⟨declaration [midAddr] [i32], [word 1], [.call (midCall trap), .load]⟩

private def program (trap : Bool) : Program := [some (leaf trap), some (mid trap), some (callerBody trap)]
private def target (trap : Bool) : CallTarget := ⟨⟨0⟩, rootAddr, (callerBody trap).decl⟩
private def caller : Frame := ⟨[Value.int .i64 7], { funcs := [rootAddr] }⟩

private theorem root (trap : Bool) : Root (program trap) caller (target trap) (callerBody trap) := ⟨rfl, rfl, rfl⟩

private theorem located {trap : Bool} {a : FuncAddr} {f : Function}
    (found : (program trap).lookup a = some f) :
    (a = leafAddr ∧ f = leaf trap) ∨ (a = midAddr ∧ f = mid trap) ∨
      (a = rootAddr ∧ f = callerBody trap) := by
  rcases a with ⟨_ | _ | _ | n⟩ <;> simp [Program.lookup, program, leafAddr, midAddr, rootAddr] at found ⊢
  all_goals exact found.symm

private theorem checked (trap : Bool) : (program trap).Checked := by
  intro addr f found
  rcases located found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases trap
    · exact .store (saved := []) rfl (.done rfl)
    · exact .store (saved := [.int .i64, i32]) rfl (.load (saved := [.int .i64]) rfl .unreachable)
  · exact .call (saved := []) rfl rfl rfl rfl (.done rfl)
  · exact .call (saved := [i32]) rfl rfl rfl rfl (.load (saved := []) rfl (.done rfl))

private def limeBase (trap : Bool) : Lime1.Execution.Store Unit :=
  { memories := [other, mem], funcs := [leaf trap, mid trap, callerBody trap].map
      (fun f => .wasm f.decl.type f.decl.module f.limeFunc) }

private def coreBase (trap : Bool) : Core.Store Unit :=
  { mems := [other.toCore, mem.toCore], funcs := [leaf trap, mid trap, callerBody trap].map Function.coreInstance }

private theorem limeLayout (trap : Bool) : LimeLayout (program trap) (limeBase trap) memAddr mem where
  mem := rfl
  funcs := by intro a f h; rcases located h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  slot := by intro a f h; rcases located h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

private theorem coreLayout (trap : Bool) : CoreLayout (program trap) (coreBase trap) memAddr mem.toCore where
  mem := rfl
  width := rfl
  funcs := by intro a f h; rcases located h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  slot := by intro a f h; rcases located h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

private def start : State := ⟨before, .call []⟩
private def atLeaf (trap : Bool) (q : Phase) : Phase :=
  .active [] [word 1] (midCall trap) (.active [] [] (leafCall trap) q []) [.load]

private theorem reaches (trap : Bool) : Runs (program trap) (callerBody trap) start
    ⟨before, atLeaf trap (.running [] (leaf trap).initial (leaf trap).code)⟩ := by
  apply Relation.ReflTransGen.head (b := ⟨before, .invoke []⟩) .resolve
  apply Relation.ReflTransGen.head (b := ⟨before, .running [] [word 1] [.call (midCall trap), .load]⟩) .enter
  apply Relation.ReflTransGen.head (b := ⟨before, .pending [] [word 1] (midCall trap) [] [.load]⟩) (.call (saved := [word 1]) (args := []) rfl)
  apply Relation.ReflTransGen.head
    (b := ⟨before, .active [] [word 1] (midCall trap) (.running [] [] [.call (leafCall trap)]) [.load]⟩)
    (.pending (callee := mid trap) rfl)
  apply Relation.ReflTransGen.head
    (b := ⟨before, .active [] [word 1] (midCall trap) (.pending [] [] (leafCall trap) [] []) [.load]⟩)
    (.active rfl (.call (saved := []) (args := []) rfl))
  exact .single (.active rfl (.pending (callee := leaf trap) rfl))

private theorem write : Memory32Context.Edge before (.store 1 0x11223344) (.written after) :=
  .store (MemoryWrite.fact (.write _ _ _ (by decide)))

private theorem loadWritten : Memory32Context.Edge after (.load 1) (.value 0x11223344) :=
  .load (MemoryQuery.fact (.load _ _ (by decide)))

private theorem bounds : Memory32Context.Edge after (.load 3) .trap :=
  .loadTrap (MemoryQuery.fact (.loadTrap _ (by decide)))

private def returned : State := ⟨after, .done (.values [word 0x11223344])⟩
private def trapped : State := ⟨after, .done .trap⟩
private def firstTrap : State :=
  ⟨after, atLeaf true (.trapped [] [Value.int .i64 9] [.unreachable])⟩

private theorem success : Runs (program false) (callerBody false) start returned := by
  refine (reaches false).trans ?_
  apply Relation.ReflTransGen.head (b := ⟨after, atLeaf false (.running [] [] [])⟩)
    (.active rfl (.active rfl (.store (saved := []) write)))
  apply Relation.ReflTransGen.head (b := ⟨after, atLeaf false (.exit [] (.values []))⟩)
    (.active rfl (.active rfl .complete))
  apply Relation.ReflTransGen.head (b := ⟨after, .active [] [word 1] (midCall false) (.running [] [] []) [.load]⟩)
    (.active rfl (.active rfl .exit))
  apply Relation.ReflTransGen.head
    (b := ⟨after, .active [] [word 1] (midCall false) (.exit [] (.values [])) [.load]⟩)
    (.active rfl .complete)
  apply Relation.ReflTransGen.head (b := ⟨after, .running [] [word 1] [.load]⟩) (.active rfl .exit)
  apply Relation.ReflTransGen.head (b := ⟨after, .running [] [word 0x11223344] []⟩)
    (.load (saved := []) loadWritten)
  exact (Relation.ReflTransGen.single Step.complete).tail .exit

private theorem hitsBounds : Runs (program true) (callerBody true) start firstTrap := by
  refine (reaches true).trans ?_
  apply Relation.ReflTransGen.head
    (b := ⟨after, atLeaf true (.running [] [Value.int .i64 9, word 3] [.load, .unreachable])⟩)
    (.active rfl (.active rfl (.store (saved := [Value.int .i64 9, word 3]) write)))
  exact .single (.active rfl (.active rfl (.load (saved := [Value.int .i64 9]) bounds)))

private theorem unwinds : Runs (program true) (callerBody true) firstTrap trapped := by
  apply Relation.ReflTransGen.head (b := ⟨after, atLeaf true (.trapped [] [] [.unreachable])⟩)
    (.active rfl (.active rfl (.discard (.cut [] [Value.int .i64 9] [] [.unreachable] (by simp)))))
  apply Relation.ReflTransGen.head (b := ⟨after, atLeaf true (.trapped [] [] [])⟩)
    (.active rfl (.active rfl (.discard (.cut [] [] [.unreachable] [] (by simp)))))
  apply Relation.ReflTransGen.head (b := ⟨after, atLeaf true (.exit [] .trap)⟩)
    (.active rfl (.active rfl .trapExit))
  apply Relation.ReflTransGen.head
    (b := ⟨after, .active [] [word 1] (midCall true) (.trapped [] [] []) [.load]⟩)
    (.active rfl (.active rfl .exit))
  apply Relation.ReflTransGen.head (b := ⟨after, .active [] [word 1] (midCall true) (.exit [] .trap) [.load]⟩)
    (.active rfl .trapExit)
  apply Relation.ReflTransGen.head (b := ⟨after, .trapped [] [word 1] [.load]⟩) (.active rfl .exit)
  apply Relation.ReflTransGen.head (b := ⟨after, .trapped [] [] [.load]⟩)
    (.discard (.cut [] [word 1] [] [Op.load] (by simp)))
  apply Relation.ReflTransGen.head (b := ⟨after, .trapped [] [] []⟩)
    (.discard (.cut [] [] [Op.load] [] (by simp)))
  exact (Relation.ReflTransGen.single Step.trapExit).tail .exit

private def limeCfg (trap : Bool) := limeConfig (limeBase trap) memAddr mem caller (target trap)
private def coreCfg (trap : Bool) := coreConfig (coreBase trap) memAddr mem.toCore caller (target trap)

example : Core.Steps Numerics.Profile.spec noHost (coreCfg false start) (coreCfg false returned) :=
  (core_run_iff (checked false) (coreLayout false) (root false) (.call rfl)).mpr
    ⟨returned, success, .done rfl, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeCfg false start) (limeCfg false returned) :=
  (lime_run_iff (checked false) (limeLayout false) (root false) (.call rfl)).mpr
    ⟨returned, success, .done rfl, rfl, rfl⟩

example : Core.Steps Numerics.Profile.spec noHost (coreCfg true start) (coreCfg true firstTrap) :=
  (core_run_iff (checked true) (coreLayout true) (root true) (.call rfl)).mpr
    ⟨firstTrap, hitsBounds,
      .active rfl rfl rfl trivial (.active rfl rfl rfl trivial .trapped (.done rfl))
        (.load (saved := []) rfl (.done rfl)), rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeCfg true start) (limeCfg true trapped) :=
  (lime_run_iff (checked true) (limeLayout true) (root true) (.call rfl)).mpr
    ⟨trapped, hitsBounds.trans unwinds, .done trivial, rfl, rfl⟩

example : Core.Steps Numerics.Profile.spec noHost (coreCfg true start) (coreCfg true trapped) :=
  (core_run_iff (checked true) (coreLayout true) (root true) (.call rfl)).mpr
    ⟨trapped, hitsBounds.trans unwinds, .done trivial, rfl, rfl⟩

example : (coreCfg true trapped).store.mems =
    [other.toCore, { mem.toCore with bytes := after }] := rfl
example : (limeCfg true trapped).store.memories = [other, { mem with data := after }] := rfl
example : (coreCfg true firstTrap).store = (coreCfg true trapped).store := rfl
example : (limeCfg true firstTrap).store = (limeCfg true trapped).store := rfl
example : (coreCfg false returned).frame = caller.toCore := rfl
example : (limeCfg true trapped).frame = caller := rfl

example : ¬ Typed (program false) (callerBody false).decl [.int .i64] [.load] := by
  intro code
  cases code with
  | load h _ =>
    have := congrArg List.getLast? h
    simp at this

-- A cyclic descriptor can enter a second activation before the finite
-- observation stops. The same memory is visible in that activation.
private def selfDecl : Declaration := declaration [leafAddr] []
private def selfCall : CallTarget := ⟨⟨0⟩, leafAddr, selfDecl⟩
private def self : Function := ⟨selfDecl, [word 1, word 0x11223344], [.store, .call selfCall]⟩
private def cycle : Program := [some self]
private def cycleCaller : Frame := ⟨caller.locals, { funcs := [leafAddr] }⟩
private def recursivePrefix : State := ⟨after, .active [] [] selfCall (.running [] [] [.call selfCall]) []⟩

private theorem cycleEntry {a : FuncAddr} {f : Function} (h : cycle.lookup a = some f) :
    a = leafAddr ∧ f = self := by
  rcases a with ⟨_ | a⟩ <;> simp [cycle, Program.lookup, leafAddr] at h ⊢
  exact h.symm

private theorem cycleChecked : cycle.Checked := by
  intro addr f h
  obtain ⟨rfl, rfl⟩ := cycleEntry h
  exact .store (saved := []) rfl (.call (saved := []) rfl rfl rfl rfl (.done rfl))

private theorem cycleRun : Runs cycle self start recursivePrefix := by
  apply Relation.ReflTransGen.head (b := ⟨before, .invoke []⟩) .resolve
  apply Relation.ReflTransGen.head (b := ⟨before, .running [] self.initial self.code⟩) .enter
  apply Relation.ReflTransGen.head (b := ⟨after, .running [] [] [.call selfCall]⟩) (.store (saved := []) write)
  apply Relation.ReflTransGen.head (b := ⟨after, .pending [] [] selfCall [] []⟩)
    (.call (saved := []) (args := []) rfl)
  apply Relation.ReflTransGen.head (b := ⟨after, .active [] [] selfCall (.running [] self.initial self.code) []⟩)
    (.pending (callee := self) rfl)
  exact .single (.active rfl (.store (saved := []) (Memory32Context.Edge.store
    (MemoryWrite.fact (.write _ _ _ (by decide))))))

private def cycleCore : Core.Store Unit :=
  { mems := [other.toCore, mem.toCore], funcs := [self.coreInstance] }

private theorem cycleCoreLayout : CoreLayout cycle cycleCore memAddr mem.toCore where
  mem := rfl
  width := rfl
  funcs := by intro a f h; obtain ⟨rfl, rfl⟩ := cycleEntry h; rfl
  slot := by intro a f h; obtain ⟨rfl, rfl⟩ := cycleEntry h; rfl

private def cycleLime : Lime1.Execution.Store Unit :=
  { memories := [other, mem], funcs := [.wasm selfDecl.type selfDecl.module self.limeFunc] }

private theorem cycleLimeLayout : LimeLayout cycle cycleLime memAddr mem where
  mem := rfl
  funcs := by intro a f h; obtain ⟨rfl, rfl⟩ := cycleEntry h; rfl
  slot := by intro a f h; obtain ⟨rfl, rfl⟩ := cycleEntry h; rfl

private theorem cycleRoot : Root cycle cycleCaller selfCall self := ⟨rfl, rfl, rfl⟩
private theorem recursiveReady : Ready cycle self recursivePrefix.phase :=
  .active rfl rfl rfl trivial (.running rfl (.call (saved := []) rfl rfl rfl rfl (.done rfl))) (.done rfl)

example : Core.Steps Numerics.Profile.spec noHost
    (coreConfig cycleCore memAddr mem.toCore cycleCaller selfCall start)
    (coreConfig cycleCore memAddr mem.toCore cycleCaller selfCall recursivePrefix) :=
  (core_run_iff cycleChecked cycleCoreLayout cycleRoot (.call rfl)).mpr
    ⟨recursivePrefix, cycleRun, recursiveReady, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeConfig cycleLime memAddr mem cycleCaller selfCall start)
    (limeConfig cycleLime memAddr mem cycleCaller selfCall recursivePrefix) :=
  (lime_run_iff cycleChecked cycleLimeLayout cycleRoot (.call rfl)).mpr
    ⟨recursivePrefix, cycleRun, recursiveReady, rfl, rfl⟩

end Silmaril.Wasm.Institution.Operational.Memory32Graph
