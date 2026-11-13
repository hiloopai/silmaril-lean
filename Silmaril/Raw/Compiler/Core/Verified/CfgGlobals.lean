module

public import Silmaril.Compiler.Core.Verified.LoopMainSound.Defs
public import Silmaril.Compiler.Core.Verified.GlobalsState.Defs

/-! # CFG startup slots and return cleanup

Globals and locals share the register/slot invariant. Creating locals preserves the
initial global definitions; return cleanup selects the slots named by its actual kills.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgGlobals

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Mem.Concrete (nextIntAddress)
open StateMem (Local Inv Fresh ptr)
open StateStmt (Keys)
open StateExpr (Key)
open ReturnConst (focusMemory)
open ReturnLit (Eff)
open LoopMain (creates)
open Silmaril.Machine

variable {file : Program} {labels : Labels}

/-- Creating locals preserves arbitrary earlier slot definitions, including globals. -/
theorem creates_reaches_fresh (xs : List Sym) (e : Eff) {ys : List Sym} {e' : Eff}
    (h : creates xs e = some (ys, e')) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs) (fresh : Fresh m ls)
    (k : List Frame) :
    ∃ env' m' ls', Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.effectExpr e' env', k, m'⟩ ∧
      Inv env' m' ls' ds ∧ Keys ls' ys ∧ m'.stdout = m.stdout ∧ Fresh m' ls' := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold creates at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlt⟩ := hc
      obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := State.createInt_inv hcr
      have hnext : nextIntAddress m = m.lastAddress - 4 := fresh.nextIntAddress
      have hpos : 0 < nextIntAddress m := by
        rw [hnext, fresh.last, hlen]
        simp only [StartupReach.errnoAddr]
        omega
      let REST := rest
      let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
      have create := Locals.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
        pref env K m hpos
      rw [State.focus_nextId] at create
      let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
      let m₁ := Actions.created pref c2 (focusMemory ann m)
      let env₁ := extendEnv [(x, ptr nl)] env
      have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
      have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
      have ids : ∀ l ∈ ls, l.id < m.nextId := fresh.ids
      have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := fresh.addrs
      have inv₁ : Inv env₁ m₁ (ls ++ [nl]) ds := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro l hl y hy
          rcases List.mem_append.mp hl with hl | hl
          · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
            exact inv.env l hl y hy
          · obtain rfl := List.mem_singleton.mp hl
            exact ConvInt.lookup_one hy
        · intro l hl
          rcases List.mem_append.mp hl with hl | hl
          · refine StateMem.live_created (Locals.liveInt_focus ann (inv.live l hl)) pref c2 ?_
            rw [State.focus_nextId]; exact Int.ne_of_lt (ids l hl)
          · obtain rfl := List.mem_singleton.mp hl
            have := Locals.created_live pref c2 (focusMemory ann m)
              (by rw [State.focus_dead, fresh.dead, State.focus_nextId]; simp)
            rwa [Locals.nextIntAddress_focus, State.focus_nextId] at this
        · intro a ha b hb ne
          rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
          · exact inv.apart a ha b hb ne
          · obtain rfl := List.mem_singleton.mp hb
            refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
            have := addrs a ha
            show a.addr + 4 ≤ nextIntAddress m ∨ nextIntAddress m + 4 ≤ a.addr
            omega
          · obtain rfl := List.mem_singleton.mp ha
            refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
            have := addrs b hb
            show nextIntAddress m + 4 ≤ b.addr ∨ b.addr + 4 ≤ nextIntAddress m
            omega
          · obtain rfl := List.mem_singleton.mp ha
            obtain rfl := List.mem_singleton.mp hb
            exact absurd rfl ne
        · intro q d hd
          obtain ⟨ok, l, hl, hk, slot⟩ := inv.defs q d hd
          refine ⟨ok, l, List.mem_append_left _ hl, hk, ?_⟩
          exact (Globals.held_created pref c2
            (Globals.held_focus ann ⟨slot, ids l hl, addrs l hl⟩)).slot
      have hls₁ : Keys (ls ++ [nl]) (xs ++ [x]) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
        rw [hls]
      have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
        rw [Locals.created_lastAddress, Locals.nextIntAddress_focus, hnext]
      have fresh₁ : Fresh m₁ (ls ++ [nl]) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Locals.created_dead, State.focus_dead, fresh.dead]
        · intro l hl
          rw [State.created_nextId, State.focus_nextId]
          rcases List.mem_append.mp hl with hl | hl
          · have := ids l hl; omega
          · obtain rfl := List.mem_singleton.mp hl
            show m.nextId < m.nextId + 1
            omega
        · intro l hl
          rw [last₁]
          rcases List.mem_append.mp hl with hl | hl
          · have := addrs l hl; omega
          · obtain rfl := List.mem_singleton.mp hl
            show m.lastAddress - 4 ≤ nextIntAddress m
            omega
        · rw [last₁, fresh.last, List.length_append, List.length_singleton]
          push_cast
          ring
      obtain ⟨env', m', ls', reach, inv', hls', out', fresh'⟩ :=
        creates_reaches_fresh (xs ++ [x]) rest h env₁ m₁ (ls ++ [nl]) inv₁ hls₁ fresh₁ k
      have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
      exact ⟨env', m', ls', (ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
        (create.trans (bind.trans reach)), inv', hls', out'.trans out, fresh'⟩
    next => cases h
  next =>
    cases h
    exact ⟨env, m, ls, .refl, inv, hls, rfl, fresh⟩
termination_by sizeOf e

/-- The original slots remain among those returned by the creation recognizer. -/
theorem creates_sublist (xs : List Sym) (e : Eff) {ys : List Sym} {e' : Eff}
    (h : creates xs e = some (ys, e')) : xs.Sublist ys := by
  unfold creates at h
  split at h
  · split at h
    · exact (List.sublist_append_left xs [_]).trans (creates_sublist _ _ h)
    · cases h
  · cases h; exact .refl _
termination_by sizeOf e

/-- Keys of the objects killed by the right spine of a return's cleanup. -/
def cleanupKeys : EE → List StateExpr.Key
  | .mk _ (.sseq _ (.mk _ (.action (.mk _ (.mk _ _ (.kill _ (.mk _ () (.sym x))))))) rest) =>
      x.key :: cleanupKeys rest
  | _ => []

/-- The return's cleanup keys, used only to select slots for the existing checked recognizer. -/
def returnKeys : EE → List StateExpr.Key
  | .mk _ (.sseq _ (.mk _ (.bound _)) rest) => cleanupKeys rest
  | _ => []

/-- Selecting slots by key preserves the correspondence of source symbols and slots. -/
theorem keys_filter {ls : List Local} {xs : List Sym} (h : Keys ls xs)
    (p : StateExpr.Key → Bool) :
    Keys (ls.filter fun l => p l.sym.key) (xs.filter fun x => p x.key) := by
  unfold Keys at h ⊢
  simpa only [List.filter_map, Function.comp_def] using congrArg (List.filter p) h

/-- Set startup globals in their allocated registers, with the first definition taking precedence. -/
def seedOps (regs : StateExpr.Key → Mir.Reg) : List (Sym × Int) → List (Lir.Op Mir.Reg)
  | [] => []
  | (x, n) :: gs => seedOps regs gs ++ [.const (regs x.key) (BitVec.ofInt 64 n)]

/-- Runtime initialization establishes exactly the startup definitions. -/
theorem seed_exec (ks : List StateExpr.Key) : (gs : List (Sym × Int)) →
    (∀ g ∈ gs, g.1.key ∈ ks) → (fr : Lir.Frame Mir.Reg) → (mem : Lir.Memory) →
    ∃ fr', Lir.execOps (seedOps (LoopMain.regOf ks) gs) fr mem = some (fr', mem) ∧
      StateLoopStep.Registers (LoopMain.regOf ks) (GlobalsState.defs gs) fr'
  | [], _, fr, mem => ⟨fr, rfl, fun _ _ h => by simp [GlobalsState.defs] at h⟩
  | (x, n) :: gs, keys, fr, mem => by
    obtain ⟨fr', hx, hr⟩ := seed_exec ks gs (fun g hg => keys g (List.mem_cons_of_mem _ hg)) fr mem
    refine ⟨fr'.set (LoopMain.regOf ks x.key) (BitVec.ofInt 64 n), ?_, ?_⟩
    · simp [seedOps, Lir.execOps_append, hx, Lir.execOps, Lir.Op.exec]
    · intro q d hd
      by_cases he : x.key = q
      · simp [GlobalsState.defs, he] at hd
        subst hd
        simp [he, IntExpr.Term.val]
      · have hd' : GlobalsState.defs gs q = some d := by
          simpa [GlobalsState.defs, he] using hd
        have hm : q ∈ ks := by
          unfold GlobalsState.defs at hd'
          obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.mp hd'
          have hq : g.1.key = q := by simpa using List.find?_some hg
          rw [← hq]
          exact keys g (List.mem_cons_of_mem _ (List.mem_of_find?_eq_some hg))
        have ne : LoopMain.regOf ks q ≠ LoopMain.regOf ks x.key := fun eq =>
          he (LoopMain.regOf_inj hm (keys (x, n) List.mem_cons_self) eq).symm
        simpa [Lir.Frame.get, Lir.Frame.set, ne] using hr q d hd'

end Silmaril.Compile.Core.Verified.CfgGlobals
