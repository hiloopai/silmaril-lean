module

public import Silmaril.Compiler.Core.Verified.CfgGlobals.Defs
public import Silmaril.Compiler.Core.Verified.PrintState.Defs
/-! # CFG locals created below the string literals

With string literals allocated by the startup (`StrLit.initial_reaches_body`), `main`'s block
creates its `int` locals below them (`LoopMain.creates`). Each creation keeps the literals'
objects and bindings, and the facts a print statement needs (`PrintMem.Facts`): no dead
allocation, the locals allocated before the frontier, the literals above every local.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgPrintStart

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Mem.Concrete (nextIntAddress)
open StateMem (Local Inv ptr)
open StateStmt (Keys)
open StateExpr (Key)
open ReturnConst (focusMemory)
open ReturnLit (Eff)
open LoopMain (creates)
open PrintMem (Lit LookOk MemOk Above)
open StrMem (Keeps)

variable {file : Program} {labels : Labels}

/-- **Creating the locals** below the literals: the slots, the literals and the print facts
are kept, and the frontier stays above `2 ^ 47` less 8 bytes per local. -/
theorem creates_reaches (xs : List Sym) (e : Eff) {ys : List Sym} {e' : Eff}
    (h : creates xs e = some (ys, e')) (L : List Lit) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (look : LookOk L env) (apart : ∀ o ∈ L, ∀ y ∈ ys, o.sym.key ≠ y.key) (dead : m.dead = [])
    (earlier : PrintfState.Earlier m ls) (hlits : MemOk L m) (above : Above L ls)
    (room : 2 ^ 47 - 8 * (ls.length : Int) ≤ m.lastAddress) (k : List Frame) :
    ∃ env' m' ls', Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.effectExpr e' env', k, m'⟩ ∧
      Inv env' m' ls' ds ∧ Keys ls' ys ∧ m'.stdout = m.stdout ∧ LookOk L env' ∧ m'.dead = [] ∧
      PrintfState.Earlier m' ls' ∧ MemOk L m' ∧ Above L ls' ∧
      2 ^ 47 - 8 * (ls'.length : Int) ≤ m'.lastAddress := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold creates at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlt⟩ := hc
      obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := State.createInt_inv hcr
      have hna : nextIntAddress m + 4 ≤ m.lastAddress ∧ m.lastAddress - 8 < nextIntAddress m := by
        unfold nextIntAddress; omega
      have hpos : 0 < nextIntAddress m := by
        have : (ls.length : Int) < 1024 := by rw [hlen]; exact_mod_cast hlt
        omega
      let REST := rest
      let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
      have create := Locals.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
        pref env K m hpos
      rw [State.focus_nextId] at create
      let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
      let m₁ := Actions.created pref c2 (focusMemory ann m)
      have hC : WrapObj.Created (focusMemory ann m) m₁ := WrapObj.created_int pref c2 _
      have keep : Keeps m m₁ := (PrintState.keeps_focus ann m).trans (PrintfArg.created_keeps pref c2 _)
      let env₁ := extendEnv [(x, ptr nl)] env
      have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
      have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
      have ids : ∀ l ∈ ls, l.id < m.nextId := earlier.ids
      have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := earlier.addrs
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
              (by rw [State.focus_dead, dead, State.focus_nextId]; simp)
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
      have last₁ : m₁.lastAddress = nextIntAddress m := by
        rw [hC.last, Locals.nextIntAddress_focus]
      have next₁ : m₁.nextId = m.nextId + 1 := by rw [hC.next, State.focus_nextId]
      have hxy : x ∈ ys :=
        (CfgGlobals.creates_sublist (xs ++ [x]) rest h).subset (List.mem_append_right _ (by simp))
      have look₁ : LookOk L env₁ :=
        PrintMem.LookOk.extend look (fun o ho => apart o ho x hxy) _
      have earlier₁ : PrintfState.Earlier m₁ (ls ++ [nl]) := by
        refine ⟨?_, ?_⟩
        · intro l hl
          rw [next₁]
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
            exact le_refl _
      have lits₁ : MemOk L m₁ := fun o ho => ⟨(hlits o ho).1.keeps keep, (hlits o ho).2⟩
      have above₁ : Above L (ls ++ [nl]) := by
        intro o ho l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact above o ho l hl
        · obtain rfl := List.mem_singleton.mp hl
          have := (hlits o ho).1.above
          show nextIntAddress m + 4 ≤ o.addr
          omega
      have room₁ : 2 ^ 47 - 8 * ((ls ++ [nl]).length : Int) ≤ m₁.lastAddress := by
        rw [last₁, List.length_append, List.length_singleton]
        push_cast
        omega
      have dead₁ : m₁.dead = [] := by rw [hC.dead, State.focus_dead, dead]
      obtain ⟨env', m', ls', reach, inv', hls', out', look', dead', earlier', lits', above', room'⟩ :=
        creates_reaches (xs ++ [x]) rest h L env₁ m₁ (ls ++ [nl]) inv₁ hls₁ look₁ apart dead₁ earlier₁
          lits₁ above₁ room₁ k
      have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
      exact ⟨env', m', ls', (ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
        (create.trans (bind.trans reach)), inv', hls', out'.trans out, look', dead', earlier', lits',
        above', room'⟩
    next => cases h
  next =>
    cases h
    exact ⟨env, m, ls, .refl, inv, hls, rfl, look, dead, earlier, hlits, above, room⟩
termination_by sizeOf e

end Silmaril.Compile.Core.Verified.CfgPrintStart
