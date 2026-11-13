module

public import Silmaril.Compiler.Core.Verified.State.Defs
public import Silmaril.Cerberus.Core.CallReach.Defs

/-! # State blocks returning to a procedure caller

The State recogniser is shared with the main fragment. These source-side lemmas run
its statements under a procedure-return frame, preserving arbitrary caller frames.
They reuse the expression, store, lifetime and branch proofs of `StateStmt`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateProc

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval Reaches tagsOf)
open Mem.Concrete (LiveInt nextIntAddress)
open Locals (Slot)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open ConvInt (IsInt)
open IntExpr (spec)
open StateExpr (Key Term values close)
open StateMem (Local Inv Fresh Defined defsOf update ptr)
open StateStmt
open State (stmts block classify classify_spec closeSize maxSize update_key)

variable {file : Program} {labels L : Labels} {caller : List Frame}

/-- A reserve for a block's own allocations, below any caller-owned objects.
Dead allocations may precede the fresh id; the base need not be the startup address. -/
structure Reserve (base : Int) (m : Mem.Concrete.State) (ls : List Local) : Prop where
  dead : ∀ id ∈ m.dead, id < m.nextId
  ids : ∀ l ∈ ls, l.id < m.nextId
  addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr
  last : m.lastAddress = base - 4 * ls.length
  aligned : base % 4 = 0
  room : 4096 < base

theorem Reserve.nextIntAddress {base : Int} {m : Mem.Concrete.State} {ls : List Local}
    (h : Reserve base m ls) : nextIntAddress m = m.lastAddress - 4 := by
  simp only [Mem.Concrete.nextIntAddress, h.last]
  have := h.aligned
  omega

/-- Startup is one instance of the reserve; callers may supply a lower base. -/
theorem Reserve.ofFresh {m : Mem.Concrete.State} {ls : List Local} (h : Fresh m ls) :
    Reserve StartupReach.errnoAddr m ls := by
  refine ⟨?_, h.ids, h.addrs, h.last, ?_, ?_⟩
  · simp [h.dead]
  · decide
  · decide

/-- The nearest boundary retains this callee's labels and its caller. -/
def Context (L : Labels) (caller k : List Frame) : Prop :=
  procedureContext labels k = (L, .procedureReturn L :: caller)

theorem context_cons {k : List Frame} (hk : Context (labels := labels) L caller k)
    {f : Frame} (hf : NoBoundary [f]) : Context (labels := labels) L caller (f :: k) := by
  cases f <;> simp_all [Context, NoBoundary, hasBoundary, procedureContext]

/-- A State expression returned to this procedure's boundary, or source overflow. -/
def Returns (s : State) (t : IntExpr.Term) (out : String) : Prop :=
  (t.Ok 0 ∧ ∃ m', m'.stdout = out ∧ Reaches file labels s
    ⟨.value (IntExpr.spec (t.val 0)), .procedureReturn L :: caller, m'⟩) ∨
  Overflows (file := file) (labels := labels) s

theorem Returns.pre {s s' : State} {t : IntExpr.Term} {out : String}
    (h : Reaches file labels s s')
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) s' t out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) s t out := by
  rcases o with ⟨ok, m', hout, r⟩ | ub
  · exact .inl ⟨ok, m', hout, h.trans r⟩
  · exact .inr (Overflows.pre h ub)

/-- The saved return label discards the callee's local frames, retaining its boundary. -/
theorem jump_returns {ret l : Sym} (hl : l.key = ret.key) (hret : ReturnLabel L ret)
    (v : Val) (env : Env) {k : List Frame} (hk : Context (labels := labels) L caller k)
    (m : Mem.Concrete.State) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels
      ⟨.value v, .runLabel l [] [] env :: k, m⟩
      ⟨.value v, .procedureReturn L :: caller, m'⟩ := by
  obtain ⟨r, bann, pann, r', hr, hlook⟩ := hret
  have hlook' : L.lookup l = some ([r], .mk bann (.pure (.mk pann () (.sym r')))) := by
    rw [ReturnLit.lookup_key hl]; exact hlook
  refine ⟨SeqReach.focusMemory bann m, by simp, ?_⟩
  exact (LoopReach.run_arguments_reaches .nil [] v _ _ m L [r] _ hk hlook' rfl).trans
    (SeqReach.effect_pure_reaches bann (SeqReach.pure_symbol pann r' _ v (ConvInt.lookup_one hr)) _ m)

theorem killsRun_returns {ret u : Sym} (hret : ReturnLabel L ret) :
    (xs : List Sym) → (ls : List Local) → Keys ls xs → (xs.map (·.key)).Nodup →
    {e : Eff} → killsRun file ret u xs e = true → (env : Env) → {k : List Frame} → Context (labels := labels) L caller k →
    (m : Mem.Concrete.State) →
    (∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ ls, LiveInt m l.id l.addr) →
    (∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    {v : Int} → IsInt v → env.lookup u = some (spec v) →
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value (spec v), .procedureReturn L :: caller, m'⟩
  | [], ls, hls, _, e, h, env, k, hk, m, _, _, _, v, hv, hu => by
    obtain ⟨rann, l, cann, a3, c3, a4, s, u', rfl, hl, hu', hs⟩ := killsRun_nil h
    have heval : Eval file (tagsOf file (focusMemory rann m)) env
        (.inl (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])))
        (.inl (spec v)) :=
      ConvInt.convLoadedInt_eval (ann := c3) hs hv
        (.cons .val (.cons (.sym (by rw [ReturnLit.lookup_key hu']; exact hu)) .nil))
    obtain ⟨m', out, halts⟩ := jump_returns hl hret (spec v) env hk (focusMemory rann m)
    refine ⟨m', by simp [out], ?_⟩
    refine (Straight.focus_reaches (m := m) Straight.request_run).trans ?_
    exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
  | x :: xs, ls, hls, nodup, e, h, env, k, hk, m, henv, hlive, hids, v, hv, hu => by
    cases ls with
    | nil => cases hls
    | cons l ls =>
      simp only [Keys, List.map_cons, List.cons.injEq] at hls
      obtain ⟨hxl, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := killsRun_cons h
      obtain ⟨kann, kill⟩ := WrapObj.killAny_reaches (file := file) (labels := labels) hkl env
        (.strongBind (.mk pann (.base (none, ty))) rest env :: k) m
        (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) (hlive l (by simp))
      let m₁ := Locals.killed (focusMemory kann m) l.id
      have ne : ∀ l' ∈ ls, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ ls.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls, e, hxl] at hm
        exact hm
      obtain ⟨m', out, reach⟩ := killsRun_returns hret xs ls hls nodup hrest env hk m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => StateMem.live_killed (Locals.liveInt_focus kann (hlive l' (by simp [hl'])))
          l.id (ne l' hl'))
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb])) hv hu
      refine ⟨m', by rw [out]; simp [m₁, Locals.killed], ?_⟩
      exact (ReturnConst.sequence_reaches file labels ann _ _ rest env k m).trans (kill.trans
        ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit rest env k m₁).trans reach))

/-- **`return e;`** shows the value of the closed expression, or undefined behaviour. -/
theorem ret_returns {ret : Sym} (hret : ReturnLabel L ret) {xs : List Sym} {e : Eff} {t : Term}
    (h : retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.key)).Nodup) (hd : Defined ds t = true) {k : List Frame}
    (hk : Context (labels := labels) L caller k) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ⟨.effectExpr e env, k, m⟩
      (close (defsOf ds) t) m.stdout := by
  unfold retStmt at h
  split at h
  · rename_i ann pann u ty bann e' kr
    split at h
    · rename_i cond
      obtain ⟨hfresh, hkr⟩ := cond
      let σ := values (defsOf ds)
      let K := Frame.strongBind (.mk pann (.base (some u, ty))) kr env :: k
      have pre : Reaches file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr)) env,
            k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
        (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
          (ReturnLit.bound_reaches bann _ env _ m)
      refine Returns.pre pre ?_
      have locs := inv.locs hd
      by_cases ok : t.Ok σ
      · left
        refine ⟨StateExpr.close_ok _ t (inv.defs_ok hd) ok, ?_⟩
        obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
          t h ok (.bound :: K) m locs
        let v := spec (t.val σ)
        have inv₁ := (inv.touched tch).extend (x := u) (v := v) (hls.fresh hfresh)
        obtain ⟨m', out, reach⟩ := killsRun_returns hret xs ls hls nodup hkr (extendEnv [(u, v)] env) hk m₁
          inv₁.env inv₁.live (fun a ha b hb ne => (inv₁.apart a ha b hb ne).1)
          (StateExpr.Term.int_of_ok t ok) (ConvInt.lookup_one rfl)
        refine ⟨m', by rw [out, tch.stdout], ?_⟩
        rw [StateExpr.close_val]
        exact (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr v K m₁).trans
          ((ReturnLit.bind_reaches pann u ty v kr env k m₁).trans reach))
      · right
        exact fails_overflows (StateExpr.term_fails (file := file) (labels := labels) t h ok
          (.bound :: K) m locs)
    · cases h
  · cases h


theorem ifRet_runs {ret : Sym} (hret : ReturnLabel L ret) {xs : List Sym} {e : Eff}
    {tc ta : Term} (h : ifRet file ret xs e = some (tc, ta)) {env : Env} {m : Mem.Concrete.State}
    {ls : List Local} {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.key)).Nodup) (hdc : Defined ds tc = true) (hda : Defined ds ta = true)
    {k : List Frame} (hk : Context (labels := labels) L caller k) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    (tc.Ok (values (defsOf ds)) ∧ tc.val (values (defsOf ds)) ≠ 1 ∧
      Returns (file := file) (labels := labels) (L := L) (caller := caller) ⟨.effectExpr e env, k, m⟩
        (close (defsOf ds) ta) m.stdout) ∨
    (tc.Ok (values (defsOf ds)) ∧ tc.val (values (defsOf ds)) = 1 ∧ ∃ m', m'.stdout = m.stdout ∧
      Inv env m' ls ds ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩) := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', ea, a7, a8, rfl, hb', hcb, hfc,
    hfb, htc, hta⟩ := ifRet_inv h
  let σ := values (defsOf ds)
  let PU : EE := .mk a7 (.pure (.mk a8 () (.val .unit)))
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea PU)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  by_cases okc : tc.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc)
    let cv := tc.val σ
    let env₁ := extendEnv [(c, spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cv
      (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    let m₃ := SeqReach.focusMemory a5 m₂
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then ea else PU) env₂, k, m₃⟩ :=
      (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have tch₃ : LoadTask.Touched m m₃ := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    have inv₃ : Inv env m₃ ls ds := inv.touched tch₃
    by_cases h1 : cv = 1
    · right
      refine ⟨okc, h1, focusMemory a7 m₃, by simp [tch₃.stdout], inv₃.focus a7, ?_⟩
      have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr PU env₂, k, m₃⟩ := by simpa [flag, h1] using enter
      exact pre.trans (enter'.trans (pure_unit_reaches a7 a8 env₂ k m₃))
    · left
      refine ⟨okc, h1, ?_⟩
      have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr ea env₂, k, m₃⟩ := by simpa [flag, h1] using enter
      have inv₂ : Inv env₂ m₃ ls ds := (inv₃.extend (hls.fresh hfc)).extend (hls.fresh hfb)
      have o := ret_returns hret hta inv₂ hls nodup hda hk
      rw [tch₃.stdout] at o
      exact Returns.pre (pre.trans enter') o
  · left
    exact Overflows.pre pre (fails_overflows (StateExpr.term_fails (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc)))


theorem shows_choose_left {s : State} {C A B : IntExpr.Term} {out : String} (okC : C.Ok 0)
    (h1 : C.val 0 ≠ 1) (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) s A out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) s (StmtIf.choose C A B) out := by
  rcases o with ⟨okA, m', hout, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okA]⟩, m', hout, ?_⟩
    rw [StmtIf.choose_val, ite_eq_right h1]; exact r
  · exact .inr ub

/-- The selection shows its second branch when the test is `1`. -/
theorem shows_choose_right {s : State} {C A B : IntExpr.Term} {out : String} (okC : C.Ok 0)
    (h1 : C.val 0 = 1) (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) s B out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) s (StmtIf.choose C A B) out := by
  rcases o with ⟨okB, m', hout, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okB]⟩, m', hout, ?_⟩
    rw [StmtIf.choose_val, ite_eq_left h1]; exact r
  · exact .inr ub

/-- **The statements** show the value of the closed expression, or undefined behaviour. -/
theorem stmts_returns {ret : Sym} (hret : ReturnLabel L ret) {xs : List Sym}
    (nodup : (xs.map (·.key)).Nodup) (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (e : Eff)
    {T : IntExpr.Term} (h : stmts file ret xs ds sz e = some T) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls ds) (hls : Keys ls xs) (k : List Frame) (hk : Context (labels := labels) L caller k) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ⟨.effectExpr e env, k, m⟩ T m.stdout := by
  unfold stmts at h
  split at h
  next ann pann ty s rest =>
    let K := Frame.strongBind (.mk pann (.base (none, ty))) rest env :: k
    have hK : Context (labels := labels) L caller K := context_cons hk (by simp [NoBoundary, hasBoundary])
    have pre : Reaches file labels ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (none, ty))) s rest))
        env, k, m⟩ ⟨.effectExpr s env, K, m⟩ :=
      ReturnConst.sequence_reaches file labels ann _ s rest env k m
    refine Returns.pre pre ?_
    split at h
    next t hc =>
      split at h
      next hd =>
        cases h
        exact ret_returns hret (classify_spec hc) inv hls nodup hd.1 hK
      next => cases h
    next c a hc =>
      split at h
      next hd =>
        cases hr : stmts file ret xs ds sz rest with
        | none => simp [hr] at h
        | some Tr =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h
          have okC := fun okc => StateExpr.close_ok (defsOf ds) c (inv.defs_ok hd.1) okc
          rcases ifRet_runs hret (classify_spec hc) inv hls nodup hd.1 hd.2.1 hK with
            ub | ⟨okc, h1, o⟩ | ⟨okc, h1, m', out, inv', reach⟩
          · exact .inr ub
          · exact shows_choose_left (okC okc) (by rw [StateExpr.close_val]; exact h1) o
          · have o := stmts_returns hret nodup ds sz rest hr env m' ls inv' hls k hk
            rw [out] at o
            exact shows_choose_right (okC okc) (by rw [StateExpr.close_val]; exact h1)
              (Returns.pre (reach.trans (ReturnConst.wildcard_sequence_reaches file labels pann ty
                .unit rest env k m')) o)
      next => cases h
    next x t hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
        rw [update_key hx] at h
        rcases assign_runs (classify_spec hc) inv hl hx hd.2.1 K with ub | ⟨-, m', out, inv', reach⟩
        · exact .inr ub
        · have o := stmts_returns hret nodup _ _ rest h env m' ls inv' hls k hk
          rw [out] at o
          exact Returns.pre (reach.trans (ReturnConst.wildcard_sequence_reaches file labels pann ty
            .unit rest env k m')) o
      next => cases h
    next x t hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
        rw [update_key hx] at h
        rcases init_runs (classify_spec hc) inv hl hx hd.2.1 K with ub | ⟨-, m', ys, out, inv', reach⟩
        · exact .inr ub
        · have o := stmts_returns hret nodup _ _ rest h env m' ls inv' hls (.annotations ys :: k)
            (context_cons hk (by simp [NoBoundary, hasBoundary]))
          rw [out] at o
          exact Returns.pre (reach.trans (Locals.annotations_bind_reaches ys pann ty .unit rest env k m'))
            o
      next => cases h
    next x hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd
        rw [update_key hx] at h
        obtain ⟨m', ys, out, inv', reach⟩ := uninit_runs (classify_spec hc) inv hl hx K
        have o := stmts_returns hret nodup _ _ rest h env m' ls inv' hls (.annotations ys :: k)
          (context_cons hk (by simp [NoBoundary, hasBoundary]))
        rw [out] at o
        exact Returns.pre (reach.trans (Locals.annotations_bind_reaches ys pann ty .unit rest env k m')) o
      next => cases h
    next => cases h
  next => cases h
termination_by sizeOf e


theorem block_returns {base : Int} {ret : Sym} (hret : ReturnLabel L ret) (xs : List Sym) (e : Eff)
    {T : IntExpr.Term} (h : block file ret xs e = some T) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls (fun _ => none)) (hls : Keys ls xs) (fresh : Reserve base m ls)
    (k : List Frame) (hk : Context (labels := labels) L caller k) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ⟨.effectExpr e env, k, m⟩ T m.stdout := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold block at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlt⟩ := hc
      obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := State.createInt_inv hcr
      have hnext : nextIntAddress m = m.lastAddress - 4 := fresh.nextIntAddress
      have hpos : 0 < nextIntAddress m := by
        rw [hnext, fresh.last, hlen]
        have := fresh.room
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
      have inv₁ : Inv env₁ m₁ (ls ++ [nl]) (fun _ => none) := by
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
              (by
                rw [State.focus_dead, State.focus_nextId]
                intro hd
                have := fresh.dead m.nextId hd
                omega)
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
        · intro q d hd; cases hd
      have hls₁ : Keys (ls ++ [nl]) (xs ++ [x]) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
        rw [hls]
      have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
        rw [Locals.created_lastAddress, Locals.nextIntAddress_focus, hnext]
      have fresh₁ : Reserve base m₁ (ls ++ [nl]) := by
        refine ⟨?_, ?_, ?_, ?_, fresh.aligned, fresh.room⟩
        · intro id hd
          rw [Locals.created_dead, State.focus_dead] at hd
          have := fresh.dead id hd
          rw [State.created_nextId, State.focus_nextId]
          omega
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
      have o := block_returns hret (xs ++ [x]) rest h env₁ m₁ (ls ++ [nl]) inv₁ hls₁ fresh₁ k hk
      have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
      rw [out] at o
      exact Returns.pre ((ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
        (create.trans bind)) o
    next => cases h
  next =>
    split at h
    next nodup => exact stmts_returns hret nodup _ _ e h env m ls inv hls k hk
    next => cases h
termination_by sizeOf e

/-- A recognised State body returns its value to the procedure's caller. -/
theorem body_returns {base : Int} {body : EE} {t : IntExpr.Term}
    (h : State.recognizeBody file body = some t) (env : Env) (caller : List Frame)
    (m : Mem.Concrete.State) (fresh : Reserve base m []) :
    Returns (file := file) (labels := labels) (L := CallReach.bodyLabels body) (caller := caller)
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: caller, m⟩ t m.stdout := by
  unfold State.recognizeBody at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      refine Returns.pre (ReturnConst.sequence_reaches file labels ann _ a _ env _ m) ?_
      let body : EE := .mk ann (.sseq (.mk pann (.base (none, bt0))) a
        (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))))
      have hret : ReturnLabel (CallReach.bodyLabels body) ret := by
        refine ⟨r, bann, pann', r', hr, ?_⟩
        simp [body, CallReach.bodyLabels, saves, StmtIf.labelFree_saves a hfree, Map.ofList]
      exact block_returns hret [] a h env m []
        ⟨by simp, by simp, by simp, fun _ _ hd => by cases hd⟩ rfl fresh
        (.strongBind (.mk pann (.base (none, bt0))) _ env ::
          .procedureReturn (CallReach.bodyLabels body) :: caller) rfl
    · cases h
  · cases h

end Silmaril.Compile.Core.Verified.StateProc
