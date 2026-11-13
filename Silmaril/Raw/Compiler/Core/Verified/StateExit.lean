module

public import Silmaril.Compiler.Core.Verified.StateExitResult.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # State statements with process termination

A statement machine over global and local integer slots. Branches choose a termination
flag and an exit expression, both computed by the target at runtime.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.StateExit

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Mem.Concrete (LiveInt nextIntAddress)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open StateExpr (Key Term term values close)
open StateMem (Local Inv Fresh Defined defsOf update ptr)
open StateStmt (isLocal isFresh Keys Overflows pure_unit_reaches)
open StateGlobals (ret_halts ifParts ifParts_size classify classify_spec seqParts seqParts_inv
  seqParts_size exprStmt killsEnd killsEnd_reaches isUnit isUnit_inv termSize budget
  Pending Falls inv_withEnv zeroDefault main_falls)
open State (closeSize maxSize)
open IntExpr (spec)
open ExitCall (Budget)

variable {file : Program} {labels : Labels}

def run (file : File Codec.wireModel Unit Unit) (ret : Sym) (ys xs : List Sym) (fall : Bool) :
    (Key → Option IntExpr.Term) → (Key → Nat) → Nat → Eff → List Eff →
      Option (Result × Nat)
  | _, _, 0, _, _ => none
  | ds, sz, n + 1, e, todo =>
    if AbortCall.abortStmt file e = true then some (.aborting, n) else
    match ExitCall.recognizeBody file e with
    | some v => if -2147483648 ≤ v ∧ v ≤ 2147483647 then some (.returning (.lit v), n) else none
    | none => match _hi : ifParts file ys e with
      | some (tc, ea, eb) =>
        if Defined ds tc = true ∧ closeSize sz tc ≤ maxSize then
          match run file ret ys xs fall ds sz n ea todo with
          | some (ta, n₁) =>
            match run file ret ys xs fall ds sz n₁ eb todo with
            | some (tb, n₂) =>
              if termSize (Result.choose (close (defsOf ds) tc) ta tb).test +
                termSize (Result.choose (close (defsOf ds) tc) ta tb).ret ≤ maxSize then
                some (Result.choose (close (defsOf ds) tc) ta tb, n₂)
              else none
            | none => none
          | none => none
        else none
      | none =>
        match classify file ret ys xs e with
        | some (.ret t) =>
          if Defined ds t = true ∧ closeSize sz t ≤ maxSize then some (.returning (close (defsOf ds) t), n)
          else none
        | some (.assign x t) =>
          if isLocal ys x = true ∧ Defined ds t = true ∧ closeSize sz t ≤ maxSize then
            match todo with
            | [] => none
            | r :: todo =>
              run file ret ys xs fall (update ds x.key (some (close (defsOf ds) t)))
                (fun q => if q = x.key then closeSize sz t else sz q) n r todo
          else none
        | some (.init x t) =>
          if isLocal ys x = true ∧ Defined ds t = true ∧ closeSize sz t ≤ maxSize then
            match todo with
            | [] => none
            | r :: todo =>
              run file ret ys xs fall (update ds x.key (some (close (defsOf ds) t)))
                (fun q => if q = x.key then closeSize sz t else sz q) n r todo
          else none
        | some (.uninit x) =>
          if isLocal ys x = true then
            match todo with
            | [] => none
            | r :: todo => run file ret ys xs fall (update ds x.key none) sz n r todo
          else none
        | _ =>
          match exprStmt file e with
          | some t =>
            if Defined ds t = true ∧ closeSize sz t ≤ maxSize then
              match todo with
              | [] => none
              | r :: todo => run file ret ys xs fall ds sz n r todo
            else none
          | none =>
            match _hs : seqParts e with
            | some (s, rest) =>
              if fall = true ∧ todo.isEmpty = true ∧ killsEnd file xs e = true then some (.returning (.lit 0), n)
              else run file ret ys xs fall ds sz n s (rest :: todo)
            | none =>
              if isUnit e = true then
                match todo with
                | [] => if fall = true ∧ xs.isEmpty = true then some (.returning (.lit 0), n) else none
                | r :: todo => run file ret ys xs fall ds sz n r todo
              else none
termination_by _ _ _ e todo => sizeOf e + (todo.map sizeOf).sum
decreasing_by
  all_goals first
    | (have := (ifParts_size _hi).1; omega)
    | (have := (ifParts_size _hi).2; omega)
    | (have := seqParts_size _hs; simp; omega)
    | (cases e; simp)


theorem run_halts_lt {ret : Sym} (hret : ReturnLabel labels ret) {ys xs : List Sym} {fall : Bool}
    (nodup : (xs.map (·.key)).Nodup) {ls lk : List Local} (hls : Keys ls ys) (hlk : Keys lk xs)
    (sub : ∀ l ∈ lk, l ∈ ls) (N : Nat) :
    ∀ (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (n : Nat) (e : Eff) (todo : List Eff)
      {T : Result} {n' : Nat}, sizeOf e + (todo.map sizeOf).sum < N →
      run file ret ys xs fall ds sz n e todo = some (T, n') → ∀ (env : Env) (m : Mem.Concrete.State),
      Inv env m ls ds → Budget m → ∀ (k : List Frame), Pending (file := file) (labels := labels) ls fall todo k →
      Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ T m.stdout := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ hN; omega
  | succ N ih =>
  intro ds sz n e todo T n' hN h env m inv hb k p
  have he1 : 0 < sizeOf e := by cases e; simp
  unfold run at h
  split at h
  next => cases h
  next n =>
    split at h
    next hab =>
      cases h
      obtain ⟨m', reach, out⟩ := AbortCall.abortStmt_reaches hab env k m
      exact .inl ⟨by simp [Result.Ok, Result.aborting, IntExpr.Term.Ok, IntExpr.Term.val, ConvInt.IsInt],
        m', out, by simpa [Result.outcome, Result.aborting, IntExpr.Term.val] using reach⟩
    next =>
      split at h
      next v hv =>
        split at h
        next hn =>
          cases h
          obtain ⟨m', reach, out⟩ := exit_reaches e hv env k m hb
          apply Shows.of_return
          exact .inl ⟨hn, m', out, reach⟩
        next => cases h
      next =>
        split at h
        next tc ea eb hi =>
          split at h
          next hd =>
            split at h
            next ta n₁ hA =>
              split at h
              next tb n₂ hB =>
                split at h
                next =>
                  cases h
                  rcases StateExitMem.if_runs hi inv hls hd.1 k hb with ub | ⟨okc, env', m', out, inv', hb', reach⟩
                  · exact .inr ub
                  · have okC := StateExpr.close_ok (defsOf ds) tc (inv.defs_ok hd.1) okc
                    by_cases h1 : tc.val (values (defsOf ds)) = 1
                    · simp only [h1, ↓reduceIte] at reach
                      have o := ih ds sz n₁ eb todo (by have := (ifParts_size hi).2; omega) hB env' m' inv' hb' k p
                      rw [out] at o
                      exact shows_choose_right okC (by rw [StateExpr.close_val]; exact h1)
                        (Shows.pre reach o)
                    · simp only [h1, ↓reduceIte] at reach
                      have o := ih ds sz n ea todo (by have := (ifParts_size hi).1; omega) hA env' m' inv' hb' k p
                      rw [out] at o
                      exact shows_choose_left okC (by rw [StateExpr.close_val]; exact h1)
                        (Shows.pre reach o)
                next => cases h
              next => cases h
            next => cases h
          next => cases h
        next hi =>
          split at h
          next t hc =>
            split at h
            next hd =>
              cases h
              exact Shows.of_return (ret_halts hret (classify_spec hc) inv hls hlk sub nodup hd.1 p.noBoundary)
            next => cases h
          next x t hc =>
            split at h
            next hd =>
              split at h
              next => cases h
              next r todo' =>
                obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
                rw [State.update_key hx] at h
                rcases StateExitMem.assignOrRmw_runs (classify_spec hc) inv hl hx hd.2.1 k hb with
                  ub | ⟨-, m', out, inv', hb', reach⟩
                · exact .inr ub
                · obtain ⟨env', k', he, p', r'⟩ := p.resume .unit none m' r todo' rfl
                  have o := ih _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
                    (inv_withEnv inv' he) hb' k' p'
                  rw [out] at o
                  exact Shows.pre (reach.trans r') o
            next => cases h
          next x t hc =>
            split at h
            next hd =>
              split at h
              next => cases h
              next r todo' =>
                obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
                rw [State.update_key hx] at h
                rcases StateExitMem.init_runs (classify_spec hc) inv hl hx hd.2.1 k hb with
                  ub | ⟨-, m', ys', out, inv', hb', reach⟩
                · exact .inr ub
                · obtain ⟨env', k', he, p', r'⟩ := p.resume .unit (some ys') m' r todo' rfl
                  have o := ih _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
                    (inv_withEnv inv' he) hb' k' p'
                  rw [out] at o
                  exact Shows.pre (reach.trans r') o
            next => cases h
          next x hc =>
            split at h
            next hd =>
              split at h
              next => cases h
              next r todo' =>
                obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd
                rw [State.update_key hx] at h
                obtain ⟨m', ys', out, inv', hb', reach⟩ := StateExitMem.uninitAny_runs (classify_spec hc) inv hl hx k hb
                obtain ⟨env', k', he, p', r'⟩ := p.resume .unit (some ys') m' r todo' rfl
                have o := ih _ _ n r todo' (by simp at hN ⊢; omega) h env' m'
                  (inv_withEnv inv' he) hb' k' p'
                rw [out] at o
                exact Shows.pre (reach.trans r') o
            next => cases h
          next =>
            split at h
            next t hx =>
              split at h
              next hd =>
                split at h
                next => cases h
                next r todo' =>
                  rcases StateExitMem.expr_runs hx inv hd.1 k hb with ub | ⟨v, m', out, inv', hb', reach⟩
                  · exact .inr ub
                  · obtain ⟨env', k', he, p', r'⟩ := p.resume v none m' r todo' rfl
                    have o := ih ds sz n r todo' (by simp at hN ⊢; omega) h env' m'
                      (inv_withEnv inv' he) hb' k' p'
                    rw [out] at o
                    exact Shows.pre (reach.trans r') o
              next => cases h
            next hx =>
              split at h
              next s rest hs =>
                obtain ⟨ann, pann, ty, rfl⟩ := seqParts_inv hs
                split at h
                next hk =>
                  cases h
                  obtain ⟨hf, hnil, hke⟩ := hk
                  have hnil' : todo = [] := List.isEmpty_iff.mp hnil
                  obtain ⟨m', out, reach⟩ := killsEnd_reaches (file := file) (labels := labels) [] xs lk hlk
                    nodup hke env k m (fun l hl => inv.env l (sub l hl)) (fun l hl => by simpa [StateStmt.KLive, StateStmt.isLocal] using inv.live l (sub l hl))
                    (fun a ha b hb ne => (inv.apart a (sub a ha) b (sub b hb) ne).1)
                  obtain ⟨m'', out', fin⟩ := p.falls hf hnil' none m'
                  exact Shows.of_return (.inl ⟨show ConvInt.IsInt 0 by constructor <;> omega, m'', out'.trans out,
                    reach.trans fin⟩)
                next =>
                  exact Shows.pre (ReturnConst.sequence_reaches file labels ann _ s rest env k m)
                    (ih ds sz n s (rest :: todo) (by simp at hN ⊢; omega) h env m inv hb _
                      (.bind pann ty rest inv.env p))
              next hs =>
                split at h
                next hu =>
                  obtain ⟨ann, pann, rfl⟩ := isUnit_inv hu
                  split at h
                  next =>
                    split at h
                    next hk =>
                      cases h
                      obtain ⟨hf, hxs⟩ := hk
                      have hxs' : xs = [] := List.isEmpty_iff.mp hxs
                      obtain ⟨m', out, reach⟩ := killsEnd_reaches (file := file) (labels := labels) [] xs lk
                        hlk nodup (e := .mk ann (.pure (.mk pann () (.val .unit)))) (by rw [hxs']; rfl)
                        env k m (fun l hl => inv.env l (sub l hl)) (fun l hl => by simpa [StateStmt.KLive, StateStmt.isLocal] using inv.live l (sub l hl))
                        (fun a ha b hb ne => (inv.apart a (sub a ha) b (sub b hb) ne).1)
                      obtain ⟨m'', out', fin⟩ := p.falls hf rfl none m'
                      exact Shows.of_return (.inl ⟨show ConvInt.IsInt 0 by constructor <;> omega, m'', out'.trans out,
                        reach.trans fin⟩)
                    next => cases h
                  next r todo' =>
                    obtain ⟨env', k', he, p', reach⟩ :=
                      p.resume .unit none (focusMemory ann m) r todo' rfl
                    have o := ih ds sz n r todo' (by simp at hN ⊢; omega) h env' (focusMemory ann m)
                      (inv_withEnv (inv.focus ann) he) (hb.focus ann) k' p'
                    rw [ReturnConst.focusMemory_stdout] at o
                    exact Shows.pre ((pure_unit_reaches ann pann env k m).trans reach) o
                next => cases h

/-- **The statements** show the value of the closed expression, or undefined behaviour. -/
theorem run_halts {ret : Sym} (hret : ReturnLabel labels ret) {ys xs : List Sym} {fall : Bool}
    (nodup : (xs.map (·.key)).Nodup) {ls lk : List Local} (hls : Keys ls ys) (hlk : Keys lk xs)
    (sub : ∀ l ∈ lk, l ∈ ls) (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (n : Nat) (e : Eff)
    (todo : List Eff) {T : Result} {n' : Nat}
    (h : run file ret ys xs fall ds sz n e todo = some (T, n')) (env : Env) (m : Mem.Concrete.State)
    (inv : Inv env m ls ds) (hb : Budget m) (k : List Frame)
    (p : Pending (file := file) (labels := labels) ls fall todo k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ T m.stdout :=
  run_halts_lt hret nodup hls hlk sub _ ds sz n e todo (Nat.lt_succ_self _) h env m inv hb k p

def block (file : File Codec.wireModel Unit Unit) (ret : Sym) (gs : List Sym) (fall : Bool)
    (ds : Key → Option IntExpr.Term) (sz : Key → Nat) : List Sym → Eff → Option Result
  | xs, .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    if Locals.createInt cr = true ∧ isFresh (gs ++ xs) x = true ∧ (gs ++ xs).length < 1024 then
      block file ret gs fall ds sz (xs ++ [x]) rest
    else none
  | xs, e =>
    if (xs.map (·.key)).Nodup ∧ (gs ++ xs).length < 1024 then (run file ret (gs ++ xs) xs fall ds sz budget e []).map (·.1)
    else none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- **The block**: creating its locals after the globals keeps `Fresh` and `Inv`, then its
statements show. -/
theorem block_halts {ret : Sym} (hret : ReturnLabel labels ret) {gs : List Sym} {fall : Bool}
    {ds : Key → Option IntExpr.Term} {sz : Key → Nat} (xs : List Sym) (e : Eff)
    {T : Result} (h : block file ret gs fall ds sz xs e = some T) (env : Env)
    (m : Mem.Concrete.State) (ls lk : List Local) (inv : Inv env m ls ds) (hls : Keys ls (gs ++ xs))
    (hlk : Keys lk xs) (sub : ∀ l ∈ lk, l ∈ ls) (fresh : Fresh m ls) (k : List Frame)
    (hk : NoBoundary k) (falls : fall = true → Falls (file := file) (labels := labels) k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ T m.stdout := by
  have hlen : ls.length = (gs ++ xs).length := by
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
          have held : Globals.Held m l.id l.addr (d.val 0) := ⟨slot, ids l hl, addrs l hl⟩
          exact (Globals.held_created pref c2 (Globals.held_focus ann held)).slot
      have hls₁ : Keys (ls ++ [nl]) (gs ++ (xs ++ [x])) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
        rw [hls, List.append_assoc]
      have hlk₁ : Keys (lk ++ [nl]) (xs ++ [x]) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hlk ⊢
        rw [hlk]
      have sub₁ : ∀ l ∈ lk ++ [nl], l ∈ ls ++ [nl] := by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact List.mem_append_left _ (sub l hl)
        · exact List.mem_append_right _ hl
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
      have o := block_halts hret (xs ++ [x]) rest h env₁ m₁ (ls ++ [nl]) (lk ++ [nl]) inv₁ hls₁ hlk₁
        sub₁ fresh₁ k hk falls
      have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
      rw [out] at o
      exact Shows.pre ((ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
        (create.trans bind)) o
    next => cases h
  next =>
    split at h
    next nd =>
      obtain ⟨nodup, room⟩ := nd
      cases hr : run file ret (gs ++ xs) xs fall ds sz budget e [] with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨T', n'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact run_halts (fall := fall) hret nodup hls hlk sub ds sz budget e [] hr env m inv (by
          refine ⟨?_, by rw [fresh.dead]; simp⟩
          rw [fresh.nextIntAddress, fresh.last, hlen]
          simp only [StartupReach.errnoAddr]
          omega) k (.base hk falls)
    next => cases h
termination_by sizeOf e

/-- The body of `main` over the globals `gs`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (gs : List (Sym × Int)) :
    Eff → Option Result
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, (_, p))] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then
        block file ret (gs.map (·.1)) (zeroDefault p) (GlobalsState.defs gs) (fun _ => 1) [] a
      else none
  | _ => none

/-- The globals are `int`s initialised by literals, with distinct symbols, and `main` is a block
of `int` statements over them and its locals. -/
def recognize (doc : Codec.Document) : Option Result := do
  let ds := Globals.definitions doc.file
  let gs ← Globals.inits doc.file ds
  if (ds.map fun d => d.1.key).Nodup ∧ ds.length < 1024 then do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file gs body
  else none

/-! ## Core side -/

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (t : Result) (h : recognize doc = some t)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s t "" := by
  unfold recognize at h
  cases hgs : Globals.inits doc.file (Globals.definitions doc.file) with
  | none => simp [hgs] at h
  | some gs =>
    simp only [hgs, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i cond
      obtain ⟨nd, room⟩ := cond
      cases main : doc.file.main with
      | none => simp [main] at h
      | some sym =>
        cases decl : doc.file.funs.lookup sym with
        | none => simp [main, decl] at h
        | some entry =>
          cases entry <;> try { simp [main, decl] at h }
          case procedure loc marker ty ps body =>
            cases ps with
            | cons p ps => simp [main, decl] at h
            | nil =>
              have hbody : recognizeBody doc.file gs body = some t := by simpa [main, decl] using h
              obtain ⟨s, m, env, xs, lg, hinit, hout, hkeys, inv, fresh, hentry⟩ :=
                GlobalsState.initial_reaches_state doc.file enums args hgs nd (by omega) main decl
              obtain ⟨labels, hlabels⟩ : ∃ labels : Labels, labels = Map.ofList (saves body).reverse :=
                ⟨_, rfl⟩
              rw [← hlabels] at hinit hentry
              unfold recognizeBody at hbody
              split at hbody
              · rename_i ann pann bt0 a sann ret bt r info p0 bann pann' r'
                split at hbody
                · rename_i cond
                  obtain ⟨hr, hfree⟩ := cond
                  have hret : ReturnLabel labels ret := by
                    rw [hlabels]
                    refine ⟨r, bann, pann', r', hr, ?_⟩
                    simp [saves, StmtIf.labelFree_saves a hfree, Map.ofList]
                  let SAVE : EE :=
                    .mk sann (.save (ret, bt) [(r, (info, p0))] (.mk bann (.pure (.mk pann' () (.sym r')))))
                  have hls : Keys lg (gs.map (·.1) ++ []) := by
                    rw [List.append_nil]
                    unfold Keys
                    have := congrArg (List.map Sym.key) hkeys
                    simp only [List.map_map] at this
                    rw [List.map_map]
                    exact this
                  have o := block_halts hret [] a hbody env m lg [] inv hls rfl (by simp) fresh
                    [.strongBind (.mk pann (.base (none, bt0))) SAVE env, .annotations xs]
                    (by simp [NoBoundary, hasBoundary]) (fun hz => main_falls hr hz env xs)
                  rw [hout] at o
                  exact ⟨s, _, hinit, Shows.pre
                    (hentry.trans (ReturnConst.sequence_reaches doc.file _ ann _ a SAVE env _ m)) o⟩
                · cases hbody
              · cases hbody
    · cases h

/-- The observation selected by the runtime termination flag. -/
def Result.obs (r : Result) : Spec.Obs :=
  if r.test.val 0 = 1 then .exit (r.ret.val 0 % 256).toNat [] else .abort []

theorem recognize_sound (doc : Codec.Document) (r : Result) (h : recognize doc = some r)
    (args : List String) :
    Spec.CoreUB doc args ∨ r.Ok ∧ Spec.CoreBeh doc args r.obs := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc r h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    by_cases flag : r.test.val 0 = 1
    · have beh := Spec.CoreBeh.exit (v := spec (r.ret.val 0)) (k := (r.ret.val 0 % 256).toNat)
        ⟨s, labels, hinit, reach⟩ (by simp [Result.outcome, flag]) rfl
      simpa [Result.obs, flag, Spec.coreBytes, out] using beh
    · have beh := Spec.CoreBeh.abort ⟨s, labels, hinit, reach⟩
        (by simp [Result.outcome, flag])
      simpa [Result.obs, flag, Spec.coreBytes, out] using beh
  · exact .inl (.inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩)

end Silmaril.Compile.Core.Verified.StateExit
