module

public import Silmaril.Compiler.Core.Verified.ArgvMem.Defs
public import Silmaril.Compiler.Core.Verified.Cond.Defs
public import Silmaril.Compiler.Core.Verified.ExitCall.Defs
public import Silmaril.Cerberus.Core.ArenaFail.Defs

/-! # `argv[i][j]`: Cerberus's elaboration of a character of an argument, by local steps

Cerberus elaborates the lvalue conversion of `e[n]` (`e` a pointer, `n` an integer constant) to

```
let weak p = CHECK(SHIFT(e, ty, n)) in load(ty, p)
SHIFT(e, ty, n) = let weak (a, c) = unseq(e, pure(Specified(n))) in
  case (a, c) of (Specified(x), Specified(y)) => let weak z = memop(PtrArrayShift, x, ty, y) in
    pure(Specified(z)) | _ => undef
CHECK(s) = let weak q = s in case q of Specified(x) => let weak b = memop(PtrValidForDeref, ty, x)
  in pure(if b then x else undef) | Unspecified(_) => undef
```

and the read of the parameter `argv` to `let weak p = pure(argv) in load(char**, p)`. So
`argv[i][j]` is `LOAD(char, CHECK(SHIFT(LOAD(char*, CHECK(SHIFT(LOAD(char**, argv), char*, i))),
char, j)))` (`charOf`).

`Ev I env e v`: from every memory satisfying `I` (an invariant that `ArgvMem.Reads` keeps), over
every continuation, `e` runs by local steps to `v`, with read accesses only, or reaches undefined
behaviour; `Bad` when it always reaches undefined behaviour. Each layer (`ev_load`, `ev_shift`,
`ev_check`, the pair `ev_pair` of an `unseq`) builds one from those of its parts, and a failure of
a part is a failure of the whole (`bad_*`), raised through the `unseq` arenas (`ArenaFail`).

`char_ev`: with the argument objects of `ArgvMem.Objs`, `argv[i][0]` for `i ≤ argc` is `Ev` of the
first byte of `args[i]` (its terminator when empty), and of every value when `i = argc` (the null
slot: `PtrArrayShift` of a null pointer is undefined behaviour, UB046). This is the byte that the
compiled code reads at the same place of `Spec.argBlock` (`charOfArgs`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvChar

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns TasksRun Plain unseqTasks
  taskFlag)
open Silmaril.Cerberus.Core.ArenaFail (Fails)
open ReturnLit (Eff)
open ArgvMem (Reads)
open Cond (OneAnn)

variable {file : Program} {labels : Labels}

/-! ## Runs that read or fail -/

/-- `e` runs from `m` over `k` to `v`: read accesses only, over at most one annotation frame, to a
memory that `Reads m`. -/
def RunsTo (env : Env) (e : EE) (k : List Frame) (m : Mem.Concrete.State) (v : Val) : Prop :=
  ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧ Reads m m' ∧
    LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value v, fr ++ k, m'⟩

/-- `e` reaches undefined behaviour from `m` over `k`, raised through every enclosing arena. -/
def FailsUB (env : Env) (e : EE) (k : List Frame) (m : Mem.Concrete.State) : Prop :=
  ∃ loc ub, Fails file labels false ⟨.effectExpr e env, k, m⟩ (.ub loc ub)

/-- From every memory satisfying `I`, over every continuation, `e` (without calls) runs to `v`
reading only, or reaches undefined behaviour. -/
def Ev (I : Mem.Concrete.State → Prop) (env : Env) (e : EE) (v : Val) : Prop :=
  hasCCall e = false ∧ ∀ k m, I m →
    RunsTo (file := file) (labels := labels) env e k m v ∨
      FailsUB (file := file) (labels := labels) env e k m

/-- From every memory satisfying `I`, `e` (without calls) reaches undefined behaviour. -/
def Bad (I : Mem.Concrete.State → Prop) (env : Env) (e : EE) : Prop :=
  hasCCall e = false ∧ ∀ k m, I m → FailsUB (file := file) (labels := labels) env e k m

/-- `I` survives reads. -/
def Stable (I : Mem.Concrete.State → Prop) : Prop := ∀ m m', I m → Reads m m' → I m'

theorem Bad.ev {I : Mem.Concrete.State → Prop} {env : Env} {e : EE}
    (h : Bad (file := file) (labels := labels) I env e) (v : Val) :
    Ev (file := file) (labels := labels) I env e v :=
  ⟨h.1, fun k m hm => .inr (h.2 k m hm)⟩

theorem FailsUB.pre {env env' : Env} {e e' : EE} {k k' : List Frame} {m m' : Mem.Concrete.State}
    (run : LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.effectExpr e' env', k', m'⟩)
    (h : FailsUB (file := file) (labels := labels) env' e' k' m') :
    FailsUB (file := file) (labels := labels) env e k m := by
  obtain ⟨loc, ub, f⟩ := h
  exact ⟨loc, ub, ArenaFail.Fails.pre file labels run f⟩

/-- A run to an ending. -/
theorem fails_end {s : State} {o : Outcome} (hv : ∀ v, s.control ≠ .value v)
    (h : requestAux file labels s.memory s.control s.stack false = .end_ o) :
    Fails file labels false s o :=
  ⟨s, .refl, hv, .inl h⟩

/-! ## Frames -/

theorem plain_effectExpr (e : EE) (env : Env) : Plain (.effectExpr e env) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
theorem plain_pureExpr (p : PE) (env : Env) : Plain (.pureExpr p env) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
theorem plain_value (v : Val) : Plain (.value v) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
theorem plain_apply (op : Prim) (vs : List Val) : Plain (.apply op vs) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- A value over at most one annotation frame reaches a weak bind. -/
theorem value_effectBind {fr : List Frame} {xs : List Access} (hfr : OneAnn fr xs) {v : Val}
    {pat : Pattern Sym} {bs : Bindings} (hm : matchPattern pat v = some bs) (b : EE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.value v, fr ++ .effectBind pat b env :: k, m⟩
      ⟨.effectExpr b (extendEnv bs env), fr ++ k, m⟩ := by
  rcases hfr with ⟨rfl, rfl⟩ | rfl
  · exact .single (.next (ExitCall.ra_effectBind file labels hm b env) (plain_effectExpr _ _))
  · exact .single (.next (ExitCall.ra_annotations file labels (by intro _ h; cases h)
      (by intro h; cases h) (fun _ => ExitCall.ra_effectBind file labels hm b env))
      (plain_effectExpr _ _))

theorem wseq_enter (an : List Annot) (pat : Pattern Sym) (a b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk an (.wseq pat a b)) env, k, m⟩
      ⟨.effectExpr a env, .effectBind pat b env :: k, m⟩ :=
  .single (.next (LoadTask.requestAux_wseq m an pat a b env k false) (plain_effectExpr _ _))

/-- A run to `v` over no continuation is a task run. -/
theorem RunsTo.task {env : Env} {e : EE} {m : Mem.Concrete.State} {v : Val}
    (h : RunsTo (file := file) (labels := labels) env e [] m v) :
    ∃ xs m', (∀ a ∈ xs, a.write = false) ∧ Reads m m' ∧
      TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ v xs m' := by
  obtain ⟨xs, m', fr, hfr, rd, g, run⟩ := h
  refine ⟨xs, m', rd, g, fr, by simpa using run, ?_⟩
  rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]

/-! ## Two unsequenced operands -/

theorem taskFlag_one {e : EE} (h : hasCCall e = false) (env : Env) (k : List Frame) :
    taskFlag false k [(0, .effectExpr e env, [])] = false :=
  Interleave.taskFlag_unseq (es := [e]) (by simpa using h) (List.prefix_refl _)

/-- **`unseq [e₁, e₂]`** runs `e₂`, then `e₁`, to the pair of their values, or reaches undefined
behaviour. -/
theorem ev_pair {I : Mem.Concrete.State → Prop} (hI : Stable I) {env : Env} {e₁ e₂ : EE}
    {v₁ v₂ : Val} (h₁ : Ev (file := file) (labels := labels) I env e₁ v₁)
    (h₂ : Ev (file := file) (labels := labels) I env e₂ v₂) (annots : List Annot) (k : List Frame)
    (m : Mem.Concrete.State) (hm : I m) :
    (∃ xs m', (∀ a ∈ xs, a.write = false) ∧ Reads m m' ∧
      LocalReaches file labels false ⟨.effectExpr (.mk annots (.unseq [e₁, e₂])) env, k, m⟩
        ⟨.value (.tuple [v₁, v₂]), .annotations xs :: k, m'⟩) ∨
    FailsUB (file := file) (labels := labels) env (.mk annots (.unseq [e₁, e₂])) k m := by
  have flag₁ := taskFlag_one h₁.1 env k
  rcases h₂.2 [] m hm with r₂ | ⟨loc, ub, f₂⟩
  · obtain ⟨xs₂, m₁, rd₂, g₁, run₂⟩ := r₂.task
    rcases h₁.2 [] m₁ (hI m m₁ hm g₁) with r₁ | ⟨loc, ub, f₁⟩
    · obtain ⟨xs₁, m₂, rd₁, g₂, run₁⟩ := r₁.task
      have runs : TasksRun file labels false k (unseqTasks [e₁, e₂] env) m
          ([] ++ [(0, v₁, xs₁)] ++ [(1, v₂, xs₂)]) m₂ := by
        rw [ArenaFail.unseqTasks_pair]
        refine .snoc (by rw [flag₁]; exact run₂) ?_
        exact .snoc (ts := []) (by simpa [taskFlag] using run₁) .nil
      have reads : ∀ x ∈ ([] ++ [(0, v₁, xs₁)] ++ [(1, v₂, xs₂)] : List (Nat × (Val × List Access))),
          ∀ a ∈ x.2.2, a.write = false := by
        intro x hx a ha
        simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl
        · exact rd₁ a ha
        · exact rd₂ a ha
      have run := Interleave.unseq_runs file labels (annots := annots) runs reads
      refine .inl ⟨_, m₂, ?_, g₁.trans g₂, by simpa using run⟩
      intro a ha
      simp only [List.mem_append] at ha
      rcases ha with ha | ha
      · exact rd₁ a ha
      · exact rd₂ a ha
    · exact .inr ⟨loc, ub, ArenaFail.fail_pair file labels
        (.inr ⟨v₂, xs₂, m₁, by rw [flag₁]; exact run₂, by simpa [taskFlag] using f₁⟩)⟩
  · exact .inr ⟨loc, ub, ArenaFail.fail_pair file labels (.inl (by rw [flag₁]; exact f₂))⟩

/-! ## Operands -/

/-- `pure(x)` runs to the value of `x`. -/
theorem ev_sym (I : Mem.Concrete.State → Prop) (annots ann : List Annot) (x : Sym) {env : Env}
    {v : Val} (hx : env.lookup x = some v) :
    Ev (file := file) (labels := labels) I env (.mk annots (.pure (.mk ann () (.sym x)))) v := by
  refine ⟨by simp [hasCCall], fun k m _ => .inl ?_⟩
  obtain ⟨l, run⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) annots ann
    x env hx k m
  exact ⟨[], _, [], .inl ⟨rfl, rfl⟩, by simp, (Reads.refl m).location l, run⟩

/-- `pure(w)` of a literal runs to its value. -/
theorem ev_val (I : Mem.Concrete.State → Prop) (annots ann : List Annot) (w : Value Codec.wireModel)
    (env : Env) :
    Ev (file := file) (labels := labels) I env (.mk annots (.pure (.mk ann () (.val w))))
      (runtimeValue w) := by
  refine ⟨by simp [hasCCall], fun k m _ => .inl ?_⟩
  obtain ⟨l, run⟩ := LoadTask.pure_val_local (file := file) (labels := labels) (wc := false) annots ann
    w env k m
  exact ⟨[], _, [], .inl ⟨rfl, rfl⟩, by simp, (Reads.refl m).location l, run⟩

/-! ## Environments -/

theorem lookup2_first {a b : Sym} {x y : Val} {env : Env} {s : Sym} (h : s.key = a.key) :
    (extendEnv [(a, x), (b, y)] env).lookup s = some x := by
  have : MapKey.key s = MapKey.key a := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [this, Finmap.lookup_insert]

theorem lookup2_second {a b : Sym} {x y : Val} {env : Env} {s : Sym} (h : s.key = b.key)
    (ne : b.key ≠ a.key) : (extendEnv [(a, x), (b, y)] env).lookup s = some y := by
  have hs : MapKey.key s ≠ MapKey.key a := by
    change s.key ≠ a.key
    rw [h]; exact ne
  have : MapKey.key s = MapKey.key b := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [Finmap.lookup_insert_of_ne _ hs, this, Finmap.lookup_insert]

/-! ## Loads -/

/-- `let weak p = X in load(ty, p)`: the operand and the type. -/
def loadOf : Eff → Option (Eff × Ctype)
  | .mk _ (.wseq (.mk _ (.base (some p, _))) X
      (.mk _ (.action (.mk .pos (.mk _ _ (.load (.mk _ () (.val (.ctype ty))) (.mk _ () (.sym p'))
        .na)))))) => if p'.key = p.key then some (X, ty) else none
  | _ => none

theorem loadOf_inv {e X : Eff} {ty : Ctype} (h : loadOf e = some (X, ty)) :
    ∃ a0 pa p pt la l u a3 a4 p', e = .mk a0 (.wseq (.mk pa (.base (some p, pt))) X
      (.mk la (.action (.mk .pos (.mk l u (.load (.mk a3 () (.val (.ctype ty))) (.mk a4 () (.sym p'))
        .na)))))) ∧ p'.key = p.key := by
  unfold loadOf at h
  split at h
  · split at h
    · cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by assumption⟩
    · cases h
  · cases h

/-- The memory transition of a typed load. -/
theorem requestAux_loadTyped {m m' : Mem.Concrete.State} {ty : Ctype} {ptr : Mem.Concrete.Pointer}
    {mv : Mem.Concrete.MemoryValue}
    (h : Mem.Concrete.loadTyped (PureEval.tagsOf file m) m ty ptr = .ok (mv, m')) (k : List Frame) :
    ∃ a : Access, a.write = false ∧
      requestAux file labels m (.apply (.memory .load) [.ctype ty, .object (.pointer ptr)]) k false =
        .memory "Load" m' (.value (.loaded (fromMemory mv))) (.annotations [a] :: k) := by
  have h' := h
  unfold Mem.Concrete.loadTyped at h'
  simp only [bind, Except.bind] at h'
  split at h'
  · cases h'
  rename_i r hacc
  obtain ⟨id, addr, size⟩ := r
  refine ⟨⟨k.findSome? fun f => match f with | .excluded n => some n | _ => none, [], false,
    addr, size⟩, rfl, ?_⟩
  rw [requestAux.eq_def]
  simp only [PureEval.tagsOf] at h hacc
  simp [awaitsScheduling, memoryRequest, h, hacc, bind, Except.bind, pure, Except.pure]
  rfl

/-- The load after its operand: `load(ty, p)` with `p` bound to `ptr`, from a memory where the load
succeeds with `mv` after any change of the current location. -/
theorem load_runs {I : Mem.Concrete.State → Prop} (hI : Stable I) {la : List Annot} {l : Loc} {u : Unit}
    {a3 a4 : List Annot} {ty : Ctype} {p' : Sym} {env : Env} {ptr : Mem.Concrete.Pointer}
    (hp : env.lookup p' = some (.object (.pointer ptr))) {mv : Mem.Concrete.MemoryValue}
    (hl : ∀ m, I m → ∃ m', Mem.Concrete.loadTyped (PureEval.tagsOf file m) m ty ptr = .ok (mv, m'))
    {fr : List Frame} {xs : List Access} (hfr : OneAnn fr xs) (k : List Frame)
    (m : Mem.Concrete.State) (hm : I m) :
    ∃ ys m' fr', OneAnn fr' ys ∧ (∀ a ∈ ys, a.write = false ∨ a ∈ xs) ∧ Reads m m' ∧
      LocalReaches file labels false
        ⟨.effectExpr (.mk la (.action (.mk .pos (.mk l u (.load (.mk a3 () (.val (.ctype ty)))
          (.mk a4 () (.sym p')) .na))))) env, fr ++ k, m⟩
        ⟨.value (.loaded (fromMemory mv)), fr' ++ k, m'⟩ := by
  obtain ⟨l₁, s₁⟩ := LoadTask.focus_local (file := file) (labels := labels) (wc := false)
    (plain_pureExpr _ env) (LoadTask.requestAux_load m la l u (.mk a3 () (.val (.ctype ty)))
      (.mk a4 () (.sym p')) env (fr ++ k) false)
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  have g₁ : Reads m m₁ := (Reads.refl m).location l₁
  obtain ⟨m₂, hload⟩ := hl m₁ (hI m m₁ hm g₁)
  obtain ⟨a, ha, hreq⟩ := requestAux_loadTyped (file := file) (labels := labels) hload (fr ++ k)
  have s₂ : LocalReaches file labels false
      ⟨.pureExpr (.mk a3 () (.val (.ctype ty))) env, .arguments (.memory .load) [] [.mk a4 () (.sym p')]
        env :: (fr ++ k), m₁⟩
      ⟨.apply (.memory .load) [.ctype ty, .object (.pointer ptr)], fr ++ k, m₁⟩ :=
    .head (.next (LoadTask.requestAux_val m₁ a3 _ env _ false) (plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₁ _ [] _ _ [] env _ false) (plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_sym m₁ a4 p' env hp _ false) (plain_value _))
          (.single (.next (LoadTask.requestAux_last_argument m₁ _ _ _ env _ false) (plain_apply _ _)))))
  obtain ⟨zs, fr'', hfr'', hzs, s₃⟩ := Cond.merge (file := file) (labels := labels) hfr (.inr rfl)
    (.loaded (fromMemory mv)) k m₂
  refine ⟨zs, m₂, fr'', hfr'', fun b hb => ?_, g₁.trans (Reads.loadTyped hload),
    s₁.trans (s₂.trans (Relation.ReflTransGen.head (.memory hreq) s₃))⟩
  rcases hzs b hb with hb | hb
  · simp only [List.mem_singleton] at hb; subst hb; exact .inl ha
  · exact .inr hb

/-- **A load** of the pointer its operand computes. -/
theorem ev_load {I : Mem.Concrete.State → Prop} (hI : Stable I) {e X : Eff} {ty : Ctype}
    (h : loadOf e = some (X, ty)) {env : Env} {ptr : Mem.Concrete.Pointer}
    (hX : Ev (file := file) (labels := labels) I env X (.object (.pointer ptr)))
    {mv : Mem.Concrete.MemoryValue}
    (hl : ∀ m, I m → ∃ m', Mem.Concrete.loadTyped (PureEval.tagsOf file m) m ty ptr = .ok (mv, m')) :
    Ev (file := file) (labels := labels) I env e (.loaded (fromMemory mv)) := by
  obtain ⟨a0, pa, p, pt, la, l, u, a3, a4, p', rfl, hp'⟩ := loadOf_inv h
  refine ⟨by simp [hasCCall, hX.1], fun k m hm => ?_⟩
  let LOAD : EE := .mk la (.action (.mk .pos (.mk l u (.load (.mk a3 () (.val (.ctype ty)))
    (.mk a4 () (.sym p')) .na))))
  have s₀ := wseq_enter (file := file) (labels := labels) a0 (.mk pa (.base (some p, pt))) X LOAD env k m
  rcases hX.2 (.effectBind (.mk pa (.base (some p, pt))) LOAD env :: k) m hm with
    ⟨xs, m₁, fr, hfr, rd, g₁, run⟩ | f
  · have s₁ := value_effectBind (file := file) (labels := labels) hfr
      (pat := .mk pa (.base (some p, pt))) (v := .object (.pointer ptr)) rfl LOAD env k m₁
    obtain ⟨ys, m₂, fr', hfr', rd', g₂, s₂⟩ := load_runs (file := file) (labels := labels) hI
      (ConvInt.lookup_one hp') hl hfr k m₁ (hI m m₁ hm g₁)
    exact .inl ⟨ys, m₂, fr', hfr', fun a ha => (rd' a ha).elim id (rd a), g₁.trans g₂,
      s₀.trans (run.trans (s₁.trans s₂))⟩
  · exact .inr (FailsUB.pre s₀ f)

/-- A load of an operand that always fails fails. -/
theorem bad_load {I : Mem.Concrete.State → Prop} {e X : Eff} {ty : Ctype}
    (h : loadOf e = some (X, ty)) {env : Env} (hX : Bad (file := file) (labels := labels) I env X) :
    Bad (file := file) (labels := labels) I env e := by
  obtain ⟨a0, pa, p, pt, la, l, u, a3, a4, p', rfl, hp'⟩ := loadOf_inv h
  refine ⟨by simp [hasCCall, hX.1], fun k m hm => ?_⟩
  exact FailsUB.pre (wseq_enter (file := file) (labels := labels) a0 _ X _ env k m) (hX.2 _ m hm)

/-! ## Memory operations -/

/-- A located `memop(PtrArrayShift, p :: ps)`: the focus, then its first operand. -/
theorem shift_enter {env : Env} {k : List Frame} {m : Mem.Concrete.State}
    (annots : List Annot) (p : PE) (ps : List PE) :
    ∃ l, LocalReaches file labels false
      ⟨.effectExpr (.mk annots (.memop .ptrArrayShift (p :: ps))) env, k, m⟩
      ⟨.pureExpr p env, .arguments (.memop .ptrArrayShift) [] ps env :: k, {m with currentLocation := l}⟩ := by
  have hr : ∃ l, requestAux file labels m (.effectExpr (.mk annots (.memop .ptrArrayShift (p :: ps))) env)
      k false =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) (.arguments (.memop .ptrArrayShift) [] ps env :: k)
      else .next (.setLocation l (.pureExpr p env)) (.arguments (.memop .ptrArrayShift) [] ps env :: k) := by
    rw [requestAux.eq_def]
    simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true, arguments]
    split
    · split
      · exact ⟨m.currentLocation, by simp⟩
      · exact ⟨_, rfl⟩
    · exact ⟨m.currentLocation, by simp⟩
  obtain ⟨l, hr⟩ := hr
  exact LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr)

/-- A located `memop(PtrValidForDeref, p :: ps)`: the focus, then its first operand. -/
theorem check_enter {env : Env} {k : List Frame} {m : Mem.Concrete.State}
    (annots : List Annot) (p : PE) (ps : List PE) :
    ∃ l, LocalReaches file labels false
      ⟨.effectExpr (.mk annots (.memop .ptrValidForDeref (p :: ps))) env, k, m⟩
      ⟨.pureExpr p env, .arguments (.pointerCheck true) [] ps env :: k, {m with currentLocation := l}⟩ := by
  have hr : ∃ l, requestAux file labels m (.effectExpr (.mk annots (.memop .ptrValidForDeref (p :: ps))) env)
      k false =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) (.arguments (.pointerCheck true) [] ps env :: k)
      else .next (.setLocation l (.pureExpr p env)) (.arguments (.pointerCheck true) [] ps env :: k) := by
    rw [requestAux.eq_def]
    simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true, arguments]
    split
    · split
      · exact ⟨m.currentLocation, by simp⟩
      · exact ⟨_, rfl⟩
    · exact ⟨m.currentLocation, by simp⟩
  obtain ⟨l, hr⟩ := hr
  exact LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr)

theorem requestAux_shift_ok {m : Mem.Concrete.State} {ptr ptr' : Mem.Concrete.Pointer} {ty : Ctype}
    {n : Int} (h : Mem.Concrete.shiftPointer (PureEval.tagsOf file m) m ptr ty n = .ok ptr')
    (k : List Frame) :
    requestAux file labels m (.apply (.memop .ptrArrayShift)
      [.object (.pointer ptr), .ctype ty, .object (.integer n)]) k false =
      .next (.value (.object (.pointer ptr'))) k := by
  rw [requestAux.eq_def]
  simp only [PureEval.tagsOf] at h
  simp [awaitsScheduling, h, bind, Except.bind, pure, Except.pure]

theorem requestAux_shift_ub {m : Mem.Concrete.State} {ptr : Mem.Concrete.Pointer} {ty : Ctype}
    {n : Int} {ub : UndefinedBehaviour}
    (h : Mem.Concrete.shiftPointer (PureEval.tagsOf file m) m ptr ty n = .error (.ub ub))
    (k : List Frame) :
    requestAux file labels m (.apply (.memop .ptrArrayShift)
      [.object (.pointer ptr), .ctype ty, .object (.integer n)]) k false = .end_ (.ub .unknown ub) := by
  rw [requestAux.eq_def]
  simp only [PureEval.tagsOf] at h
  simp [awaitsScheduling, h, bind, Except.bind]

/-- `PtrValidForDeref` of an allocated pointer whose type has an alignment. -/
theorem requestAux_check {m : Mem.Concrete.State} {ty : Ctype} {al : Int}
    (hal : Mem.Concrete.alignment (PureEval.tagsOf file m) ty = .ok al) (id addr : Int) (k : List Frame) :
    requestAux file labels m (.apply (.pointerCheck true)
      [.ctype ty, .object (.pointer (.allocated id addr))]) k false =
      .next (.value (boolean ((addr % al == 0) && !(decide (id ∈ m.dead))))) k := by
  rw [requestAux.eq_def]
  simp only [PureEval.tagsOf] at hal
  simp [awaitsScheduling, hal, pure, Except.pure, bind, Except.bind]

theorem requestAux_check_null {m : Mem.Concrete.State} {ty : Ctype} {al : Int}
    (hal : Mem.Concrete.alignment (PureEval.tagsOf file m) ty = .ok al) (t : Ctype) (k : List Frame) :
    requestAux file labels m (.apply (.pointerCheck true)
      [.ctype ty, .object (.pointer (.null t))]) k false = .next (.value (boolean false)) k := by
  rw [requestAux.eq_def]
  simp only [PureEval.tagsOf] at hal
  simp [awaitsScheduling, hal, pure, Except.pure, bind, Except.bind]

/-! ## Array shifts -/

/-- A `pure` expression (an undefined arm of the checks): it contains no call. -/
def isPure : EE → Bool
  | .mk _ (.pure _) => true
  | _ => false

/-- Case arms that are `pure` expressions. -/
def pureArms (bs : List (Pattern Sym × EE)) : Bool := bs.all fun b => isPure b.2

theorem pureArms_calls {bs : List (Pattern Sym × EE)} (h : pureArms bs = true) :
    ∀ a b, (a, b) ∈ bs → hasCCall b = false := by
  intro a b hm
  have hb := List.all_eq_true.mp h _ hm
  obtain ⟨ann, node⟩ := b
  cases node <;> simp_all [isPure, hasCCall]

/-- `SHIFT(X, ty, n)`: the operand, the element type and the literal offset. -/
def shiftOf : Eff → Option (Eff × Ctype × Int)
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some c, _))]))
      (.mk _ (.unseq [X, .mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n))))))]))
      (.mk _ (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym c')]))
        ((.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
            .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]),
          .mk _ (.wseq (.mk _ (.base (some z, _)))
            (.mk _ (.memop .ptrArrayShift [.mk _ () (.sym x'), .mk _ () (.val (.ctype ty)),
              .mk _ () (.sym y')]))
            (.mk _ (.pure (.mk _ () (.ctor .specified [.mk _ () (.sym z')])))))) :: rest)))) =>
      if a'.key = a.key ∧ c'.key = c.key ∧ x'.key = x.key ∧ y'.key = y.key ∧ z'.key = z.key ∧
          c.key ≠ a.key ∧ y.key ≠ x.key ∧ pureArms rest = true then some (X, ty, n)
      else none
  | _ => none

theorem shiftOf_inv {e X : Eff} {ty : Ctype} {n : Int} (h : shiftOf e = some (X, ty, n)) :
    ∃ (a0 pp p1 : List Annot) (a : Sym) (ta : BaseType) (p2 : List Annot) (c : Sym) (tc : BaseType)
      (au al al' ac as as1 : List Annot) (a' : Sym) (as2 : List Annot) (c' : Sym)
      (q0 q1 q2 : List Annot) (x : Sym) (tx : BaseType) (q3 q4 : List Annot) (y : Sym) (ty' : BaseType)
      (w0 w1 : List Annot) (z : Sym) (tz : BaseType) (w2 w3 : List Annot) (x' : Sym) (w4 w5 : List Annot)
      (y' : Sym) (w6 w7 w8 : List Annot) (z' : Sym) (rest : List (Pattern Sym × EE)),
      e = .mk a0 (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some c, tc))]))
        (.mk au (.unseq [X, .mk al (.pure (.mk al' () (.val (.loaded (.specified (.integer n))))))]))
        (.mk ac (.case_ (.mk as () (.ctor .tuple [.mk as1 () (.sym a'), .mk as2 () (.sym c')]))
          ((.mk q0 (.ctor .tuple [.mk q1 (.ctor .specified [.mk q2 (.base (some x, tx))]),
              .mk q3 (.ctor .specified [.mk q4 (.base (some y, ty'))])]),
            .mk w0 (.wseq (.mk w1 (.base (some z, tz)))
              (.mk w2 (.memop .ptrArrayShift [.mk w3 () (.sym x'), .mk w4 () (.val (.ctype ty)),
                .mk w5 () (.sym y')]))
              (.mk w6 (.pure (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')])))))) :: rest)))) ∧
      a'.key = a.key ∧ c'.key = c.key ∧ x'.key = x.key ∧ y'.key = y.key ∧ z'.key = z.key ∧
      c.key ≠ a.key ∧ y.key ≠ x.key ∧ pureArms rest = true := by
  unfold shiftOf at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc⟩
    · cases h
  · cases h

/-- The run of `SHIFT(X, ty, n)` up to the shift itself: its operands are evaluated (or undefined
behaviour is reached), and from the shifted pointer the rest of the run is fixed. -/
theorem shift_prefix {I : Mem.Concrete.State → Prop} (hI : Stable I) {e X : Eff} {ty : Ctype} {n : Int}
    (h : shiftOf e = some (X, ty, n)) {env : Env} {ptr : Mem.Concrete.Pointer}
    (hX : Ev (file := file) (labels := labels) I env X (.loaded (.specified (.pointer ptr))))
    (k : List Frame) (m : Mem.Concrete.State) (hm : I m) :
    FailsUB (file := file) (labels := labels) env e k m ∨
    ∃ K m₃ xs, I m₃ ∧ Reads m m₃ ∧ (∀ a ∈ xs, a.write = false) ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.apply (.memop .ptrArrayShift) [.object (.pointer ptr), .ctype ty, .object (.integer n)],
          K, m₃⟩ ∧
      ∀ ptr', ∃ m₄, Reads m₃ m₄ ∧ LocalReaches file labels false ⟨.value (.object (.pointer ptr')), K, m₃⟩
        ⟨.value (.loaded (.specified (.pointer ptr'))), .annotations xs :: k, m₄⟩ := by
  obtain ⟨a0, pp, p1, a, ta, p2, c, tc, au, al, al', ac, as, as1, a', as2, c', q0, q1, q2, x, tx, q3, q4,
    y, ty', w0, w1, z, tz, w2, w3, x', w4, w5, y', w6, w7, w8, z', rest, rfl, ha, hc, hx, hy, hz, hca,
    hyx, -⟩ := shiftOf_inv h
  let LIT : EE := .mk al (.pure (.mk al' () (.val (.loaded (.specified (.integer n))))))
  let TP : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some c, tc))])
  let MEMOP : EE := .mk w2 (.memop .ptrArrayShift [.mk w3 () (.sym x'), .mk w4 () (.val (.ctype ty)),
    .mk w5 () (.sym y')])
  let PURE : EE := .mk w6 (.pure (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')])))
  let ARM : EE := .mk w0 (.wseq (.mk w1 (.base (some z, tz))) MEMOP PURE)
  let SCRUT : PE := .mk as () (.ctor .tuple [.mk as1 () (.sym a'), .mk as2 () (.sym c')])
  let BS : List (Pattern Sym × EE) := (.mk q0 (.ctor .tuple [.mk q1 (.ctor .specified
    [.mk q2 (.base (some x, tx))]), .mk q3 (.ctor .specified [.mk q4 (.base (some y, ty'))])]), ARM) :: rest
  let CASE : EE := .mk ac (.case_ SCRUT BS)
  have s₀ := wseq_enter (file := file) (labels := labels) a0 TP (.mk au (.unseq [X, LIT])) CASE env k m
  rcases ev_pair (file := file) (labels := labels) hI hX (ev_val I al al' _ env) au
      (.effectBind TP CASE env :: k) m hm with ⟨xs, m₁, rd, g₁, s₁⟩ | f
  · let v₁ : Val := .loaded (.specified (.pointer ptr))
    let v₂ : Val := .loaded (.specified (.integer n))
    let env₁ := extendEnv [(a, v₁), (c, v₂)] env
    let K : List Frame := .annotations xs :: k
    have s₂ : LocalReaches file labels false
        ⟨.value (.tuple [v₁, v₂]), .annotations xs :: .effectBind TP CASE env :: k, m₁⟩
        ⟨.effectExpr CASE env₁, K, m₁⟩ :=
      .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a c ta tc v₁ v₂ CASE env k)
        (plain_effectExpr _ _))
    obtain ⟨l, hr⟩ := Cond.requestAux_case (file := file) (labels := labels) m₁ ac SCRUT BS env₁ K false
    obtain ⟨l₁, s₃⟩ := LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr)
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
    have heval : PureEval.Eval file (PureEval.tagsOf file m₂) env₁ (.inl SCRUT) (.inl (.tuple [v₁, v₂])) :=
      .ctor (.cons (.sym (lookup2_first ha)) (.cons (.sym (lookup2_second hc hca)) .nil))
        (by simp [primitive, pure, Except.pure])
    have s₄ := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels) heval
      (.effectCase BS env₁ :: K) m₂ rfl
    let env₂ := extendEnv [(x, .object (.pointer ptr)), (y, .object (.integer n))] env₁
    have s₅ : LocalReaches file labels false ⟨.value (.tuple [v₁, v₂]), .effectCase BS env₁ :: K, m₂⟩
        ⟨.effectExpr ARM env₂, K, m₂⟩ :=
      .single (.next (Cond.requestAux_effectCase m₂ _ BS env₁ K false
        (by simp [BS, selectCase, matchPattern, matchPatterns, v₁, v₂, pure])) (plain_effectExpr _ _))
    let K' : List Frame := .effectBind (.mk w1 (.base (some z, tz))) PURE env₂ :: K
    have s₆ := wseq_enter (file := file) (labels := labels) w0 (.mk w1 (.base (some z, tz))) MEMOP PURE env₂ K m₂
    obtain ⟨l₂, s₇⟩ := shift_enter (file := file) (labels := labels) (env := env₂) (k := K') (m := m₂) w2
      (.mk w3 () (.sym x')) [.mk w4 () (.val (.ctype ty)), .mk w5 () (.sym y')]
    let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
    have s₈ : LocalReaches file labels false
        ⟨.pureExpr (.mk w3 () (.sym x')) env₂, .arguments (.memop .ptrArrayShift) []
          [.mk w4 () (.val (.ctype ty)), .mk w5 () (.sym y')] env₂ :: K', m₃⟩
        ⟨.apply (.memop .ptrArrayShift) [.object (.pointer ptr), .ctype ty, .object (.integer n)], K', m₃⟩ :=
      .head (.next (LoadTask.requestAux_sym m₃ w3 x' env₂ (lookup2_first hx) _ false) (plain_value _))
        (.head (.next (LoadTask.requestAux_argument m₃ _ [] _ _ _ env₂ _ false) (plain_pureExpr _ _))
          (.head (.next (LoadTask.requestAux_val m₃ w4 _ env₂ _ false) (plain_value _))
            (.head (.next (LoadTask.requestAux_argument m₃ _ _ _ _ [] env₂ _ false) (plain_pureExpr _ _))
              (.head (.next (LoadTask.requestAux_sym m₃ w5 y' env₂ (lookup2_second hy hyx) _ false)
                (plain_value _))
                (.single (.next (LoadTask.requestAux_last_argument m₃ _ _ _ env₂ _ false)
                  (plain_apply _ _)))))))
    have g₃ : Reads m m₃ := (g₁.location l₁).location l₂
    refine .inr ⟨K', m₃, xs, hI m m₃ hm g₃, g₃, rd,
      s₀.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans (s₇.trans s₈))))))), ?_⟩
    intro ptr'
    let env₃ := extendEnv [(z, .object (.pointer ptr'))] env₂
    have s₉ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
      (pat := .mk w1 (.base (some z, tz))) (v := .object (.pointer ptr')) rfl PURE env₂ K m₃
    obtain ⟨l₃, s₁₀⟩ := ExitCall.pure_local file labels (wc := false) (env := env₃) (k := K) (m := m₃) w6
      (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')]))
    let m₄ : Mem.Concrete.State := {m₃ with currentLocation := l₃}
    have heval' : PureEval.Eval file (PureEval.tagsOf file m₄) env₃
        (.inl (.mk w7 () (.ctor .specified [.mk w8 () (.sym z')])))
        (.inl (.loaded (.specified (.pointer ptr')))) :=
      .ctor (.cons (.sym (ConvInt.lookup_one hz)) .nil) (by simp [primitive, pure, Except.pure])
    have s₁₁ := PureLocal.eval_local file (PureEval.tagsOf file m₄) (wc := false) (labels := labels) heval'
      (.diagnosticLocation m₃.currentLocation :: K) m₄ rfl
    exact ⟨m₄, (Reads.refl m₃).location l₃, s₉.trans (s₁₀.trans (s₁₁.tail
      (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _))))⟩
  · exact .inl (FailsUB.pre s₀ f)

/-- **An array shift** of the pointer its operand computes, from memories where it is `ptr'` or
undefined behaviour. -/
theorem ev_shift {I : Mem.Concrete.State → Prop} (hI : Stable I) {e X : Eff} {ty : Ctype} {n : Int}
    (h : shiftOf e = some (X, ty, n)) {env : Env} {ptr : Mem.Concrete.Pointer}
    (hX : Ev (file := file) (labels := labels) I env X (.loaded (.specified (.pointer ptr))))
    {ptr' : Mem.Concrete.Pointer}
    (hs : ∀ m, I m → Mem.Concrete.shiftPointer (PureEval.tagsOf file m) m ptr ty n = .ok ptr' ∨
      ∃ ub, Mem.Concrete.shiftPointer (PureEval.tagsOf file m) m ptr ty n = .error (.ub ub)) :
    Ev (file := file) (labels := labels) I env e (.loaded (.specified (.pointer ptr'))) := by
  have calls : hasCCall e = false := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, rfl, -, -, -, -, -, -, -, hrest⟩ := shiftOf_inv h
    simp [hasCCall, hX.1]
    exact fun a b hab => pureArms_calls hrest a b hab
  refine ⟨calls, fun k m hm => ?_⟩
  rcases shift_prefix hI h hX k m hm with f | ⟨K, m₃, xs, hm₃, g₃, rd, run, rest⟩
  · exact .inr f
  rcases hs m₃ hm₃ with hok | ⟨ub, hub⟩
  · obtain ⟨m₄, g₄, s⟩ := rest ptr'
    exact .inl ⟨xs, m₄, [.annotations xs], .inr rfl, rd, g₃.trans g₄,
      run.trans (.head (.next (requestAux_shift_ok hok K) (plain_value _)) s)⟩
  · exact .inr ⟨.unknown, ub, ArenaFail.Fails.pre file labels run
      (fails_end (fun _ h => nomatch h) (requestAux_shift_ub hub K))⟩

/-- An array shift of the null pointer is undefined behaviour (UB046). -/
theorem bad_shift_null {I : Mem.Concrete.State → Prop} (hI : Stable I) {e X : Eff} {ty : Ctype} {n : Int}
    (h : shiftOf e = some (X, ty, n)) {env : Env} {t : Ctype}
    (hX : Ev (file := file) (labels := labels) I env X (.loaded (.specified (.pointer (.null t)))))
    (hl : ∀ m, I m → ∃ l, Mem.Concrete.typeLayout 64 (PureEval.tagsOf file m) ty = .ok l) :
    Bad (file := file) (labels := labels) I env e := by
  have calls : hasCCall e = false := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, rfl, -, -, -, -, -, -, -, hrest⟩ := shiftOf_inv h
    simp [hasCCall, hX.1]
    exact fun a b hab => pureArms_calls hrest a b hab
  refine ⟨calls, fun k m hm => ?_⟩
  rcases shift_prefix hI h hX k m hm with f | ⟨K, m₃, xs, hm₃, g₃, rd, run, rest⟩
  · exact f
  obtain ⟨l, hl⟩ := hl m₃ hm₃
  have hub : Mem.Concrete.shiftPointer (PureEval.tagsOf file m₃) m₃ (.null t) ty n =
      .error (.ub .UB046_array_pointer_outside) := by
    simp [Mem.Concrete.shiftPointer, hl, bind, Except.bind]
    rfl
  exact ⟨.unknown, _, ArenaFail.Fails.pre file labels run
    (fails_end (fun _ h => nomatch h) (requestAux_shift_ub hub K))⟩

/-! ## Validity checks -/

theorem requestAux_pureIf (m : Mem.Concrete.State) (ann : List Annot) (p yes no : PE) (env : Env)
    (k : List Frame) :
    requestAux file labels m (.pureExpr (.mk ann () (.if_ p yes no)) env) k false =
      .next (.pureExpr p env) (.pureIf yes no env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_pureIf_false (m : Mem.Concrete.State) (yes no : PE) (env : Env) (k : List Frame) :
    requestAux file labels m (.value .false) (.pureIf yes no env :: k) false =
      .next (.pureExpr no env) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_undef (m : Mem.Concrete.State) (ann : List Annot) (l : Loc) (ub : UndefinedBehaviour)
    (env : Env) (k : List Frame) :
    requestAux file labels m (.pureExpr (.mk ann () (.undef l ub)) env) k false = .end_ (.ub l ub) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- `CHECK(S)` for the type `ty`: the operand and the type. -/
def checkOf : Eff → Option (Eff × Ctype)
  | .mk _ (.wseq (.mk _ (.base (some q, _))) S
      (.mk _ (.case_ (.mk _ () (.sym q'))
        ((.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
          .mk _ (.wseq (.mk _ (.base (some b, _)))
            (.mk _ (.memop .ptrValidForDeref [.mk _ () (.val (.ctype ty)), .mk _ () (.sym x')]))
            (.mk _ (.pure (.mk _ () (.if_ (.mk _ () (.sym b')) (.mk _ () (.sym x''))
              (.mk _ () (.undef _ _)))))))) :: rest)))) =>
      if q'.key = q.key ∧ x'.key = x.key ∧ b'.key = b.key ∧ x''.key = x.key ∧ x.key ≠ b.key ∧
          pureArms rest = true then some (S, ty) else none
  | _ => none

theorem checkOf_inv {e S : Eff} {ty : Ctype} (h : checkOf e = some (S, ty)) :
    ∃ (a0 pq : List Annot) (q : Sym) (tq : BaseType) (ac as : List Annot) (q' : Sym) (r0 r1 : List Annot)
      (x : Sym) (tx : BaseType) (w0 w1 : List Annot) (b : Sym) (tb : BaseType) (w2 w3 w4 : List Annot)
      (x' : Sym) (w5 w6 w7 : List Annot) (b' : Sym) (w8 : List Annot) (x'' : Sym) (w9 : List Annot)
      (ul : Loc) (ub : UndefinedBehaviour) (rest : List (Pattern Sym × EE)),
      e = .mk a0 (.wseq (.mk pq (.base (some q, tq))) S
        (.mk ac (.case_ (.mk as () (.sym q'))
          ((.mk r0 (.ctor .specified [.mk r1 (.base (some x, tx))]),
            .mk w0 (.wseq (.mk w1 (.base (some b, tb)))
              (.mk w2 (.memop .ptrValidForDeref [.mk w3 () (.val (.ctype ty)), .mk w4 () (.sym x')]))
              (.mk w5 (.pure (.mk w6 () (.if_ (.mk w7 () (.sym b')) (.mk w8 () (.sym x''))
                (.mk w9 () (.undef ul ub)))))))) :: rest)))) ∧
      q'.key = q.key ∧ x'.key = x.key ∧ b'.key = b.key ∧ x''.key = x.key ∧ x.key ≠ b.key ∧
      pureArms rest = true := by
  unfold checkOf at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc⟩
    · cases h
  · cases h

theorem checkOf_calls {e S : Eff} {ty : Ctype} (h : checkOf e = some (S, ty)) (hS : hasCCall S = false) :
    hasCCall e = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, -, -, -, -, -, hrest⟩ := checkOf_inv h
  simp [hasCCall, hS]
  exact fun a b hab => pureArms_calls hrest a b hab

/-- **A validity check** of the pointer its operand computes: the pointer, or undefined behaviour
when it is not valid for a dereference. -/
theorem ev_check {I : Mem.Concrete.State → Prop} (hI : Stable I) {e S : Eff} {ty : Ctype}
    (h : checkOf e = some (S, ty)) {env : Env} {ptr : Mem.Concrete.Pointer}
    (hS : Ev (file := file) (labels := labels) I env S (.loaded (.specified (.pointer ptr))))
    (hal : ∀ m, I m → ∃ al, Mem.Concrete.alignment (PureEval.tagsOf file m) ty = .ok al)
    (hp : (∃ id a, ptr = .allocated id a) ∨ ∃ t, ptr = .null t) :
    Ev (file := file) (labels := labels) I env e (.object (.pointer ptr)) := by
  refine ⟨checkOf_calls h hS.1, fun k m hm => ?_⟩
  obtain ⟨a0, pq, q, tq, ac, as, q', r0, r1, x, tx, w0, w1, b, tb, w2, w3, w4, x', w5, w6, w7, b', w8, x'',
    w9, ul, ub, rest, rfl, hq, hx, hb, hx'', hxb, -⟩ := checkOf_inv h
  let MEMOP : EE := .mk w2 (.memop .ptrValidForDeref [.mk w3 () (.val (.ctype ty)), .mk w4 () (.sym x')])
  let IF : PE := .mk w6 () (.if_ (.mk w7 () (.sym b')) (.mk w8 () (.sym x'')) (.mk w9 () (.undef ul ub)))
  let PURE : EE := .mk w5 (.pure IF)
  let ARM : EE := .mk w0 (.wseq (.mk w1 (.base (some b, tb))) MEMOP PURE)
  let BS : List (Pattern Sym × EE) := (.mk r0 (.ctor .specified [.mk r1 (.base (some x, tx))]), ARM) :: rest
  let CASE : EE := .mk ac (.case_ (.mk as () (.sym q')) BS)
  have s₀ := wseq_enter (file := file) (labels := labels) a0 (.mk pq (.base (some q, tq))) S CASE env k m
  rcases hS.2 (.effectBind (.mk pq (.base (some q, tq))) CASE env :: k) m hm with
    ⟨xs, m₁, fr, hfr, rd, g₁, run⟩ | f
  · let v : Val := .loaded (.specified (.pointer ptr))
    let env₁ := extendEnv [(q, v)] env
    have s₁ := value_effectBind (file := file) (labels := labels) hfr (pat := .mk pq (.base (some q, tq)))
      (v := v) rfl CASE env k m₁
    obtain ⟨l, hr⟩ := Cond.requestAux_case (file := file) (labels := labels) m₁ ac (.mk as () (.sym q')) BS
      env₁ (fr ++ k) false
    obtain ⟨l₁, s₂⟩ := LoadTask.focus_local (plain_pureExpr _ _) (by simpa using hr)
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₁}
    let env₂ := extendEnv [(x, .object (.pointer ptr))] env₁
    have s₃ : LocalReaches file labels false ⟨.pureExpr (.mk as () (.sym q')) env₁,
        .effectCase BS env₁ :: (fr ++ k), m₂⟩ ⟨.effectExpr ARM env₂, fr ++ k, m₂⟩ :=
      .head (.next (LoadTask.requestAux_sym m₂ as q' env₁ (ConvInt.lookup_one hq) _ false) (plain_value _))
        (.single (.next (Cond.requestAux_effectCase m₂ _ BS env₁ (fr ++ k) false
          (by simp [BS, selectCase, matchPattern, v])) (plain_effectExpr _ _)))
    let K' : List Frame := .effectBind (.mk w1 (.base (some b, tb))) PURE env₂ :: (fr ++ k)
    have s₄ := wseq_enter (file := file) (labels := labels) w0 (.mk w1 (.base (some b, tb))) MEMOP PURE env₂
      (fr ++ k) m₂
    obtain ⟨l₂, s₅⟩ := check_enter (file := file) (labels := labels) (env := env₂) (k := K') (m := m₂) w2
      (.mk w3 () (.val (.ctype ty))) [.mk w4 () (.sym x')]
    let m₃ : Mem.Concrete.State := {m₂ with currentLocation := l₂}
    have g₃ : Reads m m₃ := (g₁.location l₁).location l₂
    have s₆ : LocalReaches file labels false
        ⟨.pureExpr (.mk w3 () (.val (.ctype ty))) env₂, .arguments (.pointerCheck true) []
          [.mk w4 () (.sym x')] env₂ :: K', m₃⟩
        ⟨.apply (.pointerCheck true) [.ctype ty, .object (.pointer ptr)], K', m₃⟩ :=
      .head (.next (LoadTask.requestAux_val m₃ w3 _ env₂ _ false) (plain_value _))
        (.head (.next (LoadTask.requestAux_argument m₃ _ [] _ _ [] env₂ _ false) (plain_pureExpr _ _))
          (.head (.next (LoadTask.requestAux_sym m₃ w4 x' env₂ (ConvInt.lookup_one hx) _ false)
            (plain_value _))
            (.single (.next (LoadTask.requestAux_last_argument m₃ _ _ _ env₂ _ false) (plain_apply _ _)))))
    obtain ⟨al, hal₃⟩ := hal m₃ (hI m m₃ hm g₃)
    -- the check's value
    obtain ⟨bv, s₇⟩ : ∃ bv : Bool, LocalReaches file labels false
        ⟨.apply (.pointerCheck true) [.ctype ty, .object (.pointer ptr)], K', m₃⟩
        ⟨.value (boolean bv), K', m₃⟩ := by
      rcases hp with ⟨id, a, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨_, .single (.next (requestAux_check hal₃ id a K') (plain_value _))⟩
      · exact ⟨_, .single (.next (requestAux_check_null hal₃ t K') (plain_value _))⟩
    let env₃ := extendEnv [(b, boolean bv)] env₂
    have s₈ := value_effectBind (file := file) (labels := labels) (fr := []) (xs := []) (.inl ⟨rfl, rfl⟩)
      (pat := .mk w1 (.base (some b, tb))) (v := boolean bv) rfl PURE env₂ (fr ++ k) m₃
    obtain ⟨l₃, s₉⟩ := ExitCall.pure_local file labels (wc := false) (env := env₃) (k := fr ++ k) (m := m₃)
      w5 IF
    let m₄ : Mem.Concrete.State := {m₃ with currentLocation := l₃}
    have pre : LocalReaches file labels false ⟨.effectExpr (.mk a0 (.wseq (.mk pq (.base (some q, tq))) S
        CASE)) env, k, m⟩ ⟨.pureExpr IF env₃, .diagnosticLocation m₃.currentLocation :: (fr ++ k), m₄⟩ :=
      s₀.trans (run.trans (s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans (s₇.trans
        (s₈.trans s₉)))))))))
    have hb₃ : env₃.lookup b' = some (boolean bv) := ConvInt.lookup_one hb
    have hx₃ : env₃.lookup x'' = some (.object (.pointer ptr)) := by
      rw [ConvInt.lookup_one_other (by rw [hx'']; exact hxb), ConvInt.lookup_one hx'']
    cases bv
    · -- not valid: `undef`
      refine .inr ⟨ul, ub, ?_⟩
      refine ArenaFail.Fails.pre file labels (pre.trans ?_) (fails_end (s := ⟨.pureExpr (.mk w9 () (.undef ul ub))
        env₃, .diagnosticLocation m₃.currentLocation :: (fr ++ k), m₄⟩) (fun _ h => nomatch h) ?_)
      · refine .head (.next (requestAux_pureIf m₄ w6 _ _ _ env₃ _) (plain_pureExpr _ _)) ?_
        refine .head (.next (LoadTask.requestAux_sym m₄ w7 b' env₃ hb₃ _ false) (plain_value _)) ?_
        exact .single (.next (requestAux_pureIf_false m₄ _ _ env₃ _) (plain_pureExpr _ _))
      · exact requestAux_undef m₄ w9 ul ub env₃ _
    · -- valid: the pointer
      have heval : PureEval.Eval file (PureEval.tagsOf file m₄) env₃ (.inl IF) (.inl (.object (.pointer ptr))) :=
        .ifTrue (.sym hb₃) (.sym hx₃)
      have s₁₀ := PureLocal.eval_local file (PureEval.tagsOf file m₄) (wc := false) (labels := labels) heval
        (.diagnosticLocation m₃.currentLocation :: (fr ++ k)) m₄ rfl
      exact .inl ⟨xs, m₄, fr, hfr, rd, g₃.location l₃, pre.trans (s₁₀.tail
        (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (plain_value _)))⟩
  · exact .inr (FailsUB.pre s₀ f)

/-- A check of an operand that always fails fails. -/
theorem bad_check {I : Mem.Concrete.State → Prop} {e S : Eff} {ty : Ctype}
    (h : checkOf e = some (S, ty)) {env : Env} (hS : Bad (file := file) (labels := labels) I env S) :
    Bad (file := file) (labels := labels) I env e := by
  refine ⟨checkOf_calls h hS.1, fun k m hm => ?_⟩
  obtain ⟨a0, pq, q, tq, ac, as, q', r0, r1, x, tx, w0, w1, b, tb, w2, w3, w4, x', w5, w6, w7, b', w8, x'',
    w9, ul, ub, rest, rfl, -⟩ := checkOf_inv h
  exact FailsUB.pre (wseq_enter (file := file) (labels := labels) a0 _ S _ env k m) (hS.2 _ m hm)

/-! ## `argv[i][j]` -/

/-- `char`, at any annotations. -/
def isChar : Ctype → Bool
  | .mk _ (.basic (.integer .char)) => true
  | _ => false

/-- `char*`. -/
def isCharPtr : Ctype → Bool
  | .mk _ (.pointer _ t) => isChar t
  | _ => false

/-- `char**`. -/
def isCharPtrPtr : Ctype → Bool
  | .mk _ (.pointer _ t) => isCharPtr t
  | _ => false

/-- `pure(x)`. -/
def isSym (x : Sym) : Eff → Bool
  | .mk _ (.pure (.mk _ () (.sym x'))) => x'.key == x.key
  | _ => false

theorem isChar_inv {t : Ctype} (h : isChar t = true) : ∃ ann, t = .mk ann (.basic (.integer .char)) := by
  unfold isChar at h; split at h
  · exact ⟨_, rfl⟩
  · cases h

theorem isCharPtr_inv {t : Ctype} (h : isCharPtr t = true) :
    ∃ ann q ann', t = .mk ann (.pointer q (.mk ann' (.basic (.integer .char)))) := by
  unfold isCharPtr at h; split at h
  · obtain ⟨ann', rfl⟩ := isChar_inv h; exact ⟨_, _, _, rfl⟩
  · cases h

theorem isCharPtrPtr_inv {t : Ctype} (h : isCharPtrPtr t = true) :
    ∃ ann q r, isCharPtr r = true ∧ t = .mk ann (.pointer q r) := by
  unfold isCharPtrPtr at h; split at h
  · exact ⟨_, _, _, h, rfl⟩
  · cases h

theorem isSym_inv {x : Sym} {e : Eff} (h : isSym x e = true) :
    ∃ an ann x', e = .mk an (.pure (.mk ann () (.sym x'))) ∧ x'.key = x.key := by
  unfold isSym at h; split at h
  · exact ⟨_, _, _, rfl, by simpa using h⟩
  · cases h

/-- `argv[i][j]` with literal indices: Cerberus's elaboration over the parameter `argv`. -/
def charOf (argv : Sym) (e : Eff) : Option (Nat × Nat) :=
  match loadOf e with
  | some (c₁, t₁) => match checkOf c₁ with
    | some (s₁, t₂) => match shiftOf s₁ with
      | some (p₁, t₃, j) => match loadOf p₁ with
        | some (c₂, t₄) => match checkOf c₂ with
          | some (s₂, t₅) => match shiftOf s₂ with
            | some (l₃, t₆, i) => match loadOf l₃ with
              | some (x, t₇) =>
                if isSym argv x = true ∧ isChar t₁ = true ∧ isChar t₂ = true ∧ isChar t₃ = true ∧
                    isCharPtr t₄ = true ∧ isCharPtr t₅ = true ∧ isCharPtr t₆ = true ∧
                    isCharPtrPtr t₇ = true ∧ 0 ≤ i ∧ 0 ≤ j then some (i.toNat, j.toNat)
                else none
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | none => none

theorem charOf_inv {argv : Sym} {e : Eff} {i j : Nat} (h : charOf argv e = some (i, j)) :
    ∃ c₁ t₁ s₁ t₂ p₁ t₃ c₂ t₄ s₂ t₅ l₃ t₆ x t₇,
      loadOf e = some (c₁, t₁) ∧ checkOf c₁ = some (s₁, t₂) ∧ shiftOf s₁ = some (p₁, t₃, (j : Int)) ∧
      loadOf p₁ = some (c₂, t₄) ∧ checkOf c₂ = some (s₂, t₅) ∧ shiftOf s₂ = some (l₃, t₆, (i : Int)) ∧
      loadOf l₃ = some (x, t₇) ∧ isSym argv x = true ∧ isChar t₁ = true ∧ isChar t₂ = true ∧
      isChar t₃ = true ∧ isCharPtr t₄ = true ∧ isCharPtr t₅ = true ∧ isCharPtr t₆ = true ∧
      isCharPtrPtr t₇ = true := by
  unfold charOf at h
  split at h <;> try cases h
  rename_i c₁ t₁ h1
  split at h <;> try cases h
  rename_i s₁ t₂ h2
  split at h <;> try cases h
  rename_i p₁ t₃ j' h3
  split at h <;> try cases h
  rename_i c₂ t₄ h4
  split at h <;> try cases h
  rename_i s₂ t₅ h5
  split at h <;> try cases h
  rename_i l₃ t₆ i' h6
  split at h <;> try cases h
  rename_i x t₇ h7
  split at h
  · rename_i hc
    obtain ⟨hx, c1, c2, c3, c4, c5, c6, c7, hi, hj⟩ := hc
    cases h
    refine ⟨c₁, t₁, s₁, t₂, p₁, t₃, c₂, t₄, s₂, t₅, l₃, t₆, x, t₇, h1, h2, ?_, h4, h5, ?_, h7, hx, c1, c2,
      c3, c4, c5, c6, c7⟩
    · rw [Int.toNat_of_nonneg hj]; exact h3
    · rw [Int.toNat_of_nonneg hi]; exact h6
  · cases h

/-- Byte `j` of argument `i` (its terminator at `j = length`), `0` past the arguments. -/
def charOfArgs (args : List String) (i j : Nat) : Int :=
  if h : i < args.length then ((args[i].toList.map fun c => (c.toNat : Int)) ++ [0])[j]?.getD 0 else 0

theorem shift_live {tags : Mem.Concrete.Tags} {m : Mem.Concrete.State} {id b size : Int}
    (h : StartupArgs.Live m id b size) {ty : Ctype} {l : Mem.Concrete.TypeLayout}
    (hl : Mem.Concrete.typeLayout 64 tags ty = .ok l) {a n : Int} (h₁ : b ≤ a + l.size * n)
    (h₂ : a + l.size * n ≤ b + size) :
    Mem.Concrete.shiftPointer tags m (.allocated id a) ty n = .ok (.allocated id (a + l.size * n)) := by
  obtain ⟨⟨r, hr, hb, hs, -⟩, -⟩ := h
  simp [Mem.Concrete.shiftPointer, hl, hr, hb, hs, h₁, h₂, bind, Except.bind, pure, Except.pure]

theorem alignment_pointer (tags : Mem.Concrete.Tags) (ann : List Annot) (q : Qualifiers) (t : Ctype) :
    Mem.Concrete.alignment tags (.mk ann (.pointer q t)) = .ok 8 := by
  simp [Mem.Concrete.alignment, ArgvMem.typeLayout_pointer_ann, bind, Except.bind, pure, Except.pure]

theorem alignment_char (tags : Mem.Concrete.Tags) (ann : List Annot) :
    Mem.Concrete.alignment tags (.mk ann (.basic (.integer .char))) = .ok 1 := by
  simp [Mem.Concrete.alignment, ArgvMem.typeLayout_char_ann, bind, Except.bind, pure, Except.pure]

theorem not_function_of_charPtr {r : Ctype} (h : isCharPtr r = true) :
    ∀ ann r' ps va, r ≠ .mk ann (.function r' ps va) := by
  obtain ⟨_, _, _, rfl⟩ := isCharPtr_inv h
  intro _ _ _ _ e; cases e

theorem not_function_of_char {r : Ctype} (h : isChar r = true) :
    ∀ ann r' ps va, r ≠ .mk ann (.function r' ps va) := by
  obtain ⟨_, rfl⟩ := isChar_inv h
  intro _ _ _ _ e; cases e

theorem charOfArgs_lt {args : List String} {i j : Nat} (hi : i < args.length) (hj : j < args[i].length) :
    charOfArgs args i j = ((args[i].toList[j]'(by rw [String.length_toList]; exact hj)).toNat : Int) := by
  have hj' : j < args[i].toList.length := by rw [String.length_toList]; exact hj
  simp only [charOfArgs, hi, ↓reduceDIte]
  rw [List.getElem?_append_left (by simpa using hj'), List.getElem?_map,
    List.getElem?_eq_getElem hj']
  rfl

theorem charOfArgs_nul {args : List String} {i : Nat} (hi : i < args.length) :
    charOfArgs args i args[i].length = 0 := by
  have hl : args[i].toList.length = args[i].length := String.length_toList
  simp only [charOfArgs, hi, ↓reduceDIte]
  rw [List.getElem?_append_right (by simp [hl])]
  simp [hl]

/-- **`argv[i][j]`** with the argument objects: byte `j` of argument `i` for `i < argc` and `j` at most
its length, and undefined behaviour from the null slot `i = argc`. -/
theorem char_ev {argv : Sym} {e : Eff} {i j : Nat} (h : charOf argv e = some (i, j))
    {args : List String} (ha : Spec.ArgsOk args) {idV V idA B : Int} {qs : List Mem.Concrete.Pointer}
    (hm₀ : ∃ m, ArgvMem.Objs m args idV V idA B qs) {env : Env}
    (hargv : env.lookup argv = some (.object (.pointer (.allocated idV V))))
    (hi : i ≤ args.length) (hj : ∀ h : i < args.length, j ≤ args[i].length) :
    Ev (file := file) (labels := labels) (fun m => ArgvMem.Objs m args idV V idA B qs) env e
      (.loaded (.specified (.integer (charOfArgs args i j)))) := by
  obtain ⟨c₁, t₁, s₁, t₂, p₁, t₃, c₂, t₄, s₂, t₅, l₃, t₆, x, t₇, h1, h2, h3, h4, h5, h6, h7, hx, k1, k2,
    k3, k4, k5, k6, k7⟩ := charOf_inv h
  let I : Mem.Concrete.State → Prop := fun m => ArgvMem.Objs m args idV V idA B qs
  have hI : Stable I := fun m m' hm g => hm.reads g
  obtain ⟨m₀, hm₀⟩ := hm₀
  have hlen : qs.length = args.length := hm₀.strs.1
  -- `argv`
  obtain ⟨an, ann, x', rfl, hx'⟩ := isSym_inv hx
  have e₇ : Ev (file := file) (labels := labels) I env (.mk an (.pure (.mk ann () (.sym x'))))
      (.object (.pointer (.allocated idV V))) :=
    ev_sym I an ann x' (by rw [ReturnLit.lookup_key hx']; exact hargv)
  -- `load(char**, argv)`: the array
  obtain ⟨aV, qV, r, hr, rfl⟩ := isCharPtrPtr_inv k7
  have e₆ : Ev (file := file) (labels := labels) I env l₃ (.loaded (.specified (.pointer (.allocated idA B)))) :=
    ev_load hI h7 e₇ (mv := .pointer r (.allocated idA B)) fun m hm =>
      ArgvMem.load_pointer_ann _ m hm.ptr.live aV qV r le_rfl le_rfl hm.ptr.bytes (by have := hm.pos; omega)
        (by have := hm.top; omega)
        (ArgvMem.abstractPointer_prov m (not_function_of_charPtr hr) (by have := hm.pos; omega) hm.ptr.prov)
  -- the slot
  obtain ⟨a6, q6, a6', rfl⟩ := isCharPtr_inv k6
  have e₅ : Ev (file := file) (labels := labels) I env s₂
      (.loaded (.specified (.pointer (.allocated idA (B + 8 * i))))) :=
    ev_shift hI h6 e₆ fun m hm => .inl (by
      have := shift_live (tags := PureEval.tagsOf file m) hm.arr.live
        (ArgvMem.typeLayout_pointer_ann _ a6 q6 (.mk a6' (.basic (.integer .char)))) (a := B) (n := i) (by simp)
        (by simp [hlen]; omega)
      simpa using this)
  obtain ⟨a5, q5, a5', rfl⟩ := isCharPtr_inv k5
  have e₄ : Ev (file := file) (labels := labels) I env c₂ (.object (.pointer (.allocated idA (B + 8 * i)))) :=
    ev_check hI h5 e₅ (fun _ _ => ⟨8, alignment_pointer _ _ _ _⟩) (.inl ⟨_, _, rfl⟩)
  obtain ⟨a4, q4, a4', rfl⟩ := isCharPtr_inv k4
  obtain ⟨a3, rfl⟩ := isChar_inv k3
  obtain ⟨a2, rfl⟩ := isChar_inv k2
  obtain ⟨a1, rfl⟩ := isChar_inv k1
  rcases Nat.lt_or_ge i args.length with hlt | hge
  · -- a string: its pointer
    obtain ⟨b, hq, -, -, -, hbpos⟩ := hm₀.strs.2 i args[i] (List.getElem?_eq_getElem hlt)
    simp only [Int.zero_add] at hq
    have e₃ : Ev (file := file) (labels := labels) I env p₁ (.loaded (.specified (.pointer (.allocated i b)))) :=
      ev_load hI h4 e₄ (mv := .pointer (.mk a4' (.basic (.integer .char))) (.allocated i b)) fun m hm => by
        obtain ⟨hf, hp⟩ := hm.arr.slot i i b hq
        exact ArgvMem.load_pointer_ann _ m hm.arr.live a4 q4 _ (by omega) (by rw [hlen]; omega) hf
          (by omega) (by
            obtain ⟨b', hq', -, -, hbtop, -⟩ := hm.strs.2 i args[i] (List.getElem?_eq_getElem hlt)
            simp only [Int.zero_add, hq, Option.some.injEq, Mem.Concrete.Pointer.allocated.injEq] at hq'
            obtain ⟨-, rfl⟩ := hq'
            omega)
          (ArgvMem.abstractPointer_prov m (not_function_of_char rfl) (by omega) hp)
    have hjl := hj hlt
    -- `+ j`, its check and the character
    have e₂ : Ev (file := file) (labels := labels) I env s₁
        (.loaded (.specified (.pointer (.allocated i (b + j))))) :=
      ev_shift hI h3 e₃ fun m hm => .inl (by
        obtain ⟨b', hq', hstr, -, -, -⟩ := hm.strs.2 i args[i] (List.getElem?_eq_getElem hlt)
        simp only [Int.zero_add, hq, Option.some.injEq, Mem.Concrete.Pointer.allocated.injEq] at hq'
        obtain ⟨-, rfl⟩ := hq'
        simp only [Int.zero_add] at hstr
        have := shift_live (tags := PureEval.tagsOf file m) hstr.live (ArgvMem.typeLayout_char_ann _ a3)
          (a := b) (n := j) (by simp) (by simp; omega)
        simpa using this)
    have e₁ : Ev (file := file) (labels := labels) I env c₁ (.object (.pointer (.allocated i (b + j)))) :=
      ev_check hI h2 e₂ (fun _ _ => ⟨1, alignment_char _ _⟩) (.inl ⟨_, _, rfl⟩)
    have := ev_load hI h1 e₁ (mv := .integer .char (charOfArgs args i j)) fun m hm => by
      obtain ⟨b', hq', hstr, -, -, -⟩ := hm.strs.2 i args[i] (List.getElem?_eq_getElem hlt)
      simp only [Int.zero_add, hq, Option.some.injEq, Mem.Concrete.Pointer.allocated.injEq] at hq'
      obtain ⟨-, rfl⟩ := hq'
      simp only [Int.zero_add] at hstr
      rcases Nat.lt_or_ge j args[i].length with hj' | hj'
      · have hjl' : j < args[i].toList.length := by rw [String.length_toList]; exact hj'
        have hc := hstr.chars j _ (List.getElem?_eq_getElem hjl')
        obtain ⟨h0, h1', -⟩ := ArgvReloc.chars_of_argsOk ha _ (List.getElem_mem hlt) _
          (args[i].toList.getElem_mem hjl')
        rw [charOfArgs_lt hlt hj']
        exact ArgvMem.load_char_ann _ m hstr.live a1 (by omega) (by omega) hc (by omega) (by omega)
      · obtain rfl : j = args[i].length := by omega
        rw [charOfArgs_nul hlt]
        exact ArgvMem.load_char_ann _ m hstr.live a1 (by omega) (by omega) hstr.nul le_rfl (by norm_num)
    simpa [fromMemory] using this
  · -- the null slot
    obtain rfl : i = args.length := by omega
    have e₃ : Ev (file := file) (labels := labels) I env p₁
        (.loaded (.specified (.pointer (.null (.mk a4' (.basic (.integer .char))))))) :=
      ev_load hI h4 e₄ (mv := .pointer (.mk a4' (.basic (.integer .char))) (.null (.mk a4' (.basic (.integer .char)))))
        fun m hm => by
          have hf := hm.arr.null
          rw [hlen] at hf
          exact ArgvMem.load_pointer_ann _ m hm.arr.live a4 q4 _ (by omega) (by rw [hlen]; omega) hf
            le_rfl (by norm_num) (StartupArgs.abstractPointer_null m _ _)
    exact (bad_load h1 (bad_check h2 (bad_shift_null hI h3 e₃
      (fun _ _ => ⟨_, ArgvMem.typeLayout_char_ann _ a3⟩)))).ev _

end Silmaril.Compile.Core.Verified.ArgvChar
