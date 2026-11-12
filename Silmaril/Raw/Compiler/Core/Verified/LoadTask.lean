module

public import Silmaril.Compiler.Core.Verified.Locals.Defs
public import Silmaril.Cerberus.Core.Interleave.Defs

/-! # Reads of `int` locals as tasks of an unsequenced expression

Cerberus elaborates each read of an `int` local `x` in an operand position to

```
let weak p = pure(x) in load(int, p)
```

and every binary operator, assignment and call to an `unseq` of its operands, so a read of a
local runs as a task of the `Eunseq` arena (`Cerberus/Core/Interleave.lean`). `load_local`: that
task, from a memory where `x` points to the slot of `n` (`Locals.Slot`), runs to
`Specified n` by local steps, with one access that is a read; the memory changes only in its
current location and last used allocation, so every slot is kept. With
`Interleave.unseq_runs` (reads never race), an `unseq` of local reads and literals reaches
the tuple of their values: `unseq_reads` (the operands of `x * 4`, `x - 5`, `x | 4`).

This is the memory half of operators over locals; the operator's guard (`case` of
the tuple, `catch_exceptional_condition`) is pure and the arithmetic stays with `PureEval`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoadTask

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns Plain TasksRun unseqTasks
  taskFlag)
open ReturnConst (focusMemory)
open Locals (Slot intVal)
open Mem.Concrete (LiveInt IntRange)

variable {file : Program} {labels : Labels}

/-! ## Requests -/

theorem requestAux_wseq (m : Mem.Concrete.State) (ann : List Annot) (pat : Pattern Sym) (a b : EE)
    (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.effectExpr (.mk ann (.wseq pat a b)) env) k wc =
      .next (.effectExpr a env) (.effectBind pat b env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

/-- A focused `pure` over any frames: the operand above a diagnostic frame, after a possible
change of the current location. -/
theorem requestAux_pure (m : Mem.Concrete.State) (annots : List Annot) (p : PE) (env : Env)
    (k : List Frame) (wc : Bool) :
    ∃ l, requestAux file labels m (.effectExpr (.mk annots (.pure p)) env) k wc =
      if ({m with currentLocation := l} : Mem.Concrete.State).currentLocation == m.currentLocation
      then .next (.pureExpr p env) (.diagnosticLocation m.currentLocation :: k)
      else .next (.setLocation l (.pureExpr p env)) (.diagnosticLocation m.currentLocation :: k) := by
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.false_eq_true, ite_false, Bool.not_true]
  split
  · split
    · exact ⟨m.currentLocation, by simp⟩
    · exact ⟨_, rfl⟩
  · exact ⟨m.currentLocation, by simp⟩

theorem requestAux_sym (m : Mem.Concrete.State) (ann : List Annot) (s : Sym) (env : Env) {v : Val}
    (hs : env.lookup s = some v) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.pureExpr (.mk ann () (.sym s)) env) k wc = .next (.value v) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, hs]

theorem requestAux_val (m : Mem.Concrete.State) (ann : List Annot) (w : Value Codec.wireModel)
    (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.pureExpr (.mk ann () (.val w)) env) k wc =
      .next (.value (runtimeValue w)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_bind (m : Mem.Concrete.State) (ann : List Annot) (p : Sym) (ty : BaseType)
    (v : Val) (b : EE) (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value v) (.effectBind (.mk ann (.base (some p, ty))) b env :: k) wc =
      .next (.effectExpr b (extendEnv [(p, v)] env)) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling, matchPattern]

theorem requestAux_argument (m : Mem.Concrete.State) (op : Prim) (vs : List Val) (v : Val) (p : PE)
    (ps : List PE) (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value v) (.arguments op vs (p :: ps) env :: k) wc =
      .next (.pureExpr p env) (.arguments op (vs ++ [v]) ps env :: k) := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_last_argument (m : Mem.Concrete.State) (op : Prim) (vs : List Val) (v : Val)
    (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.value v) (.arguments op vs [] env :: k) wc =
      .next (.apply op (vs ++ [v])) k := by
  rw [requestAux.eq_def]; simp [awaitsScheduling]

theorem requestAux_load (m : Mem.Concrete.State) (ann : List Annot) (l : Loc) (u : Unit)
    (ty p : PE) (env : Env) (k : List Frame) (wc : Bool) :
    requestAux file labels m (.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.load ty p .na)))))
      env) k wc =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr ty env) (.arguments (.memory .load) [] [p] env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr ty env))
        (.arguments (.memory .load) [] [p] env :: k) := by
  simp only [requestAux, awaitsScheduling, arguments]
  rfl

/-- The load of a live `int` slot holding `n`, outside a call: one memory transition to
`Specified n` with a read access. -/
theorem requestAux_load_apply (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State}
    {id addr : Int} (h : LiveInt m id addr) (plain : Mem.Concrete.PlainAt m addr) {n : Int}
    (hn : IntRange n)
    (bytes : Mem.Concrete.fetchBytes 4 addr m.bytes = Mem.Concrete.encodeInteger 4 n) :
    ∃ a : Access, a.write = false ∧
      requestAux file labels m (.apply (.memory .load) [.ctype (Mem.Concrete.intType ann),
        .object (.pointer (.allocated id addr))]) k false =
      .memory "Load" {m with lastUsed := some id} (.value (.loaded (.specified (.integer n))))
        (.annotations [a] :: k) := by
  refine ⟨⟨k.findSome? fun f => match f with | .excluded n => some n | _ => none, [], false,
    addr, 4⟩, rfl, ?_⟩
  rw [requestAux.eq_def]
  simp [awaitsScheduling, memoryRequest, fromMemory,
    Mem.Concrete.load_int _ ann h plain hn bytes, Mem.Concrete.access_int _ ann h, bind,
    Except.bind, pure, Except.pure]
  rfl

/-! ## Local runs -/

theorem plain_effectExpr (e : EE) (env : Env) : Plain (.effectExpr e env) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem plain_pureExpr (p : PE) (env : Env) : Plain (.pureExpr p env) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem plain_value (v : Val) : Plain (.value v) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem plain_apply (op : Prim) (vs : List Val) : Plain (.apply op vs) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem plain_setLocation (l : Loc) (c : Control) : Plain (.setLocation l c) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- A focus: possibly one update of the current location, then the continuation. -/
theorem focus_local {wc : Bool} {c : Control} {k k' : List Frame} {m : Mem.Concrete.State}
    {l : Loc} {c' : Control} (hc' : Plain c')
    (h : requestAux file labels m c k wc =
      if l == m.currentLocation then .next c' k' else .next (.setLocation l c') k') :
    ∃ l', LocalReaches file labels wc ⟨c, k, m⟩ ⟨c', k', {m with currentLocation := l'}⟩ := by
  by_cases hl : l == m.currentLocation
  · simp only [hl, ↓reduceIte] at h
    exact ⟨m.currentLocation, .single (.next h hc')⟩
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨l, .head (.next h (plain_setLocation l c'))
      (.single (.update (Interleave.requestAux_setLocation file labels m l c' k' wc)))⟩

/-- `pure(x)` over any frames reaches the value of `x`. -/
theorem pure_sym_local {wc : Bool} (annots ann : List Annot) (s : Sym) (env : Env) {v : Val}
    (hs : env.lookup s = some v) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ l', LocalReaches file labels wc ⟨.effectExpr (.mk annots (.pure (.mk ann () (.sym s)))) env, k, m⟩
      ⟨.value v, k, {m with currentLocation := l'}⟩ := by
  obtain ⟨l, hr⟩ := requestAux_pure (file := file) (labels := labels) m annots
    (.mk ann () (.sym s)) env k wc
  obtain ⟨l', hf⟩ := focus_local (plain_pureExpr _ env) (by simpa using hr)
  refine ⟨l', hf.tail (.next (requestAux_sym _ ann s env hs _ wc) (plain_value v)) |>.tail ?_⟩
  exact .next (Interleave.requestAux_value_diagnostic file labels _ v _ k wc) (plain_value v)

/-- `let weak p = pure(x) in load(int, p')`: the read of the local `x` (`p'` names `p`). -/
abbrev loadExpr (a0 pa a1 a2 la a3 c1 a4 : List Annot) (pt : BaseType) (p p' x : Sym) (l : Loc)
    (u : Unit) : EE :=
  .mk a0 (.wseq (.mk pa (.base (some p, pt))) (.mk a1 (.pure (.mk a2 () (.sym x))))
    (.mk la (.action (.mk .pos (.mk l u (.load (intVal a3 c1) (.mk a4 () (.sym p')) .na))))))

/-- The memories a read leaves: only the current location and the last used allocation
change. -/
def Touched (m m' : Mem.Concrete.State) : Prop :=
  ∃ l u, m' = {m with currentLocation := l, lastUsed := u}

theorem Touched.refl (m : Mem.Concrete.State) : Touched m m :=
  ⟨m.currentLocation, m.lastUsed, rfl⟩

theorem Touched.trans {m₁ m₂ m₃ : Mem.Concrete.State} (h₁ : Touched m₁ m₂) (h₂ : Touched m₂ m₃) :
    Touched m₁ m₃ := by
  obtain ⟨l, u, rfl⟩ := h₁
  obtain ⟨l', u', rfl⟩ := h₂
  exact ⟨l', u', rfl⟩

theorem Touched.slot {m m' : Mem.Concrete.State} (h : Touched m m') {id addr n : Int}
    (s : Slot m id addr n) : Slot m' id addr n := by
  obtain ⟨l, u, rfl⟩ := h
  obtain ⟨live, plain, bytes⟩ := s
  exact ⟨Locals.liveInt_with live rfl rfl, plain, bytes⟩

theorem Touched.stdout {m m' : Mem.Concrete.State} (h : Touched m m') : m'.stdout = m.stdout := by
  obtain ⟨l, u, rfl⟩ := h
  rfl

theorem focusMemory_touched (ann : List Annot) (m : Mem.Concrete.State) :
    Touched m (focusMemory ann m) := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  exact ⟨l, m.lastUsed, by rw [hl]⟩

/-- **The read of an `int` local**, outside calls and over any continuation: local steps to
`Specified n`, the value of the slot `x` points to, with one read access. -/
theorem load_local (a0 pa a1 a2 la a3 c1 a4 : List Annot) (pt : BaseType) (p p' x : Sym) (l : Loc)
    (u : Unit) (hp' : p'.key = p.key) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : IntRange n) (slot : Slot m id addr n) :
    ∃ a m', a.write = false ∧ Touched m m' ∧
      LocalReaches file labels false
        ⟨.effectExpr (loadExpr a0 pa a1 a2 la a3 c1 a4 pt p p' x l u) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer n))), .annotations [a] :: k, m'⟩ := by
  let ptr : Val := .object (.pointer (.allocated id addr))
  let LOAD : EE := .mk la (.action (.mk .pos (.mk l u (.load (intVal a3 c1) (.mk a4 () (.sym p')) .na))))
  let env₁ := extendEnv [(p, ptr)] env
  have hp : env₁.lookup p' = some ptr := ConvInt.lookup_one hp'
  -- wseq, then `pure(x)` above the bind frame
  have s₁ : LocalReaches file labels false
      ⟨.effectExpr (loadExpr a0 pa a1 a2 la a3 c1 a4 pt p p' x l u) env, k, m⟩
      ⟨.effectExpr (.mk a1 (.pure (.mk a2 () (.sym x)))) env,
        .effectBind (.mk pa (.base (some p, pt))) LOAD env :: k, m⟩ :=
    .single (.next (requestAux_wseq m a0 _ _ _ env k false) (plain_effectExpr _ env))
  obtain ⟨l₁, s₂⟩ := pure_sym_local (file := file) (labels := labels) (wc := false) a1 a2 x env hx
    (.effectBind (.mk pa (.base (some p, pt))) LOAD env :: k) m
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  have s₃ : LocalReaches file labels false
      ⟨.value ptr, .effectBind (.mk pa (.base (some p, pt))) LOAD env :: k, m₁⟩
      ⟨.effectExpr LOAD env₁, k, m₁⟩ :=
    .single (.next (requestAux_bind m₁ pa p pt ptr LOAD env k false) (plain_effectExpr _ _))
  -- the load: focus, operands, memory transition
  obtain ⟨l₂, s₄⟩ := focus_local (file := file) (labels := labels) (wc := false)
    (plain_pureExpr (intVal a3 c1) env₁) (requestAux_load m₁ la l u (intVal a3 c1)
      (.mk a4 () (.sym p')) env₁ k false)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₂}
  have s₅ : LocalReaches file labels false
      ⟨.pureExpr (intVal a3 c1) env₁, .arguments (.memory .load) [] [.mk a4 () (.sym p')] env₁ :: k,
        m₂⟩
      ⟨.apply (.memory .load) [.ctype (Mem.Concrete.intType c1), ptr], k, m₂⟩ :=
    .head (.next (requestAux_val m₂ a3 _ env₁ _ false) (plain_value _))
      (.head (.next (requestAux_argument m₂ _ [] _ _ [] env₁ k false) (plain_pureExpr _ _))
        (.head (.next (requestAux_sym m₂ a4 p' env₁ hp _ false) (plain_value _))
          (.single (.next (requestAux_last_argument m₂ _ _ _ env₁ k false) (plain_apply _ _)))))
  have slot₂ : Slot m₂ id addr n :=
    Touched.slot (m := m) ⟨l₂, m.lastUsed, rfl⟩ slot
  obtain ⟨a, ha, hload⟩ := requestAux_load_apply (file := file) (labels := labels) c1 k
    slot₂.live slot₂.plain hn slot₂.bytes
  refine ⟨a, {m₂ with lastUsed := some id}, ha, ⟨l₂, some id, rfl⟩, ?_⟩
  exact s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail (.memory hload)))))

/-- `pure(v)` of a literal over any frames reaches its value. -/
theorem pure_val_local {wc : Bool} (annots ann : List Annot) (w : Value Codec.wireModel) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    ∃ l', LocalReaches file labels wc ⟨.effectExpr (.mk annots (.pure (.mk ann () (.val w)))) env, k, m⟩
      ⟨.value (runtimeValue w), k, {m with currentLocation := l'}⟩ := by
  obtain ⟨l, hr⟩ := requestAux_pure (file := file) (labels := labels) m annots
    (.mk ann () (.val w)) env k wc
  obtain ⟨l', hf⟩ := focus_local (plain_pureExpr _ env) (by simpa using hr)
  refine ⟨l', hf.tail (.next (requestAux_val _ ann w env _ wc) (plain_value _)) |>.tail ?_⟩
  exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ k wc) (plain_value _)

/-! ## Unsequenced reads -/

/-- A task that only reads: from every memory satisfying `I` it runs, outside calls, to the
value `v` with read accesses, touching only the current location and the last use. -/
def ReadTask (I : Mem.Concrete.State → Prop) (env : Env) (e : EE) (v : Val) : Prop :=
  hasCCall e = false ∧ ∀ m, I m → ∃ xs m', (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
    TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ v xs m'

/-- The tasks of `unseq es` run last first under flag `false`, every result a read. -/
theorem tasksRun_reads {k : List Frame} {env : Env} (I : Mem.Concrete.State → Prop)
    (hI : ∀ m m', I m → Touched m m' → I m') (val : EE → Val) (es : List EE)
    (h : ∀ e ∈ es, ReadTask (file := file) (labels := labels) I env e (val e))
    (calls : ∀ e ∈ es, hasCCall e = false) (es₀ : List EE) (pre : es <+: es₀)
    (calls₀ : ∀ e ∈ es₀, hasCCall e = false) (m : Mem.Concrete.State) (hm : I m) :
    ∃ results m', TasksRun file labels false k (unseqTasks es env) m results m' ∧
      results.map (·.2.1) = es.map val ∧ (∀ x ∈ results, ∀ a ∈ x.2.2, a.write = false) ∧
      Touched m m' := by
  induction es using List.reverseRecOn generalizing m with
  | nil => exact ⟨[], m, .nil, rfl, by simp, Touched.refl m⟩
  | append_singleton es e ih =>
    obtain ⟨-, run⟩ := h e (by simp)
    obtain ⟨xs, m₁, rd, t₁, hrun⟩ := run m hm
    have flag : taskFlag false k (unseqTasks es env) = false :=
      Interleave.taskFlag_unseq calls₀ ((List.prefix_append es [e]).trans pre)
    obtain ⟨results, m', rest, hv, rds, t'⟩ := ih (fun e' he' => h e' (by simp [he']))
      (fun e' he' => calls e' (by simp [he'])) ((List.prefix_append es [e]).trans pre) m₁
      (hI m m₁ hm t₁)
    refine ⟨results ++ [(es.length, val e, xs)], m', ?_, by simp [hv], ?_, t₁.trans t'⟩
    · rw [Interleave.unseqTasks_snoc]
      exact .snoc (by rw [flag]; exact hrun) rest
    · intro x hx a ha
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact rds x hx a ha
      · exact rd a ha

/-- **An unsequenced expression of reads** (loads of slots, pure operands) reaches the tuple of
their values in source order, outside calls, under one frame of read accesses. -/
theorem unseq_reads {k : List Frame} {annots : List Annot} {es : List EE} {env : Env}
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') (val : EE → Val)
    (h : ∀ e ∈ es, ReadTask (file := file) (labels := labels) I env e (val e))
    (m : Mem.Concrete.State) (hm : I m) :
    ∃ xs m', (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
      LocalReaches file labels false ⟨.effectExpr (.mk annots (.unseq es)) env, k, m⟩
        ⟨.value (.tuple (es.map val)), .annotations xs :: k, m'⟩ := by
  have calls : ∀ e ∈ es, hasCCall e = false := fun e he => (h e he).1
  obtain ⟨results, m', run, hv, rds, t⟩ := tasksRun_reads (k := k) I hI val es h calls es
    (List.prefix_refl es) calls m hm
  refine ⟨results.flatMap (·.2.2), m', ?_, t, ?_⟩
  · intro a ha
    simp only [List.mem_flatMap] at ha
    obtain ⟨x, hx, ha⟩ := ha
    exact rds x hx a ha
  · rw [← hv]
    exact Interleave.unseq_runs file labels (annots := annots) run rds

/-- An `Epure` task of a literal only reads. -/
theorem literal_readTask (I : Mem.Concrete.State → Prop) (env : Env) (annots ann : List Annot)
    (w : Value Codec.wireModel) :
    ReadTask (file := file) (labels := labels) I env (.mk annots (.pure (.mk ann () (.val w))))
      (runtimeValue w) := by
  refine ⟨by rw [hasCCall.eq_def], fun m _ => ?_⟩
  obtain ⟨l', run⟩ := Interleave.literal_task file labels (wc := false) annots ann w env m
  exact ⟨[], _, by simp, ⟨l', m.lastUsed, rfl⟩, run⟩

/-- The read of a local whose slot holds `n` in every memory satisfying `I` only reads. -/
theorem load_readTask (I : Mem.Concrete.State → Prop) (env : Env)
    (a0 pa a1 a2 la a3 c1 a4 : List Annot) (pt : BaseType) (p p' x : Sym) (l : Loc) (u : Unit)
    (hp' : p'.key = p.key) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : IntRange n) (slot : ∀ m, I m → Slot m id addr n) :
    ReadTask (file := file) (labels := labels) I env
      (loadExpr a0 pa a1 a2 la a3 c1 a4 pt p p' x l u) (.loaded (.specified (.integer n))) := by
  refine ⟨by simp [loadExpr, hasCCall], fun m hm => ?_⟩
  obtain ⟨a, m', ha, t, run⟩ := load_local (file := file) (labels := labels) a0 pa a1 a2 la a3 c1 a4
    pt p p' x l u hp' env [] m hx hn (slot m hm)
  exact ⟨[a], m', by simpa using ha, t, [.annotations [a]], run, rfl⟩

end Silmaril.Compile.Core.Verified.LoadTask
