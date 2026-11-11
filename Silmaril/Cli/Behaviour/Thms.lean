module

public import Silmaril.Cli.Behaviour.Defs
public import Batteries.Data.List.Basic

/-!
# CLI behaviour: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Cli.Spec`. See `Silmaril.Cli.Behaviour.Defs` for the
model and `docs/projects/cli.md`.

**Refinement and implementations.** `le_iff` (refinement unfolded), `det_le_iff`
(a deterministic program implements `S` iff each of its observations is allowed),
`Total.mono`, `total_det`, `le_inf_iff'` (meeting several requirements).

**Builders.** `pure_le_keepsFiles`, `pure_le_confined` (a pure program stays in its
footprint), `pure_le_exits`, `pure_le_stdoutIs`, `pure_le_stderrIs`, `pure_le_det`;
`le_guard`, `guard_mono`.

**Composition is monotone** (so refinement is a congruence): `mapInput_mono`,
`withArgs_mono`, `seq_mono`, `andThen_mono`, `orElse_mono`, `pipeO_mono`, `pipe_mono`,
`pipeSeq_mono`, `case_mono`,
`dispatch_mono`.

**Failures and refusals.** `le_orFail`, `orFail_mono`, `orFail_orFail`, `orFail_inf_succeeds`;
`le_orRefused`, `orRefused_mono`, **`orRefused_inf_reliable`** (in a reliable environment the
allowance disappears), `orRefused_inf_fails_le_orFail`, `orFail_inf_refused_le_orRefused`.

**Partial observations.** `Seen.le_seen`, `Seen.empty_le`, `partial_seen`, `partial_empty`,
`Partial.mono`, `Partial.ended`.

**File logs.** `Fs.replay_append`; `logged_pure`.

**Laws.** `seq_assoc`, `skip_seq`; `andThen_of_succeeds`, `andThen_of_fails`;
`Interleave.assoc`, `Interleave.swap`; **`pipeO_assoc`**, `pipeline_assoc`, `pipeSeq_assoc`;
**`pipeSeq_le_pipe`** (the sequential schedule is one of the pipe's); totality of `seq`,
`pipeSeq` and (logged) `pipe`.

**Copairing and dispatch.** `case_le_iff`, `le_case_iff`, `case_unique` (the specs of a
partition of the invocations determine one spec); `select_cons_of_ne`,
**`dispatch_cons_of_ne`** (adding a subcommand changes nothing on invocations that do not name
it), `dispatch_cons_self` (and the new command runs on those that do), `dispatch_mono`
(pointwise refinement of the commands and the default).
-/

@[expose] public section

namespace Silmaril.Cli

/-! ## Interleavings -/

namespace Interleave

variable {α : Type}

theorem nil_left : ∀ b : List α, Interleave [] b b
  | [] => .nil
  | _ :: b => .right (nil_left b)

theorem nil_right : ∀ a : List α, Interleave a [] a
  | [] => .nil
  | _ :: a => .left (nil_right a)

/-- One interleaving: all of `a`, then all of `b`. -/
theorem append : ∀ a b : List α, Interleave a b (a ++ b)
  | [], b => nil_left b
  | _ :: a, b => .left (append a b)

theorem swap {a b l : List α} (h : Interleave a b l) : Interleave b a l := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih

theorem nil_left_eq {b l : List α} (h : Interleave [] b l) : l = b := by
  induction l generalizing b with
  | nil => cases h; rfl
  | cons x l ih => cases h with | right h => rw [ih h]

/-- Interleaving is associative, left to right. -/
theorem assoc_l {a b m c l : List α} (h₁ : Interleave a b m) (h₂ : Interleave m c l) :
    ∃ m', Interleave b c m' ∧ Interleave a m' l := by
  induction h₂ generalizing a b with
  | nil => cases h₁; exact ⟨[], .nil, .nil⟩
  | left _ ih =>
    cases h₁ with
    | left h₁ =>
      obtain ⟨m', hbc, ham⟩ := ih h₁
      exact ⟨m', hbc, .left ham⟩
    | right h₁ =>
      obtain ⟨m', hbc, ham⟩ := ih h₁
      exact ⟨_, .left hbc, .right ham⟩
  | right _ ih =>
    obtain ⟨m', hbc, ham⟩ := ih h₁
    exact ⟨_, .right hbc, .right ham⟩

/-- Interleaving is associative, right to left. -/
theorem assoc_r {a b m' c l : List α} (h₁ : Interleave b c m') (h₂ : Interleave a m' l) :
    ∃ m, Interleave a b m ∧ Interleave m c l := by
  obtain ⟨m, hba, hcm⟩ := assoc_l h₁.swap h₂.swap
  exact ⟨m, hba.swap, hcm.swap⟩

theorem assoc {a b c l : List α} :
    (∃ m, Interleave a b m ∧ Interleave m c l) ↔ (∃ m', Interleave b c m' ∧ Interleave a m' l) :=
  ⟨fun ⟨_, h₁, h₂⟩ => assoc_l h₁ h₂, fun ⟨_, h₁, h₂⟩ => assoc_r h₁ h₂⟩

end Interleave

/-! ## Observations -/

@[simp] theorem Obs.andThen_stdout (o₁ o₂ : Obs) : (o₁.andThen o₂).stdout = o₁.stdout ++ o₂.stdout := rfl
@[simp] theorem Obs.andThen_stderr (o₁ o₂ : Obs) : (o₁.andThen o₂).stderr = o₁.stderr ++ o₂.stderr := rfl
@[simp] theorem Obs.andThen_exit (o₁ o₂ : Obs) : (o₁.andThen o₂).exit = o₂.exit := rfl
@[simp] theorem Obs.andThen_consumed (o₁ o₂ : Obs) :
    (o₁.andThen o₂).consumed = o₁.consumed + o₂.consumed := rfl
@[simp] theorem Obs.andThen_fs (o₁ o₂ : Obs) : (o₁.andThen o₂).fs = o₂.fs := rfl
@[simp] theorem Obs.andThen_log (o₁ o₂ : Obs) : (o₁.andThen o₂).log = o₁.log ++ o₂.log := rfl

/-! ## File logs -/

@[simp] theorem Fs.replay_nil (fs : Fs) : fs.replay [] = some fs := rfl

@[simp] theorem Fs.replay_write (fs : Fs) (p : FPath) (c : Option Bytes) (l : List FileEv) :
    fs.replay (.write p c :: l) = (fs.set p c).replay l := rfl

theorem Fs.replay_read (fs : Fs) (p : FPath) (c : Option Bytes) (l : List FileEv) :
    fs.replay (.read p c :: l) = if fs p = c then fs.replay l else none := rfl

/-- **Replaying a concatenation** replays the first log, then the second from where it left. -/
theorem Fs.replay_append (fs : Fs) (l₁ l₂ : List FileEv) :
    fs.replay (l₁ ++ l₂) = (fs.replay l₁).bind fun fs' => fs'.replay l₂ := by
  induction l₁ generalizing fs with
  | nil => rfl
  | cons e l ih =>
    cases e with
    | write p c => exact ih _
    | read p c =>
      by_cases h : fs p = c
      · simp only [List.cons_append, Fs.replay_read, h, ↓reduceIte]; exact ih fs
      · simp only [List.cons_append, Fs.replay_read, h, ↓reduceIte, Option.bind_none]

/-! ## Partial observations -/

/-- A complete observation is a partial view of itself. -/
theorem Seen.le_seen (o : Obs) : o.seen ≼ o :=
  ⟨List.prefix_refl _, List.prefix_refl _, Nat.le_refl _, fun _ h => h, id,
    fun _ h => ⟨(Option.some.inj h).symm, rfl, rfl, fun _ hf => (Option.some.inj hf).symm⟩⟩

/-- Nothing seen yet is a partial view of every run. -/
theorem Seen.empty_le (o : Obs) : ({} : Seen) ≼ o :=
  ⟨List.nil_prefix, List.nil_prefix, Nat.zero_le _, fun _ h => absurd h List.not_mem_nil,
    fun h => absurd h (by decide), fun _ h => absurd h (by simp)⟩

theorem Obs.andThen_assoc (o₁ o₂ o₃ : Obs) :
    (o₁.andThen o₂).andThen o₃ = o₁.andThen (o₂.andThen o₃) := by
  simp only [Obs.andThen, List.append_assoc, Nat.add_assoc, Bool.or_assoc]

theorem Input.after_after (i : Input) (o₁ o₂ : Obs) :
    (i.after o₁).after o₂ = i.after (o₁.andThen o₂) := by
  simp only [Input.after, Obs.andThen, List.drop_drop]

namespace Spec

/-! ## Refinement and implementations -/

theorem le_iff {S T : Spec} : S ≤ T ↔ ∀ i o, S i o → T i o := Iff.rfl

@[simp] theorem det_le_iff {f : Input → Obs} {S : Spec} : det f ≤ S ↔ ∀ i, S i (f i) := by
  constructor
  · exact fun h i => h i _ rfl
  · rintro h i o rfl; exact h i

theorem Total.mono {S T : Spec} (h : S ≤ T) (hS : S.Total) : T.Total := fun i =>
  let ⟨o, ho⟩ := hS i; ⟨o, h i o ho⟩

theorem total_det (f : Input → Obs) : (det f).Total := fun i => ⟨f i, rfl⟩

/-- Meeting several requirements, unfolded. -/
theorem le_inf_iff' {S T U : Spec} : S ≤ T ⊓ U ↔ S ≤ T ∧ S ≤ U := le_inf_iff

/-! ## Builders -/

theorem pure_le_keepsFiles (f : Input → Out) : pure f ≤ keepsFiles := fun _ _ h => h.2.2.2.1

theorem pure_le_confined (f : Input → Out) : pure f ≤ confined := by
  rintro i o ⟨-, -, -, hfs, hr, hc, -⟩
  refine ⟨?_, ?_, hc⟩
  · intro p hp; rw [hr] at hp; cases hp
  · intro p hp; exact absurd (congrFun hfs p) hp

theorem pure_le_exits (f : Input → Out) (c : ExitCode) (h : ∀ i, (f i).exit = c) :
    pure f ≤ exits c := fun i _ ho => ho.2.2.1.trans (h i)

theorem pure_le_stdoutIs (f : Input → Out) : pure f ≤ stdoutIs (fun i => (f i).stdout) :=
  fun _ _ h => h.1

theorem pure_le_stderrIs (f : Input → Out) : pure f ≤ stderrIs (fun i => (f i).stderr) :=
  fun _ _ h => h.2.1

/-- A total, deterministic implementation of a pure spec. -/
theorem det_le_pure (f : Input → Out) (c : Input → Nat) (hc : ∀ i, c i ≤ i.stdin.length) :
    det (fun i => (f i).toObs (c i) i.fs) ≤ pure f :=
  det_le_iff.2 fun i => ⟨rfl, rfl, rfl, rfl, rfl, hc i, rfl⟩

/-- A pure program logs its (absent) file effects. -/
theorem logged_pure (f : Input → Out) : (pure f).Logged := by
  rintro i o ⟨-, -, -, hfs, -, -, hlog⟩
  show i.fs.replay o.log = some o.fs
  rw [hlog, hfs]; rfl

theorem pure_le_prints (f : Input → Out) (h : ∀ i, (f i).exit = 0) :
    pure f ≤ prints fun i => (f i).stdout :=
  fun i _ ho => ⟨ho.2.2.1.trans (h i), ho.1, ho.2.2.2.1⟩

theorem total_pure (f : Input → Out) : (pure f).Total :=
  (total_det _).mono (det_le_pure f (fun _ => 0) fun _ => Nat.zero_le _)

theorem le_guard (P : Input → Prop) (S : Spec) : S ≤ guard P S := fun _ _ h _ => h

theorem guard_mono {P : Input → Prop} {S T : Spec} (h : S ≤ T) : guard P S ≤ guard P T :=
  fun i o hS hP => h i o (hS hP)

/-! ## Monotonicity -/

theorem mapInput_mono (f : Input → Input) {S T : Spec} (h : S ≤ T) : mapInput f S ≤ mapInput f T :=
  fun i o => h (f i) o

theorem withArgs_mono (as : List String) {S T : Spec} (h : S ≤ T) : withArgs as S ≤ withArgs as T :=
  mapInput_mono _ h

theorem seq_mono {S S' T T' : Spec} (hS : S ≤ S') (hT : T ≤ T') : seq S T ≤ seq S' T' := by
  rintro i o ⟨o₁, o₂, h₁, h₂, rfl⟩
  exact ⟨o₁, o₂, hS _ _ h₁, hT _ _ h₂, rfl⟩

theorem andThen_mono {S S' T T' : Spec} (hS : S ≤ S') (hT : T ≤ T') :
    andThen S T ≤ andThen S' T' := by
  rintro i o (⟨o₁, o₂, h₁, he, h₂, rfl⟩ | ⟨h, he⟩)
  · exact .inl ⟨o₁, o₂, hS _ _ h₁, he, hT _ _ h₂, rfl⟩
  · exact .inr ⟨hS _ _ h, he⟩

theorem orElse_mono {S S' T T' : Spec} (hS : S ≤ S') (hT : T ≤ T') :
    orElse S T ≤ orElse S' T' := by
  rintro i o (⟨o₁, o₂, h₁, he, h₂, rfl⟩ | ⟨h, he⟩)
  · exact .inl ⟨o₁, o₂, hS _ _ h₁, he, hT _ _ h₂, rfl⟩
  · exact .inr ⟨hS _ _ h, he⟩

theorem pipeO_mono {S S' T T' : Spec} (hS : S ≤ S') (hT : T ≤ T') : pipeO S T ≤ pipeO S' T' := by
  rintro i o ⟨o₁, o₂, fs₁, fs₂, h₁, h₂, rest⟩
  exact ⟨o₁, o₂, fs₁, fs₂, hS _ _ h₁, hT _ _ h₂, rest⟩

theorem pipe_mono {S S' T T' : Spec} (hS : S ≤ S') (hT : T ≤ T') : pipe S T ≤ pipe S' T' :=
  inf_le_inf_right _ (pipeO_mono hS hT)

theorem pipeSeq_mono {S S' T T' : Spec} (hS : S ≤ S') (hT : T ≤ T') :
    pipeSeq S T ≤ pipeSeq S' T' := by
  rintro i o ⟨o₁, o₂, h₁, h₂, rest⟩
  exact ⟨o₁, o₂, hS _ _ h₁, hT _ _ h₂, rest⟩

theorem case_mono {α : Type} (k : Input → α) {S T : α → Spec} (h : ∀ a, S a ≤ T a) :
    case k S ≤ case k T := fun i o => h (k i) i o

/-! ## Sequencing laws -/

theorem seq_assoc (S T U : Spec) : seq (seq S T) U = seq S (seq T U) := by
  funext i o
  apply propext
  constructor
  · rintro ⟨_, o₃, ⟨o₁, o₂, h₁, h₂, rfl⟩, h₃, rfl⟩
    have h₃' : U ((i.after o₁).after o₂) o₃ := by rwa [Input.after_after]
    exact ⟨o₁, o₂.andThen o₃, h₁, ⟨o₂, o₃, h₂, h₃', rfl⟩, Obs.andThen_assoc _ _ _⟩
  · rintro ⟨o₁, _, h₁, ⟨o₂, o₃, h₂, h₃, rfl⟩, rfl⟩
    have h₃' : U (i.after (o₁.andThen o₂)) o₃ := by rwa [← Input.after_after]
    exact ⟨o₁.andThen o₂, o₃, ⟨o₁, o₂, h₁, h₂, rfl⟩, h₃', (Obs.andThen_assoc _ _ _).symm⟩

theorem skip_seq (S : Spec) : seq skip S = S := by
  funext i o
  apply propext
  have hi : i.after { fs := i.fs } = i := by simp [Input.after]
  have ho : ∀ o : Obs, ({ fs := i.fs } : Obs).andThen o = o := fun o => by
    simp [Obs.andThen]
  constructor
  · rintro ⟨_, o₂, rfl, h₂, rfl⟩
    rw [hi] at h₂; rwa [ho]
  · intro h
    exact ⟨_, o, rfl, by rwa [hi], (ho o).symm⟩

theorem total_seq {S T : Spec} (hS : S.Total) (hT : T.Total) : (seq S T).Total := fun i =>
  let ⟨o₁, h₁⟩ := hS i
  let ⟨o₂, h₂⟩ := hT (i.after o₁)
  ⟨_, o₁, o₂, h₁, h₂, rfl⟩

/-- `S && T` is `S; T` when `S` always succeeds. -/
theorem andThen_of_succeeds {S : Spec} (hS : S ≤ succeeds) (T : Spec) :
    andThen S T = seq S T := by
  funext i o
  apply propext
  constructor
  · rintro (⟨o₁, o₂, h₁, -, h₂, rfl⟩ | ⟨h, he⟩)
    · exact ⟨o₁, o₂, h₁, h₂, rfl⟩
    · exact absurd (hS i o h) he
  · rintro ⟨o₁, o₂, h₁, h₂, rfl⟩
    exact .inl ⟨o₁, o₂, h₁, hS i o₁ h₁, h₂, rfl⟩

/-- `S && T` is `S` when `S` always fails. -/
theorem andThen_of_fails {S : Spec} (hS : S ≤ fails) (T : Spec) : andThen S T = S := by
  funext i o
  apply propext
  constructor
  · rintro (⟨o₁, o₂, h₁, he, -, -⟩ | ⟨h, -⟩)
    · exact absurd he (hS i o₁ h₁)
    · exact h
  · intro h
    exact .inr ⟨h, hS i o h⟩

/-! ## Pipes -/

/-- The observation of a sequential pipe schedule, from those of its two programs. -/
def pipeObs (o₁ o₂ : Obs) : Obs :=
  { stdout := o₂.stdout, stderr := o₁.stderr ++ o₂.stderr, exit := o₂.exit,
    consumed := o₁.consumed, reads := o₁.reads ++ o₂.reads, fs := o₂.fs,
    refused := o₁.refused || o₂.refused, log := o₁.log ++ o₂.log }

theorem total_pipeSeq {S T : Spec} (hS : S.Total) (hT : T.Total) : (pipeSeq S T).Total :=
  fun i =>
    let ⟨o₁, h₁⟩ := hS i
    let ⟨o₂, h₂⟩ := hT { i with stdin := o₁.stdout, fs := o₁.fs }
    ⟨pipeObs o₁ o₂, o₁, o₂, h₁, h₂, rfl, Interleave.append _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The sequential schedule is a schedule of the pipe**: for logged specs, every run of
`pipeSeq S T` is a run of `pipe S T` (its file log is `S`'s, then `T`'s). -/
theorem pipeSeq_le_pipe {S T : Spec} (hS : S.Logged) (hT : T.Logged) :
    pipeSeq S T ≤ pipe S T := by
  rintro i o ⟨o₁, o₂, h₁, h₂, hs, he, hx, hc, hr, hf, hd, hl⟩
  have c₁ : i.fs.replay o₁.log = some o₁.fs := hS _ _ h₁
  have c₂ : o₁.fs.replay o₂.log = some o₂.fs := hT _ _ h₂
  have hi : ({ i with fs := i.fs } : Input) = i := rfl
  have hcoh : i.fs.replay o.log = some o.fs := by
    rw [hl, Fs.replay_append, c₁, Option.bind_some, c₂, hf]
  refine ⟨⟨o₁, o₂, i.fs, o₁.fs, hi ▸ h₁, h₂, hs, he, hx, hc, hr, ?_, hd⟩, hcoh⟩
  exact hl ▸ Interleave.append _ _

/-- Logged specs that always have a run give a pipe that always has a run. -/
theorem total_pipe {S T : Spec} (hS : S.Total) (hT : T.Total) (hS' : S.Logged)
    (hT' : T.Logged) : (pipe S T).Total :=
  (total_pipeSeq hS hT).mono (pipeSeq_le_pipe hS' hT')

/-- The middle observation of `(S | T) | U` from those of `S` and `T`. -/
private def mid (o₁ o₂ : Obs) (e : Bytes) (l : List FileEv) (fs : Fs) : Obs :=
  { stdout := o₂.stdout, stderr := e, exit := o₂.exit, consumed := o₁.consumed,
    reads := o₁.reads ++ o₂.reads, fs := fs, refused := o₁.refused || o₂.refused, log := l }

/-- The open pipe, left to right. -/
private theorem pipeO_assoc_l {S T U : Spec} {i : Input} {o : Obs}
    (h : pipeO (pipeO S T) U i o) : pipeO S (pipeO T U) i o := by
  obtain ⟨o₁₂, o₃, fs₁₂, fs₃, ⟨o₁, o₂, fs₁, fs₂, h₁, h₂, hs, he, hx, hc, hr, hl, hd⟩, h₃,
    hs', he', hx', hc', hr', hl', hd'⟩ := h
  obtain ⟨m', h23, h1m⟩ := Interleave.assoc_l he he'
  obtain ⟨l', g23, g1m⟩ := Interleave.assoc_l hl hl'
  have h₃' : U { i with stdin := o₂.stdout, fs := fs₃ } o₃ := by rwa [hs] at h₃
  have hT : pipeO T U { i with stdin := o₁.stdout, fs := fs₂ } (mid o₂ o₃ m' l' fs₂) :=
    ⟨o₂, o₃, fs₂, fs₃, h₂, h₃', rfl, h23, rfl, rfl, rfl, g23, rfl⟩
  refine ⟨o₁, mid o₂ o₃ m' l' fs₂, fs₁, fs₂, h₁, hT, hs', h1m, hx', hc'.trans hc, ?_, g1m, ?_⟩
  · simp only [hr', hr, mid, List.append_assoc]
  · simp only [hd', hd, mid, Bool.or_assoc]

/-- The open pipe, right to left. -/
private theorem pipeO_assoc_r {S T U : Spec} {i : Input} {o : Obs}
    (h : pipeO S (pipeO T U) i o) : pipeO (pipeO S T) U i o := by
  obtain ⟨o₁, o₂₃, fs₁, fs₂₃, h₁, ⟨o₂, o₃, fs₂, fs₃, h₂, h₃, hs, he, hx, hc, hr, hl, hd⟩,
    hs', he', hx', hc', hr', hl', hd'⟩ := h
  obtain ⟨m, h12, hm3⟩ := Interleave.assoc_r he he'
  obtain ⟨l, g12, gm3⟩ := Interleave.assoc_r hl hl'
  have hST : pipeO S T { i with fs := fs₁ } (mid o₁ o₂ m l fs₁) :=
    ⟨o₁, o₂, fs₁, fs₂, h₁, h₂, rfl, h12, rfl, rfl, rfl, g12, rfl⟩
  refine ⟨mid o₁ o₂ m l fs₁, o₃, fs₁, fs₃, hST, h₃, hs'.trans hs, hm3, hx'.trans hx, hc', ?_,
    gm3, ?_⟩
  · simp only [hr', hr, mid, List.append_assoc]
  · simp only [hd', hd, mid, Bool.or_assoc]

/-- **Open pipes are associative**: `(S | T) | U = S | (T | U)` before closing; so a pipeline
`a | b | c` is one spec, `pipeO (pipeO a b) c ⊓ coherent`. -/
theorem pipeO_assoc (S T U : Spec) : pipeO (pipeO S T) U = pipeO S (pipeO T U) :=
  funext fun _ => funext fun _ => propext ⟨pipeO_assoc_l, pipeO_assoc_r⟩

/-- **A three-stage pipeline is one closing of the open pipes**, however it is bracketed. -/
theorem pipeline_assoc (S T U : Spec) :
    pipeO (pipeO S T) U ⊓ coherent = pipeO S (pipeO T U) ⊓ coherent := by
  rw [pipeO_assoc]

/-- `(S | T) | U`, scheduled left to right, from the parts. -/
private theorem pipeSeq_assoc_l {S T U : Spec} {i : Input} {o : Obs}
    (h : pipeSeq (pipeSeq S T) U i o) : pipeSeq S (pipeSeq T U) i o := by
  obtain ⟨o₁₂, o₃, ⟨o₁, o₂, h₁, h₂, hs, he, hx, hc, hr, hf, hd, hl⟩, h₃, hs', he', hx', hc',
    hr', hf', hd', hl'⟩ := h
  obtain ⟨m', h23, h1m⟩ := Interleave.assoc_l he he'
  have h₃' : U { i with stdin := o₂.stdout, fs := o₂.fs } o₃ := by rwa [hs, hf] at h₃
  have hT : pipeSeq T U { i with stdin := o₁.stdout, fs := o₁.fs }
      (mid o₂ o₃ m' (o₂.log ++ o₃.log) o₃.fs) :=
    ⟨o₂, o₃, h₂, h₃', rfl, h23, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨o₁, _, h₁, hT, hs', h1m, hx', hc'.trans hc, ?_, hf', ?_, ?_⟩
  · simp only [hr', hr, mid, List.append_assoc]
  · simp only [hd', hd, mid, Bool.or_assoc]
  · simp only [hl', hl, mid, List.append_assoc]

/-- `S | (T | U)`, scheduled left to right, from the parts. -/
private theorem pipeSeq_assoc_r {S T U : Spec} {i : Input} {o : Obs}
    (h : pipeSeq S (pipeSeq T U) i o) : pipeSeq (pipeSeq S T) U i o := by
  obtain ⟨o₁, o₂₃, h₁, ⟨o₂, o₃, h₂, h₃, hs, he, hx, hc, hr, hf, hd, hl⟩, hs', he', hx', hc',
    hr', hf', hd', hl'⟩ := h
  obtain ⟨m, h12, hm3⟩ := Interleave.assoc_r he he'
  have hST : pipeSeq S T i (mid o₁ o₂ m (o₁.log ++ o₂.log) o₂.fs) :=
    ⟨o₁, o₂, h₁, h₂, rfl, h12, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨_, o₃, hST, h₃, hs'.trans hs, hm3, hx'.trans hx, hc', ?_, hf'.trans hf, ?_, ?_⟩
  · simp only [hr', hr, mid, List.append_assoc]
  · simp only [hd', hd, mid, Bool.or_assoc]
  · simp only [hl', hl, mid, List.append_assoc]

/-- **Sequential pipes are associative.** -/
theorem pipeSeq_assoc (S T U : Spec) : pipeSeq (pipeSeq S T) U = pipeSeq S (pipeSeq T U) :=
  funext fun _ => funext fun _ => propext ⟨pipeSeq_assoc_l, pipeSeq_assoc_r⟩

/-! ## Failures and refusals -/

theorem le_orFail (S : Spec) : S ≤ orFail S := fun _ _ h => .inl h

theorem orFail_mono {S T : Spec} (h : S ≤ T) : orFail S ≤ orFail T := by
  rintro i o (hs | ⟨hx, o', hs', hp⟩)
  · exact .inl (h i o hs)
  · exact .inr ⟨hx, o', h i o' hs', hp⟩

/-- Allowing failure twice is allowing it once. -/
theorem orFail_orFail (S : Spec) : orFail (orFail S) = orFail S := by
  refine le_antisymm ?_ (le_orFail _)
  rintro i o (hs | ⟨hx, o', hs' | ⟨-, o'', hs'', hp'⟩, hp⟩)
  · exact hs
  · exact .inr ⟨hx, o', hs', hp⟩
  · exact .inr ⟨hx, o'', hs'', hp.trans hp'⟩

/-- A run that succeeds is allowed by `orFail S` only if `S` allows it. -/
theorem orFail_inf_succeeds (S : Spec) : orFail S ⊓ succeeds ≤ S := by
  rintro i o ⟨hs | ⟨hx, -⟩, h0⟩
  · exact hs
  · exact absurd h0 hx

theorem le_orRefused (S : Spec) : S ≤ orRefused S := fun _ _ h => .inl h

theorem orRefused_mono {S T : Spec} (h : S ≤ T) : orRefused S ≤ orRefused T := by
  rintro i o (hs | ⟨hr, o', hs', hp, hx⟩)
  · exact .inl (h i o hs)
  · exact .inr ⟨hr, o', h i o' hs', hp, hx⟩

/-- **In a reliable environment, `orRefused S` is `S`.** -/
theorem orRefused_inf_reliable (S : Spec) : orRefused S ⊓ reliable ≤ S := by
  rintro i o ⟨hs | ⟨hr, -⟩, hrel⟩
  · exact hs
  · exact absurd (hr.symm.trans hrel) (by decide)

/-- **The failing runs `orRefused` allows are `orFail`'s.** -/
theorem orRefused_inf_fails_le_orFail (S : Spec) : orRefused S ⊓ fails ≤ orFail S := by
  rintro i o ⟨hs | ⟨-, o', hs', hp, -⟩, hx⟩
  · exact .inl hs
  · exact .inr ⟨hx, o', hs', hp⟩

/-- On the runs that saw a refusal, `orFail` allows only what `orRefused` allows. -/
theorem orFail_inf_refused_le_orRefused (S : Spec) :
    orFail S ⊓ (fun _ o => o.refused = true) ≤ orRefused S := by
  rintro i o ⟨hs | ⟨hx, o', hs', hp⟩, hr⟩
  · exact .inl hs
  · exact .inr ⟨hr, o', hs', hp, .inr hx⟩

/-! ## Partial observations -/

/-- **An allowed complete observation is an allowed partial one.** -/
theorem partial_seen {S : Spec} {i : Input} {o : Obs} (h : S i o) : S.Partial i o.seen :=
  ⟨o, h, Seen.le_seen o⟩

/-- Partial satisfaction is monotone in the spec. -/
theorem Partial.mono {S T : Spec} {i : Input} {p : Seen} (h : S.Partial i p) (hST : S ≤ T) :
    T.Partial i p :=
  let ⟨o, ho, hp⟩ := h
  ⟨o, hST i o ho, hp⟩

/-- Before anything is seen, a spec with a run on `i` allows the view. -/
theorem partial_empty {S : Spec} {i : Input} {o : Obs} (h : S i o) : S.Partial i {} :=
  ⟨o, h, Seen.empty_le o⟩

/-- **A finished partial view that saw the files is a complete observation** (up to the lower
bounds on consumption and reads): the spec allows a run with exactly its streams, exit code
and files. -/
theorem Partial.ended {S : Spec} {i : Input} {p : Seen} (h : S.Partial i p) {c : ExitCode}
    (hc : p.exit = some c) :
    ∃ o, S i o ∧ o.stdout = p.stdout ∧ o.stderr = p.stderr ∧ o.exit = c ∧
      ∀ f, p.fs = some f → o.fs = f := by
  obtain ⟨o, ho, -, -, -, -, -, hend⟩ := h
  obtain ⟨hx, hso, hse, hf⟩ := hend c hc
  exact ⟨o, ho, hso.symm, hse.symm, hx.symm, fun f hp => (hf f hp).symm⟩

/-! ## Copairing and dispatch -/

theorem case_le_iff {α : Type} {k : Input → α} {S : α → Spec} {T : Spec} :
    case k S ≤ T ↔ ∀ a i o, k i = a → S a i o → T i o :=
  ⟨fun h _ i o hk hs => h i o (by subst hk; exact hs), fun h i o hs => h (k i) i o rfl hs⟩

theorem le_case_iff {α : Type} {k : Input → α} {S : α → Spec} {T : Spec} :
    T ≤ case k S ↔ ∀ a i o, k i = a → T i o → S a i o :=
  ⟨fun h _ i o hk ht => by subst hk; exact h i o ht, fun h i o ht => h (k i) i o rfl ht⟩

/-- **Uniqueness of the copairing**: a spec that is `S a` on the invocations classified `a`,
for every `a`, is `case k S`. -/
theorem case_unique {α : Type} {k : Input → α} {S : α → Spec} {T : Spec}
    (h : ∀ a i, k i = a → T i = S a i) : T = case k S :=
  funext fun i => h (k i) i rfl

theorem select_cons_of_ne {c : String} {S : Spec} {cmds : List (String × Spec)} {i : Input}
    (h : i.args.head? ≠ some c) : select ((c, S) :: cmds) i = select cmds i := by
  unfold select
  cases ha : i.args with
  | nil => rfl
  | cons a rest =>
    have hne : (a == c) = false := by
      rw [ha] at h; simpa using h
    simp only [List.lookup_cons, hne]

/-- **Adding a subcommand is conservative**: on invocations whose first argument is not the
new command's name, dispatch behaves as before. -/
theorem dispatch_cons_of_ne {c : String} {S : Spec} {cmds : List (String × Spec)} {dflt : Spec}
    {i : Input} (h : i.args.head? ≠ some c) :
    dispatch ((c, S) :: cmds) dflt i = dispatch cmds dflt i := by
  funext o
  simp only [dispatch, case, select_cons_of_ne h]

/-- The new subcommand runs on the invocations that name it. -/
theorem dispatch_cons_self {c : String} {S : Spec} {cmds : List (String × Spec)} {dflt : Spec}
    {i : Input} {rest : List String} (h : i.args = c :: rest) :
    dispatch ((c, S) :: cmds) dflt i = withArgs rest S i := by
  funext o
  simp [dispatch, case, select, h]

/-- Lookup in two command lists related pointwise by refinement. -/
theorem lookup_rel {cmds cmds' : List (String × Spec)}
    (h : List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) cmds cmds') (c : String) :
    Option.Rel (· ≤ ·) (cmds.lookup c) (cmds'.lookup c) := by
  induction h with
  | nil => exact .none
  | @cons a b l l' hab _ ih =>
    obtain ⟨n, S⟩ := a
    obtain ⟨n', S'⟩ := b
    obtain ⟨rfl, hle⟩ := hab
    simp only [List.lookup_cons]
    cases c == n
    · exact ih
    · exact .some hle

/-- **Dispatch is monotone** in the commands (pointwise, same names in the same order) and in
the default. -/
theorem dispatch_mono {cmds cmds' : List (String × Spec)} {dflt dflt' : Spec}
    (h : List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) cmds cmds') (hd : dflt ≤ dflt') :
    dispatch cmds dflt ≤ dispatch cmds' dflt' := by
  intro i o
  show case (select cmds) _ i o → case (select cmds') _ i o
  simp only [case, select]
  cases i.args with
  | nil => exact hd i o
  | cons c rest =>
    have hr := lookup_rel h c
    dsimp only
    revert hr
    cases cmds.lookup c <;> cases cmds'.lookup c <;> intro hr
    · exact hd i o
    · cases hr
    · cases hr
    · cases hr with | some hle => exact withArgs_mono rest hle i o

end Spec

end Silmaril.Cli
