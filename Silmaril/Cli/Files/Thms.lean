module

public import Silmaril.Cli.Files.Defs
public import Silmaril.Cli.Behaviour.Thms

/-!
# CLI behaviour, files and file transformers: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Cli`.

* **`Input.resolve_under`**: a path an argument resolves to is under a declared root.
* `failure_le_confined`, **`transform_le_confined`**: every file transformer stays inside its
  footprint (reads only under roots, writes only under writable roots), whatever its
  arguments resolve to.
* `transform_total`: a file transformer has an observation on every invocation.
* `logged_transform`: transformers log their file effects (exact pipes).
* `filter_iff`: a filter is deterministic; **`pipe_filter`**: `filter f | filter g` is
  `filter (g ∘ f)`.
-/

@[expose] public section

namespace Silmaril.Cli

theorem Input.resolve_under {i : Input} {s : String} {p : FPath} (h : i.resolve s = some p) :
    i.Under p := by
  unfold Input.resolve at h
  simp only at h
  split_ifs at h with h1 h2 h3
  · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact List.mem_map.2 ⟨r, List.mem_of_find?_eq_some hr, rfl⟩
  · cases h
    obtain ⟨r, hr, hn⟩ := List.any_eq_true.1 h3
    exact List.mem_map.2 ⟨r, hr, by simpa using hn⟩

namespace Spec

theorem failure_le_confined : failure ≤ confined := by
  rintro i o ⟨-, -, -, hr, hfs, hc, -⟩
  refine ⟨fun p hp => (by rw [hr] at hp; cases hp), fun p hp => absurd (congrFun hfs p) hp, hc⟩

theorem Source.reads_under {i : Input} {s : Source} {x : Bytes} (h : s.read i = some x) :
    ∀ p ∈ s.reads, i.Under p := by
  cases s with
  | stdin => intro p hp; cases hp
  | file q =>
    intro p hp
    have hpq : p = q := List.mem_singleton.1 hp
    by_cases hu : i.Under q
    · exact hpq ▸ hu
    · simp [Source.read, hu] at h

theorem Source.consumed_le (i : Input) (s : Source) : s.consumed i ≤ i.stdin.length := by
  cases s <;> simp [Source.consumed]

theorem transformAt_le_confined (s : Source) (d : Sink) (f : Bytes → Except Bytes Bytes) :
    transformAt s d f ≤ confined := by
  intro i o h
  unfold transformAt at h
  split at h
  · exact failure_le_confined i o h
  · next x hx =>
    split at h
    · subst h
      exact ⟨Source.reads_under hx, fun p hp => absurd rfl hp, Source.consumed_le i s⟩
    · rcases h with ⟨hok, rfl⟩ | ⟨-, hf⟩
      · show confined i (d.write i (s.consumed i) s.reads (s.log i) _)
        cases d with
        | stdout => exact ⟨Source.reads_under hx, fun p hp => absurd rfl hp, Source.consumed_le i s⟩
        | file q =>
          refine ⟨Source.reads_under hx, fun p hp => ?_, Source.consumed_le i s⟩
          by_cases hpq : p = q
          · exact hpq ▸ hok
          · exact absurd (by simp [Sink.write, Fs.set, hpq]) hp
      · exact failure_le_confined i o hf

/-- **File transformers stay inside their footprint.** -/
theorem transform_le_confined (src : Input → Option Source) (dst : Input → Option Sink)
    (f : Input → Bytes → Except Bytes Bytes) : transform src dst f ≤ confined := by
  intro i o h
  unfold transform at h
  split at h
  · exact transformAt_le_confined _ _ _ i o h
  · exact failure_le_confined i o h

theorem failure_total : failure.Total := fun i =>
  ⟨{ stderr := [0], exit := 1, fs := i.fs }, (by decide : (1 : ExitCode) ≠ 0), by simp, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

theorem transform_total (src : Input → Option Source) (dst : Input → Option Sink)
    (f : Input → Bytes → Except Bytes Bytes) : (transform src dst f).Total := by
  intro i
  unfold transform
  split
  · next s d _ _ =>
    unfold transformAt
    split
    · exact failure_total i
    · split
      · exact ⟨_, rfl⟩
      · by_cases hok : d.Ok i
        · exact ⟨_, .inl ⟨hok, rfl⟩⟩
        · obtain ⟨o, ho⟩ := failure_total i
          exact ⟨o, .inr ⟨hok, ho⟩⟩
  · exact failure_total i

/-- A filter is deterministic. -/
theorem filter_iff {f : Bytes → Bytes} {i : Input} {o : Obs} :
    filter f i o ↔ o = { stdout := f i.stdin, consumed := i.stdin.length, fs := i.fs } := by
  simp [filter, transform, transformAt, Source.read, Sink.Ok, Sink.write, Source.consumed,
    Source.reads, Source.log]

/-- The two runs of a pipe of filters, and the pipe's run. -/
private theorem pipe_filter_obs {f g : Bytes → Bytes} {i : Input} {o : Obs}
    (h : pipe (filter f) (filter g) i o) :
    o = { stdout := g (f i.stdin), consumed := i.stdin.length, fs := i.fs } := by
  obtain ⟨⟨o₁, o₂, fs₁, fs₂, h₁, h₂, hs, he, hx, hc, hr, hl, hd⟩, hcoh⟩ := h
  have e₁ : o₁ = { stdout := f i.stdin, consumed := i.stdin.length, fs := fs₁ } := filter_iff.1 h₁
  subst e₁
  have e₂ : o₂ = { stdout := g (f i.stdin), consumed := (f i.stdin).length, fs := fs₂ } :=
    filter_iff.1 h₂
  subst e₂
  have herr : o.stderr = [] := Interleave.nil_left_eq he
  have hlog : o.log = [] := Interleave.nil_left_eq hl
  have hfs : o.fs = i.fs := by
    have hr' : i.fs.replay o.log = some o.fs := hcoh
    rw [hlog, Fs.replay_nil] at hr'
    exact (Option.some.inj hr').symm
  cases o
  simp only at hs hx hc hr hd herr hlog hfs
  simp [hs, hx, hc, hr, hd, herr, hlog, hfs]

/-- **Pipes of filters compose their functions.** -/
theorem pipe_filter (f g : Bytes → Bytes) : pipe (filter f) (filter g) = filter (g ∘ f) := by
  funext i o
  apply propext
  rw [filter_iff]
  constructor
  · exact pipe_filter_obs
  · rintro rfl
    have h₁ : filter f { i with fs := i.fs }
        { stdout := f i.stdin, consumed := i.stdin.length, fs := i.fs } := filter_iff.2 rfl
    exact ⟨⟨_, _, i.fs, i.fs, h₁, filter_iff.2 rfl, rfl, .nil, rfl, rfl, rfl, .nil, rfl⟩, rfl⟩

theorem logged_failure : failure.Logged := by
  rintro i o ⟨-, -, -, -, hfs, -, hlog⟩
  show i.fs.replay o.log = some o.fs
  rw [hlog, hfs]; rfl

/-- Reading a source that can be read replays: the read sees what the file holds. -/
theorem Source.replay_log {i : Input} {s : Source} {x : Bytes} (_ : s.read i = some x) :
    i.fs.replay (s.log i) = some i.fs := by
  cases s with
  | stdin => rfl
  | file p => simp [Source.log, Fs.replay_read]

/-- Writing a result to a sink after reading the source replays to the sink's files. -/
theorem Sink.replay_write {i : Input} {s : Source} {x : Bytes} (hx : s.read i = some x)
    (d : Sink) (y : Bytes) :
    i.fs.replay (d.write i (s.consumed i) s.reads (s.log i) y).log =
      some (d.write i (s.consumed i) s.reads (s.log i) y).fs := by
  cases d with
  | stdout => exact Source.replay_log hx
  | file q =>
    show i.fs.replay (s.log i ++ [.write q (some y)]) = some (i.fs.set q (some y))
    rw [Fs.replay_append, Source.replay_log hx]; rfl

theorem logged_transformAt (s : Source) (d : Sink) (f : Bytes → Except Bytes Bytes) :
    (transformAt s d f).Logged := by
  intro i o h
  unfold transformAt at h
  split at h
  · exact logged_failure i o h
  · next x hx =>
    split at h
    · show i.fs.replay o.log = some o.fs
      rw [h]; exact Source.replay_log hx
    · rcases h with ⟨-, rfl⟩ | ⟨-, hf⟩
      · exact Sink.replay_write hx d _
      · exact logged_failure i o hf

/-- **File transformers log their file effects**, so they compose exactly in pipes. -/
theorem logged_transform (src : Input → Option Source) (dst : Input → Option Sink)
    (f : Input → Bytes → Except Bytes Bytes) : (transform src dst f).Logged := by
  intro i o h
  unfold transform at h
  split at h
  · exact logged_transformAt _ _ _ i o h
  · exact logged_failure i o h

end Spec

end Silmaril.Cli
