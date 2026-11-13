module

public import Silmaril.Net.Tcp.Service.Defs

/-!
# TCP byte-stream service: theorems

PROVED (standard axioms):

* `SvcSteps.trans`, `SvcSteps.single`.
* **`svcStep_ok`**, **`svcSteps_ok`**: steps and runs keep `Svc.Ok`; so in every admitted
  trace the octets read are a prefix of the octets written, and end of stream comes only after
  CLOSE with everything read (`svcAdmits_ok`).
* **Rechunking**: `read_split` (a read of `a ++ b` is the same as a read of `a` then a read of
  `b`) and `read_merge` (the converse), `write_split`: the service does not see chunk
  boundaries, as for the byte-chunk streams of `docs/projects/wasm-wasi.md`.
* `read_all`: when the sender wrote `w` and nothing was read, reading `w` in one chunk is
  admitted; `close_then_eof`: after CLOSE and a full read, end of stream is admitted.
-/

@[expose] public section

namespace Silmaril.Net.Tcp

theorem SvcSteps.single {s e s'} (h : SvcStep s e s') : SvcSteps s [e] s' := .cons h (.refl _)

theorem SvcSteps.trans {s l s' m s''} (h1 : SvcSteps s l s') (h2 : SvcSteps s' m s'') :
    SvcSteps s (l ++ m) s'' := by
  induction h1 with
  | refl => exact h2
  | cons h _ ih => exact .cons h (ih h2)

/-- **A step keeps the safety invariant.** -/
theorem svcStep_ok {s e s'} (hs : s.Ok) (h : SvcStep s e s') : s'.Ok := by
  cases h with
  | write bs hc =>
    refine ⟨hs.1.trans (List.prefix_append _ _), fun he => ?_⟩
    have := (hs.2 he).1
    rw [hc] at this; cases this
  | close hc =>
    refine ⟨hs.1, fun he => ?_⟩
    have := (hs.2 he).1
    rw [hc] at this; cases this
  | read bs hne hp =>
    refine ⟨hp, fun he => ?_⟩
    have h2 := (hs.2 he).2
    have hl : (s.read ++ bs).length ≤ s.written.length := hp.length_le
    have hb : bs.length ≠ 0 := by simpa using hne
    rw [List.length_append, h2] at hl
    omega
  | eof hc hr _ => exact ⟨hs.1, fun _ => ⟨hc, hr⟩⟩

/-- **Runs keep the safety invariant.** -/
theorem svcSteps_ok {s l s'} (hs : s.Ok) (h : SvcSteps s l s') : s'.Ok := by
  induction h with
  | refl => exact hs
  | cons hstep _ ih => exact ih (svcStep_ok hs hstep)

/-- In every admitted trace, the reads are a prefix of the writes, and end of stream comes only
after CLOSE with everything read. -/
theorem svcAdmits_ok {tr} (h : SvcAdmits tr) : ∃ s, SvcSteps {} tr s ∧ s.Ok := by
  obtain ⟨s, hs⟩ := h
  have h0 : ({} : Svc).Ok := ⟨List.nil_prefix, fun h => by cases h⟩
  exact ⟨s, hs, svcSteps_ok h0 hs⟩

/-- **A read of `a ++ b` is a read of `a` then of `b`.** -/
theorem read_split {s s'} {a b : List UInt8} (ha : a ≠ []) (hb : b ≠ [])
    (h : SvcStep s (.read (a ++ b)) s') :
    SvcSteps s [.read a, .read b] s' := by
  cases h with
  | read _ _ hp =>
    have hpa : s.read ++ a <+: s.written := by
      have : s.read ++ a <+: s.read ++ (a ++ b) := by
        rw [← List.append_assoc]; exact List.prefix_append _ _
      exact this.trans hp
    have hpb : (s.read ++ a) ++ b <+: s.written := by rwa [List.append_assoc]
    have h1 : SvcStep s (.read a) { s with read := s.read ++ a } := .read a ha hpa
    have h2 : SvcStep { s with read := s.read ++ a } (.read b)
        { s with read := s.read ++ a ++ b } := .read b hb hpb
    have he : ({ s with read := s.read ++ a ++ b } : Svc) = { s with read := s.read ++ (a ++ b) } := by
      rw [List.append_assoc]
    exact .cons h1 (he ▸ .single h2)

/-- **Two reads are one read of their concatenation.** -/
theorem read_merge {s s' s''} {a b : List UInt8} (h1 : SvcStep s (.read a) s')
    (h2 : SvcStep s' (.read b) s'') : SvcStep s (.read (a ++ b)) s'' := by
  cases h1 with
  | read _ ha _ =>
    cases h2 with
    | read _ _ hp =>
      have hne : a ++ b ≠ [] := by simp [ha]
      have hp' : s.read ++ (a ++ b) <+: s.written := by rwa [← List.append_assoc]
      have := SvcStep.read (s := s) (a ++ b) hne hp'
      simpa [List.append_assoc] using this

/-- **A write of `a ++ b` is a write of `a` then of `b`.** -/
theorem write_split {s s'} {a b : List UInt8} (h : SvcStep s (.write (a ++ b)) s') :
    SvcSteps s [.write a, .write b] s' := by
  cases h with
  | write _ hc =>
    have h1 : SvcStep s (.write a) { s with written := s.written ++ a } := .write a hc
    have h2 : SvcStep { s with written := s.written ++ a } (.write b)
        { s with written := s.written ++ a ++ b } := .write b hc
    have he : ({ s with written := s.written ++ a ++ b } : Svc) =
        { s with written := s.written ++ (a ++ b) } := by rw [List.append_assoc]
    exact .cons h1 (he ▸ .single h2)

/-- When nothing was read, reading everything written in one chunk is admitted. -/
theorem read_all {s : Svc} (hr : s.read = []) (hw : s.written ≠ []) :
    SvcStep s (.read s.written) { s with read := s.written } := by
  have h := SvcStep.read (s := s) s.written hw (by rw [hr]; exact List.prefix_refl _)
  simpa [hr] using h

/-- After CLOSE and a full read, end of stream is admitted. -/
theorem close_then_eof {s : Svc} (hc : s.closed = true) (hr : s.read = s.written)
    (he : s.eof = false) : SvcStep s .eof { s with eof := true } := .eof hc hr he

end Silmaril.Net.Tcp
