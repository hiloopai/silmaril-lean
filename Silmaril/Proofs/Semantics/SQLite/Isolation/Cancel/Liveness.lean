module

public import Silmaril.Semantics.SQLite.Isolation.Cancel.Defs

public section

namespace Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel

open Silmaril.Semantics.SQLite.Isolation.Cancel

/-! ## Machine level -/

theorem stopped_step {P : Profile} {H : HelperDiscipline} {code : List Nat} {vis : Bool}
    {s : MState} {r : StopReason} (h : s.status = .stopped r) : s.step P H code vis = s := by
  simp [MState.step, h]

theorem stopped_resume {s : MState} {r : StopReason} (h : s.status = .stopped r) :
    s.resume = s := by
  simp [MState.resume, h]

theorem exec_vis {p : Nat} (s : MState) (hs : s.status = .running) (i : Instr)
    (hlt : s.sincePoll < p) :
    (s.exec true i).Stopped ∨
      ((s.exec true i).active = true ∧ p - (s.exec true i).sincePoll < p - s.sincePoll) := by
  cases i with
  | halt => exact .inl ⟨_, rfl⟩
  | work => exact .inr ⟨by simp [MState.exec, MState.active, hs], by simp [MState.exec]; omega⟩
  | jump t =>
    exact .inr ⟨by simp [MState.exec, MState.active, hs], by simp [MState.exec]; omega⟩
  | branch t =>
    cases hin : s.input with
    | nil => exact .inl ⟨.inputExhausted, by simp [MState.exec, hin, MState.stopWith]⟩
    | cons b rest =>
      exact .inr ⟨by simp [MState.exec, hin, MState.active, hs],
        by simp [MState.exec, hin]; omega⟩
  | helper n =>
    exact .inr ⟨by simp [MState.exec, MState.active, hs], by simp [MState.exec]; omega⟩
  | call => exact .inr ⟨by simp [MState.exec, MState.active], by simp [MState.exec]; omega⟩
  | poll => exact .inl ⟨.cancelled, by simp [MState.exec, MState.poll, MState.stopWith]⟩
  | unsupported _ => exact .inl ⟨_, rfl⟩
  | malformed _ => exact .inl ⟨_, rfl⟩

theorem step_vis {P : Profile} {H : HelperDiscipline} (code : List Nat) {s : MState}
    (hH : H.pollsInside = true) (hs : s.status = .running) :
    (s.step P H code true).Stopped ∨
      ((s.step P H code true).active = true ∧
        (s.step P H code true).rank P < s.rank P) := by
  unfold MState.step; rw [hs]; unfold MState.runningStep MState.rank
  by_cases hhelp : s.helperLeft = 0
  · by_cases hp : P.period ≤ s.sincePoll
    · exact .inl ⟨.cancelled, by simp [hhelp, hp, MState.poll, MState.stopWith]⟩
    · cases hc : code[s.pc]? with
      | none => exact .inl ⟨.pcOutOfRange, by simp [hhelp, hp, MState.stopWith]⟩
      | some raw =>
        simpa [hhelp, hp, hc] using exec_vis (p := P.period) s hs (decode raw) (by omega)
  · by_cases hp : P.period ≤ s.sincePoll
    · exact .inl ⟨.cancelled, by simp [hhelp, hH, hp, MState.poll, MState.stopWith]⟩
    · refine .inr ⟨by simp [hhelp, hH, hp, MState.active, hs], ?_⟩
      simp [hhelp, hH, hp]; omega

theorem active_of_not_stopped {s : MState} (h : s.active = true) : ¬ s.Stopped := by
  rintro ⟨r, hr⟩
  simp [MState.active, hr] at h

theorem poll_due {P : Profile} {H : HelperDiscipline} (code : List Nat) {s : MState}
    (hs : s.status = .running) (hp : P.period ≤ s.sincePoll)
    (hh : s.helperLeft = 0 ∨ H.pollsInside = true) :
    s.step P H code true = s.stopWith .cancelled := by
  unfold MState.step; rw [hs]; unfold MState.runningStep
  rcases hh with hh | hh
  · simp [hh, hp, MState.poll]
  · by_cases hl : s.helperLeft = 0 <;> simp [hl, hh, hp, MState.poll]

theorem drive_stopped {P : Profile} {H : HelperDiscipline} {code : List Nat} {vis : Bool} :
    ∀ (k : Nat) {s : MState} {r : StopReason}, s.status = .stopped r →
      MState.drive P H code vis k s = s
  | 0, _, _, _ => rfl
  | k + 1, s, r, h => by
    simp only [MState.drive, stopped_step h, stopped_resume h]
    exact drive_stopped k h

theorem resume_running {s : MState} (h : s.active = true) :
    s.resume.status = .running ∧ s.resume.sincePoll = s.sincePoll := by
  unfold MState.resume
  cases hs : s.status with
  | running => simp [hs]
  | waiting => simp
  | stopped r => simp [MState.active, hs] at h

theorem drive_stops {P : Profile} {H : HelperDiscipline} (code : List Nat)
    (hH : H.pollsInside = true) :
    ∀ (k : Nat) {s : MState}, s.status = .running → s.rank P < k →
      (MState.drive P H code true k s).Stopped
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, s, hs, hk => by
    simp only [MState.drive]
    rcases step_vis code hH hs with ⟨r, hr⟩ | ⟨ha, hlt⟩
    · rw [stopped_resume hr, drive_stopped k hr]; exact ⟨r, hr⟩
    · obtain ⟨h1, h2⟩ := resume_running ha
      apply drive_stops code hH k h1
      simp only [MState.rank] at hlt hk ⊢
      omega

/-! ## System level -/

section System

variable {P : Profile} {H : HelperDiscipline} {code : List Nat} {s₀ : Sys} {ev : Nat → Ev}

/-- The liveness measure: twice the rank, plus one while waiting on the host. -/
def measure (P : Profile) (s : Sys) : Nat :=
  2 * s.mach.rank P + if s.mach.status = .waiting then 1 else 0

/-- The event that moves an operation with status `st`. -/
def enabling : Status → Ev
  | .running => .run
  | .waiting => .extReturn
  | .stopped _ => .idle

theorem frozen {s : Sys} {e : Ev} (hv : s.visible = true) (ha : s.mach.active = true)
    (hc : e ≠ .clear) (hn : e ≠ enabling s.mach.status) :
    (s.step P H code e).mach = s.mach ∧ (s.step P H code e).visible = true := by
  cases hst : s.mach.status with
  | stopped r => simp [MState.active, hst] at ha
  | running =>
    rw [hst] at hn
    cases e with
    | idle => exact ⟨rfl, hv⟩
    | run => exact absurd rfl hn
    | extReturn => simp [Sys.step, MState.resume, hst, hv]
    | deliver e =>
      by_cases hd : e = s.epoch ∧ s.mach.active = true <;> simp [Sys.step, hd, hv]
    | publish => simp [Sys.step, hv]
    | clear => exact absurd rfl hc
    | begin e m => simp [Sys.step, ha, hv]
  | waiting =>
    rw [hst] at hn
    cases e with
    | idle => exact ⟨rfl, hv⟩
    | run => simp [Sys.step, MState.step, hst, hv]
    | extReturn => exact absurd rfl hn
    | deliver e =>
      by_cases hd : e = s.epoch ∧ s.mach.active = true <;> simp [Sys.step, hd, hv]
    | publish => simp [Sys.step, hv]
    | clear => exact absurd rfl hc
    | begin e m => simp [Sys.step, ha, hv]

theorem enabled (hH : H.pollsInside = true) {s : Sys} (hv : s.visible = true)
    (ha : s.mach.active = true) :
    (s.step P H code (enabling s.mach.status)).visible = true ∧
      ((s.step P H code (enabling s.mach.status)).mach.Stopped ∨
        ((s.step P H code (enabling s.mach.status)).mach.active = true ∧
          measure P (s.step P H code (enabling s.mach.status)) < measure P s)) := by
  cases hst : s.mach.status with
  | stopped r => simp [MState.active, hst] at ha
  | running =>
    simp only [enabling]
    have hm : (s.step P H code .run).mach = s.mach.step P H code true := by simp [Sys.step, hv]
    refine ⟨by simp [Sys.step, hv], ?_⟩
    rcases step_vis (P := P) code hH hst with h | ⟨ha', hlt⟩
    · exact .inl (hm ▸ h)
    · refine .inr ⟨hm ▸ ha', ?_⟩
      simp only [measure, hm, hst]
      split <;> simp <;> omega
  | waiting =>
    simp only [enabling]
    have hm : (s.step P H code .extReturn).mach = { s.mach with status := .running } := by
      simp [Sys.step, MState.resume, hst]
    refine ⟨by simp [Sys.step, hv], .inr ⟨by simp [hm, MState.active], ?_⟩⟩
    simp [measure, hm, MState.rank, hst]

theorem reach (hH : H.pollsInside = true) :
    ∀ (d n : Nat), ev (n + d) = enabling (run P H code s₀ ev n).mach.status →
      (run P H code s₀ ev n).visible = true → (run P H code s₀ ev n).mach.active = true →
      (∀ m, n ≤ m → ev m ≠ .clear) →
      ∃ n', n < n' ∧ (run P H code s₀ ev n').visible = true ∧
        ((run P H code s₀ ev n').mach.Stopped ∨
          ((run P H code s₀ ev n').mach.active = true ∧
            measure P (run P H code s₀ ev n') < measure P (run P H code s₀ ev n))) := by
  intro d
  induction d with
  | zero =>
    intro n he hv ha _
    have h := enabled (P := P) (H := H) (code := code) hH hv ha
    rw [← he] at h
    exact ⟨n + 1, Nat.lt_succ_self n, h⟩
  | succ d ih =>
    intro n he hv ha hc
    by_cases hn : ev n = enabling (run P H code s₀ ev n).mach.status
    · have h := enabled (P := P) (H := H) (code := code) hH hv ha
      rw [← hn] at h
      exact ⟨n + 1, Nat.lt_succ_self n, h⟩
    · obtain ⟨hm, hv'⟩ := frozen (P := P) (H := H) (code := code) hv ha
        (hc n (Nat.le_refl n)) hn
      have hm' : (run P H code s₀ ev (n + 1)).mach = (run P H code s₀ ev n).mach := hm
      have hv'' : (run P H code s₀ ev (n + 1)).visible = true := hv'
      obtain ⟨n', hlt, hrest⟩ := ih (n + 1)
        (by rw [hm', show n + 1 + d = n + (d + 1) by omega]; exact he)
        hv'' (by rw [hm']; exact ha) (fun m hm => hc m (by omega))
      refine ⟨n', by omega, ?_⟩
      have : measure P (run P H code s₀ ev (n + 1)) = measure P (run P H code s₀ ev n) := by
        simp only [measure, hm']
      rw [← this]
      exact hrest

theorem cancel_liveness (hH : H.pollsInside = true) {t : Nat} (hfair : FairFrom ev t)
    (hext : ExternalReturnsFrom P H code s₀ ev t) (hcoh : CoherentFrom ev t)
    (hvis : (run P H code s₀ ev t).RelevantVisible) :
    ∃ m, t ≤ m ∧ (run P H code s₀ ev m).mach.Stopped := by
  suffices key : ∀ k n, t ≤ n → measure P (run P H code s₀ ev n) < k →
      (run P H code s₀ ev n).visible = true → (run P H code s₀ ev n).mach.active = true →
      ∃ m, n ≤ m ∧ (run P H code s₀ ev m).mach.Stopped by
    obtain ⟨m, hm, hs⟩ := key _ t (Nat.le_refl t) (Nat.lt_succ_self _) hvis.1 hvis.2
    exact ⟨m, hm, hs⟩
  intro k
  induction k with
  | zero => intro n _ h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro n htn hk hv ha
    have hev : ∃ m, n ≤ m ∧ ev m = enabling (run P H code s₀ ev n).mach.status := by
      cases hst : (run P H code s₀ ev n).mach.status with
      | running => exact hfair n htn
      | waiting => exact hext n htn hst
      | stopped r => simp [MState.active, hst] at ha
    obtain ⟨m, hnm, hm⟩ := hev
    obtain ⟨n', hlt, hv', hres⟩ := reach (P := P) (H := H) (code := code) (s₀ := s₀) hH
      (m - n) n (by rw [show n + (m - n) = m by omega]; exact hm) hv ha
      (fun j hj => hcoh j (by omega))
    rcases hres with hs | ⟨ha', hμ⟩
    · exact ⟨n', by omega, hs⟩
    · obtain ⟨m', hm', hs⟩ := ih n' (by omega) (by omega) hv' ha'
      exact ⟨m', by omega, hs⟩

theorem one_step_rank (hH : H.pollsInside = true) {s : Sys} {e : Ev} (hv : s.visible = true)
    (ha : s.mach.active = true) (hc : e ≠ .clear) (ha' : (s.step P H code e).mach.active = true) :
    (s.step P H code e).visible = true ∧
      (s.step P H code e).mach.rank P + (if Counted s e then 1 else 0) ≤ s.mach.rank P := by
  by_cases hn : e = enabling s.mach.status
  · subst hn
    cases hst : s.mach.status with
    | stopped r => simp [MState.active, hst] at ha
    | running =>
      have := enabled (P := P) (H := H) (code := code) hH hv ha
      simp only [hst] at this ha' ⊢
      refine ⟨this.1, ?_⟩
      rcases step_vis (P := P) code hH hst with h | ⟨_, hlt⟩
      · exact absurd h (active_of_not_stopped (by simpa [enabling, Sys.step, hv] using ha'))
      · simp [enabling, Counted, Sys.step, hv, hst]
        omega
    | waiting =>
      simp [enabling, Counted, Sys.step, hv, MState.resume, MState.rank, hst]
  · obtain ⟨hm, hv'⟩ := frozen (P := P) (H := H) (code := code) hv ha hc hn
    refine ⟨hv', ?_⟩
    rw [hm]
    have : Counted s e = false := by
      cases e with
      | run =>
        cases hst : s.mach.status with
        | running => simp [enabling, hst] at hn
        | waiting => simp [Counted, hst]
        | stopped r => simp [MState.active, hst] at ha
      | _ => rfl
    simp [this]

theorem counted_bound (hH : H.pollsInside = true) {t : Nat} (hcoh : CoherentFrom ev t)
    (hvis : (run P H code s₀ ev t).RelevantVisible) :
    ∀ k, (∀ j, j ≤ k → (run P H code s₀ ev (t + j)).mach.active = true) →
      countedAfter P H code s₀ ev t k + (run P H code s₀ ev (t + k)).mach.rank P ≤
          (run P H code s₀ ev t).mach.rank P ∧
        (run P H code s₀ ev (t + k)).visible = true := by
  intro k
  induction k with
  | zero => intro _; exact ⟨by simp [countedAfter], hvis.1⟩
  | succ k ih =>
    intro hact
    obtain ⟨h1, h2⟩ := ih (fun j hj => hact j (by omega))
    have hstep := one_step_rank (P := P) (H := H) (code := code) (e := ev (t + k)) hH h2
      (hact k (by omega)) (hcoh _ (by omega)) (hact (k + 1) (Nat.le_refl _))
    refine ⟨?_, hstep.1⟩
    have := hstep.2
    simp only [countedAfter]
    show _ + (((run P H code s₀ ev (t + k)).step P H code (ev (t + k))).mach.rank P) ≤ _
    omega

end System

end Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel
