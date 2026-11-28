module

public import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable.Safety

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine.Writable

variable {F : Footprint} {cat : Catalog}

/-- Prefix safety of the executable runner from a fresh configuration. -/
theorem run_initial_safe (F : Footprint) (cat : Catalog) (code : RawProgram) (fuel : Nat)
    (store : Store) :
    let out := run F cat code fuel (Config.initial store)
    Inv F out.config ∧ (∀ event ∈ out.events, event.Allowed F) ∧
      (∀ table, Event.write table ∉ out.events →
        out.config.working table = store table ∧ out.config.committed table = store table) ∧
      (Event.commit ∉ out.events → out.config.committed = store) :=
  trace_initial_safe (fallbackSafe_none F) (run_trace code fuel _)

theorem not_write_of_allowed {events : List Event} {table : TableId}
    (allowed : ∀ event ∈ events, event.Allowed F) (h : ¬ F.Writes table) :
    Event.write table ∉ events :=
  fun hmem => h (allowed _ hmem)

/-- A request whose touch the footprint permits behaves as without a guard. -/
theorem exec_eq_top {instr : Instr} (c : Config)
    (h : (instr.touch? cat).all F.allows = true) :
    exec F cat instr c = exec Footprint.top cat instr c := by
  cases instr with
  | transaction slot mode =>
      simp only [exec]
      cases hslot : cat.slot slot with
      | none => rfl
      | some db =>
          simp only [Instr.touch?, hslot, Option.map_some, Option.all_some] at h
          simp [h, Footprint.top]
  | openRead identifier root slot =>
      simp only [exec, openCursor]
      cases hres : cat.resolve slot root with
      | none => rfl
      | some table =>
          simp only [Instr.touch?, hres, Option.map_some, Option.all_some] at h
          simp [h, Footprint.top]
  | openWrite identifier root slot =>
      simp only [exec, openCursor]
      cases hres : cat.resolve slot root with
      | none => rfl
      | some table =>
          simp only [Instr.touch?, hres, Option.map_some, Option.all_some] at h
          simp [h, Footprint.top]
  | _ => rfl

private theorem rawWithin_of_within {code : RawProgram} {pc : Nat} {raw : RawInstruction}
    (h : within F cat code = true) (fetch : code[pc]? = some raw) :
    rawWithin F cat raw = true := by
  unfold within at h
  rw [List.all_eq_true] at h
  exact h raw (Array.mem_def.mp (Array.mem_of_getElem? fetch))

theorem step_eq_top {code : RawProgram} (h : within F cat code = true) (c : Config) :
    step F cat code c = step Footprint.top cat code c := by
  unfold step
  split
  · rfl
  · cases hfetch : code[c.pc]? with
    | none => rfl
    | some raw =>
        have hraw := rawWithin_of_within h hfetch
        simp only
        unfold rawWithin at hraw
        cases hdec : decode? raw with
        | none => simp [hdec] at hraw
        | some instr =>
            simp only [hdec] at hraw
            exact exec_eq_top c hraw

/-- Guard transparency: under a footprint that contains the code's static
touches, the guarded runner and the unguarded runner agree on events, final
configuration and result. -/
theorem run_eq_top {code : RawProgram} (h : within F cat code = true) :
    ∀ (fuel : Nat) (c : Config), run F cat code fuel c = run Footprint.top cat code fuel c
  | fuel, c => by
      unfold run
      split
      · rfl
      · cases fuel with
        | zero => rfl
        | succ fuel =>
            simp only
            rw [step_eq_top h c]
            split
            · rfl
            · rw [run_eq_top h fuel]

/-- Under `within`, every unguarded step with any fallback is a guarded step
with no fallback. -/
theorem trace_of_within {code : RawProgram} (h : within F cat code = true) {fallback : Fallback}
    {c c' : Config} {events : List Event}
    (htrace : Trace Footprint.top cat fallback code c events c') :
    Trace F cat Fallback.none code c events c' := by
  induction htrace with
  | nil c => exact .nil c
  | cons hstep _ ih =>
      refine .cons ?_ ih
      cases hstep with
      | modeled active fetch decoded hexec =>
          have hraw := rawWithin_of_within h fetch
          simp only [rawWithin, decoded] at hraw
          exact .modeled active fetch decoded ((exec_eq_top _ hraw).trans hexec)
      | fallback _ fetch unmodeled _ =>
          have hraw := rawWithin_of_within h fetch
          simp [rawWithin, unmodeled] at hraw

theorem targetRestricted_of_within {code : RawProgram} (h : within F cat code = true) :
    TargetRestricted F cat code := by
  intro fallback store events c' htrace
  exact (trace_initial_safe (fallbackSafe_none F) (trace_of_within h htrace)).2.1

theorem within_mono {small large : Footprint} (hle : small.Le large) {code : RawProgram}
    (h : within small cat code = true) : within large cat code = true := by
  unfold within at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro raw hraw
  have := h raw hraw
  unfold rawWithin at this ⊢
  cases hd : decode? raw with
  | none => simp [hd] at this
  | some instr =>
      simp only [hd] at this ⊢
      cases htouch : instr.touch? cat with
      | none => rfl
      | some touch =>
          simp only [htouch, Option.all_some] at this ⊢
          exact hle touch this

/-- `staticTouches` lists exactly what `within` requires of a footprint. -/
theorem within_iff {code : RawProgram} :
    within F cat code = true ↔
      (∀ raw ∈ code.toList, (decode? raw).isSome = true) ∧
        ∀ touch ∈ staticTouches cat code, F.allows touch = true := by
  unfold within staticTouches
  rw [List.all_eq_true]
  constructor
  · intro h
    refine ⟨fun raw hraw => ?_, fun touch htouch => ?_⟩
    · have := h raw hraw
      unfold rawWithin at this
      split at this
      · cases this
      · rename_i heq; simp [heq]
    · obtain ⟨raw, hraw, hbind⟩ := List.mem_filterMap.mp htouch
      have := h raw hraw
      unfold rawWithin at this
      cases hdec : decode? raw with
      | none => simp [hdec] at this
      | some instr =>
          simp only [hdec, Option.bind_some] at this hbind
          simp only [hbind, Option.all_some] at this
          exact this
  · rintro ⟨hdec, htouch⟩ raw hraw
    unfold rawWithin
    cases hd : decode? raw with
    | none => simpa [hd] using hdec raw hraw
    | some instr =>
        simp only
        cases ht : instr.touch? cat with
        | none => rfl
        | some touch =>
            simp only [Option.all_some]
            exact htouch touch (List.mem_filterMap.mpr ⟨raw, hraw, by simp [hd, ht]⟩)

theorem trace_opens_configured {fallback : Fallback}
    (hfb : FallbackSafe F fallback) {code : RawProgram} {store : Store} {c' : Config}
    {events : List Event} (h : Trace F cat fallback code (Config.initial store) events c') :
    (∀ db mode, c'.transactions db = some mode → F.allows (.db db mode) = true) ∧
      (∀ identifier cursor, c'.cursors identifier = some cursor →
        F.allows (.table cursor.table cursor.mode) = true ∧ F.Configured cursor.table.db) := by
  obtain ⟨inv, _, _, _⟩ := trace_initial_safe hfb h
  refine ⟨inv.transactions, fun identifier cursor hc => ⟨(inv.cursors identifier cursor hc).1, ?_⟩⟩
  have hcov := (inv.cursors identifier cursor hc).2
  cases htx : c'.transactions cursor.table.db with
  | none => simp [htx, Mode.covers] at hcov
  | some mode => exact ⟨mode, inv.transactions _ _ htx⟩

theorem trace_frame {fallback : Fallback}
    (hfb : FallbackSafe F fallback) {code : RawProgram} {store : Store} {c' : Config}
    {events : List Event} (h : Trace F cat fallback code (Config.initial store) events c') :
    Frame F.Writes store c'.working ∧ Frame F.Writes store c'.committed := by
  obtain ⟨_, allowed, frame, _⟩ := trace_initial_safe hfb h
  exact ⟨fun table hw => (frame table (not_write_of_allowed allowed hw)).1,
    fun table hw => (frame table (not_write_of_allowed allowed hw)).2⟩

theorem run_readOnly (F : Footprint) (cat : Catalog) (code : RawProgram) (fuel : Nat)
    (store : Store) :
    let out := run F.readOnly cat code fuel (Config.initial store)
    (∀ table, Event.write table ∉ out.events) ∧ out.config.working = store ∧
      out.config.committed = store := by
  obtain ⟨_, allowed, frame, _⟩ := run_initial_safe F.readOnly cat code fuel store
  have hnot : ∀ table, Event.write table ∉ (run F.readOnly cat code fuel (Config.initial store)).events :=
    fun table => not_write_of_allowed allowed (by simp [Footprint.Writes, Footprint.readOnly])
  exact ⟨hnot, funext fun table => (frame table (hnot table)).1,
    funext fun table => (frame table (hnot table)).2⟩

/-- A table no step wrote is unchanged; the union of two frames is a frame. -/
theorem frame_trans {small large : TableId → Prop} {s₁ s₂ s₃ : Store}
    (h₁ : Frame small s₁ s₂) (h₂ : Frame large s₂ s₃) :
    Frame (fun table => small table ∨ large table) s₁ s₃ :=
  fun table h => (h₂ table fun hl => h (Or.inr hl)).trans (h₁ table fun hs => h (Or.inl hs))

/-! ### Autocommit scripts -/

theorem runScript_safe (F : Footprint) (cat : Catalog) (fuel : Nat) :
    ∀ (codes : List RawProgram) (store : Store),
      (∀ event ∈ (runScript F cat fuel codes store).1, event.Allowed F) ∧
        Frame (fun table => Event.write table ∈ (runScript F cat fuel codes store).1)
          store (runScript F cat fuel codes store).2
  | [], store => ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
  | code :: rest, store => by
      obtain ⟨_, allowed, frame, _⟩ := run_initial_safe F cat code fuel store
      obtain ⟨allowedRest, frameRest⟩ := runScript_safe F cat fuel rest
        (run F cat code fuel (Config.initial store)).config.committed
      refine ⟨?_, ?_⟩
      · intro event hmem
        rcases List.mem_append.mp hmem with h | h
        · exact allowed event h
        · exact allowedRest event h
      · intro table hnot
        simp only [runScript, List.mem_append, not_or] at hnot
        exact (frameRest table hnot.2).trans (frame table hnot.1).2

theorem runScript_frame (F : Footprint) (cat : Catalog) (fuel : Nat) (codes : List RawProgram)
    (store : Store) : Frame F.Writes store (runScript F cat fuel codes store).2 := by
  obtain ⟨allowed, frame⟩ := runScript_safe F cat fuel codes store
  exact fun table h => frame table (not_write_of_allowed allowed h)

theorem runScript_eq_top {fuel : Nat} :
    ∀ {codes : List RawProgram}, (∀ code ∈ codes, within F cat code = true) →
      ∀ store, runScript F cat fuel codes store = runScript Footprint.top cat fuel codes store
  | [], _, _ => rfl
  | code :: rest, h, store => by
      simp only [runScript]
      rw [run_eq_top (h code List.mem_cons_self)]
      rw [runScript_eq_top (fun c hc => h c (List.mem_cons_of_mem _ hc))]

end Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable
