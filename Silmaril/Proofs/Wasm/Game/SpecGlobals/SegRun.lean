module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegRunBase
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.InstGen
public import Silmaril.Proofs.Wasm.Game.Machine.Doomed
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitTrap

/-!
# Segment initialisation is a forced run, every profile

The segment-initialisation code of `$instantiate` (`segCode m`, the code `prepare?` builds:
`$runelem_` and `$rundata_` of every segment, i.e. offsets, `table.init`/`memory.init`,
`elem.drop`/`data.drop`) runs **deterministically under every profile** `P`, before any suffix
(for instance the start call):

* `segInit_ok`: if silmaril-lean's trap-aware direct initialisation `initSegmentsT?` succeeds
  with `(s', f')`, the run from `⟨s, f, segCode m ++ rest⟩` to `⟨s', f', rest⟩` is forced
  (`DetTo`: every configuration before the end has exactly one host-free successor, is not at a
  host call and is not a result);
* `segInit_trap`: if it traps at the store `s'`, the run is forced up to a configuration
  `⟨s', f, vals W ++ TRAP :: R⟩` (the out-of-bounds `table.init`/`memory.init` replaced by
  `TRAP`); from there every run only bubbles the trap (`Choice.doomed_step`), with the same
  store and frame.

Assumption: the offset expressions consist of constant instructions (`OffsetsConst`,
`Instr.IsConstI`), as validation requires (`InstrConst.isConstI`); this is not derived from
validation here. The `.fail` outcome of `initSegmentsT?` (a lookup or offset evaluation fails,
impossible for validated modules) is not covered.

The proof turns silmaril-lean's runs (`initSegments?_steps`, `initSegmentsT?_trap_steps`) into
forced runs: every configuration of such a run consists of values and `Good` or constant
instructions (`Inv`, preserved by `step_shape`), whose steps are unique
(`good_step_uniq`), until a trap, after which the configuration is doomed. New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Proofs.Wasm.Game.Choice

/-! ## Doomed configurations -/

theorem doomed_step {P : Profile} {E : Ctx} {s : Store Nat} {f : Frame} {d : Config Nat}
    (h : Step P noHost ⟨s, f, E.fill [.trap]⟩ d) : Doomed s f d := by
  rcases doomed_step_lt (P := P) E s f with hE | ⟨E', h₀, -⟩
  · have h' : Step P noHost ⟨s, f, [.trap]⟩ d := by
      rw [hE] at h
      exact h
    exact absurd h' not_step_trap
  · rcases eq_or_soft h₀ h with hd | hs
    · exact ⟨by rw [hd], by rw [hd], E', by rw [hd]⟩
    · exact soft_doomed E hs

theorem doomed_steps {P : Profile} {E : Ctx} {s : Store Nat} {f : Frame} {d : Config Nat}
    (h : Steps P noHost ⟨s, f, E.fill [.trap]⟩ d) : Doomed s f d := by
  induction h with
  | refl => exact ⟨rfl, rfl, E, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨hs, hf, E', hc⟩ := ih
    rename_i b _ _
    have hb : b = ⟨s, f, E'.fill [.trap]⟩ := by
      cases b
      simp only at hs hf hc
      rw [hs, hf, hc]
    exact doomed_step (hb ▸ hstep)

theorem fill_trap_not_vals (E : Ctx) (W : List Val) : E.fill [.trap] ≠ vals W := by
  have hne : ∃ a ∈ E.fill [.trap], a.val? = none := by
    cases E with
    | top pre rest => exact ⟨.trap, by simp [Ctx.fill], rfl⟩
    | label pre n cont E rest => exact ⟨.label n cont (E.fill [.trap]), by simp [Ctx.fill], rfl⟩
    | handler pre n cs E rest => exact ⟨.handler n cs (E.fill [.trap]), by simp [Ctx.fill], rfl⟩
    | frame pre n f E rest => exact ⟨.frame n f (E.fill [.trap]), by simp [Ctx.fill], rfl⟩
  obtain ⟨a, ha, hv⟩ := hne
  intro e
  rw [e] at ha
  simp only [vals, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Admin.val?] at hv

theorem trap_form_fill (W : List Val) (R : List Admin) :
    vals W ++ .trap :: R = (Ctx.top W R).fill [.trap] := by
  simp only [Ctx.fill, List.append_assoc, List.singleton_append]

/-! ## Runs through `Good` heads -/

/-- A run from code of values and `Good` or constant instructions to values is forced. -/
theorem run_gto {P : Profile} {c d : Config Nat} (hr : Steps P noHost c d) (hinv : Inv c.code)
    (hd : ∃ W, d.code = vals W) : GTo P c d := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head hstep hrest ih =>
    rename_i a c₁
    obtain ⟨s, f, code⟩ := a
    obtain ⟨hg, -, hout⟩ := step_shape hinv hstep
    rcases hout with hi | ⟨W, R, hc, -⟩
    · exact .step hstep hg (ih hi)
    · show GTo P _ d
      have hc₁ : c₁ = ⟨c₁.store, c₁.frame, (Ctx.top W R).fill [.trap]⟩ := by
        rw [← trap_form_fill, ← hc]
      have hdd : Doomed c₁.store c₁.frame d := doomed_steps (hc₁ ▸ hrest)
      obtain ⟨-, -, E', hE'⟩ := hdd
      obtain ⟨Wd, hWd⟩ := hd
      exact absurd (hE'.symm.trans hWd) (fill_trap_not_vals E' Wd)

/-- A run from code of values and `Good` or constant instructions to a trap is forced up to the
first configuration whose first non-value is `TRAP`, with the trap's store and frame. -/
theorem run_gto_trap {P : Profile} {c d : Config Nat} (hr : Steps P noHost c d)
    (hinv : Inv c.code) (hd : d.code = [.trap]) :
    ∃ W R, GTo P c ⟨d.store, d.frame, vals W ++ .trap :: R⟩ := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have h : Inv [Admin.trap] := hd ▸ hinv
    exact (h .trap (List.mem_singleton_self _)).elim
  | head hstep hrest ih =>
    rename_i a c₁
    obtain ⟨s, f, code⟩ := a
    obtain ⟨hg, -, hout⟩ := step_shape hinv hstep
    rcases hout with hi | ⟨W, R, hc, -⟩
    · obtain ⟨W, R, hgt⟩ := ih hi
      exact ⟨W, R, .step hstep hg hgt⟩
    · show ∃ W R, GTo P _ _
      have hc₁ : c₁ = ⟨c₁.store, c₁.frame, (Ctx.top W R).fill [.trap]⟩ := by
        rw [← trap_form_fill, ← hc]
      obtain ⟨hs, hf, -⟩ := doomed_steps (hc₁ ▸ hrest)
      have he : c₁ = ⟨d.store, d.frame, vals W ++ .trap :: R⟩ := by
        rw [hs, hf, ← hc]
      exact ⟨W, R, he ▸ GTo.single hstep hg⟩

/-! ## Segment code -/

/-- The offset expressions of the active segments consist of constant instructions. -/
def OffsetsConst (m : Module) : Prop :=
  (∀ e ∈ m.elems, ∀ y off, e.mode = .active y off → ∀ i ∈ off, i.IsConstI) ∧
    ∀ d ∈ m.data, ∀ y off, d.mode = .active y off → ∀ i ∈ off, i.IsConstI

theorem inv_expression {l : List Instr} (h : ∀ i ∈ l, OkAdmin (.plain i)) : Inv (expression l) := by
  intro a ha
  simp only [expression, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact h i hi

theorem ok_runElem {k : Nat} {e : Elem}
    (he : ∀ y off, e.mode = .active y off → ∀ i ∈ off, i.IsConstI) :
    ∀ i ∈ runElem k e, OkAdmin (.plain i) := by
  intro i hi
  unfold runElem at hi
  split at hi
  · exact absurd hi (List.not_mem_nil)
  · simp only [List.mem_singleton] at hi
    exact hi ▸ .inr trivial
  · rename_i y off hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | rfl | rfl | rfl | rfl
    · exact .inl (he y off hm i hi)
    all_goals first | exact .inl trivial | exact .inr trivial

theorem ok_runData {k : Nat} {d : Data}
    (hd : ∀ y off, d.mode = .active y off → ∀ i ∈ off, i.IsConstI) :
    ∀ i ∈ runData k d, OkAdmin (.plain i) := by
  intro i hi
  unfold runData at hi
  split at hi
  · exact absurd hi (List.not_mem_nil)
  · rename_i y off hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | rfl | rfl | rfl | rfl
    · exact .inl (hd y off hm i hi)
    all_goals first | exact .inl trivial | exact .inr trivial

theorem inv_segCode {m : Module} (hm : OffsetsConst m) : Inv (segCode m) := by
  have he : ∀ i ∈ ((List.range m.elems.length).zip m.elems).flatMap (fun (k, e) => runElem k e),
      OkAdmin (.plain i) := by
    intro i hi
    obtain ⟨⟨k, e⟩, hke, hi'⟩ := List.mem_flatMap.1 hi
    exact ok_runElem (hm.1 e (List.of_mem_zip hke).2) i hi'
  have hd : ∀ i ∈ ((List.range m.data.length).zip m.data).flatMap (fun (k, d) => runData k d),
      OkAdmin (.plain i) := by
    intro i hi
    obtain ⟨⟨k, d⟩, hkd, hi'⟩ := List.mem_flatMap.1 hi
    exact ok_runData (hm.2 d (List.of_mem_zip hkd).2) i hi'
  exact (inv_append _ _).2 ⟨inv_expression he, inv_expression hd⟩

/-! ## Segment initialisation -/

/-- **Successful segment initialisation is a forced run**, every profile, before any suffix. -/
theorem segInit_ok {P : Profile} {s s' : Store Nat} {f f' : Frame} {m : Module}
    (rest : List Admin) (hm : OffsetsConst m)
    (h : initSegmentsT? evalConst? s f m = .ok (s', f')) :
    DetTo P ⟨s, f, segCode m ++ rest⟩ ⟨s', f', rest⟩ := by
  have hs : initSegments? evalConst? s f m = some (s', f') := initSegmentsT?_ok_iff.1 h
  have hr : Steps P noHost ⟨s, f, segCode m⟩ ⟨s', f', []⟩ :=
    initSegments?_steps evalConst?_evalSound hs
  have hg : GTo P ⟨s, f, segCode m⟩ ⟨s', f', []⟩ := run_gto hr (inv_segCode hm) ⟨[], rfl⟩
  exact (hg.lift [] rest).detTo

/-- **Trapping segment initialisation is a forced run up to the trap**, every profile, before
any suffix: the trapping `table.init`/`memory.init` becomes `TRAP`, at the store `s'`. -/
theorem segInit_trap {P : Profile} {s s' : Store Nat} {f : Frame} {m : Module}
    (rest : List Admin) (hm : OffsetsConst m)
    (h : initSegmentsT? evalConst? s f m = .trap s') :
    ∃ W R, DetTo P ⟨s, f, segCode m ++ rest⟩ ⟨s', f, vals W ++ .trap :: R⟩ := by
  have hr : Steps P noHost ⟨s, f, segCode m⟩ ⟨s', f, [.trap]⟩ :=
    initSegmentsT?_trap_steps evalConst?_evalSound h
  obtain ⟨W, R, hg⟩ := run_gto_trap hr (inv_segCode hm) rfl
  refine ⟨W, R ++ rest, ?_⟩
  have hl := (hg.lift [] rest).detTo
  simpa only [wrap, Det.vals_nil, List.nil_append, List.append_assoc, List.cons_append] using hl

end Silmaril.Proofs.Wasm.Game.SpecGlobals
