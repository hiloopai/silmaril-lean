module

public import Silmaril.Games.Abstract.TrapCut.Defs

/-!
# Trap ≈ divergence with trap moves: proofs

`firstCut` finds the first trap move; with no trap moves the cut is the
collapse; tagged equivalence implies cut equivalence; and an example of a
trapping answer against a silent loop, cut-equivalent but not tag-equivalent.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.TrapCut

open Silmaril.Games.Abstract Silmaril.Games.Abstract.OMachine

universe u

theorem firstCut_eq_none_iff {M : Type u} {T : M → Prop} {s : List M} :
    firstCut T s = none ↔ ∀ m ∈ s, ¬ T m := by
  induction s with
  | nil => simp [firstCut]
  | cons m s ih =>
    by_cases h : T m
    · simp [firstCut, h]
    · simp [firstCut, h, ih]

theorem firstCut_eq_some {M : Type u} {T : M → Prop} {s p : List M}
    (h : firstCut T s = some p) : ∃ m rest, s = p ++ m :: rest ∧ T m ∧ ∀ x ∈ p, ¬ T x := by
  induction s generalizing p with
  | nil => simp [firstCut] at h
  | cons m s ih =>
    by_cases hm : T m
    · simp only [firstCut, hm, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨m, s, rfl, hm, by simp⟩
    · simp only [firstCut, hm, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      obtain ⟨m', rest, rfl, hm', hp⟩ := ih hp'
      exact ⟨m', rest, rfl, hm', by simp_all⟩

theorem cut_false {G : Game.{u}} {R : Type u} :
    Obs.cut (G := G) (R := R) (fun _ => False) = Obs.collapse := by
  funext o
  rcases o with ⟨s, t⟩ | ω
  · have : firstCut (fun _ : G.Move => False) s = none := firstCut_eq_none_iff.2 (by simp)
    simp [Obs.cut, this, Obs.collapse]
  · simp [Obs.cut, Obs.collapse]

/-! ## A trapping answer against a silent loop -/

/-- An export question (environment) and a trapping answer (component). -/
inductive Mv | ask | trapAns

/-- The free game on `Mv`. -/
abbrev Gt : Game.{0} := Game.free Mv fun m => m = Mv.ask

/-- The trap moves. -/
def T : Gt.Move → Prop := fun m => m = Mv.trapAns

inductive St | s0 | s1 | s2

inductive TS : St → Option Gt.Move → St → Prop
  | ask : TS .s0 (some Mv.ask) .s1
  | trap : TS .s1 (some Mv.trapAns) .s2

inductive LS : St → Option Gt.Move → St → Prop
  | ask : LS .s0 (some Mv.ask) .s1
  | tau : LS .s1 none .s1

/-- Answer the call with a trap. -/
def trapM : OMachine Gt PUnit := ⟨⟨St, .s0, TS⟩, fun _ _ => False, fun _ => False⟩
/-- Loop silently instead of answering. -/
def loopM : OMachine Gt PUnit := ⟨⟨St, .s0, LS⟩, fun _ _ => False, fun _ => False⟩

theorem trapM_run {s : List Gt.Move} {y : St} (h : trapM.Run .s0 s y) :
    (s = [] ∧ y = .s0) ∨ (s = [Mv.ask] ∧ y = .s1) ∨ (s = [Mv.ask, Mv.trapAns] ∧ y = .s2) := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
  · exact .inl ⟨rfl, rfl⟩
  · cases h
  · cases h
    rcases h₁ with _ | ⟨h, _⟩ | ⟨h, h₂⟩
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · cases h
    · cases h
      rcases h₂ with _ | ⟨h, _⟩ | ⟨h, _⟩
      · exact .inr (.inr ⟨rfl, rfl⟩)
      · cases h
      · cases h

theorem trapM_s2 {s : List Gt.Move} {y : St} (h : trapM.Run .s2 s y) : s = [] := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, _⟩
  · rfl
  · cases h
  · cases h

theorem trapM_s1 {s : List Gt.Move} {y : St} (h : trapM.Run .s1 s y) :
    (s = [] ∧ y = .s1) ∨ (s = [Mv.trapAns] ∧ y = .s2) := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
  · exact .inl ⟨rfl, rfl⟩
  · cases h
  · cases h
    rcases h₁ with _ | ⟨h, _⟩ | ⟨h, _⟩
    · exact .inr ⟨rfl, rfl⟩
    · cases h
    · cases h

theorem loopM_s1 {x : loopM.State} {s : List Gt.Move} {y : St} (h : loopM.Run x s y)
    (hx : x = .s1) : s = [] ∧ y = .s1 := by
  induction h with
  | nil => exact ⟨rfl, hx⟩
  | tau h _ ih => subst hx; cases h; exact ih rfl
  | vis h _ _ => subst hx; cases h

theorem loopM_run {s : List Gt.Move} {y : St} (h : loopM.Run .s0 s y) :
    (s = [] ∧ y = .s0) ∨ (s = [Mv.ask] ∧ y = .s1) := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
  · exact .inl ⟨rfl, rfl⟩
  · cases h
  · cases h
    obtain ⟨rfl, rfl⟩ := loopM_s1 h₁ rfl
    exact .inr ⟨rfl, rfl⟩

/-- The common cut observations. -/
def cutSet : Set (CObs Gt PUnit) :=
  {c | c = .fin [] .run ∨ c = .fin [] .wait ∨ c = .fin [Mv.ask] .run ∨ c = .fin [Mv.ask] .abort}

theorem not_div_of_no_tau {M : OMachine Gt PUnit} {x : M.State} (h : ∀ y, ¬ M.step x none y) :
    ¬ M.DivergesFrom x := fun ⟨_, h0, hf⟩ => h _ (h0 ▸ hf 0)

theorem trapM_obs {o : Obs Gt PUnit} (ho : o ∈ trapM.obs) :
    o = .fin [] .run ∨ o = .fin [] .wait ∨ o = .fin [Mv.ask] .run ∨
      o = .fin [Mv.ask, Mv.trapAns] .run ∨ o = .fin [Mv.ask, Mv.trapAns] .stuck := by
  cases ho with
  | fin y hr hs =>
    rename_i s t
    rcases trapM_run hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases t with
      | run => exact .inl rfl
      | wait => exact .inr (.inl rfl)
      | ret r => exact hs.elim
      | trap => exact hs.elim
      | div => exact (not_div_of_no_tau (fun _ h => by cases h) hs).elim
      | stuck => exact (hs.2 _ _ TS.ask).elim
    · cases t with
      | run => exact .inr (.inr (.inl rfl))
      | wait => exact absurd (hs.2.2.1 _ _ TS.trap) (fun h => by cases h)
      | ret r => exact hs.elim
      | trap => exact hs.elim
      | div => exact (not_div_of_no_tau (fun _ h => by cases h) hs).elim
      | stuck => exact (hs.2 _ _ TS.trap).elim
    · cases t with
      | run => exact .inr (.inr (.inr (.inl rfl)))
      | stuck => exact .inr (.inr (.inr (.inr rfl)))
      | wait => obtain ⟨_, _, h⟩ := hs.2.2.2; cases h
      | ret r => exact hs.elim
      | trap => exact hs.elim
      | div => exact (not_div_of_no_tau (fun _ h => by cases h) hs).elim
  | inf x h0 hx =>
    have h₁ := hx 0
    rw [h0] at h₁
    rcases trapM_run h₁ with ⟨h, -⟩ | ⟨-, h'⟩ | ⟨h, -⟩
    · exact absurd (congrArg List.length h) (by simp)
    · have h₂ := hx 1
      rw [h'] at h₂
      rcases trapM_s1 h₂ with ⟨h, -⟩ | ⟨-, h''⟩
      · exact absurd (congrArg List.length h) (by simp)
      · have h₃ := hx 2
        rw [h''] at h₃
        exact absurd (congrArg List.length (trapM_s2 h₃)) (by simp)
    · exact absurd (congrArg List.length h) (by simp)

theorem loopM_obs {o : Obs Gt PUnit} (ho : o ∈ loopM.obs) :
    o = .fin [] .run ∨ o = .fin [] .wait ∨ o = .fin [Mv.ask] .run ∨ o = .fin [Mv.ask] .div := by
  cases ho with
  | fin y hr hs =>
    rename_i s t
    rcases loopM_run hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases t with
      | run => exact .inl rfl
      | wait => exact .inr (.inl rfl)
      | ret r => exact hs.elim
      | trap => exact hs.elim
      | div => exact (not_div_of_no_tau (fun _ h => by cases h) hs).elim
      | stuck => exact (hs.2 _ _ LS.ask).elim
    · cases t with
      | run => exact .inr (.inr (.inl rfl))
      | div => exact .inr (.inr (.inr rfl))
      | wait => exact (hs.2.1 _ LS.tau).elim
      | ret r => exact hs.elim
      | trap => exact hs.elim
      | stuck => exact (hs.2 _ _ LS.tau).elim
  | inf x h0 hx =>
    have h₁ := hx 0
    rw [h0] at h₁
    rcases loopM_run h₁ with ⟨h, -⟩ | ⟨-, h'⟩
    · exact absurd (congrArg List.length h) (by simp)
    · have h₂ := hx 1
      rw [h'] at h₂
      exact absurd (congrArg List.length (loopM_s1 h₂ rfl).1) (by simp)

theorem trapM_mem : Obs.fin [] .wait ∈ trapM.obs ∧ Obs.fin [Mv.ask, Mv.trapAns] .run ∈ trapM.obs := by
  refine ⟨.fin (y := St.s0) (.nil _) ⟨fun h => by rcases h with ⟨_, h⟩ | h <;> exact h,
    fun _ h => (by cases h), fun m _ h => (by cases h; rfl), _, _, TS.ask⟩, ?_⟩
  exact .fin (t := Tag.run) (y := St.s2) (.vis TS.ask (.vis TS.trap (.nil _))) trivial

theorem loopM_mem : Obs.fin [] .wait ∈ loopM.obs ∧ Obs.fin [Mv.ask] .div ∈ loopM.obs :=
  ⟨.fin (y := St.s0) (.nil _) ⟨fun h => by rcases h with ⟨_, h⟩ | h <;> exact h,
    fun _ h => (by cases h), fun m _ h => (by cases h; rfl), _, _, LS.ask⟩,
   .fin (y := St.s1) (.vis LS.ask (.nil _)) ⟨fun _ => .s1, rfl, fun _ => LS.tau⟩⟩

theorem cut_ask_trap (t : Tag PUnit) :
    Obs.cut T (.fin [Mv.ask, Mv.trapAns] t : Obs Gt PUnit) = .fin [Mv.ask] .abort := by
  have h : firstCut T ([Mv.ask, Mv.trapAns] : List Gt.Move) = some [Mv.ask] := by
    have h₁ : ¬ T Mv.ask := by simp [T]
    have h₂ : T Mv.trapAns := rfl
    simp only [firstCut, h₁, h₂, ↓reduceIte]
    rfl
  simp only [Obs.cut, h]

theorem cut_noTrap {s : List Gt.Move} (hs : ∀ m ∈ s, m ≠ Mv.trapAns) (t : Tag PUnit) :
    Obs.cut T (.fin s t : Obs Gt PUnit) = .fin s t.collapse := by
  have h : firstCut T s = none := firstCut_eq_none_iff.2 (fun m hm => hs m hm)
  simp only [Obs.cut, h]

theorem trapM_cut : trapM.cobsCut T = cutSet := by
  ext c
  constructor
  · rintro ⟨o, ho, rfl⟩
    rcases trapM_obs ho with rfl | rfl | rfl | rfl | rfl
    · exact .inl (by rw [cut_noTrap (by simp)]; rfl)
    · exact .inr (.inl (by rw [cut_noTrap (by simp)]; rfl))
    · exact .inr (.inr (.inl (by rw [cut_noTrap (by simp)]; rfl)))
    · exact .inr (.inr (.inr (cut_ask_trap _)))
    · exact .inr (.inr (.inr (cut_ask_trap _)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, .fin (t := Tag.run) (y := St.s0) (.nil _) trivial, by rw [cut_noTrap (by simp)]; rfl⟩
    · exact ⟨_, trapM_mem.1, by rw [cut_noTrap (by simp)]; rfl⟩
    · exact ⟨_, .fin (t := Tag.run) (y := St.s1) (.vis TS.ask (.nil _)) trivial,
        by rw [cut_noTrap (by simp)]; rfl⟩
    · exact ⟨_, trapM_mem.2, cut_ask_trap _⟩

theorem loopM_cut : loopM.cobsCut T = cutSet := by
  ext c
  constructor
  · rintro ⟨o, ho, rfl⟩
    rcases loopM_obs ho with rfl | rfl | rfl | rfl
    · exact .inl (by rw [cut_noTrap (by simp)]; rfl)
    · exact .inr (.inl (by rw [cut_noTrap (by simp)]; rfl))
    · exact .inr (.inr (.inl (by rw [cut_noTrap (by simp)]; rfl)))
    · exact .inr (.inr (.inr (by rw [cut_noTrap (by simp)]; rfl)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, .fin (t := Tag.run) (y := St.s0) (.nil _) trivial, by rw [cut_noTrap (by simp)]; rfl⟩
    · exact ⟨_, loopM_mem.1, by rw [cut_noTrap (by simp)]; rfl⟩
    · exact ⟨_, .fin (t := Tag.run) (y := St.s1) (.vis LS.ask (.nil _)) trivial,
        by rw [cut_noTrap (by simp)]; rfl⟩
    · exact ⟨_, loopM_mem.2, by rw [cut_noTrap (by simp)]; rfl⟩

theorem trap_loop_cut : trapM.CutEquiv T loopM := trapM_cut.trans loopM_cut.symm

theorem trap_loop_not_tag : ¬ trapM.TagEquiv loopM := by
  intro h
  have : Obs.fin [Mv.ask, Mv.trapAns] .run ∈ loopM.obs := h ▸ trapM_mem.2
  rcases loopM_obs this with h | h | h | h <;> cases h

end Silmaril.Proofs.Games.Abstract.TrapCut
