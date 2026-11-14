module

public import Silmaril.Games.Abstract.Link.Defs
public import Silmaril.Games.Abstract.Machine.Thms
public import Silmaril.Games.Abstract.Hiding.Thms

/-!
# Linking with hiding: proofs

The runs of a linked machine are exactly the legal joint plays whose
projections are runs of the components, with the internal moves hidden.
Hence the traces of the linked machine are the hidden images of the joint plays
both components accept, and state erasure commutes with linking for receptive
components.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.Link

open Silmaril.Games.Abstract Silmaril.Games.Abstract.Machine Silmaril.Games.Abstract.TraceModel

universe u

variable {G₁ G₂ G : Game.{u}} {Λ : LinkSpec G₁ G₂ G} {M₁ : Machine G₁} {M₂ : Machine G₂}

theorem run_of_moves {H : Game.{u}} {M : Machine H} {o : Option H.Move} {x x' : M.State}
    (h : M.Moves o x x') : M.Run x o.toList x' := by
  cases o with
  | none => cases h; exact .nil _
  | some m => exact .vis h (.nil _)

/-- One step of the linked machine, read on the components. -/
theorem step_inv {z z' : (link Λ M₁ M₂).State} {o : Option G.Move}
    (h : (link Λ M₁ M₂).step z o z') :
    ∃ u : List Λ.L.Move, z'.2.2 = z.2.2 ++ u ∧ (u ≠ [] → z.2.2 ++ u ∈ Λ.L.Legal) ∧
      o.toList = u.filterMap Λ.ext.map ∧ M₁.Run z.1 (u.filterMap Λ.π₁.map) z'.1 ∧
      M₂.Run z.2.1 (u.filterMap Λ.π₂.map) z'.2.1 := by
  cases h with
  | tau₁ h => exact ⟨[], by simp, by simp, rfl, .tau h (.nil _), .nil _⟩
  | tau₂ h => exact ⟨[], by simp, by simp, rfl, .nil _, .tau h (.nil _)⟩
  | move l hl h₁ h₂ =>
    refine ⟨[l], rfl, fun _ => hl, ?_, ?_, ?_⟩
    · cases hm : Λ.ext.map l <;> simp [hm]
    · have := run_of_moves h₁
      cases hm : Λ.π₁.map l <;> simp_all
    · have := run_of_moves h₂
      cases hm : Λ.π₂.map l <;> simp_all

theorem run_inv {z z' : (link Λ M₁ M₂).State} {t : List G.Move}
    (h : (link Λ M₁ M₂).Run z t z') :
    ∃ u : List Λ.L.Move, z'.2.2 = z.2.2 ++ u ∧ (z.2.2 ∈ Λ.L.Legal → z.2.2 ++ u ∈ Λ.L.Legal) ∧
      t = u.filterMap Λ.ext.map ∧ M₁.Run z.1 (u.filterMap Λ.π₁.map) z'.1 ∧
      M₂.Run z.2.1 (u.filterMap Λ.π₂.map) z'.2.1 := by
  induction h with
  | nil => exact ⟨[], by simp, by simp, rfl, .nil _, .nil _⟩
  | tau hs _ ih =>
    obtain ⟨u₁, e₁, l₁, t₁, r₁, s₁⟩ := step_inv hs
    obtain ⟨u₂, e₂, l₂, t₂, r₂, s₂⟩ := ih
    refine ⟨u₁ ++ u₂, by rw [e₂, e₁, List.append_assoc], fun hz => ?_, ?_, ?_, ?_⟩
    · by_cases hne : u₁ = []
      · subst hne
        simp only [List.append_nil, List.nil_append] at e₁ ⊢
        rw [e₁] at l₂; exact l₂ hz
      · have := l₂ (e₁ ▸ l₁ hne); rw [e₁, List.append_assoc] at this; exact this
    · simp only [Option.toList_none] at t₁
      rw [t₂, List.filterMap_append, ← t₁, List.nil_append]
    · rw [List.filterMap_append]; exact r₁.append r₂
    · rw [List.filterMap_append]; exact s₁.append s₂
  | vis hs _ ih =>
    obtain ⟨u₁, e₁, l₁, t₁, r₁, s₁⟩ := step_inv hs
    obtain ⟨u₂, e₂, l₂, t₂, r₂, s₂⟩ := ih
    refine ⟨u₁ ++ u₂, by rw [e₂, e₁, List.append_assoc], fun hz => ?_, ?_, ?_, ?_⟩
    · by_cases hne : u₁ = []
      · subst hne; simp at t₁
      · have := l₂ (e₁ ▸ l₁ hne); rw [e₁, List.append_assoc] at this; exact this
    · simp only [Option.toList_some] at t₁
      rw [t₂, List.filterMap_append, ← t₁, List.singleton_append]
    · rw [List.filterMap_append]; exact r₁.append r₂
    · rw [List.filterMap_append]; exact s₁.append s₂

theorem lift_tau₁ {x x' : M₁.State} (y : M₂.State) (hh : List Λ.L.Move) (h : M₁.Run x [] x') :
    (link Λ M₁ M₂).Run (x, y, hh) [] (x', y, hh) := by
  generalize hn : ([] : List G₁.Move) = n at h
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => exact .tau (LinkStep.tau₁ hs) (ih hn)
  | vis _ _ _ => cases hn

theorem lift_tau₂ (x : M₁.State) {y y' : M₂.State} (hh : List Λ.L.Move) (h : M₂.Run y [] y') :
    (link Λ M₁ M₂).Run (x, y, hh) [] (x, y', hh) := by
  generalize hn : ([] : List G₂.Move) = n at h
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => exact .tau (LinkStep.tau₂ hs) (ih hn)
  | vis _ _ _ => cases hn

/-- Split a component run at the image of one joint move. -/
theorem split {H : Game.{u}} {M : Machine H} {o : Option H.Move} {x x' : M.State}
    {s : List H.Move} (h : M.Run x (o.toList ++ s) x') :
    ∃ x₁ x₂, M.Run x [] x₁ ∧ M.Moves o x₁ x₂ ∧ M.Run x₂ s x' := by
  cases o with
  | none => exact ⟨x, x, .nil _, rfl, h⟩
  | some m =>
    obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := Run.cons_inv h
    exact ⟨x₁, x₂, h₁, h₂, h₃⟩

theorem filterMap_cons_toList {α β : Type*} (f : α → Option β) (a : α) (l : List α) :
    (a :: l).filterMap f = (f a).toList ++ l.filterMap f := by
  cases h : f a <;> simp [h]

theorem run_of {u : List Λ.L.Move} {x x' : M₁.State} {y y' : M₂.State} {hh : List Λ.L.Move}
    (hl : hh ++ u ∈ Λ.L.Legal) (r₁ : M₁.Run x (u.filterMap Λ.π₁.map) x')
    (r₂ : M₂.Run y (u.filterMap Λ.π₂.map) y') :
    (link Λ M₁ M₂).Run (x, y, hh) (u.filterMap Λ.ext.map) (x', y', hh ++ u) := by
  induction u generalizing x y hh with
  | nil =>
    simpa using (lift_tau₁ y hh r₁).append (lift_tau₂ x' hh r₂)
  | cons l u ih =>
    rw [filterMap_cons_toList] at r₁ r₂ ⊢
    obtain ⟨x₁, x₂, a₁, b₁, c₁⟩ := split r₁
    obtain ⟨y₁, y₂, a₂, b₂, c₂⟩ := split r₂
    have hl' : hh ++ [l] ∈ Λ.L.Legal := Λ.L.legal_of_prefix hl (by simp)
    have step : (link Λ M₁ M₂).step (x₁, y₁, hh) (Λ.ext.map l) (x₂, y₂, hh ++ [l]) :=
      LinkStep.move l hl' b₁ b₂
    have rest := ih (hh := hh ++ [l]) (by simpa using hl) c₁ c₂
    have := ((lift_tau₁ y hh a₁).append (lift_tau₂ x₁ hh a₂)).append (Run.step_opt step rest)
    simpa using this

theorem traces_link :
    (link Λ M₁ M₂).traces = (List.filterMap Λ.ext.map) ''
      {u | u ∈ Λ.L.Legal ∧ u.filterMap Λ.π₁.map ∈ M₁.traces ∧
        u.filterMap Λ.π₂.map ∈ M₂.traces} := by
  ext t
  constructor
  · rintro ⟨z', h⟩
    obtain ⟨u, -, hl, rfl, r₁, r₂⟩ := run_inv h
    exact ⟨u, ⟨by simpa [Machine.link] using hl Λ.L.nil_legal, ⟨_, r₁⟩, ⟨_, r₂⟩⟩, rfl⟩
  · rintro ⟨u, ⟨hl, ⟨x', r₁⟩, ⟨y', r₂⟩⟩, rfl⟩
    exact ⟨_, run_of (hh := []) (by simpa using hl) r₁ r₂⟩

theorem mem_inf_pull {T₁ : TraceModel G₁} {T₂ : TraceModel G₂} {u : List Λ.L.Move} :
    u ∈ pull Λ.π₁ T₁ ⊓ pull Λ.π₂ T₂ ↔
      u ∈ Λ.L.Legal ∧ u.filterMap Λ.π₁.map ∈ T₁ ∧ u.filterMap Λ.π₂.map ∈ T₂ := by
  rw [mem_inf, mem_pull, mem_pull]
  exact ⟨fun ⟨⟨h, a⟩, ⟨_, b⟩⟩ => ⟨h, a, b⟩, fun ⟨h, a, b⟩ => ⟨⟨h, a⟩, ⟨h, b⟩⟩⟩

theorem denote_link_le :
    (link Λ M₁ M₂).denote ≤ TraceModel.link Λ M₁.denote M₂.denote := by
  refine generate_le_iff.2 ?_
  rw [traces_link]
  rintro _ ⟨u, ⟨hl, h₁, h₂⟩, rfl⟩ -
  exact filterMap_mem_hide (mem_inf_pull.2 ⟨hl, mem_denote_of_mem_traces h₁ (Λ.π₁.legal hl),
    mem_denote_of_mem_traces h₂ (Λ.π₂.legal hl)⟩)

theorem denote_link (h₁ : G₁.Closed M₁.traces) (h₂ : G₂.Closed M₂.traces) :
    (link Λ M₁ M₂).denote = TraceModel.link Λ M₁.denote M₂.denote := by
  unfold Machine.denote TraceModel.link hide
  congr 1
  rw [traces_link]
  ext t
  simp only [Set.mem_image]
  refine exists_congr fun u => and_congr_left fun _ => ?_
  change _ ↔ u ∈ pull Λ.π₁ (generate M₁.traces) ⊓ pull Λ.π₂ (generate M₂.traces)
  rw [mem_inf_pull]
  have e₁ := coe_denote h₁
  have e₂ := coe_denote h₂
  unfold Machine.denote at e₁ e₂
  rw [← SetLike.mem_coe, ← SetLike.mem_coe (x := u.filterMap Λ.π₂.map), e₁, e₂]
  exact Iff.rfl

end Silmaril.Proofs.Games.Abstract.Link
