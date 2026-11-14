module

public import Silmaril.Servers.Core.Defs

/-!
# Proofs: sequential use

A trace that answers each request before the next arrives (`Sen.Sequential`) is linearizable
with respect to `S` exactly when its history is in `S`: the linearization points are forced.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Core

open Silmaril.Servers

variable {A : Sig}

/-- The annotated trace of a sequential use: each handler run between its request and its
response. -/
def seqAnn (h : List (ReqId × A.Req × A.Resp)) : List (LEvent A) :=
  h.flatMap fun p => [.ev (.recv p.1 p.2.1), .lin p.1 p.2.1 p.2.2, .ev (.send p.1 p.2.2)]

theorem erase_seqAnn (h : List (ReqId × A.Req × A.Resp)) :
    LEvent.erase (seqAnn h) = Trace.seq h := by
  induction h with
  | nil => rfl
  | cons p h ih =>
    simp only [seqAnn, Trace.seq, List.flatMap_cons] at ih ⊢
    simp only [LEvent.erase, List.cons_append, List.nil_append, List.filterMap_cons] at ih ⊢
    rw [ih]

theorem lins_seqAnn (h : List (ReqId × A.Req × A.Resp)) :
    LEvent.lins (seqAnn h) = h.map (·.2) := by
  induction h with
  | nil => rfl
  | cons p h ih =>
    simp only [seqAnn, List.flatMap_cons] at ih ⊢
    simp only [LEvent.lins, List.cons_append, List.nil_append, List.filterMap_cons,
      List.map_cons] at ih ⊢
    rw [ih]

theorem steps_seqAnn : ∀ (h : List (ReqId × A.Req × A.Resp)) (m : LMon A),
    (h.map (·.1)).Nodup → (∀ p ∈ h, m.req p.1 = none) → ∃ m', Steps LMon.Step m (seqAnn h) m'
  | [], m, _, _ => ⟨m, .nil _⟩
  | (i, r, s) :: h, m, hn, hf => by
    simp only [List.map_cons, List.nodup_cons] at hn
    have hi : m.req i = none := hf (i, r, s) (by simp)
    have s1 := LMon.Step.recv (m := m) (r := r) hi
    have s2 := LMon.Step.lin (s := s)
      (m := ⟨Function.update m.req i (some r), Function.update m.pending i (some r), m.ready⟩)
      (i := i) (r := r) (by simp)
    have s3 := LMon.Step.send
      (m := ⟨Function.update m.req i (some r),
        Function.update (Function.update m.pending i (some r)) i none,
        Function.update m.ready i (some s)⟩) (i := i) (s := s) (by simp)
    obtain ⟨m', hm'⟩ := steps_seqAnn h ⟨Function.update m.req i (some r),
        Function.update (Function.update m.pending i (some r)) i none,
        Function.update (Function.update m.ready i (some s)) i none⟩ hn.2 (fun p hp => by
      have hne : p.1 ≠ i := fun he => hn.1 (he ▸ List.mem_map_of_mem hp)
      simp [hne, hf p (List.mem_cons_of_mem _ hp)])
    exact ⟨m', .cons s1 (.cons s2 (.cons s3 hm'))⟩

theorem lin_of_seq {S : SeqSpec A} (h : List (ReqId × A.Req × A.Resp)) (hn : (h.map (·.1)).Nodup)
    (hS : S (h.map (·.2))) : Sen.lin S (Trace.seq h) := by
  obtain ⟨m', hm'⟩ := steps_seqAnn h (LMon.init A) hn (fun _ _ => rfl)
  exact ⟨seqAnn h, ⟨m', hm'⟩, erase_seqAnn h, by rw [lins_seqAnn]; exact hS⟩

/-- Nothing is pending and nothing is ready. -/
def Idle (m : LMon A) : Prop := (∀ j, m.pending j = none) ∧ (∀ j, m.ready j = none)

theorem lins_of_idle_nil {m m' : LMon A} {t' : List (LEvent A)} (hs : Steps LMon.Step m t' m')
    (hI : Idle m) (he : LEvent.erase t' = []) : LEvent.lins t' = [] := by
  cases hs with
  | nil => rfl
  | @cons _ m₂ _ e es hst _ =>
    cases hst with
    | recv => exact absurd he (by simp [LEvent.erase])
    | send => exact absurd he (by simp [LEvent.erase])
    | lin hp => rw [hI.1] at hp; cases hp

theorem lins_of_idle_seq : ∀ (h : List (ReqId × A.Req × A.Resp)) {m m' : LMon A}
    {t' : List (LEvent A)}, Steps LMon.Step m t' m' → Idle m → LEvent.erase t' = Trace.seq h →
    LEvent.lins t' = h.map (·.2)
  | [], _, _, _, hs, hI, he => lins_of_idle_nil hs hI he
  | (i, r, s) :: h, m, m', t', hs, hI, he => by
    -- the first event: the request
    cases hs with
    | nil => exact absurd he (by simp [LEvent.erase, Trace.seq])
    | @cons _ m₁ _ e es hst hs =>
      cases hst with
      | lin hp => rw [hI.1] at hp; cases hp
      | @send j s' hr => rw [hI.2] at hr; cases hr
      | @recv j r' _ =>
        have he₀ : Event.recv j r' :: LEvent.erase es =
            Event.recv i r :: Event.send i s :: Trace.seq h := he
        clear he
        simp only [List.cons.injEq, Event.recv.injEq] at he₀
        obtain ⟨⟨hj, hr'⟩, he₁⟩ := he₀
        subst j; subst r'
        -- the second event: the linearization point
        cases hs with
        | nil => exact absurd he₁ (by simp [LEvent.erase])
        | @cons _ m₂ _ e₂ es₂ hst₂ hs₂ =>
          cases hst₂ with
          | recv => exact absurd he₁ (by simp [LEvent.erase])
          | @send k s₂ hr => simp [hI.2 k] at hr
          | @lin k r₂ s₂ hp =>
            have hk : k = i := by
              by_contra hk; simp [hk, hI.1 k] at hp
            subst k
            simp at hp; subst r₂
            -- the third event: the response
            cases hs₂ with
            | nil => exact absurd he₁ (by simp [LEvent.erase])
            | @cons _ m₃ _ e₃ es₃ hst₃ hs₃ =>
              cases hst₃ with
              | @lin l _ _ hp' =>
                by_cases hl : l = i
                · subst l; simp at hp'
                · simp [hl, hI.1 l] at hp'
              | recv => exact absurd he₁ (by simp [LEvent.erase])
              | @send l s₃ hr =>
                have he₂ : Event.send l s₃ :: LEvent.erase es₃ =
                    Event.send i s :: Trace.seq h := he₁
                clear he₁
                simp only [List.cons.injEq, Event.send.injEq] at he₂
                obtain ⟨⟨hl, hs₃'⟩, he₃⟩ := he₂
                subst l; subst s₃
                simp at hr; subst s₂
                have hI₃ : Idle (⟨Function.update m.req i (some r),
                    Function.update (Function.update m.pending i (some r)) i none,
                    Function.update (Function.update m.ready i (some s)) i none⟩ : LMon A) := by
                  refine ⟨fun j => ?_, fun j => ?_⟩
                  · by_cases hj : j = i
                    · subst j; simp
                    · simp [hj, hI.1 j]
                  · by_cases hj : j = i
                    · subst j; simp
                    · simp [hj, hI.2 j]
                have ih := lins_of_idle_seq h hs₃ hI₃ he₃
                show (r, s) :: LEvent.lins es₃ = _
                rw [ih]; rfl

theorem seq_of_lin {S : SeqSpec A} (h : List (ReqId × A.Req × A.Resp))
    (hl : Sen.lin S (Trace.seq h)) : S (h.map (·.2)) := by
  obtain ⟨t', ⟨m, hm⟩, he, hS⟩ := hl
  rw [lins_of_idle_seq h hm ⟨fun _ => rfl, fun _ => rfl⟩ he] at hS
  exact hS

end Silmaril.Proofs.Servers.Core
