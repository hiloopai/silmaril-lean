module

public import Silmaril.Servers.Sessions.Defs
import Mathlib.Data.List.Dedup

/-!
# Proofs: connection events

* `wf_erase`: the core trace of a well-formed connection trace is well formed (the monitor's
  core part runs along);
* `exists_of_wf`: a well-formed core trace is the core trace of the connection trace that
  first opens every connection it uses;
* `graceful_answered`: in a well-formed graceful trace whose connections are all closed, every
  request is answered (the close of its connection comes after it, and the close waits for
  the answer).
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Sessions

open Silmaril.Servers

variable {A : Sig}

theorem steps_concat {S E : Type} {step : S → E → S → Prop} {x y z : S} {l l' : List E}
    (h : Steps step x l y) (h' : Steps step y l' z) : Steps step x (l ++ l') z := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

theorem steps_split {S E : Type} {step : S → E → S → Prop} :
    ∀ {x y : S} {l₁ l₂ : List E}, Steps step x (l₁ ++ l₂) y →
      ∃ z, Steps step x l₁ z ∧ Steps step z l₂ y
  | _, _, [], _, hs => ⟨_, .nil _, hs⟩
  | _, _, _ :: l₁, _, hs => by
    cases hs with
    | cons hst hs =>
      obtain ⟨z, h₁, h₂⟩ := steps_split hs
      exact ⟨z, .cons hst h₁, h₂⟩

theorem erase_append (t u : CTrace A) : CTrace.erase (t ++ u) = t.erase ++ u.erase := by
  simp [CTrace.erase, List.filterMap_append]

theorem erase_connects (L : List Nat) : CTrace.erase (L.map (CEvent.connect (A := A))) = [] := by
  simp [CTrace.erase]

theorem erase_evs (t : Trace A) : CTrace.erase (t.map CEvent.ev) = t := by
  simp [CTrace.erase]

theorem mem_erase {t : CTrace A} {e : Event A} : e ∈ t.erase ↔ CEvent.ev e ∈ t := by
  simp only [CTrace.erase, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, he⟩
    cases a with
    | ev e' => cases he; exact ha
    | connect => cases he
    | close => cases he
  · exact fun h => ⟨_, h, rfl⟩

/-! ## Forgetting connection events -/

theorem wsteps_of_steps {m m' : CMon A} {t : CTrace A} (h : Steps CMon.Step m t m') :
    Steps WMon.Step m.w t.erase m'.w := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    cases hs with
    | connect _ => exact ih
    | close _ => exact ih
    | ev _ hw => exact .cons hw ih

theorem wf_erase {t : CTrace A} (h : CSen.WF t) : Sen.WF t.erase :=
  let ⟨_, hs⟩ := h; ⟨_, wsteps_of_steps hs⟩

theorem opens : ∀ (L : List Nat) (f : Nat → Phase) (w : WMon A), L.Nodup →
    (∀ c ∈ L, f c = .fresh) →
    ∃ g, Steps CMon.Step ⟨f, w⟩ (L.map CEvent.connect) ⟨g, w⟩ ∧ (∀ c ∈ L, g c = .live) ∧
      (∀ c, c ∉ L → g c = f c)
  | [], f, _, _, _ => ⟨f, .nil _, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | c :: L, f, w, hn, hf => by
    obtain ⟨hc, hn'⟩ := List.nodup_cons.1 hn
    obtain ⟨g, hs, hl, ho⟩ := opens L (Function.update f c .live) w hn' fun c' hc' => by
      have : c' ≠ c := fun e => hc (e ▸ hc')
      rw [Function.update_of_ne this]; exact hf c' (List.mem_cons_of_mem _ hc')
    refine ⟨g, .cons (CMon.Step.connect (hf c List.mem_cons_self)) hs, fun c' hc' => ?_,
      fun c' hc' => ?_⟩
    · rcases List.mem_cons.1 hc' with rfl | h
      · rw [ho c' hc]; simp
      · exact hl c' h
    · have h₁ : c' ≠ c := fun e => hc' (e ▸ List.mem_cons_self)
      rw [ho c' fun h => hc' (List.mem_cons_of_mem _ h), Function.update_of_ne h₁]

theorem evs {g : Nat → Phase} {w w' : WMon A} {t : Trace A} (h : Steps WMon.Step w t w')
    (hg : ∀ e ∈ t, g e.id.conn = .live) : Steps CMon.Step ⟨g, w⟩ (t.map CEvent.ev) ⟨g, w'⟩ := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    exact .cons (CMon.Step.ev (hg _ List.mem_cons_self) hs)
      (ih fun e he => hg e (List.mem_cons_of_mem _ he))

theorem exists_of_wf {t : Trace A} (hw : Sen.WF t) : ∃ ct : CTrace A, CSen.WF ct ∧ ct.erase = t := by
  obtain ⟨w', hw'⟩ := hw
  obtain ⟨g, h₁, h₂, -⟩ := opens (t.map (·.id.conn)).dedup (fun _ => .fresh) (WMon.init A)
    (List.nodup_dedup _) fun _ _ => rfl
  refine ⟨(t.map (·.id.conn)).dedup.map CEvent.connect ++ t.map CEvent.ev,
    ⟨_, steps_concat h₁ (evs hw' fun e he => h₂ _ (List.mem_dedup.2 (List.mem_map_of_mem he)))⟩,
    ?_⟩
  rw [erase_append, erase_connects, erase_evs, List.nil_append]

/-! ## Graceful close -/

theorem fresh_steps {m m' : CMon A} {t : CTrace A} (h : Steps CMon.Step m t m') {c : Nat}
    (hc : CEvent.connect c ∉ t) (hf : m.phase c = .fresh) : m'.phase c = .fresh := by
  induction h with
  | nil => exact hf
  | cons hs _ ih =>
    refine ih (fun h => hc (List.mem_cons_of_mem _ h)) ?_
    cases hs with
    | @connect c' _ =>
      have : c ≠ c' := fun e => hc (e ▸ List.mem_cons_self)
      simp [Function.update_of_ne this, hf]
    | @close c' h' =>
      have : c ≠ c' := by rintro rfl; rw [hf] at h'; cases h'
      simp [Function.update_of_ne this, hf]
    | ev _ _ => exact hf

theorem closed_persist {m m' : CMon A} {t : CTrace A} (h : Steps CMon.Step m t m') {c : Nat}
    (hc : m.phase c = .closed) : m'.phase c = .closed := by
  induction h with
  | nil => exact hc
  | cons hs _ ih =>
    refine ih ?_
    cases hs with
    | @connect c' h' =>
      have : c ≠ c' := by rintro rfl; rw [hc] at h'; cases h'
      simp [Function.update_of_ne this, hc]
    | @close c' h' =>
      have : c ≠ c' := by rintro rfl; rw [hc] at h'; cases h'
      simp [Function.update_of_ne this, hc]
    | ev _ _ => exact hc

theorem closed_of_close {m m' : CMon A} {t : CTrace A} (h : Steps CMon.Step m t m') {c : Nat}
    (hc : CEvent.close c ∈ t) : m'.phase c = .closed := by
  induction h with
  | nil => exact absurd hc List.not_mem_nil
  | @cons m₁ m₂ m₃ e es hs hr ih =>
    rcases List.mem_cons.1 hc with rfl | h'
    · cases hs with
      | close _ => exact closed_persist hr (by simp)
    · exact ih h'

theorem graceful_answered {t : CTrace A} (hw : CSen.WF t) (hg : CSen.graceful t)
    (hc : CSen.allClosed t) {i : ReqId} {r : A.Req} (hr : Event.recv i r ∈ t.erase) :
    ∃ s, Event.send i s ∈ t.erase := by
  obtain ⟨m, hs⟩ := hw
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem (mem_erase.1 hr)
  obtain ⟨m₁, hpre, hpost⟩ := steps_split hs
  cases hpost with
  | @cons _ m₂ _ _ _ hst hrest =>
  have hlive : m₁.phase i.conn = .live := by cases hst with | ev h _ => exact h
  have hconn : CEvent.connect i.conn ∈ pre := Classical.byContradiction fun hn => by
    have := fresh_steps hpre hn rfl; rw [hlive] at this; cases this
  have hclose := hc i.conn (List.mem_append_left _ hconn)
  rcases List.mem_append.1 hclose with hcp | hcp
  · have := closed_of_close hpre hcp; rw [hlive] at this; cases this
  · rcases List.mem_cons.1 hcp with hcp | hcp
    · cases hcp
    · obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hcp
      obtain ⟨s, hs'⟩ := hg (pre ++ .ev (.recv i r) :: p₁) p₂ i.conn (by simp) i r
        (by rw [erase_append]; exact List.mem_append_right _ (mem_erase.2 List.mem_cons_self)) rfl
      refine ⟨s, ?_⟩
      have : pre ++ CEvent.ev (Event.recv i r) :: (p₁ ++ CEvent.close i.conn :: p₂) =
          (pre ++ CEvent.ev (Event.recv i r) :: p₁) ++ CEvent.close i.conn :: p₂ := by simp
      rw [this, erase_append]
      exact List.mem_append_left _ hs'

end Silmaril.Proofs.Servers.Sessions
