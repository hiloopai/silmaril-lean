module

public import Silmaril.Servers.Exchange.Defs

/-!
# Exchange servers: the sequential use determines the server

For `Silmaril.Servers.Exchange.Thms`: a sequential trace determines its tagged history
(`seq_inj`), and every history is the history of a sequential trace on fresh identities
(`tag`), so `seqUse` reflects refinement.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Exchange

open Silmaril.Servers Silmaril.Servers.Exchange

variable {I : Iface}

/-- A history tagged with the identities `⟨0, n⟩`, `⟨0, n + 1⟩`, …: one connection. -/
def tag {α β : Type} : Nat → List (α × β) → List (ReqId × α × β)
  | _, [] => []
  | n, p :: l => (⟨0, n⟩, p) :: tag (n + 1) l

theorem tag_snd {α β : Type} : ∀ (n : Nat) (l : List (α × β)), (tag n l).map (·.2) = l
  | _, [] => rfl
  | n, p :: l => by simp only [tag, List.map_cons, tag_snd (n + 1) l]

theorem tag_ge {α β : Type} : ∀ (n : Nat) (l : List (α × β)), ∀ x ∈ (tag n l).map (·.1), n ≤ x.seq
  | _, [] => by simp [tag]
  | n, p :: l => by
    intro x hx
    simp only [tag, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (tag_ge (n + 1) l x hx)

theorem tag_nodup {α β : Type} : ∀ (n : Nat) (l : List (α × β)), ((tag n l).map (·.1)).Nodup
  | _, [] => List.nodup_nil
  | n, p :: l => by
    simp only [tag, List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, tag_nodup (n + 1) l⟩
    have : n + 1 ≤ n := tag_ge (n + 1) l _ h
    omega

theorem seq_inj : ∀ h h' : List (ReqId × I.Req × I.Resp), Trace.seq h = Trace.seq h' → h = h'
  | [], [], _ => rfl
  | [], _ :: _, e => by simp [Trace.seq] at e
  | _ :: _, [], e => by simp [Trace.seq] at e
  | (i, r, s) :: h, (i', r', s') :: h', e => by
    simp only [Trace.seq, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
      Event.recv.injEq, Event.send.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, ⟨-, rfl⟩, e⟩ := e
    rw [seq_inj h h' e]

theorem seqUse_refines_iff (M N : Exchange.Model I) : (seqUse M).Refines (seqUse N) ↔ Refines M N := by
  refine ⟨fun H l hl => ?_, fun H _ ⟨l, hn, hm, ht⟩ => ⟨l, hn, H hm, ht⟩⟩
  obtain ⟨h', -, hm', e⟩ := H _ ⟨tag 0 l, tag_nodup 0 l, by rw [tag_snd]; exact hl, rfl⟩
  rw [seq_inj _ _ e.symm, tag_snd] at hm'
  exact hm'

end Silmaril.Proofs.Servers.Exchange
