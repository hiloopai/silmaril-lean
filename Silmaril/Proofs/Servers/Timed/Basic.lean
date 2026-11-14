module

public import Silmaril.Servers.Timed.Defs
public import Silmaril.Servers.Sockets.Thms

/-!
# Core traces read from the timing of socket events: proofs

For `Silmaril.Servers.Timed.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Timed

open Silmaril.Servers Silmaril.Servers.Platform Silmaril.Servers.Timed

theorem zipIdx_prefix {α : Type} {l l' : List α} (h : l <+: l') : l.zipIdx <+: l'.zipIdx := by
  obtain ⟨t, rfl⟩ := h
  rw [List.zipIdx_append]
  exact List.prefix_append _ _

/-- Telescoping: a prefix chain `a <+: b <+: c` read in two steps. -/
theorem drop_drop_chain {α : Type} {a b c : List α} (hab : a.length ≤ b.length) (hbc : b <+: c) :
    b.drop a.length ++ c.drop b.length = c.drop a.length := by
  obtain ⟨t, rfl⟩ := hbc
  rw [List.drop_append_of_le_length hab, List.drop_left]

theorem received_snoc_ne {c : ConnId} {e : SockEv} (h : connOfEv e ≠ c) (pre : List SockEv) :
    received c (pre ++ [e]) = received c pre := by
  rw [Sockets.received_append]
  cases e <;> simp_all [received, connOfEv]

theorem sent_snoc_ne {c : ConnId} {e : SockEv} (h : connOfEv e ≠ c) (pre : List SockEv) :
    sent c (pre ++ [e]) = sent c pre := by
  rw [Sockets.sent_append]
  cases e <;> simp_all [sent, connOfEv]

theorem recvsOn_append (c : ConnId) (a b : Trace Http.sig) :
    recvsOn c (a ++ b) = recvsOn c a ++ recvsOn c b := List.filterMap_append

theorem sendsOn_append (c : ConnId) (a b : Trace Http.sig) :
    sendsOn c (a ++ b) = sendsOn c a ++ sendsOn c b := List.filterMap_append

theorem filterMap_map_some {α β γ : Type} (f : α → β) (g : β → Option γ) (k : α → γ)
    (h : ∀ x, g (f x) = some (k x)) : ∀ l : List α, (l.map f).filterMap g = l.map k
  | [] => rfl
  | x :: l => by simp [h, filterMap_map_some f g k h l]

theorem recvsOn_newRecvs (fr : Framing) (c d : ConnId) (pre cur : List SockEv) :
    recvsOn c (newRecvs fr d pre cur) =
      if d = c then (((fr.requests (received d cur)).zipIdx).drop
        (fr.requests (received d pre)).length).map fun p => ((⟨d, p.2⟩ : ReqId), p.1)
      else [] := by
  unfold recvsOn newRecvs
  split
  · subst_vars
    exact filterMap_map_some _ _ _ (fun p => by simp) _
  · rw [List.filterMap_map, List.filterMap_eq_nil_iff]
    intro p _
    simp_all

theorem sendsOn_newRecvs (fr : Framing) (c d : ConnId) (pre cur : List SockEv) :
    sendsOn c (newRecvs fr d pre cur) = [] := by
  unfold sendsOn newRecvs
  rw [List.filterMap_map, List.filterMap_eq_nil_iff]
  intro p _
  rfl

theorem recvsOn_newSends (fr : Framing) (c d : ConnId) (pre cur : List SockEv) :
    recvsOn c (newSends fr d pre cur) = [] := by
  unfold recvsOn newSends
  rw [List.filterMap_map, List.filterMap_eq_nil_iff]
  intro p _
  rfl

theorem sendsOn_newSends (fr : Framing) (c d : ConnId) (pre cur : List SockEv) :
    sendsOn c (newSends fr d pre cur) =
      if d = c then (((connLog fr cur d).zipIdx).drop (connLog fr pre d).length).map
        fun p => ((⟨d, p.2⟩ : ReqId), p.1.2)
      else [] := by
  unfold sendsOn newSends
  split
  · subst_vars
    exact filterMap_map_some _ _ _ (fun p => by simp) _
  · rw [List.filterMap_map, List.filterMap_eq_nil_iff]
    intro p _
    simp_all

/-- The receptions of `c` in the step of `e`: the newly complete requests of `c`, whatever the
connection of `e` (another connection's event completes nothing on `c`). -/
theorem recvsOn_stepEvs (fr : Framing) (c : ConnId) (pre : List SockEv) (e : SockEv) :
    recvsOn c (stepEvs fr pre e) =
      (((fr.requests (received c (pre ++ [e]))).zipIdx).drop
        (fr.requests (received c pre)).length).map fun p => ((⟨c, p.2⟩ : ReqId), p.1) := by
  unfold stepEvs
  rw [recvsOn_append, recvsOn_newRecvs, recvsOn_newSends, List.append_nil]
  split
  · subst_vars; rfl
  · rw [received_snoc_ne (by assumption), List.drop_eq_nil_of_le (by simp)]
    rfl

theorem sendsOn_stepEvs (fr : Framing) (c : ConnId) (pre : List SockEv) (e : SockEv) :
    sendsOn c (stepEvs fr pre e) =
      (((connLog fr (pre ++ [e]) c).zipIdx).drop (connLog fr pre c).length).map
        fun p => ((⟨c, p.2⟩ : ReqId), p.1.2) := by
  unfold stepEvs
  rw [sendsOn_append, sendsOn_newRecvs, sendsOn_newSends, List.nil_append]
  split
  · subst_vars; rfl
  · have hc : connLog fr (pre ++ [e]) c = connLog fr pre c := by
      simp only [connLog, received_snoc_ne (by assumption), sent_snoc_ne (by assumption)]
    rw [hc, List.drop_eq_nil_of_le (by simp)]
    rfl

theorem recvsOn_timedAux {fr : Framing} (hm : Mono fr) (c : ConnId) :
    ∀ (rest pre : List SockEv), recvsOn c (timedAux fr pre rest) =
      (((fr.requests (received c (pre ++ rest))).zipIdx).drop
        (fr.requests (received c pre)).length).map fun p => ((⟨c, p.2⟩ : ReqId), p.1)
  | [], pre => by
    simp only [timedAux, List.append_nil]
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl
  | e :: rest, pre => by
    simp only [timedAux]
    rw [recvsOn_append, recvsOn_stepEvs, recvsOn_timedAux hm c rest (pre ++ [e]),
      ← List.map_append, List.append_assoc, List.singleton_append]
    congr 1
    have h1 := hm.2.1 (received c pre) (received c [e])
    have h2 := hm.2.1 (received c (pre ++ [e])) (received c rest)
    rw [← Sockets.received_append] at h1
    rw [← Sockets.received_append, List.append_assoc, List.singleton_append] at h2
    have := drop_drop_chain (a := (fr.requests (received c pre)).zipIdx)
      (b := (fr.requests (received c (pre ++ [e]))).zipIdx)
      (c := (fr.requests (received c (pre ++ e :: rest))).zipIdx)
      (by simpa using h1.length_le) (zipIdx_prefix h2)
    simpa using this

theorem sendsOn_timedAux {fr : Framing} (hm : Mono fr) (c : ConnId) :
    ∀ (rest pre : List SockEv), sendsOn c (timedAux fr pre rest) =
      (((connLog fr (pre ++ rest) c).zipIdx).drop (connLog fr pre c).length).map
        fun p => ((⟨c, p.2⟩ : ReqId), p.1.2)
  | [], pre => by
    simp only [timedAux, List.append_nil]
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl
  | e :: rest, pre => by
    simp only [timedAux]
    rw [sendsOn_append, sendsOn_stepEvs, sendsOn_timedAux hm c rest (pre ++ [e]),
      ← List.map_append, List.append_assoc, List.singleton_append]
    congr 1
    have h1 := hm.2.2 (received c pre) (received c [e]) (sent c pre) (sent c [e])
    have h2 := hm.2.2 (received c (pre ++ [e])) (received c rest) (sent c (pre ++ [e]))
      (sent c rest)
    simp only [← Sockets.received_append, ← Sockets.sent_append, List.append_assoc,
      List.singleton_append] at h1 h2
    have := drop_drop_chain (a := (connLog fr pre c).zipIdx)
      (b := (connLog fr (pre ++ [e]) c).zipIdx) (c := (connLog fr (pre ++ e :: rest) c).zipIdx)
      (by simpa [connLog] using h1.length_le) (zipIdx_prefix (by simpa [connLog] using h2))
    simpa using this

end Silmaril.Proofs.Servers.Timed
