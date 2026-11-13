module

public import Silmaril.Net.Tcp.State.Defs

/-!
# TCP connection state machine: theorems

PROVED (standard axioms):

* `Steps.trans`, `Steps.single`: runs compose.
* The scenarios of RFC 9293 §3.5 and §3.6 as runs: **`active_open`** (CLOSED → SYN-SENT →
  ESTABLISHED, Figure 6 left), **`passive_open`** (CLOSED → LISTEN → SYN-RECEIVED →
  ESTABLISHED, Figure 6 right), `simultaneous_open` (Figure 7), **`active_close`**
  (ESTABLISHED → FIN-WAIT-1 → FIN-WAIT-2 → TIME-WAIT → CLOSED, Figure 12 left),
  **`passive_close`** (ESTABLISHED → CLOSE-WAIT → LAST-ACK → CLOSED, Figure 12 right),
  `simultaneous_close` (via CLOSING, Figure 13).
* `reach_all`: every state is reachable from CLOSED; **`to_closed`**: CLOSED is reachable from
  every state (there is no trap state).
* **`finSent_stable`**: once our FIN is sent, every transition keeps it sent or ends in
  CLOSED (no data is sent after a CLOSE); **`finRcvd_stable`**: the same for the peer's FIN
  (no data arrives after the peer's FIN). `finRcvd_not_canRecvData`, `finSent_not_canSend`.
* `next_deterministic`: the arrows of the figure form a function; `step_closed`: from CLOSED
  only OPEN moves.
-/

@[expose] public section

namespace Silmaril.Net.Tcp

theorem Steps.single {s e a s'} (h : Step s e a s') : Steps s [(e, a)] s' :=
  .cons h (.refl _)

theorem Steps.trans {s l s' m s''} (h1 : Steps s l s') (h2 : Steps s' m s'') :
    Steps s (l ++ m) s'' := by
  induction h1 with
  | refl => exact h2
  | cons h _ ih => exact .cons h (ih h2)

private theorem arr {s e a s'} (h : next s e = some (a, s')) : Step s e a s' := .arrow h

/-- **Active open** (Figure 6, left): CLOSED, snd SYN, SYN-SENT, rcv SYN,ACK, snd ACK,
ESTABLISHED. -/
theorem active_open :
    Steps .closed [(.activeOpen, .sndSyn), (.rcvSynAck, .sndAck)] .established :=
  .cons (arr rfl) (.cons (arr rfl) (.refl _))

/-- **Passive open** (Figure 6, right): CLOSED, LISTEN, rcv SYN, snd SYN,ACK, SYN-RECEIVED,
rcv ACK of SYN, ESTABLISHED. -/
theorem passive_open :
    Steps .closed [(.passiveOpen, .none), (.rcvSyn, .sndSynAck), (.rcvAckOfSyn, .none)]
      .established :=
  .cons (arr rfl) (.cons (arr rfl) (.cons (arr rfl) (.refl _)))

/-- **Simultaneous open** (Figure 7): SYN-SENT, rcv SYN, SYN-RECEIVED, rcv ACK, ESTABLISHED. -/
theorem simultaneous_open :
    Steps .closed [(.activeOpen, .sndSyn), (.rcvSyn, .sndSynAck), (.rcvAckOfSyn, .none)]
      .established :=
  .cons (arr rfl) (.cons (arr rfl) (.cons (arr rfl) (.refl _)))

/-- **Active close** (Figure 12, left). -/
theorem active_close :
    Steps .established [(.close, .sndFin), (.rcvAckOfFin, .none), (.rcvFin, .sndAck),
      (.timeout2Msl, .none)] .closed :=
  .cons (arr rfl) (.cons (arr rfl) (.cons (arr rfl) (.cons (arr rfl) (.refl _))))

/-- **Passive close** (Figure 12, right). -/
theorem passive_close :
    Steps .established [(.rcvFin, .sndAck), (.close, .sndFin), (.rcvAckOfFin, .none)] .closed :=
  .cons (arr rfl) (.cons (arr rfl) (.cons (arr rfl) (.refl _)))

/-- **Simultaneous close** (Figure 13): FIN-WAIT-1, rcv FIN, CLOSING, rcv ACK, TIME-WAIT. -/
theorem simultaneous_close :
    Steps .established [(.close, .sndFin), (.rcvFin, .sndAck), (.rcvAckOfFin, .none),
      (.timeout2Msl, .none)] .closed :=
  .cons (arr rfl) (.cons (arr rfl) (.cons (arr rfl) (.cons (arr rfl) (.refl _))))

/-- Every state is reachable from CLOSED. -/
theorem reach_all (s : State) : ∃ l, Steps .closed l s := by
  cases s with
  | closed => exact ⟨[], .refl _⟩
  | listen => exact ⟨_, .single (arr rfl : Step .closed .passiveOpen .none .listen)⟩
  | synSent => exact ⟨_, .single (arr rfl : Step .closed .activeOpen .sndSyn .synSent)⟩
  | synRcvd p =>
    cases p
    · exact ⟨_, .cons (arr rfl : Step .closed .activeOpen .sndSyn .synSent)
        (.single (arr rfl : Step .synSent .rcvSyn .sndSynAck (.synRcvd false)))⟩
    · exact ⟨_, .cons (arr rfl : Step .closed .passiveOpen .none .listen)
        (.single (arr rfl : Step .listen .rcvSyn .sndSynAck (.synRcvd true)))⟩
  | established => exact ⟨_, active_open⟩
  | finWait1 => exact ⟨_, active_open.trans (.single (arr rfl : Step _ .close .sndFin .finWait1))⟩
  | finWait2 => exact ⟨_, active_open.trans
      (.cons (arr rfl : Step _ .close .sndFin .finWait1)
        (.single (arr rfl : Step _ .rcvAckOfFin .none .finWait2)))⟩
  | closeWait => exact ⟨_, active_open.trans (.single (arr rfl : Step _ .rcvFin .sndAck .closeWait))⟩
  | closing => exact ⟨_, active_open.trans
      (.cons (arr rfl : Step _ .close .sndFin .finWait1)
        (.single (arr rfl : Step _ .rcvFin .sndAck .closing)))⟩
  | lastAck => exact ⟨_, active_open.trans
      (.cons (arr rfl : Step _ .rcvFin .sndAck .closeWait)
        (.single (arr rfl : Step _ .close .sndFin .lastAck)))⟩
  | timeWait => exact ⟨_, active_open.trans
      (.cons (arr rfl : Step _ .close .sndFin .finWait1)
        (.single (arr rfl : Step _ .rcvFinAckOfFin .sndAck .timeWait)))⟩

/-- **CLOSED is reachable from every state.** -/
theorem to_closed (s : State) : ∃ l, Steps s l .closed := by
  by_cases hc : s = .closed
  · subst hc; exact ⟨[], .refl _⟩
  · by_cases hl : s = .listen
    · subst hl; exact ⟨_, Steps.single (arr rfl : Step .listen .close .none .closed)⟩
    · exact ⟨_, Steps.single (.rstClosed hc hl)⟩

/-- **Once our FIN is sent**, every transition keeps it sent or ends in CLOSED. -/
theorem finSent_stable {s e a s'} (hs : s.finSent = true) (h : Step s e a s') :
    s'.finSent = true ∨ s' = .closed := by
  cases h with
  | arrow hn =>
    cases s <;> cases e <;> simp [State.finSent, next] at hs hn <;> (obtain ⟨-, rfl⟩ := hn) <;>
      simp [State.finSent]
  | rstPassive => simp [State.finSent] at hs
  | rstClosed => exact Or.inr rfl
  | rstListen => simp [State.finSent] at hs
  | abortRst => exact Or.inr rfl
  | abortQuiet => exact Or.inr rfl
  | rstTimeWait => exact Or.inl rfl

/-- **Once the peer's FIN is received**, every transition keeps it received or ends in CLOSED. -/
theorem finRcvd_stable {s e a s'} (hs : s.finRcvd = true) (h : Step s e a s') :
    s'.finRcvd = true ∨ s' = .closed := by
  cases h with
  | arrow hn =>
    cases s <;> cases e <;> simp [State.finRcvd, next] at hs hn <;> (obtain ⟨-, rfl⟩ := hn) <;>
      simp [State.finRcvd]
  | rstPassive => simp [State.finRcvd] at hs
  | rstClosed => exact Or.inr rfl
  | rstListen => simp [State.finRcvd] at hs
  | abortRst => exact Or.inr rfl
  | abortQuiet => exact Or.inr rfl
  | rstTimeWait => exact Or.inl rfl

theorem finRcvd_not_canRecvData (s : State) (h : s.finRcvd = true) : s.canRecvData = false := by
  cases s <;> simp [State.finRcvd, State.canRecvData] at h ⊢

theorem finSent_not_canSend (s : State) (h : s.finSent = true) : s.canSend = false := by
  cases s <;> simp [State.finSent, State.canSend] at h ⊢

/-- The arrows of the figure form a function. -/
theorem next_deterministic {s e a a' s' s''} (h1 : next s e = some (a, s'))
    (h2 : next s e = some (a', s'')) : a = a' ∧ s' = s'' := by
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

/-- From CLOSED, only an OPEN moves. -/
theorem step_closed {e a s'} (h : Step .closed e a s') :
    (e = .passiveOpen ∧ s' = .listen) ∨ (e = .activeOpen ∧ s' = .synSent) := by
  cases h with
  | arrow hn =>
    cases e <;> simp [next] at hn <;> (obtain ⟨-, rfl⟩ := hn) <;> simp
  | rstClosed hc => exact absurd rfl hc
  | abortRst h =>
    rcases h with h | ⟨p, hp⟩
    · simp [State.synchronized] at h
    · cases hp
  | abortQuiet h => rcases h with h | h <;> cases h
  | rstTimeWait hc => exact absurd rfl hc

end Silmaril.Net.Tcp
