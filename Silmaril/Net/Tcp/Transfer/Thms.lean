module

public import Silmaril.Net.Tcp.Transfer.Defs
public import Silmaril.Net.Tcp.Seq.Thms
public import Silmaril.Net.Tcp.State.Thms
public import Silmaril.Net.Tcp.Service.Thms

/-!
# TCP connection transferring one stream: theorems

PROVED (standard axioms):

* **`tstep_sim`** (the refinement step): every transition of the connection keeps the invariant
  `Inv` and performs, on the users' view `Sys.svc`, exactly its service events as steps of the
  byte-stream service `SvcStep`. Hence **`tsteps_svc`**: every run from `Sys.init` is, seen by
  the users, a run of the service (`SvcSteps {} l s.svc`), and **`stream_safe`**: what `B`
  delivered is a prefix of what `A`'s user wrote, and end of stream means `A` closed and
  everything was delivered. This holds over a network that loses, duplicates and reorders
  segments arbitrarily, for any initial sequence numbers.
* **`tstep_fig5`**: every transition moves each endpoint along an arrow of Figure 5
  (`Tcp.State.Step`) or leaves its state unchanged.
* **`handshake`**: from `Sys.init`, the three-way handshake reaches ESTABLISHED at both ends.
* **`can_deliver`** (the reachability core of liveness): from every reachable state where the
  connection is established, a run of two transitions (one retransmission, one receipt)
  delivers the whole stream.
* `Inv.init`: the invariant holds initially.
* **`wrap_unsafe`** (refutation): without the bound `writeOk` on the stream length, safety
  fails: a state meeting every other part of the invariant, with a stream of `2^32 + 1`
  octets, lets `B` accept a stale segment whose sequence number has wrapped round to RCV.NXT
  and deliver an octet out of place (`wrap_unsafe_gen`: for every such length).

The key fact is `Tcp.Seq.Thms.adv_inj`: within one connection the stream is shorter than 2^32
octets (`writeOk`), so a segment starting at RCV.NXT carries the next octets of the stream.

OPEN: `Task.tcpStreamLive` (liveness under weak fairness of the protocol actions, frozen in
`Tcp.Transfer.Defs`); the model's simplifications are listed there.
-/

@[expose] public section

namespace Silmaril.Net.Tcp

open Silmaril.Net.Tcp.SeqNum

/-! ## The invariant -/

/-- **A segment from `A` agrees with `A`'s stream**: a SYN sits at the initial sequence number;
any other segment at `iss + 1 + o` carries the octets of the stream from offset `o`, and a FIN
only after `A`'s user closed and right after the last octet. -/
def Good (a : Snd) (g : Seg) : Prop :=
  (g.syn = true → g.seq = a.iss ∧ g.data = [] ∧ g.fin = false) ∧
  (g.syn = false → ∃ o, g.seq = adv a.iss (1 + o) ∧ o + g.data.length ≤ a.buf.length ∧
    g.data = (a.buf.drop o).take g.data.length ∧
    (g.fin = true → a.closed = true ∧ o + g.data.length = a.buf.length))

/-- `B` has not reported end of stream in its early states. -/
def Rcv.early (b : Rcv) : Prop := b.st = .listen ∨ b.st = .synRcvd true ∨ b.st = .established

/-- **The invariant of the connection.** -/
structure Inv (s : Sys) : Prop where
  bound : s.a.buf.length + 2 < 2 ^ 32
  good : ∀ g ∈ s.ab, Good s.a g
  fw1 : s.a.st = .finWait1 → s.a.closed = true
  listen : s.b.st = .listen → s.b.delivered = []
  early : s.b.early → s.b.eof = false
  nxt : s.b.st ≠ .listen →
    s.b.nxt = adv s.a.iss (1 + s.b.delivered.length + (if s.b.eof then 1 else 0))
  pre : s.b.delivered <+: s.a.buf
  eof : s.b.eof = true → s.a.closed = true ∧ s.b.delivered = s.a.buf

/-- The invariant holds initially. -/
theorem Inv.init (issA issB : SeqNum) : Inv (Sys.init issA issB) where
  bound := by simp [Sys.init]
  good := by simp [Sys.init]
  fw1 := by simp [Sys.init]
  listen := fun _ => rfl
  early := fun _ => rfl
  nxt := fun h => absurd rfl h
  pre := List.nil_prefix
  eof := fun h => by cases h

/-! ## Segments of `A` -/

theorem good_congr {a a' : Snd} {g : Seg} (hi : a'.iss = a.iss) (hb : a'.buf = a.buf)
    (hc : a.closed = true → a'.closed = true) (h : Good a g) : Good a' g := by
  refine ⟨fun hs => hi ▸ h.1 hs, fun hs => ?_⟩
  obtain ⟨o, h1, h2, h3, h4⟩ := h.2 hs
  exact ⟨o, hi ▸ h1, hb ▸ h2, hb ▸ h3, fun hf => ⟨hc (h4 hf).1, hb ▸ (h4 hf).2⟩⟩

theorem good_append {a : Snd} {g : Seg} (bs : List UInt8) (hc : a.closed = false)
    (h : Good a g) : Good { a with buf := a.buf ++ bs } g := by
  refine ⟨h.1, fun hs => ?_⟩
  obtain ⟨o, h1, h2, h3, h4⟩ := h.2 hs
  have hd : ((a.buf ++ bs).drop o).take g.data.length = (a.buf.drop o).take g.data.length := by
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
    simp only [List.length_drop]; omega
  refine ⟨o, h1, ?_, hd ▸ h3, fun hf => ?_⟩
  · simp only [List.length_append]; omega
  · have := (h4 hf).1
    rw [hc] at this; cases this

theorem good_syn (a : Snd) : Good a a.synSeg :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun h => by simp [Snd.synSeg] at h⟩

theorem good_ack (a : Snd) : Good a a.ackSeg :=
  ⟨fun h => by simp [Snd.ackSeg] at h, fun _ => ⟨a.buf.length, rfl, by simp [Snd.ackSeg],
    by simp [Snd.ackSeg], fun h => by simp [Snd.ackSeg] at h⟩⟩

theorem good_data (a : Snd) {o n : Nat} (h : o + n ≤ a.buf.length) : Good a (a.dataSeg o n) := by
  have hl : ((a.buf.drop o).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  refine ⟨fun h => by simp [Snd.dataSeg] at h, fun _ => ⟨o, rfl, ?_, ?_,
    fun h => by simp [Snd.dataSeg] at h⟩⟩
  · show o + ((a.buf.drop o).take n).length ≤ a.buf.length
    rw [hl]; exact h
  · show (a.buf.drop o).take n = (a.buf.drop o).take ((a.buf.drop o).take n).length
    rw [hl]

theorem good_fin (a : Snd) (hc : a.closed = true) : Good a a.finSeg :=
  ⟨fun h => by simp [Snd.finSeg] at h, fun _ => ⟨a.buf.length, rfl, by simp [Snd.finSeg],
    by simp [Snd.finSeg], fun _ => ⟨hc, by simp [Snd.finSeg]⟩⟩⟩

/-- Segments added to `ab` keep `good` when every new one is good. -/
theorem good_cons {a : Snd} {g : Seg} {ab : List Seg} (hg : Good a g)
    (h : ∀ x ∈ ab, Good a x) : ∀ x ∈ g :: ab, Good a x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hg
  · exact h x hx

/-! ## The receiver accepts the next octets of the stream -/

theorem adv_eq_off {iss : SeqNum} {o d : Nat} (ho : o < 2 ^ 32 - 1) (hd : d < 2 ^ 32 - 1)
    (h : adv iss (1 + o) = adv iss (1 + d)) : o = d := by
  have := adv_inj iss (i := 1 + o) (j := 1 + d) (by omega) (by omega) h
  omega

/-- **Receipt of the segment starting at RCV.NXT**: it carries the octets of the stream right
after those delivered, and a FIN only once they are all delivered. -/
theorem bData_next {s : Sys} (hi : Inv s) {g : Seg} (hst : s.b.st = .established)
    (hg : g ∈ s.ab) (hs : g.syn = false) (hq : g.seq = s.b.nxt) :
    s.b.delivered ++ g.data = s.a.buf.take (s.b.delivered.length + g.data.length) ∧
    (g.fin = true → s.a.closed = true ∧ s.b.delivered.length + g.data.length = s.a.buf.length) := by
  have heof : s.b.eof = false := hi.early (Or.inr (Or.inr hst))
  have hn : s.b.nxt = adv s.a.iss (1 + s.b.delivered.length) := by
    have h := hi.nxt (by rw [hst]; decide)
    simpa [heof] using h
  obtain ⟨o, h1, h2, h3, h4⟩ := (hi.good g hg).2 hs
  have hdl : s.b.delivered.length ≤ s.a.buf.length := hi.pre.length_le
  have hb : s.a.buf.length + 2 < 2 ^ 32 := hi.bound
  have ho : o = s.b.delivered.length :=
    adv_eq_off (by omega) (by omega) (h1.symm.trans (hq.trans hn))
  have hdel : s.b.delivered = s.a.buf.take s.b.delivered.length :=
    List.prefix_iff_eq_take.mp hi.pre
  have h3' : g.data = (s.a.buf.drop s.b.delivered.length).take g.data.length := ho ▸ h3
  refine ⟨?_, fun hf => ⟨(h4 hf).1, ho ▸ (h4 hf).2⟩⟩
  rw [List.take_add, ← hdel, ← h3']

/-- The invariant does not look at the segments `B` sent. -/
theorem Inv.with_ba {s : Sys} (hi : Inv s) (ba : List Seg) : Inv { s with ba := ba } :=
  ⟨hi.bound, hi.good, hi.fw1, hi.listen, hi.early, hi.nxt, hi.pre, hi.eof⟩

/-! ## The refinement step -/

/-- The service steps of a receipt. -/
theorem bData_svc {sv : Svc} {d : List UInt8} {f : Bool} (he : sv.eof = false)
    (hne : d ≠ [] ∨ f = true) (hp : sv.read ++ d <+: sv.written)
    (hf : f = true → sv.closed = true ∧ sv.read ++ d = sv.written) :
    SvcSteps sv (readEv d ++ (if f then [.eof] else []))
      { sv with read := sv.read ++ d, eof := f } := by
  by_cases hd : d = []
  · subst hd
    have hft : f = true := by simpa using hne
    subst hft
    have h := SvcStep.eof (s := sv) (hf rfl).1 (by simpa using (hf rfl).2) he
    simpa [readEv] using SvcSteps.single h
  · have h1 : SvcStep sv (.read d) { sv with read := sv.read ++ d } := .read d hd hp
    cases f with
    | false =>
      have hr : readEv d = [.read d] := by simp [readEv, hd]
      simpa [hr, he] using SvcSteps.single h1
    | true =>
      have h2 : SvcStep { sv with read := sv.read ++ d } .eof
          { sv with read := sv.read ++ d, eof := true } :=
        .eof (hf rfl).1 (hf rfl).2 he
      have hr : readEv d = [.read d] := by simp [readEv, hd]
      simpa [hr] using SvcSteps.cons h1 (SvcSteps.single h2)

/-- `B`'s receipt keeps the invariant. -/
theorem bData_inv {s : Sys} (hi : Inv s) {g : Seg} (hst : s.b.st = .established)
    (hg : g ∈ s.ab) (hs : g.syn = false) (hq : g.seq = s.b.nxt) :
    Inv { s with
          b := { s.b with
            st := if g.fin then .closeWait else .established
            nxt := SeqNum.adv s.b.nxt g.len
            delivered := s.b.delivered ++ g.data
            eof := g.fin }
          ba := ({ s.b with nxt := SeqNum.adv s.b.nxt g.len } : Rcv).ackSeg :: s.ba } := by
  obtain ⟨hd, hf⟩ := bData_next hi hst hg hs hq
  have heof : s.b.eof = false := hi.early (Or.inr (Or.inr hst))
  have hn : s.b.nxt = adv s.a.iss (1 + s.b.delivered.length) := by
    have h := hi.nxt (by rw [hst]; decide)
    simpa [heof] using h
  have hpre : s.b.delivered ++ g.data <+: s.a.buf := hd ▸ List.take_prefix _ _
  refine ⟨hi.bound, hi.good, hi.fw1, ?_, ?_, ?_, hpre, ?_⟩
  · intro h; cases hfin : g.fin <;> simp [hfin] at h
  · intro h
    cases hfin : g.fin
    · rfl
    · simp [Rcv.early, hfin] at h
  · intro _
    show adv s.b.nxt g.len =
      adv s.a.iss (1 + (s.b.delivered ++ g.data).length + (if g.fin then 1 else 0))
    rw [hn, adv_adv, Seg.len, List.length_append]
    congr 1
    omega
  · intro he
    obtain ⟨hc, hl⟩ := hf he
    refine ⟨hc, ?_⟩
    rw [hd, hl, List.take_length]

/-- A write keeps the invariant. -/
theorem inv_aWrite {s : Sys} (hi : Inv s) (bs : List UInt8) (hc : s.a.closed = false)
    (hw : writeOk s.a bs) : Inv { s with a := { s.a with buf := s.a.buf ++ bs } } := by
  have hb : (s.a.buf ++ bs).length + 2 < 2 ^ 32 := by
    simp only [List.length_append]; exact hw
  have hf : s.a.st = .finWait1 → false = true := fun h => hc ▸ hi.fw1 h
  have he : s.b.eof = true → false = true ∧ s.b.delivered = s.a.buf ++ bs := fun h =>
    absurd (hc ▸ (hi.eof h).1) (by decide)
  exact ⟨hb, fun g hg => good_append bs hc (hi.good g hg), fun h => hc ▸ hf h, hi.listen,
    hi.early, hi.nxt, hi.pre.trans (List.prefix_append _ _), fun h => (hc ▸ he h)⟩

/-- A close keeps the invariant. -/
theorem inv_aClose {s : Sys} (hi : Inv s) :
    Inv { s with a := { s.a with st := .finWait1, closed := true }, ab := s.a.finSeg :: s.ab } := by
  have hg : ∀ g ∈ s.a.finSeg :: s.ab, Good { s.a with st := .finWait1, closed := true } g :=
    good_cons (good_fin { s.a with st := .finWait1, closed := true } rfl)
      (fun g hg => good_congr (a := s.a) rfl rfl (fun _ => rfl) (hi.good g hg))
  exact ⟨hi.bound, hg, fun _ => rfl, hi.listen, hi.early, hi.nxt, hi.pre,
    fun he => ⟨rfl, (hi.eof he).2⟩⟩

/-- A change of `A`'s state or RCV.NXT, with a new segment that is good, keeps the invariant. -/
theorem inv_aState {s : Sys} (hi : Inv s) (st : State) (r : SeqNum) (hst : st ≠ .finWait1)
    (ab : List Seg) (hab : ∀ g ∈ ab, Good { s.a with st := st, rnxt := r } g) :
    Inv { s with a := { s.a with st := st, rnxt := r }, ab := ab } :=
  ⟨hi.bound, hab, fun h => absurd h hst, hi.listen, hi.early, hi.nxt, hi.pre, hi.eof⟩

/-- Good segments of `A` stay good across a change of its state or RCV.NXT. -/
theorem good_aState {s : Sys} (hi : Inv s) (st : State) (r : SeqNum) :
    ∀ g ∈ s.ab, Good { s.a with st := st, rnxt := r } g :=
  fun g hg => good_congr (a := s.a) rfl rfl id (hi.good g hg)

/-- A new good segment of `A` keeps the invariant. -/
theorem inv_aSeg {s : Sys} (hi : Inv s) {g : Seg} (hg : Good s.a g) :
    Inv { s with ab := g :: s.ab } :=
  ⟨hi.bound, good_cons hg hi.good, hi.fw1, hi.listen, hi.early, hi.nxt, hi.pre, hi.eof⟩

/-- A change of `B`'s state out of LISTEN, keeping RCV.NXT and leaving the early states or
staying in them before end of stream, keeps the invariant. -/
theorem inv_bState {s : Sys} (hi : Inv s) (st : State) (hl : st ≠ .listen) (hb : s.b.st ≠ .listen)
    (he : Rcv.early { s.b with st := st } → s.b.eof = false) :
    Inv { s with b := { s.b with st := st } } :=
  ⟨hi.bound, hi.good, hi.fw1, fun h => absurd h hl, he, fun _ => hi.nxt hb, hi.pre, hi.eof⟩

/-- `B`'s receipt of the SYN keeps the invariant. -/
theorem inv_bSyn {s : Sys} (hi : Inv s) {g : Seg} (hst : s.b.st = .listen) (hg : g ∈ s.ab)
    (hsyn : g.syn = true) :
    Inv { s with
      b := { s.b with st := .synRcvd true, nxt := adv g.seq 1 }
      ba := ({ s.b with nxt := adv g.seq 1 } : Rcv).synAckSeg :: s.ba } := by
  have hq : g.seq = s.a.iss := ((hi.good g hg).1 hsyn).1
  have hd : s.b.delivered = [] := hi.listen hst
  have he : s.b.eof = false := hi.early (Or.inl hst)
  have hn : adv g.seq 1 =
      adv s.a.iss (1 + s.b.delivered.length + (if s.b.eof then 1 else 0)) := by
    rw [hq, hd, he]; rfl
  have hl : State.synRcvd true ≠ State.listen := by decide
  exact ⟨hi.bound, hi.good, hi.fw1, fun h => absurd h hl, fun _ => he, fun _ => hn,
    hi.pre, hi.eof⟩

/-- **The refinement step**: a transition keeps the invariant and performs its service events
on the users' view. -/
theorem tstep_sim {s s' : Sys} {l : List SvcEv} (hi : Inv s) (h : TStep s l s') :
    Inv s' ∧ SvcSteps s.svc l s'.svc := by
  cases h with
  | aOpen hst =>
    exact ⟨inv_aState hi _ s.a.rnxt (by decide) _ (good_cons (good_syn _) (good_aState hi _ _)),
      .refl _⟩
  | aResendSyn hst => exact ⟨inv_aSeg hi (good_syn _), .refl _⟩
  | aWrite bs hc hw => exact ⟨inv_aWrite hi bs hc hw, .single (SvcStep.write bs hc)⟩
  | aSynAck hst _ _ _ _ =>
    exact ⟨inv_aState hi _ _ (by decide) _ (good_cons (good_ack _) (good_aState hi _ _)), .refl _⟩
  | aSend o n hst hon => exact ⟨inv_aSeg hi (good_data _ hon), .refl _⟩
  | aClose hst hc => exact ⟨inv_aClose hi, .single (SvcStep.close hc)⟩
  | aResendFin hst => exact ⟨inv_aSeg hi (good_fin _ (hi.fw1 hst)), .refl _⟩
  | aAckOfFin hst _ _ _ _ =>
    exact ⟨inv_aState hi .finWait2 s.a.rnxt (by decide) _ (good_aState hi _ _), .refl _⟩
  | aFin hst _ _ _ =>
    exact ⟨inv_aState hi _ _ (by decide) _ (good_cons (good_ack _) (good_aState hi _ _)), .refl _⟩
  | aTimeout hst =>
    exact ⟨inv_aState hi .closed s.a.rnxt (by decide) _ (good_aState hi _ _), .refl _⟩
  | bSyn hst hg hsyn => exact ⟨inv_bSyn hi hst hg hsyn, .refl _⟩
  | bResendSynAck hst => exact ⟨hi.with_ba _, .refl _⟩
  | bAck hst _ _ _ _ =>
    exact ⟨(inv_bState hi .established (by decide) (by rw [hst]; decide)
      (fun _ => hi.early (Or.inr (Or.inl hst)))).with_ba _, .refl _⟩
  | bData hst hg hs hq hne =>
    obtain ⟨hd, hf⟩ := bData_next hi hst hg hs hq
    have heof : s.b.eof = false := hi.early (Or.inr (Or.inr hst))
    have hp : s.b.delivered ++ _ <+: s.a.buf := hd ▸ List.take_prefix _ _
    have hfe : _ → s.a.closed = true ∧ s.b.delivered ++ _ = s.a.buf :=
      fun he => ⟨(hf he).1, by rw [hd, (hf he).2, List.take_length]⟩
    exact ⟨bData_inv hi hst hg hs hq, bData_svc heof hne hp hfe⟩
  | bSendAck hst => exact ⟨hi.with_ba _, .refl _⟩
  | bClose hst =>
    exact ⟨(inv_bState hi .lastAck (by decide) (by rw [hst]; decide)
      (fun h => absurd h (by simp [Rcv.early]))).with_ba _, .refl _⟩
  | bResendFin hst => exact ⟨hi.with_ba _, .refl _⟩
  | bAckOfFin hst _ _ _ _ =>
    exact ⟨inv_bState hi .closed (by decide) (by rw [hst]; decide)
      (fun h => absurd h (by simp [Rcv.early])), .refl _⟩

/-- **Runs refine the service**: from an invariant state, a run is, on the users' view, a run of
the byte-stream service. -/
theorem tsteps_sim {s s' : Sys} {l : List SvcEv} (hi : Inv s) (h : TSteps s l s') :
    Inv s' ∧ SvcSteps s.svc l s'.svc := by
  induction h with
  | refl => exact ⟨hi, .refl _⟩
  | cons h1 _ ih =>
    obtain ⟨hi1, hs1⟩ := tstep_sim hi h1
    obtain ⟨hi2, hs2⟩ := ih hi1
    exact ⟨hi2, hs1.trans hs2⟩

/-- **Every run of the connection from its initial state is a run of the byte-stream
service.** -/
theorem tsteps_svc {issA issB : SeqNum} {s : Sys} {l : List SvcEv}
    (h : TSteps (Sys.init issA issB) l s) : SvcSteps {} l s.svc := by
  have := (tsteps_sim (Inv.init issA issB) h).2
  exact this

/-- **Safety of the stream**: what `B` delivered is a prefix of what `A`'s user wrote, and end
of stream means `A` closed and everything was delivered. -/
theorem stream_safe {issA issB : SeqNum} {s : Sys} {l : List SvcEv}
    (h : TSteps (Sys.init issA issB) l s) :
    s.b.delivered <+: s.a.buf ∧ (s.b.eof = true → s.a.closed = true ∧ s.b.delivered = s.a.buf) :=
  have hi := (tsteps_sim (Inv.init issA issB) h).1
  ⟨hi.pre, hi.eof⟩

/-! ## Agreement with Figure 5 -/

/-- A state stays, or moves along an arrow of Figure 5. -/
def Fig5 (st st' : State) : Prop := st' = st ∨ ∃ e x, Step st e x st'

theorem fig5_arrow {st st' : State} {e : Event} {x : Action} (h : next st e = some (x, st')) :
    Fig5 st st' := Or.inr ⟨e, x, .arrow h⟩

/-- **Every transition moves each endpoint along Figure 5.** -/
theorem tstep_fig5 {s s' : Sys} {l : List SvcEv} (h : TStep s l s') :
    Fig5 s.a.st s'.a.st ∧ Fig5 s.b.st s'.b.st := by
  cases h with
  | aOpen hst => exact ⟨fig5_arrow (e := .activeOpen) (by rw [hst]; rfl), Or.inl rfl⟩
  | aSynAck hst _ _ _ _ => exact ⟨fig5_arrow (e := .rcvSynAck) (by rw [hst]; rfl), Or.inl rfl⟩
  | aClose hst _ => exact ⟨fig5_arrow (e := .close) (by rw [hst]; rfl), Or.inl rfl⟩
  | aAckOfFin hst _ _ _ _ => exact ⟨fig5_arrow (e := .rcvAckOfFin) (by rw [hst]; rfl), Or.inl rfl⟩
  | aFin hst _ _ _ =>
    refine ⟨?_, Or.inl rfl⟩
    rcases hst with hst | ⟨hst, _⟩
    · exact fig5_arrow (e := .rcvFin) (by rw [hst]; rfl)
    · exact fig5_arrow (e := .rcvFinAckOfFin) (by rw [hst]; rfl)
  | aTimeout hst => exact ⟨fig5_arrow (e := .timeout2Msl) (by rw [hst]; rfl), Or.inl rfl⟩
  | bSyn hst _ _ => exact ⟨Or.inl rfl, fig5_arrow (e := .rcvSyn) (by rw [hst]; rfl)⟩
  | bAck hst _ _ _ _ => exact ⟨Or.inl rfl, fig5_arrow (e := .rcvAckOfSyn) (by rw [hst]; rfl)⟩
  | @bData g hst _ _ _ _ =>
    refine ⟨Or.inl rfl, ?_⟩
    cases g.fin
    · exact Or.inl (by simp [hst])
    · exact fig5_arrow (e := .rcvFin) (by simp [hst]; rfl)
  | bClose hst => exact ⟨Or.inl rfl, fig5_arrow (e := .close) (by rw [hst]; rfl)⟩
  | bAckOfFin hst _ _ _ _ => exact ⟨Or.inl rfl, fig5_arrow (e := .rcvAckOfFin) (by rw [hst]; rfl)⟩
  | aResendSyn _ | aWrite _ _ _ | aSend _ _ _ _ | aResendFin _ | bResendSynAck _ | bSendAck _
  | bResendFin _ => exact ⟨Or.inl rfl, Or.inl rfl⟩

/-! ## Reachability -/

theorem TSteps.single {s s' : Sys} {l : List SvcEv} (h : TStep s l s') : TSteps s l s' := by
  simpa using TSteps.cons h (.refl _)

theorem TSteps.trans {s s' s'' : Sys} {l m : List SvcEv} (h1 : TSteps s l s')
    (h2 : TSteps s' m s'') : TSteps s (l ++ m) s'' := by
  induction h1 with
  | refl => exact h2
  | cons h _ ih => simpa [List.append_assoc] using TSteps.cons h (ih h2)

/-- **The three-way handshake**: from the initial state, both ends reach ESTABLISHED. -/
theorem handshake (issA issB : SeqNum) :
    ∃ s, TSteps (Sys.init issA issB) [] s ∧ s.a.st = .established ∧ s.b.st = .established := by
  let s0 := Sys.init issA issB
  have h1 : TStep s0 [] { s0 with a := { s0.a with st := .synSent }, ab := s0.a.synSeg :: s0.ab } :=
    .aOpen rfl
  let s1 : Sys := { s0 with a := { s0.a with st := .synSent }, ab := s0.a.synSeg :: s0.ab }
  let g1 := s1.a.synSeg
  have h2 := TStep.bSyn (s := s1) (g := g1) rfl List.mem_cons_self rfl
  let s2 : Sys := { s1 with
    b := { s1.b with st := .synRcvd true, nxt := adv g1.seq 1 }
    ba := ({ s1.b with nxt := adv g1.seq 1 } : Rcv).synAckSeg :: s1.ba }
  let g2 := ({ s1.b with nxt := adv g1.seq 1 } : Rcv).synAckSeg
  have h3 := TStep.aSynAck (s := s2) (g := g2) rfl List.mem_cons_self rfl rfl rfl
  let s3 : Sys := { s2 with
    a := { s2.a with st := .established, rnxt := adv g2.seq 1 }
    ab := ({ s2.a with rnxt := adv g2.seq 1 } : Snd).ackSeg :: s2.ab }
  let g3 := ({ s2.a with rnxt := adv g2.seq 1 } : Snd).ackSeg
  have h4 := TStep.bAck (s := s3) (g := g3) rfl List.mem_cons_self rfl rfl rfl
  refine ⟨_, TSteps.cons h1 (TSteps.cons h2 (TSteps.cons h3 (TSteps.single h4))), rfl, rfl⟩

/-- **The whole stream can be delivered**: from an invariant state where `A` is connected and
`B` is ESTABLISHED, one retransmission and one receipt deliver everything written. -/
theorem can_deliver {s : Sys} (hi : Inv s) (ha : s.a.st = .established ∨ s.a.st = .finWait1)
    (hb : s.b.st = .established) :
    ∃ s' l, TSteps s l s' ∧ s'.b.delivered = s.a.buf ∧ s'.a = s.a := by
  by_cases hd : s.b.delivered = s.a.buf
  · exact ⟨s, [], .refl _, hd, rfl⟩
  · show ∃ s' l, TSteps s l s' ∧ s'.b.delivered = s.a.buf ∧ s'.a = s.a
    have hdl : s.b.delivered.length ≤ s.a.buf.length := hi.pre.length_le
    have hlt : s.b.delivered.length < s.a.buf.length := by
      rcases Nat.lt_or_eq_of_le hdl with h | h
      · exact h
      · exact absurd (List.IsPrefix.eq_of_length hi.pre h) hd
    let d := s.b.delivered.length
    let n := s.a.buf.length - d
    have h1 : TStep s [] { s with ab := s.a.dataSeg d n :: s.ab } := .aSend d n ha (by omega)
    let s1 : Sys := { s with ab := s.a.dataSeg d n :: s.ab }
    have heof : s.b.eof = false := hi.early (Or.inr (Or.inr hb))
    have hn : s.b.nxt = adv s.a.iss (1 + d) := by
      have h := hi.nxt (by rw [hb]; decide)
      simpa [heof] using h
    let g := s.a.dataSeg d n
    have hne : g.data ≠ [] := by
      simp only [g, Snd.dataSeg, ne_eq, List.take_eq_nil_iff, List.drop_eq_nil_iff]
      omega
    have h2 := TStep.bData (s := s1) (g := g) hb List.mem_cons_self rfl hn.symm (Or.inl hne)
    refine ⟨_, _, TSteps.cons h1 (TSteps.single h2), ?_, rfl⟩
    show s.b.delivered ++ (s.a.buf.drop d).take n = s.a.buf
    have hdel : s.b.delivered = s.a.buf.take d := List.prefix_iff_eq_take.mp hi.pre
    rw [List.take_of_length_le (by simp only [List.length_drop]; omega), hdel,
      List.take_append_drop]

/-! ## Without the bound, stale data is accepted -/

/-- The stream of the counterexample: `1`, then `N + 1` zeros. -/
def wrapBuf (N : Nat) : List UInt8 := 1 :: (List.replicate N 0 ++ [0])

/-- What `B` delivered in the counterexample: all but the last octet. -/
def wrapDelivered (N : Nat) : List UInt8 := 1 :: List.replicate N 0

/-- `A` in the counterexample. -/
def wrapSnd (N : Nat) (issA : SeqNum) : Snd :=
  { st := .established, iss := issA, buf := wrapBuf N, closed := false, rnxt := 0 }

/-- The state of the counterexample: `B` has delivered `N + 1` octets; the network still holds
`A`'s first data segment (offset 0, the octet `1`). With `N + 1 = 2^32` its sequence number has
come round to RCV.NXT. -/
def wrapSys (N : Nat) (issA issB : SeqNum) : Sys :=
  ⟨wrapSnd N issA,
   { st := .established, iss := issB, nxt := adv issA 1, delivered := wrapDelivered N, eof := false },
   [(wrapSnd N issA).dataSeg 0 1], []⟩

theorem wrap_lengths (N : Nat) :
    (wrapDelivered N).length = N + 1 ∧ (wrapBuf N).length = N + 2 :=
  ⟨by simp [wrapDelivered], by simp [wrapBuf]⟩

theorem wrap_data (N : Nat) : ((wrapBuf N).drop 0).take 1 = [1] := by
  simp [wrapBuf]

/-- The counterexample for any `N` with `N + 1 ≡ 0 (mod 2^32)`. -/
theorem wrap_unsafe_gen (N : Nat) (hw : (N + 1) % 4294967296 = 0) (issA issB : SeqNum)
    (s : Sys) (hs : s = wrapSys N issA issB) :
    (∀ g ∈ s.ab, Good s.a g) ∧ s.b.delivered <+: s.a.buf ∧ s.b.st = .established ∧
      s.b.eof = false ∧ s.b.nxt = adv s.a.iss (1 + s.b.delivered.length) ∧
      ∃ l s', TStep s l s' ∧ ¬ s'.b.delivered <+: s'.a.buf := by
  subst hs
  obtain ⟨hdl, hbl⟩ := wrap_lengths N
  have hdata : ((wrapBuf N).drop 0).take 1 = [1] := wrap_data N
  have hg : Good (wrapSnd N issA) ((wrapSnd N issA).dataSeg 0 1) :=
    good_data (wrapSnd N issA) (by show 0 + 1 ≤ (wrapBuf N).length; omega)
  have hnxt : adv issA 1 = adv issA (1 + (wrapDelivered N).length) := by
    apply eq_of_toNat
    rw [adv_toNat, adv_toNat, hdl]
    omega
  have hpre : wrapDelivered N <+: wrapBuf N :=
    List.cons_prefix_cons.mpr ⟨rfl, List.prefix_append _ _⟩
  have hne : ((wrapSnd N issA).dataSeg 0 1).data ≠ [] := by
    show ((wrapBuf N).drop 0).take 1 ≠ []
    rw [hdata]; exact List.cons_ne_nil _ _
  have hstep := TStep.bData (s := wrapSys N issA issB) (g := (wrapSnd N issA).dataSeg 0 1)
    rfl List.mem_cons_self rfl rfl (Or.inl hne)
  refine ⟨fun g hm => ?_, hpre, rfl, rfl, hnxt, _, _, hstep, ?_⟩
  · rw [List.mem_singleton.mp hm]; exact hg
  · show ¬ wrapDelivered N ++ ((wrapBuf N).drop 0).take 1 <+: wrapBuf N
    rw [hdata]
    intro hp
    have hlen : (wrapDelivered N ++ [1]).length = (wrapBuf N).length := by
      rw [List.length_append, hdl, hbl, List.length_singleton]
    have heq : wrapDelivered N ++ [1] = wrapDelivered N ++ [0] := hp.eq_of_length hlen
    have h10 : ([1] : List UInt8) = [0] := List.append_cancel_left heq
    exact absurd h10 (by decide)

/-- **The sequence-space bound is necessary** (refutation of safety without `writeOk`): there is
a state satisfying every part of `Inv` except the bound (the stream is `2^32 + 1` octets long)
in which `B` accepts a stale segment whose sequence number has wrapped round to RCV.NXT and
delivers octets that are not a prefix of the stream. This is the hazard that the segment
lifetime bound and quiet time of RFC 9293 §3.4.2-§3.4.3 rule out in real TCP. -/
theorem wrap_unsafe (issA issB : SeqNum) :
    (∀ g ∈ (wrapSys 4294967295 issA issB).ab, Good (wrapSys 4294967295 issA issB).a g) ∧
      (wrapSys 4294967295 issA issB).b.delivered <+: (wrapSys 4294967295 issA issB).a.buf ∧
      ∃ l s', TStep (wrapSys 4294967295 issA issB) l s' ∧ ¬ s'.b.delivered <+: s'.a.buf := by
  obtain ⟨h1, h2, -, -, -, h6⟩ := wrap_unsafe_gen 4294967295 rfl issA issB _ rfl
  exact ⟨h1, h2, h6⟩

end Silmaril.Net.Tcp
