module

public import Silmaril.Proofs.Formats.Compression.Inflate
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberSpec
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawRuns
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.TokenContinuation
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.ParserPhases
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Fuel
public import Silmaril.Raw.Formats.Compression.Inflate.Manual.Symbols

/-!
Proofs of the completeness directions of `Silmaril.Formats.Compression.Inflate.Thms`:
the streaming raw and member machines finish every member the list decoders
accept, with calls that offer no further input.

Each call is one machine step with a scheduler budget and output capacity chosen
large enough for that step. On reachable ("canonical") states whose denotation
succeeds, one such step strictly decreases `4 * unread bits + rank`, where the
rank orders the phases that consume no bits. The existing step laws carry the
denotation (and thus success) across every step.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.InflateComplete

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Inflate
open Silmaril.Formats.Compression.Inflate.Stream

/-! ## Reservoir reads that the canonical reader can perform -/

theorem normalizes_bitsLeft {s : Reservoir} {r : LSBReader} (h : Reservoir.Normalizes s r) :
    r.bitsLeft = s.unread.length := by
  obtain ⟨_, _, ⟨_, hrep⟩, _⟩ := h
  rw [← hrep]
  simp only [LSBReader.bitsLeft, List.length_append, length_natBits, length_bytesBits]

theorem readBits_value {s : Reservoir} {r r' : LSBReader} {n v : Nat}
    (hn : Reservoir.Normalizes s r) (hr : r.readBits n = some (v, r')) :
    ∃ t, Reservoir.readBits n s = .value v t ∧ Reservoir.Normalizes t r' := by
  cases hs : Reservoir.readBits n s with
  | value v' t =>
    obtain ⟨r'', hread, ht⟩ := hn.readBits hs
    rw [hr] at hread
    simp only [Option.some.injEq, Prod.mk.injEq] at hread
    obtain ⟨rfl, rfl⟩ := hread
    exact ⟨t, rfl, ht⟩
  | needInput t =>
    exfalso
    have sound := Reservoir.readBits_sound n hn.1
    rw [hs] at sound
    obtain ⟨_, hu, _, _, hin, hlt⟩ := sound
    have h1 := normalizes_bitsLeft hn
    have h2 := Deflate.readBits_bitsLeft hr
    have h3 : t.unread.length = t.bits := by
      simp [Reservoir.unread, hin, bytesBits, length_natBits]
    rw [← hu, h3] at h1
    omega

/-- A parse that succeeds on the canonical reader completes in the reservoir
interpreter with some scheduler budget. -/
theorem run_done_of_eval {α : Type} (p : Parser α) :
    ∀ {s : Reservoir} {r r' : LSBReader} {v : α}, Reservoir.Normalizes s r →
      p.eval r = .ok (v, r') →
      ∃ F s', Parser.run F p s = .done v s' ∧ Reservoir.Normalizes s' r' := by
  induction p with
  | pure a =>
    intro s r r' v hn h
    simp only [Parser.eval, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨1, s, rfl, hn⟩
  | fail e => intro _ _ _ _ _ h; cases h
  | bits count err next ih =>
    intro s r r' v hn h
    simp only [Parser.eval] at h
    cases hr : r.readBits count with
    | none => rw [hr] at h; cases h
    | some pair =>
      obtain ⟨n, rm⟩ := pair
      rw [hr] at h
      obtain ⟨t, hs, ht⟩ := readBits_value hn hr
      obtain ⟨F, s', hrun, hn'⟩ := ih n ht h
      exact ⟨F + 1, s', by simp only [Parser.run, hs, hrun], hn'⟩
  | align next ih =>
    intro s r r' v hn h
    obtain ⟨F, s', hrun, hn'⟩ := ih hn.byteBits h
    exact ⟨F + 1, s', by simp only [Parser.run, hrun], hn'⟩

theorem header_eval_bitsLeft {r r' : LSBReader} {v : Bool × Nat}
    (h : Blocks.header.eval r = .ok (v, r')) : r'.bitsLeft + 3 = r.bitsLeft := by
  simp only [Blocks.header, Parser.eval] at h
  cases h1 : r.readBits 1 with
  | none => rw [h1] at h; cases h
  | some p1 =>
    obtain ⟨a, r1⟩ := p1
    rw [h1] at h
    dsimp only at h
    cases h2 : r1.readBits 2 with
    | none => rw [h2] at h; cases h
    | some p2 =>
      obtain ⟨b, r2⟩ := p2
      rw [h2] at h
      dsimp only at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      have := Deflate.readBits_bitsLeft h1
      have := Deflate.readBits_bitsLeft h2
      omega

/-! ## The raw machine: canonical states and the progress measure -/

/-- A raw machine that has finished, successfully or not. -/
def RawTerminal : RawMachine → Prop
  | .done _ | .bad _ _ => True
  | _ => False

/-- Phases that consume no bits are ordered by rank. -/
def rawRank : RawMachine → Nat
  | .header _ _ => 1
  | .storedCopy _ _ _ | .symbols _ _ _ _ => 2
  | .storedHeader _ _ _ | .dynamicTables _ _ _ => 3
  | .done _ | .bad _ _ => 0

/-- The progress measure: zero once finished. -/
def rawMeasure (m : RawMachine) : Nat :=
  match m with
  | .done _ | .bad _ _ => 0
  | _ => 4 * m.reservoir.unread.length + rawRank m

/-- States reachable with adequate budgets: block headers and tokens are parsed
from their beginning. -/
inductive RawCanon : RawMachine → Prop
  | header (st : RawState) : RawCanon (.header Blocks.header st)
  | storedHeader (last : Bool) (p : Parser Nat) (st : RawState) : RawCanon (.storedHeader last p st)
  | storedCopy (last : Bool) (n : Nat) (st : RawState) : RawCanon (.storedCopy last n st)
  | dynamicTables (last : Bool) (p : Parser (HuffmanTable × HuffmanTable)) (st : RawState) :
      RawCanon (.dynamicTables last p st)
  | symbols (last : Bool) (litLen dist : HuffmanTable) (s : Reservoir) (w : Window)
      (o : List UInt8) : RawCanon (.symbols last litLen dist (TokenMachine.start litLen dist s w o))
  | done (st : RawState) : RawCanon (.done st)
  | bad (e : Deflate.DecompressError) (st : RawState) : RawCanon (.bad e st)

theorem rawMeasure_le (m : RawMachine) : rawMeasure m ≤ 4 * m.reservoir.unread.length + 3 := by
  cases m <;> simp only [rawMeasure, rawRank] <;> omega

theorem canon_fixed (last : Bool) (state : RawState) : RawCanon (RawMachine.fixed last state) := by
  unfold RawMachine.fixed
  generalize Deflate.fixedLitLenTable = a
  generalize Deflate.fixedDistTable = b
  cases a <;> cases b <;> first | exact .bad _ _ | exact .symbols _ _ _ _ _ _

theorem canon_dispatch131 (kind : Nat) (last : Bool) (state : RawState) :
    RawCanon (RawMachine.dispatch131 kind last state) := by
  have hfixed := canon_fixed last state
  unfold RawMachine.dispatch131
  generalize RawMachine.fixed last state = fx at hfixed ⊢
  by_cases h0 : kind = 0
  · simp only [h0, ↓reduceIte]; exact .storedHeader _ _ _
  by_cases h1 : kind = 1
  · subst h1
    simpa only [Nat.one_ne_zero, ↓reduceIte] using hfixed
  by_cases h2 : kind = 2
  · subst h2
    simp only [Nat.succ_ne_zero, Nat.reduceEqDiff, ↓reduceIte]; exact .dynamicTables _ _ _
  · simp only [h0, h1, h2, ↓reduceIte]; exact .bad _ _

theorem canon_dispatch (version : Version) (kind : Nat) (last : Bool) (state : RawState) :
    RawCanon (RawMachine.dispatch version kind last state) := by
  cases version
  · exact canon_dispatch131 kind last state
  · rw [RawMachine.dispatch, ← RawMachine.dispatch131_eq_dispatchDevelop]
    exact canon_dispatch131 kind last state

theorem afterDecodedBlock_ok {last : Bool} {x : RawSemantics.Result} {y : List UInt8 × LSBReader}
    (h : RawSemantics.afterDecodedBlock last x = .ok y) : ∃ v, x = .ok v := by
  cases x with
  | error e => cases h
  | ok v => exact ⟨v, rfl⟩

theorem afterToken_ok {last : Bool} {litLen dist : HuffmanTable}
    {x : Except Deflate.DecompressError Deflate.SymbolStep} {y : List UInt8 × LSBReader}
    (h : RawSemantics.afterToken last litLen dist x = .ok y) : ∃ v, x = .ok v := by
  cases x with
  | error e => cases h
  | ok v => exact ⟨v, rfl⟩

/-- **Progress.** A running canonical raw machine whose denotation succeeds
takes, with some budget and capacity, one step to a canonical machine of
strictly smaller measure. -/
theorem raw_progress (version : Version) (m : RawMachine) (r : LSBReader)
    (hc : RawCanon m) (hn : Reservoir.Normalizes m.reservoir r)
    (hwf : RawSemantics.WellFormed m r) {res : List UInt8 × LSBReader}
    (hd : RawSemantics.denote m r = .ok res) (ht : ¬ RawTerminal m) :
    ∃ F C, RawCanon (RawMachine.step version m F C) ∧
      rawMeasure (RawMachine.step version m F C) < rawMeasure m := by
  have hU := normalizes_bitsLeft hn
  cases hc with
  | header st =>
    simp only [RawSemantics.denote] at hd
    split at hd
    · cases hd
    next last kind r1 he =>
    change Reservoir.Normalizes st.reservoir r at hn
    change r.bitsLeft = st.reservoir.unread.length at hU
    obtain ⟨F, s', hrun, hn'⟩ := run_done_of_eval _ hn he
    have hb := header_eval_bitsLeft he
    have hU' := normalizes_bitsLeft hn'
    have hstep : RawMachine.step version (.header Blocks.header st) F 0 =
        RawMachine.dispatch version kind last { st with reservoir := s' } := by
      simp only [RawMachine.step, hrun]
    refine ⟨F, 0, ?_, ?_⟩ <;> rw [hstep]
    · exact canon_dispatch _ _ _ _
    · have hle := rawMeasure_le (RawMachine.dispatch version kind last { st with reservoir := s' })
      rw [RawMachine.dispatch_reservoir] at hle
      change _ ≤ 4 * s'.unread.length + 3 at hle
      change _ < 4 * st.reservoir.unread.length + 1
      omega
  | storedHeader last p st =>
    simp only [RawSemantics.denote] at hd
    split at hd
    · cases hd
    next n r1 he =>
    change Reservoir.Normalizes st.reservoir r at hn
    change r.bitsLeft = st.reservoir.unread.length at hU
    obtain ⟨F, s', hrun, hn'⟩ := run_done_of_eval _ hn he
    have hb := Parser.eval_bitsLeft_le p he
    have hU' := normalizes_bitsLeft hn'
    have hstep : RawMachine.step version (.storedHeader last p st) F 0 =
        .storedCopy last n { st with reservoir := s' } := by
      simp only [RawMachine.step, hrun]
    refine ⟨F, 0, ?_, ?_⟩ <;> rw [hstep]
    · exact .storedCopy _ _ _
    · change 4 * s'.unread.length + 2 < 4 * st.reservoir.unread.length + 3
      omega
  | storedCopy last n st =>
    cases n with
    | zero =>
      refine ⟨0, 0, ?_, ?_⟩
      · cases last
        · simp only [RawMachine.step, RawMachine.finishBlock, Bool.false_eq_true, ↓reduceIte]
          exact .header _
        · simp only [RawMachine.step, RawMachine.finishBlock, ↓reduceIte]
          exact .done _
      · cases last
        · simp only [RawMachine.step, RawMachine.finishBlock, rawMeasure, rawRank,
            Bool.false_eq_true, ↓reduceIte]
          change 4 * st.reservoir.unread.length + 1 < 4 * st.reservoir.unread.length + 2
          omega
        · simp only [RawMachine.step, RawMachine.finishBlock, rawMeasure, rawRank, ↓reduceIte]
          omega
    | succ n =>
      change Reservoir.Normalizes st.reservoir r at hn
      change r.bitsLeft = st.reservoir.unread.length at hU
      simp only [RawSemantics.denote] at hd
      obtain ⟨v, hv⟩ := afterDecodedBlock_ok hd
      simp only [Deflate.readStoredBytes] at hv
      cases hb : r.readByte with
      | none => rw [hb] at hv; cases hv
      | some pb =>
        obtain ⟨b, r2⟩ := pb
        cases h8 : r.readBits 8 with
        | none => simp [LSBReader.readByte, h8] at hb
        | some p8 =>
          obtain ⟨v8, r8⟩ := p8
          obtain ⟨t, hs, ht'⟩ := readBits_value hn h8
          have hb8 := Deflate.readBits_bitsLeft h8
          have hUt := normalizes_bitsLeft ht'
          have hstep : RawMachine.step version (.storedCopy last (n + 1) st) 0 1 =
              .storedCopy last n (st.emitByte t (UInt8.ofNat v8)) := by
            simp only [RawMachine.step, hs, Nat.one_ne_zero, ↓reduceIte]
          refine ⟨0, 1, ?_, ?_⟩ <;> rw [hstep]
          · exact .storedCopy _ _ _
          · change 4 * t.unread.length + 2 < 4 * st.reservoir.unread.length + 2
            omega
  | dynamicTables last p st =>
    simp only [RawSemantics.denote] at hd
    split at hd
    · cases hd
    next lt dt r1 he =>
    change Reservoir.Normalizes st.reservoir r at hn
    change r.bitsLeft = st.reservoir.unread.length at hU
    obtain ⟨F, s', hrun, hn'⟩ := run_done_of_eval _ hn he
    have hb := Parser.eval_bitsLeft_le p he
    have hU' := normalizes_bitsLeft hn'
    have hstep : RawMachine.step version (.dynamicTables last p st) F 0 =
        .symbols last lt dt (TokenMachine.start lt dt s' st.window st.output) := by
      simp only [RawMachine.step, hrun]
    refine ⟨F, 0, ?_, ?_⟩ <;> rw [hstep]
    · exact .symbols _ _ _ _ _ _
    · change 4 * s'.unread.length + 2 < 4 * st.reservoir.unread.length + 3
      omega
  | symbols last lt dt s w o =>
    change r.bitsLeft = s.unread.length at hU
    change Reservoir.Normalizes s r at hn
    obtain ⟨_, hrep, hadm⟩ := hwf
    simp only [RawSemantics.denote] at hd
    obtain ⟨stp, hstp⟩ := afterToken_ok hd
    simp only [TokenContinuation.denote, TokenMachine.start] at hstp
    split at hstp
    · cases hstp
    next tok r1 he =>
    obtain ⟨F, s', hrun, hn'⟩ := run_done_of_eval _ hn he
    have hb := Parser.eval_bitsLeft_le _ he
    have hU' := normalizes_bitsLeft hn'
    have hstep : RawMachine.step version
        (.symbols last lt dt (TokenMachine.start lt dt s w o)) F
          (TokenOutput.start w o tok).remaining =
        RawMachine.acceptToken last lt dt
          (TokenMachine.emit s' (TokenOutput.start w o tok) (TokenOutput.start w o tok).remaining) := by
      simp only [RawMachine.step, TokenMachine.start, TokenMachine.step, hrun]
    by_cases hfits : TokenFitsHistory o tok
    · have hvalid := TokenOutput.start_valid w o tok hrep hfits
      have hden := TokenContinuation.outputDenote_start w o tok r1 hrep hfits
      rw [TokenContinuation.outputDenote_valid _ _ hvalid, hstp] at hden
      generalize hQ : (TokenOutput.start w o tok).advance (TokenOutput.start w o tok).remaining = Q
        at hden
      have hemit : TokenMachine.emit s' (TokenOutput.start w o tok)
          (TokenOutput.start w o tok).remaining = TokenMachine.finish s' Q := by
        rw [TokenMachine.emit_eq _ _ _ hvalid, hQ]
      refine ⟨F, (TokenOutput.start w o tok).remaining, ?_⟩
      rw [hstep, hemit]
      cases hph : Q.phase with
      | literal _ | matchBytes _ _ | endBlock =>
        simp only [TokenOutput.observe, hph] at hden; cases hden
      | complete flag =>
        simp only [TokenMachine.finish, hph, RawMachine.acceptToken]
        cases flag with
        | true =>
          cases last
          · simp only [RawMachine.finishBlock, Bool.false_eq_true, ↓reduceIte,
              rawMeasure, rawRank]
            refine ⟨.header _, ?_⟩
            change 4 * s'.unread.length + 1 < 4 * s.unread.length + 2
            omega
          · simp only [RawMachine.finishBlock, ↓reduceIte, rawMeasure]
            refine ⟨.done _, ?_⟩
            change 0 < 4 * s.unread.length + 2
            omega
        | false =>
          simp only [TokenOutput.observe, hph] at hden
          -- the token was not the end of the block, so it consumed at least one bit
          have hdec : Manual.decodeStep lt dt r o = .ok (.more Q.output r1) := by
            rw [Manual.decodeStep, ← ParserPhases.token_eval, he]
            exact hstp.trans hden.symm
          rw [Manual.decodeStep_eq_spec] at hdec
          have hlt := Deflate.decodeStep_more_bitsLeft_lt hdec
          refine ⟨.symbols _ _ _ _ _ _, ?_⟩
          simp only [rawMeasure, rawRank]
          change 4 * s'.unread.length + 2 < 4 * s.unread.length + 2
          omega
    · exfalso
      have hadmTok := hadm [] tok r1 (by simpa only [Reservoir.readerFeed_nil] using he)
      cases tok with
      | literal _ | endBlock => exact hfits trivial
      | matchBytes len dist =>
        simp only [Manual.applyToken] at hstp
        split at hstp
        · cases hstp
        next hle =>
        exact hfits ⟨hadmTok.2.2.1, hadmTok.2.2.2, by omega⟩
  | done st => exact absurd trivial ht
  | bad e st => exact absurd trivial ht

/-! ## Driving the raw machine to completion -/

theorem tokenMachine_feed_nil (m : TokenMachine) : m.feed [] = m := by
  cases m <;> simp only [TokenMachine.feed, Reservoir.feed, List.append_nil]

theorem rawMachine_feed_nil (m : RawMachine) : m.feed [] = m := by
  cases m <;> simp only [RawMachine.feed, RawState.feed, Reservoir.feed, List.append_nil,
    tokenMachine_feed_nil]

/-- The raw invariant: canonical, and denoting the fixed successful result `T`. -/
def RawInv (T : RawSemantics.Result) (m : RawMachine) : Prop :=
  RawCanon m ∧ ∃ r, Reservoir.Normalizes m.reservoir r ∧ RawSemantics.WellFormed m r ∧
    RawSemantics.denote m r = T

/-- One adequate step preserves the invariant (through the raw step law) and
decreases the measure. -/
theorem raw_step (version : Version) {T : RawSemantics.Result} {res : List UInt8 × LSBReader}
    (hT : T = .ok res) (m : RawMachine) (hinv : RawInv T m) (ht : ¬ RawTerminal m) :
    ∃ call : RawMachine.Call, call.input = [] ∧
      RawInv T (RawMachine.applyCall version m call) ∧
      rawMeasure (RawMachine.applyCall version m call) < rawMeasure m := by
  obtain ⟨hc, r, hn, hwf, hd⟩ := hinv
  obtain ⟨F, C, hc', hlt⟩ := raw_progress version m r hc hn hwf (hd.trans hT) ht
  obtain ⟨rest, hn', hwf', hden⟩ := RawStep.step_correct_feed version m r F C hn hwf
  have hden0 := hden []
  simp only [Reservoir.readerFeed_nil] at hden0
  refine ⟨⟨[], F, C⟩, rfl, ?_, ?_⟩ <;>
    simp only [RawMachine.applyCall, rawMachine_feed_nil]
  · exact ⟨hc', rest, hn', hwf', hden0.symm.trans hd⟩
  · exact hlt

theorem raw_drive (version : Version) {T : RawSemantics.Result} {res : List UInt8 × LSBReader}
    (hT : T = .ok res) : ∀ (n : Nat) (m : RawMachine), rawMeasure m = n → RawInv T m →
      ∃ calls : List RawMachine.Call, RawRuns.deliveredInput calls = [] ∧
        RawInv T (RawMachine.runCalls version m calls) ∧
        RawTerminal (RawMachine.runCalls version m calls) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm hinv
    by_cases ht : RawTerminal m
    · exact ⟨[], rfl, hinv, ht⟩
    · obtain ⟨call, hcall, hinv', hlt⟩ := raw_step version hT m hinv ht
      obtain ⟨calls, hdel, hinv'', ht''⟩ := ih _ (hm ▸ hlt) _ rfl hinv'
      refine ⟨call :: calls, ?_, hinv'', ht''⟩
      simp only [RawRuns.deliveredInput, List.flatMap_cons, hcall, List.nil_append]
      exact hdel

theorem raw_complete (version : Version) : (raw version).Complete Deflate.decoder := by
  intro bytes out rest h
  have htake : Deflate.deflateTake bytes = .ok (out, rest) := Deflate.decoder_eq_some.mp h
  rw [← RawRuns.format_inputView] at htake
  obtain ⟨rf, hf⟩ : ∃ rf, RawSemantics.format (Blocks.initialReader bytes) [] = .ok (out, rf) := by
    cases hfm : RawSemantics.format (Blocks.initialReader bytes) [] with
    | error e => rw [hfm] at htake; cases htake
    | ok p =>
      obtain ⟨o, rf⟩ := p
      rw [hfm] at htake
      simp only [Blocks.inputView, Except.map, Except.ok.injEq, Prod.mk.injEq] at htake
      exact ⟨rf, by rw [htake.1]⟩
  have hinv : RawInv (.ok (out, rf)) (RawMachine.start bytes) := by
    refine ⟨.header _, Blocks.initialReader bytes, RawRuns.start_normalizes bytes,
      RawRuns.start_wellFormed bytes _, ?_⟩
    have := RawRuns.start_denote bytes []
    simp only [Reservoir.readerFeed_nil, List.append_nil] at this
    rw [this, hf]
  obtain ⟨calls, hdel, hinv', hterm⟩ := raw_drive version rfl _ _ rfl hinv
  refine ⟨calls, hdel, ?_⟩
  change rawStatus (RawMachine.runCalls version (RawMachine.start bytes) calls) = .done out
  generalize RawMachine.runCalls version (RawMachine.start bytes) calls = m at hinv' hterm
  obtain ⟨_, r, _, _, hd⟩ := hinv'
  cases m with
  | done st =>
    simp only [RawSemantics.denote, Except.ok.injEq, Prod.mk.injEq] at hd
    simp only [rawStatus, hd.1]
  | bad e st => cases hd
  | _ => exact absurd hterm id

/-! ## The member machine -/

/-- A member machine that has finished, successfully or not. -/
def MemberTerminal : MemberMachine → Prop
  | .done _ | .bad _ _ => True
  | _ => False

/-- Header, then the raw body (measured by `rawMeasure`), then the trailer. -/
def memberMeasure : MemberMachine → Nat
  | .header _ _ reservoir => 4 * reservoir.unread.length + 4
  | .gzipHeader g => 4 * g.reservoir.unread.length + 5
  | .body _ checked => rawMeasure checked.machine + 2
  | .trailer _ _ => 1
  | .done _ | .bad _ _ => 0

/-- Reachable member states. -/
inductive MemberCanon : MemberMachine → Prop
  | header (kind : MemberSemantics.Kind) (p : Parser (Option Unit)) (s : Reservoir) :
      MemberCanon (.header kind p s)
  | gzipHeader (g : GzipHeader.Machine) : MemberCanon (.gzipHeader g)
  | body (kind : MemberSemantics.Kind) (checked : CheckedRaw.State) :
      RawCanon checked.machine → MemberCanon (.body kind checked)
  | trailer (p : Parser (Option Unit)) (st : RawState) : MemberCanon (.trailer p st)
  | done (st : RawState) : MemberCanon (.done st)
  | bad (e : MemberError) (st : RawState) : MemberCanon (.bad e st)

theorem readBits_progress (n : Nat) {s : Reservoir} (hs : s.Valid) (h : n ≤ s.unread.length) :
    ∃ v t, Reservoir.readBits n s = .value v t ∧ t.unread.length + n = s.unread.length := by
  have sound := Reservoir.readBits_sound n hs
  cases hr : Reservoir.readBits n s with
  | value v t =>
    rw [hr] at sound
    obtain ⟨_, _, hu, _, _⟩ := sound
    refine ⟨v, t, rfl, ?_⟩
    rw [hu, List.length_append, length_natBits]
    omega
  | needInput t =>
    rw [hr] at sound
    obtain ⟨_, hu, _, _, hin, hlt⟩ := sound
    exfalso
    have h3 : t.unread.length = t.bits := by
      simp [Reservoir.unread, hin, bytesBits, length_natBits]
    rw [← hu, h3] at h
    omega

theorem validationReader_some {x : Except Deflate.DecompressError (Option Unit × LSBReader)}
    {r : LSBReader} (h : ContainerFields.validationReader x = some r) : x = .ok (some (), r) := by
  unfold ContainerFields.validationReader at h
  split at h
  · cases h; rfl
  · cases h
  · cases h

theorem member_progress (version : Version) (m : MemberMachine) (r : LSBReader)
    (hc : MemberCanon m) (hn : Reservoir.Normalizes m.reservoir r)
    (hwf : m.WellFormed r) {res : List UInt8 × LSBReader}
    (hd : m.denote r = some res) (ht : ¬ MemberTerminal m) :
    ∃ F C, MemberCanon (MemberMachine.step version m F C) ∧
      memberMeasure (MemberMachine.step version m F C) < memberMeasure m := by
  cases hc with
  | header kind p s =>
    change Reservoir.Normalizes s r at hn
    simp only [MemberMachine.denote] at hd
    cases hv : ContainerFields.validationReader (p.eval r) with
    | none => rw [hv] at hd; cases hd
    | some r1 =>
      have he := validationReader_some hv
      obtain ⟨F, s', hrun, hn'⟩ := run_done_of_eval _ hn he
      have hb := Parser.eval_bitsLeft_le p he
      have hU := normalizes_bitsLeft hn
      have hU' := normalizes_bitsLeft hn'
      refine ⟨F, 0, ?_, ?_⟩ <;> simp only [MemberMachine.step, hrun, MemberMachine.enterBody]
      · exact .body _ _ (.header _)
      · change 4 * s'.unread.length + 1 + 2 < 4 * s.unread.length + 4
        omega
  | gzipHeader g =>
    change Reservoir.Normalizes g.reservoir r at hn
    have hU := normalizes_bitsLeft hn
    simp only [MemberMachine.denote] at hd
    by_cases hdone : g.isDone = true
    · refine ⟨0, 0, ?_, ?_⟩ <;>
        simp only [MemberMachine.step, hdone, ↓reduceIte, MemberMachine.enterBody]
      · exact .body _ _ (.header _)
      · change 4 * g.reservoir.unread.length + 1 + 2 < 4 * g.reservoir.unread.length + 5
        omega
    by_cases hbad : g.isBad = true
    · refine ⟨0, 0, ?_, ?_⟩ <;>
        simp only [MemberMachine.step, hdone, hbad, Bool.false_eq_true, ↓reduceIte]
      · exact .bad _ _
      · simp only [memberMeasure]; omega
    have hactive : g.control.active = true := by
      simp only [GzipHeader.Machine.isDone, GzipHeader.Machine.isBad, beq_iff_eq] at hdone hbad
      simp only [GzipHeader.Control.active, Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨hdone, hbad⟩
    have hinput : r.input ≠ [] := by
      intro hnil
      cases hx : g.denoteReader r with
      | none => rw [hx] at hd; cases hd
      | some _ =>
        simp only [GzipHeader.Machine.denoteReader, GzipHeader.Machine.denote, hnil,
          GzipHeader.evaluate_nil] at hx
        simp only [GzipHeader.Machine.isDone, beq_iff_eq] at hdone
        simp [hdone] at hx
    have h8 : 8 ≤ g.reservoir.unread.length := by
      rw [← hU, LSBReader.bitsLeft]
      cases hi : r.input with
      | nil => exact absurd hi hinput
      | cons _ _ => simp only [List.length_cons]; omega
    obtain ⟨v, t, hs, ht'⟩ := readBits_progress 8 hn.1 h8
    refine ⟨0, 0, ?_, ?_⟩ <;>
      simp only [MemberMachine.step, hdone, hbad, Bool.false_eq_true, ↓reduceIte,
        GzipHeader.Machine.step, hactive, hs]
    · exact .gzipHeader _
    · change 4 * t.unread.length + 5 < 4 * g.reservoir.unread.length + 5
      omega
  | body kind checked hraw =>
    obtain ⟨hinv, hrwf⟩ := hwf
    simp only [MemberMachine.denote] at hd
    obtain ⟨v, hv⟩ : ∃ v, RawSemantics.denote checked.machine r = .ok v := by
      cases hx : RawSemantics.denote checked.machine r with
      | error e => rw [hx] at hd; cases hd
      | ok v => exact ⟨v, rfl⟩
    by_cases hterm : RawTerminal checked.machine
    · refine ⟨0, 0, ?_⟩
      cases hM : checked.machine with
      | done st =>
        simp only [MemberMachine.step, hM]
        exact ⟨.trailer _ _, by change 1 < rawMeasure checked.machine + 2; omega⟩
      | bad e st =>
        simp only [MemberMachine.step, hM]
        exact ⟨.bad _ _, by change 0 < rawMeasure checked.machine + 2; omega⟩
      | _ => rw [hM] at hterm; exact absurd hterm id
    · obtain ⟨F, C, hc', hlt⟩ := raw_progress version checked.machine r hraw hn hrwf hv hterm
      have hstep : MemberMachine.step version (.body kind checked) F C =
          .body kind (CheckedRaw.step kind.checksumKind version checked F C) := by
        cases hM : checked.machine with
        | done st => rw [hM] at hterm; exact absurd trivial hterm
        | bad e st => rw [hM] at hterm; exact absurd trivial hterm
        | _ => simp only [MemberMachine.step, hM]
      refine ⟨F, C, ?_, ?_⟩ <;> rw [hstep]
      · exact .body _ _ hc'
      · change rawMeasure (RawMachine.step version checked.machine F C) + 2 <
          rawMeasure checked.machine + 2
        omega
  | trailer p st =>
    change Reservoir.Normalizes st.reservoir r at hn
    simp only [MemberMachine.denote] at hd
    cases hv : ContainerFields.validationReader (p.eval r) with
    | none => rw [hv] at hd; cases hd
    | some r1 =>
      have he := validationReader_some hv
      obtain ⟨F, s', hrun, _⟩ := run_done_of_eval _ hn he
      refine ⟨F, 0, ?_, ?_⟩ <;> simp only [MemberMachine.step, hrun]
      · exact .done _
      · simp only [memberMeasure]; omega
  | done st => exact absurd trivial ht
  | bad e st => exact absurd trivial ht

theorem memberMachine_feed_nil (m : MemberMachine) (h : MemberCanon m) : m.feed [] = m := by
  cases h with
  | body kind checked _ =>
    simp only [MemberMachine.feed, CheckedRaw.feed, rawMachine_feed_nil]
  | _ => simp only [MemberMachine.feed, RawState.feed, Reservoir.feed, List.append_nil,
      GzipHeader.Machine.feed]

/-- The member invariant: canonical, and denoting the fixed successful result. -/
def MemberInv (T : List UInt8 × LSBReader) (m : MemberMachine) : Prop :=
  MemberCanon m ∧ ∃ r, Reservoir.Normalizes m.reservoir r ∧ m.WellFormed r ∧ m.denote r = some T

theorem member_drive (version : Version) (T : List UInt8 × LSBReader) :
    ∀ (n : Nat) (m : MemberMachine), memberMeasure m = n → MemberInv T m →
      ∃ calls : List RawMachine.Call, RawRuns.deliveredInput calls = [] ∧
        MemberInv T (MemberMachine.runCalls version m calls) ∧
        MemberTerminal (MemberMachine.runCalls version m calls) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm hinv
    by_cases ht : MemberTerminal m
    · exact ⟨[], rfl, hinv, ht⟩
    · obtain ⟨hc, r, hn, hwf, hd⟩ := hinv
      obtain ⟨F, C, hc', hlt⟩ := member_progress version m r hc hn hwf hd ht
      obtain ⟨rest, hn', hwf', hden⟩ := MemberMachine.step_correct_feed version m r F C hn hwf
      have hden0 := hden []
      simp only [Reservoir.readerFeed_nil] at hden0
      have happ : MemberMachine.applyCall version m ⟨[], F, C⟩ = MemberMachine.step version m F C := by
        simp only [MemberMachine.applyCall, memberMachine_feed_nil m hc]
      obtain ⟨calls, hdel, hinv'', ht''⟩ := ih _ (hm ▸ hlt) _ rfl
        ⟨hc', rest, hn', hwf', hden0.symm.trans hd⟩
      refine ⟨⟨[], F, C⟩ :: calls, ?_, ?_, ?_⟩
      · simp only [RawRuns.deliveredInput, List.flatMap_cons, List.nil_append]
        exact hdel
      · change MemberInv T (MemberMachine.runCalls version
          (MemberMachine.applyCall version m ⟨[], F, C⟩) calls)
        rw [happ]; exact hinv''
      · change MemberTerminal (MemberMachine.runCalls version
          (MemberMachine.applyCall version m ⟨[], F, C⟩) calls)
        rw [happ]; exact ht''

theorem start_canon (kind : MemberSemantics.Kind) (bytes : List UInt8) :
    MemberCanon (MemberMachine.start kind bytes) := by
  cases kind
  · exact .header _ _ _
  · exact .gzipHeader _

/-- Completeness of the member machine (any version, zlib or gzip) against its
shared member specification. -/
theorem member_complete (version : Version) (kind : MemberSemantics.Kind) :
    (member version kind).Complete (shared kind) := by
  intro bytes out rest h
  have hview := MemberMachine.start_denote_inputView kind bytes bytes
  have hz : MemberMachine.shared kind bytes = some (out, rest) := h
  rw [hz] at hview
  obtain ⟨rf, hdn⟩ : ∃ rf, (MemberMachine.start kind bytes).denote
      (ContainerFields.alignedReader bytes) = some (out, rf) := by
    cases hx : (MemberMachine.start kind bytes).denote (ContainerFields.alignedReader bytes) with
    | none => rw [hx] at hview; cases hview
    | some p =>
      obtain ⟨o, rf⟩ := p
      rw [hx] at hview
      simp only [MemberSemantics.inputView, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hview
      exact ⟨rf, by rw [hview.1]⟩
  have hinv : MemberInv (out, rf) (MemberMachine.start kind bytes) :=
    ⟨start_canon kind bytes, _, MemberMachine.start_normalizes kind bytes,
      MemberMachine.start_wellFormed kind bytes, hdn⟩
  obtain ⟨calls, hdel, hinv', hterm⟩ := member_drive version _ _ _ rfl hinv
  refine ⟨calls, hdel, ?_⟩
  change memberStatus (MemberMachine.runCalls version (MemberMachine.start kind bytes) calls) =
    .done out
  generalize MemberMachine.runCalls version (MemberMachine.start kind bytes) calls = m
    at hinv' hterm
  obtain ⟨_, r, _, _, hd⟩ := hinv'
  cases m with
  | done st =>
    simp only [MemberMachine.denote, Option.some.injEq, Prod.mk.injEq] at hd
    simp only [memberStatus, hd.1]
  | bad e st => cases hd
  | _ => exact absurd hterm id

theorem zlib_complete (version : Version) : (member version .zlib).Complete Zlib.decoder :=
  Proofs.Formats.Compression.Inflate.shared_zlib ▸ member_complete version .zlib

theorem gzip_complete (version : Version) : (member version .gzip).Complete Gzip.decoder :=
  Proofs.Formats.Compression.Inflate.shared_gzip ▸ member_complete version .gzip

end Silmaril.Proofs.Formats.Compression.InflateComplete
