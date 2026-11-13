module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.StdoutStep
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Typed

/-!
# Proofs: WASI 0.3 over 0.2 satisfies the loose stdout theory

The invariant `OutJ` relates the component's state to the state of `stdoutTh3w`: the recorded
pairs are `(r, r + 1)` (or `(0, 0)`), recorded futures are below `next` (or `0`), the future of a
stdout binding of the channel `ch` is recorded only with the writable end `ch + 1`, the futures
of input bindings are not recorded, and the writable ends the component saw dropped are recorded
as dropped. Hence `future.read` answers `ok` only after the theory has seen the drop.
`stdout_sat` holds for every theory of the 0.2 host.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult blocked)
open Silmaril.Wasi.Versions.P3

variable {ST : Type}

/-- The stdout invariant. -/
structure OutJ (c : Core) (q : OutSt) : Prop where
  pairs : ∀ p ∈ q.pairs, (p.1 = 0 ∧ p.2 = 0) ∨ p.2 = p.1 + 1
  futs : ∀ p ∈ q.futs, p.1 = 0 ∨ p.1 < c.st.next
  outs : ∀ e ∈ c.outs, 0 < e.2.fut ∧ e.2.fut < c.st.next ∧
    ∀ p ∈ q.futs, p.1 = e.2.fut → p.2 = e.1 + 1
  ins : ∀ e ∈ c.ins, 0 < e.2.fut ∧ e.2.fut < c.st.next ∧ ∀ p ∈ q.futs, p.1 ≠ e.2.fut
  wdrop : ∀ w ∈ c.wdrop, w ∈ q.dropped
  pos : 1 ≤ c.st.next

/-- The invariant holds initially. -/
theorem OutJ.init : OutJ ({} : Core) stdoutTh3w.init :=
  ⟨by simp [stdoutTh3w], by simp [stdoutTh3w], by simp, by simp, by simp, Nat.le_refl _⟩

/-- The invariant survives a frame. -/
theorem OutJ.frame {c c' : Core} {q : OutSt} (h : OutJ c q) (hf : Frame c c') : OutJ c' q := by
  refine ⟨h.pairs, fun p hp => (h.futs p hp).imp id (fun h' => Nat.lt_of_lt_of_le h' hf.next),
    fun e he => ?_, fun e he => ?_, fun w hw => h.wdrop w (hf.wdrop ▸ hw),
    Nat.le_trans h.pos hf.next⟩
  · obtain ⟨h1, h2, h3⟩ := h.outs e (hf.outs ▸ he)
    exact ⟨h1, Nat.lt_of_lt_of_le h2 hf.next, h3⟩
  · obtain ⟨e', he', -, hfut, -, -⟩ := hf.ins e he
    obtain ⟨h1, h2, h3⟩ := h.ins e' he'
    exact ⟨hfut ▸ h1, hfut ▸ Nat.lt_of_lt_of_le h2 hf.next, hfut ▸ h3⟩

/-- The postcondition of a call for the stdout theory. -/
def OutPost (q : (nsig p3World.imports).Op) (qG : OutSt) (a : St × Option (List Val)) : Prop :=
  ∃ qG', stdoutTh3w.step qG (.imp q.1.1 q.2 a.2) = some qG' ∧ OutJ a.1.core qG'

/-- `stream.new`. -/
theorem out_post_new {c : Core} {qG : OutSt} (h : OutJ c qG) (a : List Val) :
    ∃ qG', stdoutTh3w.step qG (.imp cStreamNew a
      (some [natV (finNew c).2.1, natV (finNew c).2.2])) = some qG' ∧ OutJ (finNew c).1 qG' := by
  cases hr : c.room
  · rw [finNew_noroom hr]
    refine ⟨_, out_new qG a (by simp) (by simp), ?_⟩
    exact ⟨fun p hp => by
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Or.inl ⟨rfl, rfl⟩
      · exact h.pairs p hp, h.futs, h.outs, h.ins, h.wdrop, h.pos⟩
  · obtain ⟨h2, hn⟩ := finNew_room hr
    have hl := room_lt hr
    rw [h2]
    refine ⟨_, out_new qG a (by omega) (by omega), ?_⟩
    have hJ := h.frame (finNew_frame c)
    exact ⟨fun p hp => by
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Or.inr rfl
      · exact h.pairs p hp, hJ.futs, hJ.outs, hJ.ins, hJ.wdrop, hJ.pos⟩

/-- `write-via-stream` answered the future `x`: the stdout theory records it at most with a
writable end it paired with the argument. -/
theorem out_wvs_step (qG : OutSt) (a : List Val) {x : Nat} (hx : x < 2 ^ 32) :
    ∃ qG', stdoutTh3w.step qG (.imp stdoutWrite3 a (some [natV x])) = some qG' ∧
      qG'.pairs = qG.pairs ∧ qG'.dropped = qG.dropped ∧ ∀ p ∈ qG'.futs, p ∈ qG.futs ∨
        (p.1 = x ∧ ∃ v r, a = [v] ∧ natOf v = some r ∧ (r, p.2) ∈ qG.pairs) := by
  by_cases ha : ∃ v, a = [v]
  · obtain ⟨v, rfl⟩ := ha
    rw [out_wvs1 qG v hx]
    split
    · rename_i w hw
      refine ⟨_, rfl, rfl, rfl, fun p hp => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · cases hv : natOf v with
        | none => simp [hv] at hw
        | some r =>
          simp only [hv, Option.bind_eq_bind, Option.bind_some] at hw
          exact Or.inr ⟨rfl, v, r, rfl, hv, wOf_mem hw⟩
      · exact Or.inl hp
    · exact ⟨qG, rfl, rfl, rfl, fun p hp => Or.inl hp⟩
  · exact ⟨qG, out_wvs_ne qG (fun v hv => ha ⟨v, hv⟩) _, rfl, rfl, fun p hp => Or.inl hp⟩

/-- `write-via-stream` without room: the future `0`. -/
theorem out_post_wvs_noroom {c : Core} {qG : OutSt} (h : OutJ c qG) (a : List Val) :
    ∃ qG', stdoutTh3w.step qG (.imp stdoutWrite3 a (some [natV 0])) = some qG' ∧ OutJ c qG' := by
  obtain ⟨qG', hs, hp, hd, hfu⟩ := out_wvs_step qG a (x := 0) (by decide)
  refine ⟨qG', hs, hp ▸ h.pairs, fun p hq => ?_, fun e he => ?_, fun e he => ?_,
    hd ▸ h.wdrop, h.pos⟩
  · rcases hfu p hq with hq | ⟨hq, -⟩
    · exact h.futs p hq
    · exact Or.inl hq
  · obtain ⟨h1, h2, h3⟩ := h.outs e he
    refine ⟨h1, h2, fun p hq hpe => ?_⟩
    rcases hfu p hq with hq | ⟨hq, -⟩
    · exact h3 p hq hpe
    · omega
  · obtain ⟨h1, h2, h3⟩ := h.ins e he
    refine ⟨h1, h2, fun p hq hpe => ?_⟩
    rcases hfu p hq with hq | ⟨hq, -⟩
    · exact h3 p hq hpe
    · omega

/-- The new stdout binding of `write-via-stream`: its future is paired with `r + 1`. -/
theorem out_wvs_new {c : Core} {qG qG' : OutSt} (h : OutJ c qG) {a : List Val} {r : Nat}
    (hsrc : wvsSrc c a = some r)
    (hfu : ∀ p ∈ qG'.futs, p ∈ qG.futs ∨
      (p.1 = c.st.next ∧ ∃ v r', a = [v] ∧ natOf v = some r' ∧ (r', p.2) ∈ qG.pairs))
    (p : Nat × Nat) (hq : p ∈ qG'.futs) (hpe : p.1 = c.st.next) : p.2 = r + 1 := by
  have hpos : 1 ≤ c.st.next := h.pos
  rcases hfu p hq with hq | ⟨-, v, r', rfl, hv, hpr⟩
  · rcases h.futs p hq with h0 | h0 <;> omega
  · simp only [wvsSrc, arg1, hv] at hsrc
    split_ifs at hsrc with hr0
    simp only [Option.some.injEq] at hsrc
    subst hsrc
    rcases h.pairs _ hpr with ⟨h0, -⟩ | h1
    · exact absurd h0 hr0.1
    · exact h1

/-- The stdout bindings after `write-via-stream` with room. -/
theorem out_wvs_outs {c : Core} {qG qG' : OutSt} (h : OutJ c qG) (hr : c.room = true)
    (a : List Val) (d : Option (BitVec 32))
    (hfu : ∀ p ∈ qG'.futs, p ∈ qG.futs ∨
      (p.1 = c.st.next ∧ ∃ v r', a = [v] ∧ natOf v = some r' ∧ (r', p.2) ∈ qG.pairs))
    (e : Nat × OutB) (he : e ∈ (finWvs c a d).1.outs) :
    0 < e.2.fut ∧ e.2.fut < (finWvs c a d).1.st.next ∧
      ∀ p ∈ qG'.futs, p.1 = e.2.fut → p.2 = e.1 + 1 := by
  obtain ⟨-, hn, -, -, ho⟩ := finWvs_room hr a d
  have hl : c.st.next + 4 < 2 ^ 32 := room_lt hr
  have hpos : 1 ≤ c.st.next := h.pos
  rw [hn]
  rw [ho] at he
  split at he
  · rename_i r os hsrc
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨by simp; omega, by simp, out_wvs_new h hsrc hfu⟩
    · obtain ⟨h1, h2, h3⟩ := h.outs e he
      refine ⟨h1, by omega, fun p hq hpe => ?_⟩
      rcases hfu p hq with hq | ⟨hq, -⟩
      · exact h3 p hq hpe
      · omega
  · obtain ⟨h1, h2, h3⟩ := h.outs e he
    refine ⟨h1, by omega, fun p hq hpe => ?_⟩
    rcases hfu p hq with hq | ⟨hq, -⟩
    · exact h3 p hq hpe
    · omega

/-- `write-via-stream` with room. -/
theorem out_post_wvs_room {c : Core} {qG : OutSt} (h : OutJ c qG) (hr : c.room = true)
    (a : List Val) (d : Option (BitVec 32)) :
    ∃ qG', stdoutTh3w.step qG (.imp stdoutWrite3 a (some [natV (finWvs c a d).2])) = some qG' ∧
      OutJ (finWvs c a d).1 qG' := by
  obtain ⟨hf, hn, hi, hw, -⟩ := finWvs_room hr a d
  have hl : c.st.next + 4 < 2 ^ 32 := room_lt hr
  have hpos : 1 ≤ c.st.next := h.pos
  rw [hf]
  obtain ⟨qG', hs, hp, hd, hfu⟩ := out_wvs_step qG a (x := c.st.next) (by omega)
  refine ⟨qG', hs, hp ▸ h.pairs, fun p hq => ?_, out_wvs_outs h hr a d hfu, fun e he => ?_,
    fun w hw' => hd ▸ h.wdrop w (hw ▸ hw'), by omega⟩
  · rw [hn]
    rcases hfu p hq with hq | ⟨hq, -⟩
    · exact (h.futs p hq).imp id (fun h' => by omega)
    · exact Or.inr (by omega)
  · rw [hn]
    rw [hi] at he
    obtain ⟨h1, h2, h3⟩ := h.ins e he
    refine ⟨h1, by omega, fun p hq hpe => ?_⟩
    rcases hfu p hq with hq | ⟨hq, -⟩
    · exact h3 p hq hpe
    · omega

/-- `write-via-stream`. -/
theorem out_post_wvs {c : Core} {qG : OutSt} (h : OutJ c qG) (a : List Val)
    (d : Option (BitVec 32)) :
    ∃ qG', stdoutTh3w.step qG (.imp stdoutWrite3 a (some [natV (finWvs c a d).2])) = some qG' ∧
      OutJ (finWvs c a d).1 qG' := by
  cases hr : c.room
  · rw [finWvs_noroom hr]
    exact out_post_wvs_noroom h a
  · exact out_post_wvs_room h hr a d

/-- `stream.drop-writable`. -/
theorem out_post_dw {c : Core} {qG : OutSt} (h : OutJ c qG) (a : List Val) :
    ∃ qG', stdoutTh3w.step qG (.imp cStreamDropW a (some [])) = some qG' ∧
      OutJ (finDropW c a) qG' := by
  obtain ⟨qG', hs, hp, hf, hd, ha⟩ := out_dw qG a
  obtain ⟨hn, ho, hi, hw⟩ := finDropW_spec c a
  refine ⟨qG', hs, hp ▸ h.pairs, fun p hq => ?_, fun e he => ?_, fun e he => ?_,
    fun w hw' => ?_, Nat.le_trans h.pos hn⟩
  · exact (h.futs p (hf ▸ hq)).imp id (fun h' => Nat.lt_of_lt_of_le h' hn)
  · obtain ⟨h1, h2, h3⟩ := h.outs e (ho ▸ he)
    exact ⟨h1, Nat.lt_of_lt_of_le h2 hn, fun p hq => h3 p (hf ▸ hq)⟩
  · obtain ⟨h1, h2, h3⟩ := h.ins e (hi ▸ he)
    exact ⟨h1, Nat.lt_of_lt_of_le h2 hn, fun p hq => h3 p (hf ▸ hq)⟩
  · rw [hw] at hw'
    split at hw'
    · rename_i w' hw''
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact ha _ hw''
      · exact hd w (h.wdrop w hw')
    · exact hd w (h.wdrop w hw')

/-- `future.read` reports `ok` only for a dropped stdout stream or an input stream at its end. -/
theorem finFr_ok {c : Core} {a : List Val} {d : Option (List Val)} (h : finFr c a d = .ok) :
    ∃ f, arg1 a = some f ∧ ((∃ ch ob, c.outFut f = some (ch, ob) ∧ ch + 1 ∈ c.wdrop) ∨
      ∃ e, c.inFut f = some e) := by
  unfold finFr at h
  split at h
  · rename_i f hf
    refine ⟨f, hf, ?_⟩
    repeat' split at h
    all_goals first
      | exact Or.inl ⟨_, _, ‹_›, ‹_›⟩
      | exact Or.inr ⟨_, ‹_›⟩
      | cases h
  · cases h

/-- `future.read` answering `ok`: the theory has seen the writable end dropped. -/
theorem out_fr_dropped {c : Core} {qG : OutSt} (h : OutJ c qG) {a : List Val}
    {d : Option (List Val)} (hx : finFr c a d = .ok) (v : Val) (f w : Nat) (ha : a = [v])
    (hv : natOf v = some f) (hw : (qG.futs.find? (·.1 = f)).map (·.2) = some w) :
    w ∈ qG.dropped := by
  obtain ⟨f', hf', hcase⟩ := finFr_ok hx
  subst ha
  simp only [arg1, hv, Option.some.injEq] at hf'
  subst hf'
  cases hp : qG.futs.find? (·.1 = f) with
  | none => simp [hp] at hw
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq] at hw
    have hpm : p ∈ qG.futs := List.mem_of_find?_eq_some hp
    have hp1 : p.1 = f := by simpa using List.find?_some hp
    rcases hcase with ⟨ch, ob, hout, hdrop⟩ | ⟨e, hin⟩
    · have hof : ob.fut = f := by simpa using List.find?_some hout
      have hpe := (h.outs _ (List.mem_of_find?_eq_some hout)).2.2 p hpm (hp1.trans hof.symm)
      rw [← hw, hpe]
      exact h.wdrop _ hdrop
    · have hef : e.2.fut = f := by simpa using List.find?_some hin
      exact absurd (hp1.trans hef.symm) ((h.ins _ (List.mem_of_find?_eq_some hin)).2.2 p hpm)

/-- `future.read`. -/
theorem out_post_fr {c : Core} {qG : OutSt} (h : OutJ c qG) (a : List Val)
    (d : Option (List Val)) :
    ∃ qG', stdoutTh3w.step qG (.imp cFutureRead a (finFr c a d).enc) = some qG' ∧ OutJ c qG' := by
  cases hx : finFr c a d
  · exact ⟨qG, out_fr_notok qG a (by simp), h⟩
  · exact ⟨qG, out_fr_ok qG a fun v f w ha hv hw => out_fr_dropped h hx v f w ha hv hw, h⟩
  · exact ⟨qG, out_fr_notok qG a (by simp), h⟩

/-- The input bindings after `finIn` keep the futures of old ones, or have the new future. -/
theorem OutJ.finIn_ins {c : Core} {q : OutSt} (h : OutJ c q) (hr : c.room = true) (file : Bool)
    (d : Option (BitVec 32)) (e : Nat × InB) (he : e ∈ (P3OverP2.finIn c file d).1.ins) :
    0 < e.2.fut ∧ e.2.fut < (P3OverP2.finIn c file d).1.st.next ∧ ∀ p ∈ q.futs, p.1 ≠ e.2.fut := by
  obtain ⟨-, -, hn, -, -, hi⟩ := finIn_room hr file d
  rw [hn]
  rw [hi] at he
  rcases List.mem_cons.1 he with rfl | he
  · refine ⟨by simp, by simp, fun p hp hpe => ?_⟩
    simp only at hpe
    rcases h.futs p hp with h0 | h0 <;> omega
  · have hold : ∃ e' ∈ c.ins, e'.2.fut = e.2.fut := by
      cases d with
      | none => exact ⟨e, he, rfl⟩
      | some is =>
        simp only [killIs, List.mem_map] at he
        obtain ⟨e', he', rfl⟩ := he
        exact ⟨e', he', by split <;> rfl⟩
    obtain ⟨e', he', hfut⟩ := hold
    obtain ⟨h1, h2, h3⟩ := h.ins e' he'
    exact ⟨hfut ▸ h1, by omega, hfut ▸ h3⟩

/-- `finIn` keeps the invariant. -/
theorem OutJ.finIn {c : Core} {q : OutSt} (h : OutJ c q) (file : Bool) (d : Option (BitVec 32)) :
    OutJ (P3OverP2.finIn c file d).1 q := by
  cases hr : c.room
  · rw [finIn_noroom hr]; exact h
  · obtain ⟨-, -, hn, ho, hw, -⟩ := finIn_room hr file d
    refine ⟨h.pairs, fun p hp => ?_, fun e he => ?_, h.finIn_ins hr file d, hw ▸ h.wdrop, by omega⟩
    · rw [hn]; exact (h.futs p hp).imp id (fun h' => by omega)
    · rw [hn]
      obtain ⟨h1, h2, h3⟩ := h.outs e (ho ▸ he)
      exact ⟨h1, by omega, h3⟩

/-- `read-via-stream` keeps the invariant. -/
theorem OutJ.finRv {c : Core} {q : OutSt} (h : OutJ c q) (a : List Val) (d : Option (List Val)) :
    OutJ (P3OverP2.finRv c a d).1 q := by
  simp only [P3OverP2.finRv]
  split
  · exact h.finIn true _
  · exact h

/-- The stdout part of a call, by class. -/
theorem wp_stdout' (T : Protocol ST WEv) (s : St) (f : FnName) (hf : f ∈ p3World.imports)
    (a : List Val) (qT : ST) (qG : OutSt) (hJ : OutJ s.core qG) :
    Wp T (body s (⟨f, hf⟩, a)) (fun a' _ => ∃ qG', stdoutTh3w.step qG (.imp f a a'.2) = some qG' ∧
      OutJ a'.1.core qG') qT := by
  have hcl : ∃ c, cls f = c ∧ c ≠ .other ∧ f = c.name := cls_cases hf
  obtain ⟨c, hc, hne, rfl⟩ := hcl
  cases c <;> simp only [body, hc, thenFin]
  case other => exact absurd rfl hne
  case streamNew => exact out_post_new hJ a
  case dropR => exact ⟨qG, rfl, hJ.frame (finDropR_frame _ _)⟩
  case futDropR => exact ⟨qG, rfl, hJ.frame (finFDropR_frame _ _)⟩
  case wsNew => exact ⟨qG, rfl, hJ.frame (finWsNew_frame _)⟩
  case join => exact ⟨qG, rfl, hJ.frame (finJoin_frame _ _)⟩
  all_goals refine wp_fin' T _ _ (fun d _ => ?_) qT
  case streamWrite => exact ⟨qG, out_sw qG a _, hJ.frame (finSw_frame _ _ _)⟩
  case streamRead => exact ⟨qG, rfl, hJ.frame (finSr_frame _ _ _)⟩
  case dropW => exact out_post_dw hJ a
  case futRead => exact out_post_fr hJ a d
  case wait => exact ⟨qG, rfl, hJ.frame (finWait_frame _ _ _)⟩
  case wvs => exact out_post_wvs hJ a d
  case stdin => exact ⟨qG, rfl, hJ.finIn false d⟩
  case now => exact ⟨qG, rfl, hJ⟩
  case waitFor => exact ⟨qG, rfl, hJ⟩
  case getDirs => exact ⟨qG, rfl, hJ⟩
  case openAt => exact ⟨qG, rfl, hJ⟩
  case readVia => exact ⟨qG, rfl, hJ.finRv a d⟩

/-- The stdout part of a call: the theory accepts the answer, the invariant is kept. -/
theorem wp_stdout (T : Protocol ST WEv) (s : St) (q : (nsig p3World.imports).Op) (qT : ST)
    (qG : OutSt) (hJ : OutJ s.core qG) :
    Wp T (body s q) (fun a _ => ∃ qG', stdoutTh3w.step qG (.imp q.1.1 q.2 a.2) = some qG' ∧
      OutJ a.1.core qG') qT :=
  wp_stdout' T s q.1.1 q.1.2 q.2 qT qG hJ

/-- **The component satisfies the loose stdout theory** (for well-shaped calls), for every theory
of the 0.2 host. -/
theorem stdout_sat (T : Protocol ST WEv) :
    (agP T (retG stdoutTh3w)).holds p3OverP2 :=
  ag_of_wpInv (J := fun s _ q => OutJ s.core q)
    ⟨OutJ.init, fun s qT qG q hJ => wp_stdout T s q qT qG hJ⟩

end Silmaril.Wasi.Versions.P3OverP2
