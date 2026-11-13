module

public import Silmaril.Wasm.Component.Streams.Callback.Defs

/-!
# The local invariant of the generated driver loop

`CB.Inv T c`: facts about the globals of the module that every step keeps (`inv_init`,
`inv_step`). They say when the module has stopped reading (`$eof`), why a drop of the readable end
is pending, that a pending write's region lies in the output buffer, and that the module returns
`EXIT` only after dropping its readable end.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Callback

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event blocked)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Callback

variable {σ : Type}

/-- **The local invariant** of the module. -/
structure _root_.Silmaril.Wasm.Component.Streams.Callback.CB.Inv (T : Tr σ Val Val) (c : CB σ) :
    Prop where
  i1 : c.rdropped = true → c.eof = true
  i2 : c.ended = true → c.eof = true
  i3 : T.done c.s = true → c.eof = true
  i4 : c.pdrop = true → c.rdropped = false ∧ c.rpend = false ∧
    (c.ended = true ∨ T.done c.s = true ∨ c.dead = true)
  i5 : c.eof = true → c.rdropped = false → c.pdrop = false → c.dead = true
  i6 : c.flushed = true → c.rdropped = true
  i7 : c.wpend = true → c.wl ≤ c.out.length ∧ c.dead = false ∧ 0 < c.wl
  i8 : c.rpend = true → c.rdropped = false
  i9 : c.pc = .exit → c.rdropped = true ∧ c.wpend = false
  i10 : c.pdrop = true → c.eof = true
  i11 : c.ended = true → c.rpend = false

theorem stopReading_eq (c : CB σ) :
    c.stopReading = { c with eof := true, pdrop := c.pdrop || (!c.rdropped && !c.rpend) } := rfl

/-- `$stopReading` keeps the invariant when it is called for a reason. -/
theorem inv_stopReading {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T)
    (hwhy : c.rdropped = false → c.rpend = false → c.ended = true ∨ T.done c.s = true ∨
      c.dead = true)
    (hrp : c.rpend = true → c.dead = true) : c.stopReading.Inv T := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun hp => ?_, fun _ hr hp => ?_, h.i6, h.i7,
    h.i8, h.i9, fun _ => rfl, h.i11⟩
  · cases hpd : c.pdrop
    · cases hrd : c.rdropped <;> cases hrp' : c.rpend <;>
        simp_all [stopReading_eq]
    · exact h.i4 hpd
  · cases hrp' : c.rpend
    · simp_all [stopReading_eq]
    · exact hrp hrp'

/-- What `$onread` changes. -/
structure OnreadFields (T : Tr σ Val Val) (c c' : CB σ) (p : Nat) (ys : List Val) : Prop where
  pc : c'.pc = c.pc
  s : c'.s = (T.feed c.s ys).1
  out : c'.out = c.out ++ (T.feed c.s ys).2
  wl : c'.wl = c.wl
  rdropped : c'.rdropped = c.rdropped
  flushed : c'.flushed = c.flushed
  dead : c'.dead = c.dead
  wpend : c'.wpend = c.wpend
  rpend : c'.rpend = c.rpend
  got : c'.got = c.got ++ ys
  ack : c'.ack = c.ack
  ended : c'.ended = (c.ended || decide (status p ≠ 0))
  eof : c'.eof = (c.eof || decide (status p ≠ 0) || T.done (T.feed c.s ys).1)
  pdrop : c'.pdrop = (c.pdrop ||
    ((decide (status p ≠ 0) || T.done (T.feed c.s ys).1) && !c.rdropped && !c.rpend))

theorem onread_fields (T : Tr σ Val Val) (c : CB σ) (p : Nat) (ys : List Val) :
    OnreadFields T c (c.onread T p ys) p ys := by
  by_cases hs : status p = 0 <;> by_cases hd : T.done (T.feed c.s ys).1 = true <;>
    simp only [CB.onread, hs, hd, CB.stopReading, ↓reduceIte, Bool.false_eq_true] <;>
    constructor <;> simp [hs, hd]

/-- Why `$onread` asks for a drop, and that it stops reading then. -/
theorem onread_pdrop {T : Tr σ Val Val} {c c' : CB σ} {p : Nat} {ys : List Val}
    (F : OnreadFields T c c' p ys) (hrp : c.rpend = false) (hrd : c.rdropped = false)
    (hpd : c.pdrop = false) (hp : c'.pdrop = true) :
    (c'.ended = true ∨ T.done c'.s = true ∨ c'.dead = true) ∧ c'.eof = true := by
  have hp' : (decide (status p ≠ 0) || T.done (T.feed c.s ys).1) = true := by
    simpa [F.pdrop, hpd, hrd, hrp] using hp
  rw [F.ended, F.s, F.eof]
  by_cases hs : status p = 0 <;> simp_all

/-- `$onread` without a drop request leaves `$eof` as it was. -/
theorem onread_no_pdrop {T : Tr σ Val Val} {c c' : CB σ} {p : Nat} {ys : List Val}
    (F : OnreadFields T c c' p ys) (hrp : c.rpend = false) (hrd : c.rdropped = false)
    (hpd : c.pdrop = false) (hp : c'.pdrop = false) : c'.eof = c.eof := by
  have hs : status p = 0 := by
    by_contra hs
    simp [F.pdrop, hpd, hrd, hrp, hs] at hp
  have hd : T.done (T.feed c.s ys).1 = false := by
    cases hd : T.done (T.feed c.s ys).1 <;> simp_all [F.pdrop]
  simp [F.eof, hs, hd]

theorem inv_onread {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hrp : c.rpend = false)
    (hrd : c.rdropped = false) (hpd : c.pdrop = false) (p : Nat)
    (ys : List Val) : (c.onread T p ys).Inv T := by
  have F := onread_fields T c p ys
  have hfl : c.flushed = false := by
    cases hf : c.flushed
    · rfl
    · simp [h.i6 hf] at hrd
  have hd : T.done (c.onread T p ys).s = true → (c.onread T p ys).eof = true := fun hd => by
    rw [F.eof, ← F.s, hd]; simp
  have he : (c.onread T p ys).ended = true → (c.onread T p ys).eof = true := fun he => by
    rw [F.eof]; rw [F.ended] at he; cases hc : c.ended <;> simp_all [h.i2]
  refine ⟨fun hr => by simp [F.rdropped, hrd] at hr, he, hd,
    fun hp => ⟨F.rdropped.trans hrd, F.rpend.trans hrp, (onread_pdrop F hrp hrd hpd hp).1⟩,
    fun he' hr hp => ?_, fun hf => by simp [F.flushed, hfl] at hf, fun hw => ?_,
    fun _ => F.rdropped.trans hrd, fun hx => F.rdropped ▸ F.wpend ▸ h.i9 (F.pc ▸ hx),
    fun hp => (onread_pdrop F hrp hrd hpd hp).2, fun _ => F.rpend.trans hrp⟩
  · have he0 : c.eof = true := (onread_no_pdrop F hrp hrd hpd hp) ▸ he'
    exact F.dead.trans (h.i5 he0 hrd hpd)
  · obtain ⟨h1, h2, h3⟩ := h.i7 (F.wpend ▸ hw)
    rw [F.wl, F.out, F.dead, List.length_append]
    exact ⟨by omega, h2, h3⟩

/-- What `$onwrite` changes. -/
theorem onwrite_eq (c : CB σ) (p : Nat) :
    c.onwrite p = if status p = 0 then
      { c with out := c.out.drop (count p), ack := c.ack ++ c.out.take (count p) }
    else
      { c with
        out := c.out.drop (count p)
        ack := c.ack ++ c.out.take (count p)
        dead := true
        eof := true
        pdrop := c.pdrop || (!c.rdropped && !c.rpend) } := by
  unfold CB.onwrite CB.stopReading
  split <;> rfl

theorem inv_onwrite {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hwp : c.wpend = false)
    (p : Nat) : (c.onwrite p).Inv T := by
  rw [onwrite_eq]
  split
  · exact ⟨h.i1, h.i2, h.i3, h.i4, h.i5, h.i6, (fun hw => by simp [hwp] at hw), h.i8, h.i9, h.i10,
      h.i11⟩
  · refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun hp => ?_, fun _ _ _ => rfl, h.i6,
      (fun hw => by simp [hwp] at hw), h.i8, h.i9, (fun _ => rfl), h.i11⟩
    cases hpd : c.pdrop
    · simp only [hpd, Bool.false_or, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      exact ⟨hp.1, hp.2, Or.inr (Or.inr rfl)⟩
    · exact ⟨(h.i4 hpd).1, (h.i4 hpd).2.1, Or.inr (Or.inr rfl)⟩

/-- `$stopReading` after an event on an idle readable end (the writer dropped). -/
theorem inv_stop_ended {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hrp : c.rpend = false) :
    ({ c with pc := .run, ended := true } : CB σ).stopReading.Inv T := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun hp => ?_, fun _ hr hp => ?_, h.i6, h.i7,
    h.i8, (fun hx => by cases hx), (fun _ => rfl), fun _ => hrp⟩
  · cases hpd : c.pdrop
    · simp only [stopReading_eq, hpd, hrp, Bool.false_or, Bool.not_false, Bool.and_true,
        Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      exact ⟨hp, hrp, Or.inl rfl⟩
    · exact ⟨(h.i4 hpd).1, hrp, Or.inl rfl⟩
  · simp [stopReading_eq, hrp] at hr hp
    simp [hr] at hp

/-- `$stopReading` after an event on an idle writable end (the reader dropped). -/
theorem inv_stop_dead {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hwp : c.wpend = false) :
    ({ c with pc := .run, dead := true } : CB σ).stopReading.Inv T := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun hp => ?_, fun _ _ _ => rfl, h.i6,
    (fun hw => by simp [stopReading_eq, hwp] at hw), h.i8, (fun hx => by cases hx),
    (fun _ => rfl), h.i11⟩
  cases hpd : c.pdrop
  · simp only [stopReading_eq, hpd, Bool.false_or, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at hp
    exact ⟨hp.1, hp.2, Or.inr (Or.inr rfl)⟩
  · exact ⟨(h.i4 hpd).1, (h.i4 hpd).2.1, Or.inr (Or.inr rfl)⟩

theorem inv_init (T : Tr σ Val Val) : (CB.init T).Inv T := by
  unfold CB.init
  split
  · rename_i hd
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, Or.inr (Or.inl hd)⟩,
      (fun _ _ hp => by cases hp), (fun hf => by cases hf), (fun hw => by cases hw),
      (fun hr => by cases hr), (fun hx => by cases hx), (fun _ => rfl), fun _ => rfl⟩
  · rename_i hd
    exact ⟨(fun hr => by cases hr), (fun he => by cases he), (fun h => absurd h hd),
      (fun hp => by cases hp), (fun he => by cases he), (fun hf => by cases hf),
      (fun hw => by cases hw), (fun hr => by cases hr), (fun hx => by cases hx),
      (fun hp => by cases hp), (fun he => by cases he)⟩

theorem writeLen_pos {wmax n : Nat} (h : 0 < n) : 0 < writeLen wmax n := by
  unfold writeLen; split <;> omega

theorem writeLen_le (wmax n : Nat) : writeLen wmax n ≤ n := by
  unfold writeLen; split <;> omega

/-- A drop of the readable end that `$stopReading` asked for. -/
theorem inv_dropR {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hpd : c.pdrop = true) :
    ({ c with pdrop := false, rdropped := true } : CB σ).Inv T := by
  obtain ⟨hr, hrp, -⟩ := h.i4 hpd
  have he : c.eof = true := h.i10 hpd
  exact ⟨fun _ => he, h.i2, h.i3, (fun hp => by cases hp), (fun _ hr' => by cases hr'),
    fun _ => rfl, h.i7, (fun hx => by simp [hrp] at hx), (fun hx => ⟨rfl, (h.i9 hx).2⟩),
    (fun hp => by cases hp), h.i11⟩

/-- Leaving `$pump` with `WAIT`, after resetting an empty or dead output buffer. -/
theorem inv_wait {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hwp : c.wpend = false) :
    ({ c with pc := .wait, out := [] } : CB σ).Inv T :=
  ⟨h.i1, h.i2, h.i3, h.i4, h.i5, h.i6, (fun hw => by simp [hwp] at hw), h.i8,
    (fun hx => by cases hx), h.i10, h.i11⟩

theorem inv_flush {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hpd : c.pdrop = false)
    (hwp : c.wpend = false) (he : c.eof = true) (hd : c.dead = false) :
    ({ c with flushed := true, out := T.flush c.s } : CB σ).Inv T := by
  have hr : c.rdropped = true := by
    cases hr : c.rdropped
    · have := h.i5 he hr hpd
      rw [hd] at this
      cases this
    · rfl
  exact ⟨h.i1, h.i2, h.i3, h.i4, h.i5, (fun _ => hr), (fun hw => by simp [hwp] at hw), h.i8, h.i9,
    h.i10, h.i11⟩

theorem inv_write_step {T : Tr σ Val Val} {c : CB σ} {wmax res : Nat} (h : c.Inv T)
    (hwp : c.wpend = false) (hd : c.dead = false) (hne : c.out ≠ []) :
    (if res = blocked then
        ({ c with pc := .wait, wpend := true, wl := writeLen wmax c.out.length } : CB σ)
      else c.onwrite res).Inv T := by
  split
  · have hl : 0 < c.out.length := List.length_pos_iff.2 hne
    exact ⟨h.i1, h.i2, h.i3, h.i4, h.i5, h.i6,
      (fun _ => ⟨writeLen_le _ _, hd, writeLen_pos hl⟩), h.i8, (fun hx => by cases hx), h.i10,
      h.i11⟩
  · exact inv_onwrite h hwp _

/-- Resetting the output buffer keeps the invariant. -/
theorem inv_reset {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hwp : c.wpend = false) :
    ({ c with out := [] } : CB σ).Inv T :=
  ⟨h.i1, h.i2, h.i3, h.i4, h.i5, h.i6, (fun hw => by simp [hwp] at hw), h.i8, h.i9, h.i10, h.i11⟩

theorem inv_stopEnd_step {T : Tr σ Val Val} {c : CB σ} (h : c.Inv T) (hwp : c.wpend = false)
    (hfd : c.flushed = true ∨ c.dead = true) (hrp : c.rpend = false) (hrd : c.rdropped = false) :
    ({ c with out := [] } : CB σ).stopReading.Inv T := by
  have hd : c.dead = true := by
    rcases hfd with hf | hd
    · have := h.i6 hf
      rw [hrd] at this
      cases this
    · exact hd
  exact inv_stopReading (inv_reset h hwp) (fun _ _ => Or.inr (Or.inr hd))
    (fun hx => by simp [hrp] at hx)

theorem inv_read_step {T : Tr σ Val Val} {c : CB σ} {res : Res} (h : c.Inv T)
    (hpd : c.pdrop = false) (hwp : c.wpend = false) (he : c.eof = false) (hrp : c.rpend = false) :
    (match res with
      | .read p ys => ({ c with out := [] } : CB σ).onread T p ys
      | _ => ({ c with pc := .wait, rpend := true, out := [] } : CB σ)).Inv T := by
  have hrd : c.rdropped = false := by
    cases hr : c.rdropped
    · rfl
    · rw [h.i1 hr] at he; cases he
  split
  · exact inv_onread (inv_reset h hwp) hrp hrd hpd _ _
  · exact ⟨h.i1, h.i2, h.i3, (fun hp => by simp [hpd] at hp), (fun he' => by simp [he] at he'),
      h.i6, (fun hw => by simp [hwp] at hw), (fun _ => hrd), (fun hx => by cases hx), h.i10,
      (fun hen => by rw [h.i2 hen] at he; cases he)⟩

theorem inv_evIn_step {T : Tr σ Val Val} {c : CB σ} {e : Event} (h : c.Inv T) :
    (if c.rpend then ({ c with pc := .run, rpend := false } : CB σ).onread T e.payload e.items
      else ({ c with pc := .run, ended := true } : CB σ).stopReading).Inv T := by
  split
  · rename_i hrp
    have hrd : c.rdropped = false := h.i8 hrp
    have hpd : c.pdrop = false := by
      cases hp : c.pdrop
      · rfl
      · rw [(h.i4 hp).2.1] at hrp; cases hrp
    have h0 : ({ c with pc := .run, rpend := false } : CB σ).Inv T :=
      ⟨h.i1, h.i2, h.i3, (fun hp => by simp [hpd] at hp), h.i5, h.i6, h.i7,
        (fun hx => by cases hx), (fun hx => by cases hx), h.i10, fun _ => rfl⟩
    exact inv_onread h0 rfl hrd hpd _ _
  · rename_i hrp
    exact inv_stop_ended h (by simpa using hrp)

theorem inv_evOut_step {T : Tr σ Val Val} {c : CB σ} {e : Event} (h : c.Inv T) :
    (if c.wpend then ({ c with pc := .run, wpend := false } : CB σ).onwrite e.payload
      else ({ c with pc := .run, dead := true } : CB σ).stopReading).Inv T := by
  split
  · have h0 : ({ c with pc := .run, wpend := false } : CB σ).Inv T :=
      ⟨h.i1, h.i2, h.i3, h.i4, h.i5, h.i6, (fun hw => by cases hw), h.i8,
        (fun hx => by cases hx), h.i10, h.i11⟩
    exact inv_onwrite h0 rfl _
  · rename_i hwp
    exact inv_stop_dead h (by simpa using hwp)

/-- **Every step of the module keeps its invariant.** -/
theorem inv_cbstep {T : Tr σ Val Val} {r w ws batch wmax : Nat} {st st' : DStore} {c c' : CB σ}
    (h : c.Inv T) (hs : CBStep T r w ws batch wmax st c st' c') : c'.Inv T := by
  cases hs with
  | dropR _ hpd _ => exact inv_dropR h hpd
  | waitW _ _ hwp =>
    exact ⟨h.i1, h.i2, h.i3, h.i4, h.i5, h.i6, h.i7, h.i8, (fun hx => by cases hx), h.i10, h.i11⟩
  | write _ _ hwp hd hne _ => exact inv_write_step h hwp hd hne
  | flush _ hpd hwp _ he _ hd => exact inv_flush h hpd hwp he hd
  | waitEof _ _ hwp => exact inv_wait h hwp
  | stopEnd _ _ hwp _ _ hfd hrp hrd => exact inv_stopEnd_step h hwp hfd hrp hrd
  | dropW _ _ hwp _ _ _ _ hrd =>
    exact ⟨h.i1, h.i2, h.i3, h.i4, h.i5, h.i6, (fun hw => by simp [hwp] at hw), h.i8,
      (fun _ => ⟨hrd, hwp⟩), h.i10, h.i11⟩
  | waitR _ _ hwp => exact inv_wait h hwp
  | read _ hpd hwp _ he hrp _ => exact inv_read_step h hpd hwp he hrp
  | evIn _ _ => exact inv_evIn_step h
  | evOut _ _ => exact inv_evOut_step h

end Silmaril.Proofs.Wasm.Component.Streams.Callback
