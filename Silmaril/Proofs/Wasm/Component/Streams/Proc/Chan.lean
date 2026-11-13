module

public import Silmaril.Proofs.Wasm.Component.Streams.Proc.Store

/-!
# The channel protocol invariant

One channel with reader handle `hr` and writer handle `hw`, seen by its two ends. The writer's
view `WV` (idle, a write of `xs` issued, closed) and the reader's view `RV` (idle, a read issued,
stopped) are each related to the abstract channel state by `WInv` and `RInv`, with the items the
writer knows were transferred (`W`) and the items the reader has taken (`R`).

The lemmas give the effect of each abstract built-in (`CS.write`, `CS.read`, `CS.dropR`,
`CS.dropW`) and of taking an event (`takeW`, `takeR`) on the two invariants: the other end's
invariant is preserved, and the acting end's new view and data are determined by the result.
They are generic in the handles, so they serve both channels of the pipeline.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Proc

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async
open Silmaril.Wasm.Component.Streams.Proc

/-- The writer's view of a channel. -/
inductive WV where
  | idle
  | wait (xs : List Val)
  | closed

/-- The reader's view of a channel. -/
inductive RV where
  | idle
  | wait
  | stopped

/-- No pending write. -/
def NoW (a : CS) : Prop := ∀ h xs, a.c.pend ≠ .write h xs

/-- No pending read. -/
def NoR (a : CS) : Prop := ∀ h n, a.c.pend ≠ .read h n

/-- **The writer's invariant**: `W` are the items it knows were transferred. -/
def WInv (hw : Nat) : WV → CS → List Val → Prop
  | .idle, a, W => a.dw = false ∧ a.ew = none ∧ a.c.wDropped = false ∧ NoW a ∧ a.c.sent = W
  | .wait xs, a, W => a.dw = false ∧ a.c.wDropped = false ∧
      ((a.c.pend = .write hw xs ∧ a.ew = none ∧ a.c.sent = W) ∨
       (∃ k, a.ew = some ⟨.streamWrite, hw, packCopy .completed k, []⟩ ∧ NoW a ∧
          a.c.sent = W ++ xs.take k) ∨
       (a.ew = some ⟨.streamWrite, hw, packCopy .dropped 0, []⟩ ∧ NoW a ∧ a.c.rDropped = true ∧
          a.c.sent = W))
  | .closed, a, W => a.dw = true ∧ a.ew = none ∧ a.c.wDropped = true ∧ NoW a ∧ a.c.sent = W

/-- **The reader's invariant**: `R` are the items it has taken. -/
def RInv (hr : Nat) : RV → CS → List Val → Prop
  | .idle, a, R => a.dr = false ∧ a.er = none ∧ a.c.rDropped = false ∧ NoR a ∧ a.c.sent = R
  | .wait, a, R => a.dr = false ∧ a.c.rDropped = false ∧
      ((∃ n, a.c.pend = .read hr n ∧ a.er = none ∧ a.c.sent = R) ∨
       (∃ k ys, a.er = some ⟨.streamRead, hr, packCopy .completed k, ys⟩ ∧ NoR a ∧
          a.c.sent = R ++ ys) ∨
       (a.er = some ⟨.streamRead, hr, packCopy .dropped 0, []⟩ ∧ NoR a ∧ a.c.wDropped = true ∧
          a.c.sent = R))
  | .stopped, a, R => a.dr = true ∧ a.er = none ∧ a.c.rDropped = true ∧ NoR a ∧ a.c.sent = R

/-! ## Handles of pending copies -/

theorem RInv.readHandle {hr : Nat} {rv : RV} {a : CS} {R : List Val} (h : RInv hr rv a R) :
    ∀ h' n, a.c.pend = .read h' n → h' = hr := by
  intro h' n hp
  cases rv with
  | idle => exact absurd hp (h.2.2.2.1 h' n)
  | stopped => exact absurd hp (h.2.2.2.1 h' n)
  | wait =>
    rcases h.2.2 with ⟨m, hm, -, -⟩ | ⟨k, ys, -, hn, -⟩ | ⟨-, hn, -, -⟩
    · rw [hm] at hp
      cases hp
      rfl
    · exact absurd hp (hn h' n)
    · exact absurd hp (hn h' n)

theorem WInv.writeHandle {hw : Nat} {wv : WV} {a : CS} {W : List Val} (h : WInv hw wv a W) :
    ∀ h' xs, a.c.pend = .write h' xs → h' = hw := by
  intro h' xs hp
  cases wv with
  | idle => exact absurd hp (h.2.2.2.1 h' xs)
  | closed => exact absurd hp (h.2.2.2.1 h' xs)
  | wait ys =>
    rcases h.2.2 with ⟨hm, -, -⟩ | ⟨k, -, hn, -⟩ | ⟨-, hn, -, -⟩
    · rw [hm] at hp
      cases hp
      rfl
    · exact absurd hp (hn h' xs)
    · exact absurd hp (hn h' xs)

/-- A dropped writable end is closed. -/
theorem WInv.closed_of_wDropped {hw : Nat} {wv : WV} {a : CS} {W : List Val} (h : WInv hw wv a W)
    (hd : a.c.wDropped = true) : wv = .closed := by
  cases wv with
  | idle => exact absurd hd (by rw [h.2.2.1]; decide)
  | wait xs => exact absurd hd (by rw [h.2.1]; decide)
  | closed => rfl

/-- A dropped readable end is stopped. -/
theorem RInv.stopped_of_rDropped {hr : Nat} {rv : RV} {a : CS} {R : List Val} (h : RInv hr rv a R)
    (hd : a.c.rDropped = true) : rv = .stopped := by
  cases rv with
  | idle => exact absurd hd (by rw [h.2.2.1]; decide)
  | wait => exact absurd hd (by rw [h.2.1]; decide)
  | stopped => rfl

/-! ## Packed results -/

theorem packCopy_ne_blocked (r : CopyResult) (k : Nat) : packCopy r k ≠ blocked := by
  cases r <;> simp [packCopy, CopyResult.toNat, blocked] <;> omega

theorem status_completed (k : Nat) : copyStatus (packCopy .completed k) = 0 := by
  simp [copyStatus, packCopy, CopyResult.toNat]

theorem count_completed (k : Nat) : copyCount (packCopy .completed k) = k := by
  simp [copyCount, packCopy, CopyResult.toNat]

theorem status_dropped : copyStatus (packCopy .dropped 0) ≠ 0 := by
  simp [copyStatus, packCopy, CopyResult.toNat]

/-! ## Frames: changes the other end does not see -/

/-- The reader's invariant only depends on the reader's fields, the pending read and the
writer's drop flag. -/
theorem RInv.frame {hr : Nat} {rv : RV} {a a' : CS} {R : List Val} (h : RInv hr rv a R)
    (hn : NoR a) (hn' : NoR a') (hdr : a'.dr = a.dr) (her : a'.er = a.er)
    (hrd : a'.c.rDropped = a.c.rDropped) (hwd : a.c.wDropped = true → a'.c.wDropped = true)
    (hs : a'.c.sent = a.c.sent) : RInv hr rv a' R := by
  cases rv with
  | idle => exact ⟨hdr ▸ h.1, her ▸ h.2.1, hrd ▸ h.2.2.1, hn', hs ▸ h.2.2.2.2⟩
  | stopped => exact ⟨hdr ▸ h.1, her ▸ h.2.1, hrd ▸ h.2.2.1, hn', hs ▸ h.2.2.2.2⟩
  | wait =>
    refine ⟨hdr ▸ h.1, hrd ▸ h.2.1, ?_⟩
    rcases h.2.2 with ⟨m, hm, -, -⟩ | ⟨k, ys, he, -, hsent⟩ | ⟨he, -, hw, hsent⟩
    · exact absurd hm (hn hr m)
    · exact Or.inr (Or.inl ⟨k, ys, her ▸ he, hn', hs ▸ hsent⟩)
    · exact Or.inr (Or.inr ⟨her ▸ he, hn', hwd hw, hs ▸ hsent⟩)

/-- The writer's invariant only depends on the writer's fields, the pending write and the
reader's drop flag. -/
theorem WInv.frame {hw : Nat} {wv : WV} {a a' : CS} {W : List Val} (h : WInv hw wv a W)
    (hn : NoW a) (hn' : NoW a') (hdw : a'.dw = a.dw) (hew : a'.ew = a.ew)
    (hwd : a'.c.wDropped = a.c.wDropped) (hrd : a.c.rDropped = true → a'.c.rDropped = true)
    (hs : a'.c.sent = a.c.sent) : WInv hw wv a' W := by
  cases wv with
  | idle => exact ⟨hdw ▸ h.1, hew ▸ h.2.1, hwd ▸ h.2.2.1, hn', hs ▸ h.2.2.2.2⟩
  | closed => exact ⟨hdw ▸ h.1, hew ▸ h.2.1, hwd ▸ h.2.2.1, hn', hs ▸ h.2.2.2.2⟩
  | wait xs =>
    refine ⟨hdw ▸ h.1, hwd ▸ h.2.1, ?_⟩
    rcases h.2.2 with ⟨hm, -, -⟩ | ⟨k, he, -, hsent⟩ | ⟨he, -, hr, hsent⟩
    · exact absurd hm (hn hw xs)
    · exact Or.inr (Or.inl ⟨k, hew ▸ he, hn', hs ▸ hsent⟩)
    · exact Or.inr (Or.inr ⟨hew ▸ he, hn', hrd hr, hs ▸ hsent⟩)

theorem noW_idle (a : CS) (h : a.c.pend = .idle) : NoW a := fun _ _ e => by rw [h] at e; cases e

theorem noR_idle (a : CS) (h : a.c.pend = .idle) : NoR a := fun _ _ e => by rw [h] at e; cases e

theorem noR_write (a : CS) (hw : Nat) (xs : List Val) (h : a.c.pend = .write hw xs) : NoR a :=
  fun _ _ e => by rw [h] at e; cases e

theorem noW_read (a : CS) (hr n : Nat) (h : a.c.pend = .read hr n) : NoW a :=
  fun _ _ e => by rw [h] at e; cases e

/-- The reader does not see the writer's event. -/
theorem RInv.frame' {hr : Nat} {rv : RV} {a : CS} {R : List Val} {e : Option Event}
    (h : RInv hr rv a R) : RInv hr rv { a with ew := e } R := by
  cases rv with
  | idle => exact h
  | wait => exact h
  | stopped => exact h

/-- The writer does not see the reader's event. -/
theorem WInv.frame' {hw : Nat} {wv : WV} {a : CS} {W : List Val} {e : Option Event}
    (h : WInv hw wv a W) : WInv hw wv { a with er := e } W := by
  cases wv with
  | idle => exact h
  | wait xs => exact h
  | closed => exact h

/-- Dropping the writable end under a pending read. -/
theorem dropW_meets (hr hw n : Nat) (a : CS) (W R : List Val)
    (hW : WInv hw .idle a W) (hR : RInv hr .wait a R) (hp : a.c.pend = .read hr n) :
    RInv hr .wait (a.dropWR hr) R ∧ WInv hw .closed (a.dropWR hr) W := by
  have hsR : a.c.sent = R := by
    rcases hR.2.2 with ⟨m, -, -, hs⟩ | ⟨k, ys, -, hn, -⟩ | ⟨-, hn, -, -⟩
    · exact hs
    · exact absurd hp (hn hr n)
    · exact absurd hp (hn hr n)
  exact ⟨⟨hR.1, hR.2.1, Or.inr (Or.inr ⟨rfl, noR_idle _ rfl, rfl, hsR⟩)⟩,
    ⟨rfl, rfl, rfl, noW_idle _ rfl, hW.2.2.2.2⟩⟩

/-! ## The writer's built-ins -/

/-- The rendezvous of a write with a pending read: both invariants after it. -/
theorem write_meets (hr hw n : Nat) (a : CS) (k : Nat) (ys W R : List Val)
    (hW : WInv hw .idle a W) (hR : RInv hr .wait a R) (hp : a.c.pend = .read hr n) :
    WInv hw .idle (a.metR hr k ys) (W ++ ys) ∧ RInv hr .wait (a.metR hr k ys) R := by
  have hsR : a.c.sent = R := by
    rcases hR.2.2 with ⟨m, -, -, hs⟩ | ⟨k, ys, -, hn, -⟩ | ⟨-, hn, -, -⟩
    · exact hs
    · exact absurd hp (hn hr n)
    · exact absurd hp (hn hr n)
  have hW' : WInv hw .idle (a.metR hr k ys) (W ++ ys) :=
    ⟨hW.1, hW.2.1, hW.2.2.1, noW_idle _ rfl, by simp [CS.metR, hW.2.2.2.2]⟩
  have hR' : RInv hr .wait (a.metR hr k ys) R :=
    ⟨hR.1, hR.2.1, Or.inr (Or.inl ⟨k, ys, rfl, noR_idle _ rfl, by simp [CS.metR, hsR]⟩)⟩
  exact ⟨hW', hR'⟩

/-- The effect of a write on the writer: the three outcomes. -/
def WriteOut (hw : Nat) (a' : CS) (xs W : List Val) (r : Res) : Prop :=
  (∃ k, r = .nat (packCopy .completed k) ∧ WInv hw .idle a' (W ++ xs.take k)) ∨
  (r = .nat (packCopy .dropped 0) ∧ a'.c.rDropped = true ∧ WInv hw .idle a' W) ∨
  (r = .nat blocked ∧ WInv hw (.wait xs) a' W)

/-- A write that finds no pending read. -/
theorem write_idle_case (hr hw : Nat) (rv : RV) (a : CS) (xs W R : List Val)
    (hW : WInv hw .idle a W) (hR : RInv hr rv a R) (hp : a.c.pend = .idle) :
    (a.c.rDropped = true → RInv hr rv a R ∧ WriteOut hw a xs W (.nat (packCopy .dropped 0))) ∧
    (a.c.rDropped = false →
      RInv hr rv (a.pendW hw xs) R ∧ WriteOut hw (a.pendW hw xs) xs W (.nat blocked)) := by
  refine ⟨fun hd => ⟨hR, Or.inr (Or.inl ⟨rfl, hd, hW⟩)⟩, fun _ => ?_⟩
  have hR' : RInv hr rv (a.pendW hw xs) R :=
    hR.frame (noR_idle a hp) (noR_write _ hw xs rfl) rfl rfl rfl id rfl
  exact ⟨hR', Or.inr (Or.inr ⟨rfl, hW.1, hW.2.2.1, Or.inl ⟨rfl, hW.2.1, hW.2.2.2.2⟩⟩)⟩

/-- A write that finds no pending read, from its result. -/
theorem write_idle_res (hr hw : Nat) (rv : RV) (a a' : CS) (xs W R : List Val) (r : Res)
    (hW : WInv hw .idle a W) (hR : RInv hr rv a R) (hp : a.c.pend = .idle)
    (h : a.write hr hw xs = some (a', r)) : RInv hr rv a' R ∧ WriteOut hw a' xs W r := by
  have hc := write_idle_case hr hw rv a xs W R hW hR hp
  have he : a.write hr hw xs = if a.c.rDropped then some (a, .nat (packCopy .dropped 0))
      else some (a.pendW hw xs, .nat blocked) := by simp [CS.write, hp]
  cases hd : a.c.rDropped
  · have hres : some (a.pendW hw xs, Res.nat blocked) = some (a', r) := by
      rw [← h, he, hd]
      rfl
    obtain ⟨rfl, rfl⟩ : a.pendW hw xs = a' ∧ Res.nat blocked = r := by simpa using hres
    exact hc.2 hd
  · have hres : some (a, Res.nat (packCopy .dropped 0)) = some (a', r) := by
      rw [← h, he, hd]
      rfl
    obtain ⟨rfl, rfl⟩ : a = a' ∧ Res.nat (packCopy .dropped 0) = r := by simpa using hres
    exact hc.1 hd

/-- A write that meets a pending read, from its result. -/
theorem write_read_res (hr hw h' n : Nat) (rv : RV) (a a' : CS) (xs W R : List Val) (r : Res)
    (hW : WInv hw .idle a W) (hR : RInv hr rv a R) (hp : a.c.pend = .read h' n)
    (h : a.write hr hw xs = some (a', r)) : RInv hr rv a' R ∧ WriteOut hw a' xs W r := by
  obtain rfl := hR.readHandle h' n hp
  cases rv with
  | idle => exact absurd hp (hR.2.2.2.1 _ n)
  | stopped => exact absurd hp (hR.2.2.2.1 _ n)
  | wait =>
    have hm := write_meets h' hw n a (min n xs.length) (xs.take (min n xs.length)) W R hW hR hp
    have he : a.write h' hw xs = some (a.metR h' (min n xs.length) (xs.take (min n xs.length)),
        .nat (packCopy .completed (min n xs.length))) := by simp [CS.write, hp]
    obtain ⟨rfl, rfl⟩ : a.metR h' (min n xs.length) (xs.take (min n xs.length)) = a' ∧
        Res.nat (packCopy .completed (min n xs.length)) = r := by simpa [he] using h
    exact ⟨hm.2, Or.inl ⟨_, rfl, hm.1⟩⟩

/-- **A write from the idle writer.** -/
theorem write_spec (hr hw : Nat) (rv : RV) (a a' : CS) (xs W R : List Val) (r : Res)
    (hW : WInv hw .idle a W) (hR : RInv hr rv a R) (h : a.write hr hw xs = some (a', r)) :
    RInv hr rv a' R ∧ WriteOut hw a' xs W r := by
  rcases hp : a.c.pend with _ | ⟨h', n⟩ | ⟨h', ys⟩
  · exact write_idle_res hr hw rv a a' xs W R r hW hR hp h
  · exact write_read_res hr hw h' n rv a a' xs W R r hW hR hp h
  · exact absurd hp (hW.2.2.2.1 h' ys)

/-- **Dropping the writable end** from the idle writer. -/
theorem dropW_spec (hr hw : Nat) (rv : RV) (a a' : CS) (W R : List Val) (r : Res)
    (hW : WInv hw .idle a W) (hR : RInv hr rv a R) (h : a.dropW hr = some (a', r)) :
    RInv hr rv a' R ∧ WInv hw .closed a' W := by
  unfold CS.dropW at h
  rcases hp : a.c.pend with _ | ⟨h', n⟩ | ⟨h', ys⟩
  · simp only [hp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR.frame (noR_idle a hp) (noR_idle _ hp) rfl rfl rfl (fun _ => rfl) rfl,
      ⟨rfl, rfl, rfl, noW_idle _ hp, hW.2.2.2.2⟩⟩
  · obtain rfl := hR.readHandle h' n hp
    simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases rv with
    | idle => exact absurd hp (hR.2.2.2.1 _ n)
    | stopped => exact absurd hp (hR.2.2.2.1 _ n)
    | wait => exact dropW_meets h' hw n a W R hW hR hp
  · exact absurd hp (hW.2.2.2.1 h' ys)

/-- **Taking the writer's event** after a write of `xs`. -/
theorem takeW_spec (hr hw : Nat) (rv : RV) (a : CS) (xs W R : List Val) (e : Event)
    (hW : WInv hw (.wait xs) a W) (hR : RInv hr rv a R) (he : a.ew = some e) :
    RInv hr rv { a with ew := none } R ∧
      ((copyStatus e.payload = 0 ∧ WInv hw .idle { a with ew := none } (W ++ xs.take (copyCount e.payload))) ∨
       (copyStatus e.payload ≠ 0 ∧ a.c.rDropped = true ∧ WInv hw .idle { a with ew := none } W)) := by
  have hR' : RInv hr rv { a with ew := none } R := hR.frame'
  rcases hW.2.2 with ⟨-, hn, -⟩ | ⟨k, hk, hno, hs⟩ | ⟨hk, hno, hrd, hs⟩
  · rw [hn] at he
    cases he
  · rw [hk] at he
    cases he
    refine ⟨hR', Or.inl ⟨status_completed k, ?_⟩⟩
    rw [count_completed]
    exact ⟨hW.1, rfl, hW.2.1, hno, hs⟩
  · rw [hk] at he
    cases he
    exact ⟨hR', Or.inr ⟨status_dropped, hrd, hW.1, rfl, hW.2.1, hno, hs⟩⟩

/-- Dropping the readable end under a pending write. -/
theorem dropR_meets (hr hw : Nat) (a : CS) (xs W R : List Val) (wv : WV)
    (hR : RInv hr .idle a R) (hW : WInv hw wv a W) (hp : a.c.pend = .write hw xs) :
    WInv hw wv (a.dropRW hw) W ∧ RInv hr .stopped (a.dropRW hw) R := by
  cases wv with
  | idle => exact absurd hp (hW.2.2.2.1 _ xs)
  | closed => exact absurd hp (hW.2.2.2.1 _ xs)
  | wait ys =>
    have hsW : a.c.sent = W := by
      rcases hW.2.2 with ⟨-, -, hs⟩ | ⟨k, -, hn, -⟩ | ⟨-, hn, -, -⟩
      · exact hs
      · exact absurd hp (hn hw xs)
      · exact absurd hp (hn hw xs)
    exact ⟨⟨hW.1, hW.2.1, Or.inr (Or.inr ⟨rfl, noW_idle _ rfl, rfl, hsW⟩)⟩,
      ⟨rfl, rfl, rfl, noR_idle _ rfl, hR.2.2.2.2⟩⟩

/-! ## The reader's built-ins -/

/-- The rendezvous of a read with a pending write: both invariants after it. -/
theorem read_meets (hr hw : Nat) (a : CS) (k : Nat) (xs W R : List Val)
    (hR : RInv hr .idle a R) (hW : WInv hw (.wait xs) a W) (hp : a.c.pend = .write hw xs) :
    RInv hr .idle (a.metW hw k (xs.take k)) (R ++ xs.take k) ∧
      WInv hw (.wait xs) (a.metW hw k (xs.take k)) W := by
  have hsW : a.c.sent = W := by
    rcases hW.2.2 with ⟨-, -, hs⟩ | ⟨k, -, hn, -⟩ | ⟨-, hn, -, -⟩
    · exact hs
    · exact absurd hp (hn hw xs)
    · exact absurd hp (hn hw xs)
  have hR' : RInv hr .idle (a.metW hw k (xs.take k)) (R ++ xs.take k) :=
    ⟨hR.1, hR.2.1, hR.2.2.1, noR_idle _ rfl, by simp [CS.metW, hR.2.2.2.2]⟩
  have hW' : WInv hw (.wait xs) (a.metW hw k (xs.take k)) W :=
    ⟨hW.1, hW.2.1, Or.inr (Or.inl ⟨k, rfl, noW_idle _ rfl, by simp [CS.metW, hsW]⟩)⟩
  exact ⟨hR', hW'⟩

/-- The effect of a read on the reader: the three outcomes. -/
def ReadOut (hr : Nat) (a' : CS) (R : List Val) (r : Res) : Prop :=
  (∃ p ys, r = .read p ys ∧ copyStatus p = 0 ∧ RInv hr .idle a' (R ++ ys)) ∨
  (∃ p, r = .read p [] ∧ copyStatus p ≠ 0 ∧ a'.c.wDropped = true ∧ RInv hr .idle a' R) ∨
  (r = .nat blocked ∧ RInv hr .wait a' R)

/-- A read that finds no pending write. -/
theorem read_idle_case (hr hw n : Nat) (wv : WV) (a : CS) (W R : List Val)
    (hR : RInv hr .idle a R) (hW : WInv hw wv a W) (hp : a.c.pend = .idle) :
    (a.c.wDropped = true → WInv hw wv a W ∧ ReadOut hr a R (.read (packCopy .dropped 0) [])) ∧
    (a.c.wDropped = false →
      WInv hw wv (a.pendR hr n) W ∧ ReadOut hr (a.pendR hr n) R (.nat blocked)) := by
  refine ⟨fun hd => ⟨hW, Or.inr (Or.inl ⟨_, rfl, status_dropped, hd, hR⟩)⟩, fun _ => ?_⟩
  have hW' : WInv hw wv (a.pendR hr n) W :=
    hW.frame (noW_idle a hp) (noW_read _ hr n rfl) rfl rfl rfl id rfl
  exact ⟨hW', Or.inr (Or.inr ⟨rfl, hR.1, hR.2.2.1, Or.inl ⟨n, rfl, hR.2.1, hR.2.2.2.2⟩⟩)⟩

/-- A read that finds no pending write, from its result. -/
theorem read_idle_res (hr hw n : Nat) (wv : WV) (a a' : CS) (W R : List Val) (r : Res)
    (hR : RInv hr .idle a R) (hW : WInv hw wv a W) (hp : a.c.pend = .idle)
    (h : a.read hr hw n = some (a', r)) : WInv hw wv a' W ∧ ReadOut hr a' R r := by
  have hc := read_idle_case hr hw n wv a W R hR hW hp
  have he : a.read hr hw n = if a.c.wDropped then some (a, .read (packCopy .dropped 0) [])
      else some (a.pendR hr n, .nat blocked) := by simp [CS.read, hp]
  cases hd : a.c.wDropped
  · have hres : some (a.pendR hr n, Res.nat blocked) = some (a', r) := by
      rw [← h, he, hd]
      rfl
    obtain ⟨rfl, rfl⟩ : a.pendR hr n = a' ∧ Res.nat blocked = r := by simpa using hres
    exact hc.2 hd
  · have hres : some (a, Res.read (packCopy .dropped 0) []) = some (a', r) := by
      rw [← h, he, hd]
      rfl
    obtain ⟨rfl, rfl⟩ : a = a' ∧ Res.read (packCopy .dropped 0) [] = r := by simpa using hres
    exact hc.1 hd

/-- The pending write is the writer's issued write. -/
theorem WInv.pend_eq {hw : Nat} {ys xs : List Val} {a : CS} {W : List Val}
    (hW : WInv hw (.wait ys) a W) (hp : a.c.pend = .write hw xs) : ys = xs := by
  rcases hW.2.2 with ⟨hm, -, -⟩ | ⟨k, -, hn, -⟩ | ⟨-, hn, -, -⟩
  · rw [hp] at hm
    cases hm
    rfl
  · exact absurd hp (hn _ xs)
  · exact absurd hp (hn _ xs)

/-- A read that meets a pending write, from its result. -/
theorem read_write_res (hr hw h' n : Nat) (wv : WV) (a a' : CS) (xs W R : List Val) (r : Res)
    (hR : RInv hr .idle a R) (hW : WInv hw wv a W) (hp : a.c.pend = .write h' xs)
    (h : a.read hr hw n = some (a', r)) : WInv hw wv a' W ∧ ReadOut hr a' R r := by
  obtain rfl := hW.writeHandle h' xs hp
  cases wv with
  | idle => exact absurd hp (hW.2.2.2.1 _ xs)
  | closed => exact absurd hp (hW.2.2.2.1 _ xs)
  | wait ys =>
    obtain rfl : ys = xs := hW.pend_eq hp
    have hm := read_meets hr h' a (min n ys.length) ys W R hR hW hp
    have he : a.read hr h' n = some (a.metW h' (min n ys.length) (ys.take (min n ys.length)),
        .read (packCopy .completed (min n ys.length)) (ys.take (min n ys.length))) := by
      simp [CS.read, hp]
    obtain ⟨rfl, rfl⟩ : a.metW h' (min n ys.length) (ys.take (min n ys.length)) = a' ∧
        Res.read (packCopy .completed (min n ys.length)) (ys.take (min n ys.length)) = r := by
      simpa [he] using h
    exact ⟨hm.2, Or.inl ⟨_, _, rfl, status_completed _, hm.1⟩⟩

/-- **A read from the idle reader.** -/
theorem read_spec (hr hw n : Nat) (wv : WV) (a a' : CS) (W R : List Val) (r : Res)
    (hR : RInv hr .idle a R) (hW : WInv hw wv a W) (h : a.read hr hw n = some (a', r)) :
    WInv hw wv a' W ∧ ReadOut hr a' R r := by
  rcases hp : a.c.pend with _ | ⟨h', m⟩ | ⟨h', xs⟩
  · exact read_idle_res hr hw n wv a a' W R r hR hW hp h
  · exact absurd hp (hR.2.2.2.1 h' m)
  · exact read_write_res hr hw h' n wv a a' xs W R r hR hW hp h

/-- **Dropping the readable end** from the idle reader. -/
theorem dropR_spec (hr hw : Nat) (wv : WV) (a a' : CS) (W R : List Val) (r : Res)
    (hR : RInv hr .idle a R) (hW : WInv hw wv a W) (h : a.dropR hw = some (a', r)) :
    WInv hw wv a' W ∧ RInv hr .stopped a' R := by
  unfold CS.dropR at h
  rcases hp : a.c.pend with _ | ⟨h', n⟩ | ⟨h', xs⟩
  · simp only [hp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hW.frame (noW_idle a hp) (noW_idle _ hp) rfl rfl rfl (fun _ => rfl) rfl,
      ⟨rfl, rfl, rfl, noR_idle _ hp, hR.2.2.2.2⟩⟩
  · exact absurd hp (hR.2.2.2.1 h' n)
  · obtain rfl := hW.writeHandle h' xs hp
    simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dropR_meets hr h' a xs W R wv hR hW hp

/-- **Taking the reader's event** after a read. -/
theorem takeR_spec (hr hw : Nat) (wv : WV) (a : CS) (W R : List Val) (e : Event)
    (hR : RInv hr .wait a R) (hW : WInv hw wv a W) (he : a.er = some e) :
    WInv hw wv { a with er := none } W ∧
      ((copyStatus e.payload = 0 ∧ RInv hr .idle { a with er := none } (R ++ e.items)) ∨
       (copyStatus e.payload ≠ 0 ∧ a.c.wDropped = true ∧ RInv hr .idle { a with er := none } R)) := by
  have hW' : WInv hw wv { a with er := none } W := hW.frame'
  rcases hR.2.2 with ⟨-, -, hn, -⟩ | ⟨k, ys, hk, hno, hs⟩ | ⟨hk, hno, hwd, hs⟩
  · rw [hn] at he
    cases he
  · rw [hk] at he
    cases he
    exact ⟨hW', Or.inl ⟨status_completed k, hR.1, rfl, hR.2.1, hno, hs⟩⟩
  · rw [hk] at he
    cases he
    exact ⟨hW', Or.inr ⟨status_dropped, hwd, hR.1, rfl, hR.2.1, hno, hs⟩⟩

end Silmaril.Proofs.Wasm.Component.Streams.Proc
