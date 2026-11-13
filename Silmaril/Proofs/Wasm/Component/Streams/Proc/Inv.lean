module

public import Silmaril.Proofs.Wasm.Component.Streams.Proc.Chan
public import Silmaril.Proofs.Wasm.Component.Streams.Spec

/-!
# The pipeline invariant

`Inv T F s`: the store is `toStore A B`; channel `A` satisfies the channel invariant between the
producer (writer, view `pView`) and the transformer (reader, view `tR`), channel `B` between the
transformer (writer, view `tW`) and the consumer (reader, view `cView`); and the data of the three
components are linked:

* `PData`: the producer's transferred items `W_A`, followed by what it still has to write, are the
  input `F` (or a prefix of it once the reader has gone);
* `TLink`: the transformer's state is `T` fed with the items it has read, `R_A`, and the items it
  has written, `W_B`, followed by those it is writing, are `T`'s output so far (or the whole
  output `T.run R_A` once it stopped reading, which it does at the end of the input, `R_A = F`, or
  when `T` is done);
* `CData`: the consumer's accumulator is the items it has read, `R_B`.

`inv_init`, `pStep_inv`, `tStep_inv`, `cStep_inv`: the invariant holds initially and is preserved
by every step of every component.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Proc

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Proc
open Silmaril.Proofs.Wasm.Component.Streams.Spec

variable {σ : Type}

/-! ## Views and data -/

/-- The producer's view of channel `A`. -/
def pView : PPc → WV
  | .send _ | .close => .idle
  | .wait c _ => .wait c
  | .fin => .closed

/-- The transformer's view of channel `A`. -/
def tR : TPc σ → RV
  | .rd _ | .eoi _ | .wr _ (some _) | .wtW _ (some _) | .fault => .idle
  | .wtR _ => .wait
  | .wr _ none | .wtW _ none | .cl | .fin => .stopped

/-- The transformer's view of channel `B`. -/
def tW : TPc σ → WV
  | .rd _ | .wtR _ | .eoi _ | .wr _ _ | .cl | .fault => .idle
  | .wtW ys _ => .wait ys
  | .fin => .closed

/-- The consumer's view of channel `B`. -/
def cView : CPc → RV
  | .recv _ | .close _ => .idle
  | .wait _ => .wait
  | .fin _ => .stopped

/-- The producer's data. -/
def PData (F : List Val) : PPc → List Val → CS → Prop
  | .send cs, W, _ => W ++ cs.flatten = F
  | .wait c cs, W, _ => W ++ (c ++ cs.flatten) = F
  | .close, W, A => W <+: F ∧ A.c.rDropped = true
  | .fin, W, A => W <+: F ∧ (W = F ∨ A.c.rDropped = true)

/-- The transformer has stopped reading for a good reason. -/
def Stopped (T : Tr σ Val Val) (F R : List Val) : Prop :=
  R = F ∨ T.done (T.feed T.init R).1 = true

/-- The transformer's data. -/
def TLink (T : Tr σ Val Val) (F : List Val) : TPc σ → List Val → List Val → Prop
  | .rd s, R, W | .wtR s, R, W => s = (T.feed T.init R).1 ∧ W = (T.feed T.init R).2
  | .eoi s, R, W => s = (T.feed T.init R).1 ∧ W = (T.feed T.init R).2 ∧ R = F
  | .wr ys (some s), R, W | .wtW ys (some s), R, W =>
    s = (T.feed T.init R).1 ∧ W ++ ys = (T.feed T.init R).2
  | .wr ys none, R, W | .wtW ys none, R, W => W ++ ys = T.run R ∧ Stopped T F R
  | .cl, R, W | .fin, R, W => W = T.run R ∧ Stopped T F R
  | .fault, _, _ => False

/-- The consumer's data. -/
def CData : CPc → List Val → CS → Prop
  | .recv acc, R, _ | .wait acc, R, _ => acc = R
  | .close acc, R, B | .fin acc, R, B => acc = R ∧ B.c.wDropped = true

/-- The invariant at given channel states and data. -/
def InvAt (T : Tr σ Val Val) (F : List Val) (p : PPc) (t : TPc σ) (c : CPc) (A B : CS)
    (WA RA WB RB : List Val) : Prop :=
  WInv 2 (pView p) A WA ∧ RInv 1 (tR t) A RA ∧ WInv 4 (tW t) B WB ∧ RInv 3 (cView c) B RB ∧
    PData F p WA A ∧ TLink T F t RA WB ∧ CData c RB B

/-- **The pipeline invariant** for the input `F`. -/
def Inv (T : Tr σ Val Val) (F : List Val) (s : Sys σ) : Prop :=
  ∃ A B WA RA WB RB, s.st = toStore A B ∧ InvAt T F s.p s.t s.c A B WA RA WB RB

/-! ## Monotonicity of the data in the drop flags -/

theorem PData.mono {F : List Val} {p : PPc} {W : List Val} {A A' : CS} (h : PData F p W A)
    (hm : A.c.rDropped = true → A'.c.rDropped = true) : PData F p W A' := by
  cases p with
  | send cs => exact h
  | wait c cs => exact h
  | close => exact ⟨h.1, hm h.2⟩
  | fin => exact ⟨h.1, h.2.imp_right hm⟩

theorem CData.mono {c : CPc} {R : List Val} {B B' : CS} (h : CData c R B)
    (hm : B.c.wDropped = true → B'.c.wDropped = true) : CData c R B' := by
  cases c with
  | recv acc => exact h
  | wait acc => exact h
  | close acc => exact ⟨h.1, hm h.2⟩
  | fin acc => exact ⟨h.1, hm h.2⟩

theorem write_wDropped (hr hw : Nat) (a a' : CS) (xs : List Val) (r : Res)
    (h : a.write hr hw xs = some (a', r)) : a'.c.wDropped = a.c.wDropped := by
  unfold CS.write at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · cases h
  · split at h <;> (cases h; rfl)

theorem read_rDropped (hr hw n : Nat) (a a' : CS) (r : Res)
    (h : a.read hr hw n = some (a', r)) : a'.c.rDropped = a.c.rDropped := by
  unfold CS.read at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · cases h
  · split at h <;> (cases h; rfl)

theorem dropR_wDropped (hw : Nat) (a a' : CS) (r : Res) (h : a.dropR hw = some (a', r)) :
    a'.c.wDropped = a.c.wDropped := by
  unfold CS.dropR at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h
    rfl

theorem dropR_rDropped (hw : Nat) (a a' : CS) (r : Res) (h : a.dropR hw = some (a', r)) :
    a'.c.rDropped = true := by
  unfold CS.dropR at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h
    rfl

theorem dropW_rDropped (hr : Nat) (a a' : CS) (r : Res) (h : a.dropW hr = some (a', r)) :
    a'.c.rDropped = a.c.rDropped := by
  unfold CS.dropW at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h
    rfl

theorem dropW_wDropped (hr : Nat) (a a' : CS) (r : Res) (h : a.dropW hr = some (a', r)) :
    a'.c.wDropped = true := by
  unfold CS.dropW at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h
    rfl

/-! ## The initial state -/

theorem inv_init (T : Tr σ Val Val) (cs : List (List Val)) :
    Inv T cs.flatten { st := toStore {} {}, p := .send cs, t := .rd T.init, c := .recv [] } := by
  refine ⟨{}, {}, [], [], [], [], rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, noW_idle _ rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, noR_idle _ rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, noW_idle _ rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, noR_idle _ rfl, rfl⟩
  · exact List.nil_append _
  · exact ⟨rfl, rfl⟩

/-! ## Extracting abstract results -/

theorem onA_some {X : Type} {B : CS} {o : Option (CS × Res)} {g : Store × Res → X} {x : X}
    (h : (onA B o).map g = some x) : ∃ A' r, o = some (A', r) ∧ g (toStore A' B, r) = x := by
  cases o with
  | none => cases h
  | some p => exact ⟨p.1, p.2, rfl, by simpa [onA] using h⟩

theorem onB_some {X : Type} {A : CS} {o : Option (CS × Res)} {g : Store × Res → X} {x : X}
    (h : (onB A o).map g = some x) : ∃ B' r, o = some (B', r) ∧ g (toStore A B', r) = x := by
  cases o with
  | none => cases h
  | some p => exact ⟨p.1, p.2, rfl, by simpa [onB] using h⟩

/-! ## The producer -/

/-- The data after a copy of `k` items of `c`. -/
theorem pdata_after (F : List Val) (A : CS) (W c : List Val) (cs : List (List Val)) (k : Nat)
    (h : W ++ (c ++ cs.flatten) = F) :
    PData F (PPc.after c k cs) (W ++ c.take k) A ∧ pView (PPc.after c k cs) = .idle := by
  unfold PPc.after
  by_cases hd : c.drop k = []
  · have hc : c.take k = c := by
      have := List.take_append_drop k c
      rwa [hd, List.append_nil] at this
    simp only [hd, ↓reduceIte]
    exact ⟨by simpa [PData, hc] using h, rfl⟩
  · simp only [hd, ↓reduceIte]
    refine ⟨?_, rfl⟩
    show W ++ c.take k ++ (c.drop k :: cs).flatten = F
    rw [List.flatten_cons, List.append_assoc, ← List.append_assoc (c.take k),
      List.take_append_drop]
    exact h

theorem prefix_of_append {W X F : List Val} (h : W ++ X = F) : W <+: F := ⟨X, h⟩

/-- The producer's continuation after a copy, from the writer's new invariant. -/
theorem p_onCopy (T : Tr σ Val Val) (F : List Val) (t : TPc σ) (c' : CPc) (A' B : CS)
    (W RA WB RB c : List Val) (cs : List (List Val)) (q : Nat)
    (hF : W ++ (c ++ cs.flatten) = F) (hR : RInv 1 (tR t) A' RA) (hWB : WInv 4 (tW t) B WB)
    (hRB : RInv 3 (cView c') B RB) (hT : TLink T F t RA WB) (hC : CData c' RB B)
    (hout : (copyStatus q = 0 ∧ WInv 2 .idle A' (W ++ c.take (copyCount q))) ∨
      (copyStatus q ≠ 0 ∧ A'.c.rDropped = true ∧ WInv 2 .idle A' W)) :
    ∃ WA', InvAt T F (PPc.onCopy c cs q) t c' A' B WA' RA WB RB := by
  rcases hout with ⟨hs, hW⟩ | ⟨hs, hrd, hW⟩
  · obtain ⟨hP, hv⟩ := pdata_after F A' W c cs (copyCount q) hF
    have he : PPc.onCopy c cs q = PPc.after c (copyCount q) cs := by simp [PPc.onCopy, hs]
    rw [he]
    exact ⟨_, hv ▸ hW, hR, hWB, hRB, hP, hT, hC⟩
  · have he : PPc.onCopy c cs q = .close := by simp [PPc.onCopy, hs]
    rw [he]
    exact ⟨W, hW, hR, hWB, hRB, ⟨prefix_of_append hF, hrd⟩, hT, hC⟩

/-- The producer drops its writable end. -/
theorem p_dropW (t : TPc σ) (A B : CS) (WA RA : List Val) (st' : Store) (p' : PPc)
    (hWA : WInv 2 .idle A WA) (hRA : RInv 1 (tR t) A RA)
    (h : (step (toStore A B) (.streamDropW 2)).map (fun p => (p.1, PPc.fin)) = some (st', p')) :
    ∃ A', st' = toStore A' B ∧ p' = .fin ∧ RInv 1 (tR t) A' RA ∧ WInv 2 .closed A' WA ∧
      A'.c.rDropped = A.c.rDropped := by
  rw [dropW_A A B hWA.1 hRA.readHandle] at h
  obtain ⟨A', r, ho, hg⟩ := onA_some h
  obtain ⟨rfl, rfl⟩ : toStore A' B = st' ∧ PPc.fin = p' := by simpa using hg
  obtain ⟨hR', hW'⟩ := dropW_spec 1 2 (tR t) A A' WA RA r hWA hRA ho
  exact ⟨A', rfl, rfl, hR', hW', dropW_rDropped 1 A A' r ho⟩

/-- The producer writes a chunk. -/
theorem p_write (T : Tr σ Val Val) (F : List Val) (t : TPc σ) (c' : CPc) (A B : CS)
    (WA RA WB RB c : List Val) (cs : List (List Val)) (st' : Store) (p' : PPc)
    (hI : InvAt T F (.send (c :: cs)) t c' A B WA RA WB RB)
    (h : pStep (toStore A B) (.send (c :: cs)) = some (st', p')) :
    ∃ A' WA', st' = toStore A' B ∧ InvAt T F p' t c' A' B WA' RA WB RB := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  have e : step (toStore A B) (.streamWrite 2 c) = onA B (A.write 1 2 c) :=
    write_A A B c hWA.1 hRA.readHandle
  rcases ho : A.write 1 2 c with _ | ⟨A', r⟩
  · exact absurd h (by simp [pStep, e, ho, onA])
  obtain ⟨hR', hout⟩ := write_spec 1 2 (tR t) A A' c WA RA r hWA hRA ho
  have hF : WA ++ (c ++ cs.flatten) = F := by simpa [PData] using hP
  rcases hout with ⟨k, rfl, hW'⟩ | ⟨rfl, hrd, hW'⟩ | ⟨rfl, hW'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A' B = st' ∧ PPc.onCopy c cs (packCopy .completed k) = p' := by
      simpa [pStep, e, ho, onA, packCopy_ne_blocked] using h
    obtain ⟨WA', hI'⟩ := p_onCopy T F t c' A' B WA RA WB RB c cs _ hF hR' hWB hRB hT hC
      (Or.inl ⟨status_completed k, by rw [count_completed]; exact hW'⟩)
    exact ⟨A', WA', rfl, hI'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A' B = st' ∧ PPc.onCopy c cs (packCopy .dropped 0) = p' := by
      simpa [pStep, e, ho, onA, packCopy_ne_blocked] using h
    obtain ⟨WA', hI'⟩ := p_onCopy T F t c' A' B WA RA WB RB c cs _ hF hR' hWB hRB hT hC
      (Or.inr ⟨status_dropped, hrd, hW'⟩)
    exact ⟨A', WA', rfl, hI'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A' B = st' ∧ PPc.wait c cs = p' := by
      simpa [pStep, e, ho, onA] using h
    exact ⟨A', WA, rfl, hW', hR', hWB, hRB, hF, hT, hC⟩

/-- The producer takes the event of its write. -/
theorem p_wait (T : Tr σ Val Val) (F : List Val) (t : TPc σ) (c' : CPc) (A B : CS)
    (WA RA WB RB c : List Val) (cs : List (List Val)) (st' : Store) (p' : PPc)
    (hI : InvAt T F (.wait c cs) t c' A B WA RA WB RB)
    (h : pStep (toStore A B) (.wait c cs) = some (st', p')) :
    ∃ A' WA', st' = toStore A' B ∧ InvAt T F p' t c' A' B WA' RA WB RB := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  rcases he : A.ew with _ | e
  · simp [pStep, wait6_none A B he] at h
  obtain rfl : st' = toStore { A with ew := none } B := by
    simp [pStep, wait6_A A B e hWA.1 he] at h
    exact h.1.symm
  obtain rfl : p' = PPc.onCopy c cs e.payload := by
    simp [pStep, wait6_A A B e hWA.1 he] at h
    exact h.symm
  obtain ⟨hR', hout⟩ := takeW_spec 1 2 (tR t) A c WA RA e hWA hRA he
  obtain ⟨WA', hI'⟩ := p_onCopy T F t c' _ B WA RA WB RB c cs e.payload hP hR' hWB hRB hT hC hout
  exact ⟨_, WA', rfl, hI'⟩

/-- **The producer's steps preserve the invariant.** -/
theorem pStep_inv (T : Tr σ Val Val) (F : List Val) (p : PPc) (t : TPc σ) (c' : CPc)
    (A B : CS) (WA RA WB RB : List Val) (st' : Store) (p' : PPc)
    (hI : InvAt T F p t c' A B WA RA WB RB) (h : pStep (toStore A B) p = some (st', p')) :
    ∃ A' WA', st' = toStore A' B ∧ InvAt T F p' t c' A' B WA' RA WB RB := by
  cases p with
  | send cs =>
    cases cs with
    | nil =>
      obtain ⟨A', rfl, rfl, hR', hW', -⟩ := p_dropW t A B WA RA st' p' hI.1 hI.2.1 h
      have hF : WA = F := by simpa [PData] using hI.2.2.2.2.1
      exact ⟨A', WA, rfl, hW', hR', hI.2.2.1, hI.2.2.2.1,
        ⟨hF ▸ List.prefix_refl _, Or.inl hF⟩, hI.2.2.2.2.2⟩
    | cons c cs => exact p_write T F t c' A B WA RA WB RB c cs st' p' hI h
  | wait c cs => exact p_wait T F t c' A B WA RA WB RB c cs st' p' hI h
  | close =>
    obtain ⟨A', rfl, rfl, hR', hW', hrd⟩ := p_dropW t A B WA RA st' p' hI.1 hI.2.1 h
    exact ⟨A', WA, rfl, hW', hR', hI.2.2.1, hI.2.2.2.1,
      ⟨hI.2.2.2.2.1.1, Or.inr (hrd ▸ hI.2.2.2.2.1.2)⟩, hI.2.2.2.2.2⟩
  | fin => cases h

/-! ## The consumer -/

/-- The consumer's continuation after a read, from the reader's new invariant. -/
theorem c_onRead (T : Tr σ Val Val) (F : List Val) (p : PPc) (t : TPc σ) (A B' : CS)
    (WA RA WB RB acc ys : List Val) (q : Nat) (hacc : acc = RB)
    (hWA : WInv 2 (pView p) A WA) (hRA : RInv 1 (tR t) A RA) (hW : WInv 4 (tW t) B' WB)
    (hP : PData F p WA A) (hT : TLink T F t RA WB)
    (hout : (copyStatus q = 0 ∧ RInv 3 .idle B' (RB ++ ys)) ∨
      (copyStatus q ≠ 0 ∧ B'.c.wDropped = true ∧ RInv 3 .idle B' RB)) :
    ∃ RB', InvAt T F p t (CPc.onRead acc q ys) A B' WA RA WB RB' := by
  rcases hout with ⟨hs, hR⟩ | ⟨hs, hwd, hR⟩
  · have he : CPc.onRead acc q ys = .recv (acc ++ ys) := by simp [CPc.onRead, hs]
    rw [he]
    exact ⟨RB ++ ys, hWA, hRA, hW, hR, hP, hT, by rw [hacc]; rfl⟩
  · have he : CPc.onRead acc q ys = .close acc := by simp [CPc.onRead, hs]
    rw [he]
    exact ⟨RB, hWA, hRA, hW, hR, hP, hT, hacc, hwd⟩

/-- The consumer reads. -/
theorem c_read (T : Tr σ Val Val) (F : List Val) (p : PPc) (t : TPc σ) (A B : CS)
    (WA RA WB RB acc : List Val) (n : Nat) (st' : Store) (c' : CPc)
    (hI : InvAt T F p t (.recv acc) A B WA RA WB RB)
    (h : cStep n (toStore A B) (.recv acc) = some (st', c')) :
    ∃ B' RB', st' = toStore A B' ∧ InvAt T F p t c' A B' WA RA WB RB' := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  have e : step (toStore A B) (.streamRead 3 n) = onB A (B.read 3 4 n) :=
    read_B A B n hRB.1 hWB.writeHandle
  rcases ho : B.read 3 4 n with _ | ⟨B', r⟩
  · exact absurd h (by simp [cStep, e, ho, onB])
  obtain ⟨hW', hout⟩ := read_spec 3 4 n (tW t) B B' WB RB r hRB hWB ho
  rcases hout with ⟨q, ys, rfl, hs, hR'⟩ | ⟨q, rfl, hs, hwd, hR'⟩ | ⟨rfl, hR'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A B' = st' ∧ CPc.onRead acc q ys = c' := by
      simpa [cStep, e, ho, onB] using h
    obtain ⟨RB', hI'⟩ := c_onRead T F p t A B' WA RA WB RB acc ys q hC hWA hRA hW' hP hT
      (Or.inl ⟨hs, hR'⟩)
    exact ⟨B', RB', rfl, hI'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A B' = st' ∧ CPc.onRead acc q [] = c' := by
      simpa [cStep, e, ho, onB] using h
    obtain ⟨RB', hI'⟩ := c_onRead T F p t A B' WA RA WB RB acc [] q hC hWA hRA hW' hP hT
      (Or.inr ⟨hs, hwd, hR'⟩)
    exact ⟨B', RB', rfl, hI'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A B' = st' ∧ CPc.wait acc = c' := by
      simpa [cStep, e, ho, onB] using h
    exact ⟨B', RB, rfl, hWA, hRA, hW', hR', hP, hT, hC⟩

/-- The consumer takes the event of its read. -/
theorem c_wait (T : Tr σ Val Val) (F : List Val) (p : PPc) (t : TPc σ) (A B : CS)
    (WA RA WB RB acc : List Val) (n : Nat) (st' : Store) (c' : CPc)
    (hI : InvAt T F p t (.wait acc) A B WA RA WB RB)
    (h : cStep n (toStore A B) (.wait acc) = some (st', c')) :
    ∃ B' RB', st' = toStore A B' ∧ InvAt T F p t c' A B' WA RA WB RB' := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  rcases he : B.er with _ | e
  · exact absurd h (by simp [cStep, wait7_none A B he])
  have hs : some (toStore A { B with er := none }, CPc.onRead acc e.payload e.items) =
      some (st', c') := by
    simpa [cStep, wait7_B A B e hRB.1 he] using h
  obtain ⟨rfl, rfl⟩ : toStore A { B with er := none } = st' ∧
      CPc.onRead acc e.payload e.items = c' := by simpa using hs
  obtain ⟨hW', hout⟩ := takeR_spec 3 4 (tW t) B WB RB e hRB hWB he
  obtain ⟨RB', hI'⟩ :=
    c_onRead T F p t A _ WA RA WB RB acc e.items e.payload hC hWA hRA hW' hP hT hout
  exact ⟨_, RB', rfl, hI'⟩

/-- The consumer drops its readable end. -/
theorem c_close (T : Tr σ Val Val) (F : List Val) (p : PPc) (t : TPc σ) (A B : CS)
    (WA RA WB RB acc : List Val) (n : Nat) (st' : Store) (c' : CPc)
    (hI : InvAt T F p t (.close acc) A B WA RA WB RB)
    (h : cStep n (toStore A B) (.close acc) = some (st', c')) :
    ∃ B' RB', st' = toStore A B' ∧ InvAt T F p t c' A B' WA RA WB RB' := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  have h' : (onB A (B.dropR 4)).map (fun q => (q.1, CPc.fin acc)) = some (st', c') := by
    rw [← dropR_B A B hRB.1 hWB.writeHandle]
    exact h
  obtain ⟨B', r, ho, hg⟩ := onB_some h'
  obtain ⟨rfl, rfl⟩ : toStore A B' = st' ∧ CPc.fin acc = c' := by simpa using hg
  obtain ⟨hW', hR'⟩ := dropR_spec 3 4 (tW t) B B' WB RB r hRB hWB ho
  have hwd : B'.c.wDropped = true := by rw [dropR_wDropped 4 B B' r ho]; exact hC.2
  exact ⟨B', RB, rfl, hWA, hRA, hW', hR', hP, hT, hC.1, hwd⟩

/-- **The consumer's steps preserve the invariant.** -/
theorem cStep_inv (T : Tr σ Val Val) (F : List Val) (p : PPc) (t : TPc σ) (c : CPc)
    (A B : CS) (WA RA WB RB : List Val) (n : Nat) (st' : Store) (c' : CPc)
    (hI : InvAt T F p t c A B WA RA WB RB) (h : cStep n (toStore A B) c = some (st', c')) :
    ∃ B' RB', st' = toStore A B' ∧ InvAt T F p t c' A B' WA RA WB RB' := by
  cases c with
  | recv acc => exact c_read T F p t A B WA RA WB RB acc n st' c' hI h
  | wait acc => exact c_wait T F p t A B WA RA WB RB acc n st' c' hI h
  | close acc => exact c_close T F p t A B WA RA WB RB acc n st' c' hI h
  | fin acc => cases h

/-! ## The transformer -/

theorem pView_closed {p : PPc} (h : pView p = .closed) : p = .fin := by
  cases p <;> first | rfl | cases h

theorem cView_stopped {c : CPc} (h : cView c = .stopped) : ∃ acc, c = .fin acc := by
  cases c with
  | fin acc => exact ⟨acc, rfl⟩
  | _ => cases h

/-- **At the end of the input the transformer has read all of it.** -/
theorem eoi_full (F : List Val) (p : PPc) (A : CS) (WA RA : List Val)
    (hW : WInv 2 (pView p) A WA) (hR : RInv 1 .idle A RA) (hwd : A.c.wDropped = true)
    (hP : PData F p WA A) : RA = F := by
  obtain rfl := pView_closed (hW.closed_of_wDropped hwd)
  have hWF : WA = F := hP.2.resolve_right (by rw [hR.2.2.1]; decide)
  have hsW : A.c.sent = WA := hW.2.2.2.2
  have hsR : A.c.sent = RA := hR.2.2.2.2
  rw [← hsR, hsW, hWF]

/-- The consumer is not finished while the transformer may still write. -/
theorem consumer_live {t : TPc σ} {c : CPc} {B : CS} {WB RB : List Val}
    (hW : WInv 4 (tW t) B WB) (hwd : (tW t = .idle ∨ ∃ ys, tW t = .wait ys))
    (hR : RInv 3 (cView c) B RB) (hC : CData c RB B) (hrd : B.c.rDropped = true) : False := by
  obtain ⟨acc, rfl⟩ := cView_stopped (hR.stopped_of_rDropped hrd)
  rcases hwd with he | ⟨ys, he⟩
  · rw [he] at hW
    exact absurd hC.2 (by rw [hW.2.2.1]; decide)
  · rw [he] at hW
    exact absurd hC.2 (by rw [hW.2.1]; decide)

/-- Feeding more items after the ones read. -/
theorem feed_more (T : Tr σ Val Val) (R ys : List Val) :
    (T.feed (T.feed T.init R).1 ys).1 = (T.feed T.init (R ++ ys)).1 ∧
      (T.feed T.init R).2 ++ (T.feed (T.feed T.init R).1 ys).2 = (T.feed T.init (R ++ ys)).2 := by
  rw [feed_append]
  exact ⟨rfl, rfl⟩

/-- The transformer's continuation after a read, from the reader's new invariant. -/
theorem t_onRead (T : Tr σ Val Val) (F : List Val) (p : PPc) (c : CPc) (A' B : CS)
    (WA RA WB RB ys : List Val) (s0 : σ) (q : Nat)
    (hl : s0 = (T.feed T.init RA).1 ∧ WB = (T.feed T.init RA).2)
    (hWA : WInv 2 (pView p) A' WA) (hWB : WInv 4 .idle B WB) (hRB : RInv 3 (cView c) B RB)
    (hP : PData F p WA A') (hC : CData c RB B)
    (hout : (copyStatus q = 0 ∧ RInv 1 .idle A' (RA ++ ys)) ∨
      (copyStatus q ≠ 0 ∧ A'.c.wDropped = true ∧ RInv 1 .idle A' RA)) :
    ∃ RA', InvAt T F p (TPc.onRead T s0 q ys) c A' B WA RA' WB RB := by
  obtain ⟨rfl, rfl⟩ := hl
  rcases hout with ⟨hs, hR⟩ | ⟨hs, hwd, hR⟩
  · have he : TPc.onRead T (T.feed T.init RA).1 q ys =
        .wr (T.feed (T.feed T.init RA).1 ys).2 (some (T.feed (T.feed T.init RA).1 ys).1) := by
      simp [TPc.onRead, hs]
    rw [he]
    obtain ⟨h1, h2⟩ := feed_more T RA ys
    exact ⟨RA ++ ys, hWA, hR, hWB, hRB, hP, ⟨h1, h2⟩, hC⟩
  · have he : TPc.onRead T (T.feed T.init RA).1 q ys = .eoi (T.feed T.init RA).1 := by
      simp [TPc.onRead, hs]
    rw [he]
    exact ⟨RA, hWA, hR, hWB, hRB, hP, ⟨rfl, rfl, eoi_full F p A' WA RA hWA hR hwd hP⟩, hC⟩

/-- The transformer drops its readable end (when `T` is done, or at the end of the input). -/
theorem t_dropR (T : Tr σ Val Val) (F : List Val) (p : PPc) (c : CPc) (A B : CS)
    (WA RA WB RB : List Val) (s0 : σ) (st' : Store) (t' : TPc σ)
    (hWA : WInv 2 (pView p) A WA) (hRA : RInv 1 .idle A RA) (hWB : WInv 4 .idle B WB)
    (hRB : RInv 3 (cView c) B RB) (hP : PData F p WA A) (hC : CData c RB B)
    (hl : s0 = (T.feed T.init RA).1 ∧ WB = (T.feed T.init RA).2) (hs : Stopped T F RA)
    (h : (step (toStore A B) (.streamDropR 1)).map (fun q => (q.1, TPc.wr (T.flush s0) none)) =
      some (st', t')) :
    ∃ A', st' = toStore A' B ∧ InvAt T F p t' c A' B WA RA WB RB := by
  rw [dropR_A A B hRA.1 hWA.writeHandle] at h
  obtain ⟨A', r, ho, hg⟩ := onA_some h
  obtain ⟨rfl, rfl⟩ : toStore A' B = st' ∧ TPc.wr (T.flush s0) none = t' := by simpa using hg
  obtain ⟨hW', hR'⟩ := dropR_spec 1 2 (pView p) A A' WA RA r hRA hWA ho
  have hrun : WB ++ T.flush s0 = T.run RA := by rw [hl.1, hl.2]; rfl
  exact ⟨A', rfl, hW', hR', hWB, hRB, hP.mono (fun _ => dropR_rDropped 2 A A' r ho),
    ⟨hrun, hs⟩, hC⟩

/-- The transformer reads (or stops when `T` is done). -/
theorem t_rd (T : Tr σ Val Val) (N : Nat) (F : List Val) (p : PPc) (c : CPc) (A B : CS)
    (WA RA WB RB : List Val) (s0 : σ) (st' : Store) (t' : TPc σ)
    (hI : InvAt T F p (.rd s0) c A B WA RA WB RB)
    (h : tStep T N (toStore A B) (.rd s0) = some (st', t')) :
    ∃ A' RA', st' = toStore A' B ∧ InvAt T F p t' c A' B WA RA' WB RB := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  by_cases hd : T.done s0 = true
  · have h' : (step (toStore A B) (.streamDropR 1)).map
        (fun q => (q.1, TPc.wr (T.flush s0) none)) = some (st', t') := by simpa [tStep, hd] using h
    obtain ⟨A', hst, hI'⟩ := t_dropR T F p c A B WA RA WB RB s0 st' t' hWA hRA hWB hRB hP hC hT
      (Or.inr (hT.1 ▸ hd)) h'
    exact ⟨A', RA, hst, hI'⟩
  have e : step (toStore A B) (.streamRead 1 N) = onA B (A.read 1 2 N) :=
    read_A A B N hRA.1 hWA.writeHandle
  rcases ho : A.read 1 2 N with _ | ⟨A', r⟩
  · exact absurd h (by simp [tStep, hd, e, ho, onA])
  obtain ⟨hW', hout⟩ := read_spec 1 2 N (pView p) A A' WA RA r hRA hWA ho
  have hP' : PData F p WA A' := hP.mono (fun h => (read_rDropped 1 2 N A A' r ho).trans h)
  rcases hout with ⟨q, ys, rfl, hs, hR'⟩ | ⟨q, rfl, hs, hwd, hR'⟩ | ⟨rfl, hR'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A' B = st' ∧ TPc.onRead T s0 q ys = t' := by
      simpa [tStep, hd, e, ho, onA] using h
    obtain ⟨RA', hI'⟩ := t_onRead T F p c A' B WA RA WB RB ys s0 q hT hW' hWB hRB hP' hC
      (Or.inl ⟨hs, hR'⟩)
    exact ⟨A', RA', rfl, hI'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A' B = st' ∧ TPc.onRead T s0 q [] = t' := by
      simpa [tStep, hd, e, ho, onA] using h
    obtain ⟨RA', hI'⟩ := t_onRead T F p c A' B WA RA WB RB [] s0 q hT hW' hWB hRB hP' hC
      (Or.inr ⟨hs, hwd, hR'⟩)
    exact ⟨A', RA', rfl, hI'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A' B = st' ∧ TPc.wtR s0 = t' := by
      simpa [tStep, hd, e, ho, onA] using h
    exact ⟨A', RA, rfl, hW', hR', hWB, hRB, hP', hT, hC⟩

/-- The transformer takes the event of its read. -/
theorem t_wtR (T : Tr σ Val Val) (N : Nat) (F : List Val) (p : PPc) (c : CPc) (A B : CS)
    (WA RA WB RB : List Val) (s0 : σ) (st' : Store) (t' : TPc σ)
    (hI : InvAt T F p (.wtR s0) c A B WA RA WB RB)
    (h : tStep T N (toStore A B) (.wtR s0) = some (st', t')) :
    ∃ A' RA', st' = toStore A' B ∧ InvAt T F p t' c A' B WA RA' WB RB := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  rcases he : A.er with _ | e
  · exact absurd h (by simp [tStep, wait5_none A B he hWB.2.1])
  have hs : some (toStore { A with er := none } B, TPc.onRead T s0 e.payload e.items) =
      some (st', t') := by
    simpa [tStep, wait5_A A B e hRA.1 he] using h
  obtain ⟨rfl, rfl⟩ : toStore { A with er := none } B = st' ∧
      TPc.onRead T s0 e.payload e.items = t' := by simpa using hs
  obtain ⟨hW', hout⟩ := takeR_spec 1 2 (pView p) A WA RA e hRA hWA he
  obtain ⟨RA', hI'⟩ :=
    t_onRead T F p c _ B WA RA WB RB e.items s0 e.payload hT hW' hWB hRB (hP.mono id) hC hout
  exact ⟨_, RA', rfl, hI'⟩

/-- The written items move from the pending ones to the transferred ones. -/
theorem tlink_shift (T : Tr σ Val Val) (F RA WB ys : List Val) (next : Option σ) (k : Nat)
    (h : TLink T F (.wr ys next) RA WB) : TLink T F (.wr (ys.drop k) next) RA (WB ++ ys.take k) := by
  have hc : WB ++ ys.take k ++ ys.drop k = WB ++ ys := by
    rw [List.append_assoc, List.take_append_drop]
  cases next with
  | some s => exact ⟨h.1, hc.trans h.2⟩
  | none => exact ⟨hc.trans h.1, h.2⟩

theorem tlink_wtW (T : Tr σ Val Val) (F RA WB ys : List Val) (next : Option σ) :
    TLink T F (.wtW ys next) RA WB ↔ TLink T F (.wr ys next) RA WB := by
  cases next <;> exact Iff.rfl

theorem tR_wr (ys zs : List Val) (next : Option σ) : tR (.wr ys next) = tR (.wtW zs next) := by
  cases next <;> rfl

/-- The transformer's continuation after a write, from the writer's new invariant. -/
theorem t_onWrite (T : Tr σ Val Val) (F : List Val) (p : PPc) (c : CPc) (A B' : CS)
    (WA RA WB RB ys : List Val) (next : Option σ) (q : Nat)
    (hWA : WInv 2 (pView p) A WA) (hRA : RInv 1 (tR (.wr ys next)) A RA)
    (hRB : RInv 3 (cView c) B' RB) (hP : PData F p WA A) (hT : TLink T F (.wr ys next) RA WB)
    (hC : CData c RB B')
    (hout : copyStatus q = 0 ∧ WInv 4 .idle B' (WB ++ ys.take (copyCount q))) :
    ∃ WB', InvAt T F p (TPc.onWrite ys next q) c A B' WA RA WB' RB := by
  have he : TPc.onWrite ys next q = .wr (ys.drop (copyCount q)) next := by
    simp [TPc.onWrite, hout.1]
  rw [he]
  refine ⟨_, hWA, ?_, hout.2, hRB, hP, tlink_shift T F RA WB ys next _ hT, hC⟩
  rw [tR_wr _ ys]
  rw [tR_wr _ ys] at hRA
  exact hRA

/-- The internal step after a finished write. -/
theorem t_wr_nil (T : Tr σ Val Val) (N : Nat) (F : List Val) (p : PPc) (c : CPc) (A B : CS)
    (WA RA WB RB : List Val) (next : Option σ) (st' : Store) (t' : TPc σ)
    (hI : InvAt T F p (.wr [] next) c A B WA RA WB RB)
    (h : tStep T N (toStore A B) (.wr [] next) = some (st', t')) :
    ∃ A' B' RA' WB', st' = toStore A' B' ∧ InvAt T F p t' c A' B' WA RA' WB' RB := by
  obtain ⟨rfl, rfl⟩ : toStore A B = st' ∧ TPc.resume next = t' := by
    simpa [tStep] using h
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  refine ⟨A, B, RA, WB, rfl, ?_⟩
  cases next with
  | some s0 => exact ⟨hWA, hRA, hWB, hRB, hP, ⟨hT.1, by simpa using hT.2⟩, hC⟩
  | none => exact ⟨hWA, hRA, hWB, hRB, hP, ⟨by simpa using hT.1, hT.2⟩, hC⟩

/-- A write that reports `DROPPED` leaves the channel unchanged. -/
theorem write_rDropped_drop (hr hw : Nat) (a a' : CS) (xs : List Val)
    (h : a.write hr hw xs = some (a', .nat (packCopy .dropped 0))) : a.c.rDropped = a'.c.rDropped := by
  unfold CS.write at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq, Res.nat.injEq] at h
      exact absurd h.2 (by simp [packCopy, CopyResult.toNat])
    · cases h
  · split at h
    · cases h
      rfl
    · simp only [Option.some.injEq, Prod.mk.injEq, Res.nat.injEq] at h
      exact absurd h.2 (by simp [packCopy, CopyResult.toNat, blocked])

/-- The transformer drops its writable end. -/
theorem t_cl (T : Tr σ Val Val) (N : Nat) (F : List Val) (p : PPc) (c : CPc) (A B : CS)
    (WA RA WB RB : List Val) (st' : Store) (t' : TPc σ)
    (hI : InvAt T F p .cl c A B WA RA WB RB)
    (h : tStep T N (toStore A B) .cl = some (st', t')) :
    ∃ B', st' = toStore A B' ∧ InvAt T F p t' c A B' WA RA WB RB := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  have h' : (onB A (B.dropW 3)).map (fun q => (q.1, (TPc.fin : TPc σ))) = some (st', t') := by
    rw [← dropW_B A B hWB.1 hRB.readHandle]
    exact h
  obtain ⟨B', r, ho, hg⟩ := onB_some h'
  obtain ⟨rfl, rfl⟩ : toStore A B' = st' ∧ (TPc.fin : TPc σ) = t' := by simpa using hg
  obtain ⟨hR', hW'⟩ := dropW_spec 3 4 (cView c) B B' WB RB r hWB hRB ho
  exact ⟨B', rfl, hWA, hRA, hW', hR', hP, hT, hC.mono (fun _ => dropW_wDropped 3 B B' r ho)⟩

theorem tW_wr (ys : List Val) (next : Option σ) : tW (.wr ys next) = .idle := by
  cases next <;> rfl

/-- The transformer writes. -/
theorem t_wr (T : Tr σ Val Val) (N : Nat) (F : List Val) (p : PPc) (c : CPc) (A B : CS)
    (WA RA WB RB : List Val) (y : Val) (ys : List Val) (next : Option σ) (st' : Store)
    (t' : TPc σ) (hI : InvAt T F p (.wr (y :: ys) next) c A B WA RA WB RB)
    (h : tStep T N (toStore A B) (.wr (y :: ys) next) = some (st', t')) :
    ∃ B' WB', st' = toStore A B' ∧ InvAt T F p t' c A B' WA RA WB' RB := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  have hWB' : WInv 4 .idle B WB := tW_wr (y :: ys) next ▸ hWB
  have e : step (toStore A B) (.streamWrite 4 (y :: ys)) = onB A (B.write 3 4 (y :: ys)) :=
    write_B A B _ hWB'.1 hRB.readHandle
  rcases ho : B.write 3 4 (y :: ys) with _ | ⟨B', r⟩
  · exact absurd h (by simp [tStep, e, ho, onB])
  obtain ⟨hR', hout⟩ := write_spec 3 4 (cView c) B B' (y :: ys) WB RB r hWB' hRB ho
  have hC' : CData c RB B' := hC.mono (fun h => (write_wDropped 3 4 B B' _ r ho).trans h)
  rcases hout with ⟨k, rfl, hW'⟩ | ⟨rfl, hrd, -⟩ | ⟨rfl, hW'⟩
  · obtain ⟨rfl, rfl⟩ : toStore A B' = st' ∧ TPc.onWrite (y :: ys) next (packCopy .completed k) = t' := by
      simpa [tStep, e, ho, onB, packCopy_ne_blocked] using h
    obtain ⟨WB', hI'⟩ := t_onWrite T F p c A B' WA RA WB RB (y :: ys) next _ hWA hRA hR' hP hT hC'
      ⟨status_completed k, by rw [count_completed]; exact hW'⟩
    exact ⟨B', WB', rfl, hI'⟩
  · exact (consumer_live hWB (Or.inl (tW_wr (y :: ys) next)) hRB hC (by
      rw [write_rDropped_drop 3 4 B B' _ ho]; exact hrd)).elim
  · obtain ⟨rfl, rfl⟩ : toStore A B' = st' ∧ TPc.wtW (y :: ys) next = t' := by
      simpa [tStep, e, ho, onB] using h
    exact ⟨B', WB, rfl, hWA, (tR_wr (y :: ys) (y :: ys) next) ▸ hRA, hW', hR', hP,
      (tlink_wtW T F RA WB (y :: ys) next).2 hT, hC'⟩

/-- The transformer takes the event of its write. -/
theorem t_wtW (T : Tr σ Val Val) (N : Nat) (F : List Val) (p : PPc) (c : CPc) (A B : CS)
    (WA RA WB RB : List Val) (ys : List Val) (next : Option σ) (st' : Store)
    (t' : TPc σ) (hI : InvAt T F p (.wtW ys next) c A B WA RA WB RB)
    (h : tStep T N (toStore A B) (.wtW ys next) = some (st', t')) :
    ∃ B' WB', st' = toStore A B' ∧ InvAt T F p t' c A B' WA RA WB' RB := by
  obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
  have hAe : A.er = none := by
    cases next with
    | some _ => exact hRA.2.1
    | none => exact hRA.2.1
  rcases he : B.ew with _ | e
  · exact absurd h (by simp [tStep, wait5_none A B hAe he])
  have hs : some (toStore A { B with ew := none }, TPc.onWrite ys next e.payload) =
      some (st', t') := by
    simpa [tStep, wait5_B A B e hAe hWB.1 he] using h
  obtain ⟨rfl, rfl⟩ : toStore A { B with ew := none } = st' ∧
      TPc.onWrite ys next e.payload = t' := by simpa using hs
  obtain ⟨hR', hout⟩ := takeW_spec 3 4 (cView c) B ys WB RB e hWB hRB he
  rcases hout with hok | ⟨-, hrd, -⟩
  · obtain ⟨WB', hI'⟩ := t_onWrite T F p c A _ WA RA WB RB ys next e.payload hWA
      ((tR_wr ys ys next).symm ▸ hRA) hR' hP ((tlink_wtW T F RA WB ys next).1 hT) (hC.mono id) hok
    exact ⟨_, WB', rfl, hI'⟩
  · exact (consumer_live hWB (Or.inr ⟨ys, rfl⟩) hRB hC hrd).elim

/-- **The transformer's steps preserve the invariant.** -/
theorem tStep_inv (T : Tr σ Val Val) (N : Nat) (F : List Val) (p : PPc) (t : TPc σ) (c : CPc)
    (A B : CS) (WA RA WB RB : List Val) (st' : Store) (t' : TPc σ)
    (hI : InvAt T F p t c A B WA RA WB RB) (h : tStep T N (toStore A B) t = some (st', t')) :
    ∃ A' B' RA' WB', st' = toStore A' B' ∧ InvAt T F p t' c A' B' WA RA' WB' RB := by
  cases t with
  | rd s0 =>
    obtain ⟨A', RA', hst, hI'⟩ := t_rd T N F p c A B WA RA WB RB s0 st' t' hI h
    exact ⟨A', B, RA', WB, hst, hI'⟩
  | wtR s0 =>
    obtain ⟨A', RA', hst, hI'⟩ := t_wtR T N F p c A B WA RA WB RB s0 st' t' hI h
    exact ⟨A', B, RA', WB, hst, hI'⟩
  | eoi s0 =>
    obtain ⟨hWA, hRA, hWB, hRB, hP, hT, hC⟩ := hI
    obtain ⟨A', hst, hI'⟩ := t_dropR T F p c A B WA RA WB RB s0 st' t' hWA hRA hWB hRB hP hC
      ⟨hT.1, hT.2.1⟩ (Or.inl hT.2.2) h
    exact ⟨A', B, RA, WB, hst, hI'⟩
  | wr ys next =>
    cases ys with
    | nil => exact t_wr_nil T N F p c A B WA RA WB RB next st' t' hI h
    | cons y ys =>
      obtain ⟨B', WB', hst, hI'⟩ := t_wr T N F p c A B WA RA WB RB y ys next st' t' hI h
      exact ⟨A, B', RA, WB', hst, hI'⟩
  | wtW ys next =>
    obtain ⟨B', WB', hst, hI'⟩ := t_wtW T N F p c A B WA RA WB RB ys next st' t' hI h
    exact ⟨A, B', RA, WB', hst, hI'⟩
  | cl =>
    obtain ⟨B', hst, hI'⟩ := t_cl T N F p c A B WA RA WB RB st' t' hI h
    exact ⟨A, B', RA, WB, hst, hI'⟩
  | fin => cases h
  | fault => cases h

end Silmaril.Proofs.Wasm.Component.Streams.Proc
