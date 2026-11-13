module

public import Silmaril.Wasi.Runtime.Defs
public import Silmaril.Wasi.Os.Thms

/-!
# Proofs: write loops up to an invariant, and the refutation of `Task.helloRt_exists`

* `writeSource_length_le`: LPS's write source has at most `MAX_RW_COUNT` bytes.
* **`writeStub_empty`**, **`not_helloRt_exists`**: there is no `WriteStub`, so the frozen
  `Task.helloRt_exists` is false. A stub must have every non-empty list as its source,
  including one longer than `MAX_RW_COUNT`.
* `WriteStub.toLoop`, `HelloRt.toLoop`: the exact-state obligations are the invariant ones
  with `Inv bs m := bs ≠ [] ∧ m = st bs` (so `WriteLoop` generalises `WriteStub`).
* **`ioSafe_writeLoop`**, **`helloLoop_ioSafe`**, **`helloLoop_psafe`**, **`helloLoop_e2e`**: the
  results of `Silmaril.Wasi.Os` (`ioSafe_writeStub`, `helloRt_ioSafe`, `helloRt_psafe`,
  `hello_e2e`) for the invariant form. The proofs follow those of `Silmaril.Proofs.Wasi.Os.Write`.
* `HelloLoop.ofRefines`: a runtime on `c` is a runtime on every machine refining `c`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Runtime

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Proofs.Machine.Process.IoSpec (ioSafe_of_safeN ioSafe_trap ioSafe_exit ioSafe_psafeLps)
open Silmaril.Wasi.Os
open Silmaril.Wasi.Examples (hiBytes)

/-! ## The refutation -/

theorem readableBytesAux_length_le (mp : Word → Option Byte) :
    ∀ (a : Word) (n : Nat), (readableBytesAux mp a n).length ≤ n
  | _, 0 => by simp [readableBytesAux]
  | a, n + 1 => by
    unfold readableBytesAux
    split
    · simp
    · have := readableBytesAux_length_le mp (a + 1) n
      simp only [List.length_cons]
      omega

/-- **LPS writes at most `MAX_RW_COUNT` bytes at once.** -/
theorem writeSource_length_le (mp : Word → Option Byte) (buf count : Word) :
    (writeSource mp buf count).length ≤ 0x7ffff000 := by
  refine (readableBytesAux_length_le mp buf _).trans ?_
  have h0 : 0 ≤ rwCountClamp count := by
    simp only [rwCountClamp, uns, MAX_RW_COUNT]
    omega
  have h1 : rwCountClamp count ≤ 0x7ffff000 := by
    simp only [rwCountClamp, MAX_RW_COUNT]
    omega
  simp only [zw, BitVec.toNat_ofInt]
  omega

/-- **No stub has every non-empty list as its source**: `WriteStub` is empty. -/
theorem writeStub_empty {c : MState → Option MState} {segs : List Segment} {ch : Word}
    {e : Silmaril.Process.LPS.Model} : IsEmpty (WriteStub c segs ch e) := by
  refine ⟨fun W => ?_⟩
  obtain ⟨bs, hlen⟩ : ∃ bs : List Byte, bs.length = 0x7ffff001 :=
    ⟨List.replicate _ 0, List.length_replicate⟩
  have hne : bs ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hs := W.source bs hne ⟨false, false, false, false, false, false⟩
  have hl := writeSource_length_le
    ((reqAt segs (W.st bs) ⟨false, false, false, false, false, false⟩).mem)
    ((reqAt segs (W.st bs) ⟨false, false, false, false, false, false⟩).arg 1)
    ((reqAt segs (W.st bs) ⟨false, false, false, false, false, false⟩).arg 2)
  rw [hs] at hl
  omega

/-- **`Task.helloRt_exists` is false.** -/
theorem not_helloRt_exists : ¬ Task.helloRt_exists := by
  rintro ⟨c, segs, ch, e, -, ⟨R⟩⟩
  exact writeStub_empty.false R.toWriteStub

/-! ## Exact states are an invariant -/

/-- A stub is a loop with the invariant "the state is `st bs`". -/
def _root_.Silmaril.Wasi.Os.WriteStub.toLoop {c : MState → Option MState} {segs : List Segment}
    {ch : Word} {e : Silmaril.Process.LPS.Model} (W : WriteStub c segs ch e) :
    WriteLoop c segs ch e where
  Inv bs m := bs ≠ [] ∧ m = W.st bs
  Fin m := m = W.fin
  nonempty _ _ h := h.1
  trap bs _ h := h.2 ▸ W.trap bs h.1
  handles bs _ h := h.2 ▸ W.handles bs h.1
  chan bs _ h := h.2 ▸ W.chan bs h.1
  source bs _ h := h.2 ▸ W.source bs h.1
  next bs m h k ds h1 hp n := by
    obtain ⟨hne, rfl⟩ := h
    refine Silmaril.Machine.X86.Safe.safeN_post (fun m' hm' => ?_) (W.next bs hne k ds h1 hp n)
    by_cases hr : bs.drop ds.length = []
    · simp only [hr, ↓reduceIte] at hm' ⊢
      exact hm'
    · simp only [hr, ↓reduceIte] at hm' ⊢
      exact ⟨hr, hm'⟩

/-- A runtime is a loop runtime. -/
def _root_.Silmaril.Wasi.Os.HelloRt.toLoop {c : MState → Option MState} {segs : List Segment}
    {ch : Word} {e : Silmaril.Process.LPS.Model} (R : HelloRt c segs ch e) :
    HelloLoop c segs ch e where
  toWriteLoop := R.toWriteStub.toLoop
  start := R.start
  toWrite n := Silmaril.Machine.X86.Safe.safeN_post
    (fun m h => show _ ∧ _ from ⟨by decide, h⟩) (R.toWrite n)
  toExit m h n := by
    have hm : m = R.fin := h
    subst hm
    exact Silmaril.Machine.X86.Safe.safeN_post
      (fun m' h' => h' ▸ ⟨R.exitTrap, R.exitNo, R.exitCode⟩) (R.toExit n)

/-- A runtime on `c` is a runtime on every machine refining `c`. -/
def HelloLoop.ofRefines {c c' : MState → Option MState} {segs : List Segment} {ch : Word}
    {e : Silmaril.Process.LPS.Model} (hc : Silmaril.Machine.X86.Safe.Refines c c')
    (R : HelloLoop c segs ch e) : HelloLoop c' segs ch e where
  Inv := R.Inv
  Fin := R.Fin
  nonempty := R.nonempty
  trap := R.trap
  handles := R.handles
  chan := R.chan
  source := R.source
  next bs m h k ds h1 hp n := Silmaril.Machine.X86.Safe.safeN_of_refines hc (R.next bs m h k ds h1 hp n)
  start := R.start
  toWrite n := Silmaril.Machine.X86.Safe.safeN_of_refines hc (R.toWrite n)
  toExit m h n := Silmaril.Machine.X86.Safe.safeN_of_refines hc (R.toExit m h n)

/-! ## Safety of write loops -/

variable {c : MState → Option MState} {segs : List Segment} {ch : Word}
  {e : Silmaril.Process.LPS.Model}

/-- The answers of `lpsEnv` at the loop: a partial write of a non-empty prefix `ds` of the bytes
left, resuming with the model unchanged. -/
theorem writeLoop_answer (W : WriteLoop c segs ch e) {bs : List Byte} {m : MState}
    (hi : W.Inv bs m) (k : X86FlagChoices.Choice) {o : IoOut Silmaril.Process.LPS.Model}
    (ho : (lpsEnv segs).arm (trapAt m k) e o) :
    ∃ ds : List Byte, 1 ≤ ds.length ∧ ds <+: bs ∧
      o = .resume (resume (trapAt m k) (writeEff segs m k ds)) e (ds.map (.writeEv ch)) := by
  obtain ⟨ch', hch', ds, hds1, -, hds, ho'⟩ := lpsEnv_arm_write (W.handles bs m hi k).1 ho
  have hch : some (FdEntry.channel ch') = some (FdEntry.channel ch) :=
    hch'.symm.trans (W.chan bs m hi k)
  have hch2 : ch' = ch := FdEntry.channel.inj (Option.some.inj hch)
  have hpref : ds <+: bs := by
    have hds' : ds = bs.take ds.length := by rw [← W.source bs m hi k]; exact hds
    exact hds' ▸ List.take_prefix _ _
  exact ⟨ds, hds1, hpref, hch2 ▸ ho'⟩

/-- After a partial write of `ds`, every state the loop continues with is `IoSafe` (given the
loop for shorter rests). -/
theorem writeLoop_next (W : WriteLoop c segs ch e)
    {Q : MState → Silmaril.Process.LPS.Model → (List Event → Prop) → Prop}
    {bs ds : List Byte} {A : List Event → Prop} (hpref : ds <+: bs)
    (hpre : ∀ p, p <+: bs → A (p.map (.writeEv ch)))
    (hfin : ∀ m, W.Fin m → ∀ n, IoSafeN c (lpsEnv segs) Q n m e
      (fun tr => A (bs.map (.writeEv ch) ++ tr)))
    (ih : ∀ rest : List Byte, rest = bs.drop ds.length → ∀ {A' : List Event → Prop},
      (∀ p, p <+: rest → A' (p.map (.writeEv ch))) →
      (∀ m, W.Fin m → ∀ n, IoSafeN c (lpsEnv segs) Q n m e
        (fun tr => A' (rest.map (.writeEv ch) ++ tr))) →
      ∀ m, W.Inv rest m → ∀ n, IoSafeN c (lpsEnv segs) Q n m e A') :
    ∀ m', (if bs.drop ds.length = [] then W.Fin m' else W.Inv (bs.drop ds.length) m') →
      ∀ n, IoSafeN c (lpsEnv segs) Q n m' e (fun tr => A (ds.map (.writeEv ch) ++ tr)) := by
  intro m' hm'
  have hbs : bs = ds ++ bs.drop ds.length := prefix_split hpref
  by_cases hr : bs.drop ds.length = []
  · simp only [hr, ↓reduceIte] at hm'
    have hd : bs = ds := by rw [hr, List.append_nil] at hbs; exact hbs
    exact hd ▸ hfin m' hm'
  · simp only [hr, ↓reduceIte] at hm'
    have hp : ∀ p, p <+: bs.drop ds.length → A (ds.map (.writeEv ch) ++ p.map (.writeEv ch)) :=
      fun p hp => List.map_append ▸ hpre _ (hbs ▸ (List.prefix_append_right_inj ds).2 hp)
    have hf : ∀ m, W.Fin m → ∀ n, IoSafeN c (lpsEnv segs) Q n m e
        (fun tr => A (ds.map (.writeEv ch) ++ ((bs.drop ds.length).map (.writeEv ch) ++ tr))) := by
      intro m hm n
      have hf0 := hfin m hm n
      rw [hbs, List.map_append] at hf0
      simpa only [List.append_assoc] using hf0
    exact ih _ rfl hp hf m' hm'

/-- The statement of `ioSafe_writeLoop` for the bytes `bs`. -/
def LoopSafe (W : WriteLoop c segs ch e)
    (Q : MState → Silmaril.Process.LPS.Model → (List Event → Prop) → Prop) (bs : List Byte) :
    Prop :=
  ∀ {A : List Event → Prop}, (∀ p, p <+: bs → A (p.map (.writeEv ch))) →
    (∀ m, W.Fin m → ∀ n, IoSafeN c (lpsEnv segs) Q n m e
      (fun tr => A (bs.map (.writeEv ch) ++ tr))) →
    ∀ m, W.Inv bs m → ∀ n, IoSafeN c (lpsEnv segs) Q n m e A

/-- One `write` of the loop, given the loop for every shorter list. -/
theorem loopSafe_step (W : WriteLoop c segs ch e)
    {Q : MState → Silmaril.Process.LPS.Model → (List Event → Prop) → Prop} {len : Nat}
    (ih : ∀ bs : List Byte, bs.length ≤ len → LoopSafe W Q bs) (bs : List Byte)
    (hl : bs.length ≤ len + 1) : LoopSafe W Q bs := by
  intro A hpre hfin m hm
  refine ioSafe_trap (W.trap bs m hm) (hpre [] List.nil_prefix) fun k =>
    ⟨lpsEnv_handles_write (W.handles bs m hm k), fun o ho => ?_⟩
  obtain ⟨ds, hds1, hpref, rfl⟩ := writeLoop_answer W hm k ho
  have hA : A (ds.map (.writeEv ch) ++ []) := by
    rw [List.append_nil]
    exact hpre ds hpref
  have hih : ∀ rest : List Byte, rest = bs.drop ds.length → LoopSafe W Q rest := fun rest hrest =>
    ih rest (by rw [hrest, List.length_drop]; omega)
  exact fun n => ioSafe_of_safeN hA (writeLoop_next W hpref hpre hfin hih) n
    (W.next bs m hm k ds hds1 hpref)

/-- **A write loop is `IoSafe`.** -/
theorem ioSafe_writeLoop (W : WriteLoop c segs ch e)
    {Q : MState → Silmaril.Process.LPS.Model → (List Event → Prop) → Prop} :
    ∀ (len : Nat) (bs : List Byte), bs.length ≤ len → LoopSafe W Q bs := by
  intro len
  induction len with
  | zero =>
    intro bs hl A _ _ m hm
    exact absurd (List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)) (W.nonempty bs m hm)
  | succ len ih => exact loopSafe_step W ih

/-- **`hello`'s loop runtime is `IoSafe`** with `lpsEnv`, for the traces `helloAllowed`. -/
theorem helloLoop_ioSafe (R : HelloLoop c segs ch e) :
    ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n R.start e (helloAllowed ch e.fs) := by
  have hA0 : ∀ tr, tr <+: hiOut ch → helloAllowed ch e.fs tr :=
    fun tr h => h.trans (List.prefix_append _ _)
  have hexit : ∀ m, ExitOk m → ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n m e
      (fun tr => helloAllowed ch e.fs (hiOut ch ++ tr)) := by
    rintro m ⟨ht, hno, hcode⟩
    refine ioSafe_exit ht (.inl hno) ?_ ?_
    · exact hA0 _ (by rw [List.append_nil])
    · rw [hcode]
      exact List.prefix_refl _
  have hfin : ∀ m, R.Fin m → ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n m e
      (fun tr => helloAllowed ch e.fs (hiBytes.map (.writeEv ch) ++ tr)) := fun m hm n =>
    ioSafe_of_safeN (by rw [List.append_nil]; exact hA0 _ (List.prefix_refl _)) hexit n
      (R.toExit m hm)
  have hst := ioSafe_writeLoop R.toWriteLoop 2 hiBytes le_rfl
    (fun p hp => hA0 _ (hp.map _)) hfin
  exact fun n => ioSafe_of_safeN (hA0 [] List.nil_prefix) hst n R.toWrite

/-- **`hello`'s loop runtime is process-safe for LPS**, with the traces `helloAllowed`, on
every native machine agreeing with `c`. -/
theorem helloLoop_psafe {oracle : Oracle} {nstep : NStep} {refused : RefusalFilter}
    (hM : Agrees nstep c) (R : HelloLoop c segs ch e) {cfg : Config (flagMachine oracle nstep)}
    (al : AlignedF cfg R.start) (he : cfg.model = e) :
    PSafeF segs refused (helloAllowed ch e.fs) cfg := by
  subst he
  exact ioSafe_psafeLps hM (fun _ _ _ _ _ _ h => h.elim) al (helloLoop_ioSafe R)

/-- **End to end**: a loop runtime of `hello` is `IoSafeN` with `lpsEnv` for "a prefix of the
OS image of `hello`'s run against `stdoutImpl`, then `exit 0`". -/
theorem helloLoop_e2e (R : HelloLoop c segs ch e) :
    ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n R.start e
      (fun tr => tr <+: osTrace ch (Silmaril.Wasi.wtrace helloRun) ++ [.exitEv 0 e.fs]) := by
  rw [helloRun_os]
  exact helloLoop_ioSafe R

end Silmaril.Wasi.Runtime
