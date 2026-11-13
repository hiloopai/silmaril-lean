module

public import Silmaril.Wasi.Os.Defs
public import Silmaril.Machine.Process.IoSpec.Thms

/-!
# Proofs: the stdout host stub and `hello`'s runtime through `IoSpec`

* `lpsEnv_arm_write`: at a trap with number `1`, every answer of `lpsEnv` is an answer of
  `writeArm`.
* **`ioSafe_writeStub`**: a stdout host stub with bytes `bs` left is `IoSafeN` with `lpsEnv`, for
  every trace predicate allowing the prefixes of `bs.map (writeEv ch)` and every continuation
  after the full write. The proof is by induction on the bytes left. Each `write` syscall writes a
  non-empty prefix (LPS allows short writes), and the stub loops on the rest.
* **`helloRt_ioSafe`**: an x86 runtime of `hello` is `IoSafeN` with `lpsEnv`, for the traces
  `helloAllowed` (a prefix of `hi`, then `exit 0`).
* **`helloRt_psafe`**: on every native machine agreeing with `c`, the runtime is process-safe
  for LPS (`PSafeF`), with these traces.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Os

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Proofs.Machine.Process.IoSpec (ioSafe_of_safeN ioSafe_trap ioSafe_exit ioSafe_psafeLps)
open Silmaril.Wasi.Examples (hiBytes)

variable {c : MState → Option MState} {segs : List Segment} {ch : Word}
  {e : Silmaril.Process.LPS.Model}

/-- At a trap with number `1`, the answers of `lpsEnv` are those of `writeArm`. -/
theorem lpsEnv_arm_write {s : X86State} {o : IoOut Silmaril.Process.LPS.Model}
    (h1 : (reqOf segs s).sysno.toNat = 1) (ho : (lpsEnv segs).arm s e o) :
    (writeArm segs).out s e o := by
  obtain ⟨a, ha, hH, ho⟩ := ho
  simp only [lpsArms, List.mem_cons, List.not_mem_nil, or_false] at ha
  have hr : (s.m.core.read .rax).toNat = 1 := h1
  rcases ha with rfl | rfl | rfl
  · rcases hH with h | h <;> omega
  · exact ho
  · have h0 : (s.m.core.read .rax).toNat = 0 := hH.1
    omega

/-- A trap that `writeArm` handles is handled by `lpsEnv`. -/
theorem lpsEnv_handles_write {s : X86State} (h : (writeArm segs).Handles s e) :
    (lpsEnv segs).Handles s e :=
  ⟨writeArm segs, by simp [lpsArms], h⟩

/-- The rest of a write: what is left after `ds`, with `bs = ds ++ rest`. -/
theorem prefix_split {ds bs : List Byte} (h : ds <+: bs) : bs = ds ++ bs.drop ds.length := by
  obtain ⟨u, rfl⟩ := h
  simp

/-- The answers of `lpsEnv` at the stub: a partial write of a non-empty prefix `ds` of the bytes
left, resuming at the stub's next state with the model unchanged. -/
theorem writeStub_answer (W : WriteStub c segs ch e) {bs : List Byte} (hne : bs ≠ [])
    (k : X86FlagChoices.Choice) {o : IoOut Silmaril.Process.LPS.Model}
    (ho : (lpsEnv segs).arm (trapAt (W.st bs) k) e o) :
    ∃ ds : List Byte, 1 ≤ ds.length ∧ ds <+: bs ∧
      o = .resume (resume (trapAt (W.st bs) k) (writeEff segs (W.st bs) k ds)) e
        (ds.map (.writeEv ch)) := by
  obtain ⟨ch', hch', ds, hds1, -, hds, ho'⟩ := lpsEnv_arm_write (W.handles bs hne k).1 ho
  have hch : some (FdEntry.channel ch') = some (FdEntry.channel ch) :=
    hch'.symm.trans (W.chan bs hne k)
  have hch2 : ch' = ch := FdEntry.channel.inj (Option.some.inj hch)
  have hpref : ds <+: bs := by
    have hds' : ds = bs.take ds.length := by rw [← W.source bs hne k]; exact hds
    exact hds' ▸ List.take_prefix _ _
  exact ⟨ds, hds1, hpref, hch2 ▸ ho'⟩

/-- After a partial write of `ds`, the stub's next state is `IoSafe` (given the loop for shorter
rests). -/
theorem writeStub_next (W : WriteStub c segs ch e)
    {Q : MState → Silmaril.Process.LPS.Model → (List Event → Prop) → Prop}
    {bs ds : List Byte} {A : List Event → Prop} (hpref : ds <+: bs)
    (hpre : ∀ p, p <+: bs → A (p.map (.writeEv ch)))
    (hfin : ∀ n, IoSafeN c (lpsEnv segs) Q n W.fin e (fun tr => A (bs.map (.writeEv ch) ++ tr)))
    (ih : ∀ rest : List Byte, rest = bs.drop ds.length → rest ≠ [] →
      ∀ {A' : List Event → Prop}, (∀ p, p <+: rest → A' (p.map (.writeEv ch))) →
      (∀ n, IoSafeN c (lpsEnv segs) Q n W.fin e (fun tr => A' (rest.map (.writeEv ch) ++ tr))) →
      ∀ n, IoSafeN c (lpsEnv segs) Q n (W.st rest) e A') :
    ∀ n, IoSafeN c (lpsEnv segs) Q n
      (if bs.drop ds.length = [] then W.fin else W.st (bs.drop ds.length)) e
      (fun tr => A (ds.map (.writeEv ch) ++ tr)) := by
  have hbs : bs = ds ++ bs.drop ds.length := prefix_split hpref
  by_cases hr : bs.drop ds.length = []
  · show ∀ n, IoSafeN c (lpsEnv segs) Q n (if bs.drop ds.length = [] then W.fin else _) e _
    have hd : bs = ds := by rw [hr, List.append_nil] at hbs; exact hbs
    have hf : ∀ n, IoSafeN c (lpsEnv segs) Q n W.fin e (fun tr => A (ds.map (.writeEv ch) ++ tr)) :=
      hd ▸ hfin
    simpa only [hr, ↓reduceIte] using hf
  · show ∀ n, IoSafeN c (lpsEnv segs) Q n (if bs.drop ds.length = [] then _ else _) e _
    have hp : ∀ p, p <+: bs.drop ds.length → A (ds.map (.writeEv ch) ++ p.map (.writeEv ch)) :=
      fun p hp => List.map_append ▸ hpre _ (hbs ▸ (List.prefix_append_right_inj ds).2 hp)
    have hf : ∀ n, IoSafeN c (lpsEnv segs) Q n W.fin e
        (fun tr => A (ds.map (.writeEv ch) ++ ((bs.drop ds.length).map (.writeEv ch) ++ tr))) := by
      intro n
      have hf0 := hfin n
      rw [hbs, List.map_append] at hf0
      simpa only [List.append_assoc] using hf0
    simpa only [hr, ↓reduceIte] using ih _ rfl hr hp hf

/-- **The stdout host stub is `IoSafe`.** -/
theorem ioSafe_writeStub (W : WriteStub c segs ch e)
    {Q : MState → Silmaril.Process.LPS.Model → (List Event → Prop) → Prop} :
    ∀ (len : Nat) (bs : List Byte), bs.length ≤ len → bs ≠ [] → ∀ {A : List Event → Prop},
      (∀ p, p <+: bs → A (p.map (.writeEv ch))) →
      (∀ n, IoSafeN c (lpsEnv segs) Q n W.fin e (fun tr => A (bs.map (.writeEv ch) ++ tr))) →
      ∀ n, IoSafeN c (lpsEnv segs) Q n (W.st bs) e A := by
  intro len
  induction len with
  | zero => exact fun bs hl hne => absurd (List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)) hne
  | succ len ih =>
    intro bs hl hne A hpre hfin
    refine ioSafe_trap (W.trap bs hne) (hpre [] (List.nil_prefix)) fun k =>
      ⟨lpsEnv_handles_write (W.handles bs hne k), fun o ho => ?_⟩
    obtain ⟨ds, hds1, hpref, rfl⟩ := writeStub_answer W hne k ho
    have hA : A (ds.map (.writeEv ch) ++ []) := by
      rw [List.append_nil]
      exact hpre ds hpref
    have hih : ∀ rest : List Byte, rest = bs.drop ds.length → rest ≠ [] →
        ∀ {A' : List Event → Prop}, (∀ p, p <+: rest → A' (p.map (.writeEv ch))) →
        (∀ n, IoSafeN c (lpsEnv segs) Q n W.fin e (fun tr => A' (rest.map (.writeEv ch) ++ tr))) →
        ∀ n, IoSafeN c (lpsEnv segs) Q n (W.st rest) e A' := fun rest hrest hr =>
      ih rest (by rw [hrest, List.length_drop]; omega) hr
    exact fun n => ioSafe_of_safeN hA (fun _ hm' => hm' ▸ writeStub_next W hpref hpre hfin hih) n
      (W.next bs hne k ds hds1 hpref)

/-- **`hello`'s x86 runtime is `IoSafe`** with `lpsEnv`, for the traces `helloAllowed`. -/
theorem helloRt_ioSafe (R : HelloRt c segs ch e) :
    ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n R.start e (helloAllowed ch e.fs) := by
  have hA0 : ∀ tr, tr <+: hiOut ch → helloAllowed ch e.fs tr :=
    fun tr h => h.trans (List.prefix_append _ _)
  have hexit : ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n R.exitSt e
      (fun tr => helloAllowed ch e.fs (hiOut ch ++ tr)) := by
    refine ioSafe_exit R.exitTrap (.inl R.exitNo) ?_ ?_
    · exact hA0 _ (by rw [List.append_nil])
    · rw [R.exitCode]
      exact List.prefix_refl _
  have hfin : ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n R.fin e
      (fun tr => helloAllowed ch e.fs (hiBytes.map (.writeEv ch) ++ tr)) := fun n =>
    ioSafe_of_safeN (by rw [List.append_nil]; exact hA0 _ (List.prefix_refl _))
      (fun _ h => h ▸ hexit) n R.toExit
  have hst := ioSafe_writeStub R.toWriteStub 2 hiBytes le_rfl (by decide)
    (fun p hp => hA0 _ (hp.map _)) hfin
  exact fun n => ioSafe_of_safeN (hA0 [] List.nil_prefix) (fun _ h => h ▸ hst) n R.toWrite

/-- **`hello`'s x86 runtime is process-safe for LPS**, with the traces `helloAllowed`, on every
native machine agreeing with `c`. -/
theorem helloRt_psafe {oracle : Oracle} {nstep : NStep} {refused : RefusalFilter}
    (hM : Agrees nstep c) (R : HelloRt c segs ch e) {cfg : Config (flagMachine oracle nstep)}
    (al : AlignedF cfg R.start) (he : cfg.model = e) :
    PSafeF segs refused (helloAllowed ch e.fs) cfg := by
  subst he
  exact ioSafe_psafeLps hM (fun _ _ _ _ _ _ h => h.elim) al (helloRt_ioSafe R)

end Silmaril.Wasi.Os
