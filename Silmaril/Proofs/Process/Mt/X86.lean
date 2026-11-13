module

public import Silmaril.Process.Mt.X86.Defs
public import Silmaril.Process.Mt.Prim.Thms

/-!
# Proofs: the executable scheduler runs the multithreaded x86 process

The header is `Silmaril/Process/Mt/X86/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.X86

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory)
open Silmaril.Process.Mt
open Silmaril.Process.Mt.X86

variable {γ : Type}

/-! ## Thread tables -/

theorem setTh_isSome {σ : Type} {th : Nat → Option (TRec σ)} {t u : Nat} {r : TRec σ}
    (ht : (th t).isSome) (h : (setTh th t r u).isSome) : (th u).isSome := by
  by_cases hu : u = t
  · subst hu; exact ht
  · simpa [setTh, upd, hu] using h

theorem wakeAll_isSome {σ : Type} {th : Nat → Option (TRec σ)} {ws : List Nat} {u : Nat}
    (h : (wakeAll th ws u).isSome) : (th u).isSome := by
  unfold wakeAll at h; split at h
  · simpa using h
  · exact h

theorem wakeAll_isSome_eq {σ : Type} {th : Nat → Option (TRec σ)} {ws : List Nat} {u : Nat} :
    (wakeAll th ws u).isSome = (th u).isSome := by
  unfold wakeAll; split <;> simp

theorem cover_of {tids : List Nat} {C C' : XCfg γ} (hc : Cover tids C)
    (h : ∀ u, (C'.th u).isSome → (C.th u).isSome) : Cover tids C' :=
  ⟨hc.1, fun u hu => hc.2 u (h u hu)⟩

theorem liveB_iff {th : Nat → Option (TRec Core)} {u : Nat} : liveB (th u) = true ↔ LiveT th u := by
  unfold liveB LiveT
  cases th u with
  | none => simp
  | some r => simp

theorem waitingB_iff {th : Nat → Option (TRec Core)} {a u : Nat} :
    waitingB a (th u) = true → Waiting th a u := by
  unfold waitingB Waiting
  cases h : th u with
  | none => simp
  | some r =>
    rcases r with ⟨st, ctid⟩
    cases st with
    | wait b k => intro hb; simp only [beq_iff_eq] at hb; subst hb; exact ⟨_, k, rfl, rfl⟩
    | run _ => simp
    | exited => simp

theorem any_live_iff {tids : List Nat} {th : Nat → Option (TRec Core)}
    (hc : ∀ u, (th u).isSome → u ∈ tids) :
    (tids.any fun u => liveB (th u)) = true ↔ ∃ u, LiveT th u := by
  simp only [List.any_eq_true, liveB_iff]
  constructor
  · rintro ⟨u, _, hu⟩; exact ⟨u, hu⟩
  · rintro ⟨u, r, hr, hx⟩
    exact ⟨u, hc u (by simp [hr]), ⟨r, hr, hx⟩⟩

open Classical in
theorem lastExit_eq {tids : List Nat} {th : Nat → Option (TRec Core)} {c : Nat}
    (hc : ∀ u, (th u).isSome → u ∈ tids) :
    lastExit th c = if (tids.any fun u => liveB (th u)) then none else some c := by
  unfold lastExit
  by_cases h : ∃ u, LiveT th u
  · have h2 := (any_live_iff hc).2 h
    simp [h, h2]
  · have h2 : ¬ (tids.any fun u => liveB (th u)) = true := fun h' => h ((any_live_iff hc).1 h')
    simp [h, h2]

theorem wakes_of {tids : List Nat} {th : Nat → Option (TRec Core)} {a n : Nat} (hn : tids.Nodup) :
    Wakes th a n ((tids.filter fun u => waitingB a (th u)).take n) := by
  refine ⟨(hn.filter _).sublist (List.take_sublist _ _), by simp, ?_⟩
  intro u hu
  have := List.mem_of_mem_take hu
  simp only [List.mem_filter] at this
  exact waitingB_iff this.2

/-! ## The canonical outcomes are outcomes of `step` -/

theorem primRet_primK (c : Core) (ra w : Word) : PrimRet c.core ra w (primK c ra w) := by
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · simp [primK, State.read, State.write]
  · simp [primK, State.read, State.write]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [primK, State.read, State.write]

variable {X : Env γ} {t : Nat} {c : Core} {m : Memory} {g : γ}

theorem step_prim {a : Word} {p : Nat} {ra : Word} (hpf : X.prims.find? (·.1 == c.core.rip) = some (a, p))
    (hra : retAddr c.core m = some ra) :
    step X t c m g (.prim p (callArgs c.core) (primK c ra)) := by
  unfold step; rw [hpf]; simp only; rw [hra]
  exact ⟨primK c ra, fun w => primRet_primK c ra w, rfl⟩

theorem step_user {y : Silmaril.X86.Sse9.XState} (hpf : X.prims.find? (·.1 == c.core.rip) = none)
    (hlf : X.libs.find? (·.1 == c.core.rip) = none) (hf : ¬ m.fetchBytes c.core.rip.toNat 2 = some syscallBytes)
    (hy : Silmaril.X86.Str9FsXN.step ⟨⟨c.core, m⟩, c.xmm⟩ = some y) :
    step X t c m g (.step ⟨y.m.core, y.xmm⟩ (X.acc c m) y.m.memory) := by
  unfold step; rw [hpf]; simp only; rw [hlf]; simp only [hf, ↓reduceIte]; rw [hy]

theorem step_arch (hpf : X.prims.find? (·.1 == c.core.rip) = none)
    (hlf : X.libs.find? (·.1 == c.core.rip) = none) (hf : m.fetchBytes c.core.rip.toNat 2 = some syscallBytes)
    (ha : (c.core.read .rax).toNat = nrArchPrctl ∧ (c.core.read .rdi).toNat = archSetFs) :
    step X t c m g (.step (sysK ⟨{ (pastSys c).core with fsBase := c.core.read .rsi }, (pastSys c).xmm⟩ 0 0)
      none m) := by
  unfold step; rw [hpf]; simp only; rw [hlf]; simp only [hf, ↓reduceIte]
  exact ⟨0, by simp only [ha, and_self, ↓reduceIte]⟩

theorem step_sys (hpf : X.prims.find? (·.1 == c.core.rip) = none)
    (hlf : X.libs.find? (·.1 == c.core.rip) = none) (hf : m.fetchBytes c.core.rip.toNat 2 = some syscallBytes)
    (ha : ¬ ((c.core.read .rax).toNat = nrArchPrctl ∧ (c.core.read .rdi).toNat = archSetFs)) :
    step X t c m g (.sys (c.core.read .rax).toNat (sysArgs c.core) (sysK (pastSys c) 0)
      (cloneChild (pastSys c) 0 (sysArgs c.core))) := by
  unfold step; rw [hpf]; simp only; rw [hlf]; simp only [hf, ↓reduceIte]
  exact ⟨0, by simp only [ha, ↓reduceIte]⟩

theorem step_sysN {nr : Nat} (hn : (c.core.read .rax).toNat = nr)
    (hpf : X.prims.find? (·.1 == c.core.rip) = none)
    (hlf : X.libs.find? (·.1 == c.core.rip) = none) (hf : m.fetchBytes c.core.rip.toNat 2 = some syscallBytes)
    (ha : ¬ ((c.core.read .rax).toNat = nrArchPrctl ∧ (c.core.read .rdi).toNat = archSetFs)) :
    step X t c m g (.sys nr [c.core.read .rdi, c.core.read .rsi, c.core.read .rdx, c.core.read .r10,
      c.core.read .r8, c.core.read .r9] (sysK (pastSys c) 0) (cloneChild (pastSys c) 0 (sysArgs c.core))) := by
  subst hn; exact step_sys hpf hlf hf ha

/-! ## System calls -/

theorem le_foldr_max {tids : List Nat} {u : Nat} (h : u ∈ tids) : u ≤ tids.foldr max 0 := by
  induction tids with
  | nil => cases h
  | cons v vs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem execSys_sound {tids tids' : List Nat} {C C' : XCfg γ} {r : TRec Core}
    (hc : Cover tids C) (hl : C.Live (mtX X)) (ht : C.th t = some r) (hr : r.st = .run c)
    (hpf : X.prims.find? (·.1 == c.core.rip) = none) (hlf : X.libs.find? (·.1 == c.core.rip) = none)
    (hf : C.ms.fetchBytes c.core.rip.toNat 2 = some syscallBytes)
    (h : execSys tids C t r c = some (C', tids')) :
    MtProc X sc Prim.table (Base.none γ) C C' ∧ Cover tids' C' := by
  have htS : (C.th t).isSome := by simp [ht]
  have hcs : ∀ r', Cover tids { C with th := setTh C.th t r' } :=
    fun _ => cover_of hc fun _ hu => setTh_isSome htS hu
  unfold execSys at h
  simp only at h
  split at h
  · rename_i ha
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨.user hl ht hr (step_arch hpf hlf hf ha) rfl, hcs _⟩
  rename_i ha
  split at h
  · rename_i hn
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨.gettid hl ht hr trivial (step_sysN hn hpf hlf hf ha), hcs _⟩
  split at h
  · rename_i hn
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨.exitGroup hl ht hr trivial (step_sysN hn hpf hlf hf ha), cover_of hc fun _ hu => hu⟩
  split at h
  · rename_i hn
    split at h
    · rename_i hal
      split at h
      · rename_i hop
        split at h
        · rename_i w hw
          split at h
          · rename_i heq
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨.futexBlock hl ht hr trivial (step_sysN hn hpf hlf hf ha) hop hal (heq ▸ hw), hcs _⟩
          · rename_i hne
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨.futexAgain hl ht hr trivial (step_sysN hn hpf hlf hf ha) hop hal hw hne, hcs _⟩
        · cases h
      · split at h
        · rename_i hop' hop
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨.futexWake hl ht hr trivial (step_sysN hn hpf hlf hf ha) hop hal (wakes_of hc.1), ?_⟩
          exact cover_of hc fun u hu => wakeAll_isSome (setTh_isSome (by rw [wakeAll_isSome_eq]; exact htS) hu)
        · cases h
    · cases h
  split at h
  · rename_i hn
    have hth1 : ∀ u, (setTh C.th t { r with st := .exited } u).isSome → u ∈ tids :=
      fun u hu => hc.2 u (setTh_isSome htS hu)
    split at h
    · rename_i a hct
      split at h
      · rename_i m' hm
        split at h
        · rename_i hother
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨.exitClear hl ht hr trivial (step_sysN hn hpf hlf hf ha) hct hm ((any_live_iff hth1).1 hother)
            (wakes_of hc.1), ?_⟩
          exact cover_of hc fun u hu => setTh_isSome htS (wakeAll_isSome hu)
        · rename_i hother
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, cover_of hc fun u hu => setTh_isSome htS hu⟩
          have : MtProc X sc Prim.table (Base.none γ) C { C with
              th := setTh C.th t { r with st := .exited }
              status := lastExit (setTh C.th t { r with st := .exited }) ((c.core.read .rdi).toNat % 256) } :=
            MtStep.exitPlain
            hl ht hr trivial (step_sysN hn hpf hlf hf ha) (fun a' ha' _ => by
              rw [hct] at ha'; cases ha'; exact fun h' => hother ((any_live_iff hth1).2 h'))
          rw [lastExit_eq hth1] at this
          simp only [hother, Bool.false_eq_true, ↓reduceIte] at this
          exact this
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, cover_of hc fun u hu => setTh_isSome htS hu⟩
        have : MtProc X sc Prim.table (Base.none γ) C { C with
            th := setTh C.th t { r with st := .exited }
            status := lastExit (setTh C.th t { r with st := .exited }) ((c.core.read .rdi).toNat % 256) } :=
          MtStep.exitPlain
          hl ht hr trivial (step_sysN hn hpf hlf hf ha) (fun a' ha' hw => by
            rw [hct] at ha'; cases ha'
            change (C.ms.writeBytes _ _).isSome = true at hw
            rw [hm] at hw; cases hw)
        rwa [lastExit_eq hth1] at this
    · rename_i hct
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, cover_of hc fun u hu => setTh_isSome htS hu⟩
      have : MtProc X sc Prim.table (Base.none γ) C { C with
          th := setTh C.th t { r with st := .exited }
          status := lastExit (setTh C.th t { r with st := .exited }) ((c.core.read .rdi).toNat % 256) } :=
        MtStep.exitPlain
        hl ht hr trivial (step_sysN hn hpf hlf hf ha) (fun a' ha' _ => by rw [hct] at ha'; cases ha')
      rwa [lastExit_eq hth1] at this
  split at h
  · rename_i hn
    split at h
    · rename_i hok
      split at h
      · rename_i m' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        have hfresh : C.th (tids.foldr max 0 + 1) = none := by
          cases e : C.th (tids.foldr max 0 + 1) with
          | none => rfl
          | some _ =>
            have := le_foldr_max (hc.2 (tids.foldr max 0 + 1) (by rw [e]; rfl)); omega
        refine ⟨.clone hl ht hr trivial (step_sysN hn hpf hlf hf ha) hok.1 hfresh (by omega) hok.2 hm, ?_⟩
        refine ⟨hc.1.append (List.nodup_singleton _) ?_, ?_⟩
        · intro u hu hu'
          simp only [List.mem_singleton] at hu'; subst hu'
          have := le_foldr_max hu; omega
        · intro u hu
          simp only [List.mem_append, List.mem_singleton]
          by_cases e : u = tids.foldr max 0 + 1
          · exact .inr e
          · exact .inl (hc.2 u (setTh_isSome htS (by simpa [setTh, upd, e] using hu)))
      · cases h
    · cases h
  · cases h

/-! ## One step, and runs -/

theorem exec1_sound {tids tids' : List Nat} {C C' : XCfg γ} (hc : Cover tids C)
    (h : exec1 X tids C t = some (C', tids')) :
    MtProc X sc Prim.table (Base.none γ) C C' ∧ Cover tids' C' := by
  unfold exec1 at h
  split at h
  · rename_i hl
    split at h
    · rename_i r ht
      have htS : (C.th t).isSome := by simp [ht]
      split at h
      · rename_i c hr
        split at h
        · rename_i a p hpf
          split at h
          · rename_i ra hra
            split at h
            · rename_i w sh2 hex
              simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              obtain ⟨sp, hp, hpre, hpost⟩ := Prim.execTable_sound hex
              exact ⟨.prim hl ht hr trivial (step_prim hpf hra) hp hpre hpost,
                cover_of hc fun _ hu => setTh_isSome htS hu⟩
            · cases h
          · cases h
        · rename_i hpf
          split at h
          · cases h
          · rename_i hlf
            split at h
            · rename_i hf
              exact execSys_sound hc hl ht hr hpf hlf hf h
            · rename_i hf
              split at h
              · rename_i y hy
                simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                exact ⟨.user hl ht hr (step_user hpf hlf hf hy) rfl,
                  cover_of hc fun _ hu => setTh_isSome htS hu⟩
              · cases h
      · cases h
    · cases h
  · cases h

theorem run_sound {ts : List Nat} {tids tids' : List Nat} {C C' : XCfg γ} (hc : Cover tids C)
    (h : run X ts (C, tids) = some (C', tids')) :
    MtReach (mtX X) sc Prim.table (Base.none γ) C C' ∧ Cover tids' C' := by
  induction ts generalizing C tids with
  | nil =>
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨.refl, hc⟩
  | cons t ts ih =>
    simp only [run] at h
    cases e : exec1 X tids C t with
    | none => rw [e] at h; cases h
    | some p =>
      rw [e] at h
      obtain ⟨C1, tids1⟩ := p
      obtain ⟨h1, hc1⟩ := exec1_sound hc e
      obtain ⟨h2, hc2⟩ := ih hc1 h
      exact ⟨.head h1 h2, hc2⟩

end Silmaril.Proofs.Process.Mt.X86
