module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Trig

/-!
# The XL bridge: the whole schedule

Proofs for `Csl.Task.cirXlOpAx`. Tick by tick (`H.tick`, `H.run_to`) the
closed-form configuration stays reachable; after the last clock value every thread catches up
to its end, takes its final silent steps, and every buffer is empty (`H.finish`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff cellsOf LocsFacts)

/-- After every clock value. -/
def tEnd (x : Exec) : Nat := 2 * (x.n * x.n + x.n) + 2

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)} {R : Nat → Regs}
  {S Pre : Nat → Nat → Stmt × Regs}

theorem H.κ_lt (h : H P L x U) {u : Nat} (hu : u < x.n) : κ x u < tEnd x := by
  classical
  have hg : gH x (fstU x u) ≤ x.n := by
    unfold gH
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hm : gH x (fstU x u) * x.n ≤ x.n * x.n := Nat.mul_le_mul_right _ hg
  have := (h.fst_spec hu).1
  have := bit_le x u
  simp only [κ, tEnd]
  omega

/-- **One tick.** -/
theorem H.tick (h : H P L x U) (hr : Runs P L R S Pre) {I : HProp} {Q : Nat → Regs → HProp}
    {hs : Nat → Heap} {hI : Heap} (G : GInv I Q P.threads.length (progInit P) hs hI)
    {T : Nat} {cnt : Nat → Nat} (hIv : Inv L x T cnt) (hR : Reach P L x S T cnt)
    (hist : ∀ τ < T, ∃ cnt, Inv L x τ cnt ∧ Reach P L x S τ cnt) :
    ∃ cnt', Inv L x (T + 1) cnt' ∧ Reach P L x S (T + 1) cnt' := by
  by_cases hex : ∃ u < x.n, κ x u = T
  · obtain ⟨u, hu, hκ⟩ := hex
    have hi := h.tid_lt hu
    obtain ⟨c, hc, k, hk, hp, -, -⟩ := h.labAt hu rfl
    have hue : pidx x (x.evN u).tid (base L (x.evN u).tid c + k) = u := by
      rw [← hp]; exact h.pidx_eq hu
    by_cases ht : trig (L (x.evN u).tid)[c] = some k
    · exact h.tick_trig hr G hi hc ht (by rw [hue, hκ]) hIv hR hist
    · by_cases hn : ∃ e ∈ nsts (L (x.evN u).tid)[c], e.1 = k
      · obtain ⟨e, he, rfl⟩ := hn
        exact h.tick_store hr hi hc he (by rw [hue, hκ]) hIv hR
      · exact ⟨cnt, h.tick_other hi hc hk (by rw [hue, hκ]) ht
          (fun e he he1 => hn ⟨e, he, he1⟩) hIv hR⟩
  · exact ⟨cnt, h.tick_none (fun u hu he => hex ⟨u, hu, he⟩) hIv hR⟩

theorem Runs.init_cfg (hr : Runs P L R S Pre) : cfg P L x S 0 (fun _ => 0) = (progInit P).toO := by
  simp only [cfg, Cfg.toO, progInit, OCfg.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext i
    by_cases hi : i < P.threads.length
    · rw [(hr.cut i hi).start, List.getElem?_eq_getElem hi]; rfl
    · rw [hr.out i (by omega), List.getElem?_eq_none (by omega)]; rfl
  · funext a
    simp only [nMem, initHeap]
    congr 1
    funext l
    have : cval x 0 a = none := cval_none' fun _ _ _ _ => Nat.zero_le _
    rw [this]; rfl
  · funext i; simp [nBuf, rawP]

theorem inv_zero : Inv L x 0 fun _ => 0 :=
  ⟨fun _ => Nat.zero_le _, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
    fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- **Every tick is reached.** -/
theorem H.run_to (h : H P L x U) (hr : Runs P L R S Pre) {I : HProp} {Q : Nat → Regs → HProp}
    {hs : Nat → Heap} {hI : Heap} (G : GInv I Q P.threads.length (progInit P) hs hI) :
    ∀ T, ∀ τ ≤ T, ∃ cnt, Inv L x τ cnt ∧ Reach P L x S τ cnt
  | 0, τ, hτ => by
    obtain rfl : τ = 0 := by omega
    refine ⟨fun _ => 0, inv_zero, ?_⟩
    unfold Reach; rw [hr.init_cfg]; exact Star.refl
  | T + 1, τ, hτ => by
    by_cases hle : τ ≤ T
    · exact h.run_to hr G T τ hle
    · obtain rfl : τ = T + 1 := by omega
      obtain ⟨cnt, hIv, hR⟩ := h.run_to hr G T T le_rfl
      exact h.tick hr G hIv hR fun τ' hτ' => h.run_to hr G T τ' (by omega)

/-- **The end**: every thread finished, every buffer empty, memory the closed form at `tEnd`. -/
theorem H.finish (h : H P L x U) (hr : Runs P L R S Pre) {cnt : Nat → Nat}
    (hIv : Inv L x (tEnd x) cnt) (hR : Reach P L x S (tEnd x) cnt) :
    ∃ C : OCfg, OReach .xl P.threads.length (progInit P).toO C ∧ C.Drained ∧
      (∀ t < P.threads.length, C.ts t = (.skip, R t)) ∧ C.mem = nMem P x (tEnd x) := by
  -- every thread runs its remaining labels
  have key : ∀ m ≤ P.threads.length, ∃ cnt' : Nat → Nat, Inv L x (tEnd x) cnt' ∧
      Reach P L x S (tEnd x) cnt' ∧ ∀ i < m, cnt' i = (L i).length := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨cnt, hIv, hR, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨cnt', hI', hR', hall⟩ := ih (by omega)
      have hle := hI'.le m
      obtain ⟨hI2, hR2⟩ := hr.catchup h (by omega : m < P.threads.length) ((L m).length - cnt' m)
        (cnt := cnt') (by omega) hI'
        (fun c hc h1 h2 => by
          cases ht : trig (L m)[c] with
          | none => rfl
          | some k =>
            exfalso
            obtain ⟨-, hu, -⟩ := h.trig_unit (by omega) hc ht
            have := hI'.trigDone m c hc k ht (h.κ_lt hu)
            omega)
        (fun c hc h1 h2 e he => by
          by_contra hlt
          have := hI'.stDone m c hc e he (h.κ_lt (h.nst_unit (by omega) hc he).1)
          omega)
        (fun c hc h1 h2 _ c' hc' _ e he => h.κ_lt (h.nst_unit (by omega) hc' he).1) hR'
      refine ⟨_, hI2, hR2, fun i hi => ?_⟩
      by_cases him : i = m
      · subst him; simp; omega
      · rw [upd_ne _ _ him]; exact hall i (by omega)
  obtain ⟨cntF, hIF, hRF, hallF⟩ := key _ le_rfl
  -- final silent steps
  have taus : ∀ m ≤ P.threads.length, OReach .xl P.threads.length (progInit P).toO
      ⟨fun i => if i < m then (.skip, R i) else S i (cntF i), nMem P x (tEnd x), nBuf L x (tEnd x) cntF⟩ := by
    intro m
    induction m with
    | zero => exact fun _ => by simpa [Reach, cfg] using hRF
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have hcut := hr.cut m (by omega)
      have hlast : Star TauR (S m (cntF m)) (.skip, R m) := by
        rw [hallF m (by omega)]; exact hcut.last
      have h2 := reach_taus (M := .xl) (by omega : m < P.threads.length) hlast
        ⟨fun i => if i < m then (.skip, R i) else S i (cntF i), nMem P x (tEnd x),
          nBuf L x (tEnd x) cntF⟩ (by simp)
      convert star_trans h1 h2 using 2
      funext i
      by_cases him : i = m
      · subst him; simp
      · simp only [upd, him, ↓reduceIte]
        by_cases hi : i < m
        · simp [hi, show i < m + 1 by omega]
        · simp [hi, show ¬ i < m + 1 by omega]
  refine ⟨_, taus _ le_rfl, fun i => ?_, fun t ht => by simp [ht], rfl⟩
  exact nBuf_nil fun c hc _ e he => by
    have hi : i < P.threads.length := by
      by_contra hn
      have hc' := hc
      rw [h.lout i (by omega)] at hc'
      simp at hc'
    exact h.κ_lt (h.nst_unit hi hc he).1

end

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
