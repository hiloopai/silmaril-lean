module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Interfere

/-!
# The XL bridge: one tick

Proofs for `Csl.Task.cirXlOpAx`. From the closed form at tick `T`, the unit `u`
with clock `T` (if any) acts:

* the trigger of a label: its thread catches up to the label and runs it (`tick_trig`);
* a native store: its label is run if it has not been yet, and the store is flushed
  (`tick_store`);
* any other unit, or no unit: nothing happens (`tick_other`, `tick_none`).

Every case reaches the closed form at `T + 1`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff cellsOf LocsFacts)

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)} {R : Nat → Regs}
  {S Pre : Nat → Nat → Stmt × Regs}

theorem Runs.step_bufAt (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat} {i c : Nat}
    (hi : i < P.threads.length) (hcn : cnt i = c) (hc : c < (L i).length)
    (hm : (L i)[c].isMem = true) (hd : (L i)[c].drains = false)
    (htouch : ∀ a, (L i)[c].Touches a → (nMem P x T a).isSome)
    (hok : (L i)[c].okH (view (nMem P x T) (nBuf L x T cnt i)))
    (hents : (labEnts L x T i c).map Prod.snd = (L i)[c].ents) :
    OReach .xl P.threads.length (cfg P L x S T cnt) (cfg P L x S T (upd cnt i (c + 1))) := by
  subst hcn; exact hr.step_buf hi hc hm hd htouch hok hents

theorem Runs.step_drainAt (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat} {i c : Nat}
    (hi : i < P.threads.length) (hcn : cnt i = c) (hc : c < (L i).length)
    (hm : (L i)[c].isMem = true) (hd : (L i)[c].drains = true)
    (he : nBuf L x T cnt i = [])
    (htouch : ∀ a, (L i)[c].Touches a → (nMem P x T a).isSome)
    (hok : (L i)[c].okH (nMem P x T)) (hnil : labEnts L x T i c = []) :
    OReach .xl P.threads.length (cfg P L x S T cnt)
      ⟨fun j => S j (upd cnt i (c + 1) j), (L i)[c].updH (nMem P x T),
        nBuf L x T (upd cnt i (c + 1))⟩ := by
  subst hcn; exact hr.step_drain hi hc hm hd he htouch hok hnil

/-- Units are named by their thread, label and offset. -/
theorem H.ident (h : H P L x U) {i c k j c' k' : Nat} (hi : i < P.threads.length)
    (hc : c < (L i).length) (hk : k < (labRoles (L i)[c]).length) (hj : j < P.threads.length)
    (hc' : c' < (L j).length) (hk' : k' < (labRoles (L j)[c']).length)
    (he : pidx x j (base L j c' + k') = pidx x i (base L i c + k)) : j = i ∧ c' = c ∧ k' = k := by
  obtain ⟨-, h1, -⟩ := h.at hi hc hk
  obtain ⟨-, h2, -⟩ := h.at hj hc' hk'
  rw [he] at h2
  have ht : j = i := by have := congrArg Ev.tid (h1.symm.trans h2); simpa using this.symm
  subst ht
  have hp := congrArg Ev.pos (h1.symm.trans h2)
  simp only [Role.ev_pos] at hp
  obtain ⟨h3, h4⟩ := lab_unique hc' hc hk' hk hp.symm
  exact ⟨rfl, h3, h4⟩

/-- Time advances over buffers when the unit at `T` is no native store of the thread. -/
theorem H.adv_buf (h : H P L x U) {T : Nat} {cnt : Nat → Nat} {j : Nat}
    (hT : ∀ v < x.n, κ x v = T → (x.evN v).isW = true → isLW (x.evN v) = false →
      (x.evN v).tid = j → False) : nBuf L x (T + 1) cnt j = nBuf L x T cnt j := by
  refine nBuf_succT fun c hc e he hκ => ?_
  have hj : j < P.threads.length := by
    by_contra hn
    have hc' := hc
    rw [h.lout j (by omega)] at hc'
    simp at hc'
  obtain ⟨hw, hW, hlw, ht, -, -⟩ := h.nst_unit hj hc he
  exact hT _ hw hκ hW hlw ht


theorem H.adv_mem (h : H P L x U) {T : Nat}
    (hT : ∀ w < x.n, (x.evN w).isW = true → κ x (fstU x w) = T → ∀ l ∈ P.locs,
      (x.evN w).covers l.addr = true → False) : nMem P x (T + 1) = nMem P x T :=
  h.nMem_succ fun l hl w hw hW hc he => hT w hw hW he l hl hc

/-- No native store has clock `T` unless it is the unit `u`. -/
theorem H.nst_at (h : H P L x U) {T i c k : Nat} (hi : i < P.threads.length) (hc : c < (L i).length)
    (hk : k < (labRoles (L i)[c]).length) (hu : κ x (pidx x i (base L i c + k)) = T) {j c' : Nat}
    (hc' : c' < (L j).length) {e : Nat × Nat × Nat} (he : e ∈ nsts (L j)[c'])
    (hκ : κ x (pidx x j (base L j c' + e.1)) = T) : j = i ∧ c' = c ∧ e.1 = k := by
  have hj : j < P.threads.length := by
    by_contra hn
    have hc'' := hc'
    rw [h.lout j (by omega)] at hc''
    simp at hc''
  obtain ⟨hw, -⟩ := h.nst_unit hj hc' he
  obtain ⟨hu', -⟩ := h.at hi hc hk
  have := h.κ_inj hw hu' (by rw [hκ, hu])
  exact h.ident hi hc hk hj hc' (nsts_role he).1 this

/-- The trigger with clock `T` is the unit `u`. -/
theorem H.trig_at (h : H P L x U) {T i c k : Nat} (hi : i < P.threads.length) (hc : c < (L i).length)
    (hk : k < (labRoles (L i)[c]).length) (hu : κ x (pidx x i (base L i c + k)) = T) {j c' k' : Nat}
    (hc' : c' < (L j).length) (ht : trig (L j)[c'] = some k')
    (hκ : κ x (pidx x j (base L j c' + k')) = T) : j = i ∧ c' = c ∧ k' = k := by
  have hj : j < P.threads.length := by
    by_contra hn
    have hc'' := hc'
    rw [h.lout j (by omega)] at hc''
    simp at hc''
  obtain ⟨hk', hw, -⟩ := h.trig_unit hj hc' ht
  obtain ⟨hu', -⟩ := h.at hi hc hk
  have := h.κ_inj hw hu' (by rw [hκ, hu])
  exact h.ident hi hc hk hj hc' hk' this

theorem Inv.succ {T : Nat} {cnt : Nat → Nat} (hI : Inv L x T cnt)
    (htr : ∀ j c (hc : c < (L j).length) k, trig (L j)[c] = some k →
      κ x (pidx x j (base L j c + k)) = T → c < cnt j)
    (hst : ∀ j c (hc : c < (L j).length), ∀ e ∈ nsts (L j)[c],
      κ x (pidx x j (base L j c + e.1)) = T → c < cnt j) : Inv L x (T + 1) cnt := by
  refine ⟨hI.le, fun j c hc k h1 h2 => by have := hI.past j c hc k h1 h2; omega,
    fun j c hc k ht hk => ?_, fun j c hc e he hk => ?_⟩
  · rcases Nat.lt_or_ge (κ x (pidx x j (base L j c + k))) T with h1 | h1
    · exact hI.trigDone j c hc k ht h1
    · exact htr j c hc k ht (by omega)
  · rcases Nat.lt_or_ge (κ x (pidx x j (base L j c + e.1))) T with h1 | h1
    · exact hI.stDone j c hc e he h1
    · exact hst j c hc e he (by omega)

/-- **A tick without a unit.** -/
theorem H.tick_none (h : H P L x U) {T : Nat} {cnt : Nat → Nat} (hno : ∀ u < x.n, κ x u ≠ T)
    (hI : Inv L x T cnt) (hR : Reach P L x S T cnt) :
    Inv L x (T + 1) cnt ∧ Reach P L x S (T + 1) cnt := by
  have hmem : nMem P x (T + 1) = nMem P x T :=
    h.adv_mem fun w hw _ he => absurd he (hno _ (h.fst_spec hw).1)
  have hbuf : ∀ j, nBuf L x (T + 1) cnt j = nBuf L x T cnt j := fun j =>
    nBuf_succT fun c hc e he hκ => by
      have hj : j < P.threads.length := by
        by_contra hn
        have hc'' := hc
        rw [h.lout j (by omega)] at hc''
        simp at hc''
      exact hno _ (h.nst_unit hj hc he).1 hκ
  refine ⟨hI.succ (fun j c hc k ht hk => ?_) (fun j c hc e he hk => ?_), ?_⟩
  · have hj : j < P.threads.length := by
      by_contra hn
      have hc'' := hc
      rw [h.lout j (by omega)] at hc''
      simp at hc''
    exact absurd hk (hno _ (h.trig_unit hj hc ht).2.1)
  · have hj : j < P.threads.length := by
      by_contra hn
      have hc'' := hc
      rw [h.lout j (by omega)] at hc''
      simp at hc''
    exact absurd hk (hno _ (h.nst_unit hj hc he).1)
  · unfold Reach at hR ⊢
    have : cfg P L x S (T + 1) cnt = cfg P L x S T cnt := by
      simp only [cfg, hmem, OCfg.mk.injEq, true_and]; funext j; exact hbuf j
    rw [this]; exact hR

/-- **A tick of a unit that is no trigger and no native store.** -/
theorem H.tick_other (h : H P L x U) {T : Nat} {cnt : Nat → Nat} {i c k : Nat}
    (hi : i < P.threads.length) (hc : c < (L i).length) (hk : k < (labRoles (L i)[c]).length)
    (hu : κ x (pidx x i (base L i c + k)) = T) (hnt : trig (L i)[c] ≠ some k)
    (hns : ∀ e ∈ nsts (L i)[c], e.1 ≠ k)
    (hI : Inv L x T cnt) (hR : Reach P L x S T cnt) :
    Inv L x (T + 1) cnt ∧ Reach P L x S (T + 1) cnt := by
  obtain ⟨hun, heu, -⟩ := h.at hi hc hk
  have hmem : nMem P x (T + 1) = nMem P x T := by
    refine h.adv_mem fun w hw hW he l hl hcov => ?_
    have hfu : fstU x w = pidx x i (base L i c + k) :=
      h.κ_inj (h.fst_spec hw).1 hun (by rw [he, hu])
    have hlow := h.lf.below l hl
    have hlsz := h.lf.size l hl
    rw [covers_iff] at hcov
    cases hlw : isLW (x.evN w)
    · rw [fst_of hlw] at hfu
      subst hfu
      rw [heu] at hW hlw hcov
      rcases role_W hW with ⟨a, sz, v, hr⟩ | ⟨a, sz, v, hr⟩
      · rw [hr] at hcov
        simp only [Role.ev] at hcov
        have hn : ¬ (k, a, v) ∈ nsts (L i)[c] := fun hm => hns _ hm rfl
        by_cases ha : a < ctlAddr 0
        · exact hn (role_nsts hk hr ha)
        · omega
      · rw [hr] at hlw; simp [isLW, Role.ev, Ev.isW] at hlw
    · obtain ⟨r, hr', ht', hp', hlr, ha', -⟩ := h.partnerW hw hlw
      rw [h.fst_lw hlw hr' ht' hp'] at hfu
      subst hfu
      rw [heu] at hlr ha'
      obtain ⟨a, sz, v, hrole⟩ := role_isLR hlr
      have := lr_ghost hk hrole hnt
      rw [hrole] at ha'
      simp only [Role.ev] at ha'
      omega
  have hbuf : ∀ j, nBuf L x (T + 1) cnt j = nBuf L x T cnt j := fun j =>
    nBuf_succT fun c' hc' e he hκ => by
      obtain ⟨rfl, rfl, he1⟩ := h.nst_at hi hc hk hu hc' he hκ
      exact hns e he he1
  refine ⟨hI.succ (fun j c' hc' k' ht hk' => ?_) (fun j c' hc' e he hk' => ?_), ?_⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h.trig_at hi hc hk hu hc' ht hk'
    exact absurd ht hnt
  · obtain ⟨rfl, rfl, he1⟩ := h.nst_at hi hc hk hu hc' he hk'
    exact absurd he1 (hns e he)
  · unfold Reach at hR ⊢
    have : cfg P L x S (T + 1) cnt = cfg P L x S T cnt := by
      simp only [cfg, hmem, OCfg.mk.injEq, true_and]; funext j; exact hbuf j
    rw [this]; exact hR


/-- At `T + 1` the buffer of a thread loses exactly its entry at the position of the write with
clock `T`. -/
theorem H.labEnts_drop (h : H P L x U) {T i p : Nat} (hi : i < P.threads.length)
    (hp : p < (RL L i).length) (hκ : κ x (pidx x i p) = T)
    (hW : (x.evN (pidx x i p)).isW = true) (c : Nat) :
    labEnts L x (T + 1) i c = (labEnts L x T i c).filter fun q => q.1 ≠ p := by
  obtain ⟨hpu, hpe, -⟩ := h.atPos hi hp
  by_cases hc : c < (L i).length
  · rw [labEnts_get hc, labEnts_get hc]
    split
    · rename_i hs
      have hk0 : 0 < (labRoles (L i)[c]).length := by rw [hs]; simp [labRoles]
      obtain ⟨hf, hfe, -⟩ := h.at hi hc hk0
      have hne : base L i c ≠ p := by
        intro he
        have : pidx x i (base L i c + 0) = pidx x i p := by rw [Nat.add_zero, he]
        rw [this] at hfe
        rw [hfe] at hW
        simp [hs, labRoles, Role.ev, Ev.isW] at hW
      simp [hne]
    · rw [List.filter_map, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro e he
      obtain ⟨hw, -, -, -, hwp, -⟩ := h.nst_unit hi hc he
      simp only [Function.comp, ne_eq, decide_not]
      by_cases hq : base L i c + e.1 = p
      · have : pidx x i (base L i c + e.1) = pidx x i p := by rw [hq]
        rw [this, hκ]; simp [hq]
      · have hne : κ x (pidx x i (base L i c + e.1)) ≠ T := by
          intro he'
          have := h.κ_inj hw hpu (by rw [he', hκ])
          have h2 := congrArg (fun v => (x.evN v).pos) this
          simp only [hwp, hpe, Role.ev_pos] at h2
          exact hq h2
        have hiff : (T + 1 ≤ κ x (pidx x i (base L i c + e.1))) ↔
            (T ≤ κ x (pidx x i (base L i c + e.1))) := by omega
        simp [hq, hiff]
  · simp [labEnts, List.getElem?_eq_none (show (L i).length ≤ c by omega)]

theorem H.rawP_drop (h : H P L x U) {T i p : Nat} (hi : i < P.threads.length)
    (hp : p < (RL L i).length) (hκ : κ x (pidx x i p) = T)
    (hW : (x.evN (pidx x i p)).isW = true) (cnt : Nat → Nat) :
    rawP L x (T + 1) cnt i = (rawP L x T cnt i).filter fun q => q.1 ≠ p := by
  simp only [rawP, List.filter_flatMap]
  exact List.flatMap_congr fun c _ => h.labEnts_drop hi hp hκ hW c

theorem dropWhile_bars {A : List Ent} (hA : ∀ e ∈ A, e = .bar) (m : List Ent) :
    (A ++ m).dropWhile (· == .bar) = m.dropWhile (· == .bar) := by
  induction A with
  | nil => rfl
  | cons e A ih =>
    rw [hA e List.mem_cons_self]
    simp only [List.cons_append, List.dropWhile_cons, beq_self_eq_true, ↓reduceIte]
    exact ih fun e' he' => hA e' (List.mem_cons_of_mem _ he')

/-- **A tick of a native store**: its label runs if it has not yet, and the store is flushed. -/
theorem H.tick_store (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat}
    {i c : Nat} {e : Nat × Nat × Nat} (hi : i < P.threads.length) (hc : c < (L i).length)
    (he : e ∈ nsts (L i)[c]) (hu : κ x (pidx x i (base L i c + e.1)) = T)
    (hI : Inv L x T cnt) (hR : Reach P L x S T cnt) :
    ∃ cnt', Inv L x (T + 1) cnt' ∧ Reach P L x S (T + 1) cnt' := by
  obtain ⟨hk, sz, hrole, hcell, hfit, hun, heu, hval⟩ := h.nst hi hc he
  obtain ⟨hun', hW, hlw, htu, hpu, hau⟩ := h.nst_unit hi hc he
  -- run the label if needed
  obtain ⟨cnt₁, hI₁, hR₁, hc₁⟩ : ∃ cnt₁ : Nat → Nat, Inv L x T cnt₁ ∧ Reach P L x S T cnt₁ ∧
      c < cnt₁ i := by
    by_cases hex : c < cnt i
    · exact ⟨cnt, hI, hR, hex⟩
    · obtain ⟨hI', hR'⟩ := hr.catchupTo h hI hR hi hc hk (isM_W hW) (le_of_eq hu) (by omega)
      have hlz : trig (L i)[c] = none := by
        cases ht : trig (L i)[c] with
        | none => rfl
        | some k' =>
          exfalso
          obtain ⟨hk', hu', hR'', htu', hpu'⟩ := h.trig_unit hi hc ht
          have hlt := trig_lt_nsts ht he
          have := h.κ_ppoR hu' hun' (by rw [htu', htu]) (by rw [hpu', hpu]; omega) hR'' (isM_W hW)
          have := hI'.trigDone i c hc k' ht (by omega)
          simp [upd] at this
      have s := hr.lazyStepAt h hi (T := T) (cnt := upd cnt i c) (by simp) hc hlz
        (fun e' he' => by
          by_contra hlt
          have := hI'.stDone i c hc e' he' (by omega)
          simp [upd] at this)
        (fun hm => by rw [hm] at he; simp [nsts] at he)
      refine ⟨_, ?_, star_trans hR' s, by simp⟩
      have := hI'.upd_mono (i := i) (v := c + 1) (by simp [upd]) (by omega)
        (fun c' hc' h1 h2 => by
          simp only [upd_same] at h1
          obtain rfl : c' = c := by omega
          exact hlz)
      simpa [upd_upd] using this
  -- the buffer, split at the store
  have hq := rawP_mem (T := T) (cnt := cnt₁) hc₁ hc he (by rw [hu])
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hq
  have hsort := rawP_pairwise L x T cnt₁ i
  rw [hAB, List.pairwise_append, List.pairwise_cons] at hsort
  have hA : ∀ q ∈ A, q.2 = .bar := by
    intro q hqA
    have hqr : q ∈ rawP L x T cnt₁ i := by rw [hAB]; exact List.mem_append_left _ hqA
    have hlt := hsort.2.2 q hqA _ List.mem_cons_self
    obtain ⟨c', hcn', hq'⟩ := mem_rawP.mp hqr
    obtain ⟨hc', ⟨-, rfl⟩ | ⟨-, e', he', hT', rfl⟩⟩ := mem_labEnts hq'
    · rfl
    · exfalso
      obtain ⟨hw', hW', -, ht', hp', -⟩ := h.nst_unit hi hc' he'
      have := h.κ_ppoW hw' hun' (by rw [ht', htu]) (by rw [hp', hpu]; exact hlt) hW' hW
      omega
  have hbuf : nBuf L x T cnt₁ i = .st e.2.1 e.2.2 false :: B.map Prod.snd := by
    simp only [nBuf, hAB, List.map_append, List.map_cons]
    rw [dropWhile_bars (fun e' he' => by
      obtain ⟨q, hq', rfl⟩ := List.mem_map.mp he'; exact hA q hq')]
    simp
  have hp_lt : base L i c + e.1 < (RL L i).length := (RL_get hc hk).1
  have hW' : (x.evN (pidx x i (base L i c + e.1))).isW = true := hW
  have hbuf' : nBuf L x (T + 1) cnt₁ i = (B.map Prod.snd).dropWhile (· == .bar) := by
    simp only [nBuf, h.rawP_drop hi hp_lt hu hW' cnt₁, hAB, List.filter_append, List.filter_cons]
    rw [List.filter_eq_self.mpr (fun q hqA => by
        have := hsort.2.2 q hqA _ List.mem_cons_self; simp; omega),
      List.filter_eq_self.mpr (fun q hqB => by
        have := hsort.2.1.1 q hqB; simp; omega)]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
      List.map_append]
    exact dropWhile_bars (fun e' he' => by
      obtain ⟨q, hq', rfl⟩ := List.mem_map.mp he'; exact hA q hq') _
  -- flush
  have hf := reach_flush hi (cfg P L x S T cnt₁) hbuf
  obtain ⟨l, hlm, hla, hls, hszp, -⟩ := loc_of_cell h.lf hcell
  have hsz : (x.evN (pidx x i (base L i c + e.1))).size = sz := by rw [heu]; rfl
  have hmem : (fun y => if y = e.2.1 then some e.2.2 else nMem P x T y) = nMem P x (T + 1) := by
    funext y
    by_cases hy : y = e.2.1
    · subst hy
      rw [ite_eq_left rfl, ← hla, nMem_loc h.lf hlm, hla,
        h.cval_write hun' hW (by rw [covers_iff, hau, hsz]; omega) (by rw [fst_of hlw, hu]), hval]
      rfl
    · rw [ite_eq_right hy]
      unfold nMem
      cases hf' : P.locs.find? (fun l => l.addr == y) with
      | none => rfl
      | some l' =>
        have hm' := List.mem_of_find?_eq_some hf'
        have hp' := List.find?_some hf'
        simp only [beq_iff_eq] at hp'
        simp only [Option.map_some]
        rw [h.cval_same fun w hw hWw hcw hκw => ?_]
        have hfu := h.κ_inj (h.fst_spec hw).1 hun' (by rw [hκw, hu])
        cases hlww : isLW (x.evN w)
        · rw [fst_of hlww] at hfu
          subst hfu
          rw [covers_iff, hau, hsz] at hcw
          have := loc_cover h.lf hcell hm' (by omega) (by omega)
          exact hy (hp' ▸ this)
        · obtain ⟨r', hr', ht', hpp', hlr, -⟩ := h.partnerW hw hlww
          rw [h.fst_lw hlww hr' ht' hpp'] at hfu
          subst hfu
          simp only [isLR, Bool.and_eq_true] at hlr
          exact RW_false hlr.1 hW
  refine ⟨cnt₁, hI₁.succ (fun j c' hc' k' ht hk' => ?_) (fun j c' hc' e' he' hk' => ?_), ?_⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h.trig_at hi hc hk hu hc' ht hk'
    exact absurd rfl (nsts_not_trig ht he)
  · obtain ⟨rfl, rfl, -⟩ := h.nst_at hi hc hk hu hc' he' hk'
    exact hc₁
  · unfold Reach at hR₁ ⊢
    have : (⟨(cfg P L x S T cnt₁).ts, fun y => if y = e.2.1 then some e.2.2 else (cfg P L x S T cnt₁).mem y,
        upd (cfg P L x S T cnt₁).buf i ((B.map Prod.snd).dropWhile (· == .bar))⟩ : OCfg) =
        cfg P L x S (T + 1) cnt₁ := by
      simp only [cfg, OCfg.mk.injEq, true_and]
      refine ⟨hmem, ?_⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp [hbuf']
      · rw [upd_ne _ _ hj]
        exact (nBuf_succT fun c' hc' e' he' hκ => by
          obtain ⟨rfl, -, -⟩ := h.nst_at hi hc hk hu hc' he' hκ; exact hj rfl).symm
    rw [← this]; exact star_trans hR₁ hf

end

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
