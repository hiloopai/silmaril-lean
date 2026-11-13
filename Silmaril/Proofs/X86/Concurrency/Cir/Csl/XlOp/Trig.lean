module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Run

/-!
# The XL bridge: ticks of triggers

Proofs for `Csl.Task.cirXlOpAx`. At the tick of its trigger a label runs, after
its thread caught up to it: a load or a block reads its view (`H.readOK`; for a block every
load, which no other thread can tear, `Runs.interfere`), a read-modify-write or a futex call
finds its buffer empty and acts on memory.
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

/-- At the tick of a plain read nothing else changes. -/
theorem H.adv_read (h : H P L x U) {T u : Nat} (hu : u < x.n) (hκ : κ x u = T)
    (hR : (x.evN u).isR = true) (hlr : isLR (x.evN u) = false) {cnt : Nat → Nat} :
    nMem P x (T + 1) = nMem P x T ∧ ∀ j, nBuf L x (T + 1) cnt j = nBuf L x T cnt j := by
  refine ⟨h.adv_mem fun w hw hW he l hl hc => ?_, fun j => nBuf_succT fun c hc e he hκ' => ?_⟩
  · have hfu := h.κ_inj (h.fst_spec hw).1 hu (by rw [he, hκ])
    cases hlw : isLW (x.evN w)
    · rw [fst_of hlw] at hfu; subst hfu; exact RW_false hR hW
    · obtain ⟨r', hr', ht', hp', hlr', -⟩ := h.partnerW hw hlw
      rw [h.fst_lw hlw hr' ht' hp'] at hfu; subst hfu; rw [hlr] at hlr'; cases hlr'
  · have hj : j < P.threads.length := by
      by_contra hn
      have hc'' := hc
      rw [h.lout j (by omega)] at hc''
      simp at hc''
    obtain ⟨hw, hW, -⟩ := h.nst_unit hj hc he
    have := h.κ_inj hw hu (by rw [hκ', hκ])
    rw [this] at hW; exact RW_false hR hW

/-- The invariant after a trigger's label ran. -/
theorem Inv.after_trig (h : H P L x U) {T : Nat} {cnt : Nat → Nat} {i c k : Nat}
    (hi : i < P.threads.length) (hc : c < (L i).length) (ht : trig (L i)[c] = some k)
    (hu : κ x (pidx x i (base L i c + k)) = T) (hI : Inv L x T cnt) (hcn : cnt i = c) :
    Inv L x (T + 1) (upd cnt i (c + 1)) := by
  have hk := (h.trig_unit hi hc ht).1
  refine ⟨fun j => ?_, fun j c' hc' k' h1 h2 => ?_, fun j c' hc' k' h1 h2 => ?_,
    fun j c' hc' e he h1 => ?_⟩
  · by_cases hj : j = i
    · subst hj; simp; omega
    · rw [upd_ne _ _ hj]; exact hI.le j
  · by_cases hj : j = i
    · subst hj
      rw [upd_same] at h1
      by_cases hcc : c' = c
      · subst hcc; rw [ht, Option.some.injEq] at h2; subst h2; omega
      · have := hI.past j c' hc' k' (by omega) h2; omega
    · rw [upd_ne _ _ hj] at h1; have := hI.past j c' hc' k' h1 h2; omega
  · rcases Nat.lt_or_ge (κ x (pidx x j (base L j c' + k'))) T with h3 | h3
    · have := hI.trigDone j c' hc' k' h1 h3
      by_cases hj : j = i
      · subst hj; rw [upd_same]; omega
      · rw [upd_ne _ _ hj]; exact this
    · obtain ⟨rfl, rfl, rfl⟩ := h.trig_at hi hc hk hu hc' h1 (by omega)
      rw [upd_same]; omega
  · rcases Nat.lt_or_ge (κ x (pidx x j (base L j c' + e.1))) T with h3 | h3
    · have := hI.stDone j c' hc' e he h3
      by_cases hj : j = i
      · subst hj; rw [upd_same]; omega
      · rw [upd_ne _ _ hj]; exact this
    · obtain ⟨rfl, rfl, he1⟩ := h.nst_at hi hc hk hu hc' he (by omega)
      exact absurd he1 (nsts_not_trig ht he)

theorem view_nil (M : Heap) (a : Nat) : view M [] a = M a := by simp [view, newest]


theorem H.adv_bufR (h : H P L x U) {T u : Nat} (hu : u < x.n) (hκ : κ x u = T)
    (hR : (x.evN u).isR = true) {cnt : Nat → Nat} (j : Nat) :
    nBuf L x (T + 1) cnt j = nBuf L x T cnt j := by
  refine nBuf_succT fun c hc e he hκ' => ?_
  have hj : j < P.threads.length := by
    by_contra hn
    have hc'' := hc
    rw [h.lout j (by omega)] at hc''
    simp at hc''
  obtain ⟨hw, hW, -⟩ := h.nst_unit hj hc he
  have := h.κ_inj hw hu (by rw [hκ', hκ])
  rw [this] at hW; exact RW_false hR hW

theorem cfg_succ_eq {P : Prog} {L : Nat → List Lab} {x : Exec} {S : Nat → Nat → Stmt × Regs}
    {T : Nat} {cnt : Nat → Nat} (hm : nMem P x (T + 1) = nMem P x T)
    (hb : ∀ j, nBuf L x (T + 1) cnt j = nBuf L x T cnt j) :
    cfg P L x S (T + 1) cnt = cfg P L x S T cnt := by
  simp only [cfg, hm, OCfg.mk.injEq, true_and]; funext j; exact hb j

theorem updH_none {l : Lab} (hl : ∀ a, l.wval a = none) (M : Heap) : l.updH M = M := by
  funext a; simp [Lab.updH, hl a]

/-- The facts of a load role of label `c`. -/
theorem H.ldAt (h : H P L x U) {i c k : Nat} (hi : i < P.threads.length) (hc : c < (L i).length)
    (hk : k < (labRoles (L i)[c]).length) {a sz v : Nat} (hrole : (labRoles (L i)[c])[k] = .ld a sz v) :
    pidx x i (base L i c + k) < x.n ∧ (x.evN (pidx x i (base L i c + k))).isR = true ∧
      isLR (x.evN (pidx x i (base L i c + k))) = false ∧
      (x.evN (pidx x i (base L i c + k))).tid = i ∧
      (x.evN (pidx x i (base L i c + k))).pos = base L i c + k ∧
      (x.evN (pidx x i (base L i c + k))).addr = a ∧ (x.evN (pidx x i (base L i c + k))).size = sz ∧
      ex U (pidx x i (base L i c + k)) = natBytes v sz := by
  obtain ⟨hu, he, hx⟩ := h.at hi hc hk
  rw [hrole] at he hx
  rw [he]
  exact ⟨hu, rfl, by simp [isLR, Role.ev], by simp, by simp, rfl, rfl, hx⟩

/-- A read of a location's cell at its own tick (or a later one, given `NI`) sees `v`. -/
theorem H.readV (h : H P L x U) {T i c k : Nat} {cnt : Nat → Nat} (_hi : i < P.threads.length)
    (hc : c < (L i).length) (hk : k < (labRoles (L i)[c]).length) (hcn : cnt i = c)
    {a sz v : Nat} (hcell : (a, sz) ∈ cellsOf P.locs) (hv : v < 2 ^ (8 * sz))
    (hu : pidx x i (base L i c + k) < x.n) (hR : (x.evN (pidx x i (base L i c + k))).isR = true)
    (ht : (x.evN (pidx x i (base L i c + k))).tid = i)
    (hp : (x.evN (pidx x i (base L i c + k))).pos = base L i c + k)
    (ha : (x.evN (pidx x i (base L i c + k))).addr = a)
    (hs : (x.evN (pidx x i (base L i c + k))).size = sz)
    (hex : ex U (pidx x i (base L i c + k)) = natBytes v sz)
    (hT : κ x (pidx x i (base L i c + k)) ≤ T) (hNI : NI x (pidx x i (base L i c + k)) T) :
    view (nMem P x T) (nBuf L x T cnt i) a = some v := by
  obtain ⟨l, hlm, hla, hls, -, -⟩ := loc_of_cell h.lf hcell
  have h1 := h.readOK hu hR ht hc hk hp hcn hT hlm (by rw [hla, ha]) (by rw [hls, hs]) hNI
  rw [ha] at h1
  rw [h1, h.srcVal_eq hu hR (by rw [hs]; exact hex) (by rw [hs]; exact hv) hlm (by rw [hla, ha])
    (by rw [hls, hs])]


/-- **A load.** -/
theorem H.trig_rd (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat} {i c : Nat}
    (hi : i < P.threads.length) (hc : c < (L i).length) (hcn : cnt i = c)
    (hR : Reach P L x S T cnt) {m : Mode} {fl : Flav} {a sz v : Nat}
    (hl : (L i)[c] = .rd m fl a sz v) (hu : κ x (pidx x i (base L i c + 0)) = T) :
    Reach P L x S (T + 1) (upd cnt i (c + 1)) := by
  obtain ⟨hG, bs, hok⟩ := h.lab i _ (List.getElem_mem hc)
  have hok' := hok; rw [hl] at hok'
  have hk : 0 < (labRoles (L i)[c]).length := by rw [hl]; simp [labRoles]
  have hrole : (labRoles (L i)[c])[0] = .ld a sz v := by simp [hl, labRoles]
  obtain ⟨hun, hRu, hlr, htu, hpu, hau, hsu, hex⟩ := h.ldAt hi hc hk hrole
  have hview := h.readV hi hc hk hcn hok'.1 hok'.2 hun hRu htu hpu hau hsu hex (le_of_eq hu)
    (hu ▸ h.ni_self hun hRu)
  have s := hr.step_bufAt (x := x) (T := T) hi hcn hc (by rw [hl]; rfl) (by rw [hl]; rfl)
    (fun a' ha' => by obtain ⟨sz', hsz'⟩ := touch_loc hok ha'; exact nMem_some h.lf hsz')
    (by rw [hl]; intro p hp; simp only [Lab.reads, List.mem_singleton] at hp; subst hp; exact hview)
    (labEnts_ents hc hG fun e he => by rw [hl] at he; simp [nsts] at he)
  obtain ⟨hm, hb⟩ := h.adv_read hun hu hRu hlr (cnt := upd cnt i (c + 1))
  unfold Reach at hR ⊢
  rw [cfg_succ_eq hm hb]
  exact star_trans hR s

/-- **A read-modify-write.** -/
theorem H.trig_rmw (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat} {i c : Nat}
    (hi : i < P.threads.length) (hc : c < (L i).length) (hcn : cnt i = c)
    (hR : Reach P L x S T cnt) {m : Mode} {a sz o n : Nat}
    (hl : (L i)[c] = .rmw m a sz o n) (hu : κ x (pidx x i (base L i c + 0)) = T) :
    Reach P L x S (T + 1) (upd cnt i (c + 1)) := by
  obtain ⟨hG, bs, hok⟩ := h.lab i _ (List.getElem_mem hc)
  have hok' := hok; rw [hl] at hok'
  have hk : 0 < (labRoles (L i)[c]).length := by rw [hl]; simp [labRoles]
  have hk1 : 1 < (labRoles (L i)[c]).length := by rw [hl]; simp [labRoles]
  obtain ⟨hun, heu, hex⟩ := h.at hi hc hk
  obtain ⟨hw1, hew1, -⟩ := h.at hi hc hk1
  have hr0 : (labRoles (L i)[c])[0] = .lr a sz o := by simp [hl, labRoles]
  have hr1 : (labRoles (L i)[c])[1] = .lw a sz n := by simp [hl, labRoles]
  rw [hr0] at heu hex
  rw [hr1] at hew1
  have hRu : (x.evN (pidx x i (base L i c + 0))).isR = true := by rw [heu]; rfl
  have hAu : (x.evN (pidx x i (base L i c + 0))).isA = true := by rw [heu]; rfl
  obtain ⟨l, hlm, hla, hls, hszp, -⟩ := loc_of_cell h.lf hok'.1
  -- the buffer is empty: `implied` orders earlier stores before the locked read
  have he : nBuf L x T cnt i = [] := nBuf_nil fun c' hc' hlt e he => by
    obtain ⟨hw, hW, -, ht', hp', -⟩ := h.nst_unit hi hc' he
    have := h.κ_impl hw hun (by rw [ht', heu]; simp)
      (by rw [hp', heu]; simpa using lab_lt (k' := 0) hc' (nsts_role he).1 (show c' < c by omega))
      hW hRu (.inr hAu)
    omega
  have hview := h.readV (cnt := cnt) hi hc hk hcn hok'.1 hok'.2.1 hun hRu (by rw [heu]; simp)
    (by rw [heu]; simp) (by rw [heu]; rfl) (by rw [heu]; rfl) hex (le_of_eq hu)
    (hu ▸ h.ni_self hun hRu)
  rw [he, view_nil] at hview
  have s := hr.step_drainAt (x := x) (T := T) hi hcn hc (by rw [hl]; rfl) (by rw [hl]; rfl) he
    (fun a' ha' => by obtain ⟨sz', hsz'⟩ := touch_loc hok ha'; exact nMem_some h.lf hsz')
    (by rw [hl]; intro p hp; simp only [Lab.reads, List.mem_singleton] at hp; subst hp; exact hview)
    (by rw [labEnts_get hc, hl]; simp [nsts])
  -- the new memory
  have hW1 : (x.evN (pidx x i (base L i c + 1))).isW = true := by rw [hew1]; rfl
  have hlw1 : isLW (x.evN (pidx x i (base L i c + 1))) = true := by rw [hew1]; rfl
  have hfst1 : fstU x (pidx x i (base L i c + 1)) = pidx x i (base L i c + 0) :=
    h.fst_lw hlw1 hun (by rw [heu, hew1]; simp) (by rw [heu, hew1]; simp)
  have hmem : (L i)[c].updH (nMem P x T) = nMem P x (T + 1) := by
    funext y
    rw [hl]
    simp only [Lab.updH, Lab.wval]
    by_cases hy : a = y
    · subst hy
      rw [ite_eq_left rfl, Option.some_or, ← hla, nMem_loc h.lf hlm (T := T + 1), hla,
        h.cval_write hw1 hW1 (by rw [hew1, covers_iff]; simp only [Role.ev]; omega)
          (by rw [hfst1, hu])]
      simp only [Option.getD_some, wval, hew1, Role.ev]
      rw [bval_natBytes _ _ hok'.2.2]
    · rw [ite_eq_right hy, Option.none_or]
      unfold nMem
      cases hf' : P.locs.find? (fun l => l.addr == y) with
      | none => rfl
      | some l' =>
        have hm' := List.mem_of_find?_eq_some hf'
        have hp' := List.find?_some hf'
        simp only [beq_iff_eq] at hp'
        simp only [Option.map_some]
        rw [h.cval_same fun w hw hWw hcw hκw => ?_]
        have hfu := h.κ_inj (h.fst_spec hw).1 hun (by rw [hκw, hu])
        cases hlww : isLW (x.evN w)
        · rw [fst_of hlww] at hfu; subst hfu; exact RW_false hRu hWw
        · obtain ⟨r', hr', ht', hpp', -⟩ := h.partnerW hw hlww
          rw [h.fst_lw hlww hr' ht' hpp'] at hfu
          subst hfu
          have hw1e : w = pidx x i (base L i c + 1) :=
            h.uniq hw hw1 (by rw [← ht', heu, hew1]; simp) (by rw [hpp', heu, hew1]; simp)
          subst hw1e
          rw [hew1, covers_iff] at hcw
          simp only [Role.ev] at hcw
          exact hy (by have := loc_cover h.lf hok'.1 hm' (by omega) (by omega); rw [← this, hp'])
  unfold Reach at hR ⊢
  have heq : cfg P L x S (T + 1) (upd cnt i (c + 1)) =
      ⟨fun j => S j (upd cnt i (c + 1) j), (L i)[c].updH (nMem P x T),
        nBuf L x T (upd cnt i (c + 1))⟩ := by
    simp only [cfg, hmem, OCfg.mk.injEq, true_and]
    funext j; exact h.adv_bufR hun hu hRu j
  rw [heq]
  exact star_trans hR s


/-- The buffer is empty at a unit after an `mfence` at offset `0` of its label. -/
theorem H.buf_mf (h : H P L x U) {T : Nat} {cnt : Nat → Nat} {i c k : Nat}
    (hi : i < P.threads.length) (hc : c < (L i).length) (hcn : cnt i = c)
    (hk : k < (labRoles (L i)[c]).length) (hk0 : 0 < k)
    (hf : (labRoles (L i)[c])[0]'(by omega) = .fn .mfence)
    (hu : κ x (pidx x i (base L i c + k)) = T) : nBuf L x T cnt i = [] := by
  obtain ⟨hun, heu, -⟩ := h.at hi hc hk
  obtain ⟨hfn, hfe, -⟩ := h.at hi hc (show 0 < (labRoles (L i)[c]).length by omega)
  rw [hf] at hfe
  refine nBuf_nil fun c' hc' hlt e he => ?_
  obtain ⟨hw, hW, -, ht', hp', -⟩ := h.nst_unit hi hc' he
  have := h.κ_mf hw hun hfn (by rw [hfe]; rfl) (by rw [ht', hfe]; simp)
    (by rw [hp', hfe]; simpa using lab_lt (k' := 0) hc' (nsts_role he).1 (show c' < c by omega))
    (by rw [hfe, heu]; simp) (by rw [hfe, heu]; simp; omega)
  omega

/-- **A futex wait.** -/
theorem H.trig_fwait (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat}
    {i c k : Nat} (hi : i < P.threads.length) (hc : c < (L i).length) (hcn : cnt i = c)
    (hR : Reach P L x S T cnt) {a e s r : Nat}
    (hl : (L i)[c] = .fwait a e s r) (hkv : k = if s = e then 3 else 1)
    (hu : κ x (pidx x i (base L i c + k)) = T) :
    Reach P L x S (T + 1) (upd cnt i (c + 1)) := by
  obtain ⟨hG, bs, hok⟩ := h.lab i _ (List.getElem_mem hc)
  have hok' := hok; rw [hl] at hok'
  have hk : k < (labRoles (L i)[c]).length := by
    rw [hl, hkv]; simp only [labRoles]; split <;> simp
  have hrole : (labRoles (L i)[c])[k] = .ld a 4 s := by
    simp only [hl, labRoles, hkv]; split <;> simp
  have hf : (labRoles (L i)[c])[0]'(by omega) = .fn .mfence := by
    simp only [hl, labRoles]; split <;> simp
  obtain ⟨hun, hRu, hlr, htu, hpu, hau, hsu, hex⟩ := h.ldAt hi hc hk hrole
  have he := h.buf_mf (cnt := cnt) hi hc hcn hk (by rw [hkv]; split <;> omega) hf hu
  have hview := h.readV (cnt := cnt) hi hc hk hcn hok'.1 hok'.2.1 hun hRu htu hpu hau hsu hex
    (le_of_eq hu) (hu ▸ h.ni_self hun hRu)
  rw [he, view_nil] at hview
  have s := hr.step_drainAt (x := x) (T := T) hi hcn hc (by rw [hl]; rfl) (by rw [hl]; rfl) he
    (fun a' ha' => by obtain ⟨sz', hsz'⟩ := touch_loc hok ha'; exact nMem_some h.lf hsz')
    (by rw [hl]; intro p hp; simp only [Lab.reads, List.mem_singleton] at hp; subst hp; exact hview)
    (by rw [labEnts_get hc, hl]; simp [nsts])
  rw [updH_none (by rw [hl]; intro; rfl)] at s
  obtain ⟨hm, hb⟩ := h.adv_read hun hu hRu hlr (cnt := upd cnt i (c + 1))
  unfold Reach at hR ⊢
  rw [cfg_succ_eq hm hb]
  exact star_trans hR s

/-- **A futex wake.** -/
theorem H.trig_fwake (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat}
    {i c : Nat} (hi : i < P.threads.length) (hc : c < (L i).length) (hcn : cnt i = c)
    (hR : Reach P L x S T cnt) {a n q : Nat}
    (hl : (L i)[c] = .fwake a n q) (hu : κ x (pidx x i (base L i c + 1)) = T) :
    Reach P L x S (T + 1) (upd cnt i (c + 1)) := by
  have hk : 1 < (labRoles (L i)[c]).length := by rw [hl]; simp [labRoles]
  have hrole : (labRoles (L i)[c])[1] = .lr (qAddr a) 1 q := by simp [hl, labRoles]
  have hf : (labRoles (L i)[c])[0]'(by omega) = .fn .mfence := by simp [hl, labRoles]
  obtain ⟨hun, heu, -⟩ := h.at hi hc hk
  rw [hrole] at heu
  have hRu : (x.evN (pidx x i (base L i c + 1))).isR = true := by rw [heu]; rfl
  have he := h.buf_mf (cnt := cnt) hi hc hcn hk (by omega) hf hu
  have s := hr.step_drainAt (x := x) (T := T) hi hcn hc (by rw [hl]; rfl) (by rw [hl]; rfl) he
    (fun a' ha' => by
      rw [hl] at ha'
      rcases ha' with ⟨v, hv⟩ | hw
      · simp [Lab.reads] at hv
      · simp [Lab.wval] at hw)
    (by rw [hl]; intro p hp; simp [Lab.reads] at hp)
    (by rw [labEnts_get hc, hl]; simp [nsts])
  rw [updH_none (by rw [hl]; intro; rfl)] at s
  have hm : nMem P x (T + 1) = nMem P x T := by
    refine h.adv_mem fun w hw hW he' l hl' hcov => ?_
    have hfu := h.κ_inj (h.fst_spec hw).1 hun (by rw [he', hu])
    cases hlw : isLW (x.evN w)
    · rw [fst_of hlw] at hfu; subst hfu; exact RW_false hRu hW
    · obtain ⟨r', hr', ht', hp', -, ha', hs'⟩ := h.partnerW hw hlw
      rw [h.fst_lw hlw hr' ht' hp'] at hfu
      subst hfu
      rw [heu] at ha' hs'
      simp only [Role.ev] at ha' hs'
      rw [covers_iff, ha', hs'] at hcov
      have := Silmaril.Proofs.X86.Concurrency.Cir.Domain.ghost_q a
      have := h.lf.below l hl'
      have := h.lf.size l hl'
      omega
  unfold Reach at hR ⊢
  rw [cfg_succ_eq hm (fun j => h.adv_bufR hun hu hRu j)]
  exact star_trans hR s


/-- **A `local` block**, at the tick of its last load. -/
theorem H.trig_blk (h : H P L x U) (hr : Runs P L R S Pre) {I : HProp} {Q : Nat → Regs → HProp}
    {hs : Nat → Heap} {hI : Heap} (G : GInv I Q P.threads.length (progInit P) hs hI)
    {T : Nat} {cnt : Nat → Nat} {i c : Nat} (hi : i < P.threads.length) (hc : c < (L i).length)
    (hcn : cnt i = c) (hR : Reach P L x S T cnt) {nm : String} {ins outs : List (Nat × Nat × Nat)}
    {rvs : List Nat} (hl : (L i)[c] = .blk nm ins outs rvs) (hins : 0 < ins.length)
    (hu : κ x (pidx x i (base L i c + (ins.length - 1))) = T)
    (hist : ∀ τ < T, ∃ cnt, Inv L x τ cnt ∧ Reach P L x S τ cnt) :
    Reach P L x S (T + 1) (upd cnt i (c + 1)) := by
  obtain ⟨hG, bs, hok⟩ := h.lab i _ (List.getElem_mem hc)
  have hok' := hok; rw [hl] at hok'
  have hlen : (labRoles (L i)[c]).length = ins.length + outs.length := by
    rw [hl]; simp [labRoles]
  have hrole : ∀ j (hj : j < ins.length), (labRoles (L i)[c])[j]'(by omega) =
      .ld ins[j].1 ins[j].2.1 ins[j].2.2 := by
    intro j hj
    simp only [hl, labRoles]
    rw [List.getElem_append_left (by simpa using hj)]
    simp
  have htrig : trig (L i)[c] = some (ins.length - 1) := by
    rw [hl]; simp only [trig]; rw [ite_eq_right (List.ne_nil_of_length_pos hins)]
  have hk1 : ins.length - 1 < (labRoles (L i)[c]).length := by omega
  obtain ⟨hun, hRu, hlr, htu, hpu, -⟩ := h.ldAt hi hc hk1 (hrole _ (by omega))
  have hview : ∀ p ∈ (Lab.blk nm ins outs rvs).reads, view (nMem P x T) (nBuf L x T cnt i) p.1 = some p.2 := by
    intro p hp
    simp only [Lab.reads, List.mem_map] at hp
    obtain ⟨cc, hcc, rfl⟩ := hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcc
    have hkj : j < (labRoles (L i)[c]).length := by omega
    obtain ⟨hrj, hRj, -, htj, hpj, haj, hsj, hexj⟩ := h.ldAt hi hc hkj (hrole j hj)
    have hcell := hok'.1 ins[j] (List.mem_append_left _ (List.getElem_mem hj))
    have hκj : κ x (pidx x i (base L i c + j)) ≤ T := by
      rw [← hu]
      rcases Nat.lt_or_ge j (ins.length - 1) with hlt | hge
      · exact Nat.le_of_lt (h.κ_ppoR hrj hun (by rw [htj, htu]) (by rw [hpj, hpu]; omega)
          hRj (isM_R hRu))
      · rw [show j = ins.length - 1 by omega]
    exact h.readV hi hc hkj hcn hcell.1 hcell.2 hrj hRj htj hpj haj hsj hexj hκj
      (hr.interfere h G hi hc hl hins hu hist hj)
  have s := hr.step_bufAt (x := x) (T := T) hi hcn hc (by rw [hl]; rfl) (by rw [hl]; rfl)
    (fun a' ha' => by obtain ⟨sz', hsz'⟩ := touch_loc hok ha'; exact nMem_some h.lf hsz')
    (by rw [hl]; exact hview)
    (labEnts_ents hc hG fun e he => by
      obtain ⟨hw, hW, -, ht', hp', -⟩ := h.nst_unit hi hc he
      have hlt := trig_lt_nsts htrig he
      have := h.κ_ppoR hun hw (by rw [htu, ht']) (by rw [hpu, hp']; omega) hRu (isM_W hW)
      omega)
  obtain ⟨hm, hb⟩ := h.adv_read hun hu hRu hlr (cnt := upd cnt i (c + 1))
  unfold Reach at hR ⊢
  rw [cfg_succ_eq hm hb]
  exact star_trans hR s

/-- **A tick of a trigger.** -/
theorem H.tick_trig (h : H P L x U) (hr : Runs P L R S Pre) {I : HProp} {Q : Nat → Regs → HProp}
    {hs : Nat → Heap} {hI : Heap} (G : GInv I Q P.threads.length (progInit P) hs hI)
    {T : Nat} {cnt : Nat → Nat} {i c k : Nat} (hi : i < P.threads.length) (hc : c < (L i).length)
    (ht : trig (L i)[c] = some k) (hu : κ x (pidx x i (base L i c + k)) = T)
    (hI : Inv L x T cnt) (hR : Reach P L x S T cnt)
    (hist : ∀ τ < T, ∃ cnt, Inv L x τ cnt ∧ Reach P L x S τ cnt) :
    ∃ cnt', Inv L x (T + 1) cnt' ∧ Reach P L x S (T + 1) cnt' := by
  obtain ⟨hk, hun, hRu, htu, hpu⟩ := h.trig_unit hi hc ht
  have hcn : cnt i ≤ c := by
    by_contra hn
    have := hI.past i c hc k (by omega) ht
    omega
  obtain ⟨hI₁, hR₁⟩ := hr.catchupTo h hI hR hi hc hk (isM_R hRu) (le_of_eq hu) hcn
  have hcn₁ : upd cnt i c i = c := by simp
  refine ⟨_, hI₁.after_trig h hi hc ht hu hcn₁, ?_⟩
  have hreach : Reach P L x S (T + 1) (upd (upd cnt i c) i (c + 1)) := by
    obtain ⟨hG, -⟩ := h.lab i _ (List.getElem_mem hc)
    generalize hl : (L i)[c] = l at ht hG
    cases l with
    | rd m fl a sz v =>
      simp only [trig, Option.some.injEq] at ht; subst ht
      exact h.trig_rd hr hi hc hcn₁ hR₁ hl hu
    | rmw m a sz o n =>
      simp only [trig, Option.some.injEq] at ht; subst ht
      exact h.trig_rmw hr hi hc hcn₁ hR₁ hl hu
    | fwait a e s r =>
      simp only [trig] at ht
      exact h.trig_fwait hr hi hc hcn₁ hR₁ hl (by split at ht <;> simp_all) hu
    | fwake a n q =>
      simp only [trig, Option.some.injEq] at ht; subst ht
      exact h.trig_fwake hr hi hc hcn₁ hR₁ hl hu
    | blk nm ins outs rvs =>
      simp only [trig] at ht
      split at ht
      · cases ht
      · rename_i hn
        simp only [Option.some.injEq] at ht; subst ht
        exact h.trig_blk hr G hi hc hcn₁ hR₁ hl (List.length_pos_of_ne_nil hn) hu hist
    | _ => simp [trig] at ht
  simpa [upd_upd] using hreach

end

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
