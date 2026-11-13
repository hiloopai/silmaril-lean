module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.State

/-!
# The XL bridge: reads see the candidate's `rf`

Proofs for `Csl.Task.cirXlOpAx`: buffer facts (`H.rawP_st`, `H.rawP_mem`), and
`H.readOK`: a read of a location's cell, by a thread that has executed exactly the labels
before the read's, sees at tick `T ≥ κ r` the value `srcVal` of its `rf` source, provided no
write it reads before is visible at `T` (`NI`, automatic at `T = κ r`: `H.ni_self`).
`H.srcVal_eq`: that value is the value the read's label expects.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff WfFacts mem_touched natBytes_succ
  length_natBytes natBytes_inj cellsOf LocsFacts)
open Relation

/-! ## Locations -/

theorem find_loc {locs : List Loc} (hl : LocsFacts locs) {l : Loc} (hm : l ∈ locs) :
    locs.find? (fun l' => l'.addr == l.addr) = some l := by
  cases hf : locs.find? (fun l' => l'.addr == l.addr) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (hf l hm) (by simp)
  | some l' =>
    have hm' := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    have := hl.size l hm
    rcases hl.disj l hm l' hm' with rfl | h | h
    · rfl
    · omega
    · have := hl.size l' hm'; omega

theorem loc_of_cell {locs : List Loc} (hl : LocsFacts locs) {a sz : Nat}
    (h : (a, sz) ∈ cellsOf locs) : ∃ l ∈ locs, l.addr = a ∧ l.size = sz ∧ 0 < sz ∧
      a + sz ≤ ctlAddr 0 := by
  obtain ⟨l, hlm, he⟩ := List.mem_map.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have := hl.size l hlm
  exact ⟨l, hlm, rfl, rfl, by omega, hl.below l hlm⟩

theorem nMem_loc {P : Prog} {x : Exec} {T : Nat} (hl : LocsFacts P.locs) {l : Loc} (hm : l ∈ P.locs) :
    nMem P x T l.addr = some ((cval x T l.addr).getD l.init) := by
  simp [nMem, find_loc hl hm]

/-! ## Native stores as units -/

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

/-- **A native store is a write unit of a location's cell.** -/
theorem H.nst (h : H P L x U) {i c : Nat} (hi : i < P.threads.length) (hc : c < (L i).length)
    {e : Nat × Nat × Nat} (he : e ∈ nsts (L i)[c]) :
    ∃ hk : e.1 < (labRoles (L i)[c]).length, ∃ sz, (labRoles (L i)[c])[e.1] = .st e.2.1 sz e.2.2 ∧
      (e.2.1, sz) ∈ cellsOf P.locs ∧ e.2.2 < 2 ^ (8 * sz) ∧
      pidx x i (base L i c + e.1) < x.n ∧
      x.evN (pidx x i (base L i c + e.1)) = (Role.st e.2.1 sz e.2.2).ev i (base L i c + e.1) ∧
      wval x (pidx x i (base L i c + e.1)) = e.2.2 := by
  obtain ⟨hk, sz, hr⟩ := nsts_role he
  have hok := h.roleOk hc hk
  rw [hr] at hok
  have hloc : (e.2.1, sz) ∈ cellsOf P.locs ∧ e.2.2 < 2 ^ (8 * sz) := by
    rcases hok with hok | ⟨-, hg⟩
    · exact hok
    · exfalso
      obtain ⟨-, bs, hlok⟩ := h.lab i _ (List.getElem_mem hc)
      generalize hl : (L i)[c] = l at he hlok
      cases l with
      | wr m fl a sz' v =>
        simp only [nsts, List.mem_singleton] at he; subst he
        obtain ⟨l', hl', rfl, -, hp0, hb⟩ := loc_of_cell h.lf hlok.1
        simp only at hg; omega
      | blk nm ins outs rvs =>
        simp only [nsts] at he
        obtain ⟨j, hj, rfl⟩ := (mem_idxd _ _ _).mp he
        have := (hlok.1 outs[j] (List.mem_append_right _ (List.getElem_mem hj))).1
        obtain ⟨l', hl', ha, -, hp0, hb⟩ := loc_of_cell h.lf this
        simp only at hg; omega
      | _ => simp [nsts] at he
  obtain ⟨hu, hev, -⟩ := h.at hi hc hk
  rw [hr] at hev
  refine ⟨hk, sz, hr, hloc.1, hloc.2, hu, hev, ?_⟩
  simp only [wval, hev, Role.ev]
  exact bval_natBytes sz _ hloc.2

theorem mem_labEnts {L : Nat → List Lab} {x : Exec} {T i c : Nat} {q : Nat × Ent}
    (hq : q ∈ labEnts L x T i c) : ∃ hc : c < (L i).length,
      ((L i)[c] = .fence .sfence ∧ q = (base L i c, .bar)) ∨
      ((L i)[c] ≠ .fence .sfence ∧ ∃ e ∈ nsts (L i)[c],
        T ≤ κ x (pidx x i (base L i c + e.1)) ∧ q = (base L i c + e.1, .st e.2.1 e.2.2 false)) := by
  unfold labEnts at hq
  split at hq
  · simp at hq
  · rename_i l hl
    have hc : c < (L i).length := by
      by_contra hn; rw [List.getElem?_eq_none (by omega)] at hl; cases hl
    rw [List.getElem?_eq_getElem hc, Option.some.injEq] at hl
    refine ⟨hc, ?_⟩
    rw [hl]
    split at hq
    · simp only [List.mem_singleton] at hq; exact .inl ⟨by assumption, hq⟩
    · rename_i hne
      simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hq
      obtain ⟨e, ⟨he, hT⟩, rfl⟩ := hq
      exact .inr ⟨hne, e, he, hT, rfl⟩

theorem labEnts_pos {L : Nat → List Lab} {x : Exec} {T i c : Nat} {q : Nat × Ent}
    (hq : q ∈ labEnts L x T i c) : ∃ _ : c < (L i).length, base L i c ≤ q.1 ∧ q.1 < base L i (c + 1) := by
  obtain ⟨hc, h⟩ := mem_labEnts hq
  refine ⟨hc, ?_⟩
  rw [base_succ hc]
  rcases h with ⟨hs, rfl⟩ | ⟨-, e, he, -, rfl⟩
  · simp [hs, labRoles]
  · obtain ⟨hk, -⟩ := nsts_role he
    simp only; omega

theorem labEnts_pairwise (L : Nat → List Lab) (x : Exec) (T i c : Nat) :
    (labEnts L x T i c).Pairwise fun p q => p.1 < q.1 := by
  unfold labEnts
  split
  · simp
  · split
    · simp
    · rw [List.pairwise_map]
      exact ((nsts_pairwise _).sublist List.filter_sublist).imp fun h => by omega

theorem rawP_pairwise (L : Nat → List Lab) (x : Exec) (T : Nat) (cnt : Nat → Nat) (i : Nat) :
    (rawP L x T cnt i).Pairwise fun p q => p.1 < q.1 := by
  unfold rawP
  rw [List.pairwise_flatMap]
  refine ⟨fun c _ => labEnts_pairwise L x T i c, ?_⟩
  refine List.pairwise_lt_range.imp ?_
  intro c c' hcc' q hq q' hq'
  obtain ⟨-, -, h1⟩ := labEnts_pos hq
  obtain ⟨-, h2, -⟩ := labEnts_pos hq'
  have := base_mono (L := L) (i := i) (show c + 1 ≤ c' by omega)
  omega

theorem mem_rawP {L : Nat → List Lab} {x : Exec} {T : Nat} {cnt : Nat → Nat} {i : Nat}
    {q : Nat × Ent} : q ∈ rawP L x T cnt i ↔ ∃ c < cnt i, q ∈ labEnts L x T i c := by
  simp [rawP, List.mem_flatMap]

/-- **A buffered entry of a cell is a native store** of an executed label, not yet flushed. -/
theorem H.rawP_st (_h : H P L x U) {T i a : Nat} {cnt : Nat → Nat} (_hi : i < P.threads.length)
    {q : Nat × Ent} (hq : q ∈ rawP L x T cnt i) (hv : (q.2.val a).isSome) :
    ∃ c < cnt i, ∃ hc : c < (L i).length, ∃ e ∈ nsts (L i)[c],
      q = (base L i c + e.1, .st a e.2.2 false) ∧ e.2.1 = a ∧
      T ≤ κ x (pidx x i (base L i c + e.1)) := by
  obtain ⟨c, hcn, hq⟩ := mem_rawP.mp hq
  obtain ⟨hc, hb | ⟨-, e, he, hT, rfl⟩⟩ := mem_labEnts hq
  · rw [hb.2] at hv; simp [Ent.val] at hv
  · simp only [Ent.val] at hv
    have hea : e.2.1 = a := by by_contra hn; simp [hn] at hv
    exact ⟨c, hcn, hc, e, he, by rw [hea], hea, hT⟩

/-- An executed native store not yet flushed is in the buffer. -/
theorem rawP_mem {L : Nat → List Lab} {x : Exec} {T i c : Nat} {cnt : Nat → Nat}
    (hcn : c < cnt i) (hc : c < (L i).length) {e : Nat × Nat × Nat} (he : e ∈ nsts (L i)[c])
    (hT : T ≤ κ x (pidx x i (base L i c + e.1))) :
    (base L i c + e.1, Ent.st e.2.1 e.2.2 false) ∈ rawP L x T cnt i := by
  refine mem_rawP.mpr ⟨c, hcn, ?_⟩
  unfold labEnts
  rw [List.getElem?_eq_getElem hc]
  simp only
  split
  · rename_i hs; rw [hs] at he; simp [nsts] at he
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨e, ⟨he, hT⟩, rfl⟩

end


/-! ## Own writes before a read -/

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

theorem role_W {r : Role} {i p : Nat} (h : (r.ev i p).isW = true) :
    (∃ a sz v, r = .st a sz v) ∨ ∃ a sz v, r = .lw a sz v := by
  cases r <;> simp_all [Role.ev, Ev.isW]

theorem role_R {r : Role} {i p : Nat} (h : (r.ev i p).isR = true) :
    (∃ a sz v, r = .ld a sz v) ∨ ∃ a sz v, r = .lr a sz v := by
  cases r <;> simp_all [Role.ev, Ev.isR]

/-- A unit, its label and its role, at a given thread. -/
theorem H.labAt (h : H P L x U) {u i : Nat} (hu : u < x.n) (ht : (x.evN u).tid = i) :
    ∃ c, ∃ hc : c < (L i).length, ∃ k, ∃ hk : k < (labRoles (L i)[c]).length,
      (x.evN u).pos = base L i c + k ∧
      x.evN u = ((labRoles (L i)[c])[k]).ev i (base L i c + k) ∧
      ex U u = ((labRoles (L i)[c])[k]).exp := by
  subst ht
  obtain ⟨c, hc, k, hk, hp, he, hx⟩ := h.labOf hu
  exact ⟨c, hc, k, hk, hp, by rw [← hp]; exact he, hx⟩

/-- A write of a location's cell before a read of the same thread is in an earlier label. -/
theorem H.lab_lt_of_write (h : H P L x U) {u v i : Nat} (hu : u < x.n) (hv : v < x.n)
    (htu : (x.evN u).tid = i) (htv : (x.evN v).tid = i) (hp : (x.evN u).pos < (x.evN v).pos)
    (huW : (x.evN u).isW = true) (hua : (x.evN u).addr < ctlAddr 0) (hvR : (x.evN v).isR = true)
    {cu ku cv kv : Nat} (hcu : cu < (L i).length) (hku : ku < (labRoles (L i)[cu]).length)
    (hpu : (x.evN u).pos = base L i cu + ku)
    (hcv : cv < (L i).length) (hkv : kv < (labRoles (L i)[cv]).length)
    (hpv : (x.evN v).pos = base L i cv + kv) : cu < cv := by
  rcases Nat.lt_trichotomy cu cv with hlt | heq | hgt
  · exact hlt
  · exfalso
    subst heq
    have hi : i < P.threads.length := htu ▸ h.tid_lt hu
    obtain ⟨-, he1, -⟩ := h.at hi hcu hku
    obtain ⟨-, he2, -⟩ := h.at hi hcu hkv
    rw [show u = pidx x i (base L i cu + ku) by rw [← hpu, ← htu, h.pidx_eq hu]] at huW hua
    rw [show v = pidx x i (base L i cu + kv) by rw [← hpv, ← htv, h.pidx_eq hv]] at hvR
    rw [he1] at huW hua
    rw [he2] at hvR
    have hjk : ku < kv := by omega
    rcases role_W huW with ⟨a, sz, w', he⟩ | ⟨a, sz, w', he⟩ <;>
    rcases role_R hvR with ⟨b, sz', v', he'⟩ | ⟨b, sz', v', he'⟩ <;>
    rw [he] at hua <;> simp only [Role.ev] at hua
    · exact roles_write_after hjk hkv (.inl he) hua (.inl he')
    · exact roles_write_after hjk hkv (.inl he) hua (.inr he')
    · exact roles_write_after hjk hkv (.inr he) hua (.inl he')
    · exact roles_write_after hjk hkv (.inr he) hua (.inr he')
  · have := lab_lt (L := L) (i := i) hcv hkv hgt (k' := ku); omega

/-- A write unit that is not locked and is below the ghost bytes is a native store. -/
theorem H.native (h : H P L x U) {w i : Nat} (hw : w < x.n) (ht : (x.evN w).tid = i)
    (hW : (x.evN w).isW = true) (hl : isLW (x.evN w) = false) (ha : (x.evN w).addr < ctlAddr 0) :
    ∃ c, ∃ hc : c < (L i).length, ∃ e ∈ nsts (L i)[c],
      (x.evN w).pos = base L i c + e.1 ∧ e.2.1 = (x.evN w).addr ∧
      w = pidx x i (base L i c + e.1) := by
  obtain ⟨c, hc, k, hk, hp, he, -⟩ := h.labAt hw ht
  have hW' := hW
  rw [he] at hW' hl ha
  rcases role_W hW' with ⟨a, sz, v, hr⟩ | ⟨a, sz, v, hr⟩
  · rw [hr] at ha
    have hn := role_nsts hk hr (by simpa [Role.ev] using ha)
    refine ⟨c, hc, (k, a, v), hn, hp, ?_, ?_⟩
    · show a = (x.evN w).addr
      rw [he, hr]; rfl
    · show w = pidx x i (base L i c + k)
      rw [← hp, ← ht, h.pidx_eq hw]
  · rw [hr] at hl; simp [isLW, Role.ev, Ev.isW] at hl

end

/-! ## Reads -/

/-- No write that `r` reads before is visible at `T`. -/
def NI (x : Exec) (r T : Nat) : Prop :=
  ∀ w (hw : w < x.n) (hr : r < x.n), (x.evN w).isW = true → κ x (fstU x w) < T →
    x.frR ⟨r, hr⟩ ⟨w, hw⟩ = true → False

/-- The value the `rf` source of `r` gives it. -/
noncomputable def srcVal (P : Prog) (x : Exec) (r : Nat) : Nat :=
  match x.rf r (x.evN r).addr with
  | some w => wval x w
  | none => ((P.locs.find? fun l => l.addr == (x.evN r).addr).map (·.init)).getD 0

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

/-- At its own tick, nothing a read reads before is visible. -/
theorem H.ni_self (h : H P L x U) {r : Nat} (hr : r < x.n) (hR : (x.evN r).isR = true) :
    NI x r (κ x r) := by
  intro w hw _ hW hvis hfr
  have h1 := h.κ_fr hr hw hfr
  have h2 := h.κ_fst hw
  have h3 := bit_le x w
  have hne : fstU x w ≠ r := by
    intro he
    cases hl : isLW (x.evN w)
    · rw [fst_of hl] at he; subst he; exact RW_false hR hW
    · obtain ⟨r', hr', ht, hp, hlr, -⟩ := h.partnerW hw hl
      rw [h.fst_lw hl hr' ht hp] at he; subst he
      -- `r` is the read half of `w`; it is `fr`-before `w` only if `w` is not its source
      have := h.κ_fst hw
      simp only [bit, hl, ↓reduceIte] at this
      omega
  have := h.κ_inj (h.fst_spec hw).1 hr
  have hne' : κ x (fstU x w) ≠ κ x r := fun he => hne (this he)
  simp only [bit] at h2 h3
  split at h2 <;> omega


theorem H.rfW (h : H P L x U) {r w y : Nat} (hr : r < x.n) (hR : (x.evN r).isR = true)
    (hy : (x.evN r).covers y = true) (hrf : x.rf r y = some w) :
    w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true := by
  have hev : x.ev ⟨r, hr⟩ = x.evN r := (ev_eq _).trans rfl
  obtain ⟨hw, hW, hC⟩ := h.wf.rf ⟨r, hr⟩ (by rw [hev]; exact hR) y
    (by rw [hev, Silmaril.Proofs.X86.Concurrency.Cir.Domain.mem_bytes]; rwa [covers_iff] at hy) w hrf
  have hev' : x.ev ⟨w, hw⟩ = x.evN w := (ev_eq _).trans rfl
  rw [hev'] at hW hC
  exact ⟨hw, hW, hC⟩

/-- **Reads see their `rf` source.** -/
theorem H.readOK (h : H P L x U) {T i c k r : Nat} {cnt : Nat → Nat} (hr : r < x.n)
    (hR : (x.evN r).isR = true) (htid : (x.evN r).tid = i) (hc : c < (L i).length)
    (hk : k < (labRoles (L i)[c]).length) (hpos : (x.evN r).pos = base L i c + k)
    (hcnt : cnt i = c) (hT : κ x r ≤ T) {l : Loc} (hl : l ∈ P.locs)
    (hla : l.addr = (x.evN r).addr) (hls : l.size = (x.evN r).size) (hNI : NI x r T) :
    view (nMem P x T) (nBuf L x T cnt i) (x.evN r).addr = some (srcVal P x r) := by
  have hi : i < P.threads.length := htid ▸ h.tid_lt hr
  have hsz : 0 < (x.evN r).size := by have := h.lf.size l hl; omega
  have hlow : (x.evN r).addr + (x.evN r).size ≤ ctlAddr 0 := by have := h.lf.below l hl; omega
  have hcr : (x.evN r).covers (x.evN r).addr = true := by rw [covers_iff]; omega
  have hrM := isM_R hR
  have hcell : ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers (x.evN r).addr = true →
      (x.evN w).addr = (x.evN r).addr := by
    intro w hw hW hcw
    have := Silmaril.Proofs.X86.Concurrency.Cir.Domain.cell_eq h.cells (a := ⟨w, hw⟩)
      (b := ⟨r, hr⟩) (by rw [ev_eq]; exact isM_W hW) (by rw [ev_eq]; exact hrM)
      (by rw [ev_eq]; exact hcw) (by rw [ev_eq]; exact hcr)
    rw [ev_eq, ev_eq] at this; exact this.1
  have hmem : nMem P x T (x.evN r).addr = some ((cval x T (x.evN r).addr).getD l.init) := by
    rw [← hla]; exact nMem_loc h.lf hl
  -- buffered entries of the cell: own native stores before `r`, not yet flushed
  have hbuf : ∀ q ∈ rawP L x T cnt i, (q.2.val (x.evN r).addr).isSome → ∃ w < x.n,
      (x.evN w).tid = i ∧ (x.evN w).pos = q.1 ∧ (x.evN w).pos < (x.evN r).pos ∧
      (x.evN w).isW = true ∧ isLW (x.evN w) = false ∧ (x.evN w).covers (x.evN r).addr = true ∧
      T ≤ κ x w ∧ q.2 = .st (x.evN r).addr (wval x w) false := by
    intro q hq hv
    obtain ⟨c', hc'n, hc', e, he, rfl, hea, hT'⟩ := h.rawP_st hi hq hv
    obtain ⟨hk', sz, -, hcell', -, hw, hev, hval⟩ := h.nst hi hc' he
    obtain ⟨-, -, -, -, hsz', -⟩ := loc_of_cell h.lf hcell'
    refine ⟨_, hw, by rw [hev]; simp, by rw [hev]; simp, ?_, by rw [hev]; simp [Role.ev, Ev.isW],
      by rw [hev]; simp [Role.ev, isLW], ?_, hT', by rw [hval]⟩
    · rw [hev, hpos]; simp only [Role.ev_pos]; exact lab_lt hc' hk' (by omega)
    · rw [hev]; simp only [Role.ev, covers_iff]; omega
  -- a buffered entry not after `w` in program order is not the newest
  have hsame : ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers (x.evN r).addr = true →
      (x.evN w).tid = i → (x.evN w).pos < (x.evN r).pos → x.rf r (x.evN r).addr = some w →
      ∀ w' < x.n, (x.evN w').tid = i → (x.evN w').pos < (x.evN r).pos → (x.evN w').isW = true →
      (x.evN w').covers (x.evN r).addr = true → (x.evN w).pos < (x.evN w').pos → False := by
    intro w hw hW hcw htw hpw hsrc w' hw' htw' hpw' hW' hcw' hlt
    have hne : w ≠ w' := by rintro rfl; omega
    have hc1 := h.coIn hw hW hcw
    have hc2 := h.coIn hw' hW' hcw'
    rcases before_total hc1 hc2 hne with hb | hb
    · exact h.cyc_fr hr hw' (by rw [htw', htid]) hpw' hW' hR hcr hcw'
        (frR_of hr hw' hR hW' hcr hcw' (by rw [hsrc]; exact hb))
    · exact h.cyc_co hw hw' (by rw [htw, htw']) hlt hW hW' hcw hcw' hb
  simp only [view, srcVal]
  rw [hmem]
  cases hsrc : x.rf r (x.evN r).addr with
  | none =>
    have hnb : newest (nBuf L x T cnt i) (x.evN r).addr = none := by
      rw [nBuf, newest_dropWhile]; apply newest_none; intro e he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      cases hv : q.2.val (x.evN r).addr with
      | none => rfl
      | some _ =>
        exfalso
        obtain ⟨w, hw, htw, -, hpw, hW, -, hcw, -, -⟩ := hbuf q hq (by simp [hv])
        exact h.cyc_fr hr hw (by rw [htw, htid]) hpw hW hR hcr hcw
          (frR_of hr hw hR hW hcr hcw (by rw [hsrc]; trivial))
    have hcv : cval x T (x.evN r).addr = none := cval_none' fun w hw hW hcw => by
      by_contra hlt
      exact hNI w hw hr hW (by omega) (frR_of hr hw hR hW hcr hcw (by rw [hsrc]; trivial))
    rw [hnb, hcv, ← hla, find_loc h.lf hl]; rfl
  | some w =>
    obtain ⟨hw, hW, hcw⟩ := h.rfW hr hR hcr hsrc
    have hwa := hcell w hw hW hcw
    -- the coherence-later writes are not visible
    have hlater : ∀ w'' < x.n, (x.evN w'').isW = true → (x.evN w'').covers (x.evN r).addr = true →
        before (x.co (x.evN r).addr) w w'' = true → T ≤ κ x (fstU x w'') := by
      intro w'' hw'' hW'' hc'' hb
      by_contra hlt
      exact hNI w'' hw'' hr hW'' (by omega) (frR_of hr hw'' hR hW'' hcr hc'' (by rw [hsrc]; exact hb))
    by_cases htw : (x.evN w).tid = i
    · rcases Nat.lt_trichotomy (x.evN w).pos (x.evN r).pos with hlt | heq | hgt
      · cases hlw : isLW (x.evN w)
        · -- a native store of this thread
          obtain ⟨c', hc', e, he, hpw, hea, hwe⟩ :=
            h.native hw htw hW hlw (by rw [hwa]; omega)
          have hcc : c' < c := h.lab_lt_of_write hw hr htw htid hlt hW (by rw [hwa]; omega) hR hc'
            (nsts_role he).1 hpw hc hk hpos
          obtain ⟨-, sz, -, -, -, -, -, hval⟩ := h.nst hi hc' he
          rw [← hwe] at hval
          by_cases hTw : T ≤ κ x w
          · have hnb : newest (nBuf L x T cnt i) (x.evN r).addr = some (wval x w) := by
              rw [nBuf, newest_dropWhile]
              have hm := rawP_mem (T := T) (cnt := cnt) (by omega) hc' he (by rw [← hwe]; exact hTw)
              refine newest_sorted (rawP_pairwise L x T cnt i) hm (wk := false)
                (by simp only; rw [hea, hwa, hval]) ?_
              intro q' hq' hv'
              obtain ⟨w', hw', htw', hpw', hpwr', hW', -, hcw', -, -⟩ := hbuf q' hq' hv'
              by_contra hgt'
              exact hsame w hw hW hcw htw hlt hsrc w' hw' htw' hpwr' hW' hcw' (by omega)
            rw [hnb]; rfl
          · have hnb : newest (nBuf L x T cnt i) (x.evN r).addr = none := by
              rw [nBuf, newest_dropWhile]; apply newest_none; intro e' he'
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he'
              cases hv : q.2.val (x.evN r).addr with
              | none => rfl
              | some _ =>
                exfalso
                obtain ⟨w', hw', htw', -, hpwr', hW', -, hcw', hT', -⟩ := hbuf q hq (by simp [hv])
                rcases Nat.lt_trichotomy (x.evN w').pos (x.evN w).pos with h1 | h1 | h1
                · have := h.κ_ppoW hw' hw (by rw [htw', htw]) h1 hW' hW; omega
                · have := h.uniq hw' hw (by rw [htw', htw]) h1; subst this; omega
                · exact hsame w hw hW hcw htw hlt hsrc w' hw' htw' hpwr' hW' hcw' h1
            have hcv := h.cval_of hw hW hcw (by rw [fst_of hlw]; omega) hlater
            rw [hnb, hcv]; rfl
        · -- the locked write of a read-modify-write of this thread
          obtain ⟨rw', hrw, ht', hp', hlr, -⟩ := h.partnerW hw hlw
          have hrR : (x.evN rw').isR = true := by simp only [isLR, Bool.and_eq_true] at hlr; exact hlr.1
          have hκR : κ x rw' < κ x r :=
            h.κ_ppoR hrw hr (by rw [ht', htw, htid]) (by omega) hrR hrM
          have hfst : fstU x w = rw' := h.fst_lw hlw hrw ht' hp'
          have hnb : newest (nBuf L x T cnt i) (x.evN r).addr = none := by
            rw [nBuf, newest_dropWhile]; apply newest_none; intro e' he'
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he'
            cases hv : q.2.val (x.evN r).addr with
            | none => rfl
            | some _ =>
              exfalso
              obtain ⟨w', hw', htw', -, hpwr', hW', hlw', hcw', hT', -⟩ := hbuf q hq (by simp [hv])
              rcases Nat.lt_trichotomy (x.evN w').pos (x.evN w).pos with h1 | h1 | h1
              · have hne : (x.evN w').pos ≠ (x.evN rw').pos := by
                  intro he
                  have := h.uniq hw' hrw (by rw [htw', ht', htw]) he
                  subst this; exact RW_false hrR hW'
                have hA : (x.evN rw').isA = true := by
                  simp only [isLR, Bool.and_eq_true] at hlr; simp [Ev.isA, Ev.isM, hlr.1, hlr.2]
                have := h.κ_impl hw' hrw (by rw [htw', ht', htw]) (by omega) hW' hrR (.inr hA)
                omega
              · have := h.uniq hw' hw (by rw [htw', htw]) h1; subst this; rw [hlw] at hlw'; cases hlw'
              · exact hsame w hw hW hcw htw hlt hsrc w' hw' htw' hpwr' hW' hcw' h1
          have hcv := h.cval_of hw hW hcw (by rw [hfst]; omega) hlater
          rw [hnb, hcv]; rfl
      · exfalso
        have := h.uniq hw hr (by rw [htw, htid]) heq; subst this; exact RW_false hR hW
      · exact absurd (h.cyc_rf hr hw (by rw [htw, htid]) hgt hW hR hcr hcw hsrc) id
    · -- another thread's write
      have hκw : κ x w < κ x r := h.κ_rfe hw hr hW hR hcr hcw hsrc (by rw [htid]; exact htw)
      have hnb : newest (nBuf L x T cnt i) (x.evN r).addr = none := by
        rw [nBuf, newest_dropWhile]; apply newest_none; intro e' he'
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he'
        cases hv : q.2.val (x.evN r).addr with
        | none => rfl
        | some _ =>
          exfalso
          obtain ⟨w', hw', htw', -, hpwr', hW', -, hcw', hT', -⟩ := hbuf q hq (by simp [hv])
          have hne : w ≠ w' := by rintro rfl; exact htw htw'
          rcases before_total (h.coIn hw hW hcw) (h.coIn hw' hW' hcw') hne with hb | hb
          · exact h.cyc_fr hr hw' (by rw [htw', htid]) hpwr' hW' hR hcr hcw'
              (frR_of hr hw' hR hW' hcr hcw' (by rw [hsrc]; exact hb))
          · have := h.κ_co hw' hw hW' hW hcw' hcw hb; omega
      have h1 := h.κ_fst hw
      have h2 := bit_le x w
      have hcv := h.cval_of hw hW hcw (by omega) hlater
      rw [hnb, hcv]; rfl


/-- **The `rf` value is the label's value.** -/
theorem H.srcVal_eq (h : H P L x U) {r : Nat} (hr : r < x.n) (hR : (x.evN r).isR = true) {v : Nat}
    (hex : ex U r = natBytes v (x.evN r).size) (hv : v < 2 ^ (8 * (x.evN r).size)) {l : Loc}
    (hl : l ∈ P.locs) (hla : l.addr = (x.evN r).addr) (hls : l.size = (x.evN r).size) :
    srcVal P x r = v := by
  have hsz : 0 < (x.evN r).size := by have := h.lf.size l hl; omega
  have hcr : (x.evN r).covers (x.evN r).addr = true := by rw [covers_iff]; omega
  have hev : x.ev ⟨r, hr⟩ = x.evN r := (ev_eq _).trans rfl
  have hrb := h.reads r hr hR
  rw [hex] at hrb
  have huni : ∀ y ∈ (x.evN r).bytes, x.rf r y = x.rf r (x.evN r).addr := by
    intro y hy
    have := Silmaril.Proofs.X86.Concurrency.Cir.Domain.rf_uniform h.wf
      (Silmaril.Proofs.X86.Concurrency.Cir.Domain.noTwo_of_tso h.tso) h.cells (r := ⟨r, hr⟩)
      (by rw [hev]; exact hR) (y₁ := y) (y₂ := (x.evN r).addr) (by rw [hev]; exact hy)
      (by rw [hev, Silmaril.Proofs.X86.Concurrency.Cir.Domain.mem_bytes]; omega)
    exact this
  simp only [srcVal]
  cases hsrc : x.rf r (x.evN r).addr with
  | none =>
    have : (x.evN r).bytes.map (x.readByte P.memTest.initB r) =
        (List.range' l.addr l.size).map fun y => (Silmaril.X86.MemoryModel.Litmus.initByte P.locs y).getD 0 := by
      rw [hla, hls]
      apply List.map_congr_left
      intro y hy
      simp only [Exec.readByte, huni y hy, hsrc]
      rfl
    unfold Exec.readBytes at hrb
    rw [this, Silmaril.Proofs.X86.Concurrency.Cir.Domain.init_bytes h.lf hl, hls] at hrb
    have := natBytes_inj _ _ _ (by rw [← hls]; exact h.lf.init l hl) hv hrb
    rw [← hla, find_loc h.lf hl]; simp [this]
  | some w =>
    obtain ⟨hw, hW, hcw⟩ := h.rfW hr hR hcr hsrc
    have hcell := Silmaril.Proofs.X86.Concurrency.Cir.Domain.cell_eq h.cells (a := ⟨w, hw⟩)
      (b := ⟨r, hr⟩) (by rw [ev_eq]; exact isM_W hW) (by rw [ev_eq]; exact isM_R hR)
      (by rw [ev_eq]; exact hcw) (by rw [ev_eq]; exact hcr)
    rw [ev_eq, ev_eq] at hcell
    have : (x.evN r).bytes.map (x.readByte P.memTest.initB r) = (x.evN w).data := by
      rw [← Silmaril.Proofs.X86.Concurrency.Cir.Domain.bytes_byte_data (h.dataLen hw hW)]
      have hb : (x.evN r).bytes = (x.evN w).bytes := by simp [Ev.bytes, hcell.1, hcell.2]
      rw [hb]
      apply List.map_congr_left
      intro y hy
      simp only [Exec.readByte, huni y (hb ▸ hy), hsrc]
    unfold Exec.readBytes at hrb
    rw [this] at hrb
    simp only [wval, hrb]
    exact bval_natBytes _ _ hv

end

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
