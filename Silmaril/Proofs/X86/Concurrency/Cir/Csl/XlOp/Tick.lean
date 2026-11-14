module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Step

/-!
# The XL bridge: label kinds, catching up to a unit, and time advancing

Proofs for `Csl.Task.cirXlOpAx`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff cellsOf LocsFacts)

/-! ## Kinds of units within a label -/

/-- The trigger of a label is a read. -/
theorem trig_read {l : Lab} {k : Nat} (ht : trig l = some k) :
    ∃ hk : k < (labRoles l).length, (∃ a sz v, (labRoles l)[k] = .ld a sz v) ∨
      (∃ a sz v, (labRoles l)[k] = .lr a sz v) := by
  cases l with
  | rd => simp only [trig, Option.some.injEq] at ht; subst ht; exact ⟨by simp [labRoles], .inl ⟨_, _, _, rfl⟩⟩
  | rmw => simp only [trig, Option.some.injEq] at ht; subst ht; exact ⟨by simp [labRoles], .inr ⟨_, _, _, rfl⟩⟩
  | fwait a e s r =>
    simp only [trig] at ht
    by_cases hs : s = e
    · simp only [hs, ↓reduceIte, Option.some.injEq] at ht; subst ht
      exact ⟨by simp [labRoles, hs], .inl ⟨a, 4, s, by simp [labRoles, hs]⟩⟩
    · simp only [hs, ↓reduceIte, Option.some.injEq] at ht; subst ht
      exact ⟨by simp [labRoles, hs], .inl ⟨a, 4, s, by simp [labRoles, hs]⟩⟩
  | fwake => simp only [trig, Option.some.injEq] at ht; subst ht; exact ⟨by simp [labRoles], .inr ⟨_, _, _, rfl⟩⟩
  | blk nm ins outs rvs =>
    simp only [trig] at ht
    split at ht
    · cases ht
    · rename_i hn
      simp only [Option.some.injEq] at ht; subst ht
      have hlen : ins.length - 1 < ins.length := by
        cases ins with
        | nil => exact absurd rfl hn
        | cons => simp
      refine ⟨by simp [labRoles]; omega, .inl ⟨ins[ins.length - 1].1, ins[ins.length - 1].2.1,
        ins[ins.length - 1].2.2, ?_⟩⟩
      simp only [labRoles]
      rw [List.getElem_append_left (by simpa using hlen)]
      simp
  | _ => simp [trig] at ht

theorem nsts_not_trig {l : Lab} {k : Nat} (ht : trig l = some k) {e : Nat × Nat × Nat}
    (he : e ∈ nsts l) : e.1 ≠ k := by
  rintro rfl
  obtain ⟨hk, hr⟩ := trig_read ht
  obtain ⟨_, sz, hs⟩ := nsts_role he
  rcases hr with ⟨a, sz', v, h⟩ | ⟨a, sz', v, h⟩ <;> rw [h] at hs <;> cases hs

theorem lr_ghost {l : Lab} {k a sz v : Nat} (hk : k < (labRoles l).length)
    (h : (labRoles l)[k] = .lr a sz v) (ht : trig l ≠ some k) : ctlAddr 0 ≤ a := by
  have hq := Silmaril.Proofs.X86.Concurrency.Cir.Domain.ghost_q
  cases l with
  | rmw =>
    simp only [labRoles, List.length_cons, List.length_nil] at hk h
    rcases k with _ | _ | k
    · simp [trig] at ht
    · simp at h
    · omega
  | fwake =>
    simp only [labRoles, List.length_cons, List.length_nil] at hk h
    rcases k with _ | _ | _ | _ | k
    · simp at h
    · simp [trig] at ht
    · simp at h
    · simp at h
    · omega
  | fwait a' e s r =>
    simp only [labRoles] at hk h
    split at hk <;> rename_i hs <;> simp only [hs, ↓reduceIte, List.length_cons,
      List.length_nil] at hk h
    · rcases k with _ | _ | _ | _ | _ | _ | k <;> simp at h
      · obtain ⟨rfl, -, -⟩ := h; exact hq _
      · omega
    · rcases k with _ | _ | _ | k <;> simp at h; omega
  | blk nm ins outs rvs =>
    rcases blk_roles (List.getElem_mem hk) with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [h] at he <;>
      cases he
  | rd => simp only [labRoles, List.length_singleton] at hk; obtain rfl : k = 0 := by omega
          simp [labRoles] at h
  | wr => simp only [labRoles, List.length_singleton] at hk; obtain rfl : k = 0 := by omega
          simp [labRoles] at h
  | fence => simp only [labRoles, List.length_singleton] at hk; obtain rfl : k = 0 := by omega
             simp [labRoles] at h
  | _ => simp [labRoles] at hk

/-- A locked read of a location's cell is the read of a read-modify-write label. -/
theorem lr_rmw {l : Lab} {k a sz v : Nat} (hk : k < (labRoles l).length)
    (h : (labRoles l)[k] = .lr a sz v) (ha : a < ctlAddr 0) :
    ∃ m n, l = .rmw m a sz v n ∧ k = 0 := by
  by_cases ht : trig l = some k
  · cases l with
    | rmw m a' sz' o n =>
      simp only [trig, Option.some.injEq] at ht; subst ht
      simp only [labRoles, List.getElem_cons_zero, Role.lr.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨m, n, rfl, rfl⟩
    | fwake a' n q =>
      simp only [trig, Option.some.injEq] at ht; subst ht
      simp only [labRoles] at h
      have := Silmaril.Proofs.X86.Concurrency.Cir.Domain.ghost_q a'
      simp at h; omega
    | rd => simp only [trig, Option.some.injEq] at ht; subst ht; simp [labRoles] at h
    | fwait a' e s r =>
      simp only [trig] at ht
      by_cases hs : s = e
      · simp only [hs, ↓reduceIte, Option.some.injEq] at ht; subst ht; simp [labRoles, hs] at h
      · simp only [hs, ↓reduceIte, Option.some.injEq] at ht; subst ht; simp [labRoles, hs] at h
    | blk nm ins outs rvs =>
      exfalso
      rcases blk_roles (List.getElem_mem hk) with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [h] at he <;>
        cases he
    | _ => simp [trig] at ht
  · have := lr_ghost hk h ht; omega

/-! ## Locations -/

theorem loc_cover {locs : List Loc} (hl : LocsFacts locs) {a sz : Nat} (h : (a, sz) ∈ cellsOf locs)
    {l : Loc} (hm : l ∈ locs) (h1 : a ≤ l.addr) (h2 : l.addr < a + sz) : l.addr = a := by
  obtain ⟨l', hl', rfl, rfl, -, -⟩ := loc_of_cell hl h
  have := hl.size l hm
  rcases hl.disj l hm l' hl' with rfl | h | h
  · rfl
  · omega
  · omega


section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)} {R : Nat → Regs}
  {S Pre : Nat → Nat → Stmt × Regs}

/-- The unit of a trigger is a read. -/
theorem H.trig_unit (h : H P L x U) {i c k : Nat} (hi : i < P.threads.length)
    (hc : c < (L i).length) (ht : trig (L i)[c] = some k) :
    ∃ _ : k < (labRoles (L i)[c]).length, pidx x i (base L i c + k) < x.n ∧
      (x.evN (pidx x i (base L i c + k))).isR = true ∧
      (x.evN (pidx x i (base L i c + k))).tid = i ∧
      (x.evN (pidx x i (base L i c + k))).pos = base L i c + k := by
  obtain ⟨hk, hr⟩ := trig_read ht
  obtain ⟨hu, he, -⟩ := h.at hi hc hk
  refine ⟨hk, hu, ?_, by rw [he]; simp, by rw [he]; simp⟩
  rw [he]; rcases hr with ⟨a, sz, v, hr⟩ | ⟨a, sz, v, hr⟩ <;> rw [hr] <;> simp [Role.ev, Ev.isR]

/-- A native store as a unit: a write, not locked, at its position. -/
theorem H.nst_unit (h : H P L x U) {i c : Nat} (hi : i < P.threads.length)
    (hc : c < (L i).length) {e : Nat × Nat × Nat} (he : e ∈ nsts (L i)[c]) :
    pidx x i (base L i c + e.1) < x.n ∧ (x.evN (pidx x i (base L i c + e.1))).isW = true ∧
      isLW (x.evN (pidx x i (base L i c + e.1))) = false ∧
      (x.evN (pidx x i (base L i c + e.1))).tid = i ∧
      (x.evN (pidx x i (base L i c + e.1))).pos = base L i c + e.1 ∧
      (x.evN (pidx x i (base L i c + e.1))).addr = e.2.1 := by
  obtain ⟨hk, sz, -, -, -, hu, hev, -⟩ := h.nst hi hc he
  rw [hev]; exact ⟨hu, by simp [Role.ev, Ev.isW], by simp [Role.ev, isLW], by simp, by simp,
    by simp [Role.ev]⟩

/-- **Catching a thread up to a unit** of one of its labels whose clock is not after `T`. -/
theorem Runs.catchupTo (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat}
    {i c k : Nat} (hI : Inv L x T cnt) (hR : Reach P L x S T cnt) (hi : i < P.threads.length)
    (hc : c < (L i).length) (hk : k < (labRoles (L i)[c]).length)
    (hvM : (x.evN (pidx x i (base L i c + k))).isM = true)
    (hκ : κ x (pidx x i (base L i c + k)) ≤ T) (hcn : cnt i ≤ c) :
    Inv L x T (upd cnt i c) ∧ Reach P L x S T (upd cnt i c) := by
  obtain ⟨hv, hev, -⟩ := h.at hi hc hk
  have hvt : (x.evN (pidx x i (base L i c + k))).tid = i := by rw [hev]; simp
  have hvp : (x.evN (pidx x i (base L i c + k))).pos = base L i c + k := by rw [hev]; simp
  have := hr.catchup h hi (c - cnt i) (cnt := cnt) (by omega) hI ?_ ?_ ?_ hR
  · rwa [show cnt i + (c - cnt i) = c by omega] at this
  · intro c' hc' h1 h2
    cases ht : trig (L i)[c'] with
    | none => rfl
    | some k' =>
      exfalso
      obtain ⟨hk', hu, hR', htu, hpu⟩ := h.trig_unit hi hc' ht
      have := h.κ_ppoR hu hv (by rw [htu, hvt]) (by rw [hpu, hvp]; exact lab_lt hc' hk' (by omega))
        hR' hvM
      have := hI.trigDone i c' hc' k' ht (by omega)
      omega
  · intro c' hc' h1 h2 e he
    by_contra hlt
    have := hI.stDone i c' hc' e he (by omega)
    omega
  · intro c' hc' h1 h2 hmf c'' hc'' hlt e he
    obtain ⟨hw, hwW, -, hwt, hwp, -⟩ := h.nst_unit hi hc'' he
    have hk0 : 0 < (labRoles (L i)[c']).length := by rw [hmf]; simp [labRoles]
    obtain ⟨hf, hfe, -⟩ := h.at hi hc' hk0
    have hff : (x.evN (pidx x i (base L i c' + 0))).isFence .mfence = true := by
      rw [hfe]; simp [hmf, labRoles, Role.ev, Ev.isFence]
    have hk'' := (nsts_role he).1
    have := h.κ_mf hw hv hf hff (by rw [hwt, hfe]; simp) (by rw [hwp, hfe]; simpa using lab_lt (k' := 0) hc'' hk'' hlt)
      (by rw [hfe, hvt]; simp) (by rw [hfe, hvp]; simp; exact lab_lt hc' hk0 (by omega))
    omega

/-! ## Time advancing -/

theorem H.nMem_succ (h : H P L x U) {T : Nat}
    (hn : ∀ l ∈ P.locs, ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers l.addr = true →
      κ x (fstU x w) ≠ T) : nMem P x (T + 1) = nMem P x T := by
  funext a
  unfold nMem
  cases hf : P.locs.find? (fun l => l.addr == a) with
  | none => rfl
  | some l =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    subst hp
    simp only [Option.map_some, h.cval_same (hn l hm)]

theorem labEnts_succ {T j c : Nat}
    (hn : ∀ hc : c < (L j).length, ∀ e ∈ nsts (L j)[c], κ x (pidx x j (base L j c + e.1)) ≠ T) :
    labEnts L x (T + 1) j c = labEnts L x T j c := by
  by_cases hc : c < (L j).length
  · rw [labEnts_get hc, labEnts_get hc]
    split
    · rfl
    · congr 1
      apply List.filter_congr
      intro e he
      have := hn hc e he
      simp only [decide_eq_decide]; omega
  · simp [labEnts, List.getElem?_eq_none (show (L j).length ≤ c by omega)]

theorem nBuf_succT {T : Nat} {cnt : Nat → Nat} {j : Nat}
    (hn : ∀ c (hc : c < (L j).length), ∀ e ∈ nsts (L j)[c], κ x (pidx x j (base L j c + e.1)) ≠ T) :
    nBuf L x (T + 1) cnt j = nBuf L x T cnt j := by
  simp only [nBuf, rawP]
  congr 2
  apply List.flatMap_congr
  intro c _
  exact labEnts_succ fun hc => hn c hc

end

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
