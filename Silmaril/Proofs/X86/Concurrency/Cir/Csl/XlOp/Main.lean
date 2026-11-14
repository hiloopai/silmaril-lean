module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Sched

/-!
# The XL bridge: the theorem

Proof of `Csl.Task.cirXlOpAx`.
Take an axiomatic XL behaviour of a uniform, thread-free, positive-size program whose
CIR-native start is CSL-certified: one run per thread and a consistent candidate `x` over
their units. No access tears, every unit is write-back, so `x` is x86-TSO-consistent
(`Exec.xl_iff_tso_of_tame`). The hypotheses `H` hold of `x`; the runs cut at their labels
(`run_cut`) give `Runs`; the schedule (`H.run_to`, `H.finish`) reaches a drained final
configuration of `OStep .xl` whose registers are the runs' and whose memory, read at each
location, is the candidate's final memory (`H.final_mem`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc XTrace Final leValue initByte accUnits units finalAx
  writtenByte threadUnits)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff cellsOf LocsFacts)

/-! ## Little-endian values -/

theorem leValue_of {mem : Nat → Option Byte} : ∀ {n a : Nat} {bs : List Byte}, bs.length = n →
    (∀ j (hj : j < bs.length), mem (a + j) = some bs[j]) → leValue mem a n = some (bval bs)
  | 0, a, [], _, _ => rfl
  | 0, a, _ :: _, hl, _ => by simp at hl
  | n + 1, a, [], hl, _ => by simp at hl
  | n + 1, a, b :: bs, hl, hj => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have h0 := hj 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have ih := leValue_of (mem := mem) (a := a + 1) hl fun j hj' => by
      have := hj (j + 1) (by simp; omega)
      rw [show a + (j + 1) = a + 1 + j by omega] at this
      simpa using this
    simp [leValue, h0, ih, bval]

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

/-- A memory unit is on a location's cell or a ghost byte. -/
theorem H.cellOf (h : H P L x U) {w : Nat} (hw : w < x.n) (hM : (x.evN w).isM = true) :
    ((x.evN w).addr, (x.evN w).size) ∈ cellsOf P.locs ∨ ctlAddr 0 ≤ (x.evN w).addr := by
  obtain ⟨c, hc, k, hk, -, he, -⟩ := h.labOf hw
  have hok := h.roleOk hc hk
  rw [he] at hM ⊢
  generalize (labRoles (L (x.evN w).tid)[c])[k] = r at hok hM ⊢
  cases r with
  | fn => simp [Role.ev, Ev.isM, Ev.isR, Ev.isW] at hM
  | _ =>
    simp only [RoleOk] at hok
    rcases hok with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact .inl h1
    · exact .inr h2

/-- A write covering a byte of a location writes that location's cell. -/
theorem H.write_loc (h : H P L x U) {w : Nat} (hw : w < x.n) (hW : (x.evN w).isW = true)
    {l : Loc} (hl : l ∈ P.locs) {y : Nat} (hy1 : l.addr ≤ y) (hy2 : y < l.addr + l.size)
    (hc : (x.evN w).covers y = true) : (x.evN w).addr = l.addr ∧ (x.evN w).size = l.size := by
  rw [covers_iff] at hc
  have hb := h.lf.below l hl
  rcases h.cellOf hw (isM_W hW) with hcell | hg
  · obtain ⟨l', hl', ha', hs', hp', -⟩ := loc_of_cell h.lf hcell
    rcases h.lf.disj l hl l' hl' with rfl | h1 | h1
    · exact ⟨ha'.symm, hs'.symm⟩
    · omega
    · omega
  · omega

/-- **The final memory**: at each location, the candidate's final bytes have the value of the
closed form at the end. -/
theorem H.final_mem (h : H P L x U) (trs : List XTrace) {l : Loc} (hl : l ∈ P.locs) :
    leValue (finalAx P.memTest trs x).mem l.addr l.size = nMem P x (tEnd x) l.addr := by
  rw [nMem_loc h.lf hl]
  have hsz := h.lf.size l hl
  have hb := h.lf.below l hl
  show leValue (fun y => if writtenByte x y then some (x.finalByte P.memTest.initB y)
    else P.memTest.initMem y) l.addr l.size = _
  by_cases hex : ∃ w < x.n, (x.evN w).isW = true ∧ (x.evN w).covers l.addr = true
  · obtain ⟨w, hw, hW, hcw⟩ := hex
    have hwM := isM_W hW
    have hne : x.co l.addr ≠ [] := List.ne_nil_of_mem (h.coIn hw hW hcw)
    obtain ⟨wl, hwl⟩ : ∃ wl, (x.co l.addr).getLast? = some wl := by
      cases hg : (x.co l.addr).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hne
      | some wl => exact ⟨wl, rfl⟩
    have hwlm : wl ∈ x.co l.addr := List.mem_of_getLast? hwl
    obtain ⟨hwl', hWl, hcl⟩ := h.coMem hw hwM hcw hwlm
    obtain ⟨hal, hsl⟩ := h.write_loc hwl' hWl hl (le_refl _) (by omega) hcl
    have hcv : cval x (tEnd x) l.addr = some (wval x wl) := by
      simp only [cval]
      rw [List.filter_eq_self.mpr fun w' hw' => by
        obtain ⟨h1, h2, h3⟩ := h.coMem hw hwM hcw hw'
        simp [vis, h1, h2, h3, h.κ_lt (h.fst_spec h1).1], hwl]
      rfl
    rw [hcv]
    simp only [Option.getD_some, wval]
    have hdl : (x.evN wl).data.length = l.size := by rw [h.dataLen hwl' hWl, hsl]
    refine leValue_of (bs := (x.evN wl).data) hdl fun j hj => ?_
    rw [hdl] at hj
    have hcy : (x.evN wl).covers (l.addr + j) = true := by rw [covers_iff, hal, hsl]; omega
    have hwr : writtenByte x (l.addr + j) = true := by
      simp only [writtenByte, List.any_eq_true, Bool.and_eq_true]
      exact ⟨x.evN wl, by rw [h.evs_get hwl']; exact List.getElem_mem _, hWl, hcy⟩
    have hco : x.co (l.addr + j) = x.co l.addr :=
      Silmaril.Proofs.X86.Concurrency.Cir.Domain.co_uniform h.wf
        (Silmaril.Proofs.X86.Concurrency.Cir.Domain.noTwo_of_tso h.tso) h.cells
        (e := ⟨wl, hwl'⟩) (by rw [ev_eq]; exact isM_W hWl)
        (by rw [ev_eq, Silmaril.Proofs.X86.Concurrency.Cir.Domain.mem_bytes, hal, hsl]; omega)
        (by rw [ev_eq, Silmaril.Proofs.X86.Concurrency.Cir.Domain.mem_bytes, hal, hsl]; omega)
    simp only [hwr, ↓reduceIte, Exec.finalByte, hco, hwl, Option.some.injEq]
    simp [Ev.byte, hal, List.getElem?_eq_getElem (show j < (x.evN wl).data.length by omega)]
  · have hcv : cval x (tEnd x) l.addr = none := cval_none' fun w hw hW hc => absurd ⟨w, hw, hW, hc⟩ hex
    rw [hcv]
    simp only [Option.getD_none]
    have hinit := Silmaril.Proofs.X86.Concurrency.Cir.Domain.init_bytes h.lf hl
    rw [← bval_natBytes l.size l.init (h.lf.init l hl)]
    refine leValue_of (by simp [Silmaril.Proofs.X86.Concurrency.Cir.Domain.length_natBytes])
      fun j hj => ?_
    rw [Silmaril.Proofs.X86.Concurrency.Cir.Domain.length_natBytes] at hj
    have hwr : writtenByte x (l.addr + j) = false := by
      simp only [writtenByte, List.any_eq_false, Bool.and_eq_true, not_and]
      intro e he hW hc
      obtain ⟨w, hw, rfl⟩ := List.getElem_of_mem he
      have hw' : w < x.n := hw
      have he' : x.evs[w] = x.evN w := (h.evs_get hw').symm
      rw [he'] at hW hc
      obtain ⟨ha, hs⟩ := h.write_loc hw' hW hl (by omega) (by omega) hc
      exact hex ⟨w, hw', hW, by rw [covers_iff, ha, hs]; omega⟩
    have hj' := congrArg (fun l => l[j]?) hinit
    simp only [List.getElem?_map, List.getElem?_range', hj, Option.map_some] at hj'
    simp only [hwr, Bool.false_eq_true, ↓reduceIte, Silmaril.X86.MemoryModel.Litmus.Test.initMem]
    have hsome : (initByte P.locs (l.addr + j)).isSome := by
      simp only [initByte, Option.isSome_map]
      cases hf : P.locs.find? (fun l' => decide (l'.addr ≤ l.addr + j) &&
          decide (l.addr + j < l'.addr + l'.size)) with
      | none =>
        rw [List.find?_eq_none] at hf
        exact absurd (hf l hl) (by simp; omega)
      | some _ => rfl
    show initByte P.locs (l.addr + j) = _
    rw [← Option.some_get hsome]
    congr 1
    rw [List.getElem?_eq_getElem (by simp [Silmaril.Proofs.X86.Concurrency.Cir.Domain.length_natBytes]; omega)] at hj'
    simp only [Option.some.injEq] at hj'
    rw [← hj', Nat.one_mul]
    exact Option.get_eq_getD _

end


/-! ## Uniform units -/

theorem roleOk_uok {cs : List (Nat × Nat)} {r : Role} (h : RoleOk cs r) (i p : Nat) :
    Silmaril.Proofs.X86.Concurrency.Cir.Domain.UOk cs (r.ev i p) := by
  intro hM
  cases r with
  | fn => simp [Role.ev, Ev.isM, Ev.isR, Ev.isW] at hM
  | _ =>
    simp only [RoleOk] at h
    refine ⟨rfl, rfl, ?_⟩
    rcases h with ⟨h1, -⟩ | h2
    · exact .inl h1
    · exact .inr h2

theorem tearable_false {locs : List Loc} (hl : LocsFacts locs) {x : Exec}
    (hu : ∀ b : Fin x.n, Silmaril.Proofs.X86.Concurrency.Cir.Domain.UOk (cellsOf locs) (x.ev b))
    (a : Fin x.n) : x.tearable a = false := by
  simp only [Exec.tearable, Bool.and_eq_false_iff]
  by_cases hM : (x.ev a).isM = true
  · right
    obtain ⟨hsc, -⟩ := Silmaril.Proofs.X86.Concurrency.Cir.Domain.uok_single hl (hu a) hM
    simp only [hsc, Bool.not_true, Bool.false_or, List.any_eq_false, Bool.and_eq_true,
      bne_iff_ne, ne_eq, not_and, Bool.or_eq_true]
    intro b _ ⟨hbM, hov⟩ hne
    obtain ⟨ha, hs, -⟩ := hu a hM
    obtain ⟨ha', hs', -⟩ := hu b hbM
    simp only [Ev.accOverlap, ha, hs, ha', hs', Bool.and_eq_true, decide_eq_true_eq] at hov hne
    rcases Silmaril.Proofs.X86.Concurrency.Cir.Domain.uok_cell hl (hu a) (hu b) hM hbM with
      ⟨e1, e2⟩ | h' | h'
    · rcases hne with hne | hne
      · exact hne e1
      · exact hne e2
    · omega
    · omega
  · left; simpa using hM

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc XTrace Final leValue initByte accUnits units finalAx
  writtenByte threadUnits finalOf)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff cellsOf LocsFacts)

/-- **`Csl.Task.cirXlOpAx` holds.** -/
theorem cirXlOpAx : Task.cirXlOpAx := by
  intro P hU hthr hcsl f hf
  obtain ⟨I, Q, hs, hI, G⟩ := hcsl
  obtain ⟨D, trs, hT, x, hevs, hrmw, hwf, hreads, hM, rfl⟩ := hf
  simp only [Prog.uniformB, Bool.and_eq_true, List.all_eq_true] at hU
  obtain ⟨hlocs, hcells⟩ := hU
  have hl := Silmaril.Proofs.X86.Concurrency.Cir.Domain.locsFacts hlocs
  have hcs := Silmaril.Proofs.X86.Concurrency.Cir.Domain.cellsOf_lt hl
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hthr
  have hlen : trs.length = P.threads.length := by simpa [Prog.traces] using hT.length_eq
  have hdata := Silmaril.Proofs.X86.Concurrency.Cir.Domain.thread_of hT
  -- one run per thread
  have hch : ∀ i, ∃ p : List Lab × Regs, (∀ hi : i < P.threads.length,
      p ∈ run D P.threads[i].body Regs.zero ∧ trs[i]'(by omega) = P.threads[i].xtrace i p) ∧
      (P.threads.length ≤ i → p = ([], Regs.zero)) := by
    intro i
    by_cases hi : i < P.threads.length
    · obtain ⟨_, p, hp, he⟩ := hdata i (by omega)
      exact ⟨p, fun _ => ⟨hp, he⟩, fun h' => absurd h' (by omega)⟩
    · exact ⟨([], Regs.zero), fun h' => absurd h' hi, fun _ => rfl⟩
  choose p hp using hch
  -- the runs, cut
  have hcut : ∀ i, ∃ SP : (Nat → Stmt × Regs) × (Nat → Stmt × Regs),
      (∀ hi : i < P.threads.length,
        Cut P.threads[i].body Regs.zero (p i).1 (.skip, (p i).2) SP.1 SP.2) ∧
      (P.threads.length ≤ i → ∀ c, SP.1 c = (.skip, Regs.zero)) := by
    intro i
    by_cases hi : i < P.threads.length
    · obtain ⟨S', Pre', hc'⟩ := run_cut D ((hp i).1 hi).1
      exact ⟨(S', Pre'), fun _ => hc', fun h' => absurd h' (by omega)⟩
    · exact ⟨(fun _ => (.skip, Regs.zero), fun _ => (.skip, Regs.zero)), fun h' => absurd h' hi,
        fun _ _ => rfl⟩
  choose SP hSP using hcut
  have hr : Runs P (fun i => (p i).1) (fun i => (p i).2) (fun i => (SP i).1) (fun i => (SP i).2) :=
    ⟨fun i hi => (hSP i).1 hi, fun i hi c => (hSP i).2 hi c⟩
  -- the labels
  have hlab : ∀ i (hi : i < P.threads.length), ∀ l ∈ (p i).1, LabG l ∧
      Silmaril.Proofs.X86.Concurrency.Cir.Domain.LabOk (cellsOf P.locs) P.threads[i].body.blocks l := by
    intro i hi l hlm
    have hrun := ((hp i).1 hi).1
    have hth := hthr _ (List.getElem_mem hi)
    exact ⟨labs_shape D _ _ (hcells _ (List.getElem_mem hi)) hth.1.1 _ _ hrun l hlm,
      Silmaril.Proofs.X86.Concurrency.Cir.Domain.labs_ok D _ hcs _ (hcells _ (List.getElem_mem hi))
        _ _ hrun l hlm⟩
  -- the units
  have hacts : ∀ i (hi : i < trs.length), (trs[i]).acts = (p i).1.flatMap Lab.acts := by
    intro i hi
    rw [((hp i).1 (by omega)).2, Silmaril.Proofs.X86.Concurrency.Cir.Domain.xtrace_acts]
    simp [Thread.acts, (hthr _ (List.getElem_mem (show i < P.threads.length by omega))).2]
  have hueq : accUnits trs = ((List.range P.threads.length).map fun i =>
      rolesUnits i 0 (RL (fun i => (p i).1) i)).flatten := by
    unfold accUnits
    congr 1
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.length_mapIdx] at h1
      simp only [List.getElem_mapIdx, List.getElem_map, List.getElem_range]
      rw [hacts i h1]
      exact tu_labs i 0 _ fun l hl' => (hlab i (by omega) l hl').1
  have huok : ∀ u ∈ accUnits trs, Silmaril.Proofs.X86.Concurrency.Cir.Domain.UOk (cellsOf P.locs) u.1 := by
    intro u hu
    rw [hueq] at hu
    simp only [List.mem_flatten, List.mem_map, List.mem_range] at hu
    obtain ⟨_, ⟨i, hi, rfl⟩, hu⟩ := hu
    obtain ⟨k, hk, rfl⟩ := mem_rolesUnits hu
    obtain ⟨c, hc, k', hk', rfl⟩ := pos_lab hk
    obtain ⟨_, hget⟩ := RL_get (L := fun i => (p i).1) hc hk'
    simp only [hget]
    obtain ⟨-, hok⟩ := hlab i hi _ (List.getElem_mem hc)
    exact roleOk_uok (labRoles_ok hok _ (List.getElem_mem hk')) _ _
  have hun : units trs = accUnits trs := Silmaril.Proofs.X86.Concurrency.Cir.Domain.units_eq hl huok
  rw [hun] at hevs hrmw hreads
  have hevU : ∀ b : Fin x.n, Silmaril.Proofs.X86.Concurrency.Cir.Domain.UOk (cellsOf P.locs) (x.ev b) := by
    intro b
    have hb : b.val < (accUnits trs).length := by have := b.isLt; simp [Exec.n, hevs] at this; exact this
    have : x.ev b = (accUnits trs)[b.val].1 := by
      show x.evs[b.val] = _
      simp only [hevs, List.getElem_map]
    rw [this]; exact huok _ (List.getElem_mem hb)
  have htame : x.Tame := by
    intro a
    refine ⟨?_, tearable_false hl hevU a⟩
    have ha : a.val < (accUnits trs).length := by have := a.isLt; simp [Exec.n, hevs] at this; exact this
    have hmU : ∀ u ∈ accUnits trs, ∃ i < P.threads.length,
        u ∈ rolesUnits i 0 (RL (fun i => (p i).1) i) := by
      intro u hu
      rw [hueq] at hu
      simp only [List.mem_flatten, List.mem_map, List.mem_range] at hu
      obtain ⟨_, ⟨i, hi, rfl⟩, hu⟩ := hu
      exact ⟨i, hi, hu⟩
    obtain ⟨i, hi, hm⟩ := hmU _ (List.getElem_mem ha)
    obtain ⟨k, hk, he⟩ := mem_rolesUnits hm
    have : x.ev a = (accUnits trs)[a.val].1 := by
      show x.evs[a.val] = _
      simp only [hevs, List.getElem_map]
    rw [this, he]
    generalize (RL (fun i => (p i).1) i)[k] = r
    cases r <;> rfl
  have htso : x.Tso := (x.xl_iff_tso_of_tame htame).mp hM
  have h : H P (fun i => (p i).1) x (accUnits trs) :=
    { lf := hl
      lout := fun i hi => by simp [(hp i).2 hi]
      lab := fun i l hlm => by
        by_cases hi : i < P.threads.length
        · exact ⟨(hlab i hi l hlm).1, _, (hlab i hi l hlm).2⟩
        · simp [(hp i).2 (by omega)] at hlm
      ueq := hueq
      evs := hevs
      rmw := hrmw
      wf := Silmaril.Proofs.X86.Concurrency.Cir.Domain.wfFacts hwf
      cells := by
        rw [hevs]
        exact Silmaril.Proofs.X86.Concurrency.Cir.Domain.cellsOk_of hl fun e he => by
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he; exact huok u hu
      tso := htso
      reads := fun r hr hR => hreads r hr hR }
  obtain ⟨cnt, hIv, hRe⟩ := h.run_to hr G (tEnd x) (tEnd x) le_rfl
  obtain ⟨C, hreach, hdr, hts, hmem⟩ := h.finish hr hIv hRe
  refine ⟨C, hreach, hdr, fun t ht => ⟨by rw [hts t ht], ?_⟩, fun l hlm => by
    rw [hmem]; exact h.final_mem trs hlm⟩
  rw [hts t ht]
  funext r
  simp only [finalAx, finalOf]
  rw [List.getElem?_eq_getElem (by omega), ((hp t).1 ht).2]
  simp [Thread.xtrace, coreOf, Silmaril.X86.State.read]

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
