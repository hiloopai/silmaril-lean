module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Tick
public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Drf

/-!
# The XL bridge: no thread tears a CSL-certified `local` block

Proofs for `Csl.Task.cirXlOpAx`. A `local` block runs as one step at the tick of
its last load. Its earlier loads must still see their `rf` value then: no write of another
thread to a cell the block reads may become visible in between (`Runs.interfere`). Suppose one
did, at tick `τ`. Run the schedule to `τ` (the configurations before `T` are reachable), catch
the block's thread up to the block and the writing thread up to the write: then the block's
thread is about to run the block, so by its CSL safety it owns the cell (`safe_touch`), while
the writer has the cell in its store buffer (owned, by `XInv`) or is about to write it with a
locked instruction (owned or in the invariant's heap). Both contradict the disjointness of
ownership.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff cellsOf LocsFacts)

theorem trig_lt_nsts {l : Lab} {k : Nat} (ht : trig l = some k) {e : Nat × Nat × Nat}
    (he : e ∈ nsts l) : k < e.1 := by
  cases l with
  | blk nm ins outs rvs =>
    simp only [trig] at ht
    split at ht
    · cases ht
    · rename_i hn
      have := List.length_pos_of_ne_nil hn
      simp only [Option.some.injEq] at ht; subst ht
      simp only [nsts] at he
      obtain ⟨j, -, rfl⟩ := (mem_idxd _ _ _).mp he
      simp only; omega
  | wr => simp [trig] at ht
  | _ => simp [nsts] at he

theorem newest_isSome {a : Nat} : ∀ {l : List Ent} {e : Ent}, e ∈ l → (e.val a).isSome →
    (newest l a).isSome
  | e' :: l, e, he, hv => by
    simp only [newest, Option.isSome_or]
    rcases List.mem_cons.mp he with rfl | he
    · simp [hv]
    · simp [newest_isSome he hv]

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)} {R : Nat → Regs}
  {S Pre : Nat → Nat → Stmt × Regs}

/-- **The CSL contradiction**: in a reachable configuration where thread `i` is about to run a
non-atomic label touching cell `a`, no other thread has `a` buffered. -/
theorem Runs.own_buf (hr : Runs P L R S Pre) {I : HProp} {Q : Nat → Regs → HProp}
    {hs : Nat → Heap} {hI : Heap} (G : GInv I Q P.threads.length (progInit P) hs hI)
    {T : Nat} {cnt : Nat → Nat} (hR : Reach P L x S T cnt) {i t : Nat} (hi : i < P.threads.length)
    (hc : cnt i < (L i).length) (hna : (L i)[cnt i].na = true) {a : Nat}
    (ht : (L i)[cnt i].Touches a) (hti : t ≠ i)
    (hb : (newest (nBuf L x T cnt t) a).isSome) : False := by
  obtain ⟨hs', hI', hX⟩ := (Silmaril.Proofs.X86.Concurrency.Cir.Csl.drf_reach G hR).2
  obtain ⟨⟨hd, -, -, -, -, hsafe⟩, hbuf⟩ := hX
  have hsi := hsafe i hi
  have hcut := hr.cut i hi
  have h1 := safe_taus (hcut.taus (cnt i) hc) hsi
  have h2 := (safe_touch h1 (hcut.step (cnt i) hc)).1 hna a ht
  obtain ⟨-, h3⟩ := hbuf t a hb
  rcases hd i t (Ne.symm hti) a with h4 | h4
  · rw [h4] at h2; cases h2
  · rw [h4] at h3; cases h3

/-- **The CSL contradiction, locked**: thread `t` about to run an atomic label touching `a`
while thread `i` is about to run a non-atomic one touching it. -/
theorem Runs.own_lock (hr : Runs P L R S Pre) {I : HProp} {Q : Nat → Regs → HProp}
    {hs : Nat → Heap} {hI : Heap} (G : GInv I Q P.threads.length (progInit P) hs hI)
    {T : Nat} {cnt : Nat → Nat} (hR : Reach P L x S T cnt) {i t : Nat} (hi : i < P.threads.length)
    (ht' : t < P.threads.length)
    (hc : cnt i < (L i).length) (hna : (L i)[cnt i].na = true) {a : Nat}
    (ht : (L i)[cnt i].Touches a) (hti : t ≠ i)
    (hc' : cnt t < (L t).length) (hna' : (L t)[cnt t].na = false) (ht2 : (L t)[cnt t].Touches a) :
    False := by
  obtain ⟨hs', hI', hX⟩ := (Silmaril.Proofs.X86.Concurrency.Cir.Csl.drf_reach G hR).2
  obtain ⟨⟨hd, hdI, -, -, hIv, hsafe⟩, -⟩ := hX
  have hcut := hr.cut i hi
  have h2 := (safe_touch (safe_taus (hcut.taus (cnt i) hc) (hsafe i hi)) (hcut.step (cnt i) hc)).1
    hna a ht
  have hcut' := hr.cut t ht'
  have h3 := (safe_touch (safe_taus (hcut'.taus (cnt t) hc') (hsafe t ht'))
    (hcut'.step (cnt t) hc')).2 hna' hI' hIv (hdI t) a ht2
  simp only [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion] at h3
  split at h3
  · rename_i v hv
    rcases hd i t (Ne.symm hti) a with h4 | h4
    · rw [h4] at h2; cases h2
    · rw [h4] at hv; cases hv
  · rcases hdI i a with h4 | h4
    · rw [h4] at h2; cases h2
    · rw [h4] at h3; cases h3


theorem Runs.lazyStepAt (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat}
    {i c : Nat} (hi : i < P.threads.length) (hcn : cnt i = c) (hc : c < (L i).length)
    (hlazy : trig (L i)[c] = none)
    (hst : ∀ e ∈ nsts (L i)[c], T ≤ κ x (pidx x i (base L i c + e.1)))
    (hmf : (L i)[c] = .fence .mfence → ∀ c' (hc' : c' < (L i).length), c' < c →
      ∀ e ∈ nsts (L i)[c'], κ x (pidx x i (base L i c' + e.1)) < T) :
    OReach .xl P.threads.length (cfg P L x S T cnt) (cfg P L x S T (upd cnt i (c + 1))) := by
  subst hcn; exact hr.lazyStep h hi hc hlazy hst hmf

theorem tid_fst (h : H P L x U) {w : Nat} (hw : w < x.n) :
    (x.evN (fstU x w)).tid = (x.evN w).tid := by
  cases hl : isLW (x.evN w)
  · rw [fst_of hl]
  · obtain ⟨r, hr, ht, hp, -⟩ := h.partnerW hw hl
    rw [h.fst_lw hl hr ht hp, ht]

/-- **No interference with a block** (see the module doc). -/
theorem Runs.interfere (h : H P L x U) (hr : Runs P L R S Pre) {I : HProp}
    {Q : Nat → Regs → HProp} {hs : Nat → Heap} {hI : Heap}
    (G : GInv I Q P.threads.length (progInit P) hs hI)
    {T i c : Nat} (hi : i < P.threads.length) (hc : c < (L i).length) {nm : String}
    {ins outs : List (Nat × Nat × Nat)} {rvs : List Nat}
    (hl : (L i)[c] = .blk nm ins outs rvs) (hins : 0 < ins.length)
    (hT : κ x (pidx x i (base L i c + (ins.length - 1))) = T)
    (hist : ∀ τ < T, ∃ cnt, Inv L x τ cnt ∧ Reach P L x S τ cnt)
    {j : Nat} (hj : j < ins.length) : NI x (pidx x i (base L i c + j)) T := by
  intro w hw hr' hW hvis hfr
  have hlen : (labRoles (L i)[c]).length = ins.length + outs.length := by
    rw [hl]; simp [labRoles]
  have hrole : ∀ j' (hj' : j' < ins.length), (labRoles (L i)[c])[j']'(by omega) =
      .ld ins[j'].1 ins[j'].2.1 ins[j'].2.2 := by
    intro j' hj'
    simp only [hl, labRoles]
    rw [List.getElem_append_left (by simpa using hj')]
    simp
  have hunit : ∀ j' (hj' : j' < ins.length), pidx x i (base L i c + j') < x.n ∧
      x.evN (pidx x i (base L i c + j')) =
        (Role.ld ins[j'].1 ins[j'].2.1 ins[j'].2.2).ev i (base L i c + j') := by
    intro j' hj'
    obtain ⟨h1, h2, -⟩ := h.at hi hc (show j' < (labRoles (L i)[c]).length by omega)
    rw [hrole j' hj'] at h2
    exact ⟨h1, h2⟩
  have hk1 : ins.length - 1 < ins.length := by omega
  obtain ⟨hu, heu⟩ := hunit _ hk1
  obtain ⟨-, her⟩ := hunit j hj
  obtain ⟨hL0, he0⟩ := hunit 0 hins
  have hRr : (x.evN (pidx x i (base L i c + j))).isR = true := by rw [her]; rfl
  have hRu : (x.evN (pidx x i (base L i c + (ins.length - 1)))).isR = true := by rw [heu]; rfl
  have hR0 : (x.evN (pidx x i (base L i c + 0))).isR = true := by rw [he0]; rfl
  have hκr : κ x (pidx x i (base L i c + j)) ≤ T := by
    rw [← hT]
    rcases Nat.lt_or_ge j (ins.length - 1) with hlt | hge
    · exact Nat.le_of_lt (h.κ_ppoR hr' hu (by rw [her, heu]; simp) (by rw [her, heu]; simp; omega)
        hRr (isM_R hRu))
    · rw [show j = ins.length - 1 by omega]
  have hκ0 : κ x (pidx x i (base L i c + 0)) ≤ κ x (pidx x i (base L i c + j)) := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; exact le_rfl
    · exact Nat.le_of_lt (h.κ_ppoR hL0 hr' (by rw [he0, her]; simp) (by rw [he0, her]; simp; omega)
        hR0 (isM_R hRr))
  obtain ⟨-, -, y, hyr, hyw, -⟩ := frR_elim hfr
  simp only at hyr hyw
  have hκrw := h.κ_fr hr' hw hfr
  have hcell := Silmaril.Proofs.X86.Concurrency.Cir.Domain.cell_eq h.cells
    (a := ⟨w, hw⟩) (b := ⟨_, hr'⟩) (by rw [ev_eq]; exact isM_W hW) (by rw [ev_eq]; exact isM_R hRr)
    (by rw [ev_eq]; exact hyw) (by rw [ev_eq]; exact hyr)
  rw [ev_eq, ev_eq] at hcell
  have hwa : (x.evN w).addr = ins[j].1 := by rw [hcell.1, her]; rfl
  obtain ⟨-, bsL, hokL⟩ := h.lab i _ (List.getElem_mem hc)
  rw [hl] at hokL
  have hinsloc := (hokL.1 ins[j] (List.mem_append_left _ (List.getElem_mem hj))).1
  obtain ⟨-, -, -, -, -, hbelow⟩ := loc_of_cell h.lf hinsloc
  have hwlow : (x.evN w).addr < ctlAddr 0 := by
    rw [hwa]; have := (loc_of_cell h.lf hinsloc); obtain ⟨_, _, _, _, hp, hb⟩ := this; omega
  have htouch : (L i)[c].Touches (x.evN w).addr := by
    rw [hl, hwa]
    exact .inl ⟨ins[j].2.2, List.mem_map.mpr ⟨ins[j], List.getElem_mem hj, rfl⟩⟩
  have hna : (L i)[c].na = true := by rw [hl]; rfl
  have htrig : trig (L i)[c] = some (ins.length - 1) := by
    rw [hl]; simp only [trig]
    rw [ite_eq_right (List.ne_nil_of_length_pos hins)]
  by_cases htw : (x.evN w).tid = i
  · -- the block's own thread: only writes after the block's last load
    rcases Nat.lt_trichotomy (x.evN w).pos (x.evN (pidx x i (base L i c + j))).pos with h1 | h1 | h1
    · exact h.cyc_fr hr' hw (by rw [htw, her]; simp) h1 hW hRr hyr hyw hfr
    · have := h.uniq hw hr' (by rw [htw, her]; simp) h1; subst this; exact RW_false hRr hW
    · have hposu : (x.evN (pidx x i (base L i c + (ins.length - 1)))).pos < (x.evN w).pos := by
        by_contra hle
        rw [heu] at hle; simp only [Role.ev_pos] at hle
        rw [her] at h1; simp only [Role.ev_pos] at h1
        obtain ⟨cw, hcw, kw, hkw, hpw, hew, -⟩ := h.labAt hw htw
        have hj' : (x.evN w).pos - base L i c < ins.length := by omega
        obtain ⟨rfl, rfl⟩ := lab_unique hcw hc hkw (show (x.evN w).pos - base L i c <
          (labRoles (L i)[c]).length by omega) (by omega)
        have : x.evN w = (Role.ld ins[(x.evN w).pos - base L i cw].1
            ins[(x.evN w).pos - base L i cw].2.1 ins[(x.evN w).pos - base L i cw].2.2).ev i
            (base L i cw + ((x.evN w).pos - base L i cw)) := by
          rw [← hrole _ hj']; exact hew
        rw [this] at hW; simp [Role.ev, Ev.isW] at hW
      cases hlw : isLW (x.evN w)
      · have := h.κ_ppoR hu hw (by rw [heu, htw]; simp) hposu hRu (isM_W hW)
        rw [fst_of hlw] at hvis; omega
      · obtain ⟨rw', hrw, ht', hp', hlr, -⟩ := h.partnerW hw hlw
        rw [h.fst_lw hlw hrw ht' hp'] at hvis
        rcases Nat.lt_or_ge (x.evN (pidx x i (base L i c + (ins.length - 1)))).pos (x.evN rw').pos
          with h2 | h2
        · have := h.κ_ppoR hu hrw (by rw [heu, ht', htw]; simp) h2 hRu
            (by simp only [isLR, Bool.and_eq_true] at hlr; exact isM_R hlr.1)
          omega
        · have := h.uniq hrw hu (by rw [ht', htw, heu]; simp) (by omega)
          subst this
          rw [heu] at hlr; simp [isLR, Role.ev] at hlr
  · -- another thread: run to the write and contradict ownership
    have hfst := h.κ_fst hw
    have hbit := bit_le x w
    have hne : κ x (fstU x w) ≠ κ x (pidx x i (base L i c + j)) := by
      intro he
      have := h.κ_inj (h.fst_spec hw).1 hr' he
      have h3 := tid_fst h hw
      rw [this, her] at h3; simp at h3; exact htw h3.symm
    have hτ : κ x (pidx x i (base L i c + 0)) ≤ κ x (fstU x w) := by omega
    obtain ⟨cnt₀, hI₀, hR₀⟩ := hist _ hvis
    generalize hτd : κ x (fstU x w) = τ at hI₀ hR₀ hτ hvis
    have hcn : cnt₀ i ≤ c := by
      by_contra hn
      have := hI₀.past i c hc _ (by omega) htrig
      omega
    obtain ⟨hI₁, hR₁⟩ := hr.catchupTo h hI₀ hR₀ hi hc (k := 0) (by omega) (isM_R hR0) hτ hcn
    have ht'N : (x.evN w).tid < P.threads.length := h.tid_lt hw
    cases hlw : isLW (x.evN w)
    · obtain ⟨cw, hcw, e, he, hpw, hea, hwe⟩ := h.native hw rfl hW hlw hwlow
      have hκw : κ x w = τ := by rw [← hτd, fst_of hlw]
      obtain ⟨cnt₂, hR₂, hc₂, hcw₂⟩ : ∃ cnt₂ : Nat → Nat, Reach P L x S τ cnt₂ ∧ cnt₂ i = c ∧
          cw < cnt₂ (x.evN w).tid := by
        by_cases hex : cw < upd cnt₀ i c (x.evN w).tid
        · exact ⟨_, hR₁, by simp, hex⟩
        · have hwM : (x.evN (pidx x (x.evN w).tid (base L (x.evN w).tid cw + e.1))).isM = true := by
            rw [← hwe]; exact isM_W hW
          obtain ⟨hI₂, hR₂⟩ := hr.catchupTo h hI₁ hR₁ ht'N hcw (nsts_role he).1 hwM
            (by rw [← hwe, hκw]) (by omega)
          have hlz : trig (L (x.evN w).tid)[cw] = none := by
            cases ht : trig (L (x.evN w).tid)[cw] with
            | none => rfl
            | some k' =>
              exfalso
              obtain ⟨hk', hu', hR', htu', hpu'⟩ := h.trig_unit ht'N hcw ht
              have hlt := trig_lt_nsts ht he
              have := h.κ_ppoR hu' hw (by rw [htu']) (by rw [hpu', hpw]; omega) hR' (isM_W hW)
              have := hI₁.trigDone _ cw hcw k' ht (by omega)
              exact hex this
          have s := hr.lazyStepAt h ht'N (T := τ) (cnt := upd (upd cnt₀ i c) (x.evN w).tid cw)
            (by simp) hcw hlz
            (fun e' he' => by
              by_contra hlt
              have := hI₁.stDone _ cw hcw e' he' (by omega)
              exact hex this)
            (fun hm => by rw [hm] at he; simp [nsts] at he)
          refine ⟨_, star_trans hR₂ s, ?_, by simp⟩
          rw [upd_ne _ _ (Ne.symm htw), upd_ne _ _ (Ne.symm htw)]; simp
      have hb : (newest (nBuf L x τ cnt₂ (x.evN w).tid) (x.evN w).addr).isSome := by
        have hq := rawP_mem (T := τ) (cnt := cnt₂) hcw₂ hcw he (by rw [← hwe, hκw])
        rw [nBuf, newest_dropWhile]
        exact newest_isSome (List.mem_map_of_mem (f := Prod.snd) hq) (by simp [Ent.val, hea])
      exact hr.own_buf G hR₂ hi (by rw [hc₂]; exact hc) (by simp only [hc₂]; exact hna)
        (by simp only [hc₂]; exact htouch) htw hb
    · obtain ⟨rw', hrw, ht', hp', hlr, ha', -⟩ := h.partnerW hw hlw
      have hκr : κ x rw' = τ := by rw [← hτd, h.fst_lw hlw hrw ht' hp']
      obtain ⟨cw, hcw, kw, hkw, hpw, hew, -⟩ := h.labAt hrw ht'
      have hlr' := hlr
      rw [hew] at hlr'
      obtain ⟨a', sz', o', hrole'⟩ := role_isLR hlr'
      have hlow' : a' < ctlAddr 0 := by
        have : (x.evN rw').addr = a' := by rw [hew, hrole']; rfl
        rw [← this, ← ha']; exact hwlow
      obtain ⟨m', n', hlab', rfl⟩ := lr_rmw hkw hrole' hlow'
      have htr : trig (L (x.evN w).tid)[cw] = some 0 := by rw [hlab']; rfl
      have hrw0 : pidx x (x.evN w).tid (base L (x.evN w).tid cw + 0) = rw' := by
        rw [← hpw, ← ht', h.pidx_eq hrw]
      have hcn' : upd cnt₀ i c (x.evN w).tid ≤ cw := by
        by_contra hn
        have := hI₁.past _ cw hcw 0 (by omega) htr
        rw [hrw0] at this; omega
      have hrM : (x.evN (pidx x (x.evN w).tid (base L (x.evN w).tid cw + 0))).isM = true := by
        rw [hrw0]
        simp only [isLR, Bool.and_eq_true] at hlr; exact isM_R hlr.1
      obtain ⟨hI₂, hR₂⟩ := hr.catchupTo h hI₁ hR₁ ht'N hcw hkw hrM (by rw [hrw0, hκr]) hcn'
      have hci : upd (upd cnt₀ i c) (x.evN w).tid cw i = c := by
        rw [upd_ne _ _ (Ne.symm htw)]; simp
      have hcw' : upd (upd cnt₀ i c) (x.evN w).tid cw (x.evN w).tid = cw := by simp
      have hwa' : (x.evN w).addr = a' := by rw [ha', hew, hrole']; rfl
      exact hr.own_lock G hR₂ hi ht'N (by rw [hci]; exact hc) (by simp only [hci]; exact hna)
        (by simp only [hci]; exact htouch) htw (by rw [hcw']; exact hcw)
        (by simp only [hcw', hlab']; rfl)
        (by simp only [hcw', hlab']; rw [hwa']; exact .inl ⟨o', by simp [Lab.reads]⟩)

end

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
