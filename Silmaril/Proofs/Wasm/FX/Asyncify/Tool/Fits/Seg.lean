module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Fits.Basic

/-!
# The memory segments of the generated code stay in bounds

Saving a frame record at `a` (`saveCode`), restoring one from `a` (`restoreCode`), writing a
request (`reqCode`) and reading the answers (`pushAns`): every access ends at or below `cap` when
the record, or the request area, ends there.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem accessAt_st {o : Nat} (ho : o < 2 ^ 64) (v w : W) (ops : List W) :
    accessAt (st o) (v :: w :: ops) = some (w.toNat + o) := by
  simp [accessAt, st, marg_off ho]

theorem accessAt_ld {o : Nat} (ho : o < 2 ^ 64) (w : W) (ops : List W) :
    accessAt (ld o) (w :: ops) = some (w.toNat + o) := by
  simp [accessAt, ld, marg_off ho]

/-- A store whose address and value are pushed by two instructions without access. -/
theorem segSafe_st {cap o : Nat} {x y : Instr} {s : LS} (hx : AccFree x) (hy : AccFree y)
    (ho : o < 2 ^ 64)
    (h : ∀ s1, segStep x s = some s1 → ∀ s2, segStep y s1 = some s2 →
      ∃ v w ops, s2.ops = v :: w :: ops ∧ w.toNat + o + 4 ≤ cap) :
    SegSafe cap [x, y, st o] s := by
  refine ⟨fun a ha => (by rw [hx] at ha; cases ha), fun s1 h1 => ?_⟩
  refine ⟨fun a ha => (by rw [hy] at ha; cases ha), fun s2 h2 => ?_⟩
  refine ⟨fun a ha => ?_, fun _ _ => trivial⟩
  obtain ⟨v, w, ops, hops, hle⟩ := h s1 h1 s2 h2
  have hacc : accessAt (st o) s2.ops = some (w.toNat + o) := by rw [hops]; exact accessAt_st ho v w ops
  have hae : a = w.toNat + o := Option.some.inj (ha.symm.trans hacc)
  omega

/-- A load whose address is pushed by an instruction without access. -/
theorem segSafe_ld {cap o : Nat} {x : Instr} {s : LS} (hx : AccFree x) (ho : o < 2 ^ 64)
    (h : ∀ s1, segStep x s = some s1 → ∃ w ops, s1.ops = w :: ops ∧ w.toNat + o + 4 ≤ cap) :
    SegSafe cap [x, ld o] s := by
  refine ⟨fun a ha => (by rw [hx] at ha; cases ha), fun s1 h1 => ?_⟩
  refine ⟨fun a ha => ?_, fun _ _ => trivial⟩
  obtain ⟨w, ops, hops, hle⟩ := h s1 h1
  have hacc : accessAt (ld o) s1.ops = some (w.toNat + o) := by rw [hops]; exact accessAt_ld ho w ops
  have hae : a = w.toNat + o := Option.some.inj (ha.symm.trans hacc)
  omega

theorem segStep_gSp {ls ops gs : List W} {sp : W} {mem : Nat → W} (hsp : gs[1]? = some sp) :
    segStep gSp ⟨ls, ops, gs, mem⟩ = some ⟨ls, sp :: ops, gs, mem⟩ := by
  simp [segStep, ctlOf, segCore, gSp, hsp]

theorem segStep_c32 {n : Nat} {s : LS} :
    segStep (c32 n) s = some { s with ops := BitVec.ofNat 32 n :: s.ops } := by
  simp [segStep, ctlOf, segCore, c32, pexec]

theorem segStep_get {ls ops gs : List W} {mem : Nat → W} {a : LocalIdx}
    (h : a.value.val < ls.length) :
    segStep (.localGet a) ⟨ls, ops, gs, mem⟩ = some ⟨ls, ls[a.value.val] :: ops, gs, mem⟩ := by
  simp [segStep, ctlOf, segCore, pexec, List.getElem?_eq_getElem h]

/-- Storing locals `i … i+n-1` at `sp + 4i, …` stays in bounds when `sp + 4 (i + n) ≤ cap`. -/
theorem saveLocals_safe {cap : Nat} {ls ops gs : List W} {sp : W} (hsp : gs[1]? = some sp) :
    ∀ {i n : Nat} {mem : Nat → W}, i + n ≤ ls.length → 4 * (i + n) < 2 ^ 32 →
    sp.toNat + 4 * (i + n) ≤ cap → SegSafe cap (saveLocals i n) ⟨ls, ops, gs, mem⟩
  | i, 0, mem, _, _, _ => by simp [saveLocals, SegSafe]
  | i, n + 1, mem, h1, h2, h3 => by
    have hi : i < ls.length := by omega
    have hli : (lidx i).value.val = i := lidx_val (by omega)
    have hhead : SegSafe cap [gSp, .localGet (lidx i), st (4 * i)] ⟨ls, ops, gs, mem⟩ := by
      refine segSafe_st (accFree_gget _) (accFree_get _) (by omega) fun s1 e1 s2 e2 => ?_
      have hs1 : s1 = ⟨ls, sp :: ops, gs, mem⟩ :=
        Option.some.inj (e1.symm.trans (segStep_gSp hsp))
      subst hs1
      have hs2 : s2 = ⟨ls, ls[i] :: sp :: ops, gs, mem⟩ := by
        have := segStep_get (gs := gs) (mem := mem) (ops := sp :: ops) (a := lidx i) (by rw [hli]; omega)
        simp only [hli] at this
        exact Option.some.inj (e2.symm.trans this)
      exact ⟨ls[i], sp, ops, by rw [hs2], by omega⟩
    refine segSafe_append hhead fun s' hs' => ?_
    have hseg : runSeg [gSp, .localGet (lidx i), st (4 * i)] ⟨ls, ops, gs, mem⟩ =
        some ⟨ls, ops, gs, upd mem (sp.toNat + 4 * i) ls[i]⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, gSp, st, pexec, hsp, hli,
        marg_off (show 4 * i < 2 ^ 64 by omega), hi]
    have hs' : s' = ⟨ls, ops, gs, upd mem (sp.toNat + 4 * i) ls[i]⟩ :=
      Option.some.inj (hs'.symm.trans hseg)
    rw [hs']
    exact saveLocals_safe hsp (i := i + 1) (n := n) (by omega) (by omega) (by omega)

/-- Reloading locals `i … i+n-1` from `sp + 4i, …` stays in bounds when `sp + 4 (i + n) ≤ cap`. -/
theorem loadLocals_safe {cap : Nat} {ops gs : List W} {sp : W} {mem : Nat → W}
    (hsp : gs[1]? = some sp) :
    ∀ {i n : Nat} {ls : List W}, i + n = ls.length → 4 * (i + n) < 2 ^ 32 →
    sp.toNat + 4 * (i + n) ≤ cap → SegSafe cap (loadLocals i n) ⟨ls, ops, gs, mem⟩
  | i, 0, ls, _, _, _ => by simp [loadLocals, SegSafe]
  | i, n + 1, ls, h1, h2, h3 => by
    have hi : i < ls.length := by omega
    have hli : (lidx i).value.val = i := lidx_val (by omega)
    have hhead : SegSafe cap ([gSp, ld (4 * i)] ++ [.localSet (lidx i)]) ⟨ls, ops, gs, mem⟩ := by
      refine segSafe_append (segSafe_ld (accFree_gget _) (by omega) fun s1 e1 => ?_)
        fun _ _ => segSafe_free fun j hj => by simp at hj; subst hj; exact accFree_set _
      have hs1 : s1 = ⟨ls, sp :: ops, gs, mem⟩ :=
        Option.some.inj (e1.symm.trans (segStep_gSp hsp))
      exact ⟨sp, ops, by rw [hs1], by omega⟩
    refine segSafe_append hhead fun s' hs' => ?_
    have hseg : runSeg ([gSp, ld (4 * i)] ++ [.localSet (lidx i)]) ⟨ls, ops, gs, mem⟩ =
        some ⟨ls.set i (mem (sp.toNat + 4 * i)), ops, gs, mem⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, gSp, ld, pexec, hsp, hli,
        marg_off (show 4 * i < 2 ^ 64 by omega), hi]
    have hs' : s' = ⟨ls.set i (mem (sp.toNat + 4 * i)), ops, gs, mem⟩ :=
      Option.some.inj (hs'.symm.trans hseg)
    rw [hs']
    exact loadLocals_safe hsp (i := i + 1) (n := n) (by rw [List.length_set]; omega) (by omega)
      (by omega)

theorem accFree_push {F : Nat} : ∀ i ∈ [gSp, c32 (4 * F), addI, sSp], AccFree i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact accFree_gget _
  · exact accFree_c32 _
  · exact accFree_bin _
  · exact accFree_gset _

/-- Storing the resume index at `a + 4 (F - 1)` and bumping `sp` stays in bounds. -/
theorem saveSel_safe {cap F k a : Nat} {tl ops : List W} {g0 : W} {mem : Nat → W}
    (hF : 1 ≤ F) (ha : a + 4 * F < 2 ^ 32) (hcap : a + 4 * F ≤ cap) :
    SegSafe cap ([gSp, c32 k, st (4 * (F - 1))] ++ [gSp, c32 (4 * F), addI, sSp])
      ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ := by
  have hsp : ([g0, BitVec.ofNat 32 a] : List W)[1]? = some (BitVec.ofNat 32 a) := rfl
  have hta : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  refine segSafe_append (segSafe_st (accFree_gget _) (accFree_c32 _) (by omega)
    fun s1 e1 s2 e2 => ?_) fun _ _ => segSafe_free accFree_push
  have h1 : s1 = ⟨tl, BitVec.ofNat 32 a :: ops, [g0, BitVec.ofNat 32 a], mem⟩ :=
    Option.some.inj (e1.symm.trans (segStep_gSp hsp))
  have h2 : s2 = { s1 with ops := BitVec.ofNat 32 k :: s1.ops } :=
    Option.some.inj (e2.symm.trans segStep_c32)
  have hops : s2.ops = BitVec.ofNat 32 k :: BitVec.ofNat 32 a :: ops := by rw [h2, h1]
  exact ⟨_, _, _, hops, by rw [hta]; omega⟩

/-- Saving a frame record at `a` stays in bounds when it ends at or below `cap`. -/
theorem saveCode_safe {cap F k a : Nat} {tl ops : List W} {g0 : W} {mem : Nat → W}
    (hl : tl.length = F) (hF : 1 ≤ F) (ha : a + 4 * F < 2 ^ 32) (hcap : a + 4 * F ≤ cap) :
    SegSafe cap (saveCode F k) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ := by
  have hsp : ([g0, BitVec.ofNat 32 a] : List W)[1]? = some (BitVec.ofNat 32 a) := rfl
  have hta : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  let mem1 := writeWords mem ((BitVec.ofNat 32 a).toNat + 4 * 0) ((tl.drop 0).take (F - 1))
  have hrun : runSeg (saveLocals 0 (F - 1)) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ =
      some ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem1⟩ :=
    saveLocals_seg hsp (by omega) (by omega)
  have hsave : SegSafe cap (saveLocals 0 (F - 1)) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ :=
    saveLocals_safe hsp (by omega) (by omega) (by omega)
  have htail : SegSafe cap ([gSp, c32 k, st (4 * (F - 1))] ++ [gSp, c32 (4 * F), addI, sSp])
      ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem1⟩ := saveSel_safe hF ha hcap
  unfold saveCode
  exact segSafe_append hsave fun s' hs' => (Option.some.inj (hs'.symm.trans hrun)) ▸ htail

/-- Popping and reloading a record from `a` (with `sp = a + 4F` before) stays in bounds when
the record ends at or below `cap`. -/
theorem restoreCode_safe {cap F a : Nat} {ls ops : List W} {g0 : W} {mem : Nat → W}
    (hl : ls.length = F) (ha : a + 4 * F < 2 ^ 32) (hcap : a + 4 * F ≤ cap) :
    SegSafe cap (restoreCode F) ⟨ls, ops, [g0, BitVec.ofNat 32 (a + 4 * F)], mem⟩ := by
  unfold restoreCode
  have h1 : runSeg [gSp, c32 (4 * F), subI, sSp] ⟨ls, ops, [g0, BitVec.ofNat 32 (a + 4 * F)], mem⟩ =
      some ⟨ls, ops, [g0, BitVec.ofNat 32 a], mem⟩ := by
    have hs := sub_ofNat32 a (4 * F)
    simp only [runSeg, segStep, ctlOf, segCore, gSp, sSp, c32, subI, pexec, Numerics.intBinOp]
    simp only [Option.bind_some]
    rw [← hs]; rfl
  refine segSafe_append (segSafe_free fun j hj => ?_) fun s' hs' => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact accFree_gget _
    · exact accFree_c32 _
    · exact accFree_bin _
    · exact accFree_gset _
  · have hs : s' = ⟨ls, ops, [g0, BitVec.ofNat 32 a], mem⟩ := Option.some.inj (hs'.symm.trans h1)
    rw [hs]
    exact loadLocals_safe (sp := BitVec.ofNat 32 a) rfl (by simp [hl]) (by omega)
      (by rw [toNat_ofNat32 (by omega)]; omega)

/-- Writing arguments at words `j, j + 1, …` stays in bounds below `cap`. -/
theorem reqArgs_safe {cap : Nat} {ls ops gs : List W} :
    ∀ {j : Nat} {as : List LocalIdx} {mem : Nat → W}, 4 * (j + as.length) < 2 ^ 32 →
    4 * (j + as.length) ≤ cap → (∀ a ∈ as, a.value.val < ls.length) →
    SegSafe cap (reqArgs j as) ⟨ls, ops, gs, mem⟩
  | j, [], mem, _, _, _ => by simp [reqArgs, SegSafe]
  | j, a :: as, mem, h, hc, ha => by
    have hal : a.value.val < ls.length := ha a (by simp)
    simp only [List.length_cons] at h hc
    have hhead : SegSafe cap [c32 0, .localGet a, st (4 * j)] ⟨ls, ops, gs, mem⟩ := by
      refine segSafe_st (accFree_c32 _) (accFree_get _) (by omega) fun s1 e1 s2 e2 => ?_
      have hs1 := Option.some.inj (e1.symm.trans segStep_c32)
      subst hs1
      have hs2 := Option.some.inj (e2.symm.trans (segStep_get hal))
      subst hs2
      exact ⟨_, _, _, rfl, by simp; omega⟩
    refine segSafe_append hhead fun s' hs' => ?_
    have hseg : runSeg [c32 0, .localGet a, st (4 * j)] ⟨ls, ops, gs, mem⟩ =
        some ⟨ls, ops, gs, upd mem (4 * j) (lv ls a)⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, c32, st, pexec, hal, lv,
        marg_off (show 4 * j < 2 ^ 64 by omega)]
    rw [Option.some.inj (hs'.symm.trans hseg)]
    exact reqArgs_safe (j := j + 1) (by omega) (by omega) fun b hb => ha b (by simp [hb])

/-- Writing a request stays in bounds when the request area does. -/
theorem reqCode_safe {cap : Nat} {ls ops gs : List W} {mem : Nat → W} {f : FuncIdx}
    {as : List LocalIdx} (h : 4 * (1 + as.length) < 2 ^ 32) (hc : 4 * (1 + as.length) ≤ cap)
    (ha : ∀ a ∈ as, a.value.val < ls.length) :
    SegSafe cap (reqCode f as) ⟨ls, ops, gs, mem⟩ := by
  unfold reqCode
  refine segSafe_append (segSafe_st (accFree_c32 _) (accFree_c32 _) (by omega)
    fun s1 e1 s2 e2 => ?_) fun s' hs' => ?_
  · have hs1 := Option.some.inj (e1.symm.trans segStep_c32)
    subst hs1
    have hs2 := Option.some.inj (e2.symm.trans segStep_c32)
    subst hs2
    exact ⟨_, _, _, rfl, by simp; omega⟩
  · have hseg : runSeg [c32 0, c32 f.value.val, st 0] ⟨ls, ops, gs, mem⟩ =
        some ⟨ls, ops, gs, upd mem 0 (BitVec.ofNat 32 f.value.val)⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, c32, st, pexec, marg_off (show 0 < 2 ^ 64 by omega)]
    rw [Option.some.inj (hs'.symm.trans hseg)]
    exact reqArgs_safe (j := 1) h hc ha

/-- Reading answers from words `j, j + 1, …` stays in bounds below `cap`. -/
theorem pushAns_safe {cap : Nat} {ls gs : List W} {mem : Nat → W} :
    ∀ {j m : Nat} {ops : List W}, 4 * (j + m) < 2 ^ 32 → 4 * (j + m) ≤ cap →
    SegSafe cap (pushAns j m) ⟨ls, ops, gs, mem⟩
  | j, 0, ops, _, _ => by simp [pushAns, SegSafe]
  | j, m + 1, ops, h, hc => by
    have hhead : SegSafe cap [c32 0, ld (4 * j)] ⟨ls, ops, gs, mem⟩ := by
      refine segSafe_ld (accFree_c32 _) (by omega) fun s1 e1 => ?_
      have hs1 := Option.some.inj (e1.symm.trans segStep_c32)
      subst hs1
      exact ⟨_, _, rfl, by simp; omega⟩
    refine segSafe_append hhead fun s' hs' => ?_
    have hseg : runSeg [c32 0, ld (4 * j)] ⟨ls, ops, gs, mem⟩ =
        some ⟨ls, mem (4 * j) :: ops, gs, mem⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, c32, ld, pexec,
        marg_off (show 4 * j < 2 ^ 64 by omega)]
    rw [Option.some.inj (hs'.symm.trans hseg)]
    exact pushAns_safe (j := j + 1) (by omega) (by omega)

end Silmaril.Wasm.FX.Asyncify.Tool
