module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.MemoryBulk
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.Memory

@[expose] public section

/-! # Lime1 → Core step simulation: `memory.copy`

Lime1 copies atomically (`Memory.copy`, memmove semantics); Core iterates byte by
byte: `copy-le` (destination ≤ source) copies forwards, `copy-gt` backwards from the
high end. Two loop lemmas (`copy_fwd`, `copy_bwd`) run the Core iteration by
induction on the count with a pointwise memmove invariant; `memoryCopy` /
`memoryCopyTrap` assemble them with the byte-level lemmas of `MemoryBulk`. -/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution.ToCore

variable {H : Type}

local notation "CStep" => Silmaril.Wasm.Execution.Core.Step
  Silmaril.Wasm.Numerics.Profile.spec

/-! ## Core-store helpers -/

theorem cp_mem_setMem {cs : CStore H} {cf : CFrame} {ma : Nat} {mi : Core.MemInst}
    (h : cs.mem? cf ⟨0⟩ = some (ma, mi)) (mi' : Core.MemInst) :
    (cs.setMem ma mi').mem? cf ⟨0⟩ = some (ma, mi') := by
  simp only [Core.Store.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h ⊢
  obtain ⟨a, ha, m, hm, he⟩ := h
  cases he
  refine ⟨ma, ha, mi', ?_, rfl⟩
  simp only [Core.Store.setMem]
  rw [List.getElem?_set_self']
  simp [hm]

theorem cp_setMem_self {cs : CStore H} {cf : CFrame} {ma : Nat} {mi : Core.MemInst}
    (h : cs.mem? cf ⟨0⟩ = some (ma, mi)) : cs.setMem ma mi = cs := by
  simp only [Core.Store.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, m, hm, he⟩ := h
  cases he
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hm
  simp only [Core.Store.setMem]
  rw [← heq, List.set_getElem_self hlt]

theorem cp_setMem_setMem (cs : CStore H) (ma : Nat) (m₁ m₂ : Core.MemInst) :
    (cs.setMem ma m₁).setMem ma m₂ = cs.setMem ma m₂ := by
  simp [Core.Store.setMem]

/-- The Core `memory.copy` redex on memory 0 with `i32` operands. -/
def cpCode (d sa n : BitVec 32) : List Core.Admin :=
  [Core.aconst .i32 d, Core.aconst .i32 sa, Core.aconst .i32 n, .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]

theorem cp_setWidth (w : BitVec 8) :
    ((w.setWidth 32).setWidth 8).toNat = w.toNat := by
  simp

/-- One byte move: `[d, s, load8u, store8] ++ rest` reduces (in two steps) to `rest` with
byte `d` set to byte `s`. -/
theorem cp_move {tgt : CHostSemantics H} {cs : CStore H} {cf : CFrame} {ma : Nat}
    {mi : Core.MemInst} (hm : cs.mem? cf ⟨0⟩ = some (ma, mi)) (d sa : BitVec 32)
    (hd : d.toNat + 1 ≤ mi.bytes.size) (hs : sa.toNat + 1 ≤ mi.bytes.size)
    (rest : List Core.Admin) (hr : rest ≠ []) :
    ∃ A : ByteArray, A.size = mi.bytes.size ∧
      (∀ j, A.data[j]? = if j = d.toNat then mi.bytes.data[sa.toNat]? else mi.bytes.data[j]?) ∧
      Relation.TransGen (CStep tgt)
        ⟨cs, cf, [Core.aconst .i32 d, Core.aconst .i32 sa, Core.load8u ⟨0⟩, Core.store8 ⟨0⟩] ++ rest⟩
        ⟨cs.setMem ma { mi with bytes := A }, cf, rest⟩ := by
  obtain ⟨w, hl, hw⟩ := bulk_load8 (M := mi.bytes) (i := sa.toNat) hs
  obtain ⟨A, hA, hsz, hget⟩ := bulk_store8 (M := mi.bytes) (i := d.toNat)
    ((w.setWidth 32).setWidth 8) hd
  refine ⟨A, hsz, fun j => ?_, ?_⟩
  · rw [hget j, hw, cp_setWidth]
  · have h1 : CStep tgt
        ⟨cs, cf, [Core.aconst .i32 d, Core.aconst .i32 sa, Core.load8u ⟨0⟩, Core.store8 ⟨0⟩] ++ rest⟩
        ⟨cs, cf, [Core.aconst .i32 d, .plain (.intConst .i32 (w.setWidth 32)), Core.store8 ⟨0⟩]
          ++ rest⟩ :=
      Core.Step.ctxtInstrs (vs := [.num ⟨.int .i32, d⟩])
        (is := [Core.aconst .i32 sa, Core.load8u ⟨0⟩]) (rest := Core.store8 ⟨0⟩ :: rest)
        (.memory (.loadPackVal (a := .i32) (i := sa) (sz := .i8) (sx := .unsigned) (c := w)
          hm hl)) (Or.inl (by simp))
    have h2 : CStep tgt
        ⟨cs, cf, [Core.aconst .i32 d, .plain (.intConst .i32 (w.setWidth 32)), Core.store8 ⟨0⟩]
          ++ rest⟩
        ⟨cs.setMem ma { mi with bytes := A }, cf, rest⟩ := by
      have hA' : Memory.store mi.bytes (Core.effAddr d.toNat Core.memarg0)
          (count := PackSize.i8.width / 8) ((w.setWidth 32).setWidth _) = some A := hA
      have := Core.Step.ctxtInstrs (P := Silmaril.Wasm.Numerics.Profile.spec) (host := tgt)
        (vs := []) (rest := rest)
        (.memory (.storePackVal (a := .i32) (i := d) (t := .i32) (sz := .i8)
          (c := w.setWidth 32) (b := A) hm (arg := Core.memarg0) hA')) (Or.inr hr)
      simpa [Core.vals, Core.store8] using this
    exact .head h1 (.single h2)

/-! ## Loops -/

theorem copy_fwd {tgt : CHostSemantics H} {cf : CFrame} {ma : Nat} :
    ∀ (k : Nat) (cs : CStore H) (mi : Core.MemInst) (d sa n : BitVec 32), n.toNat = k →
      cs.mem? cf ⟨0⟩ = some (ma, mi) → mi.bytes.size ≤ 2 ^ 32 →
      d.toNat + k ≤ mi.bytes.size → sa.toNat + k ≤ mi.bytes.size →
      (0 < k → d.toNat ≤ sa.toNat) →
      ∃ B : ByteArray, B.size = mi.bytes.size ∧
        (∀ j, B.data[j]? = if d.toNat ≤ j ∧ j < d.toNat + k then
          mi.bytes.data[sa.toNat + (j - d.toNat)]? else mi.bytes.data[j]?) ∧
        Relation.TransGen (CStep tgt) ⟨cs, cf, cpCode d sa n⟩
          ⟨cs.setMem ma { mi with bytes := B }, cf, []⟩ := by
  intro k
  induction k with
  | zero =>
    intro cs mi d sa n hn hm _ hd hs _
    have : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst this
    refine ⟨mi.bytes, rfl, fun j => by simp, ?_⟩
    rw [show ({ mi with bytes := mi.bytes } : Core.MemInst) = mi from rfl, cp_setMem_self hm]
    exact .single (.memory (.copyZero (a₁ := .i32) (a₂ := .i32) (a' := .i32) (i₁ := d) (i₂ := sa)
      hm hm ⟨show d.toNat ≤ mi.bytes.size by omega, show sa.toNat ≤ mi.bytes.size by omega⟩))
  | succ k ih =>
    intro cs mi d sa n hn hm hsz hd hs hle
    have hle := hle (by omega)
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    obtain ⟨A, hAsz, hA, hst⟩ := cp_move (tgt := tgt) hm d sa (by omega) (by omega)
      (cpCode (d + 1) (sa + 1) (n - 1)) (by simp [cpCode])
    have hm' := cp_mem_setMem hm { mi with bytes := A }
    have hn' : (n - 1).toNat = k := by bv_omega
    have hd1 : (d + 1).toNat ≤ d.toNat + 1 := by bv_omega
    have hs1 : (sa + 1).toNat ≤ sa.toNat + 1 := by bv_omega
    have hd2 : 0 < k → (d + 1).toNat = d.toNat + 1 := by intro; bv_omega
    have hs2 : 0 < k → (sa + 1).toNat = sa.toNat + 1 := by intro; bv_omega
    obtain ⟨B, hBsz, hB, hsteps⟩ := ih (cs.setMem ma { mi with bytes := A })
      { mi with bytes := A } (d + 1) (sa + 1) (n - 1) hn' hm'
      (by show A.size ≤ 2 ^ 32; omega) (by show _ ≤ A.size; omega) (by show _ ≤ A.size; omega)
      (by intro hk; rw [hd2 hk, hs2 hk]; omega)
    refine ⟨B, by rw [hBsz]; exact hAsz, fun j => ?_, ?_⟩
    · rw [hB j]
      simp only [hA]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
      · have e1 := hd2 hk
        have e2 := hs2 hk
        split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
    · have hc : CStep tgt ⟨cs, cf, cpCode d sa n⟩
          ⟨cs, cf, [Core.aconst .i32 d, Core.aconst .i32 sa, Core.load8u ⟨0⟩, Core.store8 ⟨0⟩]
            ++ cpCode (d + 1) (sa + 1) (n - 1)⟩ :=
        .memory (.copyLe (a₁ := .i32) (a₂ := .i32) (a' := .i32) (i₁ := d) (i₂ := sa) (n := n)
          hm hm ⟨show d.toNat + n.toNat ≤ mi.bytes.size by omega,
            show sa.toNat + n.toNat ≤ mi.bytes.size by omega⟩ hn0 hle)
      have hfin := hsteps
      rw [cp_setMem_setMem] at hfin
      exact .head hc (.trans hst hfin)

theorem copy_bwd {tgt : CHostSemantics H} {cf : CFrame} {ma : Nat} :
    ∀ (k : Nat) (cs : CStore H) (mi : Core.MemInst) (d sa n : BitVec 32), n.toNat = k →
      cs.mem? cf ⟨0⟩ = some (ma, mi) → mi.bytes.size ≤ 2 ^ 32 →
      d.toNat + k ≤ mi.bytes.size → sa.toNat + k ≤ mi.bytes.size →
      (0 < k → sa.toNat < d.toNat) →
      ∃ B : ByteArray, B.size = mi.bytes.size ∧
        (∀ j, B.data[j]? = if d.toNat ≤ j ∧ j < d.toNat + k then
          mi.bytes.data[sa.toNat + (j - d.toNat)]? else mi.bytes.data[j]?) ∧
        Relation.TransGen (CStep tgt) ⟨cs, cf, cpCode d sa n⟩
          ⟨cs.setMem ma { mi with bytes := B }, cf, []⟩ := by
  intro k
  induction k with
  | zero =>
    intro cs mi d sa n hn hm _ hd hs _
    have : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst this
    refine ⟨mi.bytes, rfl, fun j => by simp, ?_⟩
    rw [show ({ mi with bytes := mi.bytes } : Core.MemInst) = mi from rfl, cp_setMem_self hm]
    exact .single (.memory (.copyZero (a₁ := .i32) (a₂ := .i32) (a' := .i32) (i₁ := d) (i₂ := sa)
      hm hm ⟨show d.toNat ≤ mi.bytes.size by omega, show sa.toNat ≤ mi.bytes.size by omega⟩))
  | succ k ih =>
    intro cs mi d sa n hn hm hsz hd hs hlt
    have hlt := hlt (by omega)
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hdk : (d + BitVec.ofNat 32 n.toNat - 1).toNat = d.toNat + k := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hsk : (sa + BitVec.ofNat 32 n.toNat - 1).toNat = sa.toNat + k := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    obtain ⟨A, hAsz, hA, hst⟩ := cp_move (tgt := tgt) hm (d + BitVec.ofNat 32 n.toNat - 1)
      (sa + BitVec.ofNat 32 n.toNat - 1) (by omega) (by omega)
      (cpCode d sa (n - 1)) (by simp [cpCode])
    have hm' := cp_mem_setMem hm { mi with bytes := A }
    have hn' : (n - 1).toNat = k := by bv_omega
    obtain ⟨B, hBsz, hB, hsteps⟩ := ih (cs.setMem ma { mi with bytes := A })
      { mi with bytes := A } d sa (n - 1) hn' hm'
      (by show A.size ≤ 2 ^ 32; omega) (by show _ ≤ A.size; omega) (by show _ ≤ A.size; omega) (fun _ => hlt)
    refine ⟨B, by rw [hBsz]; exact hAsz, fun j => ?_, ?_⟩
    · rw [hB j]
      simp only [hA, hdk, hsk]
      split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
    · have hc : CStep tgt ⟨cs, cf, cpCode d sa n⟩
          ⟨cs, cf, [Core.aconst .i32 (d + BitVec.ofNat 32 n.toNat - 1 : BitVec 32),
            Core.aconst .i32 (sa + BitVec.ofNat 32 n.toNat - 1 : BitVec 32), Core.load8u ⟨0⟩, Core.store8 ⟨0⟩]
            ++ cpCode d sa (n - 1)⟩ :=
        .memory (.copyGt (a₁ := .i32) (a₂ := .i32) (a' := .i32) (i₁ := d) (i₂ := sa) (n := n)
          hm hm ⟨show d.toNat + n.toNat ≤ mi.bytes.size by omega,
            show sa.toNat + n.toNat ≤ mi.bytes.size by omega⟩ hn0 hlt)
      have hfin := hsteps
      rw [cp_setMem_setMem] at hfin
      exact .head hc (.trans hst hfin)

/-! ## Head rules -/

theorem memoryCopy {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame}
    {d src n : BitVec 32} {a : MemAddr} {m : MemInst} {bytes : Memory.Bytes}
    (memory : frameMemory s f = some (a, m))
    (copied : Memory.copy m.data d.toNat src.toNat n.toNat = some bytes)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 d), value (.int .i32 src), value (.int .i32 n),
      .source .memoryCopy]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step
        Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, []⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_value _ _)
      (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _)
        (mem_rigid_nil _)))))
  have hm := mem_lookup hE hF memory
  have hwfm := mem_frameMemory_wf hwf.1 memory
  have hb : ¬ (m.data.size < src.toNat + n.toNat ∨ m.data.size < d.toNat + n.toNat) := by
    intro h; rw [← bulk_copy_none] at h; rw [h] at copied; cases copied
  have hsize : bytes.size = m.data.size := by
    have := bulk_copy_get copied
    simp only [Memory.copy, Option.bind_eq_bind, Option.bind_eq_some_iff] at copied
    obtain ⟨_, _, hw⟩ := copied
    exact Memory.writeBytes_size _ _ _ _ hw
  have hmain : ∃ B : ByteArray, B.size = m.toCore.bytes.size ∧
      (∀ j, B.data[j]? = if d.toNat ≤ j ∧ j < d.toNat + n.toNat then
        m.toCore.bytes.data[src.toNat + (j - d.toNat)]? else m.toCore.bytes.data[j]?) ∧
      Relation.TransGen (CStep tgt) ⟨cfg.store, cfg.frame, cpCode d src n⟩
        ⟨cfg.store.setMem a.value { m.toCore with bytes := B }, cfg.frame, []⟩ := by
    have h1 : m.toCore.bytes = m.data := rfl
    by_cases hle : d.toNat ≤ src.toNat
    · exact copy_fwd n.toNat cfg.store m.toCore d src n rfl hm (by rw [h1]; exact hwfm.1)
        (by rw [h1]; omega) (by rw [h1]; omega) (fun _ => hle)
    · exact copy_bwd n.toNat cfg.store m.toCore d src n rfl hm (by rw [h1]; exact hwfm.1)
        (by rw [h1]; omega) (by rw [h1]; omega) (fun _ => by omega)
  obtain ⟨B, _, hB, hsteps⟩ := hmain
  have hBeq : B = bytes := bulk_ext fun j => by
    rw [hB j, bulk_copy_get copied j]; rfl
  subst hBeq
  refine ⟨⟨cfg.store.setMem a.value ({ m with data := B } : MemInst).toCore, cfg.frame,
    Admin.listToCore (setMemory s a { m with data := B }) []⟩, ?_,
    mem_sim_mk (mem_erase_setMem hE a _) hF
      ⟨mem_storeWF_set hwf.1 memory (by rw [hsize]; exact hwfm.1) rfl, hwf.2.1, trivial⟩⟩
  rw [hc, ← mem_toCore_bytes m B hsize]
  exact hsteps

theorem memoryCopyTrap {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame}
    {d src n : BitVec 32} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (copied : Memory.copy m.data d.toNat src.toNat n.toNat = none)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 d), value (.int .i32 src), value (.int .i32 n),
      .source .memoryCopy]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step
        Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_value _ _)
      (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _)
        (mem_rigid_nil _)))))
  have hm := mem_lookup hE hF memory
  have hb := bulk_copy_none.mp copied
  refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [.trap]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, trivial, trivial⟩⟩
  rw [hc]
  exact .single (.memory (.copyOob (a₁ := .i32) (a₂ := .i32) (a' := .i32) (i₁ := d) (i₂ := src)
    (n := n) hm hm hb.symm))

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
