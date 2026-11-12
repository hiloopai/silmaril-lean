module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.MemoryBulk
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.Memory

@[expose] public section

/-! # Lime1 → Core step simulation: `memory.fill`

Lime1 fills atomically (`Memory.fill`); Core iterates `fill-succ` (a `store8`
followed by the recursive fill at `i + 1`, count `n - 1`) until `fill-zero`.
`fill_loop` runs the Core iteration by induction on the count, tracking the
bytes pointwise; the wraparound of `i + 1` only happens when the remaining
count is `0`, so no size bound is needed for the loop itself. -/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution.ToCore

variable {H : Type}

theorem fill_mem?_setMem {cs : CStore H} {cf : CFrame} {x : Silmaril.Wasm.MemIdx} {ma : Nat}
    {mi : Silmaril.Wasm.Execution.Core.MemInst} (hm : cs.mem? cf x = some (ma, mi))
    (mi' : Silmaril.Wasm.Execution.Core.MemInst) :
    (cs.setMem ma mi').mem? cf x = some (ma, mi') := by
  simp only [Silmaril.Wasm.Execution.Core.Store.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hm ⊢
  obtain ⟨a', ha, m₀, hm₀, he⟩ := hm
  cases he
  refine ⟨ma, ha, mi', ?_, rfl⟩
  simp only [Silmaril.Wasm.Execution.Core.Store.setMem]
  rw [List.getElem?_set_self]
  exact (List.getElem?_eq_some_iff.mp hm₀).1

theorem fill_setMem_self {cs : CStore H} {cf : CFrame} {x : Silmaril.Wasm.MemIdx} {ma : Nat}
    {mi : Silmaril.Wasm.Execution.Core.MemInst} (hm : cs.mem? cf x = some (ma, mi)) :
    cs.setMem ma mi = cs := by
  simp only [Silmaril.Wasm.Execution.Core.Store.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hm
  obtain ⟨a', _, m₀, hm₀, he⟩ := hm
  cases he
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hm₀
  simp only [Silmaril.Wasm.Execution.Core.Store.setMem]
  rw [← heq, List.set_getElem_self hlt]

theorem fill_setMem_setMem (cs : CStore H) (ma : Nat) (m₁ m₂ : Silmaril.Wasm.Execution.Core.MemInst) :
    (cs.setMem ma m₁).setMem ma m₂ = cs.setMem ma m₂ := by
  simp [Silmaril.Wasm.Execution.Core.Store.setMem]

theorem fill_uint8_setWidth (b : BitVec 32) :
    UInt8.ofNat (b.setWidth 8).toNat = UInt8.ofNat b.toNat := by
  apply UInt8.toNat.inj
  simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]

/-- The Core `memory.fill` loop, by induction on the count. -/
theorem fill_loop {tgt : CHostSemantics H} (x : Silmaril.Wasm.MemIdx) (b : BitVec 32) :
    ∀ (k : Nat) (cs : CStore H) (cf : CFrame) (ma : Nat) (mi : Silmaril.Wasm.Execution.Core.MemInst)
      (i n : BitVec 32), cs.mem? cf x = some (ma, mi) → n.toNat = k →
      i.toNat + k ≤ mi.bytes.size → mi.bytes.size ≤ 2 ^ 32 →
      ∃ B : ByteArray, B.size = mi.bytes.size ∧
        (∀ j, B.data[j]? = if i.toNat ≤ j ∧ j < i.toNat + k then some (UInt8.ofNat b.toNat)
          else mi.bytes.data[j]?) ∧
        Relation.TransGen (Silmaril.Wasm.Execution.Core.Step
            Silmaril.Wasm.Numerics.Profile.spec tgt)
          ⟨cs, cf, [Silmaril.Wasm.Execution.Core.aconst .i32 i,
            Silmaril.Wasm.Execution.Core.aconst .i32 b,
            Silmaril.Wasm.Execution.Core.aconst .i32 n,
            .plain (.memoryFill x)]⟩
          ⟨cs.setMem ma { mi with bytes := B }, cf, []⟩ := by
  intro k
  induction k with
  | zero =>
    intro cs cf ma mi i n hm hn hle _
    have hn0 : n = 0 := by
      apply BitVec.eq_of_toNat_eq; simpa using hn
    subst hn0
    refine ⟨mi.bytes, rfl, fun j => by simp, ?_⟩
    rw [show ({ mi with bytes := mi.bytes } : Silmaril.Wasm.Execution.Core.MemInst) = mi from rfl,
      fill_setMem_self hm]
    exact .single (.memory (.fillZero (a := .i32) (i := i)
      (v := .num ⟨.int .i32, b⟩) hm hle))
  | succ k ih =>
    intro cs cf ma mi i n hm hn hle hsz
    have hn0 : n ≠ 0 := by
      intro h; subst h; simp at hn
    have h2 : i.toNat + n.toNat ≤ mi.bytes.size := by omega
    have hi1 : i.toNat + 1 ≤ mi.bytes.size := by omega
    obtain ⟨A, hA, hAsz, hAget⟩ := bulk_store8 (b.setWidth 8) hi1
    -- recursive call
    have hm' := fill_mem?_setMem hm { mi with bytes := A }
    have hn' : (n - 1).toNat = k := by
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]; simp; omega)]
      simp; omega
    have hi' : (i + 1).toNat ≤ i.toNat + 1 := by
      rw [BitVec.toNat_add]; exact Nat.mod_le _ _ |>.trans (by simp)
    have hcase : k = 0 ∨ (i + 1).toNat = i.toNat + 1 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact .inl hk
      · right; simp [BitVec.toNat_add]; omega
    have hle' : (i + 1).toNat + k ≤ A.size := by
      rw [hAsz]; omega
    obtain ⟨B, hBsz, hBget, hsteps⟩ := ih _ cf ma { mi with bytes := A } (i + 1) (n - 1) hm' hn'
      hle' (by rw [hAsz]; exact hsz)
    refine ⟨B, by rw [hBsz]; exact hAsz, ?_, ?_⟩
    · intro j
      rw [hBget j]
      simp only [hAget j]
      split_ifs <;> first | omega | rfl | (congr 1; exact fill_uint8_setWidth b)
    · refine .head (.memory (.fillSucc (a := .i32) (i := i) (n := n)
        (v := .num ⟨.int .i32, b⟩) hm h2 hn0)) ?_
      have hst : Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt
          ⟨cs, cf, [Silmaril.Wasm.Execution.Core.aconst .i32 i,
            Silmaril.Wasm.Execution.Core.aconst .i32 b, Silmaril.Wasm.Execution.Core.store8 x]⟩
          ⟨cs.setMem ma { mi with bytes := A }, cf, []⟩ :=
        .memory (.storePackVal (t := .i32) (sz := .i8) (a := .i32) (i := i) (c := b) hm
          hA)
      have hctx := Silmaril.Wasm.Execution.Core.Step.ctxtInstrs (vs := [])
        (rest := [Silmaril.Wasm.Execution.Core.aconst .i32 (show BitVec 32 from i + 1),
          Silmaril.Wasm.Execution.Core.aconst .i32 b,
          Silmaril.Wasm.Execution.Core.aconst .i32 (show BitVec 32 from n - 1), .plain (.memoryFill x)])
        hst (.inr (by simp))
      simp only [Silmaril.Wasm.Execution.Core.vals, List.map_nil, List.nil_append,
        List.cons_append] at hctx
      refine .head hctx ?_
      rw [fill_setMem_setMem] at hsteps
      exact hsteps

theorem memoryFill {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame}
    {d byte n : BitVec 32} {a : MemAddr} {m : MemInst} {bytes : Memory.Bytes}
    (memory : frameMemory s f = some (a, m))
    (filled : Memory.fill m.data d.toNat (UInt8.ofNat byte.toNat) n.toNat = some bytes)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 d), value (.int .i32 byte), value (.int .i32 n),
      .source .memoryFill]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, []⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_value _ _)
      (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _)
        (mem_rigid_nil _)))))
  have hm := mem_lookup hE hF memory
  have hwfm := mem_frameMemory_wf hwf.1 memory
  have hsize : bytes.size = m.data.size := Memory.writeBytes_size _ _ _ _ filled
  have hle : d.toNat + n.toNat ≤ m.data.size := by
    have h := (bulk_fill_none (M := m.data) (d := d.toNat) (n := n.toNat)
      (b := UInt8.ofNat byte.toNat)).not.mp (by rw [filled]; simp)
    omega
  obtain ⟨B, hBsz, hBget, hsteps⟩ := fill_loop (tgt := tgt) ⟨0⟩ byte n.toNat cfg.store cfg.frame
    a.value m.toCore d n hm rfl hle hwfm.1
  have hB : B = bytes := bulk_ext fun j => by
    rw [hBget j, bulk_fill_get filled j]; rfl
  subst hB
  refine ⟨⟨cfg.store.setMem a.value ({ m with data := B } : MemInst).toCore, cfg.frame,
    Admin.listToCore (setMemory s a { m with data := B }) []⟩, ?_,
    mem_sim_mk (mem_erase_setMem hE a _) hF
      ⟨mem_storeWF_set hwf.1 memory (by rw [hsize]; exact hwfm.1) rfl, hwf.2.1, trivial⟩⟩
  rw [hc, ← mem_toCore_bytes m B hsize]
  exact hsteps

theorem memoryFillTrap {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame}
    {d byte n : BitVec 32} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (filled : Memory.fill m.data d.toNat (UInt8.ofNat byte.toNat) n.toNat = none)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 d), value (.int .i32 byte), value (.int .i32 n),
      .source .memoryFill]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_value _ _)
      (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _)
        (mem_rigid_nil _)))))
  have hm := mem_lookup hE hF memory
  have hlt := bulk_fill_none.mp filled
  refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [.trap]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, trivial, trivial⟩⟩
  rw [hc]
  exact .single (.memory (.fillOob (a := .i32) (i := d) (n := n)
    (v := .num ⟨.int .i32, byte⟩) hm hlt))

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
