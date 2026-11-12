module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Runtime
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Lime1 → Core step simulation: memory access head rules

For each Lime1 memory `Step` constructor `K` (loads, stores, `memory.size`,
`memory.grow`), `ToCoreSim.K` shows that a Core configuration related by `Sim` to
the redex takes one Core `MemoryStep` to a configuration related to the reduct.

The Lime1 memory image is `MemInst.toCore` (bytes unchanged, `i32` addresses,
minimum = current page count). Byte-level loads/stores are the shared
`Execution.Memory.load`/`store`, so only bounds and widths need relating.
`StoreWF` supplies `data.size ≤ 2^32` and the `Fin (2^64)` bound on maxima,
and is re-established after stores (size preserved) and growth. -/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution.ToCore

variable {H : Type}

/-! ## Helpers -/

theorem mem_sim_inv {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cfg : CConfig H}
    (hs : Sim ⟨s, f, code⟩ cfg) (hr : ∀ y ∈ Admin.listToCore s code, Rigid y) :
    cfg = ⟨cfg.store, cfg.frame, Admin.listToCore s code⟩ ∧
      ToCore.Store.erase cfg.store = s.toCore ∧ ToCore.Frame.erase cfg.frame = f.toCore ∧
      ConfigWF (⟨s, f, code⟩ : Silmaril.Wasm.Execution.Runtime.Config H) := by
  obtain ⟨hn, hwf⟩ := hs
  obtain ⟨cs, cf, cl⟩ := cfg
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨?_, h1, h2, hwf⟩
  have := map_norm_eq_of_rigid (L := Admin.listToCore s code) hr h3
  rw [this]

theorem mem_sim_mk {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    (hE : ToCore.Store.erase cs = s.toCore) (hF : ToCore.Frame.erase cf = f.toCore)
    (hwf : ConfigWF (⟨s, f, code⟩ : Silmaril.Wasm.Execution.Runtime.Config H)) :
    Sim ⟨s, f, code⟩ ⟨cs, cf, Admin.listToCore s code⟩ :=
  ⟨ToCore.Config.norm_eq_toCore_iff.mpr ⟨hE, hF, map_norm_listToCore _ _ _⟩, hwf⟩

theorem mem_rigid_value (s : Silmaril.Wasm.Execution.Runtime.Store H) (v : Value) :
    ∀ y ∈ Admin.toCore s (value v), Rigid y := by
  rw [value_toCore]; intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact Rigid.val _

theorem mem_rigid_source (s : Silmaril.Wasm.Execution.Runtime.Store H) (i : Instr) :
    ∀ y ∈ Admin.toCore s (.source i), Rigid y := by
  rw [source_toCore]; intro y hy; simp only [List.mem_singleton] at hy; subst hy
  exact Rigid.toCore _

theorem mem_rigid_cons {s : Silmaril.Wasm.Execution.Runtime.Store H} {a : Admin} {l : List Admin}
    (h₁ : ∀ y ∈ Admin.toCore s a, Rigid y) (h₂ : ∀ y ∈ Admin.listToCore s l, Rigid y) :
    ∀ y ∈ Admin.listToCore s (a :: l), Rigid y := by
  rw [listToCore_cons]; intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact h₁ y h
  · exact h₂ y h

theorem mem_rigid_nil (s : Silmaril.Wasm.Execution.Runtime.Store H) : ∀ y ∈ Admin.listToCore s [], Rigid y := by simp

theorem mem_wf_value (s : Silmaril.Wasm.Execution.Runtime.Store H) (v : Value) : Admin.WF s (value v) := by
  rcases v with ⟨_ | _, _⟩ <;> simp [value, Admin.WF]

theorem mem_lookup {cs : CStore H} {cf : CFrame} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {a : MemAddr}
    {m : MemInst} (hE : ToCore.Store.erase cs = s.toCore) (hF : ToCore.Frame.erase cf = f.toCore)
    (hm : frameMemory s f = some (a, m)) :
    cs.mem? cf ⟨0⟩ = some (a.value, m.toCore) := by
  have h1 : cs.mems = s.memories.map MemInst.toCore := by
    have := congrArg Silmaril.Wasm.Execution.Core.Store.mems hE
    simpa [ToCore.Store.erase, Runtime.Store.toCore] using this
  have h2 : cf.module.mems = f.module.memories.map Addr.value := by
    have := congrArg (fun fr : CFrame => fr.module.mems) hF
    simpa [ToCore.Frame.erase, ToCore.ModuleInst.erase, Runtime.Frame.toCore,
      Runtime.ModuleInst.toCore] using this
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hm
  obtain ⟨a', ha, m', hm', he⟩ := hm
  cases he
  simp [Silmaril.Wasm.Execution.Core.Store.mem?, h1, h2, ha, hm', Silmaril.Wasm.Idx.toNat]

theorem mem_erase_setMem {cs : CStore H} {s : Silmaril.Wasm.Execution.Runtime.Store H} (hE : ToCore.Store.erase cs = s.toCore)
    (a : MemAddr) (m' : MemInst) :
    ToCore.Store.erase (cs.setMem a.value m'.toCore) = (setMemory s a m').toCore := by
  have : ToCore.Store.erase (cs.setMem a.value m'.toCore) =
      (ToCore.Store.erase cs).setMem a.value m'.toCore := rfl
  rw [this, hE]
  simp [Silmaril.Wasm.Execution.Core.Store.setMem, Runtime.Store.toCore, setMemory, List.map_set]

theorem mem_toCore_bytes (m : MemInst) (b : ByteArray) (h : b.size = m.data.size) :
    ({ m.toCore with bytes := b } : Silmaril.Wasm.Execution.Core.MemInst) =
      ({ m with data := b } : MemInst).toCore := by
  simp [MemInst.toCore, h]

theorem mem_storeWF_set {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {a : MemAddr} {m m' : MemInst}
    (hwf : StoreWF s) (hm : frameMemory s f = some (a, m)) (hsize : m'.data.size ≤ 2 ^ 32)
    (hmax : m'.max = m.max) : StoreWF (setMemory s a m') := by
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hm
  obtain ⟨a', _, m₀, hm₀, he⟩ := hm
  cases he
  refine ⟨fun i t mod c h => hwf.1 i t mod c h, fun i mi h => ?_⟩
  simp only [setMemory, List.getElem?_set] at h
  by_cases hi : a.value = i
  · subst hi
    simp only [↓reduceIte] at h
    split at h
    · cases h; refine ⟨hsize, ?_⟩; rw [hmax]; exact (hwf.2 _ _ hm₀).2
    · cases h
  · rw [ite_eq_right hi] at h; exact hwf.2 i mi h

theorem mem_setMemory_self {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (hm : frameMemory s f = some (a, m)) : setMemory s a m = s := by
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hm
  obtain ⟨a', _, m₀, hm₀, he⟩ := hm
  cases he
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hm₀
  simp only [setMemory]
  rw [← heq, List.set_getElem_self hlt]

theorem mem_load_none {data : ByteArray} {start count : Nat}
    (h : Memory.load data start count = none) : data.size < start + count := by
  simp only [Memory.load, Memory.readBytes, Option.map_eq_none_iff, ite_eq_right_iff,
    reduceCtorEq, imp_false] at h
  omega

theorem mem_store_none {data : ByteArray} {start count : Nat} {w : BitVec (8 * count)}
    (h : Memory.store data start w = none) : data.size < start + count := by
  simp only [Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_right_iff,
    reduceCtorEq, imp_false] at h
  omega

theorem mem_store_size {data b : ByteArray} {start count : Nat} {w : BitVec (8 * count)}
    (h : Memory.store data start w = some b) : b.size = data.size :=
  Memory.writeBytes_size _ _ _ _ h

theorem mem_frameMemory_wf {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (hwf : StoreWF s) (hm : frameMemory s f = some (a, m)) :
    m.data.size ≤ 2 ^ 32 ∧ ∀ j, m.max = some j → j < 2 ^ 64 := by
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hm
  obtain ⟨a', _, m₀, hm₀, he⟩ := hm
  cases he
  exact hwf.2 _ _ hm₀

theorem mem_grow_toCore (m : MemInst) (delta : Nat) (bytes : ByteArray)
    (h : Memory.grow? m.data m.max delta = some bytes) (hmax : ∀ j, m.max = some j → j < 2 ^ 64) :
    m.toCore.grow? delta = some ({ m with data := bytes } : MemInst).toCore ∧
      bytes.size ≤ 2 ^ 32 := by
  unfold Memory.grow? at h
  split_ifs at h with hc
  cases h
  obtain ⟨hmod, hle, hmx⟩ := hc
  have hsz : (m.data ++ ⟨Array.replicate (delta * Memory.pageSize) 0⟩).size =
      m.data.size + delta * Memory.pageSize := by
    rw [ByteArray.size_append]
    show m.data.size + (Array.replicate (delta * Memory.pageSize) (0 : UInt8)).size = _
    rw [Array.size_replicate]
  have hk : m.data.size = m.data.size / Memory.pageSize * Memory.pageSize :=
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)).symm
  have hdiv : (m.data.size + delta * Memory.pageSize) / Memory.pageSize =
      m.data.size / Memory.pageSize + delta := by
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < Memory.pageSize)]
  unfold Memory.size at hle hmx
  refine ⟨?_, ?_⟩
  · unfold Silmaril.Wasm.Execution.Core.MemInst.grow? MemInst.toCore
    rw [ite_eq_left]
    · simp only [hsz, hdiv]
    · refine ⟨?_, ?_⟩
      · refine le_of_le_of_eq (by simpa [Memory.maxPages] using hle) ?_
        rfl
      · intro j hj
        rcases hmm : m.max with _ | j₀
        · simp [hmm] at hj
        · simp only [hmm, Option.map_some, Option.some.injEq] at hj
          subst hj
          have := hmax j₀ hmm
          simp only [hmm, Option.isNone_some, Bool.false_eq_true, Option.getD_some,
            false_or] at hmx
          have this' : j₀ < 18446744073709551616 := by simpa using this
          simp only [Fin.val_ofNat, Nat.mod_eq_of_lt this']
          exact hmx
  · rw [hsz]
    have : m.data.size / Memory.pageSize * Memory.pageSize + delta * Memory.pageSize ≤
        Memory.maxPages * Memory.pageSize := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hle
    rw [← hk] at this
    simpa [Memory.maxPages, Memory.pageSize] using this

/-! ## Loads -/

theorem intLoad {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {t} {packed} {arg} {c : BitVec 32}
    {a : MemAddr} {m : MemInst} {v : Value}
    (memory : frameMemory s f = some (a, m))
    (loaded : loadInt t packed m.data (effectiveAddress c arg) = some v)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [value v]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _)))
  have hm := mem_lookup hE hF memory
  refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [value v]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, mem_wf_value _ _, trivial⟩⟩
  rw [hc]
  rcases packed with _ | ⟨p, sx⟩
  · simp only [loadInt, Option.map_eq_some_iff] at loaded
    obtain ⟨x, hx, rfl⟩ := loaded
    exact .single (.memory (.loadIntVal (a := .i32) (i := c) hm hx))
  · simp only [loadInt, Option.map_eq_some_iff] at loaded
    obtain ⟨x, hx, rfl⟩ := loaded
    cases p <;> cases sx <;>
      exact .single (.memory (.loadPackVal (a := .i32) (i := c) hm hx))

theorem intLoadTrap {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {t} {packed} {arg}
    {c : BitVec 32} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (loaded : loadInt t packed m.data (effectiveAddress c arg) = none)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _)))
  have hm := mem_lookup hE hF memory
  refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [.trap]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, trivial, trivial⟩⟩
  rw [hc]
  rcases packed with _ | ⟨p, sx⟩
  · simp only [loadInt, Option.map_eq_none_iff] at loaded
    exact .single (.memory (.loadIntOob (a := .i32) (i := c) hm (mem_load_none loaded)))
  · simp only [loadInt, Option.map_eq_none_iff] at loaded
    cases p <;>
      exact .single (.memory (.loadPackOob (a := .i32) (i := c) hm (mem_load_none loaded)))

theorem floatLoad {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {t} {arg} {c : BitVec 32}
    {a : MemAddr} {m : MemInst} {v : Value}
    (memory : frameMemory s f = some (a, m))
    (loaded : loadFloat t m.data (effectiveAddress c arg) = some v)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [value v]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _)))
  have hm := mem_lookup hE hF memory
  refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [value v]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, mem_wf_value _ _, trivial⟩⟩
  rw [hc]
  simp only [loadFloat, Option.map_eq_some_iff] at loaded
  obtain ⟨x, hx, rfl⟩ := loaded
  exact .single (.memory (.loadFloatVal (a := .i32) (i := c) hm hx))

theorem floatLoadTrap {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {t} {arg}
    {c : BitVec 32} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (loaded : loadFloat t m.data (effectiveAddress c arg) = none)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _)))
  have hm := mem_lookup hE hF memory
  refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [.trap]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, trivial, trivial⟩⟩
  rw [hc]
  simp only [loadFloat, Option.map_eq_none_iff] at loaded
  exact .single (.memory (.loadFloatOob (a := .i32) (i := c) hm (mem_load_none loaded)))

/-! ## Stores -/

theorem intStore {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {t} {packed} {arg}
    {c : BitVec 32} {x : BitVec t.width} {a : MemAddr} {m : MemInst} {bytes : Memory.Bytes}
    (memory : frameMemory s f = some (a, m))
    (stored : storeInt t packed m.data (effectiveAddress c arg) x = some bytes)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t packed arg)]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, []⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_value _ _)
      (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _))))
  have hm := mem_lookup hE hF memory
  have hsize : bytes.size = m.data.size := mem_store_size stored
  have hwfm := mem_frameMemory_wf hwf.1 memory
  refine ⟨⟨cfg.store.setMem a.value ({ m with data := bytes } : MemInst).toCore, cfg.frame,
    Admin.listToCore (setMemory s a { m with data := bytes }) []⟩, ?_,
    mem_sim_mk (mem_erase_setMem hE a _) hF
      ⟨mem_storeWF_set hwf.1 memory (by rw [hsize]; exact hwfm.1) rfl, hwf.2.1, trivial⟩⟩
  rw [hc, ← mem_toCore_bytes m bytes hsize]
  rcases packed with _ | p
  · exact .single (.memory (.storeIntVal (a := .i32) (i := c) hm stored))
  · cases p <;> exact .single (.memory (.storePackVal (a := .i32) (i := c) hm stored))

theorem intStoreTrap {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {t} {packed} {arg}
    {c : BitVec 32} {x : BitVec t.width} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (stored : storeInt t packed m.data (effectiveAddress c arg) x = none)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t packed arg)]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_value _ _)
      (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _))))
  have hm := mem_lookup hE hF memory
  refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [.trap]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, trivial, trivial⟩⟩
  rw [hc]
  rcases packed with _ | p
  · exact .single (.memory (.storeIntOob (a := .i32) (i := c) hm (mem_store_none stored)))
  · cases p <;>
      exact .single (.memory (.storePackOob (a := .i32) (i := c) hm (mem_store_none stored)))

theorem floatStore {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {t} {arg}
    {c : BitVec 32} {x : BitVec t.width} {a : MemAddr} {m : MemInst} {bytes : Memory.Bytes}
    (memory : frameMemory s f = some (a, m))
    (stored : storeFloat t m.data (effectiveAddress c arg) x = some bytes)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, []⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_value _ _)
      (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _))))
  have hm := mem_lookup hE hF memory
  have hsize : bytes.size = m.data.size := mem_store_size stored
  have hwfm := mem_frameMemory_wf hwf.1 memory
  refine ⟨⟨cfg.store.setMem a.value ({ m with data := bytes } : MemInst).toCore, cfg.frame,
    Admin.listToCore (setMemory s a { m with data := bytes }) []⟩, ?_,
    mem_sim_mk (mem_erase_setMem hE a _) hF
      ⟨mem_storeWF_set hwf.1 memory (by rw [hsize]; exact hwfm.1) rfl, hwf.2.1, trivial⟩⟩
  rw [hc, ← mem_toCore_bytes m bytes hsize]
  exact .single (.memory (.storeFloatVal (a := .i32) (i := c) hm stored))

theorem floatStoreTrap {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {t} {arg}
    {c : BitVec 32} {x : BitVec t.width} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (stored : storeFloat t m.data (effectiveAddress c arg) x = none)
    {cfg : CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_value _ _)
      (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _))))
  have hm := mem_lookup hE hF memory
  refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [.trap]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, trivial, trivial⟩⟩
  rw [hc]
  exact .single (.memory (.storeFloatOob (a := .i32) (i := c) hm (mem_store_none stored)))

/-! ## Size and growth -/

theorem memorySize {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {a : MemAddr}
    {m : MemInst} (memory : frameMemory s f = some (a, m))
    {cfg : CConfig H} (hs : Sim ⟨s, f, [.source .memorySize]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨s, f, [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _))
  have hm := mem_lookup hE hF memory
  refine ⟨⟨cfg.store, cfg.frame,
      Admin.listToCore s [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩, ?_,
    mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, mem_wf_value _ _, trivial⟩⟩
  rw [hc]
  exact .single (.memory (.size hm))

theorem memoryGrow {tgt : CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {a : MemAddr}
    {m : MemInst} {c r : BitVec 32} {bytes : Memory.Bytes}
    (memory : frameMemory s f = some (a, m))
    (grown : Memory.Grow m.data m.max c.toNat bytes r)
    {cfg : CConfig H} (hs : Sim ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩ cfg) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Silmaril.Wasm.Numerics.Profile.spec tgt) cfg c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, [value (.int .i32 r)]⟩ c' := by
  obtain ⟨hc, hE, hF, hwf⟩ := mem_sim_inv hs
    (mem_rigid_cons (mem_rigid_value _ _) (mem_rigid_cons (mem_rigid_source _ _) (mem_rigid_nil _)))
  have hm := mem_lookup hE hF memory
  have hwfm := mem_frameMemory_wf hwf.1 memory
  cases grown with
  | success _ hg =>
    obtain ⟨hgC, hsz⟩ := mem_grow_toCore m _ _ hg hwfm.2
    refine ⟨⟨cfg.store.setMem a.value ({ m with data := bytes } : MemInst).toCore, cfg.frame,
      Admin.listToCore (setMemory s a { m with data := bytes })
        [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩, ?_,
      mem_sim_mk (mem_erase_setMem hE a _) hF
        ⟨mem_storeWF_set hwf.1 memory hsz rfl, hwf.2.1, mem_wf_value _ _, trivial⟩⟩
    rw [hc]
    exact .single (.memory (.growSucceed (a := .i32) (n := c) hm hgC trivial))
  | failure =>
    rw [show ({ m with data := m.data } : MemInst) = m from rfl, mem_setMemory_self memory]
    have h1 : (-1 : BitVec 32) = BitVec.allOnes 32 := by decide
    rw [h1]
    refine ⟨⟨cfg.store, cfg.frame, Admin.listToCore s [value (.int .i32 (BitVec.allOnes 32))]⟩, ?_,
      mem_sim_mk hE hF ⟨hwf.1, hwf.2.1, mem_wf_value _ _, trivial⟩⟩
    rw [hc]
    exact .single (.memory (.growFail (a := .i32) (n := c) hm (.inl trivial)))

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
