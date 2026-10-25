module

public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping

@[expose] public section

/-! # Soundness, memory family

Preservation of `MemoryStep` (the frame is unchanged; the store is extended and
stays valid) and progress for `MemoryInstrOk`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Inversion of memory-instruction typing -/

/-- The memory-family instructions. -/
def _root_.Silmaril.Wasm.Instr.IsMemI : Instr → Prop
  | .memorySize _ | .memoryGrow _ | .memoryFill _ | .memoryCopy _ _ | .memoryInit _ _
  | .dataDrop _ | .intLoad _ _ _ _ | .floatLoad _ _ _ | .intStore _ _ _ _ | .floatStore _ _ _
  | .vecLoad _ _ _ | .vecLoadLane _ _ _ _ | .vecStore _ _ | .vecStoreLane _ _ _ _ => True
  | _ => False

/-- The number of operands of a memory-family instruction. -/
def _root_.Silmaril.Wasm.Instr.memArity : Instr → Nat
  | .memoryGrow _ | .intLoad _ _ _ _ | .floatLoad _ _ _ | .vecLoad _ _ _ => 1
  | .intStore _ _ _ _ | .floatStore _ _ _ | .vecLoadLane _ _ _ _ | .vecStore _ _
  | .vecStoreLane _ _ _ _ => 2
  | .memoryFill _ | .memoryCopy _ _ | .memoryInit _ _ => 3
  | _ => 0

theorem _root_.Silmaril.Wasm.Validation.InstrOk.memory_inv {C : Context} {i : Instr}
    {it : InstrType} (h : InstrOk C i it) (hi : i.IsMemI) : MemoryInstrOk C i it := by
  cases h <;> first
    | assumption
    | (rename_i h'; cases h' <;> simp [Instr.IsMemI] at hi)
    | simp [Instr.IsMemI] at hi

theorem _root_.Silmaril.Wasm.Validation.MemoryInstrOk.hi {C : Context} {i : Instr}
    {it : InstrType} (h : MemoryInstrOk C i it) :
    it.inits = [] ∧ it.params.length = i.memArity ∧ ResultOk {} it.params := by
  cases h <;> exact ⟨rfl, rfl, by rok⟩

theorem memHi {C : Context} {i : Instr} (hti : i.IsMemI) {vs : List Val}
    (hlen : vs.length = i.memArity) :
    ∀ it₀, InstrOk C i it₀ →
      it₀.inits = [] ∧ it₀.params.length = vs.length ∧ ResultOk {} it₀.params := by
  intro it₀ h
  obtain ⟨h₁, h₂, h₃⟩ := (h.memory_inv hti).hi
  exact ⟨h₁, h₂.trans hlen.symm, h₃⟩

theorem StateOk.mem_ctx {s : Store H} {f : Frame} {C : Context} {x : MemIdx}
    {a : AddrType} {l : Limits} {ma : Nat} {mi : MemInst}
    (hst : StateOk s f C) (hx : C.mems[x.toNat]? = some ⟨a, l⟩)
    (hm : s.mem? f x = some (ma, mi)) :
    mi.type.address = a ∧ MemInstOk mi ∧ s.mems[ma]? = some mi := by
  obtain ⟨ma', mi', hm', h₁, h₂⟩ := hst.mem hx
  rw [hm] at hm'
  cases hm'
  exact ⟨h₁, h₂, (Store.mem?_spec hm).2⟩

theorem memarg0_ok (a : AddrType) {N : Nat} (hN : 8 ≤ N) : MemArgOk memarg0 a N := by
  refine ⟨?_, ?_⟩
  · simp only [memarg0]
    show 1 ≤ N / 8
    omega
  · simp only [memarg0]
    exact Nat.pow_pos (by decide)

theorem instrOk_store8 {C : Context} {x : MemIdx} {a : AddrType} {l : Limits}
    (hx : C.mems[x.toNat]? = some ⟨a, l⟩) :
    InstrOk C (.intStore .i32 (some .i8) x memarg0) ⟨[a.valType, Ty.i32], [], []⟩ :=
  .memory (.intStorePack hx (by decide) (memarg0_ok a (by decide)))

theorem instrOk_load8u {C : Context} {x : MemIdx} {a : AddrType} {l : Limits}
    (hx : C.mems[x.toNat]? = some ⟨a, l⟩) :
    InstrOk C (.intLoad .i32 (some (.i8, .unsigned)) x memarg0) ⟨[a.valType], [], [Ty.i32]⟩ :=
  .memory (.intLoadPack hx (by decide) (memarg0_ok a (by decide)))

theorem MemInstOk.store {mi : MemInst} {b : ByteArray} {start count : Nat}
    {word : BitVec (8 * count)} (hok : MemInstOk mi)
    (hs : Memory.store mi.bytes start word = some b) :
    MemInstOk { mi with bytes := b } ∧ ExtendMem mi { mi with bytes := b } := by
  have hsz := Memory.store_size hs
  exact ⟨⟨hok.1, hsz.trans hok.2⟩, ⟨rfl, rfl, Nat.le_refl _, by simp [hsz]⟩⟩

/-- **Preservation (memory).** -/
theorem MemoryStep.preservation {P : Profile} {c c' : Config H} {C : Context} {it : InstrType}
    (hst : StateOk c.store c.frame C) (hty : AdminsOk c.store C c.code it)
    (h : MemoryStep P c c') :
    c'.frame = c.frame ∧ StoreOk c'.store ∧ Extend c.store c'.store ∧
      AdminsOk c'.store C c'.code it := by
  have hs := hst.1
  cases h with
  | @loadIntOob s f t x arg a i ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | intLoad hx hma => exact SeqOk.trap (by rok)
  | @loadIntVal s f t x arg a i ma mi c hm hl =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | intLoad hx hma => exact SeqOk.v (v := .num ⟨.int t, _⟩) SeqOk.nil (.num _) (.num _)
  | @loadPackOob s f t sz sx x arg a i ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | intLoadPack hx hsz hma => exact SeqOk.trap (by rok)
  | @loadPackVal s f t sz sx x arg a i ma mi c hm hl =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | intLoadPack hx hsz hma => exact SeqOk.v (v := .num ⟨.int t, _⟩) SeqOk.nil (.num _) (.num _)
  | @loadFloatOob s f t x arg a i ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | floatLoad hx hma => exact SeqOk.trap (by rok)
  | @loadFloatVal s f t x arg a i ma mi c hm hl =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | floatLoad hx hma => exact SeqOk.v (v := .num ⟨.float t, _⟩) SeqOk.nil (.num _) (.num _)
  | @vecLoadOob s f op x arg a i ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | vecLoad hx hma => exact SeqOk.trap (by rok)
  | @vecLoadVal s f op x arg a i ma mi c hm hl =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | vecLoad hx hma => exact SeqOk.v (v := .vec _) SeqOk.nil (.vec _) (.vec _)
  | @vecLoadLaneOob s f sz x arg j a i v ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, .vec v]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | vecLoadLane hx hma hj => exact SeqOk.trap (by rok)
  | @vecLoadLaneVal s f sz x arg j a i v ma mi k hm hl =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, .vec v]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | vecLoadLane hx hma hj => exact SeqOk.v (v := .vec _) SeqOk.nil (.vec _) (.vec _)
  | @storeIntOob s f t x arg a i c ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | intStore hx hma => exact SeqOk.trap resultOk_nil
  | @storeIntVal s f t x arg a i c ma mi b hm hsto =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv
      (vs := [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩]) hst (memHi (by trivial) (by rfl)) hty
    cases hi.memory_inv trivial with
    | intStore hx hma =>
      obtain ⟨-, hmok, hget⟩ := hst.mem_ctx hx hm
      obtain ⟨hok', hx'⟩ := MemInstOk.store hmok hsto
      obtain ⟨hs', he⟩ := StoreOk.setMem hs hget hx' hok'
      exact ⟨rfl, hs', he, hk _ _ SeqOk.nil⟩
  | @storePackOob s f t sz x arg a i c ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | intStorePack hx hsz hma => exact SeqOk.trap resultOk_nil
  | @storePackVal s f t sz x arg a i c ma mi b hm hsto =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv
      (vs := [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩]) hst (memHi (by trivial) (by rfl)) hty
    cases hi.memory_inv trivial with
    | intStorePack hx hsz hma =>
      obtain ⟨-, hmok, hget⟩ := hst.mem_ctx hx hm
      obtain ⟨hok', hx'⟩ := MemInstOk.store hmok hsto
      obtain ⟨hs', he⟩ := StoreOk.setMem hs hget hx' hok'
      exact ⟨rfl, hs', he, hk _ _ SeqOk.nil⟩
  | @storeFloatOob s f t x arg a i c ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, .num ⟨.float t, c⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | floatStore hx hma => exact SeqOk.trap resultOk_nil
  | @storeFloatVal s f t x arg a i c ma mi b hm hsto =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv
      (vs := [.num ⟨.int a.intType, i⟩, .num ⟨.float t, c⟩]) hst (memHi (by trivial) (by rfl)) hty
    cases hi.memory_inv trivial with
    | floatStore hx hma =>
      obtain ⟨-, hmok, hget⟩ := hst.mem_ctx hx hm
      obtain ⟨hok', hx'⟩ := MemInstOk.store hmok hsto
      obtain ⟨hs', he⟩ := StoreOk.setMem hs hget hx' hok'
      exact ⟨rfl, hs', he, hk _ _ SeqOk.nil⟩
  | @vecStoreOob s f x arg a i c ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, .vec c]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | vecStore hx hma => exact SeqOk.trap resultOk_nil
  | @vecStoreVal s f x arg a i c ma mi b hm hsto =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv
      (vs := [.num ⟨.int a.intType, i⟩, .vec c]) hst (memHi (by trivial) (by rfl)) hty
    cases hi.memory_inv trivial with
    | vecStore hx hma =>
      obtain ⟨-, hmok, hget⟩ := hst.mem_ctx hx hm
      obtain ⟨hok', hx'⟩ := MemInstOk.store hmok hsto
      obtain ⟨hs', he⟩ := StoreOk.setMem hs hget hx' hok'
      exact ⟨rfl, hs', he, hk _ _ SeqOk.nil⟩
  | @vecStoreLaneOob s f sz x arg j a i c ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, .vec c]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | vecStoreLane hx hma hj => exact SeqOk.trap resultOk_nil
  | @vecStoreLaneVal s f sz x arg j a i c ma mi b hm hsto =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv
      (vs := [.num ⟨.int a.intType, i⟩, .vec c]) hst (memHi (by trivial) (by rfl)) hty
    cases hi.memory_inv trivial with
    | vecStoreLane hx hma hj =>
      obtain ⟨-, hmok, hget⟩ := hst.mem_ctx hx hm
      obtain ⟨hok', hx'⟩ := MemInstOk.store hmok hsto
      obtain ⟨hs', he⟩ := StoreOk.setMem hs hget hx' hok'
      exact ⟨rfl, hs', he, hk _ _ SeqOk.nil⟩
  | @size s f x ma mi hm =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := []) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memorySize hx =>
      obtain ⟨haddr, -⟩ := hst.mem_ctx hx hm
      subst haddr
      exact SeqOk.addr SeqOk.nil _ _
  | @growSucceed s f x a n ma mi mi' hm hg hp =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv (vs := [.num ⟨.int a.intType, n⟩])
      hst (memHi (by trivial) (by rfl)) hty
    cases hi.memory_inv trivial with
    | memoryGrow hx =>
      obtain ⟨-, hmok, hget⟩ := hst.mem_ctx hx hm
      rcases hvs with _ | ⟨hn, -⟩
      obtain rfl := ValOk.addr_eq hn
      obtain ⟨hok', hx'⟩ := MemInst.grow?_ok hmok hg
      obtain ⟨hs', he⟩ := StoreOk.setMem hs hget hx' hok'
      exact ⟨rfl, hs', he, hk _ _ (SeqOk.addr SeqOk.nil _ _)⟩
  | @growFail s f x a n ma mi hm hp =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, n⟩]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryGrow hx =>
      rcases hvs with _ | ⟨hn, -⟩
      obtain rfl := ValOk.addr_eq hn
      exact SeqOk.addr SeqOk.nil _ _
  | @fillOob s f x a i n v ma mi hm hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, v, .num ⟨.int a.intType, n⟩])
      hst (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryFill hx => exact SeqOk.trap resultOk_nil
  | @fillZero s f x a i v ma mi hm hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, v, .num ⟨.int a.intType, 0⟩])
      hst (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryFill hx => exact SeqOk.nil
  | @fillSucc s f x a i n v ma mi hm hle hn =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, v, .num ⟨.int a.intType, n⟩])
      hst (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryFill hx =>
      rcases hvs with _ | ⟨ha, _ | ⟨hv, _ | ⟨-, -⟩⟩⟩
      obtain rfl := ValOk.addr_eq ha
      have e1 := SeqOk.addr (s := s) (C := C) SeqOk.nil a i
      have e2 := SeqOk.v e1 hv (.num _)
      have e3 := SeqOk.ins [] [a.valType, Ty.i32] e2 (instrOk_store8 hx)
      have e4 := SeqOk.addr e3 a (i + 1)
      have e5 := SeqOk.v e4 hv (.num _)
      have e6 := SeqOk.addr e5 a (n - 1)
      exact SeqOk.ins [] [a.valType, Ty.i32, a.valType] e6 (.memory (.memoryFill hx))
  | @copyOob s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a₁.intType, i₁⟩, .num ⟨.int a₂.intType, i₂⟩,
      .num ⟨.int a'.intType, n⟩]) hst (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryCopy hx₁ hx₂ => exact SeqOk.trap resultOk_nil
  | @copyZero s f x₁ x₂ a₁ a₂ a' i₁ i₂ ma₁ ma₂ mi₁ mi₂ h₁ h₂ hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a₁.intType, i₁⟩, .num ⟨.int a₂.intType, i₂⟩,
      .num ⟨.int a'.intType, 0⟩]) hst (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryCopy hx₁ hx₂ => exact SeqOk.nil
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ hle' hn hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a₁.intType, i₁⟩, .num ⟨.int a₂.intType, i₂⟩,
      .num ⟨.int a'.intType, n⟩]) hst (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryCopy hx₁ hx₂ =>
      rcases hvs with _ | ⟨ha₁, _ | ⟨ha₂, _ | ⟨ha', -⟩⟩⟩
      obtain rfl := ValOk.addr_eq ha₁
      obtain rfl := ValOk.addr_eq ha₂
      obtain rfl := ValOk.addr_eq ha'
      have e1 := SeqOk.addr (s := s) (C := C) SeqOk.nil a₁ i₁
      have e2 := SeqOk.addr e1 a₂ i₂
      have e3 := SeqOk.ins [a₁.valType] [a₂.valType] e2 (instrOk_load8u hx₂)
      have e4 := SeqOk.ins [] [a₁.valType, Ty.i32] e3 (instrOk_store8 hx₁)
      have e5 := SeqOk.addr e4 a₁ (i₁ + 1)
      have e6 := SeqOk.addr e5 a₂ (i₂ + 1)
      have e7 := SeqOk.addr e6 _ (n - 1)
      exact SeqOk.ins [] [a₁.valType, a₂.valType, _] e7 (.memory (.memoryCopy hx₁ hx₂))
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ hle' hn hgt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a₁.intType, i₁⟩, .num ⟨.int a₂.intType, i₂⟩,
      .num ⟨.int a'.intType, n⟩]) hst (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryCopy hx₁ hx₂ =>
      rcases hvs with _ | ⟨ha₁, _ | ⟨ha₂, _ | ⟨ha', -⟩⟩⟩
      obtain rfl := ValOk.addr_eq ha₁
      obtain rfl := ValOk.addr_eq ha₂
      obtain rfl := ValOk.addr_eq ha'
      have e1 := SeqOk.addr (s := s) (C := C) SeqOk.nil a₁ (i₁ + BitVec.ofNat _ n.toNat - 1)
      have e2 := SeqOk.addr e1 a₂ (i₂ + BitVec.ofNat _ n.toNat - 1)
      have e3 := SeqOk.ins [a₁.valType] [a₂.valType] e2 (instrOk_load8u hx₂)
      have e4 := SeqOk.ins [] [a₁.valType, Ty.i32] e3 (instrOk_store8 hx₁)
      have e5 := SeqOk.addr e4 a₁ i₁
      have e6 := SeqOk.addr e5 a₂ i₂
      have e7 := SeqOk.addr e6 _ (n - 1)
      exact SeqOk.ins [] [a₁.valType, a₂.valType, _] e7 (.memory (.memoryCopy hx₁ hx₂))
  | @initOob s f x y a i j n ma da mi di hm hd hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, Val.i32 j, Val.i32 n]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryInit hx hy => exact SeqOk.trap resultOk_nil
  | @initZero s f x y a i j ma da mi di hm hd hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, Val.i32 j, Val.i32 0]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryInit hx hy => exact SeqOk.nil
  | @initSucc s f x y a i j n ma da mi di byte hm hd hle hn hb =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, Val.i32 j, Val.i32 n]) hst
      (memHi (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.memory_inv trivial with
    | memoryInit hx hy =>
      rcases hvs with _ | ⟨ha, -⟩
      obtain rfl := ValOk.addr_eq ha
      have e1 := SeqOk.addr (s := s) (C := C) SeqOk.nil a i
      have e2 := SeqOk.i32 e1 (BitVec.ofNat 32 byte.toNat)
      have e3 := SeqOk.ins [] [a.valType, Ty.i32] e2 (instrOk_store8 hx)
      have e4 := SeqOk.addr e3 a (i + 1)
      have e5 := SeqOk.i32 e4 (j + 1)
      have e6 := SeqOk.i32 e5 (n - 1)
      exact SeqOk.ins [] [a.valType, Ty.i32, Ty.i32] e6 (.memory (.memoryInit hx hy))
  | @dataDrop s f y da di hd =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv (vs := []) hst
      (memHi (by trivial) (by rfl)) hty
    cases hi.memory_inv trivial with
    | dataDrop hy =>
      obtain ⟨hs', he'⟩ := StoreOk.setData_empty (a := da) hs
      exact ⟨rfl, hs', he', hk _ _ SeqOk.nil⟩

/-- **Progress (memory).** -/
theorem MemoryInstrOk.progress {P : Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    {vs : List Val} (hst : StateOk s f C) (hi : MemoryInstrOk C i ⟨t₁, xs, t₂⟩)
    (hvs : List.Forall₂ (ValOk s) vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | memorySize h =>
    obtain ⟨⟩ := hvs
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    exact ⟨_, .memory (.size hm)⟩
  | memoryGrow h =>
    obtain ⟨v, rfl, hv⟩ := forall₂_one hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hf : P.growMayFail .memory ma mi.pages b.toNat
    · exact ⟨_, .memory (.growFail hm (.inl hf))⟩
    · cases hg : mi.grow? b.toNat with
      | none => exact ⟨_, .memory (.growFail hm (.inr hg))⟩
      | some mi' =>
        exact ⟨_, .memory (.growSucceed hm hg (Profile.growMaySucceed_of_not_fail hf))⟩
  | memoryFill h =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨n, hn⟩ := ValOk.addr_inv hv₃
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb, hn]
    by_cases hoob : mi.bytes.size < b.toNat + n.toNat
    · exact ⟨_, .memory (.fillOob hm hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .memory (.fillZero hm (by simp at hoob; omega))⟩
      · exact ⟨_, .memory (.fillSucc hm (by omega) hz)⟩
  | memoryCopy h₁ h₂ =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b₁, hb₁⟩ := ValOk.addr_inv hv₁
    obtain ⟨b₂, hb₂⟩ := ValOk.addr_inv hv₂
    obtain ⟨n, hn⟩ := ValOk.addr_inv hv₃
    obtain ⟨ma₁, mi₁, hm₁, -⟩ := hst.mem h₁
    obtain ⟨ma₂, mi₂, hm₂, -⟩ := hst.mem h₂
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb₁, hb₂, hn]
    by_cases hoob : mi₁.bytes.size < b₁.toNat + n.toNat ∨ mi₂.bytes.size < b₂.toNat + n.toNat
    · exact ⟨_, .memory (.copyOob hm₁ hm₂ hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .memory (.copyZero hm₁ hm₂ (by simp at hoob; omega))⟩
      · by_cases hle : b₁.toNat ≤ b₂.toNat
        · exact ⟨_, .memory (.copyLe hm₁ hm₂ (by omega) hz hle)⟩
        · exact ⟨_, .memory (.copyGt hm₁ hm₂ (by omega) hz (by omega))⟩
  | memoryInit h hd =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨j, hj⟩ := ValOk.i32_inv hv₂
    obtain ⟨n, hn⟩ := ValOk.i32_inv hv₃
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    obtain ⟨da, di, hdi⟩ := hst.data hd
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb, hj, hn]
    by_cases hoob : mi.bytes.size < b.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat
    · exact ⟨_, .memory (.initOob hm hdi hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .memory (.initZero hm hdi (by simp at hoob; omega))⟩
      · have hn0 := BitVec.toNat_ne_zero hz
        have hlt : j.toNat < di.bytes.data.size := by
          have : di.bytes.size = di.bytes.data.size := rfl
          omega
        exact ⟨_, .memory (.initSucc hm hdi (by omega) hz (Array.getElem?_eq_getElem hlt))⟩
  | dataDrop hd =>
    obtain ⟨⟩ := hvs
    obtain ⟨da, di, hdi⟩ := hst.data hd
    exact ⟨_, .memory (.dataDrop hdi)⟩
  | @intLoad t _ arg _ _ h hm =>
    obtain ⟨v, rfl, hv⟩ := forall₂_one hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + t.width / 8
    · exact ⟨_, .memory (.loadIntOob hm hoob)⟩
    · obtain ⟨c, hc⟩ := Memory.load_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := t.width / 8) (by omega)
      exact ⟨_, .memory (.loadIntVal hm hc)⟩
  | @intLoadPack t sz sx _ arg _ _ h hsz hm =>
    obtain ⟨v, rfl, hv⟩ := forall₂_one hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + sz.width / 8
    · exact ⟨_, .memory (.loadPackOob hm hoob)⟩
    · obtain ⟨c, hc⟩ := Memory.load_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := sz.width / 8) (by omega)
      exact ⟨_, .memory (.loadPackVal hm hc)⟩
  | @floatLoad t _ arg _ _ h hm =>
    obtain ⟨v, rfl, hv⟩ := forall₂_one hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + t.width / 8
    · exact ⟨_, .memory (.loadFloatOob hm hoob)⟩
    · obtain ⟨c, hc⟩ := Memory.load_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := t.width / 8) (by omega)
      exact ⟨_, .memory (.loadFloatVal hm hc)⟩
  | @intStore t _ arg _ _ h hm =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨c, rfl⟩ := ValOk.int_inv hv₂
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + t.width / 8
    · exact ⟨_, .memory (.storeIntOob hm hoob)⟩
    · obtain ⟨bs, hbs⟩ := Memory.store_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := t.width / 8) (c.setWidth _) (by omega)
      exact ⟨_, .memory (.storeIntVal hm hbs)⟩
  | @intStorePack t sz _ arg _ _ h hsz hm =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨c, rfl⟩ := ValOk.int_inv hv₂
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + sz.width / 8
    · exact ⟨_, .memory (.storePackOob hm hoob)⟩
    · obtain ⟨bs, hbs⟩ := Memory.store_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := sz.width / 8) (c.setWidth _) (by omega)
      exact ⟨_, .memory (.storePackVal hm hbs)⟩
  | @floatStore t _ arg _ _ h hm =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨c, rfl⟩ := ValOk.float_inv hv₂
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + t.width / 8
    · exact ⟨_, .memory (.storeFloatOob hm hoob)⟩
    · obtain ⟨bs, hbs⟩ := Memory.store_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := t.width / 8) (c.setWidth _) (by omega)
      exact ⟨_, .memory (.storeFloatVal hm hbs)⟩
  | @vecLoad op _ arg _ _ h hm =>
    obtain ⟨v, rfl, hv⟩ := forall₂_one hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + op.accessWidth / 8
    · exact ⟨_, .memory (.vecLoadOob hm hoob)⟩
    · obtain ⟨c, hc⟩ := Memory.load_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := op.accessWidth / 8) (by omega)
      exact ⟨_, .memory (.vecLoadVal hm hc)⟩
  | @vecLoadLane sz _ arg j _ _ h hm hlane =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨c, rfl⟩ := ValOk.v128_inv hv₂
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + sz.width / 8
    · exact ⟨_, .memory (.vecLoadLaneOob hm hoob)⟩
    · obtain ⟨k, hk⟩ := Memory.load_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := sz.width / 8) (by omega)
      exact ⟨_, .memory (.vecLoadLaneVal hm hk)⟩
  | @vecStore _ arg _ _ h hm =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨c, rfl⟩ := ValOk.v128_inv hv₂
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + 16
    · exact ⟨_, .memory (.vecStoreOob hm hoob)⟩
    · obtain ⟨bs, hbs⟩ := Memory.store_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := 16) c (by omega)
      exact ⟨_, .memory (.vecStoreVal hm hbs)⟩
  | @vecStoreLane sz _ arg j _ _ h hm hlane =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨c, rfl⟩ := ValOk.v128_inv hv₂
    obtain ⟨ma, mi, hm, -⟩ := hst.mem h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hoob : mi.bytes.size < effAddr b.toNat arg + sz.width / 8
    · exact ⟨_, .memory (.vecStoreLaneOob hm hoob)⟩
    · obtain ⟨bs, hbs⟩ := Memory.store_of_le (m := mi.bytes) (start := effAddr b.toNat arg)
        (count := sz.width / 8) (((lanes sz.width (128 / sz.width) c).getD j.val 0).setWidth _) (by omega)
      exact ⟨_, .memory (.vecStoreLaneVal hm hbs)⟩

end Silmaril.Wasm.Execution.Core
