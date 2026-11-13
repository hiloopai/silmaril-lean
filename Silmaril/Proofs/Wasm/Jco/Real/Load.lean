module

public import Silmaril.Proofs.Wasm.Jco.Real.Step

/-!
# Adaptor instructions against the reference engine: integer loads

An integer load of a width that Wasm has (`intWidthOk`) is simulated by the Core 3.0 load of
its Lime1 image (`i32.load`, `i32.load8_u`, …, `i64.load32_s`, `i64.load`), on the memory of
`realInst` read as a Core byte array (`memBytes_load`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) (fi : String → Nat)

theorem leNat_lt : ∀ bs : List UInt8, leNat bs < 256 ^ bs.length
  | [] => by simp [leNat]
  | b :: bs => by
    have h1 := leNat_lt bs
    have h2 : b.toNat < 256 := b.toNat_lt
    show b.toNat + 256 * leNat bs < 256 ^ (bs.length + 1)
    rw [Nat.pow_succ']
    omega

theorem read_length {m : Mem} {p n : Nat} {bs : List UInt8} (h : m.read p n = some bs) :
    bs.length = n := by
  unfold Mem.read at h
  split at h
  · cases h
    simp only [List.length_take, List.length_drop]
    omega
  · cases h

theorem effAddr_memArg (i : BitVec 32) (al off : Nat) (hoff : off < 2 ^ 32) :
    effAddr i.toNat (memArg al off).toCore = i.toNat + off := by
  have h' : off < 4294967296 := hoff
  simp [effAddr, memArg, Silmaril.Wasm.V1.MemArg.toCore, Silmaril.Wasm.V1.widen32,
    Nat.mod_eq_of_lt h']

/-- The cases of `intWidthOk`. -/
theorem intWidthOk_cases {it : Silmaril.Wasm.IntType} {n : Nat} (h : intWidthOk it n = true) :
    (it = .i32 ∧ (n = 1 ∨ n = 2 ∨ n = 4)) ∨ (it = .i64 ∧ (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)) := by
  cases it
  · simp only [intWidthOk, Bool.or_eq_true, beq_iff_eq] at h
    exact .inl ⟨rfl, by omega⟩
  · simp only [intWidthOk, Bool.or_eq_true, beq_iff_eq] at h
    exact .inr ⟨rfl, by omega⟩

theorem setWidth_ofNat_lt {k w L : Nat} (hk : k ≤ w) (hL : L < 2 ^ k) :
    (BitVec.ofNat k L).setWidth w = BitVec.ofNat w L := by
  apply BitVec.eq_of_toNat_eq
  have hw : L < 2 ^ w := Nat.lt_of_lt_of_le hL (Nat.pow_le_pow_right (by omega) hk)
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hw]

theorem toAdmin_loadVal (it : Silmaril.Wasm.IntType) (n : Nat) (sx : Bool) (bs : List UInt8) :
    (toVal (loadVal (.int it) n sx bs)).toAdmin =
      .plain (.intConst it (if sx then (BitVec.ofNat (8 * n) (leNat bs)).signExtend it.width
        else BitVec.ofNat it.width (leNat bs))) := by
  cases sx <;> rfl

theorem signExtend_eq_setWidth {w v : Nat} (x : BitVec w) (h : v = w) :
    x.signExtend v = x.setWidth v := by
  subst h
  simp

/-- The facts of a successful read used by the Core load: the memory instance, the Core load of
the bytes, and their bound. -/
theorem load_facts {n off : Nat} (hn0 : 0 < n) (hoff : off < 2 ^ 32) {s : Store H}
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hmem : cf.module.mems[0]? = some ma)
    {a : BitVec 32} {bs : List UInt8} (hr : (memBytes ma s).read (a.toNat + off) n = some bs) :
    ∃ m, s.mem? cf ⟨0⟩ = some (ma, m) ∧
      Silmaril.Wasm.Execution.Memory.load m.bytes (effAddr a.toNat (memArg (alignExp n) off).toCore) n =
        some (BitVec.ofNat (8 * n) (leNat bs)) ∧ leNat bs < 2 ^ (8 * n) := by
  have hlen : bs.length = n := read_length hr
  have h256 : (2 : Nat) ^ (8 * n) = 256 ^ n := by rw [Nat.pow_mul]
  have hL : leNat bs < 2 ^ (8 * n) := by
    rw [h256, ← hlen]
    exact leNat_lt bs
  obtain ⟨m, hm, hload⟩ := memBytes_load hn0 hr
  have hsm : s.mem? cf ⟨0⟩ = some (ma, m) := by
    simp [Store.mem?, Silmaril.Wasm.Idx.toNat, hmem, hm]
  rw [effAddr_memArg a (alignExp n) off hoff]
  exact ⟨m, hsm, hload, hL⟩

/-- **The Core 3.0 load** of the image of an integer load, on the bytes `bs` read by `realInst`. -/
theorem core_loadInt {it : Silmaril.Wasm.IntType} {n : Nat} {sx : Bool} {off : Nat}
    (hn : intWidthOk it n = true) (hoff : off < 2 ^ 32) {s : Store H}
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hmem : cf.module.mems[0]? = some ma)
    {a : BitVec 32} {bs : List UInt8} (hr : (memBytes ma s).read (a.toNat + off) n = some bs) :
    Step P host ⟨s, cf, [.plain (.intConst .i32 a), .plain (coreOf fi (.load (.int it) n sx off))]⟩
      ⟨s, cf, [(toVal (loadVal (.int it) n sx bs)).toAdmin]⟩ := by
  have hcases := intWidthOk_cases hn
  have hn0 : 0 < n := by omega
  obtain ⟨m, hsm, hload, hL⟩ := load_facts ma hn0 hoff hmem hr
  rcases hcases with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ <;> cases sx <;>
    rw [toAdmin_loadVal] <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    first
    | exact Step.memory (MemoryStep.loadPackVal (sx := .signed) (a := .i32) (i := a) hsm hload)
    | (rw [← setWidth_ofNat_lt ?_ hL]
       · first
         | exact Step.memory (MemoryStep.loadPackVal (sx := .unsigned) (a := .i32) (i := a)
             hsm hload)
         | exact Step.memory (MemoryStep.loadIntVal (a := .i32) (i := a) hsm hload)
       · decide)
    | (rw [signExtend_eq_setWidth _ ?_]
       · exact Step.memory (MemoryStep.loadIntVal (a := .i32) (i := a) hsm hload)
       · decide)

theorem sim_loadInt {it : Silmaril.Wasm.IntType} {n : Nat} {sx : Bool} {off : Nat}
    (hn : intWidthOk it n = true) (hoff : off < 2 ^ 32) {f f' : Silmaril.Wasm.Jco.Frame}
    {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) (.load (.int it) n sx off) f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi (.load (.int it) n sx off))] := by
  rcases f with ⟨ls, _ | ⟨va, st⟩⟩ <;> simp only [XInstr.step] at h
  · cases h
  · obtain ⟨a, s₁, ha, h₁⟩ := ok_bind h
    obtain ⟨ha', rfl⟩ := ok_ofOption ha
    obtain ⟨bs, s₂, hb, hp⟩ := ok_bind h₁
    obtain ⟨hr, rfl⟩ := ok_load hb
    obtain ⟨rfl, rfl⟩ := ok_pure hp
    refine ⟨cf, rfl, hl, ?_⟩
    have hrun := lift P host st (core_loadInt P host ma fi (sx := sx) hn hoff he.mem hr).steps
    rw [stackCode_cons, stackCode_cons, asI32?_eq ha', toAdmin_i32, List.append_assoc]
    exact hrun

end Silmaril.Proofs.Wasm.Jco.Real
