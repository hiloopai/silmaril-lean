module

public import Silmaril.Wasm.Logic.Hoare.Thms

/-! Pure full-width store inversions, extracted without statement or proof changes from
`Silmaril.Proofs.Wasm.Logic.Iris.Head`. The original Iris names remain wrappers. -/

@[expose] public section
namespace Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
variable {H : Type} {P : Profile}

/-- Compute both sides of a first-non-value equation. -/
local macro "fnv_simp " h:ident : tactic => `(tactic| (
  try simp only [SingleThreaded.Det.fnv_toAdmin_cons, SingleThreaded.Det.fnv_ref_cons, constI32,
    SingleThreaded.Det.fnv_vals_append, aconst, fnv_intConst_cons] at $h:ident
  simp [SingleThreaded.Det.fnv, Admin.val?] at $h:ident))

/-- Close a family case of another instruction. -/
local macro "fam_cfg " h:ident : tactic => `(tactic| (
  obtain ⟨rfl, rfl, h₁⟩ := cfg_split $h rfl
  fnv_simp h₁))

/-- Close a `Det.Head` case whose instruction is not the one at hand. -/
local macro "head_absurd" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | (simp only [Admin.IsCallRef, Admin.IsReturnCallRef] at *; done)))

theorem mem_intStore {s : Store H} {f : Frame} {args : List Val} {t : IntType} {x : MemIdx}
    {arg : MemArg} {c₀ : Config H}
    (h : MemoryStep P ⟨s, f, vals args ++ [.plain (.intStore t none x arg)]⟩ c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (c : BitVec t.width) (ma : Nat) (mi : MemInst),
      args = [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩] ∧ s.mem? f x = some (ma, mi) ∧
      ((mi.bytes.size < effAddr i.toNat arg + t.width / 8 ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        ∃ b, Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8)
          (c.setWidth _) = some b ∧ c₀ = ⟨s.setMem ma { mi with bytes := b }, f, []⟩) := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.intStore t none x arg)]⟩ : Config H) = c at h
  cases h with
  | storeIntOob hm hb =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, _, rfl, hm, .inl ⟨hb, rfl⟩⟩
  | storeIntVal hm hs =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, _, rfl, hm, .inr ⟨_, hs, rfl⟩⟩
  | _ => fam_cfg hc

theorem head_intStore {s : Store H} {f : Frame} {args : List Val} {t : IntType} {x : MemIdx}
    {arg : MemArg} {c₀ : Config H} (h : Head P s f args (.plain (.intStore t none x arg)) c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (c : BitVec t.width) (ma : Nat) (mi : MemInst),
      args = [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩] ∧ s.mem? f x = some (ma, mi) ∧
      ((mi.bytes.size < effAddr i.toNat arg + t.width / 8 ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        ∃ b, Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8)
          (c.setWidth _) = some b ∧ c₀ = ⟨s.setMem ma { mi with bytes := b }, f, []⟩) := by
  cases h with
  | memory h => exact mem_intStore h
  | _ => head_absurd

end Silmaril.Wasm.Logic.Hoare
