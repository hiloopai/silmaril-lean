module

public import Silmaril.Wasm.Examples.Farkas.Defs
public import Silmaril.Wasm.Game.Signature.Defs

@[expose] public section

/-!
# The Farkas checker: the instance and the machine state in the store

`Mach`: the values the checker keeps (four globals and the memory bytes); `Holds s m`: the
store `s` holds them, in the layout of the instance (`farkasStore`'s functions, globals at
addresses `0‥3`, memory at address `0`). The facts about the instance are computed:
`farkasMI_globals`, `farkasStore_globals`, `farkasStore_mems`, `farkasStore_funcs` by `rfl`,
the export types and validation by `decide +kernel`.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game

/-- The type of the two `i32` globals. -/
def gT32 : Silmaril.Wasm.Validation.CGlobalType := ⟨.var, .num (.int .i32)⟩
/-- The type of the two `i64` globals. -/
def gT64 : Silmaril.Wasm.Validation.CGlobalType := ⟨.var, .num (.int .i64)⟩
/-- The memory type: one page, not growable. -/
def memTy : MemoryType := ⟨.i32, ⟨1, some 1⟩⟩
/-- The initial memory: one page of zeros. -/
def zeroBytes : ByteArray := ⟨Array.replicate 65536 0⟩

/-- The machine state of the checker. -/
structure Mach where
  /-- The sticky failure flag. -/
  bad : BitVec 32
  /-- Whether a row has been started. -/
  hr : BitVec 32
  /-- The current multiplier. -/
  y : BitVec 64
  /-- The weighted sum of the bounds. -/
  vb : BitVec 64
  /-- The memory: the accumulators `acc[j]` at `8 j`. -/
  mem : ByteArray

/-- The globals holding a machine state. -/
def Mach.globals (m : Mach) : List GlobalInst :=
  [⟨gT32, .i32 m.bad⟩, ⟨gT32, .i32 m.hr⟩, ⟨gT64, .i64 m.y⟩, ⟨gT64, .i64 m.vb⟩]

/-- The store `s` with the machine state `m` in the instance's globals and memory. -/
def withMach (s : Store Nat) (m : Mach) : Store Nat :=
  { s with globals := m.globals, mems := [⟨memTy, m.mem⟩] }

/-- The store holds the machine state in the instance's layout (and its functions). -/
def Holds (s : Store Nat) (m : Mach) : Prop :=
  ∃ s₀ : Store Nat, s₀.funcs = farkasStore.funcs ∧ s = withMach s₀ m

theorem withMach_withMach (s : Store Nat) (m m' : Mach) : withMach (withMach s m) m' = withMach s m' :=
  rfl

theorem funcs_withMach (s : Store Nat) (m : Mach) : (withMach s m).funcs = s.funcs := rfl

theorem Holds.funcs {s : Store Nat} {m : Mach} (h : Holds s m) : s.funcs = farkasStore.funcs := by
  obtain ⟨s₀, hf, rfl⟩ := h
  exact hf

theorem holds_withMach {s : Store Nat} (h : s.funcs = farkasStore.funcs) (m' : Mach) :
    Holds (withMach s m') m' := ⟨s, h, rfl⟩

/-- The initial machine state. -/
def Mach.init : Mach := ⟨0, 0, 0, 0, zeroBytes⟩

theorem farkasMI_globals : farkasMI.globals = [0, 1, 2, 3] := rfl
theorem farkasMI_mems : farkasMI.mems = [0] := rfl
theorem farkasRun_eq : farkasRun = some (farkasStore, (match farkasRun with
    | some (_, f, _) => f | none => {}), none) := rfl

theorem farkasStore_holds : Holds farkasStore Mach.init := ⟨farkasStore, rfl, rfl⟩

/-- The three functions of the instance. -/
theorem farkasStore_funcs : ∃ fi₀ fi₁ fi₂ : FuncInst Nat, farkasStore.funcs = [fi₀, fi₁, fi₂] ∧
    fi₀.module = farkasMI ∧ fi₁.module = farkasMI ∧ fi₂.module = farkasMI ∧
    fi₀.code = .wasm ⟨⟨0⟩, [.i64], rowBody⟩ ∧ fi₁.code = .wasm ⟨⟨1⟩, [.i32, .i64], entryBody⟩ ∧
    fi₂.code = .wasm ⟨⟨2⟩, [.i32, .i32], checkBody⟩ ∧
    FnType.ofDefType? fi₀.type = some farkasExports[0] ∧
    FnType.ofDefType? fi₁.type = some farkasExports[1] ∧
    FnType.ofDefType? fi₂.type = some farkasExports[2] := by
  have hty : farkasStore.funcs.map (fun fi => FnType.ofDefType? fi.type) =
      farkasExports.map some := by decide +kernel
  have hmod : farkasStore.funcs.map FuncInst.module = [farkasMI, farkasMI, farkasMI] := rfl
  have hcode : farkasStore.funcs.map FuncInst.code = farkasMod.funcs.map .wasm := rfl
  have hlen : farkasStore.funcs.length = 3 := rfl
  obtain ⟨fi₀, fi₁, fi₂, hf⟩ := List.length_eq_three.mp hlen
  rw [hf] at hty hmod hcode
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, farkasExports,
    farkasMod] at hty hmod hcode
  exact ⟨fi₀, fi₁, fi₂, hf, hmod.1, hmod.2.1, hmod.2.2, hcode.1, hcode.2.1, hcode.2.2,
    hty.1, hty.2.1, hty.2.2⟩

end Silmaril.Wasm.Examples.Farkas
