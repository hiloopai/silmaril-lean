module

public import Silmaril.Wasm.Spec.Attest.Core.Defs
public import Silmaril.Wasm.Verify.Check.Thms

/-!
# The instantiated gate, `true` and `false` modules

Kernel-checked facts (`decide +kernel`: validation and instantiation by `instance?`) about the
stores of `gateMod`, `ttMod` and `ffMod`, and their shapes (`GateShape`, `TTShape`): the
functions, their code, types and module instances, and the gate's globals.

New proofs, following `Silmaril.Proofs.Wasm.Game.ULinkExample` (this repository).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify Silmaril.Wasm.Spec.Attest.Core
  Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

/-! ### Kernel facts -/

theorem gate_instance : (instance? gateMod).isSome = true := by decide +kernel
theorem tt_instance : (instance? ttMod).isSome = true := by decide +kernel
theorem ff_instance : (instance? ffMod).isSome = true := by decide +kernel
theorem gate_imports : (instOf gateMod).imports = [unitFn] := by decide +kernel
theorem gate_exports : (instOf gateMod).exports = [unitFn, unitFn] := by decide +kernel
theorem gate_addrs : (instOf gateMod).addrs = [1, 2] := by decide +kernel
theorem tt_imports : (instOf ttMod).imports = [unitFn] := by decide +kernel
theorem tt_exports : (instOf ttMod).exports = [unitFn] := by decide +kernel
theorem tt_addrs : (instOf ttMod).addrs = [1] := by decide +kernel
theorem ff_imports : (instOf ffMod).imports = [unitFn] := by decide +kernel
theorem ff_exports : (instOf ffMod).exports = [unitFn] := by decide +kernel

/-- The `false` module never calls `attest`: the verifier proves it. -/
theorem ff_check : (check ffMod (.neverCall 0)).verdict = .proved := by decide +kernel

/-- The gate's body. -/
def isGate (m o : Fin (2 ^ 32)) (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 a, .globalSet x, .globalGet y, .if_ .empty [.call z] [],
      .unreachable]⟩ => a == 1 && x == ⟨m⟩ && y == ⟨o⟩ && z == ⟨0⟩
  | _ => false

/-- The `true` module's body. -/
def isFire (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.call z]⟩ => z == ⟨0⟩
  | _ => false

/-- The host function `attest`. -/
def isHost0 (fi : FuncInst Nat) : Bool := match fi.code with
  | .host 0 => true
  | _ => false

/-- `[] → []`, expanded. -/
abbrev voidTy : CCompType := .func (Ty.ofList []) (Ty.ofList [])

abbrev gS : Store Nat := (instOf gateMod).store
abbrev tS : Store Nat := (instOf ttMod).store

theorem g_len : gS.funcs.length = 3 := by decide +kernel
theorem g_L : gS.funcs.map (isGate 0 1) = [false, true, false] := by decide +kernel
theorem g_R : gS.funcs.map (isGate 1 0) = [false, false, true] := by decide +kernel
theorem g_host : gS.funcs.map isHost0 = [true, false, false] := by decide +kernel
theorem g_glob : gS.funcs.map (·.module.globals) = [[], [0, 1], [0, 1]] := by decide +kernel
theorem g_mfun : gS.funcs.map (·.module.funcs) = [[], [0, 1, 2], [0, 1, 2]] := by decide +kernel
theorem g_exp : gS.funcs.map (·.type.expand?) = [some voidTy, some voidTy, some voidTy] := by
  decide +kernel
theorem g_globals : gS.globals.map (·.value) = [.i32 0, .i32 0] := by decide +kernel
theorem t_len : tS.funcs.length = 2 := by decide +kernel
theorem t_fire : tS.funcs.map isFire = [false, true] := by decide +kernel
theorem t_host : tS.funcs.map isHost0 = [true, false] := by decide +kernel
theorem t_mfun : tS.funcs.map (·.module.funcs) = [[], [0, 1]] := by decide +kernel
theorem t_exp : tS.funcs.map (·.type.expand?) = [some voidTy, some voidTy] := by decide +kernel

theorem gateI_addr0 : gateI.addr (gateOp 0).1 = 1 := by
  show (instOf gateMod).addrs.getD 0 0 = 1
  rw [gate_addrs]
  rfl

theorem gateI_addr1 : gateI.addr (gateOp 1).1 = 2 := by
  show (instOf gateMod).addrs.getD 1 0 = 2
  rw [gate_addrs]
  rfl

/-! ### Reading the checks back -/

theorem isGate_code {m o : Fin (2 ^ 32)} {fi : FuncInst Nat} (h : isGate m o fi = true) :
    ∃ t, fi.code = .wasm ⟨t, [], gateBody m o⟩ := by
  unfold isGate at h
  split at h
  · rename_i t a x y z hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
    exact ⟨t, hc⟩
  · cases h

theorem isFire_code {fi : FuncInst Nat} (h : isFire fi = true) :
    ∃ t, fi.code = .wasm ⟨t, [], [.call ⟨0⟩]⟩ := by
  unfold isFire at h
  split at h
  · rename_i t z hc
    simp only [beq_iff_eq] at h
    exact ⟨t, h ▸ hc⟩
  · cases h

theorem isHost0_code {fi : FuncInst Nat} (h : isHost0 fi = true) : fi.code = .host 0 := by
  unfold isHost0 at h
  split at h
  · assumption
  · cases h

/-! ### Shapes -/

/-- The shape of the gate's store. -/
structure GateShape (fi₀ fi₁ fi₂ : FuncInst Nat) (g₀ g₁ : GlobalInst) : Prop where
  funcs : gS.funcs = [fi₀, fi₁, fi₂]
  code₀ : fi₀.code = .host 0
  code₁ : ∃ t, fi₁.code = .wasm ⟨t, [], gateBody 0 1⟩
  code₂ : ∃ t, fi₂.code = .wasm ⟨t, [], gateBody 1 0⟩
  ty₀ : Expand fi₀.type voidTy
  ty₁ : Expand fi₁.type voidTy
  ty₂ : Expand fi₂.type voidTy
  glob₁ : fi₁.module.globals = [0, 1]
  glob₂ : fi₂.module.globals = [0, 1]
  mfun₁ : fi₁.module.funcs = [0, 1, 2]
  mfun₂ : fi₂.module.funcs = [0, 1, 2]
  globals : gS.globals = [g₀, g₁]
  val₀ : g₀.value = .i32 0
  val₁ : g₁.value = .i32 0

theorem gateShape : ∃ fi₀ fi₁ fi₂ g₀ g₁, GateShape fi₀ fi₁ fi₂ g₀ g₁ := by
  obtain ⟨fi₀, fi₁, fi₂, hf⟩ := List.length_eq_three.mp g_len
  have hL : [fi₀, fi₁, fi₂].map (isGate 0 1) = [false, true, false] := hf ▸ g_L
  have hR : [fi₀, fi₁, fi₂].map (isGate 1 0) = [false, false, true] := hf ▸ g_R
  have hH : [fi₀, fi₁, fi₂].map isHost0 = [true, false, false] := hf ▸ g_host
  have hG : [fi₀, fi₁, fi₂].map (·.module.globals) = [[], [0, 1], [0, 1]] := hf ▸ g_glob
  have hM : [fi₀, fi₁, fi₂].map (·.module.funcs) = [[], [0, 1, 2], [0, 1, 2]] := hf ▸ g_mfun
  have hE : [fi₀, fi₁, fi₂].map (·.type.expand?) = [some voidTy, some voidTy, some voidTy] :=
    hf ▸ g_exp
  have hlen : gS.globals.length = 2 := by simpa using congrArg List.length g_globals
  obtain ⟨g₀, g₁, hg⟩ := List.length_eq_two.mp hlen
  have hV : [g₀, g₁].map (·.value) = [.i32 0, .i32 0] := hg ▸ g_globals
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hL hR hH hG hM hE hV
  exact ⟨fi₀, fi₁, fi₂, g₀, g₁, hf, isHost0_code hH.1, isGate_code hL.2.1, isGate_code hR.2.2.1,
    Expand.iff.mpr hE.1, Expand.iff.mpr hE.2.1, Expand.iff.mpr hE.2.2.1, hG.2.1, hG.2.2.1,
    hM.2.1, hM.2.2.1, hg, hV.1, hV.2.1⟩

/-- The shape of the `true` module's store. -/
structure TTShape (fi₀ fi₁ : FuncInst Nat) : Prop where
  funcs : tS.funcs = [fi₀, fi₁]
  code₀ : fi₀.code = .host 0
  code₁ : ∃ t, fi₁.code = .wasm ⟨t, [], [.call ⟨0⟩]⟩
  ty₀ : Expand fi₀.type voidTy
  ty₁ : Expand fi₁.type voidTy
  mfun₁ : fi₁.module.funcs = [0, 1]

theorem ttShape : ∃ fi₀ fi₁, TTShape fi₀ fi₁ := by
  obtain ⟨fi₀, fi₁, hf⟩ := List.length_eq_two.mp t_len
  have hF : [fi₀, fi₁].map isFire = [false, true] := hf ▸ t_fire
  have hH : [fi₀, fi₁].map isHost0 = [true, false] := hf ▸ t_host
  have hM : [fi₀, fi₁].map (·.module.funcs) = [[], [0, 1]] := hf ▸ t_mfun
  have hE : [fi₀, fi₁].map (·.type.expand?) = [some voidTy, some voidTy] := hf ▸ t_exp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hF hH hM hE
  exact ⟨fi₀, fi₁, hf, isHost0_code hH.1, isFire_code hF.2.1, Expand.iff.mpr hE.1,
    Expand.iff.mpr hE.2.1, hM.2.1⟩

end Silmaril.Proofs.Wasm.Spec.Attest
