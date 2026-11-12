module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdRestR
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowB
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Decode

/-!
# Builtins that answer 1.0's bytes and growth: `bytesB10`

1.0's `$bytes_`, `$ibytes_` and `$growmemory` are answered by the builtins: the first two are
declared `hint(builtin)` with no clauses, and the one clause of `$growmemory` fails definitely
(round 2, `growmemory10_builtin`). The spec's builtins `floatIntB` answer none of them, so at
`floatIntB` a successful load or `memory.grow` never fires (pass 2). This module defines
`bytesB10 P`, the 1.0 counterpart of 2.0's `growB`: `floatIntB P` with those three names answered
as V1 does.

* `$bytes_(t, c)`: the little-endian bytes of the value `c` of type `t`, at the image of a V1
  number (`bytesCall10_numV`). The value is read back with round 5's `decNum`.
* `$ibytes_(N, %(k))`: the `N/8` little-endian bytes of `k` (`ibytesCall10_pct`).
* `$growmemory(mi, n)`: the image of V1's successful `Memory.grow?`, at the image of a V1 memory
  instance (`bytesB10_growmemory`). It is well defined because the 1.0 encoding of memory instances
  is injective (`memInstV10_injective`).

Elsewhere `bytesB10 P` is `floatIntB P` (`bytesB10_call_of_ne`), so it still extends the spec's
numerics (`intB_bytesB10`, `floatB_bytesB10`) and `NumAgree10` holds there
(`numAgree10_bytesB10`). With pass 3's assembly this gives the forward half at `bytesB10` from
`FwdRestR10 (bytesB10 _)` (`wholeStepFwd10_bytesB10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Config HostSemantics Step)
open Silmaril.Wasm.Execution.Runtime (MemInst)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)

variable {H : Type} {hn : H → String}

/-! ## The answers -/

/-- The little-endian bytes of `k`, `n` of them, as a `byte*`. -/
def leBytesV (n k : Nat) : Value := bytesV (Execution.Memory.encodeLE n k)

/-- `$bytes_` at a number type, from the value's image. -/
noncomputable def bytesAns10 (t : NumType) (cv : Value) : Option Value :=
  (Sim.Floats.decNum t cv).map fun b => leBytesV (t.width / 8) b.toNat

/-- **`$bytes_(t, c)`**, at the images of V1 numbers. -/
noncomputable def bytesCall10 : List ArgV → Option Value
  | [.val tv, .val cv] =>
    if tv = valTypeV (.int .i32) then bytesAns10 (.int .i32) cv
    else if tv = valTypeV (.int .i64) then bytesAns10 (.int .i64) cv
    else if tv = valTypeV (.float .f32) then bytesAns10 (.float .f32) cv
    else if tv = valTypeV (.float .f64) then bytesAns10 (.float .f64) cv
    else none
  | _ => none

/-- **`$ibytes_(N, %(k))`**: the `N/8` little-endian bytes of `k`. -/
def ibytesCall10 : List ArgV → Option Value
  | [.val (.num (.natN N)), .val (.case "%" (.tuple [.num (.natN k)]))] => some (leBytesV (N / 8) k)
  | _ => none

open Classical in
/-- **`$growmemory(mi, n)`**, at the images of V1 memory instances: V1's successful growth. -/
noncomputable def growCall10 (ws : List ArgV) : Option Value :=
  if h : ∃ p : MemInst × Nat, ws = [.val (memInstV p.1), .val (.num (.natN p.2))] then
    (Execution.Memory.grow? h.choose.1.data h.choose.1.max h.choose.2).map fun d =>
      memInstV {h.choose.1 with data := d}
  else none

/-- **The spec's builtins, with 1.0's bytes and growth answered as V1 does.** -/
noncomputable def bytesB10 (P : Profile) : Builtins :=
  ⟨fun x ws => if x = "bytes_" then bytesCall10 ws else if x = "ibytes_" then ibytesCall10 ws
    else if x = "growmemory" then growCall10 ws else (Sim.Floats.floatIntB P).call x ws⟩

/-! ## The encodings are injective -/

theorem limitsV10_injective {a b : Nat} {x y : Option Nat} (h : limitsV a x = limitsV b y) :
    a = b ∧ x = y := by
  simp only [limitsV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.opt.injEq,
    true_and, and_true] at h
  refine ⟨by simpa [pctV] using h.1, ?_⟩
  have hinj : Function.Injective pctV := Sim20.Whole.pctV_injective
  exact (Option.map_injective hinj) h.2

theorem bytesV10_injective : Function.Injective bytesV := fun a b h =>
  Sim20.Whole.bytesV_injective (show Sim20.bytesV a = Sim20.bytesV b from h)

/-- **The 1.0 encoding of memory instances is injective.** -/
theorem memInstV10_injective : Function.Injective memInstV := by
  rintro ⟨d₁, m₁⟩ ⟨d₂, m₂⟩ h
  simp only [memInstV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, true_and,
    and_true] at h
  rw [(limitsV10_injective h.1).2, bytesV10_injective h.2]

/-! ## The answers at V1's images -/

/-- `$bytes_` dispatches on the value type. -/
theorem bytesCall10_type (t : NumType) (cv : Value) :
    bytesCall10 [.val (valTypeV t), .val cv] = bytesAns10 t cv := by
  rcases t with (_ | _) | (_ | _) <;> simp [bytesCall10, valTypeV, Sim20.numTypeV, caseNilV]

/-- `decNum` reads back the 1.0 image of a number. -/
theorem decNum_numV10 (v : Execution.Runtime.Value) :
    Sim.Floats.decNum v.type (numV v) = some v.bits := by
  obtain ⟨t, b⟩ := v
  have h := Sim.Floats.decNum_numV t b
  rcases t with t | t <;> exact h

theorem bytesCall10_numV (v : Execution.Runtime.Value) :
    bytesCall10 [.val (valTypeV v.type), .val (numV v)] =
      some (leBytesV (v.type.width / 8) v.bits.toNat) := by
  rw [bytesCall10_type, bytesAns10, decNum_numV10]
  rfl

theorem ibytesCall10_pct (N k : Nat) :
    ibytesCall10 [.val (.num (.natN N)), .val (pctV k)] = some (leBytesV (N / 8) k) := rfl

theorem growCall10_memInstV (m : MemInst) (n : Nat) :
    growCall10 [.val (memInstV m), .val (.num (.natN n))] =
      (Execution.Memory.grow? m.data m.max n).map fun d => memInstV {m with data := d} := by
  have h : ∃ p : MemInst × Nat, [ArgV.val (memInstV m), .val (.num (.natN n))] =
      [.val (memInstV p.1), .val (.num (.natN p.2))] := ⟨(m, n), rfl⟩
  have e : h.choose = (m, n) := by
    obtain ⟨a₁, t₁⟩ := List.cons.inj h.choose_spec
    obtain ⟨a₂, -⟩ := List.cons.inj t₁
    exact Prod.ext (memInstV10_injective (ArgV.val.inj a₁).symm)
      (Num.natN.inj (Value.num.inj (ArgV.val.inj a₂))).symm
  simp only [growCall10, h, ↓reduceDIte, e]

theorem bytesB10_bytes (P : Profile) (ws : List ArgV) :
    (bytesB10 P).call "bytes_" ws = bytesCall10 ws := by simp [bytesB10]

theorem bytesB10_ibytes (P : Profile) (ws : List ArgV) :
    (bytesB10 P).call "ibytes_" ws = ibytesCall10 ws := by simp [bytesB10]

theorem bytesB10_growmemory (P : Profile) (m : MemInst) (n : Nat) :
    (bytesB10 P).call "growmemory" [.val (memInstV m), .val (.num (.natN n))] =
      (Execution.Memory.grow? m.data m.max n).map fun d => memInstV {m with data := d} := by
  simp [bytesB10, growCall10_memInstV]

/-- `bytesB10` agrees with `floatIntB` away from the three new names. -/
theorem bytesB10_call_of_ne {P : Profile} {x : IL.Id} (h₁ : x ≠ "bytes_") (h₂ : x ≠ "ibytes_")
    (h₃ : x ≠ "growmemory") (ws : List ArgV) :
    (bytesB10 P).call x ws = (Sim.Floats.floatIntB P).call x ws := by
  simp [bytesB10, h₁, h₂, h₃]

/-! ## The spec's numerics are kept -/

theorem intB_bytesB10 (P : Profile) : Sim.IntNumeric.IntB (bytesB10 P) := by
  intro x ws v h
  by_cases h₁ : x = "bytes_"
  · subst h₁; simp [Sim.IntNumeric.intCall] at h
  by_cases h₂ : x = "ibytes_"
  · subst h₂; simp [Sim.IntNumeric.intCall] at h
  by_cases h₃ : x = "growmemory"
  · subst h₃; simp [Sim.IntNumeric.intCall] at h
  rw [bytesB10_call_of_ne h₁ h₂ h₃]
  exact Sim.Floats.intB_floatIntB P x ws v h

theorem floatB_bytesB10 (P : Profile) : Sim.Floats.FloatB P (bytesB10 P) := by
  intro x ws v h
  by_cases h₁ : x = "bytes_"
  · subst h₁; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  by_cases h₂ : x = "ibytes_"
  · subst h₂; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  by_cases h₃ : x = "growmemory"
  · subst h₃; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  rw [bytesB10_call_of_ne h₁ h₂ h₃]
  exact Sim.Floats.floatB_floatIntB P x ws v h

/-- **`NumAgree10` holds at `bytesB10`.** -/
theorem numAgree10_bytesB10 (P : Profile) : NumAgree10 (simEnv10 (bytesB10 P)) P :=
  numAgree10_simEnv10 (intB_bytesB10 P) (floatB_bytesB10 P)

/-! ## The forward half at `bytesB10` -/

/-- **The forward 1.0 half at `bytesB10`**, from the three obligations of `FwdRestR10`. -/
theorem wholeStepFwd10_bytesB10 {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    (R : FwdRestR10 (bytesB10 (Profile.spec nd r)) hn) {c c' : Config H}
    (hc : Typed10 (simEnv10 (bytesB10 (Profile.spec nd r))) hn c)
    (hc' : Typed10 (simEnv10 (bytesB10 (Profile.spec nd r))) hn c')
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store)
    (h : Step host c c') :
    SStepB (simEnv10 (bytesB10 (Profile.spec nd r))) (configV hn c) (configV hn c') :=
  wholeStepFwd10_of_restR (numAgree10_bytesB10 _) R hc hc' hpl hg hal h

end Silmaril.Wasm.SpecTec.Sim10.Whole
