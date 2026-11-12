module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowAnswer
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestMemInit

/-!
# Builtins that grow: `growB`, and the backward half there

`floatIntB` answers neither `$growtable` nor `$growmemory`, so at the spec's builtins the
wasm-2.0 script never grows (`WholeRestGrow`). `growB P` is `floatIntB P` with those two names
answered by V2's growth, at the images of V2 instances (`growCall20`). It still extends the spec's
numerics (`intB_growB`, `floatB_growB`), still answers no inert primitive (`inertEnv20_growB`),
and its growth answers are V2's (`growAnswers20_growB`). So the backward half holds there
(`wholeStepBwdW_growB`), and here `Step` 8 and 19 can fire.

The answers are well defined because the encodings of table and memory instances are injective
(`tableInstV_injective`, `memInstV_injective`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)

variable {H : Type}

/-! ## The encodings of instances are injective -/

theorem pctV_injective : Function.Injective pctV := by
  intro a b h
  simpa [pctV] using h

theorem refTypeV_injective : Function.Injective refTypeV := by
  intro a b h
  cases a <;> cases b <;> simp_all [refTypeV, caseNilV]

theorem refV_injective : Function.Injective refV := by
  intro a b h
  cases a <;> cases b <;> simp_all [refV, refTypeV_injective.eq_iff]

theorem limitsV_injective : Function.Injective limitsV := by
  rintro ⟨m₁, x₁⟩ ⟨m₂, x₂⟩ h
  have h' : m₁.val = m₂.val ∧ x₁.map (fun m => pctV m.val) = x₂.map (fun m => pctV m.val) := by
    simpa [limitsV, pctV] using h
  have hx : x₁ = x₂ := by
    cases x₁ <;> cases x₂ <;> simp_all [pctV, Fin.ext_iff]
  rw [Fin.ext h'.1, hx]

theorem tableTypeV_injective : Function.Injective tableTypeV := by
  rintro ⟨l₁, e₁⟩ ⟨l₂, e₂⟩ h
  simp only [tableTypeV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
    true_and] at h
  rw [limitsV_injective h.1, refTypeV_injective h.2]

theorem tableInstV_injective : Function.Injective tableInstV := by
  rintro ⟨t₁, r₁⟩ ⟨t₂, r₂⟩ h
  simp only [tableInstV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, true_and,
    Value.list.injEq, and_true] at h
  rw [tableTypeV_injective h.1, (List.map_injective_iff.2 refV_injective) h.2]

theorem bytesV_injective : Function.Injective bytesV := by
  intro a b h
  have hl : a.toList.map (fun x => pctV x.toNat) = b.toList.map (fun x => pctV x.toNat) := by
    simpa [bytesV] using h
  have hinj : Function.Injective (fun x : UInt8 => pctV x.toNat) :=
    fun x y hxy => UInt8.toNat_inj.1 (pctV_injective hxy)
  have ht : a.data.toList = b.data.toList := by
    rw [← byteArray_toList_eq, ← byteArray_toList_eq]
    exact (List.map_injective_iff.2 hinj) hl
  cases a; cases b
  simp only [ByteArray.mk.injEq]
  exact Array.ext' ht

theorem memInstV_injective : Function.Injective memInstV := by
  rintro ⟨⟨l₁⟩, b₁⟩ ⟨⟨l₂⟩, b₂⟩ h
  simp only [memInstV, memTypeV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, true_and,
    Value.case.injEq, and_true] at h
  rw [limitsV_injective h.1, bytesV_injective h.2]

/-! ## The growth primitives -/

open Classical in
/-- `$growtable` and `$growmemory` at the images of V2 instances: the image of V2's growth. -/
noncomputable def growCall20 (x : IL.Id) (ws : List ArgV) : Option Value :=
  if x = "growtable" then
    if h : ∃ p : TableInst × Nat × Ref,
        ws = [.val (tableInstV p.1), .val (.num (.natN p.2.1)), .val (refV p.2.2)] then
      (h.choose.1.grow? h.choose.2.1 h.choose.2.2).map tableInstV
    else none
  else if x = "growmemory" then
    if h : ∃ p : MemInst × Nat, ws = [.val (memInstV p.1), .val (.num (.natN p.2))] then
      (h.choose.1.grow? h.choose.2).map memInstV
    else none
  else none

open Classical in
/-- **The spec's builtins, with growth answered as V2 does.** -/
noncomputable def growB (P : Profile) : Builtins :=
  ⟨fun x ws => if x = "growtable" ∨ x = "growmemory" then growCall20 x ws
    else (Sim.Floats.floatIntB P).call x ws⟩

/-- `growB` agrees with `floatIntB` away from the two growth names. -/
theorem growB_call_of_ne {P : Profile} {x : IL.Id} (h₁ : x ≠ "growtable") (h₂ : x ≠ "growmemory")
    (ws : List ArgV) : (growB P).call x ws = (Sim.Floats.floatIntB P).call x ws := by
  simp [growB, h₁, h₂]

theorem growB_growtable (P : Profile) (ti : TableInst) (n : Nat) (r : Ref) :
    (growB P).call "growtable" [.val (tableInstV ti), .val (.num (.natN n)), .val (refV r)] =
      (ti.grow? n r).map tableInstV := by
  have h : ∃ p : TableInst × Nat × Ref, [ArgV.val (tableInstV ti), .val (.num (.natN n)),
      .val (refV r)] = [.val (tableInstV p.1), .val (.num (.natN p.2.1)), .val (refV p.2.2)] :=
    ⟨(ti, n, r), rfl⟩
  have e : h.choose = (ti, n, r) := by
    obtain ⟨a₁, t₁⟩ := List.cons.inj h.choose_spec
    obtain ⟨a₂, t₂⟩ := List.cons.inj t₁
    obtain ⟨a₃, -⟩ := List.cons.inj t₂
    exact Prod.ext (tableInstV_injective (ArgV.val.inj a₁).symm) (Prod.ext
      (Num.natN.inj (Value.num.inj (ArgV.val.inj a₂))).symm
      (refV_injective (ArgV.val.inj a₃).symm))
  simp only [growB, growCall20, true_or, ↓reduceIte, h, ↓reduceDIte, e]

theorem growB_growmemory (P : Profile) (mi : MemInst) (n : Nat) :
    (growB P).call "growmemory" [.val (memInstV mi), .val (.num (.natN n))] =
      (mi.grow? n).map memInstV := by
  have h : ∃ p : MemInst × Nat, [ArgV.val (memInstV mi), .val (.num (.natN n))] =
      [.val (memInstV p.1), .val (.num (.natN p.2))] := ⟨(mi, n), rfl⟩
  have e : h.choose = (mi, n) := by
    obtain ⟨a₁, t₁⟩ := List.cons.inj h.choose_spec
    obtain ⟨a₂, -⟩ := List.cons.inj t₁
    exact Prod.ext (memInstV_injective (ArgV.val.inj a₁).symm)
      (Num.natN.inj (Value.num.inj (ArgV.val.inj a₂))).symm
  have hne : ("growmemory" : IL.Id) ≠ "growtable" := by decide
  simp only [growB, growCall20, or_true, ↓reduceIte, hne, h, ↓reduceDIte, e]

/-! ## `growB` has the four properties -/

theorem growAnswers20_growB (P : Profile) : GrowAnswers20 (growB P) where
  table ti n r v h := by
    rw [growB_growtable] at h
    obtain ⟨ti', hg, hv⟩ := Option.map_eq_some_iff.1 h
    exact ⟨ti', hg, hv.symm⟩
  mem mi n v h := by
    rw [growB_growmemory] at h
    obtain ⟨mi', hg, hv⟩ := Option.map_eq_some_iff.1 h
    exact ⟨mi', hg, hv.symm⟩

theorem intB_growB (P : Profile) : Sim.IntNumeric.IntB (growB P) := by
  intro x ws v h
  by_cases h₁ : x = "growtable"
  · subst h₁; simp [Sim.IntNumeric.intCall] at h
  by_cases h₂ : x = "growmemory"
  · subst h₂; simp [Sim.IntNumeric.intCall] at h
  rw [growB_call_of_ne h₁ h₂]
  exact Sim.Floats.intB_floatIntB P x ws v h

theorem floatB_growB (P : Profile) : Sim.Floats.FloatB P (growB P) := by
  intro x ws v h
  by_cases h₁ : x = "growtable"
  · subst h₁; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  by_cases h₂ : x = "growmemory"
  · subst h₂; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  rw [growB_call_of_ne h₁ h₂]
  exact Sim.Floats.floatB_floatIntB P x ws v h

theorem inertEnv20_growB (P : Profile) : InertEnv (simEnv20 (growB P)) := by
  intro f hf
  have hn : f ≠ "growtable" ∧ f ≠ "growmemory" := by
    simp only [inertNames, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨hd, -⟩ := inertEnv20 P f hf
  refine ⟨by simpa [simEnv20] using hd, fun ws => ?_⟩
  rw [simEnv20, Env.builtins_withBuiltins, growB_call_of_ne hn.1 hn.2]
  exact floatIntB_inert P hf ws

/-! ## The backward half at `growB` -/

/-- **The backward half at builtins that grow**: at `growB (Profile.spec nd r)`, every step of the
wasm-2.0 script from the image of a `GoodW` configuration is the image of a V2 step. Unlike at
`floatIntB`, `Step` 8 and 19 can fire here, and each is matched by V2's `grow-succeed`. -/
theorem wholeStepBwdW_growB {hn : H → String} {host : HostSemantics H} (nd : Bool)
    (r : Silmaril.Wasm.Numerics.RelaxedChoice) (c : Config H) (w : Value) (hg : GoodW c)
    (hs : Sim.Round6.Reading.SStepB (simEnv20 (growB (Profile.spec nd r))) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c' :=
  wholeStepBwdW_at (intB_growB _) (floatB_growB _) (inertEnv20_growB _) (growAnswers20_growB _)
    (growMayFail_spec nd r) (fun _ _ _ _ => trivial) c w hg hs

end Silmaril.Wasm.SpecTec.Sim20.Whole
