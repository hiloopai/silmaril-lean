module

public import Silmaril.Proofs.Wasm.Logic.Instr.Table

/-!
# Instruction rules: vector (SIMD) instructions

In both readings (`Wp m`) and every profile:

* `Wp.vector`: every profile-free vector instruction (`v128` bitwise
  operations, integer lane operations other than the relaxed ones, comparisons,
  shifts, bitmask, `swizzle`, `shuffle`, `splat`, lane extraction and
  replacement, extending unary operations, narrowing) from one silmaril-lean
  `VectorStep` witness;
* `Wp.vectorAll`: every vector instruction, quantifying over all the results
  the profile allows;
* dedicated rules for the profile-dependent ones: `Wp.vecFloatUnOp`,
  `Wp.vecFloatBinOp`, `Wp.vecFloatTernOp` (NaN and relaxed choices, and their
  traps), `Wp.vecIntBinOp`, `Wp.vecIntTernOp` and `Wp.vecRelaxedSwizzle` (the
  relaxed choice of the profile), `Wp.vecExtBinOp`, `Wp.vecExtTernOp` (relaxed
  dot products) and `Wp.vecConvert` (including relaxed truncation).

A Silmaril addition; the step rules are silmaril-lean's
`Silmaril/Wasm/Execution/Core/Step/Vector.lean` and the result relations of
`Silmaril.Wasm.Numerics.VectorProfile`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}
variable {m : Corr} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin} {Q : Post H}

/-- `famOf` of a concrete instruction. -/
local macro "fam_ok" : term => `(by simp [famOf])

/-- Close a family case whose instruction is not the one at hand. -/
local macro "last_absurd " hl:ident : tactic => `(tactic| (
  have h₂ := congrArg List.getLast? $hl
  simp [vals, Val.toAdmin] at h₂))

/-! ## Generic vector rules -/

/-- **Profile-free vector instructions**, from one step. -/
theorem Wp.vector {args : List Val} {i : Instr} {is' : List Admin}
    (hfam : famOf (.plain i) = .vector) (hpf : ProfileFree i)
    (h₁ : VectorStep P (vals args ++ [.plain i]) is')
    (h : Wp m P host s f (vals us ++ is' ++ rest) Q) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q :=
  Wp.det (c₁ := ⟨s, f, is'⟩) (by rw [hfam]; simp) hpf (.vector h₁) h

/-- **Every vector instruction**, over all results the profile allows. -/
theorem Wp.vectorAll {args : List Val} {i : Instr} (hfam : famOf (.plain i) = .vector)
    (hp : ∃ is', VectorStep P (vals args ++ [.plain i]) is')
    (h : ∀ is', VectorStep P (vals args ++ [.plain i]) is' →
      Wp m P host s f (vals us ++ is' ++ rest) Q) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q := by
  have hfam' : famOf (.plain i) ≠ .control := by rw [hfam]; simp
  obtain ⟨is₀, h₀⟩ := hp
  refine Wp.fam hfam' ⟨_, .vector h₀⟩ fun c₀ hh => ?_
  have hr := hh.fam_inv hfam'
  rw [hfam] at hr
  obtain ⟨is', hv, rfl⟩ := hr
  exact h is' hv

/-! ## Inversions for the profile-dependent instructions -/

section Inv

variable {a b c : V128}

theorem vec_floatUnOp {sh : FloatShape} {op : FloatUnOp} {r : List Admin}
    (h : VectorStep P (vals [.vec a] ++ [.plain (.vecFloatUnOp sh op)]) r) :
    (∃ r', VecFloatUnOpRel P sh op a r' ∧ r = vals [.vec r']) ∨
      ((∀ r', ¬ VecFloatUnOpRel P sh op a r') ∧ r = [.trap]) := by
  generalize hl : vals [Val.vec a] ++ [Admin.plain (.vecFloatUnOp sh op)] = l at h
  cases h
  case vecFloatUnOp => cases hl; exact .inl ⟨_, by assumption, rfl⟩
  case vecFloatUnOpTrap => cases hl; exact .inr ⟨by assumption, rfl⟩
  all_goals last_absurd hl

theorem vec_floatBinOp {sh : FloatShape} {op : VecFloatBinOp} {r : List Admin}
    (h : VectorStep P (vals [.vec a, .vec b] ++ [.plain (.vecFloatBinOp sh op)]) r) :
    (∃ r', VecFloatBinOpRel P sh op a b r' ∧ r = vals [.vec r']) ∨
      ((∀ r', ¬ VecFloatBinOpRel P sh op a b r') ∧ r = [.trap]) := by
  generalize hl : vals [Val.vec a, .vec b] ++ [Admin.plain (.vecFloatBinOp sh op)] = l at h
  cases h
  case vecFloatBinOp => cases hl; exact .inl ⟨_, by assumption, rfl⟩
  case vecFloatBinOpTrap => cases hl; exact .inr ⟨by assumption, rfl⟩
  all_goals last_absurd hl

theorem vec_floatTernOp {sh : FloatShape} {op : VecFloatTernOp} {r : List Admin}
    (h : VectorStep P (vals [.vec a, .vec b, .vec c] ++ [.plain (.vecFloatTernOp sh op)]) r) :
    (∃ r', VecFloatTernOpRel P sh op a b c r' ∧ r = vals [.vec r']) ∨
      ((∀ r', ¬ VecFloatTernOpRel P sh op a b c r') ∧ r = [.trap]) := by
  generalize hl : vals [Val.vec a, .vec b, .vec c] ++ [Admin.plain (.vecFloatTernOp sh op)] = l at h
  cases h
  case vecFloatTernOp => cases hl; exact .inl ⟨_, by assumption, rfl⟩
  case vecFloatTernOpTrap => cases hl; exact .inr ⟨by assumption, rfl⟩
  all_goals last_absurd hl

theorem vec_intBinOp {sh : IntShape} {op : VecIntBinOp} {r : List Admin}
    (h : VectorStep P (vals [.vec a, .vec b] ++ [.plain (.vecIntBinOp sh op)]) r) :
    r = vals [.vec (vecIntBinOp P sh op a b)] := by
  generalize hl : vals [Val.vec a, .vec b] ++ [Admin.plain (.vecIntBinOp sh op)] = l at h
  cases h
  case vecIntBinOp => cases hl; rfl
  all_goals last_absurd hl

theorem vec_intTernOp {sh : IntShape} {op : VecIntTernOp} {r : List Admin}
    (h : VectorStep P (vals [.vec a, .vec b, .vec c] ++ [.plain (.vecIntTernOp sh op)]) r) :
    r = vals [.vec (vecIntTernOp P sh op a b c)] := by
  generalize hl : vals [Val.vec a, .vec b, .vec c] ++ [Admin.plain (.vecIntTernOp sh op)] = l at h
  cases h
  case vecIntTernOp => cases hl; rfl
  all_goals last_absurd hl

theorem vec_relaxedSwizzle {r : List Admin}
    (h : VectorStep P (vals [.vec a, .vec b] ++ [.plain (.vecSwizzle .relaxedSwizzle)]) r) :
    r = vals [.vec (vecRelaxedSwizzle P a b)] := by
  generalize hl : vals [Val.vec a, .vec b] ++ [Admin.plain (.vecSwizzle .relaxedSwizzle)] = l at h
  cases h
  case vecRelaxedSwizzle => cases hl; rfl
  all_goals last_absurd hl

theorem vec_extBinOp {sh₁ sh₂ : IntShape} {op : VecExtBinOp} {r : List Admin}
    (h : VectorStep P (vals [.vec a, .vec b] ++ [.plain (.vecExtBinOp sh₁ sh₂ op)]) r) :
    ∃ r', VecExtBinOpRel P sh₁ sh₂ op a b r' ∧ r = vals [.vec r'] := by
  generalize hl : vals [Val.vec a, .vec b] ++ [Admin.plain (.vecExtBinOp sh₁ sh₂ op)] = l at h
  cases h
  case vecExtBinOp => cases hl; exact ⟨_, by assumption, rfl⟩
  all_goals last_absurd hl

theorem vec_extTernOp {sh₁ sh₂ : IntShape} {op : VecExtTernOp} {r : List Admin}
    (h : VectorStep P (vals [.vec a, .vec b, .vec c] ++ [.plain (.vecExtTernOp sh₁ sh₂ op)]) r) :
    ∃ r', VecExtTernOpRel P sh₁ sh₂ op a b c r' ∧ r = vals [.vec r'] := by
  generalize hl : vals [Val.vec a, .vec b, .vec c] ++
    [Admin.plain (.vecExtTernOp sh₁ sh₂ op)] = l at h
  cases h
  case vecExtTernOp => cases hl; exact ⟨_, by assumption, rfl⟩
  all_goals last_absurd hl

theorem vec_convert {sh₁ sh₂ : Shape} {op : VecConvertOp} {r : List Admin}
    (h : VectorStep P (vals [.vec a] ++ [.plain (.vecConvert sh₁ sh₂ op)]) r) :
    ∃ r', VecConvertRel P sh₁ sh₂ op a r' ∧ r = vals [.vec r'] := by
  generalize hl : vals [Val.vec a] ++ [Admin.plain (.vecConvert sh₁ sh₂ op)] = l at h
  cases h
  case vecConvert => cases hl; exact ⟨_, by assumption, rfl⟩
  all_goals last_absurd hl

end Inv

/-! ## Profile-dependent vector instructions -/

section Rules

variable {a b c : V128}

/-- **Vector float unary operations**: every result the profile allows, or a trap
when it allows none. -/
theorem Wp.vecFloatUnOp {sh : FloatShape} {op : FloatUnOp}
    (h : ∀ r, VecFloatUnOpRel P sh op a r → Wp m P host s f (vals (us ++ [.vec r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.vec a]) ++ .plain (.vecFloatUnOp sh op) :: rest) Q := by
  obtain ⟨r₀, h₀⟩ := VecFloatUnOpRel_nonempty P sh op a
  refine Wp.vectorAll (args := [.vec a]) (by simp [famOf]) ⟨_, .vecFloatUnOp h₀⟩ fun is' hv => ?_
  rcases vec_floatUnOp hv with ⟨r, hr, rfl⟩ | ⟨hn, -⟩
  · simpa using h r hr
  · exact absurd h₀ (hn r₀)

/-- **Vector float binary operations** (including `relaxed_min/max`). -/
theorem Wp.vecFloatBinOp {sh : FloatShape} {op : VecFloatBinOp}
    (hp : ∃ r, VecFloatBinOpRel P sh op a b r ∨ ∀ r', ¬ VecFloatBinOpRel P sh op a b r')
    (h : ∀ r, VecFloatBinOpRel P sh op a b r →
      Wp m P host s f (vals (us ++ [.vec r]) ++ rest) Q)
    (htrap : (∀ r, ¬ VecFloatBinOpRel P sh op a b r) → Q s f .trap) :
    Wp m P host s f (vals (us ++ [.vec a, .vec b]) ++ .plain (.vecFloatBinOp sh op) :: rest) Q := by
  have hp' : ∃ is', VectorStep P (vals [.vec a, .vec b] ++ [.plain (.vecFloatBinOp sh op)]) is' := by
    obtain ⟨r, hr | hn⟩ := hp
    · exact ⟨_, .vecFloatBinOp hr⟩
    · exact ⟨_, .vecFloatBinOpTrap hn⟩
  refine Wp.vectorAll (by simp [famOf]) hp' fun is' hv => ?_
  rcases vec_floatBinOp hv with ⟨r, hr, rfl⟩ | ⟨hn, rfl⟩
  · simpa using h r hr
  · simpa using Wp.trap (m := m) (P := P) (host := host) (us := us) (rest := rest) (htrap hn)

/-- **Vector float ternary operations** (`relaxed_madd/nmadd`). -/
theorem Wp.vecFloatTernOp {sh : FloatShape} {op : VecFloatTernOp}
    (hp : ∃ r, VecFloatTernOpRel P sh op a b c r ∨ ∀ r', ¬ VecFloatTernOpRel P sh op a b c r')
    (h : ∀ r, VecFloatTernOpRel P sh op a b c r →
      Wp m P host s f (vals (us ++ [.vec r]) ++ rest) Q)
    (htrap : (∀ r, ¬ VecFloatTernOpRel P sh op a b c r) → Q s f .trap) :
    Wp m P host s f (vals (us ++ [.vec a, .vec b, .vec c]) ++
      .plain (.vecFloatTernOp sh op) :: rest) Q := by
  have hp' : ∃ is', VectorStep P (vals [.vec a, .vec b, .vec c] ++
      [.plain (.vecFloatTernOp sh op)]) is' := by
    obtain ⟨r, hr | hn⟩ := hp
    · exact ⟨_, .vecFloatTernOp hr⟩
    · exact ⟨_, .vecFloatTernOpTrap hn⟩
  refine Wp.vectorAll (by simp [famOf]) hp' fun is' hv => ?_
  rcases vec_floatTernOp hv with ⟨r, hr, rfl⟩ | ⟨hn, rfl⟩
  · simpa using h r hr
  · simpa using Wp.trap (m := m) (P := P) (host := host) (us := us) (rest := rest) (htrap hn)

/-- **Vector integer binary operations** (including relaxed `q15mulr`, by the
profile's choice). -/
theorem Wp.vecIntBinOp {sh : IntShape} {op : VecIntBinOp}
    (h : Wp m P host s f (vals (us ++ [.vec (vecIntBinOp P sh op a b)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.vec a, .vec b]) ++ .plain (.vecIntBinOp sh op) :: rest) Q :=
  Wp.vectorAll (by simp [famOf]) ⟨_, .vecIntBinOp sh op a b⟩ fun is' hv => by
    rw [vec_intBinOp hv]; simpa using h

/-- **Vector integer ternary operations** (relaxed lane select). -/
theorem Wp.vecIntTernOp {sh : IntShape} {op : VecIntTernOp}
    (h : Wp m P host s f (vals (us ++ [.vec (vecIntTernOp P sh op a b c)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.vec a, .vec b, .vec c]) ++
      .plain (.vecIntTernOp sh op) :: rest) Q :=
  Wp.vectorAll (by simp [famOf]) ⟨_, .vecIntTernOp sh op a b c⟩ fun is' hv => by
    rw [vec_intTernOp hv]; simpa using h

/-- **`i8x16.relaxed_swizzle`.** -/
theorem Wp.vecRelaxedSwizzle
    (h : Wp m P host s f (vals (us ++ [.vec (vecRelaxedSwizzle P a b)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.vec a, .vec b]) ++ .plain (.vecSwizzle .relaxedSwizzle) ::
      rest) Q :=
  Wp.vectorAll (by simp [famOf]) ⟨_, .vecRelaxedSwizzle a b⟩ fun is' hv => by
    rw [vec_relaxedSwizzle hv]; simpa using h

/-- **Extending binary operations** (`extmul`, `dot`, `relaxed_dot`). -/
theorem Wp.vecExtBinOp {sh₁ sh₂ : IntShape} {op : VecExtBinOp}
    (h : ∀ r, VecExtBinOpRel P sh₁ sh₂ op a b r →
      Wp m P host s f (vals (us ++ [.vec r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.vec a, .vec b]) ++ .plain (.vecExtBinOp sh₁ sh₂ op) :: rest) Q := by
  obtain ⟨r₀, h₀⟩ := VecExtBinOpRel_nonempty P sh₁ sh₂ op a b
  refine Wp.vectorAll (by simp [famOf]) ⟨_, .vecExtBinOp h₀⟩ fun is' hv => ?_
  obtain ⟨r, hr, rfl⟩ := vec_extBinOp hv
  simpa using h r hr

/-- **Extending ternary operations** (`relaxed_dot_add`). -/
theorem Wp.vecExtTernOp {sh₁ sh₂ : IntShape} {op : VecExtTernOp}
    (h : ∀ r, VecExtTernOpRel P sh₁ sh₂ op a b c r →
      Wp m P host s f (vals (us ++ [.vec r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.vec a, .vec b, .vec c]) ++
      .plain (.vecExtTernOp sh₁ sh₂ op) :: rest) Q := by
  obtain ⟨r₀, h₀⟩ := VecExtTernOpRel_nonempty P sh₁ sh₂ op a b c
  refine Wp.vectorAll (by simp [famOf]) ⟨_, .vecExtTernOp h₀⟩ fun is' hv => ?_
  obtain ⟨r, hr, rfl⟩ := vec_extTernOp hv
  simpa using h r hr

/-- **Vector conversions** (including `relaxed_trunc`): every result the profile
allows; `hp` says some result exists (an invalid conversion is stuck). -/
theorem Wp.vecConvert {sh₁ sh₂ : Shape} {op : VecConvertOp}
    (hp : ∃ r, VecConvertRel P sh₁ sh₂ op a r)
    (h : ∀ r, VecConvertRel P sh₁ sh₂ op a r → Wp m P host s f (vals (us ++ [.vec r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.vec a]) ++ .plain (.vecConvert sh₁ sh₂ op) :: rest) Q := by
  obtain ⟨r₀, h₀⟩ := hp
  refine Wp.vectorAll (by simp [famOf]) ⟨_, .vecConvert h₀⟩ fun is' hv => ?_
  obtain ⟨r, hr, rfl⟩ := vec_convert hv
  simpa using h r hr

end Rules

end Silmaril.Wasm.Logic.Hoare
