module

public import Silmaril.Wasm.Numerics.Float
public import Silmaril.Wasm.Numerics.Integer
public import Silmaril.Wasm.Numerics.Relaxed

@[expose] public section

/-! # Execution profiles: `$ND`, relaxed choices, NaN policy, grow policy

The spec (§1.0, §3.0) leaves four things to the implementation:

* `$ND : bool` (builtin): whether relaxed operators may use their
  non-deterministic alternatives;
* the relaxed choice constants `$R_fmadd`, `$R_fmin`, `$R_fmax`, `$R_idot`,
  `$R_iq15mulr`, `$R_trunc_u`, `$R_trunc_s`, `$R_swizzle`, `$R_laneselect`
  (builtins, fixed per implementation);
* NaN payloads: float operators return *sets* of results (`$fadd_ … : fN*`);
* `memory.grow`/`table.grow` may fail at any time (`…-fail` rules have no premise).

`Profile` packages all four. The spec semantics is `Profile.spec nd R`
(`nan := .spec`, `grow := .nondet`): every rule of the spec is available, for the
given builtins. The *deterministic profile* of the spec appendix (and of the
single-threaded layer) is `Profile.deterministic o`: `$ND = false`, canonical
NaNs, and grow failure decided by an explicit oracle `o`.
-/

namespace Silmaril.Wasm.Numerics

/-- How float results are chosen. -/
inductive NaNPolicy where
  /-- The spec's result sets (`floatUnOpRel`, `floatBinOpRel`, `convertRel`). -/
  | spec
  /-- The deterministic function (canonical NaN results). -/
  | canonical
  deriving DecidableEq, Repr

-- `RelaxedChoice` (the builtins `$R_*`) and `relaxed2`/`relaxed4` are in `Numerics/Relaxed.lean`.

/-- Which resizing instruction is growing. -/
inductive GrowKind where
  | memory | table
  deriving DecidableEq, Repr

/-- How `memory.grow`/`table.grow` choose between success and failure. -/
inductive GrowPolicy where
  /-- The spec: failure is always possible, success when the new size is valid. -/
  | nondet
  /-- Deterministic: `oracle kind address size delta = true` forces failure;
  otherwise the instruction succeeds whenever the new size is valid. -/
  | oracle (decideFail : GrowKind → Nat → Nat → Nat → Bool)

structure Profile where
  /-- `$ND`. -/
  nd : Bool
  /-- `$R_*`. -/
  relaxed : RelaxedChoice := {}
  nan : NaNPolicy := .spec
  grow : GrowPolicy := .nondet

namespace Profile

/-- The spec semantics for given builtins `$ND` and `$R_*`. -/
def spec (nd : Bool := true) (r : RelaxedChoice := {}) : Profile := ⟨nd, r, .spec, .nondet⟩

/-- The deterministic profile with a grow oracle. -/
def deterministic (o : GrowKind → Nat → Nat → Nat → Bool) : Profile :=
  ⟨false, {}, .canonical, .oracle o⟩

/-- May a grow of `delta` at `address` (current size `size`) fail? -/
def growMayFail (P : Profile) (k : GrowKind) (address size delta : Nat) : Prop :=
  match P.grow with
  | .nondet => True
  | .oracle o => o k address size delta = true

/-- May a (valid) grow succeed? -/
def growMaySucceed (P : Profile) (k : GrowKind) (address size delta : Nat) : Prop :=
  match P.grow with
  | .nondet => True
  | .oracle o => o k address size delta = false

instance (P : Profile) (k : GrowKind) (a s d : Nat) : Decidable (P.growMayFail k a s d) := by
  unfold growMayFail; split <;> infer_instance

instance (P : Profile) (k : GrowKind) (a s d : Nat) : Decidable (P.growMaySucceed k a s d) := by
  unfold growMaySucceed; split <;> infer_instance

end Profile

/-! ## Profile-aware scalar float numerics -/

def floatUnOpP (P : Profile) (t : FloatType) (op : FloatUnOp) (x z : FloatValue t) : Prop :=
  match P.nan with
  | .spec => floatUnOpRel t op x z
  | .canonical => z = floatUnOp t op x

def floatBinOpP (P : Profile) (t : FloatType) (op : FloatBinOp) (x y z : FloatValue t) : Prop :=
  match P.nan with
  | .spec => floatBinOpRel t op x y z
  | .canonical => z = floatBinOp t op x y

def convertP (P : Profile) (op : ConvertOp) (x : NumValue op.source)
    (r : Except FloatTrap (NumValue op.target)) : Prop :=
  match P.nan with
  | .spec => convertRel op x r
  | .canonical => r = convert op x

/-- The canonical profile is a refinement of the spec's NaN sets. -/
theorem floatUnOpP_canonical_spec {P : Profile} {t : FloatType} {op : FloatUnOp}
    {x z : FloatValue t} (h : P.nan = .canonical) (hz : floatUnOpP P t op x z) :
    floatUnOpP { P with nan := .spec } t op x z := by
  simp only [floatUnOpP, h] at hz
  subst hz
  exact floatUnOpRel_self t op x

theorem floatBinOpP_canonical_spec {P : Profile} {t : FloatType} {op : FloatBinOp}
    {x y z : FloatValue t} (h : P.nan = .canonical) (hz : floatBinOpP P t op x y z) :
    floatBinOpP { P with nan := .spec } t op x y z := by
  simp only [floatBinOpP, h] at hz
  subst hz
  exact floatBinOpRel_self t op x y

theorem convertP_canonical_spec {P : Profile} {op : ConvertOp} {x : NumValue op.source}
    {r : Except FloatTrap (NumValue op.target)} (h : P.nan = .canonical) (hr : convertP P op x r) :
    convertP { P with nan := .spec } op x r := by
  simp only [convertP, h] at hr
  subst hr
  exact convertRel_self op x

/-! ## Non-emptiness obligations (why the float `unop-trap`/`binop-trap` rules are omitted)

The spec's float `unop-trap`/`binop-trap` rules fire when the result *set* is
empty. These lemmas record that it never is, for every profile, so progress does
not rely on an unstated fact. -/

theorem floatUnOpP_nonempty (P : Profile) (t : FloatType) (op : FloatUnOp) (x : FloatValue t) :
    ∃ z, floatUnOpP P t op x z := by
  unfold floatUnOpP
  cases P.nan
  · exact ⟨_, floatUnOpRel_self t op x⟩
  · exact ⟨_, rfl⟩

theorem floatBinOpP_nonempty (P : Profile) (t : FloatType) (op : FloatBinOp)
    (x y : FloatValue t) : ∃ z, floatBinOpP P t op x y z := by
  unfold floatBinOpP
  cases P.nan
  · exact ⟨_, floatBinOpRel_self t op x y⟩
  · exact ⟨_, rfl⟩

theorem convertP_nonempty (P : Profile) (op : ConvertOp) (x : NumValue op.source) :
    ∃ r, convertP P op x r := by
  unfold convertP
  cases P.nan
  · exact ⟨_, convertRel_self op x⟩
  · exact ⟨_, rfl⟩

end Silmaril.Wasm.Numerics
