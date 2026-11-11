module

public import Silmaril.Proofs.Wasm.Logic.Instr.Det

/-!
# Instruction rules: parametric, variable, numeric and reference instructions

Each rule is derived from the generic family rules of
`Silmaril.Proofs.Wasm.Logic.Instr.Det` and holds in both readings (`Wp m`, for
`m = .part` partial correctness and `m = .total` total correctness), in every
profile and for every host relation.

* Deterministic instructions (`Wp.det`): `nop`, `unreachable`, `drop`, `select`,
  `local.get/set/tee`, `global.get/set`, integer unary/binary/test/relational
  operations (binary ones may trap), float relational operations, and all
  reference instructions (`ref.null`, `ref.func`, `ref.is_null`,
  `ref.as_non_null`, `ref.eq`, `ref.test`, `ref.cast`, `ref.i31`, `i31.get`,
  `extern.convert_any`, `any.convert_extern`).
* Nondeterministic instructions (`Wp.fam`, quantifying over every result the
  profile allows): float unary and binary operations (`floatUnOpP`,
  `floatBinOpP`: NaN payloads) and conversions (`convertP`, with traps).

A Silmaril addition; the step rules are silmaril-lean's
(`Silmaril/Wasm/Execution/Core/Step/{Parametric,Variable,Numeric,Reference}.lean`).
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

/-! ## Parametric instructions -/

/-- **`nop`.** -/
theorem Wp.nop (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals us ++ .plain .nop :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (res := []) (rest := rest) fam_ok (by trivial)
    (.parametric .nop) (by simpa using h)

/-- **`unreachable`** traps. -/
theorem Wp.unreachable (hq : Q s f .trap) :
    Wp m P host s f (vals us ++ .plain .unreachable :: rest) Q := by
  simpa using Wp.detTrap (us := us) (args := []) (rest := rest) fam_ok (by trivial)
    (.parametric .unreachable) hq

/-- **`drop`.** -/
theorem Wp.drop {v : Val} (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v]) ++ .plain .drop :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.parametric (.drop v)) (by simpa using h)

/-- **`select`** with a nonzero condition keeps the first operand. -/
theorem Wp.selectTrue {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List ValType)} (hc : c ≠ 0)
    (h : Wp m P host s f (vals (us ++ [v₁]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v₁, v₂, .i32 c]) ++ .plain (.select ts) :: rest) Q :=
  Wp.detVals (res := [v₁]) fam_ok (by trivial)
    (.parametric (.selectTrue (v₁ := v₁) (v₂ := v₂) (ts := ts) hc)) h

/-- **`select`** with a zero condition keeps the second operand. -/
theorem Wp.selectFalse {v₁ v₂ : Val} {ts : Option (List ValType)}
    (h : Wp m P host s f (vals (us ++ [v₂]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v₁, v₂, .i32 0]) ++ .plain (.select ts) :: rest) Q :=
  Wp.detVals (res := [v₂]) fam_ok (by trivial) (.parametric (.selectFalse v₁ v₂ ts)) h

/-! ## Locals and globals -/

/-- **`local.get`.** -/
theorem Wp.localGet {x : LocalIdx} {v : Val} (hv : f.local? x = some (some v))
    (h : Wp m P host s f (vals (us ++ [v]) ++ rest) Q) :
    Wp m P host s f (vals us ++ .plain (.localGet x) :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (res := [v]) (rest := rest) fam_ok (by trivial)
    (.variable (.localGet hv)) h

/-- **`local.set`.** -/
theorem Wp.localSet {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length)
    (h : Wp m P host s (f.setLocal x v) (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v]) ++ .plain (.localSet x) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.variable (.localSet hx)) (by simpa using h)

/-- **`local.tee`**: duplicates the operand, then sets the local. -/
theorem Wp.localTee {x : LocalIdx} {v : Val}
    (h : Wp m P host s f (vals (us ++ [v, v]) ++ .plain (.localSet x) :: rest) Q) :
    Wp m P host s f (vals (us ++ [v]) ++ .plain (.localTee x) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.variable (.localTee (s := s) (f := f) (x := x) (v := v)))
    (by simpa using h)

/-- **`global.get`** (any global of the module, mutable or not). -/
theorem Wp.globalGet {x : GlobalIdx} {a : Nat} {g : GlobalInst} (hg : s.global? f x = some (a, g))
    (h : Wp m P host s f (vals (us ++ [g.value]) ++ rest) Q) :
    Wp m P host s f (vals us ++ .plain (.globalGet x) :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (res := [g.value]) (rest := rest) fam_ok (by trivial)
    (.variable (.globalGet hg)) h

/-- **`global.set`.** -/
theorem Wp.globalSet {x : GlobalIdx} {a : Nat} {g : GlobalInst} {v : Val}
    (hg : s.global? f x = some (a, g)) (h : Wp m P host (s.setGlobal a v) f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v]) ++ .plain (.globalSet x) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.variable (.globalSet hg)) (by simpa using h)

/-! ## Integer and float numerics -/

section Numeric

variable {t : IntType}

/-- **Integer unary operations** (`clz`, `ctz`, `popcnt`, sign extensions). -/
theorem Wp.intUnOp {op : IntUnOp} {x : BitVec t.width}
    (h : Wp m P host s f (vals (us ++ [.num ⟨.int t, Numerics.intUnOp t op x⟩]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.num ⟨.int t, x⟩]) ++ .plain (.intUnOp t op) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.numeric (.intUnOp (op := op) (x := x))) h

/-- **Integer binary operations** that do not trap. -/
theorem Wp.intBinOp {op : IntBinOp} {x y z : BitVec t.width} (hz : Numerics.intBinOp t op x y = .ok z)
    (h : Wp m P host s f (vals (us ++ [.num ⟨.int t, z⟩]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
      .plain (.intBinOp t op) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.numeric (.intBinOp hz)) h

/-- **Integer binary operations** that trap (division by zero, overflow). -/
theorem Wp.intBinOp_trap {op : IntBinOp} {x y : BitVec t.width} {e : IntTrap}
    (he : Numerics.intBinOp t op x y = .error e) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
      .plain (.intBinOp t op) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.numeric (.intBinOpTrap he)) hq

/-- **Integer test operations** (`eqz`). -/
theorem Wp.intTestOp {op : IntTestOp} {x : BitVec t.width}
    (h : Wp m P host s f (vals (us ++ [.i32 (Numerics.intTestOp t op x)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.num ⟨.int t, x⟩]) ++ .plain (.intTestOp t op) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.numeric (.intTestOp (op := op) (x := x))) h

/-- **Integer comparisons.** -/
theorem Wp.intRelOp {op : IntRelOp} {x y : BitVec t.width}
    (h : Wp m P host s f (vals (us ++ [.i32 (Numerics.intRelOp t op x y)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
      .plain (.intRelOp t op) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.numeric (.intRelOp (op := op) (x := x) (y := y))) h

/-- **Float comparisons** (deterministic). -/
theorem Wp.floatRelOp {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width}
    (h : Wp m P host s f (vals (us ++ [.i32 (Numerics.floatRelOp t op x y)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.num ⟨.float t, x⟩, .num ⟨.float t, y⟩]) ++
      .plain (.floatRelOp t op) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.numeric (.floatRelOp (op := op) (x := x) (y := y))) h

/-- Close a family case whose instruction is not the one at hand. -/
local macro "last_absurd " hl:ident : tactic => `(tactic| (
  have h₂ := congrArg List.getLast? $hl
  simp [vals, Val.toAdmin] at h₂))

theorem num_floatUnOp {t : FloatType} {op : FloatUnOp} {x : BitVec t.width} {r : List Admin}
    (h : NumericStep P (vals [.num ⟨.float t, x⟩] ++ [.plain (.floatUnOp t op)]) r) :
    ∃ z, floatUnOpP P t op x z ∧ r = vals [.num ⟨.float t, z⟩] := by
  generalize hl : vals [Val.num ⟨.float t, x⟩] ++ [Admin.plain (.floatUnOp t op)] = l at h
  cases h
  case floatUnOp z hz =>
    cases hl
    exact ⟨z, hz, rfl⟩
  all_goals last_absurd hl

theorem num_floatBinOp {t : FloatType} {op : FloatBinOp} {x y : BitVec t.width} {r : List Admin}
    (h : NumericStep P (vals [.num ⟨.float t, x⟩, .num ⟨.float t, y⟩] ++
      [.plain (.floatBinOp t op)]) r) :
    ∃ z, floatBinOpP P t op x y z ∧ r = vals [.num ⟨.float t, z⟩] := by
  generalize hl : vals [Val.num ⟨.float t, x⟩, .num ⟨.float t, y⟩] ++
    [Admin.plain (.floatBinOp t op)] = l at h
  cases h
  case floatBinOp z hz =>
    cases hl
    exact ⟨z, hz, rfl⟩
  all_goals last_absurd hl

theorem num_convert {op : ConvertOp} {x : BitVec op.source.width} {r : List Admin}
    (h : NumericStep P (vals [.num ⟨op.source, x⟩] ++ [.plain (.convert op)]) r) :
    (∃ z, convertP P op x (.ok z) ∧ r = vals [.num ⟨op.target, z⟩]) ∨
      (∃ e, convertP P op x (.error e) ∧ r = [.trap]) := by
  generalize hl : vals [Val.num ⟨op.source, x⟩] ++ [Admin.plain (.convert op)] = l at h
  cases h
  case convert x' z hz =>
    simp [vals] at hl
    obtain ⟨hx, rfl⟩ := hl
    obtain rfl : x = x' := by simpa using hx
    exact .inl ⟨z, hz, rfl⟩
  case convertTrap x' e he =>
    simp [vals] at hl
    obtain ⟨hx, rfl⟩ := hl
    obtain rfl : x = x' := by simpa using hx
    exact .inr ⟨e, he, rfl⟩
  all_goals last_absurd hl

/-- **Float unary operations**, every result the profile allows (NaN choices). -/
theorem Wp.floatUnOp {t : FloatType} {op : FloatUnOp} {x : BitVec t.width}
    (h : ∀ z, floatUnOpP P t op x z →
      Wp m P host s f (vals (us ++ [.num ⟨.float t, z⟩]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.num ⟨.float t, x⟩]) ++ .plain (.floatUnOp t op) :: rest) Q := by
  obtain ⟨z₀, hz₀⟩ := floatUnOpP_nonempty P t op x
  refine Wp.fam fam_ok ⟨_, .numeric (.floatUnOp hz₀)⟩ fun c₀ hh => ?_
  obtain ⟨is', hn, rfl⟩ := hh.fam_inv fam_ok
  obtain ⟨z, hz, rfl⟩ := num_floatUnOp hn
  simpa using h z hz

/-- **Float binary operations**, every result the profile allows (NaN choices). -/
theorem Wp.floatBinOp {t : FloatType} {op : FloatBinOp} {x y : BitVec t.width}
    (h : ∀ z, floatBinOpP P t op x y z →
      Wp m P host s f (vals (us ++ [.num ⟨.float t, z⟩]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.num ⟨.float t, x⟩, .num ⟨.float t, y⟩]) ++
      .plain (.floatBinOp t op) :: rest) Q := by
  obtain ⟨z₀, hz₀⟩ := floatBinOpP_nonempty P t op x y
  refine Wp.fam fam_ok ⟨_, .numeric (.floatBinOp hz₀)⟩ fun c₀ hh => ?_
  obtain ⟨is', hn, rfl⟩ := hh.fam_inv fam_ok
  obtain ⟨z, hz, rfl⟩ := num_floatBinOp hn
  simpa using h z hz

/-- **Conversions**, every result the profile allows, including traps (float to
integer truncation out of range). -/
theorem Wp.convert {op : ConvertOp} {x : BitVec op.source.width}
    (hok : ∀ z, convertP P op x (.ok z) →
      Wp m P host s f (vals (us ++ [.num ⟨op.target, z⟩]) ++ rest) Q)
    (htrap : ∀ e, convertP P op x (.error e) → Q s f .trap) :
    Wp m P host s f (vals (us ++ [.num ⟨op.source, x⟩]) ++ .plain (.convert op) :: rest) Q := by
  have hp : ∃ c₀, Head P s f [.num ⟨op.source, x⟩] (.plain (.convert op)) c₀ := by
    obtain ⟨r, hr⟩ := convertP_nonempty P op x
    rcases r with e | z
    · exact ⟨_, .numeric (.convertTrap hr)⟩
    · exact ⟨_, .numeric (.convert hr)⟩
  refine Wp.fam fam_ok hp fun c₀ hh => ?_
  obtain ⟨is', hn, rfl⟩ := hh.fam_inv fam_ok
  rcases num_convert hn with ⟨z, hz, rfl⟩ | ⟨e, he, rfl⟩
  · simpa using hok z hz
  · simpa using Wp.trap (m := m) (P := P) (host := host) (us := us) (rest := rest) (htrap e he)

end Numeric

/-! ## References -/

section Ref

variable {r : Ref}

/-- **`ref.null`.** -/
theorem Wp.refNull {ht : HeapType} (h : Wp m P host s f (vals (us ++ [.ref .null]) ++ rest) Q) :
    Wp m P host s f (vals us ++ .plain (.refNull ht) :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (res := [.ref .null]) (rest := rest) fam_ok
    (by trivial) (.reference (.refNull ht)) h

/-- **`ref.func`.** -/
theorem Wp.refFunc {x : FuncIdx} {a : Nat} (hx : f.module.funcs[x.toNat]? = some a)
    (h : Wp m P host s f (vals (us ++ [.ref (.func a)]) ++ rest) Q) :
    Wp m P host s f (vals us ++ .plain (.refFunc x) :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (res := [.ref (.func a)]) (rest := rest) fam_ok
    (by trivial) (.reference (.refFunc hx)) h

/-- **`ref.i31`.** -/
theorem Wp.refI31 {i : BitVec 32}
    (h : Wp m P host s f (vals (us ++ [.ref (.i31 (i.setWidth 31))]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.i32 i]) ++ .plain .refI31 :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference (.refI31 i)) h

/-- **`ref.is_null`** on a null reference. -/
theorem Wp.refIsNull_null (h : Wp m P host s f (vals (us ++ [.i32 1]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref .null]) ++ .plain .refIsNull :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference .isNullTrue) h

/-- **`ref.is_null`** on a non-null reference. -/
theorem Wp.refIsNull_ne (hr : r ≠ .null) (h : Wp m P host s f (vals (us ++ [.i32 0]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain .refIsNull :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference (.isNullFalse hr)) h

/-- **`ref.as_non_null`** on a null reference traps. -/
theorem Wp.refAsNonNull_null (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null]) ++ .plain .refAsNonNull :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.reference .asNonNullNull) hq

/-- **`ref.as_non_null`** on a non-null reference. -/
theorem Wp.refAsNonNull (hr : r ≠ .null) (h : Wp m P host s f (vals (us ++ [.ref r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain .refAsNonNull :: rest) Q :=
  Wp.detVals (res := [.ref r]) fam_ok (by trivial) (.reference (.asNonNullAddr hr)) h

/-- **`ref.eq`** on two null references. -/
theorem Wp.refEq_null (h : Wp m P host s f (vals (us ++ [.i32 1]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref .null, .ref .null]) ++ .plain .refEq :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference .eqNull) h

/-- **`ref.eq`** on a non-null reference and itself. -/
theorem Wp.refEq_self (hr : r ≠ .null) (h : Wp m P host s f (vals (us ++ [.i32 1]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r, .ref r]) ++ .plain .refEq :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference (.eqTrue hr)) h

/-- **`ref.eq`** on two different references. -/
theorem Wp.refEq_ne {r₁ r₂ : Ref} (hr : r₁ ≠ r₂)
    (h : Wp m P host s f (vals (us ++ [.i32 0]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r₁, .ref r₂]) ++ .plain .refEq :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference (.eqFalse hr)) h

/-- **`ref.test`** that succeeds. -/
theorem Wp.refTest_true {rt : RefType} (hr : RefOk s r (f.module.instRef rt))
    (h : Wp m P host s f (vals (us ++ [.i32 1]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.refTest rt) :: rest) Q :=
  Wp.detVals (res := [.i32 1]) fam_ok (by trivial) (.reference (.testTrue hr)) h

/-- **`ref.test`** that fails. -/
theorem Wp.refTest_false {rt : RefType} (hr : ¬ RefOk s r (f.module.instRef rt))
    (h : Wp m P host s f (vals (us ++ [.i32 0]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.refTest rt) :: rest) Q :=
  Wp.detVals (res := [.i32 0]) fam_ok (by trivial) (.reference (.testFalse hr)) h

/-- **`ref.cast`** that succeeds. -/
theorem Wp.refCast {rt : RefType} (hr : RefOk s r (f.module.instRef rt))
    (h : Wp m P host s f (vals (us ++ [.ref r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.refCast rt) :: rest) Q :=
  Wp.detVals (res := [.ref r]) fam_ok (by trivial) (.reference (.castSucceed hr)) h

/-- **`ref.cast`** that fails traps. -/
theorem Wp.refCast_fail {rt : RefType} (hr : ¬ RefOk s r (f.module.instRef rt))
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.refCast rt) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.reference (.castFail hr)) hq

/-- **`i31.get`** on a null reference traps. -/
theorem Wp.i31Get_null {sx : Signedness} (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null]) ++ .plain (.i31Get sx) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.reference (.i31GetNull sx)) hq

/-- **`i31.get`** on an `i31` reference. -/
theorem Wp.i31Get {sx : Signedness} {i : BitVec 31}
    (h : Wp m P host s f (vals (us ++ [.i32 (match sx with
      | .signed => i.signExtend 32 | .unsigned => i.setWidth 32)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.i31 i)]) ++ .plain (.i31Get sx) :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference (.i31GetNum sx i)) h

/-- **`extern.convert_any`** on a null reference. -/
theorem Wp.externConvertAny_null (h : Wp m P host s f (vals (us ++ [.ref .null]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref .null]) ++ .plain .externConvertAny :: rest) Q :=
  Wp.detVals (res := [.ref .null]) fam_ok (by trivial) (.reference .externConvertNull) h

/-- **`extern.convert_any`** on a non-null reference. -/
theorem Wp.externConvertAny (hr : r ≠ .null)
    (h : Wp m P host s f (vals (us ++ [.ref (.extern r)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain .externConvertAny :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference (.externConvertAddr hr)) h

/-- **`any.convert_extern`** on a null reference. -/
theorem Wp.anyConvertExtern_null (h : Wp m P host s f (vals (us ++ [.ref .null]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref .null]) ++ .plain .anyConvertExtern :: rest) Q :=
  Wp.detVals (res := [.ref .null]) fam_ok (by trivial) (.reference .anyConvertNull) h

/-- **`any.convert_extern`** on an external reference. -/
theorem Wp.anyConvertExtern (h : Wp m P host s f (vals (us ++ [.ref r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.extern r)]) ++ .plain .anyConvertExtern :: rest) Q :=
  Wp.detVals fam_ok (by trivial) (.reference (.anyConvertAddr r)) h

end Ref

end Silmaril.Wasm.Logic.Hoare
