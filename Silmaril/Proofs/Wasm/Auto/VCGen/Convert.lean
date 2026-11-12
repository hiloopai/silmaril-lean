module

public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# The every-run rule for integer conversions

`HWP.convertInt`: a conversion `op` whose result relation is the function `convert op` in the
profile at hand (`i32.wrap_i64`, `i64.extend_i32_s`, `i64.extend_i32_u` in every profile:
`convertP_wrap`, `convertP_extend`) that does not trap continues with its result, for every run.
An instance of `Silmaril.Wasm.Logic.Hoare.HWP.head` with an inversion of the conversion's head step
(the pattern of the integer binary-operator rule `HWP.intBinOp`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.VCGen

open Silmaril.Wasm
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Logic.Hoare (HWP fnv_eq_split)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Compute both sides of a first-non-value equation. -/
local macro "fnv_simp " h:ident : tactic => `(tactic| (
  try simp only [SingleThreaded.Det.fnv_toAdmin_cons, SingleThreaded.Det.fnv_ref_cons, constI32,
    SingleThreaded.Det.fnv_vals_append, aconst, Silmaril.Wasm.Logic.Hoare.fnv_intConst_cons]
    at $h:ident
  simp [SingleThreaded.Det.fnv, Admin.val?] at $h:ident))

local macro "fam_code " h:ident : tactic => `(tactic| (
  have h₁ := fnv_eq_split $h rfl
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

theorem num_convert {args : List Val} {op : ConvertOp} {is' : List Admin}
    (h : NumericStep P (vals args ++ [.plain (.convert op)]) is') :
    ∃ x : BitVec op.source.width, args = [.num ⟨op.source, x⟩] ∧
      ((∃ z, convertP P op x (.ok z) ∧ is' = [(Val.num ⟨op.target, z⟩).toAdmin]) ∨
        (∃ e, convertP P op x (.error e) ∧ is' = [.trap])) := by
  generalize hc : vals args ++ [.plain (.convert op)] = c at h
  cases h with
  | convert hz =>
    have h₁ := fnv_eq_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, rfl, .inl ⟨_, hz, rfl⟩⟩
  | convertTrap he =>
    have h₁ := fnv_eq_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, rfl, .inr ⟨_, he, rfl⟩⟩
  | _ => fam_code hc

theorem head_convert {s : Store H} {f : Frame} {args : List Val} {op : ConvertOp}
    {c₀ : Config H} (h : Head P s f args (.plain (.convert op)) c₀) :
    ∃ x : BitVec op.source.width, args = [.num ⟨op.source, x⟩] ∧
      ((∃ z, convertP P op x (.ok z) ∧ c₀ = ⟨s, f, [(Val.num ⟨op.target, z⟩).toAdmin]⟩) ∨
        (∃ e, convertP P op x (.error e) ∧ c₀ = ⟨s, f, [.trap]⟩)) := by
  cases h with
  | numeric h =>
    obtain ⟨x, rfl, ⟨z, hz, rfl⟩ | ⟨e, he, rfl⟩⟩ := num_convert h
    · exact ⟨x, rfl, .inl ⟨z, hz, rfl⟩⟩
    · exact ⟨x, rfl, .inr ⟨e, he, rfl⟩⟩
  | _ => head_absurd

theorem numVal_inj {t : NumType} {x y : BitVec t.width} (h : (⟨t, x⟩ : NumVal) = ⟨t, y⟩) :
    x = y := by
  injection h

/-- **A non-trapping conversion whose result is a function of its argument**, every run. -/
theorem HWP.convertInt {s : Store H} {f : Frame} {vs : List Val} {op : ConvertOp}
    {x : BitVec op.source.width} {z : BitVec op.target.width} {rest : List Admin} {Q : Post H}
    (hP : ∀ r, convertP P op x r ↔ r = Silmaril.Wasm.Numerics.convert op x)
    (hz : Silmaril.Wasm.Numerics.convert op x = .ok z)
    (h : HWP P host s f (vals (vs ++ [.num ⟨op.target, z⟩]) ++ rest) Q) :
    HWP P host s f (vals (vs ++ [.num ⟨op.source, x⟩]) ++ .plain (.convert op) :: rest) Q := by
  have hp : ∃ vs' args c₀, vs ++ [Val.num ⟨op.source, x⟩] = vs' ++ args ∧
      Head P s f args (.plain (.convert op)) c₀ :=
    ⟨vs, _, _, rfl, .numeric (.convert ((hP _).2 hz.symm))⟩
  refine Silmaril.Wasm.Logic.Hoare.HWP.head ⟨rfl, by simp, rfl⟩ hp ?_
  intro vs' args c₀ hW hh
  obtain ⟨x', rfl, hc⟩ := head_convert hh
  obtain ⟨rfl, hv⟩ := SingleThreaded.Det.append_singleton_inj.mp hW
  have hx : x = x' := numVal_inj (Val.num.inj hv)
  subst hx
  rcases hc with ⟨z', hz', rfl⟩ | ⟨e, he, rfl⟩
  · have hzz : z' = z := by
      have := ((hP _).1 hz').trans hz
      injection this
    subst hzz
    simpa [vals] using h
  · have := ((hP _).1 he).trans hz
    cases this

theorem convertP_wrap {x : NumValue ConvertOp.wrap.source}
    (r : Except FloatTrap (NumValue ConvertOp.wrap.target)) :
    convertP P .wrap x r ↔ r = Silmaril.Wasm.Numerics.convert .wrap x := by
  unfold convertP
  split <;> (cases r <;> exact Iff.rfl)

theorem convertP_extend {sx : Signedness} {x : NumValue (ConvertOp.extend sx).source}
    (r : Except FloatTrap (NumValue (ConvertOp.extend sx).target)) :
    convertP P (.extend sx) x r ↔ r = Silmaril.Wasm.Numerics.convert (.extend sx) x := by
  unfold convertP
  split <;> (cases r <;> exact Iff.rfl)

/-- **`i32.wrap_i64`**, every run. -/
theorem HWP.wrap {s : Store H} {f : Frame} {vs : List Val} {x : BitVec 64} {rest : List Admin}
    {Q : Post H} (h : HWP P host s f (vals (vs ++ [.num ⟨.int .i32, x.setWidth 32⟩]) ++ rest) Q) :
    HWP P host s f (vals (vs ++ [.num ⟨.int .i64, x⟩]) ++ .plain (.convert .wrap) :: rest) Q :=
  HWP.convertInt (op := .wrap) (x := x) convertP_wrap rfl h

/-- **`i64.extend_i32_s`/`i64.extend_i32_u`**, every run. -/
theorem HWP.extend {s : Store H} {f : Frame} {vs : List Val} {sx : Signedness} {x : BitVec 32}
    {rest : List Admin} {Q : Post H}
    (h : HWP P host s f (vals (vs ++ [.num ⟨.int .i64, match sx with
      | .signed => x.signExtend 64
      | .unsigned => x.setWidth 64⟩]) ++ rest) Q) :
    HWP P host s f (vals (vs ++ [.num ⟨.int .i32, x⟩]) ++ .plain (.convert (.extend sx)) :: rest)
      Q := by
  cases sx
  · exact HWP.convertInt (op := .extend .signed) (x := x) convertP_extend rfl h
  · exact HWP.convertInt (op := .extend .unsigned) (x := x) convertP_extend rfl h

end Silmaril.Proofs.Wasm.Auto.VCGen