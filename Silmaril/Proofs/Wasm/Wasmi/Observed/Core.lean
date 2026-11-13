module

public import Silmaril.Proofs.Wasm.Wasmi.Observed.Run
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Every Core 3.0 run of a rounding function (proofs)

`floatUnOp_valid`: in every profile and for every host, every run of the call `a x` of a
function `local.get 0; t.op` (`RoundFn`) that returns values returns `t.const z` with `z` a
result the profile allows for `t.op x`. This is a specification of the every-run logic
(`Silmaril.Wasm.Logic.Hoare`), proved from the body (`FSpecAt.of_body`) with the rules for
`local.get` and for a float unary operator (`HWP.floatUnOp`, below, an instance of the head rule
with an inversion of the numeric family). `core_returns_iff` reads it on Core observations.

New proofs; the inversion follows `Silmaril.Wasm.Logic.Hoare`'s `head_intBinOp`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi.Observed Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Compute both sides of a first-non-value equation. -/
local macro "fnv_simp " h:ident : tactic => `(tactic| (
  try simp only [SingleThreaded.Det.fnv_toAdmin_cons, SingleThreaded.Det.fnv_ref_cons, constI32,
    SingleThreaded.Det.fnv_vals_append, aconst, fnv_intConst_cons] at $h:ident
  simp [SingleThreaded.Det.fnv, Admin.val?] at $h:ident))

/-- Close a family case of another instruction. -/
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

/-! ## The rule for float unary operators -/

theorem num_floatUnOp {args : List Val} {t : FloatType} {op : FloatUnOp} {is' : List Admin}
    (h : NumericStep P (vals args ++ [.plain (.floatUnOp t op)]) is') :
    ∃ x z : FloatValue t, args = [.num ⟨.float t, x⟩] ∧ floatUnOpP P t op x z ∧
      is' = [.plain (.floatConst t z)] := by
  generalize hc : vals args ++ [.plain (.floatUnOp t op)] = c at h
  cases h with
  | floatUnOp hz =>
    have h₁ := fnv_eq_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    exact ⟨_, _, rfl, hz, rfl⟩
  | _ => fam_code hc

theorem head_floatUnOp {s : Store H} {f : Frame} {args : List Val} {t : FloatType}
    {op : FloatUnOp} {c₀ : Config H} (h : Head P s f args (.plain (.floatUnOp t op)) c₀) :
    ∃ x z : FloatValue t, args = [.num ⟨.float t, x⟩] ∧ floatUnOpP P t op x z ∧
      c₀ = ⟨s, f, [.plain (.floatConst t z)]⟩ := by
  cases h with
  | numeric h =>
    obtain ⟨x, z, rfl, hz, rfl⟩ := num_floatUnOp h
    exact ⟨x, z, rfl, hz, rfl⟩
  | _ => head_absurd

/-- **Float unary operators**, every result the profile allows. -/
theorem HWP.floatUnOp {s : Store H} {f : Frame} {vs : List Val} {t : FloatType}
    {op : FloatUnOp} {x : FloatValue t} {rest : List Admin} {Q : Post H}
    (h : ∀ z, floatUnOpP P t op x z →
      HWP P host s f (vals vs ++ .plain (.floatConst t z) :: rest) Q) :
    HWP P host s f (vals (vs ++ [.num ⟨.float t, x⟩]) ++ .plain (.floatUnOp t op) :: rest) Q := by
  obtain ⟨z₀, hz₀⟩ := floatUnOpP_nonempty P t op x
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨vs, _, _, rfl, .numeric (.floatUnOp hz₀)⟩ ?_
  intro vs' args c₀ hW hh
  obtain ⟨x', z, rfl, hz, rfl⟩ := head_floatUnOp hh
  obtain ⟨rfl, hx⟩ := split_one hW
  have hx' : x' = x := by
    injection hx with hx
    injection hx
  subst hx'
  simpa using h z hz

/-! ## The specification of a rounding function -/

/-- The specification of `a x`: every normal outcome is `t.const z` for an allowed `z`. -/
def roundSpec (s : Store H) (t : FloatType) (op : FloatUnOp) (x : FloatValue t) : FSpec H where
  pre s' args := s' = s ∧ args = [fval t x]
  post _ _ _ o := ∃ z, floatUnOpP P t op x z ∧ o = .normal [fval t z]

namespace RoundFn

variable {s : Store H} {a : Nat} {t : FloatType} {op : FloatUnOp} (R : RoundFn s a t op)

/-- The body meets the specification. -/
theorem body_hwp (x : FloatValue t) (n : Nat) (f : Frame) (vs₀ : List Val) :
    HWP P host s (R.frame x) (expression R.code.body)
      (bodyPostK P host R.rs.length f vs₀
        (callPost f vs₀ ((roundSpec (P := P) s t op x).post s [fval t x])) n) := by
  have hb : expression R.code.body =
      vals [] ++ .plain (.localGet ⟨0⟩) :: [.plain (.floatUnOp t op)] := by
    rw [R.hbody]
    rfl
  rw [hb]
  refine HWP.localGet (R.local0 x) (HWP.floatUnOp (vs := []) fun z hz => ?_)
  refine HWP.of_vals (vs := [fval t z]) ?_
  exact ⟨by simp [R.hrs], rfl, .inl ⟨[fval t z], by simp, z, hz, rfl⟩⟩

include R in
/-- **The specification holds** in every profile and for every host. -/
theorem valid (x : FloatValue t) :
    FSpecValid P host a (roundSpec (P := P) s t op x) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n _ =>
    refine FSpecAt.of_body (fi := R.fi) (fun _ _ h => h.1 ▸ R.hf) R.hcode R.he
      (fun _ _ h => by simp [h.2, R.hps]) fun s' args hpre f vs₀ => ?_
    obtain ⟨rfl, rfl⟩ := hpre
    exact R.body_hwp x n f vs₀ n

include R in
/-- **Every Core value result of `a x` is an allowed result of `t.op x`**, and every allowed
result is a Core observation. -/
theorem core_returns_iff (x : FloatValue t) (vs : List Val) :
    Behaviour.returns vs ∈ Core.obs P (s, host) (a, [fval t x]) ↔
      ∃ z, floatUnOpP P t op x z ∧ vs = [fval t z] := by
  constructor
  · rintro (⟨c', r, hs, hc, hb⟩ | ⟨hb, -⟩)
    · cases r with
      | values vs' =>
        obtain rfl : vs = vs' := by simpa using hb
        obtain ⟨s', f', code'⟩ := c'
        obtain rfl : code' = vals vs := hc
        obtain ⟨z, hz, ho⟩ := FSpecValid.invoke_vals (R.valid (P := P) (host := host) (op := op) x)
          ⟨rfl, rfl⟩ hs
        exact ⟨z, hz, by injection ho⟩
      | throw _ => cases hb
      | trap => cases hb
    · cases hb
  · rintro ⟨z, hz, rfl⟩
    exact .inl ⟨_, .values [fval t z], R.core_run hz, rfl, rfl⟩

end RoundFn

end Silmaril.Proofs.Wasm.Wasmi.Observed
