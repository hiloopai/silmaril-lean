module

public import Silmaril.Proofs.Wasm.Logic.HoareExamples.Catch

/-!
# Example: a tail-recursive function

`loopSpec_valid`: a function whose body is `loopBody t x` (count the `i32`
argument down to zero by `return_call x`, a call of itself, then return `42`)
satisfies, in every profile and for every host, the specification "returns
`42` and leaves the store unchanged" (`loopSpec`). The proof is by Löb induction
on the step index (`FSpecAt.of_body` for `n + 1` steps from the specification
for `n` steps, used at the tail call through `framePostK_tail`). Termination is
not claimed (partial correctness).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.HoareExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The specification: from a store holding the function, on any `i32`, the call
returns `42` and does not change the store. -/
def loopSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ m : BitVec 32, args = [.i32 m]
  post s _ s' o := s' = s ∧ o = .normal [.i32 42]

section

variable {a : Nat} {fi : FuncInst H} {code : Func} {t : ValType} {x : FuncIdx}
  {ps rs : Ty (.list .val)}

theorem forCall_local0 (m : ModuleInst) (v : Val) (ls : List ValType) :
    (Frame.forCall m [v] ls).local? x0 = some (some v) := by
  simp [Frame.forCall, Frame.local?, x0, Idx.toNat]

/-- The `else` branch returns `42`. -/
theorem loop_else {n : Nat} {s : Store H} {F f : Frame} {vs₀ args : List Val}
    (hrs : rs.length = 1) :
    HWP P host s F (vals [] ++ .plain (.block (.value t) [.intConst .i32 42]) :: [])
      (bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s args)) n) := by
  have hq : bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s args)) n
      s F (.normal [.i32 42]) :=
    ⟨by simp [hrs], rfl, .inl ⟨[.i32 42], rfl, rfl, rfl⟩⟩
  have h₁ : HWP P host s F (vals [.i32 42] ++ [])
      (bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s args)) n) :=
    HWP.of_vals hq
  have h₂ : labelPost P host [F.module.instVal t].length [] [] (seqPost P host []
      (bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s args)) n))
      s F (.normal [.i32 42]) := h₁
  exact HWP.block (us := []) (vs := []) rfl rfl (HWP.of_vals h₂)

/-- The `then` branch decrements and calls itself in tail position. -/
theorem loop_then {n : Nat} {s : Store H} {f : Frame} {vs₀ : List Val} {m : BitVec 32}
    (hx : fi.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (ih : FSpecAt P host n a (loopSpec a fi)) :
    HWP P host s (Frame.forCall fi.module [.i32 m] code.locals)
      (vals [] ++ .plain (.block (.value t)
        [.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub, .returnCall x]) :: [])
      (bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s [.i32 m])) n) := by
  have htail : bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s [.i32 m])) n
      s (Frame.forCall fi.module [.i32 m] code.locals)
      (.tail ([] ++ [.i32 (m - 1)]) a (.returnCallRefType fi.type)) :=
    framePostK_tail (m := rs.length) (vs₁ := []) trivial hf he (by simp [hps]) ih ⟨hf, _, rfl⟩
      fun _ _ h => h
  have hcall : HWP P host s (Frame.forCall fi.module [.i32 m] code.locals)
      (vals [.i32 (m - 1)] ++ .plain (.returnCall x) :: [])
      (labelPost P host [fi.module.instVal t].length [] [] (seqPost P host []
        (bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s [.i32 m])) n))) :=
    HWP.returnCallIdx hx hf htail
  have hsub : HWP P host s (Frame.forCall fi.module [.i32 m] code.locals)
      (vals ([] ++ [Val.num ⟨.int .i32, m⟩, .num ⟨.int .i32, 1⟩]) ++
        .plain (.intBinOp .i32 .sub) :: [.plain (.returnCall x)]) _ :=
    HWP.intBinOp (fun z hz => by cases hz; exact hcall) fun e he => by cases he
  have hget : HWP P host s (Frame.forCall fi.module [.i32 m] code.locals)
      (vals [] ++ .plain (.localGet x0) ::
        [.plain (.intConst .i32 1), .plain (.intBinOp .i32 .sub), .plain (.returnCall x)]) _ :=
    HWP.localGet (forCall_local0 _ _ _) hsub
  exact HWP.block (us := []) (vs := []) rfl rfl hget

/-- The body satisfies the specification for `n` steps, given it for `n` steps. -/
theorem loop_body {n : Nat} {s : Store H} {args : List Val} {f : Frame} {vs₀ : List Val}
    (hcode : code.body = loopBody t x) (hx : fi.module.funcs[x.toNat]? = some a)
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1)
    (ih : FSpecAt P host n a (loopSpec a fi)) (hpre : (loopSpec a fi).pre s args) :
    HWP P host s (Frame.forCall fi.module args code.locals) (expression code.body)
      (bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s args)) n) := by
  obtain ⟨hf, m, rfl⟩ := hpre
  have hif : HWP P host s (Frame.forCall fi.module [.i32 m] code.locals)
      (vals ([] ++ [.i32 m]) ++ .plain (.if_ (.value t)
        [.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub, .returnCall x]
        [.intConst .i32 42]) :: []) _ :=
    HWP.if_ (Q := bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((loopSpec a fi).post s [.i32 m])) n)
      (fun _ => loop_then hx hf he hps ih) (fun _ => loop_else hrs)
  rw [hcode]
  exact HWP.localGet (vs := []) (forCall_local0 _ _ _) hif

/-- **The tail-recursive function meets its specification.** -/
theorem loopSpec_valid (hcode : fi.code = .wasm code) (hbody : code.body = loopBody t x)
    (hx : fi.module.funcs[x.toNat]? = some a) (he : Expand fi.type (.func ps rs))
    (hps : ps.length = 1) (hrs : rs.length = 1) :
    FSpecValid P host a (loopSpec a fi) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n ih =>
    refine FSpecAt.of_body (fun _ _ h => h.1) hcode he
      (fun _ _ ⟨_, _, h⟩ => by simp [h, hps]) fun s args hpre f vs₀ => ?_
    exact loop_body hbody hx he hps hrs ih hpre n

end

end Silmaril.Wasm.Logic.HoareExamples
