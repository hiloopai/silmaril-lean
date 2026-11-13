module

public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Execution.Core.Exec.ConstExprArity
public import Silmaril.Wasm.Execution.Core.Soundness.FrameRegularity
public import Silmaril.Wasm.SingleThreaded.Soundness

/-!
# Typed constant code evaluates

`offset_eval`: a validated constant expression of address type (`ExprOkConst C off a.valType`),
in a frame typed against `C` over a well-typed store, is evaluated by `evalConst?` to an address
constant, into a well-typed extension of the store. The proof runs Core reduction: a typed
configuration of constant code is terminal or steps (`Config.progress`), every step is a
constant-instruction redex (`Step.const_redex`) that decreases a weight of the code
(`ConstRedex.weight_lt`), the result is typed (`Step.preservation`); the run gives the
evaluator's result (`evalConst?_of_exprOkConst`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded

/-- The weight of a constant instruction: expanding instructions weigh two. -/
def instrW : Instr → Nat
  | .structNewDefault _ | .arrayNew _ | .arrayNewDefault _ => 2
  | _ => 1

/-- The weight of an administrative instruction: plain instructions weigh, values do not. -/
def adminW : Admin → Nat
  | .plain i => if (Admin.plain i).val?.isSome then 0 else instrW i
  | _ => 0

/-- The weight of code. -/
def codeW (l : List Admin) : Nat := (l.map adminW).sum

theorem codeW_append (a b : List Admin) : codeW (a ++ b) = codeW a + codeW b := by
  simp only [codeW, List.map_append, List.sum_append]

theorem codeW_cons (a : Admin) (b : List Admin) : codeW (a :: b) = adminW a + codeW b := by
  simp only [codeW, List.map_cons, List.sum_cons]

theorem adminW_val (v : Val) : adminW v.toAdmin = 0 := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

theorem codeW_vals (vs : List Val) : codeW (vals vs) = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals, List.map_cons] at ih ⊢
    rw [codeW_cons, adminW_val, ih]

theorem sum_adminW_vals (vs : List Val) : (vs.map (adminW ∘ Val.toAdmin)).sum = 0 := by
  have h := codeW_vals vs
  simpa only [codeW, vals, List.map_map] using h

/-- Constant redexes decrease the weight. -/
theorem constRedex_weight_lt {H : Type} {s s₁ : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s₁ out) : codeW out < adminW (.plain i) := by
  cases h <;> simp only [codeW_append, codeW_vals, codeW_cons, adminW_val] <;>
    simp [codeW, adminW, instrW, Admin.val?]

theorem constOk_vals_append (vs : List Val) (l : List Admin) (hl : ∀ a ∈ l, a.ConstOk) :
    ∀ a ∈ vals vs ++ l, a.ConstOk := by
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · exact Admin.constOk_vals vs a ha
  · exact hl a ha

theorem constRedex_constOk {H : Type} {s s₁ : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s₁ out) : ∀ a ∈ out, a.ConstOk := by
  cases h
  all_goals first
    | exact constOk_vals_append _ _ (by simp [Admin.ConstOk, Instr.IsConstI])
    | exact Admin.constOk_vals [_]
    | simp [Admin.ConstOk, Instr.IsConstI]

variable {P : Profile}

/-- Typed constant code runs to values. -/
theorem const_run (n : Nat) :
    ∀ (c : Config Nat) (ts : List CValType), codeW c.code < n → ConfigOk c ts →
      (∀ a ∈ c.code, a.ConstOk) →
      ∃ (s' : Store Nat) (ws : List Val),
        Steps P (divHost (H := Nat)) c ⟨s', c.frame, vals ws⟩ := by
  induction n with
  | zero => intro c ts h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro c ts hw hc hk
    rcases Config.progress (P := P) divHost_ok hc with ⟨r, hr⟩ | ⟨c', hs⟩
    · have hv : ∃ ws, c.code = vals ws := terminal_vals hk hr
      obtain ⟨ws, hws⟩ := hv
      refine ⟨c.store, ws, ?_⟩
      have e : c = ⟨c.store, c.frame, vals ws⟩ := by rw [← hws]
      rw [← e]
    · obtain ⟨hf, pre, w, i, post, out, e₁, e₂, hr⟩ := Step.const_redex hs hk
      have hc' : ConfigOk c' ts := (Step.preservation divHost_ok hc hs).1
      have hk' : ∀ a ∈ c'.code, a.ConstOk := by
        intro a ha
        rw [e₂] at ha
        rcases List.mem_append.1 ha with ha | ha
        · rcases List.mem_append.1 ha with ha | ha
          · exact Admin.constOk_vals pre a ha
          · exact constRedex_constOk hr a ha
        · exact hk a (by rw [e₁]; simp [ha])
      have hw' : codeW c'.code < n := by
        have h₁ : codeW c.code = codeW post + adminW (.plain i) := by
          rw [e₁, codeW_append, codeW_append, codeW_cons, codeW_vals, codeW_vals]; omega
        have h₂ : codeW c'.code = codeW out + codeW post := by
          rw [e₂, codeW_append, codeW_append, codeW_vals]; omega
        have h₃ := constRedex_weight_lt hr
        omega
      obtain ⟨s', ws, hrun⟩ := ih c' ts hw' hc' hk'
      rw [hf] at hrun
      exact ⟨s', ws, .head hs hrun⟩
where
  terminal_vals {c : Config Nat} {r : Result} (hk : ∀ a ∈ c.code, a.ConstOk)
      (hr : c.code = r.toAdmin) : ∃ ws, c.code = vals ws := by
    cases r with
    | values ws => exact ⟨ws, hr⟩
    | trap =>
      have h := hk .trap (by rw [hr]; exact List.mem_singleton_self _)
      exact absurd h Admin.not_constOk_trap
    | throw a =>
      have h := hk (.plain .throwRef) (by rw [hr]; simp [Result.toAdmin])
      simp [Admin.ConstOk, Instr.IsConstI] at h

/-- Typing and store extension along runs. -/
theorem steps_typed {c c' : Config Nat} {ts : List CValType} (hc : ConfigOk c ts)
    (h : Steps P (divHost (H := Nat)) c c') : ConfigOk c' ts ∧ Extend c.store c'.store := by
  induction h with
  | refl => exact ⟨hc, Extend.refl (SingleThreaded.ConfigOk.storeOk hc)⟩
  | tail _ hs ih =>
    obtain ⟨hc₁, he₁⟩ := ih
    obtain ⟨hc₂, he₂⟩ := Step.preservation divHost_ok hc₁ hs
    exact ⟨hc₂, he₁.trans he₂⟩

theorem frameOk_types {s : Store Nat} {f : Frame} {C : Context} (hf : FrameOk s f C) :
    f.module.types = C.types := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  exact (hm.ctx_fields.2.2.2).symm

theorem valOk_num {s : Store Nat} {v : Val} {nt : NumType} (h : ValOk s v (.num nt)) :
    ∃ b, v = .num ⟨nt, b⟩ := by
  generalize e : (Ty.num nt : CValType) = T at h
  cases h with
  | num nv =>
    obtain ⟨nt', b⟩ := nv
    cases e
    exact ⟨b, rfl⟩
  | vec => cases e
  | ref => cases e

/-- A typed value of an integer type is an integer constant. -/
theorem int_of_typed {s : Store Nat} {f : Frame} {v : Val} {t : IntType}
    (hc : ConfigOk ⟨s, f, vals [v]⟩ [.num (.int t)]) : ∃ i, v = .num ⟨.int t, i⟩ := by
  obtain ⟨C', ⟨hs₁, hf'⟩, hcode⟩ := hc
  obtain ⟨ts, hv, hsub⟩ := AdminsOk.vals_inv (FrameOk.toTypeCtx_okReg hs₁ hf') hcode
  cases hv with
  | @cons _ t' _ _ hv₁ hrest =>
    cases hrest
    have hsub₁ : Sub C'.toTypeCtx t' (.num (.int t)) := by
      cases hsub with
      | cons h _ => exact h
    rcases Sub.num_inv' hsub₁ with he | he
    · rw [he] at hv₁
      exact valOk_num hv₁
    · rw [he] at hv₁
      exact (ValOk.not_botv' hv₁).elim

/-- **A validated constant offset evaluates to an address constant**, into a well-typed
extension of the store. -/
theorem offset_eval {s : Store Nat} {f : Frame} {C : Context} {off : Expr} {a : AddrType}
    (hs : StoreOk s) (hf : FrameOk s f C) (ho : ExprOkConst C off a.valType) :
    ∃ s₁ i, evalConst? s f off = some (s₁, .num ⟨.int a.intType, i⟩) ∧ StoreOk s₁ ∧
      Extend s s₁ := by
  have hc : ConfigOk ⟨s, f, expression off⟩ [a.valType] :=
    ⟨C, ⟨hs, hf⟩, AdminsOk.of_instrsOk ho.typed⟩
  have hk : ∀ x ∈ (⟨s, f, expression off⟩ : Config Nat).code, x.ConstOk := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact (ho.const i hi).isConstI
  obtain ⟨s₁, ws, hrun⟩ := const_run (P := profile neverFail) _ _ _ (Nat.lt_succ_self _) hc hk
  obtain ⟨-, v, rfl, hev⟩ := evalConst?_of_exprOkConst ho (frameOk_types hf) hrun
  obtain ⟨hc₁, he₁⟩ := steps_typed hc hrun
  obtain ⟨i, rfl⟩ := int_of_typed hc₁
  exact ⟨s₁, i, hev, SingleThreaded.ConfigOk.storeOk hc₁, he₁⟩

end Silmaril.Proofs.Wasm.Game.SpecGlobals
