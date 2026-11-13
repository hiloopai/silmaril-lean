module

public import Silmaril.Raw.Wasm.Auto2.Calls.Run

/-!
# Symbolic execution with inlined calls: the forward rule (unrefined)

**`wp_xsexecC`**: in a typed context whose function environment is correct (`FEnvOk`), the
weakest precondition of code that `xsexecC` runs is `XOut` of the final state: the trap
postcondition at the first failing guard, or the weakest precondition of the final
configuration. Both readings, every profile and host relation; by induction on the fuel. The loop
and plain cases are those of `EquivUnroll.wp_xsexecU`; at a call, the induction hypothesis in the
callee's context (`calleeCtx`, total reading, postcondition `Pin`) pins the callee's body,
`EquivFn.wp_call_pinned` gives what the caller sees, and the caller continues from `afterCall`
(a trap inside the callee is the caller's trap, in the store where it happened and the caller's
frame).

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Calls

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (NoFuncTop wp_seq_iff seqPostM_normal seqPostM_ne_normal)
open Silmaril.Wasm.Auto.EquivFn (wp_call_pinned Pinned Pin xOutcome fits_xOutcome FrameOut)
open Silmaril.Wasm.Auto.EquivUnroll (wp_loop_xstep xout_of_fail)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The executor with inlined calls is sound.** -/
theorem wp_xsexecC {mem : Bool} {fe : Nat → Option Callee} :
    ∀ (fuel : Nat) (m : Corr) (c : XCtx H), c.Good mem → FEnvOk c.s c.f.module fe →
      ∀ (us : List Val), NoFuncTop us → ∀ (rest : List Admin) (Q : Post H) (a : List Instr)
        {S S' : XState}, S.globs.length = c.ga.length → firstFail c.ρ c.mi.bytes S.guards = none →
        xsexecC mem fe fuel S a = some S' →
        (Wp m P host (c.storeOf mem S) (c.frameOf S)
            (vals (us ++ (c.stackOf S).reverse) ++ expression a ++ rest) Q ↔
          XOut m P host c mem S' us rest Q)
  | _, m, c, _, _, us, _, rest, Q, [], S, S', _, hf, h => by
    unfold xsexecC at h
    cases h
    simp [XOut, hf, expression]
  | 0, _, _, _, _, _, _, _, _, _ :: _, _, _, _, _, h => by unfold xsexecC at h; cases h
  | f + 1, m, c, hc, hfe, us, hus, rest, Q, i :: is, S, S', hl, hf, h => by
    have e : vals (us ++ (c.stackOf S).reverse) ++ expression (i :: is) ++ rest =
        vals (us ++ (c.stackOf S).reverse) ++ .plain i :: (expression is ++ rest) := by
      simp [expression]
    rw [e]
    unfold xsexecC at h
    split at h
    · rename_i b
      split at h
      · rename_i body hS hb
        split at h
        · rename_i S₁ hr
          split at h
          · rename_i e₀ st' h₁
            have hl₁ : S₁.globs.length = c.ga.length := by rw [xsexec_globs hr, hl]
            split at h
            · rename_i hk
              rw [wp_loop_xstep hc hus hS hl hf hb hr h₁ hk]
              cases hT : firstFail c.ρ c.mi.bytes S₁.guards with
              | some T =>
                simp only
                exact (xout_of_fail hT (by
                  obtain ⟨G, hG⟩ := xsexecC_guards f h
                  exact ⟨G, hG⟩)).symm
              | none =>
                simp only [↓reduceIte]
                have := wp_xsexecC f m c hc hfe us hus rest Q is (S := { S₁ with stack := st' })
                  hl₁ hT h
                rw [← this]
                simp [expression]
                rfl
            · rename_i n hk
              rw [wp_loop_xstep hc hus hS hl hf hb hr h₁ hk]
              cases hT : firstFail c.ρ c.mi.bytes S₁.guards with
              | some T =>
                simp only
                exact (xout_of_fail hT (by
                  obtain ⟨G, hG⟩ := xsexecC_guards f h
                  exact ⟨G, hG⟩)).symm
              | none =>
                simp only [Nat.add_one_ne_zero, ↓reduceIte]
                have := wp_xsexecC f m c hc hfe us hus rest Q (.loop .empty b :: is)
                  (S := { S₁ with stack := [] }) hl₁ hT h
                rw [← this]
                simp [expression]
                rfl
            · cases h
          · cases h
        · cases h
      · cases h
    · rename_i x
      split at h
      · rename_i ce hce
        split at h
        · rename_i hn
          split at h
          · rename_i A hA
            split at h
            · rename_i hnr
              obtain ⟨a₀, fi, code, ps, rs, hx, hfi, hcode, hexp, hps, hrs, hbody, hls, hmf, hmg,
                hmm⟩ := hfe _ ce hce
              have hfi' : (c.storeOf mem S).funcs[a₀]? = some fi := by rw [storeOf_funcs]; exact hfi
              -- The callee's context and run.
              have hc' := calleeCtx_good hc hmg hmm
                ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse code.locals
              have hfe' : FEnvOk (calleeCtx c fi.module
                  ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse code.locals).s
                  (calleeCtx c fi.module
                  ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse code.locals).f.module fe :=
                fenvOk_congr hfe hmf hmg hmm
              have hw := wp_xsexecC f .total _ hc' hfe' [] (fun _ h => by simp at h) []
                (Pin (xOutcome (calleeCtx c fi.module
                  ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse code.locals) mem A).1
                  (xOutcome (calleeCtx c fi.module
                  ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse code.locals) mem A).2)
                ce.body (S := calleeInit S ce.np ce.ls) hl rfl hA
              rw [calleeCtx_storeOf, frameOf_calleeInit c S hls, calleeCtx_stackOf,
                show c.stackOf (calleeInit S ce.np ce.ls) = [] from rfl,
                show c.storeOf mem (calleeInit S ce.np ce.ls) = c.storeOf mem S from
                  storeOf_congr c mem rfl rfl, ← hbody] at hw
              have hpin : Pinned P host (c.storeOf mem S)
                  (Frame.forCall fi.module ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse
                    code.locals) (expression code.body)
                  (xOutcome (calleeCtx c fi.module
                    ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse code.locals) mem A).1
                  (xOutcome (calleeCtx c fi.module
                    ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse code.locals) mem A).2 := by
                have hx' := hw.mpr (by
                  unfold XOut
                  cases hT : firstFail c.ρ c.mi.bytes A.guards with
                  | some T =>
                    simp only [calleeCtx_ρ, calleeCtx_mi, hT, xOutcome]
                    exact ⟨rfl, rfl⟩
                  | none =>
                    simp only [calleeCtx_ρ, calleeCtx_mi, hT, xOutcome, List.nil_append,
                      List.append_nil]
                    exact wp_vals_iff'.mpr ⟨rfl, rfl⟩)
                unfold Pinned
                simpa using hx'
              have hfits : Silmaril.Wasm.Auto.EquivFn.Fits rs.length (xOutcome (calleeCtx c fi.module
                  ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse code.locals) mem A).2 :=
                fits_xOutcome (by rw [hnr, hrs])
              have hlen : ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse.length =
                  ps.length := by
                simp [hps, Nat.min_eq_left hn]
              -- The caller's call.
              have hstk : (c.stackOf S).reverse =
                  ((S.stack.drop ce.np).map (denX c.ρ c.mi.bytes)).reverse ++
                    ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse := by
                simp only [XCtx.stackOf]
                conv_lhs => rw [← List.take_append_drop ce.np S.stack]
                simp
              rw [hstk, ← List.append_assoc, wp_callIdx_iff (f := c.frameOf S) hx hfi']
              have e₂ : vals ((us ++ ((S.stack.drop ce.np).map (denX c.ρ c.mi.bytes)).reverse) ++
                    ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse) ++
                    [.ref (.func a₀), .callRefType fi.type] ++ (expression is ++ rest) =
                  (vals (us ++ ((S.stack.drop ce.np).map (denX c.ρ c.mi.bytes)).reverse) ++
                    vals ((S.stack.take ce.np).map (denX c.ρ c.mi.bytes)).reverse ++
                    [.ref (.func a₀), .callRefType fi.type]) ++ (expression is ++ rest) := by
                simp [vals]
              rw [e₂, wp_seq_iff, wp_call_pinned (P := P) (host := host) (c := .callRefType fi.type) trivial hfi' hcode hexp
                hlen hpin hfits]
              obtain ⟨G, hG⟩ := xsexecC_guards f h
              cases hT : firstFail c.ρ c.mi.bytes A.guards with
              | some T =>
                have hT' : firstFail c.ρ c.mi.bytes (afterCall S ce.np A).guards =
                    some { T with locals := S.locals } := by
                  simp only [afterCall]
                  rw [firstFail_append_none _ hf, firstFail_retLocals, hT]
                  rfl
                rw [xout_of_fail hT' ⟨G, hG⟩]
                simp only [xOutcome, calleeCtx_ρ, calleeCtx_mi, hT, FrameOut, calleeCtx_storeOf]
                rw [seqPostM_ne_normal (by intro vs h; cases h),
                  storeOf_congr c mem (S := T) (T := { T with locals := S.locals }) rfl rfl,
                  frameOf_congr c (S := { T with locals := S.locals }) (T := S) rfl]
              | none =>
                have hT' : firstFail c.ρ c.mi.bytes (afterCall S ce.np A).guards = none := by
                  simp only [afterCall]
                  rw [firstFail_append_none _ hf, firstFail_retLocals, hT]
                  rfl
                have hl'' : (afterCall S ce.np A).globs.length = c.ga.length := by
                  simp only [afterCall]
                  rw [xsexecC_globs f hA]
                  exact hl
                rw [← wp_xsexecC f m c hc hfe us hus rest Q is hl'' hT' h]
                simp only [xOutcome, calleeCtx_ρ, calleeCtx_mi, hT, FrameOut, calleeCtx_storeOf,
                  calleeCtx_stackOf]
                rw [seqPostM_normal]
                have hlenr : (c.stackOf A).reverse.length = rs.length := by
                  simp [XCtx.stackOf, hnr, hrs]
                rw [and_iff_right hlenr,
                  storeOf_congr c mem (S := afterCall S ce.np A) (T := A) rfl rfl,
                  frameOf_congr c (S := afterCall S ce.np A) (T := S) rfl]
                have hst : (c.stackOf (afterCall S ce.np A)).reverse =
                    ((S.stack.drop ce.np).map (denX c.ρ c.mi.bytes)).reverse ++
                      (c.stackOf A).reverse := by
                  simp [XCtx.stackOf, afterCall, List.map_append, List.reverse_append]
                rw [hst]
                simp [List.append_assoc]
            · cases h
          · cases h
        · cases h
      · cases h
    · split at h
      · rename_i S₁ hs
        have hx : xsexec mem S [i] = some S₁ := by simp [xsexec, hs]
        have h₀ := wp_xsexec (m := m) (P := P) (host := host) hc us (expression is ++ rest) Q [i]
          hl hf hx
        have e' : vals (us ++ (c.stackOf S).reverse) ++ expression [i] ++ (expression is ++ rest) =
            vals (us ++ (c.stackOf S).reverse) ++ .plain i :: (expression is ++ rest) := by
          simp [expression]
        rw [e'] at h₀
        rw [h₀]
        have hl₁ : S₁.globs.length = c.ga.length := by rw [xsexec_globs hx, hl]
        unfold XOut
        cases hT : firstFail c.ρ c.mi.bytes S₁.guards with
        | some T =>
          simp only
          obtain ⟨G, hG⟩ := xsexecC_guards f h
          have hf' : firstFail c.ρ c.mi.bytes S'.guards = some T := by
            rw [hG]
            exact firstFail_append_some G hT
          simp only [hf']
        | none =>
          simp only
          have := wp_xsexecC f m c hc hfe us hus rest Q is hl₁ hT h
          rw [← List.append_assoc]
          exact this
      · cases h

end Silmaril.Wasm.Auto2.Calls
