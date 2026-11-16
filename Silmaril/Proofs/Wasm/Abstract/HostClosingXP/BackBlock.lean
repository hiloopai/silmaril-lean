module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackCtl

/-!
# The logged backward simulation of blocks and loops (proofs)

`case_block`, `case_loop`: see `BackCtl`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {host : HostSemantics H} {tags : List TagInst} {o : GrowOracle}

section Cases

variable {s : Store H} {f : Frame} {stk : List Val} {c : Config H}
  {cs : List (Call (wasmHostSig H))} {n : Nat}

/-- **Blocks.** -/
theorem case_block (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {bt : BlockType} {body es : List Binaryen.BExpr}
    (ihB : ∀ m ≤ n, BackG tags o host m body) (ihk : ∀ m ≤ n, BackG tags o host m es) :
    BackG tags o host n (.block bt body :: es) := by
  intro s f stk c cs ht hrun hend hnd
  have hct := typedP_ctx ht
  obtain ⟨-, labels, ret, out, hS, hc, -, hTM, hts⟩ := id ht
  obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, hp, hb, rfl⟩ := chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  let B := Binaryen.BExpr.lowerList body
  let E := expression (Binaryen.BExpr.lowerList es)
  have henter : Steps (profile o) NH ⟨s, f, tcode stk (.block bt body :: es)⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.label nr [] (vals (stk.take np).reverse ++ expression B)] ++ E⟩ := by
    change Steps _ _ ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList
      (.block bt body :: es))⟩ _
    rw [code_block]
    exact steps_enter hp (step_block har) E
  obtain ⟨m₀, hm₀, hk₀⟩ := through henter hrun hend
  obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hend₁, hk, hx⟩ := evRunN_label_seq_split hk₀ hend
  have hnd₁ := nd_label hx hnd
  have htb : TypedP tags s f (stk.take np) body := block_body_typedP har ht
  obtain ⟨l₁, ⟨s₁, f₁, ob⟩, hd₁, hres₁, hok₁⟩ :=
    ihB N₁ (by omega) s f (stk.take np) cb cs₁ htb h₁ hend₁ hnd₁
  cases ob with
  | tail a' args k => exact mkOut'' hH hE ht hrun hend (.blockEsc har hd₁ trivial) hres₁
  | flow fl =>
    rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
    · have hne : fl ≠ .trap := ne_trap_of_blockVals' hvs
      have hq₁ := resX_nontrap hres₁ (by simpa using hne)
      have hcons₁ : Cons host cs₁ := (cons_append.1 (evRun_consistent (evRunN_evRun hrun))).1
      obtain ⟨-, t₁, a₁, -⟩ := full_run (P := profile o) hH hE hd₁
        (substPre_mono (close_le_goodCX hH hE) hq₁) hcons₁ hts
      obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS (arityE_of_arityP a₁) hb
        (take_length_of_le hp)
      have hnr := blockVals_length hok hob hvs
      have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
        rintro ws rfl; exact length_of_ends hok hob
      rcases hok₁ with ⟨oc, he, hm⟩ | ⟨h, -⟩
      swap
      · exact absurd (by simpa using h) hne
      obtain ⟨hs₁, hf₁, hfm⟩ := match_of_matchP hne hm
      obtain ⟨cst, cfr, ccd⟩ := cb
      simp only at hs₁ hf₁ he hk h₁
      subst hs₁ hf₁
      have hex := exit_blockVals (P := profile o) (host := NH) (s₁ := cst) (f₁ := cfr)
        (pre := (stk.drop np).reverse) (rest := E) he hfm hvs hnr hnorm
      have hcont : vals ((stk.drop np).reverse ++ (vs.take nr).reverse) ++ E =
          tcode (vs.take nr ++ stk.drop np) es := by simp [tcode, E]
      rw [hcont] at hex
      obtain ⟨m', hm', hk'⟩ := through hex hk hend
      have hstT : Steps (profile o) host ⟨s, f, tcode stk (.block bt body :: es)⟩
          ⟨cst, cfr, tcode (vs.take nr ++ stk.drop np) es⟩ :=
        (steps_host henter).trans ((Steps.ctx _ _ (Steps.label nr [] (evRunN_steps h₁))).trans
          (steps_host hex))
      have htk : TypedP tags cst cfr (vs.take nr ++ stk.drop np) es :=
        typedP_of (storeChk_inv inv1 hS) (chk_after inv1 hp hnr h2)
          (ContextTyped.steps_typed hT hct hstT) (by rw [inv1.2.1]; exact hTM) t₁
      obtain ⟨l₂, r₂, hd₂, hres₂, -⟩ := ihk m' (by omega) _ _ _ c cs₂ htk hk' hend hnd
      exact mkOut hH hE ht hrun hend (.blockOk har hd₁ hvs hd₂) (resX_prepend hq₁ hres₂)
    · exact mkOut'' hH hE ht hrun hend (.blockBrk har hd₁) (.inl (resX_nontrap hres₁ (by simp)))
    · exact mkOut'' hH hE ht hrun hend (.blockEsc har hd₁ hesc) hres₁

/-- **Loops.** -/
theorem case_loop (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {bt : BlockType} {body es : List Binaryen.BExpr}
    (ihB : ∀ m ≤ n, BackG tags o host m body) (ihk : ∀ m ≤ n, BackG tags o host m es)
    (ihlt : ∀ m < n, BackG tags o host m (.loop bt body :: es)) :
    BackG tags o host n (.loop bt body :: es) := by
  intro s f stk c cs ht hrun hend hnd
  have hct := typedP_ctx ht
  obtain ⟨-, labels, ret, out, hS, hc, -, hTM, hts⟩ := id ht
  obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨np, nr, ha, hp, hb, rfl⟩ := chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  let B := Binaryen.BExpr.lowerList body
  let E := expression (Binaryen.BExpr.lowerList es)
  have hcode : tcode stk (.loop bt body :: es) = vals stk.reverse ++ .plain (.loop bt B) :: E :=
    code_loop stk bt es
  have hstep : Step (profile o) Det.noHost ⟨s, f, tcode stk (.loop bt body :: es)⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.label np [.loop bt B] (vals (stk.take np).reverse ++ expression B)] ++ E⟩ := by
    rw [hcode]; exact step_enter hp (step_loop har) E
  obtain ⟨m₀, rfl, hk₀⟩ := evRunN_unique
    (fun c₁ h => loop_step_unique' har hp (by rw [hcode] at h; exact h)) hstep hrun hend
  obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hend₁, hk, hx⟩ := evRunN_label_seq_split hk₀ hend
  have hnd₁ := nd_label hx hnd
  have htb : TypedP tags s f (stk.take np) body := loop_body_typedP har ht
  obtain ⟨l₁, ⟨s₁, f₁, ob⟩, hd₁, hres₁, hok₁⟩ :=
    ihB N₁ (by omega) s f (stk.take np) cb cs₁ htb h₁ hend₁ hnd₁
  have hcons₁ : Cons host cs₁ := (cons_append.1 (evRun_consistent (evRunN_evRun hrun))).1
  cases ob with
  | tail a' args k => exact mkOut'' hH hE ht hrun hend (.loopEsc har hd₁ trivial) hres₁
  | flow fl =>
    rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
    · -- the body falls through
      have hq₁ := resX_nontrap hres₁ (by simp)
      obtain ⟨-, t₁, a₁, -⟩ := full_run (P := profile o) hH hE hd₁
        (substPre_mono (close_le_goodCX hH hE) hq₁) hcons₁ hts
      obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS (arityE_of_arityP a₁) hb
        (take_length_of_le hp)
      have hlen : vs.length = nr := length_of_ends hok hob
      rcases hok₁ with ⟨oc, he, hm⟩ | ⟨h, -⟩
      swap
      · simp at h
      obtain ⟨hs₁, hf₁, hfm⟩ := match_of_matchP (by simp) hm
      obtain ⟨cst, cfr, ccd⟩ := cb
      simp only at hs₁ hf₁ he hk h₁
      subst hs₁ hf₁
      have hex := exit_normal (P := profile o) (host := NH) (s₁ := cst) (f₁ := cfr)
        (n := np) (cont := [.loop bt B]) he hfm ((stk.drop np).reverse) E
      have htake : vs.take nr = vs := List.take_of_length_le hlen.le
      have hcont : vals ((stk.drop np).reverse ++ vs.reverse) ++ E =
          tcode (vs.take nr ++ stk.drop np) es := by rw [htake]; simp [tcode, E]
      rw [hcont] at hex
      obtain ⟨m', hm', hk'⟩ := through hex hk hend
      have hstT : Steps (profile o) host ⟨s, f, tcode stk (.loop bt body :: es)⟩
          ⟨cst, cfr, tcode (vs.take nr ++ stk.drop np) es⟩ :=
        (Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans
          ((Steps.ctx _ _ (Steps.label np [.loop bt B] (evRunN_steps h₁))).trans (steps_host hex))
      have htk : TypedP tags cst cfr (vs.take nr ++ stk.drop np) es :=
        typedP_of (storeChk_inv inv1 hS) (chk_after inv1 hp hlen.ge h2)
          (ContextTyped.steps_typed hT hct hstT) (by rw [inv1.2.1]; exact hTM) t₁
      obtain ⟨l₂, r₂, hd₂, hres₂, -⟩ := ihk m' (by omega) _ _ _ c cs₂ htk hk' hend hnd
      exact mkOut hH hE ht hrun hend (.loopOk har hd₁ hd₂) (resX_prepend hq₁ hres₂)
    · -- the body branches back to the loop
      have hq₁ := resX_nontrap hres₁ (by simp)
      obtain ⟨-, t₁, a₁, -⟩ := full_run (P := profile o) hH hE hd₁
        (substPre_mono (close_le_goodCX hH hE) hq₁) hcons₁ hts
      obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS (arityE_of_arityP a₁) hb
        (take_length_of_le hp)
      have hnp : np ≤ vs.length := by
        obtain ⟨k', hk', hle⟩ := hok
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
        omega
      rcases hok₁ with ⟨oc, he, hm⟩ | ⟨h, -⟩
      swap
      · simp at h
      obtain ⟨hs₁, hf₁, hfm⟩ := match_of_matchP (by simp) hm
      obtain ⟨cst, cfr, ccd⟩ := cb
      simp only at hs₁ hf₁ he hk h₁
      subst hs₁ hf₁
      have hex := exit_br0 (P := profile o) (host := NH) (s₁ := cst) (f₁ := cfr)
        (cont := [.loop bt B]) he hfm hnp ((stk.drop np).reverse) E
      have hcont : vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++ expression [.loop bt B] ++
          E = tcode (vs.take np ++ stk.drop np) (.loop bt body :: es) := by
        change _ = vals (vs.take np ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList (.loop bt body :: es))
        rw [code_loop]; simp [E, B, expression]
      rw [hcont] at hex
      obtain ⟨m', hm', hk'⟩ := through hex hk hend
      have hstT : Steps (profile o) host ⟨s, f, tcode stk (.loop bt body :: es)⟩
          ⟨cst, cfr, tcode (vs.take np ++ stk.drop np) (.loop bt body :: es)⟩ :=
        (Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans
          ((Steps.ctx _ _ (Steps.label np [.loop bt B] (evRunN_steps h₁))).trans (steps_host hex))
      have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
        simp only [List.length_append, List.length_take, List.length_drop]; omega
      have htk : TypedP tags cst cfr (vs.take np ++ stk.drop np) (.loop bt body :: es) := by
        refine typedP_of (storeChk_inv inv1 hS) (labels := labels) (ret := ret) (out := out) ?_
          (ContextTyped.steps_typed hT hct hstT) (by rw [inv1.2.1]; exact hTM) t₁
        rw [hlen]
        exact chk_inv inv1 hc
      obtain ⟨l₂, r₂, hd₂, hres₂, -⟩ := ihlt m' (by omega) _ _ _ c cs₂ htk hk' hend hnd
      exact mkOut hH hE ht hrun hend (.loopBack har hd₁ hd₂) (resX_prepend hq₁ hres₂)
    · exact mkOut'' hH hE ht hrun hend (.loopBrk har hd₁) (.inl (resX_nontrap hres₁ (by simp)))
    · exact mkOut'' hH hE ht hrun hend (.loopEsc har hd₁ trivial) hres₁
    · exact mkOut'' hH hE ht hrun hend (.loopEsc har hd₁ trivial) hres₁
    · exact mkOut'' hH hE ht hrun hend (.loopEsc har hd₁ trivial) hres₁

end Cases

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
