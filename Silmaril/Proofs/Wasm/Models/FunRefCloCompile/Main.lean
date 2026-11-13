module

public import Silmaril.Proofs.Wasm.Models.FunRefCloCompile.Clo

/-!
# Compiling FunRefClo: application, recursion and the behaviours of `main`

* `spec_app`: application is a `call` of `apply` (`TSafe.callIdx`) with `ApplyOK`;
* `applyOK_of_spec`: `apply` is totally correct for closures whose body evaluates with fuel `k`;
* **`spec_all`**: the code of every term is correct for every fuel, by induction on the fuel;
* `main_tspec`, **`behaviours_main`**: `main` returns the word of the program's value.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRefClo (Tm eval Prog Heap tableLocals ValTy obsWord)
open Silmaril.Wasm.Models.FunCompile (dBox dMain lx unbox anyref)
open Silmaril.Wasm.Models.FunCloCompile (dApply)
open Silmaril.Wasm.Models.FunRefCompile (dCell)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree twp_unbox twp_box twp_localGet
  twp_localSet len_setLocal setLocal_get lt_lim expr_append depth_left depth_right
  bodyPostT_normal behaviours_eq_of_tspec setWidth_31_32 vals_pair)
open Silmaril.Wasm.Logic.Core (Post Outcome)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## Application -/

theorem eval_app_inv {k : Nat} {σ σ' : Heap} {ρ : List FunRefClo.Val} {f a : Tm}
    {v : FunRefClo.Val} (h : eval (k + 1) σ ρ (.app f a) = some (v, σ')) :
    ∃ b ρ' σ₁ u σ₂, eval k σ ρ f = some (.clo b ρ', σ₁) ∧ eval k σ₁ ρ a = some (u, σ₂) ∧
      eval k σ₂ (u :: .clo b ρ' :: ρ') b = some (v, σ') := by
  simp only [eval] at h
  split at h
  · next b ρ' σ₁ hf =>
    split at h
    · next u σ₂ ha => exact ⟨b, ρ', σ₁, u, σ₂, hf, ha, h⟩
    · cases h
  · cases h

/-- **Application calls `apply`.** -/
theorem spec_app {k d : Nat} {f a : Tm} (hf : Spec P host p k d f) (ha : Spec P host p k d a)
    (happ : ApplyOK P host p k) : Spec P host p (k + 1) d (.app f a) := by
  intro σ ρ v σ' hv μ s fr hfr hfn hd hr hh hfx us rest Q hk
  obtain ⟨b, ρ', σ₁, u, σ₂, hef, hea, heb⟩ := eval_app_inv hv
  show TWP P host s fr (vals us ++ (expression (compile p.table d f ++ compile p.table d a ++
    [.call ⟨1⟩]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine hf σ ρ _ σ₁ hef μ s fr hfr hfn (depth_left hd) hr hh (sub_left hfx) us _ Q
    fun μ₁ s₁ f₁ wc hμ₁ hs₁ hf₁ hh₁ hwc => ?_
  refine ha σ₁ ρ _ σ₂ hea μ₁ s₁ f₁ (hfr.of_agree hf₁) (hs₁.funcs hfn)
    (by rw [hf₁.2.1]; exact depth_right hd) (hr.of_agree hμ₁ hs₁.1 hf₁) hh₁ (sub_right hfx)
    _ _ Q fun μ₂ s₂ f₂ wu hμ₂ hs₂ hf₂ hh₂ hwu => ?_
  have hfn₂ : s₂.funcs[1]? = some (applyInst p) := (hs₁.trans hs₂).funcs hfn
  have hx : f₂.module.funcs[(⟨1⟩ : FuncIdx).toNat]? = some 1 :=
    (hfr.of_agree (hf₁.trans hf₂)).2.1
  have hpre : (applySpec p b ρ' u v σ₂ σ' μ₂).pre s₂ [wc, wu] :=
    ⟨hfn₂, hh₂, wc, wu, rfl, hwc.mono hμ₂ hs₂.1, hwu⟩
  have hcall := TSafe.callIdx (P := P) (host := host) (vs₀ := us) (args := [wc, wu])
    (rest := rest) (Q := Q) hx hfn₂ (happ b ρ' u v σ₂ σ' μ₂ heb) hpre fun s' o hpost => by
      obtain ⟨-, ⟨res, rfl, w, μ', hres, hext, hμ', hh', hw⟩ | ⟨-, w, μ', h, -⟩ |
        ⟨_, -, w, μ', h, -⟩⟩ := hpost
      · cases hres
        exact hk μ' s' f₂ w ((hμ₁.trans hμ₂).trans hμ') ((hs₁.trans hs₂).trans hext)
          (hf₁.trans hf₂) hh' hw
      · cases h
      · cases h
  rw [vals_pair]
  exact hcall

/-! ## `apply` -/

/-- The frame of `apply` on the closure `wc` and the argument `wu`. -/
def applyFrame (L : List (Nat × Tm)) (wc wu : Val) : Frame :=
  Frame.forCall instOf [wc, wu] (applyFunc L).locals

theorem applyFrame_len (L : List (Nat × Tm)) (wc wu : Val) :
    (applyFrame L wc wu).locals.length = tableLocals L + 2 := by
  simp [applyFrame, Frame.forCall, applyFunc]

theorem applyFrame_ok {L : List (Nat × Tm)} (hL : tableLocals L + 2 ≤ 2 ^ 32) (wc wu : Val) :
    FOK (applyFrame L wc wu) :=
  ⟨⟨⟨[dMain, dCell, dApply], rfl⟩, by rw [applyFrame_len]; exact hL⟩, rfl, rfl⟩

/-- **`apply` is totally correct** for closures whose body evaluates with fuel `k`. -/
theorem applyOK_of_spec {k : Nat} (hfit : p.Fits) (hspec : ∀ d e, Spec P host p k d e) :
    ApplyOK P host p k := by
  intro b ρ' u v σ σ' μ hev
  refine TFSpecAt.of_body (fi := applyInst p) (code := applyFunc p.table)
    (fun _ _ h => h.1) rfl ⟨rfl⟩ ?_ ?_
  · rintro s args ⟨-, -, wc, wu, rfl, -⟩
    rfl
  · rintro s args ⟨hfn, hh, wc, wu, rfl, hrc, hru⟩ f vs₀
    obtain ⟨addr, we, rfl, hst, hL', hel⟩ := id hrc
    have hF := applyFrame_ok hfit.2.1 (.ref (.struct addr)) wu
    have hc : DispatchCtx P host p k μ s (applyFrame p.table (.ref (.struct addr)) wu) b ρ' u v
        σ σ' addr wu we :=
      ⟨hspec, hfit.2.2, hF, hfn, by rw [applyFrame_len], by simp [applyFrame, Frame.forCall],
        by simp [applyFrame, Frame.forCall], hrc, hst, hL', hru, hh, hev⟩
    have h' := twp_dispatch hc (tagOf p.table ρ'.length b) 0 (by simp) (us := []) (rest := [])
      (Q := bodyPostT P host 1 f vs₀ (callPost f vs₀ ((applySpec p b ρ' u v σ σ' μ).post s
        [.ref (.struct addr), wu])))
      fun μ' s' F' w hμ hs hh' hw => Wp.of_vals (m := .total) (vs := [w])
        (bodyPostT_normal rfl ⟨w, μ', rfl, hs, hμ, hh', hw⟩)
    simp only [vals, List.map_nil, List.nil_append, List.append_nil, List.drop_zero] at h'
    exact h'

/-! ## Every term, every fuel -/

/-- **The code of every term is correct for every fuel**, at every depth, profile and host. -/
theorem spec_all (hfit : p.Fits) : ∀ k d e, Spec P host p k d e
  | 0 => fun _ _ _ _ _ _ h => by simp [eval] at h
  | k + 1 => fun d e => by
    have ih := spec_all hfit k
    have happ : ApplyOK P host p k := applyOK_of_spec hfit ih
    cases e with
    | var i => exact spec_var k d i
    | int n => exact spec_int k d n
    | bool b => exact spec_bool k d b
    | arith op a b => exact spec_arith (ih d a) (ih d b)
    | cmp op a b => exact spec_cmp (ih d a) (ih d b)
    | ite c t e => exact spec_ite (ih d c) (ih d t) (ih d e)
    | let_ a b => exact spec_let (ih d a) (ih (d + 1) b)
    | pair a b => exact spec_pair (ih d a) (ih d b)
    | fst e => exact spec_fst (ih d e)
    | snd e => exact spec_snd (ih d e)
    | inl e => exact spec_inl (ih d e)
    | inr e => exact spec_inr (ih d e)
    | case e l r => exact spec_case (ih d e) (ih (d + 1) l) (ih (d + 1) r)
    | fix b => exact spec_fix k d b
    | app f a => exact spec_app (ih d f) (ih d a) happ
    | ref e => exact spec_ref (ih d e)
    | get e => exact spec_get (ih d e)
    | set a b => exact spec_set (ih d a) (ih d b)

/-! ## `main` -/

/-- The specification of `main` on `n`, returning the word `w`. -/
def mainSpec (p : Prog) (n w : BitVec 31) : FSpec Nat :=
  ⟨fun s args => s.funcs[0]? = some (mainInst p) ∧ s.funcs[1]? = some (applyInst p) ∧
      args = [.i32 (n.setWidth 32)],
    fun _ _ _ o => o = .normal [.i32 (w.setWidth 32)]⟩

/-- A ground value is represented by the `i31` of its word. -/
theorem rep_ground {μ : List Nat} {s : Store Nat} {v : FunRefClo.Val} {Ψ : List FunRefClo.Ty}
    {τ : FunRefClo.Ty} (ht : ValTy Ψ v τ) (hg : τ.Ground) {w : Val}
    (hw : Rep p.table μ s v w) : w = .ref (.i31 (obsWord v)) := by
  cases ht with
  | int n => exact hw
  | bool b => exact hw
  | pair => exact hg.elim
  | inl => exact hg.elim
  | inr => exact hg.elim
  | clo => exact hg.elim
  | loc => exact hg.elim

/-- The frame of `main` on `n`. -/
def frame0 (p : Prog) (n : BitVec 31) : Frame :=
  Frame.forCall instOf [.i32 (n.setWidth 32)] (mainFunc p).locals

theorem frame0_len (p : Prog) (n : BitVec 31) :
    (frame0 p n).locals.length = p.body.depth + 2 := by
  simp [frame0, Frame.forCall, mainFunc]

theorem frame0_ok {p : Prog} (hfit : p.Fits) (n : BitVec 31) : FOK (frame0 p n) :=
  ⟨⟨⟨[dMain, dCell, dApply], rfl⟩, by rw [frame0_len]; exact Nat.le_of_lt hfit.1⟩, rfl, rfl⟩

theorem frame0_arg (p : Prog) (n : BitVec 31) :
    (frame0 p n).locals[0]? = some (some (.i32 (n.setWidth 32))) := by
  simp [frame0, Frame.forCall]

/-- The environment after the prologue: the boxed argument in local `1`. -/
theorem env_prologue {p : Prog} (hfit : p.Fits) (s : Store Nat) (n : BitVec 31) :
    EnvRep p.table [] s ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))) 1 [.int n] := by
  have hlt : 1 < (frame0 p n).locals.length := by rw [frame0_len]; omega
  refine ⟨rfl, fun i u hi => ?_⟩
  have hi0 : i = 0 := by
    rcases i with _ | i
    · rfl
    · simp at hi
  subst hi0
  have hu : u = .int n := by simpa using hi.symm
  exact ⟨_, setLocal_get _ hlt (lt_lim (frame0_ok hfit n).1 hlt), hu ▸ rfl⟩

theorem mainBody_code (p : Prog) :
    expression (mainBody p) = vals [] ++ .plain (.localGet (lx 0)) :: .plain .refI31 ::
      .plain (.localSet (lx 1)) ::
        (expression (compile p.table 1 p.body) ++ (expression unbox ++ [])) := by
  simp [mainBody, expression]

/-- **The body of `main` is totally correct**: it returns the word of the program's value. -/
theorem body_twp (hp : p.WellTyped) (hfit : p.Fits) {n : BitVec 31} {k : Nat}
    {v : FunRefClo.Val} {σ' : Heap} (hv : eval k [] [.int n] p.body = some (v, σ'))
    (s : Store Nat) (hfn : s.funcs[1]? = some (applyInst p)) (f : Frame) (vs₀ : List Val) :
    TWP P host s (frame0 p n) (expression (mainBody p))
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
  obtain ⟨Ψ, hty⟩ : ∃ Ψ, ValTy Ψ v p.res := FunRefClo.Prog.Eval.sound hp ⟨k, σ', hv⟩
  have hok := frame0_ok hfit n
  have hlt : 1 < (frame0 p n).locals.length := by rw [frame0_len]; omega
  have hd : 1 + p.body.depth <
      ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))).locals.length := by
    rw [len_setLocal, frame0_len]; omega
  have hh : HeapRep p.table [] s [] := HeapRep.empty _ _
  have hk : Cont P host p.table 1 [] s ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))) v σ' []
      (expression unbox ++ [])
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
    intro μ' s' f' w _ _ _ _ hw
    rw [rep_ground hty hp.2 hw]
    have hb : bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)])) s' f'
        (.normal [.i32 ((obsWord v).setWidth 32)]) := bodyPostT_normal rfl rfl
    have hw' : TWP P host s' f' (vals [.i32 ((obsWord v).setWidth 32)]) _ :=
      Wp.of_vals (m := .total) hb
    exact twp_unbox (by simpa using hw')
  rw [mainBody_code]
  refine twp_localGet hok.1 (frame0_arg p n) (twp_box ?_)
  rw [setWidth_31_32]
  exact twp_localSet hok.1 hlt (spec_all hfit k 1 p.body [] [.int n] v σ' hv [] s _
    (hok.setLocal _ _) hfn hd (env_prologue hfit s n) hh (fun _ hx => hx) [] _ _ hk)

/-- **`main` meets its total specification**, at every profile and for every host. -/
theorem main_tspec (hp : p.WellTyped) (hfit : p.Fits) {n : BitVec 31} {k : Nat}
    {v : FunRefClo.Val} {σ' : Heap} (hv : eval k [] [.int n] p.body = some (v, σ')) :
    TFSpecAt P host 0 (mainSpec p n (obsWord v)) := by
  refine TFSpecAt.of_body (fi := mainInst p) (code := mainFunc p) (fun _ _ h => h.1) rfl ⟨rfl⟩
    ?_ ?_
  · rintro s args ⟨-, -, rfl⟩
    rfl
  · rintro s args ⟨-, hfn, rfl⟩ f vs₀
    exact body_twp hp hfit hv s hfn f vs₀

/-- **The behaviours of the compiled program**: if the program returns `v` on `n`, `main` on `n`
returns the word of `v`, and does nothing else, at every profile and for every host. -/
theorem behaviours_main (P : Numerics.Profile) (host : HostSemantics Nat) {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) {n : BitVec 31} {v : FunRefClo.Val} (hv : p.Eval n v) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((obsWord v).setWidth 32)]} := by
  obtain ⟨k, σ', hk⟩ := hv
  exact behaviours_eq_of_tspec (main_tspec hp hfit hk) ⟨rfl, rfl, rfl⟩ fun _ _ h => h

end Silmaril.Proofs.Wasm.Models.FunRefCloCompile
