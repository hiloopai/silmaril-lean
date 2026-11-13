module

public import Silmaril.Proofs.Wasm.Models.FunCloGame.Harness

/-!
# The closure game of FunClo: the simulation between source and Wasm runs

* `HInv p s H W`: the store has the functions of `storeG p`, the Wasm handles `W` represent the
  source handles `H` in `s`, and every source handle is a closure of a first-order function type.
* `fo_cases`, `rep_ans`: a value of a first-order type is an integer, a boolean or a closure of a
  first-order function type; its representation is read off as its answer, and the handles grow
  together.
* `step_fwd`: a source step is matched by an invocation returning a representation of its value.
* `step_bwd`: an invocation that returns comes from a source step (the source cannot diverge:
  then `mainR` or `apply` would never return, by `mainR_div` and FunCloDiv's `div_all`).
* `run_fwd`, `run_bwd`: runs correspond, so `wasmPlays_eq`: the plays of the Wasm runs are the
  plays of the source runs.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloGame

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile Silmaril.Wasm.Models.FunCloGame
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunClo (Tm eval Prog Ty HasTy ValTy EnvTy eval_sound)
open Silmaril.Proofs.Wasm.Models.FunCloCompile (Rep Ext spec_all applyOK_of_spec)
open Silmaril.Proofs.Wasm.Models.FunCloDiv (div_all SDiv conv_or_div)
open Silmaril.Wasm.Logic.Core (Outcome)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## The invariant -/

/-- **The invariant** between the source handles `H` and the Wasm handles `W` in the store `s`. -/
def HInv (p : Prog) (s : Store Nat) (H : List FunClo.Val) (W : List Val) : Prop :=
  s.funcs = (storeG p).funcs ∧ List.Forall₂ (Rep p.table s) H W ∧
    ∀ v ∈ H, ∃ τ, ValTy v (.arr .int τ) ∧ Ty.FO τ

theorem HInv.init (p : Prog) : HInv p (storeG p) [] [] :=
  ⟨rfl, .nil, by simp⟩

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {a : α},
      l₁[i]? = some a → ∃ b, l₂[i]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨_, rfl, h ▸ hab⟩
  | _, _, .cons _ hl, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? hl h

theorem forall₂_getElem?_rev {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {b : β},
      l₂[i]? = some b → ∃ a, l₁[i]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨_, rfl, h ▸ hab⟩
  | _, _, .cons _ hl, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem?_rev hl h

theorem forall₂_mono {s s' : Store Nat} (hs : s.structs <+: s'.structs) :
    ∀ {H : List FunClo.Val} {W : List Val}, List.Forall₂ (Rep p.table s) H W →
      List.Forall₂ (Rep p.table s') H W
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (h.mono hs) (forall₂_mono hs hl)

theorem HInv.mono {s s' : Store Nat} {H : List FunClo.Val} {W : List Val} (hI : HInv p s H W)
    (hs : Ext s s') : HInv p s' H W :=
  ⟨hs.2.trans hI.1, forall₂_mono hs.1 hI.2.1, hI.2.2⟩

theorem HInv.apply {s : Store Nat} {H : List FunClo.Val} {W : List Val} (hI : HInv p s H W) :
    s.funcs[1]? = some (applyInst p) := by
  rw [hI.1]
  rfl

theorem HInv.mainR {s : Store Nat} {H : List FunClo.Val} {W : List Val} (hI : HInv p s H W) :
    s.funcs[2]? = some (mainRInst p) := by
  rw [hI.1]
  rfl

/-! ## Values of first-order types -/

/-- **A value of a first-order type** is an integer, a boolean or a closure of a first-order
function type. -/
theorem fo_cases {v : FunClo.Val} {τ : Ty} (ht : ValTy v τ) (hfo : Ty.FO τ) :
    (∃ n, v = .int n) ∨ (∃ b, v = .bool b) ∨
      ∃ τ', ValTy v (.arr .int τ') ∧ Ty.FO τ' ∧ ∃ b ρ, v = .clo b ρ := by
  cases ht with
  | int n => exact .inl ⟨n, rfl⟩
  | bool b => exact .inr (.inl ⟨b, rfl⟩)
  | pair => exact hfo.elim
  | inl => exact hfo.elim
  | inr => exact hfo.elim
  | @clo b ρ Γ σ τ' hρ hb =>
    cases σ with
    | int => exact .inr (.inr ⟨τ', .clo hρ hb, hfo, b, ρ, rfl⟩)
    | bool => exact hfo.elim
    | prod => exact hfo.elim
    | sum => exact hfo.elim
    | arr => exact hfo.elim

/-- **The answer and the handles of a value of a first-order type** agree with those of its
representation. -/
theorem rep_ans {s : Store Nat} {H : List FunClo.Val} {W : List Val} (hI : HInv p s H W)
    {v : FunClo.Val} {τ : Ty} (ht : ValTy v τ) (hfo : Ty.FO τ) {w : Val}
    (hw : Rep p.table s v w) : readAns w = ansOf v ∧ HInv p s (push H v) (wpush W w) := by
  rcases fo_cases ht hfo with ⟨n, rfl⟩ | ⟨b, rfl⟩ | ⟨τ', hcl, hfo', b, ρ, rfl⟩
  · have hw' : w = .ref (.i31 n) := hw
    subst hw'
    exact ⟨rfl, hI⟩
  · have hw' : w = .ref (.i31 (if b then 1 else 0)) := hw
    subst hw'
    exact ⟨rfl, hI⟩
  · obtain ⟨addr, we, hw', -⟩ := id hw
    subst hw'
    refine ⟨rfl, hI.1, List.rel_append hI.2.1 (.cons hw .nil), fun u hu => ?_⟩
    rcases List.mem_append.1 hu with hu | hu
    · exact hI.2.2 u hu
    · rw [List.mem_singleton.1 hu]
      exact ⟨τ', hcl, hfo'⟩

/-! ## Single steps -/

/-- What a matched step provides: a run of the invocation of the question, returning a
representation of a value of a first-order type in an extended store. -/
def Matched (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (s : Store Nat)
    (W : List Val) (o : Op) (v : FunClo.Val) : Prop :=
  ∃ a args, invokeOf W o = some (a, args) ∧ ∃ s' w, Returns P host s a args s' w ∧ Ext s s' ∧
    Rep p.table s' v w ∧ ∃ τ, ValTy v τ ∧ Ty.FO τ

/-- The closure of a handle, its typing and its representation. -/
theorem handle_clo {s : Store Nat} {H : List FunClo.Val} {W : List Val} (hI : HInv p s H W)
    {h : Nat} {u : FunClo.Val} (hu : H[h]? = some u) :
    ∃ τ b ρ Γ, u = .clo b ρ ∧ EnvTy ρ Γ ∧ HasTy (.int :: .arr .int τ :: Γ) b τ ∧ Ty.FO τ := by
  obtain ⟨τ, hcl, hfo⟩ := hI.2.2 u (List.mem_of_getElem? hu)
  obtain ⟨b, ρ, Γ, rfl, hρ, hb⟩ := FunClo.ValTy.arr_inv hcl
  exact ⟨τ, b, ρ, Γ, rfl, hρ, hb, hfo⟩

theorem normal_single_inj {w w' : Val} (h : Outcome.normal [w] = .normal [w']) : w = w' := by
  injection h with h
  injection h

/-- `main n` is matched. -/
theorem step_fwd_main (hp : p.GOk) {s : Store Nat} {H : List FunClo.Val} {W : List Val}
    (hI : HInv p s H W) {n : BitVec 31} {v : FunClo.Val} (hst : p.Eval n v) :
    Matched P host p s W (.main n) v := by
  obtain ⟨k, hk⟩ := hst
  obtain ⟨s', w, hret, w', hw, hext, hrep⟩ := returns_of_tspec (mainR_tspec (P := P)
    (host := host) hp.2.2 hk) ⟨hI.mainR, hI.apply, rfl⟩ fun _ _ ⟨w, hw, _⟩ => ⟨w, hw⟩
  have hww : w = w' := normal_single_inj hw
  subst hww
  exact ⟨2, _, rfl, s', w, hret, hext, hrep, p.res, eval_sound k hp.1 (.cons (.int n) .nil) hk,
    hp.2.1⟩

/-- `call h m` is matched. -/
theorem step_fwd_call (hp : p.GOk) {s : Store Nat} {H : List FunClo.Val} {W : List Val}
    (hI : HInv p s H W) {h : Nat} {m : BitVec 31} {v : FunClo.Val}
    (hst : SrcStep p H (.call h m) v) : Matched P host p s W (.call h m) v := by
  obtain ⟨b, ρ, k, hH, hev⟩ := hst
  obtain ⟨wc, hW, hrc⟩ := forall₂_getElem? hI.2.1 hH
  obtain ⟨τ, b', ρ', Γ, he, hρ, hb, hfo⟩ := handle_clo hI hH
  cases he
  have happ := applyOK_of_spec (P := P) (host := host) hp.2.2 (spec_all hp.2.2 k) b ρ
    (.int m) v hev
  obtain ⟨s', w, hret, w', hw, hext, hrep⟩ := returns_of_tspec happ
    ⟨hI.apply, wc, .ref (.i31 m), rfl, hrc, rfl⟩ fun _ _ ⟨w, hw, _⟩ => ⟨w, hw⟩
  have hww : w = w' := normal_single_inj hw
  subst hww
  exact ⟨1, [wc, .ref (.i31 m)], by simp [invokeOf, hW], s', w, hret, hext, hrep, τ,
    eval_sound k hb (.cons (.int m) (.cons (.clo hρ hb) hρ)) hev, hfo⟩

/-- **A source step is matched** by an invocation. -/
theorem step_fwd (hp : p.GOk) {s : Store Nat} {H : List FunClo.Val} {W : List Val}
    (hI : HInv p s H W) {o : Op} {v : FunClo.Val} (hst : SrcStep p H o v) :
    Matched P host p s W o v := by
  cases o with
  | main n => exact step_fwd_main hp hI hst
  | call h m => exact step_fwd_call hp hI hst

/-- What a source step behind a returning invocation provides. -/
def Sourced (p : Prog) (s s' : Store Nat) (H : List FunClo.Val) (o : Op) (w : Val) : Prop :=
  ∃ v, SrcStep p H o v ∧ Ext s s' ∧ Rep p.table s' v w ∧ ∃ τ, ValTy v τ ∧ Ty.FO τ

/-- A returning invocation of `mainR` comes from a source step. -/
theorem step_bwd_main (hp : p.GOk) {s s' : Store Nat} {H : List FunClo.Val} {W : List Val}
    (hI : HInv p s H W) {n : BitVec 31} {f' : Frame} {w : Val}
    (hsteps : Steps P host (invoke s 2 [.ref (.i31 0), .ref (.i31 n)]) ⟨s', f', vals [w]⟩) :
    Sourced p s s' H (.main n) w := by
  rcases FunCloDiv.eval_or_div p n with ⟨v, k, hk⟩ | hdv
  · obtain ⟨w', hw, hext, hrep⟩ := (mainR_tspec (P := P) (host := host) hp.2.2 hk).invoke_vals
      ⟨hI.mainR, hI.apply, rfl⟩ hsteps
    have hww : w = w' := normal_single_inj hw
    subst hww
    exact ⟨v, ⟨k, hk⟩, hext, hrep, p.res, eval_sound k hp.1 (.cons (.int n) .nil) hk, hp.2.1⟩
  · exact ((mainR_div (P := P) (host := host) hp.2.2 hp.1 hdv).invoke_vals
      ⟨hI.mainR, hI.apply, rfl⟩ hsteps).elim

/-- A returning invocation of `apply` on a handle comes from a source step. -/
theorem step_bwd_call (hp : p.GOk) {s s' : Store Nat} {H : List FunClo.Val} {W : List Val}
    (hI : HInv p s H W) {h : Nat} {m : BitVec 31} {wc : Val} (hW : W[h]? = some wc)
    {f' : Frame} {w : Val}
    (hsteps : Steps P host (invoke s 1 [wc, .ref (.i31 m)]) ⟨s', f', vals [w]⟩) :
    Sourced p s s' H (.call h m) w := by
  obtain ⟨u, hH, hrc⟩ := forall₂_getElem?_rev hI.2.1 hW
  obtain ⟨τ, b, ρ, Γ, rfl, hρ, hb, hfo⟩ := handle_clo hI hH
  have henv := EnvTy.cons (FunClo.ValTy.int m) (.cons (.clo hρ hb) hρ)
  have hpre : s.funcs[1]? = some (applyInst p) ∧ ∃ wc' wu, [wc, .ref (.i31 m)] = [wc', wu] ∧
      Rep p.table s (.clo b ρ) wc' ∧ Rep p.table s (.int m) wu :=
    ⟨hI.apply, wc, .ref (.i31 m), rfl, hrc, rfl⟩
  rcases conv_or_div (.int m :: .clo b ρ :: ρ) b with ⟨k, v, hev⟩ | hdv
  · obtain ⟨w', hw, hext, hrep⟩ := (applyOK_of_spec (P := P) (host := host) hp.2.2
      (spec_all hp.2.2 k) b ρ (.int m) v hev).invoke_vals hpre hsteps
    have hww : w = w' := normal_single_inj hw
    subst hww
    exact ⟨v, ⟨b, ρ, k, hH, hev⟩, hext, hrep, τ, eval_sound k hb henv hev, hfo⟩
  · have hval : FSpecValid P host 1
        (Silmaril.Proofs.Wasm.Models.FunCloDiv.divApplySpec p b ρ (.int m)) := fun n =>
      (div_all (P := P) (host := host) hp.2.2 n).1 b ρ (.int m) _ τ henv hb hdv
    exact (hval.invoke_vals hpre hsteps).elim

/-- **An invocation that returns comes from a source step.** -/
theorem step_bwd (hp : p.GOk) {s s' : Store Nat} {H : List FunClo.Val} {W : List Val}
    (hI : HInv p s H W) {o : Op} {a : Nat} {args : List Val} {w : Val}
    (hinv : invokeOf W o = some (a, args)) (hret : Returns P host s a args s' w) :
    Sourced p s s' H o w := by
  obtain ⟨f', hsteps⟩ := hret
  cases o with
  | main n =>
    simp only [invokeOf, Option.some.injEq, Prod.mk.injEq] at hinv
    obtain ⟨rfl, rfl⟩ := hinv
    exact step_bwd_main hp hI hsteps
  | call h m =>
    simp only [invokeOf, Option.map_eq_some_iff, Prod.mk.injEq] at hinv
    obtain ⟨wc, hW, rfl, rfl⟩ := hinv
    exact step_bwd_call hp hI hW hsteps

/-! ## Runs -/

/-- **Source runs are Wasm runs.** -/
theorem run_fwd (hp : p.GOk) {H : List FunClo.Val} {t : List (Op × Ans)}
    (hr : SrcRun p H t) : ∀ {s : Store Nat} {W : List Val}, HInv p s H W → WRun P host s W t := by
  induction hr with
  | nil H => exact fun _ => .nil _ _
  | @cons H o v t hst _ ih =>
    intro s W hI
    obtain ⟨a, args, hinv, s', w, hret, hext, hrep, τ, ht, hfo⟩ :=
      step_fwd (P := P) (host := host) hp hI hst
    obtain ⟨hans, hI'⟩ := rep_ans (hI.mono hext) ht hfo hrep
    rw [← hans]
    exact .cons hinv hret (ih hI')

/-- **Wasm runs are source runs.** -/
theorem run_bwd (hp : p.GOk) {s : Store Nat} {W : List Val} {t : List (Op × Ans)}
    (hr : WRun P host s W t) : ∀ {H : List FunClo.Val}, HInv p s H W → SrcRun p H t := by
  induction hr with
  | nil s W => exact fun _ => .nil _
  | @cons s s' W o a args w t hinv hret _ ih =>
    intro H hI
    obtain ⟨v, hst, hext, hrep, τ, ht, hfo⟩ := step_bwd hp hI hinv hret
    obtain ⟨hans, hI'⟩ := rep_ans (hI.mono hext) ht hfo hrep
    rw [hans]
    exact .cons hst (ih hI')

/-- **The plays of the Wasm runs are the plays of the source runs.** -/
theorem wasmPlays_eq (hp : p.GOk) : wasmPlays P host p = srcPlays p := by
  ext x
  constructor
  · rintro ⟨t, hr, rfl⟩
    exact ⟨t, run_bwd hp hr (HInv.init p), rfl⟩
  · rintro ⟨t, hr, rfl⟩
    exact ⟨t, run_fwd hp hr (HInv.init p), rfl⟩

end Silmaril.Proofs.Wasm.Models.FunCloGame
