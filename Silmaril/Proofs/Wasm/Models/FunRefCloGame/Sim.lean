module

public import Silmaril.Proofs.Wasm.Models.FunRefCloGame.Harness

/-!
# The closure game of FunRefClo: the simulation between source and Wasm runs

* `HInvAt p s σ H W μ Ψ`: the store has the functions of `storeG p`; the cells `μ` represent the
  heap `σ` (FunRefCloCompile's `HeapRep`), which is typed by `Ψ`; the Wasm handles `W`
  represent the source handles `H`; every source handle is a closure of a first-order function
  type under `Ψ`. `HInv` hides `μ` and `Ψ`.
* `After`: what a step provides: an extended store, more cells, a larger heap typing, the final
  heap represented and typed, and a representation of a value of a first-order type.
  `HInvAt.after`: the invariant is re-established, and the answer read off the reference is the
  answer of the value.
* `step_fwd`, `step_bwd`: single steps (as for FunClo; a diverging step has no returning
  invocation, by `mainR_div` and FunRefCloDiv's `div_all`).
* `run_fwd`, `run_bwd`, `wasmPlays_eq`: runs correspond, and so do their plays.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloGame

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCloCompile Silmaril.Wasm.Models.FunRefCloGame
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRefClo (Tm eval Prog Heap Ty HasTy ValTy EnvTy HeapTy Out eval_sound)
open Silmaril.Wasm.Models.FunCloGame (Op Ans readAns wpush invokeOf Returns WRun)
open Silmaril.Proofs.Wasm.Models.FunRefCloCompile (Rep Ext HeapRep spec_all applyOK_of_spec
  applySpec)
open Silmaril.Proofs.Wasm.Models.FunRefCloDiv (div_all SDiv Typed conv_or_div divApplySpec)
open Silmaril.Proofs.Wasm.Models.FunCloGame (returns_of_tspec normal_single_inj forall₂_getElem?
  forall₂_getElem?_rev)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## The invariant -/

/-- **The invariant** with the cells `μ` and the heap typing `Ψ`. -/
def HInvAt (p : Prog) (s : Store Nat) (σ : Heap) (H : List FunRefClo.Val) (W : List Val)
    (μ : List Nat) (Ψ : List Ty) : Prop :=
  s.funcs = (storeG p).funcs ∧ HeapRep p.table μ s σ ∧ HeapTy Ψ σ ∧
    List.Forall₂ (Rep p.table μ s) H W ∧ ∀ v ∈ H, ∃ τ, ValTy Ψ v (.arr .int τ) ∧ Ty.FO τ

/-- **The invariant**, for some cells and heap typing. -/
def HInv (p : Prog) (s : Store Nat) (σ : Heap) (H : List FunRefClo.Val) (W : List Val) : Prop :=
  ∃ μ Ψ, HInvAt p s σ H W μ Ψ

theorem HInv.init (p : Prog) : HInv p (storeG p) [] [] [] :=
  ⟨[], [], rfl, HeapRep.empty _ _, .nil, .nil, by simp⟩

theorem HInvAt.apply {s : Store Nat} {σ : Heap} {H : List FunRefClo.Val} {W : List Val}
    {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) :
    s.funcs[1]? = some (applyInst p) := by
  rw [hI.1]
  rfl

theorem HInvAt.mainR {s : Store Nat} {σ : Heap} {H : List FunRefClo.Val} {W : List Val}
    {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) :
    s.funcs[2]? = some (mainRInst p) := by
  rw [hI.1]
  rfl

/-! ## Values of first-order types -/

/-- **A value of a first-order type** is an integer, a boolean or a closure of a first-order
function type. -/
theorem fo_cases {Ψ : List Ty} {v : FunRefClo.Val} {τ : Ty} (ht : ValTy Ψ v τ)
    (hfo : Ty.FO τ) : (∃ n, v = .int n) ∨ (∃ b, v = .bool b) ∨
      ∃ τ', ValTy Ψ v (.arr .int τ') ∧ Ty.FO τ' ∧ ∃ b ρ, v = .clo b ρ := by
  cases ht with
  | int n => exact .inl ⟨n, rfl⟩
  | bool b => exact .inr (.inl ⟨b, rfl⟩)
  | pair => exact hfo.elim
  | inl => exact hfo.elim
  | inr => exact hfo.elim
  | loc => exact hfo.elim
  | @clo b ρ Γ σ τ' hρ hb =>
    cases σ with
    | int => exact .inr (.inr ⟨τ', .clo hρ hb, hfo, b, ρ, rfl⟩)
    | bool => exact hfo.elim
    | prod => exact hfo.elim
    | sum => exact hfo.elim
    | arr => exact hfo.elim
    | ref => exact hfo.elim

/-- What a step provides, from the cells `μ` and the heap typing `Ψ` in the store `s`. -/
def After (p : Prog) (s : Store Nat) (μ : List Nat) (Ψ : List Ty) (s' : Store Nat) (σ' : Heap)
    (v : FunRefClo.Val) (w : Val) : Prop :=
  ∃ μ' Ψ' τ, Ext s s' ∧ μ <+: μ' ∧ Ψ <+: Ψ' ∧ HeapRep p.table μ' s' σ' ∧ HeapTy Ψ' σ' ∧
    Rep p.table μ' s' v w ∧ ValTy Ψ' v τ ∧ Ty.FO τ

theorem forall₂_mono {μ μ' : List Nat} {s s' : Store Nat} (hμ : μ <+: μ')
    (hs : Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt s s') :
    ∀ {H : List FunRefClo.Val} {W : List Val}, List.Forall₂ (Rep p.table μ s) H W →
      List.Forall₂ (Rep p.table μ' s') H W
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (h.mono hμ hs) (forall₂_mono hμ hs hl)

/-- The handles keep their types in a larger heap typing. -/
theorem handles_mono {Ψ Ψ' : List Ty} (hΨ : Ψ <+: Ψ') {H : List FunRefClo.Val}
    (h : ∀ v ∈ H, ∃ τ, ValTy Ψ v (.arr .int τ) ∧ Ty.FO τ) :
    ∀ v ∈ H, ∃ τ, ValTy Ψ' v (.arr .int τ) ∧ Ty.FO τ := fun v hv =>
  let ⟨τ, ht, hfo⟩ := h v hv
  ⟨τ, ht.mono hΨ, hfo⟩

/-- **After a step, the invariant holds again**, and the answer read off the reference is the
answer of the value. -/
theorem HInvAt.after {s s' : Store Nat} {σ σ' : Heap} {H : List FunRefClo.Val} {W : List Val}
    {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) {v : FunRefClo.Val} {w : Val}
    (ha : After p s μ Ψ s' σ' v w) :
    readAns w = ansOf v ∧ HInv p s' σ' (push H v) (wpush W w) := by
  obtain ⟨μ', Ψ', τ, hext, hμ, hΨ, hh, hσ, hw, ht, hfo⟩ := ha
  have hF : List.Forall₂ (Rep p.table μ' s') H W := forall₂_mono hμ hext.1 hI.2.2.2.1
  have hH : ∀ u ∈ H, ∃ τ, ValTy Ψ' u (.arr .int τ) ∧ Ty.FO τ := handles_mono hΨ hI.2.2.2.2
  have hfn : s'.funcs = (storeG p).funcs := hext.2.trans hI.1
  rcases fo_cases ht hfo with ⟨n, rfl⟩ | ⟨b, rfl⟩ | ⟨τ', hcl, hfo', b, ρ, rfl⟩
  · have hw' : w = .ref (.i31 n) := hw
    subst hw'
    exact ⟨rfl, μ', Ψ', hfn, hh, hσ, hF, hH⟩
  · have hw' : w = .ref (.i31 (if b then 1 else 0)) := hw
    subst hw'
    exact ⟨rfl, μ', Ψ', hfn, hh, hσ, hF, hH⟩
  · obtain ⟨addr, we, hw', -⟩ := id hw
    subst hw'
    refine ⟨rfl, μ', Ψ', hfn, hh, hσ, List.rel_append hF (.cons hw .nil), fun u hu => ?_⟩
    rcases List.mem_append.1 hu with hu | hu
    · exact hH u hu
    · rw [List.mem_singleton.1 hu]
      exact ⟨τ', hcl, hfo'⟩

/-! ## Single steps -/

/-- The closure of a handle and its typing. -/
theorem handle_clo {s : Store Nat} {σ : Heap} {H : List FunRefClo.Val} {W : List Val}
    {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) {h : Nat} {u : FunRefClo.Val}
    (hu : H[h]? = some u) : ∃ τ b ρ Γ, u = .clo b ρ ∧ EnvTy Ψ ρ Γ ∧
      HasTy (.int :: .arr .int τ :: Γ) b τ ∧ Ty.FO τ := by
  obtain ⟨τ, hcl, hfo⟩ := hI.2.2.2.2 u (List.mem_of_getElem? hu)
  obtain ⟨b, ρ, Γ, rfl, hρ, hb⟩ := FunRefClo.ValTy.arr_inv hcl
  exact ⟨τ, b, ρ, Γ, rfl, hρ, hb, hfo⟩

/-- The typed result of a step, as an `After` with the representation. -/
theorem after_of {s s' : Store Nat} {σ' : Heap} {μ μ' : List Nat} {Ψ : List Ty} {τ : Ty}
    {v : FunRefClo.Val} {w : Val} (hext : Ext s s') (hμ : μ <+: μ')
    (hh : HeapRep p.table μ' s' σ') (hw : Rep p.table μ' s' v w) (ho : Out Ψ τ v σ')
    (hfo : Ty.FO τ) : After p s μ Ψ s' σ' v w :=
  let ⟨Ψ', hΨ, hσ, ht⟩ := ho
  ⟨μ', Ψ', τ, hext, hμ, hΨ, hh, hσ, hw, ht, hfo⟩

/-- What a matched step provides. -/
def Matched (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (s : Store Nat)
    (μ : List Nat) (Ψ : List Ty) (W : List Val) (o : Op) (v : FunRefClo.Val) (σ' : Heap) :
    Prop :=
  ∃ a args, invokeOf W o = some (a, args) ∧ ∃ s' w, Returns P host s a args s' w ∧
    After p s μ Ψ s' σ' v w

/-- `main n` is matched. -/
theorem step_fwd_main (hp : p.GOk) {s : Store Nat} {σ σ' : Heap} {H : List FunRefClo.Val}
    {W : List Val} {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) {n : BitVec 31}
    {v : FunRefClo.Val} {k : Nat} (hk : eval k σ [.int n] p.body = some (v, σ')) :
    Matched P host p s μ Ψ W (.main n) v σ' := by
  obtain ⟨s', w, hret, w', μ', hw, hext, hμ, hh, hrep⟩ := returns_of_tspec
    (mainR_tspec (P := P) (host := host) hp.2.2 hk μ) ⟨hI.mainR, hI.apply, hI.2.1, rfl⟩
    fun _ _ ⟨w, _, hw, _⟩ => ⟨w, hw⟩
  have hww : w = w' := normal_single_inj hw
  subst hww
  exact ⟨2, _, rfl, s', w, hret, after_of hext hμ hh hrep
    (eval_sound k hp.1 hI.2.2.1 (.cons (.int n) .nil) hk) hp.2.1⟩

/-- `call h m` is matched. -/
theorem step_fwd_call (hp : p.GOk) {s : Store Nat} {σ σ' : Heap} {H : List FunRefClo.Val}
    {W : List Val} {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) {h : Nat}
    {m : BitVec 31} {v : FunRefClo.Val} (hst : SrcStep p σ H (.call h m) v σ') :
    Matched P host p s μ Ψ W (.call h m) v σ' := by
  obtain ⟨b, ρ, k, hH, hev⟩ := hst
  obtain ⟨wc, hW, hrc⟩ := forall₂_getElem? hI.2.2.2.1 hH
  obtain ⟨τ, b', ρ', Γ, he, hρ, hb, hfo⟩ := handle_clo hI hH
  cases he
  have happ := applyOK_of_spec (P := P) (host := host) hp.2.2 (spec_all hp.2.2 k) b ρ
    (.int m) v σ σ' μ hev
  obtain ⟨s', w, hret, w', μ', hw, hext, hμ, hh, hrep⟩ := returns_of_tspec happ
    ⟨hI.apply, hI.2.1, wc, .ref (.i31 m), rfl, hrc, rfl⟩ fun _ _ ⟨w, _, hw, _⟩ => ⟨w, hw⟩
  have hww : w = w' := normal_single_inj hw
  subst hww
  exact ⟨1, [wc, .ref (.i31 m)], by simp [invokeOf, hW], s', w, hret, after_of hext hμ hh hrep
    (eval_sound k hb hI.2.2.1 (.cons (.int m) (.cons (.clo hρ hb) hρ)) hev) hfo⟩

/-- **A source step is matched** by an invocation. -/
theorem step_fwd (hp : p.GOk) {s : Store Nat} {σ σ' : Heap} {H : List FunRefClo.Val}
    {W : List Val} {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) {o : Op}
    {v : FunRefClo.Val} (hst : SrcStep p σ H o v σ') : Matched P host p s μ Ψ W o v σ' := by
  cases o with
  | main n =>
    obtain ⟨k, hk⟩ := hst
    exact step_fwd_main hp hI hk
  | call h m => exact step_fwd_call hp hI hst

/-- What a source step behind a returning invocation provides. -/
def Sourced (p : Prog) (s : Store Nat) (σ : Heap) (H : List FunRefClo.Val) (μ : List Nat)
    (Ψ : List Ty) (o : Op) (s' : Store Nat) (w : Val) : Prop :=
  ∃ v σ', SrcStep p σ H o v σ' ∧ After p s μ Ψ s' σ' v w

/-- A returning invocation of `mainR` comes from a source step. -/
theorem step_bwd_main (hp : p.GOk) {s s' : Store Nat} {σ : Heap} {H : List FunRefClo.Val}
    {W : List Val} {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) {n : BitVec 31}
    {f' : Frame} {w : Val}
    (hsteps : Steps P host (invoke s 2 [.ref (.i31 0), .ref (.i31 n)]) ⟨s', f', vals [w]⟩) :
    Sourced p s σ H μ Ψ (.main n) s' w := by
  have hpre : mainRPre p n σ μ s [.ref (.i31 0), .ref (.i31 n)] :=
    ⟨hI.mainR, hI.apply, hI.2.1, rfl⟩
  rcases conv_or_div σ [.int n] p.body with ⟨k, v, σ', hk⟩ | hdv
  · obtain ⟨w', μ', hw, hext, hμ, hh, hrep⟩ :=
      (mainR_tspec (P := P) (host := host) hp.2.2 hk μ).invoke_vals hpre hsteps
    have hww : w = w' := normal_single_inj hw
    subst hww
    exact ⟨v, σ', ⟨k, hk⟩, after_of hext hμ hh hrep
      (eval_sound k hp.1 hI.2.2.1 (.cons (.int n) .nil) hk) hp.2.1⟩
  · have hT : Typed [.int] σ [.int n] := ⟨Ψ, hI.2.2.1, .cons (.int n) .nil⟩
    exact ((mainR_div (P := P) (host := host) hp.2.2 hp.1 hT hdv μ).invoke_vals hpre
      hsteps).elim

/-- A returning invocation of `apply` on a handle comes from a source step. -/
theorem step_bwd_call (hp : p.GOk) {s s' : Store Nat} {σ : Heap} {H : List FunRefClo.Val}
    {W : List Val} {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) {h : Nat}
    {m : BitVec 31} {wc : Val} (hW : W[h]? = some wc) {f' : Frame} {w : Val}
    (hsteps : Steps P host (invoke s 1 [wc, .ref (.i31 m)]) ⟨s', f', vals [w]⟩) :
    Sourced p s σ H μ Ψ (.call h m) s' w := by
  obtain ⟨u, hH, hrc⟩ := forall₂_getElem?_rev hI.2.2.2.1 hW
  obtain ⟨τ, b, ρ, Γ, rfl, hρ, hb, hfo⟩ := handle_clo hI hH
  have henv : EnvTy Ψ (.int m :: .clo b ρ :: ρ) (.int :: .arr .int τ :: Γ) :=
    .cons (.int m) (.cons (.clo hρ hb) hρ)
  rcases conv_or_div σ (.int m :: .clo b ρ :: ρ) b with ⟨k, v, σ', hev⟩ | hdv
  · obtain ⟨w', μ', hw, hext, hμ, hh, hrep⟩ := (applyOK_of_spec (P := P) (host := host)
      hp.2.2 (spec_all hp.2.2 k) b ρ (.int m) v σ σ' μ hev).invoke_vals
      ⟨hI.apply, hI.2.1, wc, .ref (.i31 m), rfl, hrc, rfl⟩ hsteps
    have hww : w = w' := normal_single_inj hw
    subst hww
    exact ⟨v, σ', ⟨b, ρ, k, hH, hev⟩, after_of hext hμ hh hrep
      (eval_sound k hb hI.2.2.1 henv hev) hfo⟩
  · have hval : FSpecValid P host 1 (divApplySpec p b ρ (.int m) σ μ) := fun n =>
      (div_all (P := P) (host := host) hp.2.2 n).1 b ρ (.int m) σ μ _ τ
        ⟨Ψ, hI.2.2.1, henv⟩ hb hdv
    exact (hval.invoke_vals ⟨hI.apply, hI.2.1, wc, .ref (.i31 m), rfl, hrc, rfl⟩ hsteps).elim

/-- **An invocation that returns comes from a source step.** -/
theorem step_bwd (hp : p.GOk) {s s' : Store Nat} {σ : Heap} {H : List FunRefClo.Val}
    {W : List Val} {μ : List Nat} {Ψ : List Ty} (hI : HInvAt p s σ H W μ Ψ) {o : Op} {a : Nat}
    {args : List Val} {w : Val} (hinv : invokeOf W o = some (a, args))
    (hret : Returns P host s a args s' w) : Sourced p s σ H μ Ψ o s' w := by
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
theorem run_fwd (hp : p.GOk) {σ : Heap} {H : List FunRefClo.Val} {t : List (Op × Ans)}
    (hr : SrcRun p σ H t) :
    ∀ {s : Store Nat} {W : List Val}, HInv p s σ H W → WRun P host s W t := by
  induction hr with
  | nil σ H => exact fun _ => .nil _ _
  | @cons σ σ' H o v t hst _ ih =>
    rintro s W ⟨μ, Ψ, hI⟩
    obtain ⟨a, args, hinv, s', w, hret, haft⟩ := step_fwd (P := P) (host := host) hp hI hst
    obtain ⟨hans, hI'⟩ := hI.after haft
    rw [← hans]
    exact .cons hinv hret (ih hI')

/-- **Wasm runs are source runs.** -/
theorem run_bwd (hp : p.GOk) {s : Store Nat} {W : List Val} {t : List (Op × Ans)}
    (hr : WRun P host s W t) :
    ∀ {σ : Heap} {H : List FunRefClo.Val}, HInv p s σ H W → SrcRun p σ H t := by
  induction hr with
  | nil s W => exact fun _ => .nil _ _
  | @cons s s' W o a args w t hinv hret _ ih =>
    rintro σ H ⟨μ, Ψ, hI⟩
    obtain ⟨v, σ', hst, haft⟩ := step_bwd hp hI hinv hret
    obtain ⟨hans, hI'⟩ := hI.after haft
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

end Silmaril.Proofs.Wasm.Models.FunRefCloGame
