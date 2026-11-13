module

public import Silmaril.Proofs.Wasm.Models.FXPres.Redex

/-!
# Preservation at labels, frames and handler frames

Values leaving a label, frame or handler frame; `br` to the innermost label and to outer labels;
`return` through labels and out of frames; `br` and `return` reaching a handler frame (not
typed: a handler frame's body has no labels and no return); `drop` of a continuation; traps and
exceptions through contexts.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {E : TyEnv H} {P : Profile} {host : HostSemantics H}
  {fx : H → Option FuncFX} {s : Store H} {Γ : List TypeIdx} {K : List (Option ContFX)}
  {f : Frame} {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy}

/-- Values typed from the empty stack. -/
theorem vals_inv0 (hyp : CoreHyp E P host fx) {Ls₁ : List (List FTy)} {R₁ : Option (List FTy)}
    {vs : List FVal} {T : List FTy} (h : TL E s Γ Ls₁ R₁ (fvals vs) [] T) : ValsTy E s Γ vs T := by
  obtain ⟨T', hT', hv⟩ := TL.vals_inv hyp.val h
  simp only [List.nil_append] at hT'
  exact hT' ▸ hv

/-! ## Values leaving a context -/

theorem pres_labelVals (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {n : Nat} {k : List InstrFX} {vs : List FVal}
    (h : TL E s Γ Ls R [.label n k (fvals vs)] i o) : PresC E s Γ Ls R i o s K f (fvals vs) := by
  cases h with
  | label _ _ hb hr =>
    cases hr
    exact presC_same hyp hf hK (TL.vals (vals_inv0 hyp hb) i)

theorem pres_frameVals (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {n : Nat} {fi : Frame} {vs : List FVal}
    (h : TL E s Γ Ls R [.frame n fi (fvals vs)] i o) : PresC E s Γ Ls R i o s K f (fvals vs) := by
  cases h with
  | frame _ _ hb hr =>
    cases hr
    exact presC_same hyp hf hK (TL.vals (vals_inv0 hyp hb) i)

theorem pres_handlerVals (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀)
    (hK : KOk E s Γ K) {hs : List HClause} {vs : List FVal}
    (h : TL E s Γ Ls R [.handler hs (fvals vs)] i o) : PresC E s Γ Ls R i o s K f (fvals vs) := by
  cases h with
  | handler _ hb hr =>
    cases hr
    exact presC_same hyp hf hK (TL.vals (vals_inv0 hyp hb) i)

/-! ## `br` -/

theorem pres_brLabelZero (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {n : Nat} {k : List InstrFX} {vs' vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
    (hl : l.toNat = 0) (hn : vs.length = n)
    (h : TL E s Γ Ls R [.label n k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest)]
      i o) :
    PresC E s Γ Ls R i o s K f (fvals vs ++ k.map InstrFX.toAdmin) := by
  cases h with
  | label hn' hk hb hr =>
    cases hr
    obtain ⟨m₁, m₂, hvv, hbr, -⟩ := TL.split3 hb
    obtain ⟨m₀, hv', hv⟩ := TL.split hvv
    obtain ⟨T, h₂, hT⟩ := TL.vals_inv hyp.val hv
    cases hbr with
    | br hlk _ =>
      rw [hl] at hlk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hlk
      subst hlk
      obtain ⟨-, rfl⟩ := stack_split h₂ (by rw [← hT.length_eq, hn, hn'])
      exact presC_same hyp hf hK (TL.append (TL.vals hT i) (TL.weaken i hk))
    | core _ hn _ => exact absurd trivial hn

theorem pres_brLabelSucc (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {n : Nat} {k : List InstrFX} {vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
    (hl : 0 < l.toNat)
    (h : TL E s Γ Ls R [.label n k (fvals vs ++ [.core (.plain (.br l))] ++ rest)] i o) :
    PresC E s Γ Ls R i o s K f (fvals vs ++ [.core (.plain (.br (labelPred l)))]) := by
  cases h with
  | label _ _ hb hr =>
    cases hr
    obtain ⟨m₁, m₂, hv, hbr, -⟩ := TL.split3 hb
    obtain ⟨T, h₂, hT⟩ := TL.vals_inv hyp.val hv
    cases hbr with
    | @br _ _ _ _ pre ts _ _ hlk _ =>
      have hlk' : Ls[(labelPred l).toNat]? = some ts := by
        obtain ⟨j, hj⟩ : ∃ j, l.toNat = j + 1 := ⟨l.toNat - 1, by omega⟩
        rw [hj] at hlk
        simpa [show (labelPred l).toNat = l.toNat - 1 from rfl, hj] using hlk
      simp only [List.nil_append] at h₂
      subst h₂
      exact presC_same hyp hf hK
        (TL.append (TL.vals hT i) (by simpa using TL.br (pre := i ++ pre) hlk' .nil))
    | core _ hn _ => exact absurd trivial hn

theorem pres_brHandler {hs : List HClause} {vs : List FVal} {l : LabelIdx}
    {rest : List AdminFX} {P' : Prop}
    (h : TL E s Γ Ls R [.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest)] i o) : P' := by
  cases h with
  | handler _ hb _ =>
    obtain ⟨m₁, m₂, -, hbr, -⟩ := TL.split3 hb
    cases hbr with
    | br hlk _ => simp at hlk
    | core _ hn _ => exact absurd trivial hn

/-! ## `return` -/

theorem pres_returnLabel (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {n : Nat} {k : List InstrFX} {vs : List FVal} {rest : List AdminFX}
    (h : TL E s Γ Ls R [.label n k (fvals vs ++ [.core (.plain .return_)] ++ rest)] i o) :
    PresC E s Γ Ls R i o s K f (fvals vs ++ [.core (.plain .return_)]) := by
  cases h with
  | label _ _ hb hr =>
    cases hr
    obtain ⟨m₁, m₂, hv, hret, -⟩ := TL.split3 hb
    obtain ⟨T, h₂, hT⟩ := TL.vals_inv hyp.val hv
    cases hret with
    | @ret _ _ _ pre ts _ _ hR _ =>
      simp only [List.nil_append] at h₂
      subst h₂
      exact presC_same hyp hf hK
        (TL.append (TL.vals hT i) (by simpa using TL.ret (pre := i ++ pre) hR .nil))
    | core _ hn _ => exact absurd trivial hn

theorem pres_returnHandler {hs : List HClause} {vs : List FVal} {rest : List AdminFX}
    {P' : Prop}
    (h : TL E s Γ Ls R [.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest)] i o) : P' := by
  cases h with
  | handler _ hb _ =>
    obtain ⟨m₁, m₂, -, hret, -⟩ := TL.split3 hb
    cases hret with
    | ret hR _ => cases hR
    | core _ hn _ => exact absurd trivial hn

theorem pres_returnFrame (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {n : Nat} {fi : Frame} {vs' vs : List FVal} {rest : List AdminFX} (hn : vs.length = n)
    (h : TL E s Γ Ls R [.frame n fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest)]
      i o) :
    PresC E s Γ Ls R i o s K f (fvals vs) := by
  cases h with
  | frame _ hn' hb hr =>
    cases hr
    obtain ⟨m₁, m₂, hvv, hret, -⟩ := TL.split3 hb
    obtain ⟨m₀, -, hv⟩ := TL.split hvv
    obtain ⟨T, h₂, hT⟩ := TL.vals_inv hyp.val hv
    cases hret with
    | ret hR _ =>
      cases hR
      obtain ⟨-, rfl⟩ := stack_split h₂ (by rw [← hT.length_eq, hn, hn'])
      exact presC_same hyp hf hK (TL.vals hT i)
    | core _ hn _ => exact absurd trivial hn

/-! ## `drop` of a continuation -/

theorem pres_dropCont (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {k : Nat} (h : TL E s Γ Ls R [.contRef k, .core (.plain .drop)] i o) :
    PresC E s Γ Ls R i o s K f [] := by
  cases h with
  | contRef _ hr =>
    obtain ⟨pre, i₀, o₀, hc, heq, hr'⟩ := TL.core_inv (by simp [IsCtl]) hr
    obtain ⟨x, rfl, rfl⟩ := hyp.drop hc
    obtain ⟨rfl, -⟩ := stack_split heq rfl
    cases hr'
    exact presC_same hyp hf hK (by simp only [List.append_nil]; exact .nil)

/-! ## Exceptions through contexts -/

theorem pres_throwSeq (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {vs : List FVal} {a : Nat} {rest : List AdminFX}
    (h : TL E s Γ Ls R (fvals vs ++ cthrowing a ++ rest) i o) :
    PresC E s Γ Ls R i o s K f (cthrowing a) := by
  obtain ⟨m₁, m₂, -, ht, -⟩ := TL.split3 h
  exact presC_throwing hyp hf hK ht

theorem pres_throwLabel (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {n : Nat} {k : List InstrFX} {a : Nat}
    (h : TL E s Γ Ls R [.label n k (cthrowing a)] i o) :
    PresC E s Γ Ls R i o s K f (cthrowing a) := by
  cases h with
  | label _ _ hb _ => exact presC_throwing hyp hf hK hb

theorem pres_throwFrame (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {n : Nat} {fi : Frame} {a : Nat} (h : TL E s Γ Ls R [.frame n fi (cthrowing a)] i o) :
    PresC E s Γ Ls R i o s K f (cthrowing a) := by
  cases h with
  | frame _ _ hb _ => exact presC_throwing hyp hf hK hb

theorem pres_throwHandler (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {hs : List HClause} {a : Nat} (h : TL E s Γ Ls R [.handler hs (cthrowing a)] i o) :
    PresC E s Γ Ls R i o s K f (cthrowing a) := by
  cases h with
  | handler _ hb _ => exact presC_throwing hyp hf hK hb

end Silmaril.Proofs.Wasm.Models.FXPres
