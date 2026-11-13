module

public import Silmaril.Wasm.Models.FXPres.Defs
public import Silmaril.Wasm.Models.FXV.Thms

/-!
# The configuration typing `TL`: structural lemmas

* `TL.append`, `TL.split`: typing of a concatenation is typing of the parts;
* `TL.weaken`: stack weakening;
* `TL.lift`: more labels and a return type (code typed with fewer stays typed);
* `TL.mono`: store extension and a longer slot typing;
* `VTy`, `ValsTy`: FX values at FX types; `TL.vals_inv`, `TL.vals`: a sequence of values is typed
  exactly by pushing its value types.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {E : TyEnv H} {s : Store H} {Γ : List TypeIdx}
  {Ls : List (List FTy)} {R : Option (List FTy)}

/-! ## Concatenation -/

theorem TL.append {a b : List AdminFX} {i m o : List FTy} (ha : TL E s Γ Ls R a i m)
    (hb : TL E s Γ Ls R b m o) : TL E s Γ Ls R (a ++ b) i o := by
  induction ha with
  | nil => exact hb
  | core hc hn _ ih => exact .core hc hn (ih hb)
  | br hl _ ih => exact .br hl (ih hb)
  | ret hR _ ih => exact .ret hR (ih hb)
  | contRef hk _ ih => exact .contRef hk (ih hb)
  | contNew h _ ih => exact .contNew h (ih hb)
  | contBind h h' _ ih => exact .contBind h h' (ih hb)
  | resume h hh _ ih => exact .resume h hh (ih hb)
  | resumeThrow h hx ht htt hh _ ih => exact .resumeThrow h hx ht htt hh (ih hb)
  | suspend hx ht htt _ ih => exact .suspend hx ht htt (ih hb)
  | block hbt hbody _ _ ih => exact .block hbt hbody (ih hb)
  | loop hbt hbody _ _ ih => exact .loop hbt hbody (ih hb)
  | if_ hbt h₁ h₂ _ _ _ ih => exact .if_ hbt h₁ h₂ (ih hb)
  | label hn hk hbd _ _ _ ih => exact .label hn hk hbd (ih hb)
  | frame hm hn hbd _ _ ih => exact .frame hm hn hbd (ih hb)
  | handler hh hbd _ _ ih => exact .handler hh hbd (ih hb)

/-- The head of a typed sequence is typed on its own. -/
theorem TL.uncons {x : AdminFX} {as : List AdminFX} {i o : List FTy}
    (h : TL E s Γ Ls R (x :: as) i o) : ∃ m, TL E s Γ Ls R [x] i m ∧ TL E s Γ Ls R as m o := by
  cases h with
  | core hc hn hr => exact ⟨_, .core hc hn .nil, hr⟩
  | br hl hr => exact ⟨_, .br hl .nil, hr⟩
  | ret hR hr => exact ⟨_, .ret hR .nil, hr⟩
  | contRef hk hr => exact ⟨_, .contRef hk .nil, hr⟩
  | contNew h hr => exact ⟨_, .contNew h .nil, hr⟩
  | contBind h h' hr => exact ⟨_, .contBind h h' .nil, hr⟩
  | resume h hh hr => exact ⟨_, .resume h hh .nil, hr⟩
  | resumeThrow h hx ht htt hh hr => exact ⟨_, .resumeThrow h hx ht htt hh .nil, hr⟩
  | suspend hx ht htt hr => exact ⟨_, .suspend hx ht htt .nil, hr⟩
  | block hbt hbody hr => exact ⟨_, .block hbt hbody .nil, hr⟩
  | loop hbt hbody hr => exact ⟨_, .loop hbt hbody .nil, hr⟩
  | if_ hbt h₁ h₂ hr => exact ⟨_, .if_ hbt h₁ h₂ .nil, hr⟩
  | label hn hk hbd hr => exact ⟨_, .label hn hk hbd .nil, hr⟩
  | frame hm hn hbd hr => exact ⟨_, .frame hm hn hbd .nil, hr⟩
  | handler hh hbd hr => exact ⟨_, .handler hh hbd .nil, hr⟩

/-- **A typed concatenation splits.** -/
theorem TL.split {a b : List AdminFX} {i o : List FTy} (h : TL E s Γ Ls R (a ++ b) i o) :
    ∃ m, TL E s Γ Ls R a i m ∧ TL E s Γ Ls R b m o := by
  induction a generalizing i with
  | nil => exact ⟨i, .nil, h⟩
  | cons x as ih =>
    obtain ⟨m₁, hx, hr⟩ := TL.uncons h
    obtain ⟨m, ha, hb⟩ := ih hr
    exact ⟨m, TL.append hx ha, hb⟩

theorem TL.split3 {a b c : List AdminFX} {i o : List FTy}
    (h : TL E s Γ Ls R (a ++ b ++ c) i o) :
    ∃ m₁ m₂, TL E s Γ Ls R a i m₁ ∧ TL E s Γ Ls R b m₁ m₂ ∧ TL E s Γ Ls R c m₂ o := by
  obtain ⟨m₂, hab, hc⟩ := TL.split h
  obtain ⟨m₁, ha, hb⟩ := TL.split hab
  exact ⟨m₁, m₂, ha, hb, hc⟩

theorem TL.append3 {a b c : List AdminFX} {i m₁ m₂ o : List FTy} (ha : TL E s Γ Ls R a i m₁)
    (hb : TL E s Γ Ls R b m₁ m₂) (hc : TL E s Γ Ls R c m₂ o) : TL E s Γ Ls R (a ++ b ++ c) i o :=
  TL.append (TL.append ha hb) hc

/-! ## Weakening -/

/-- **Stack weakening.** -/
theorem TL.weaken {c : List AdminFX} {i o : List FTy} (pre : List FTy)
    (h : TL E s Γ Ls R c i o) : TL E s Γ Ls R c (pre ++ i) (pre ++ o) := by
  induction h with
  | nil => exact .nil
  | core hc hn _ ih => simpa using TL.core (pre := pre ++ _) hc hn (by simpa using ih)
  | br hl _ ih => simpa using TL.br (pre := pre ++ _) hl ih
  | ret hR _ ih => simpa using TL.ret (pre := pre ++ _) hR ih
  | contRef hk _ ih => simpa using TL.contRef (pre := pre ++ _) hk (by simpa using ih)
  | contNew h _ ih => simpa using TL.contNew (pre := pre ++ _) h (by simpa using ih)
  | contBind h h' _ ih => simpa using TL.contBind (pre := pre ++ _) h h' (by simpa using ih)
  | resume h hh _ ih => simpa using TL.resume (pre := pre ++ _) h hh (by simpa using ih)
  | resumeThrow h hx ht htt hh _ ih =>
    simpa using TL.resumeThrow (pre := pre ++ _) h hx ht htt hh (by simpa using ih)
  | suspend hx ht htt _ ih => simpa using TL.suspend (pre := pre ++ _) hx ht htt (by simpa using ih)
  | block hbt hbody _ _ ih => simpa using TL.block (pre := pre ++ _) hbt hbody (by simpa using ih)
  | loop hbt hbody _ _ ih => simpa using TL.loop (pre := pre ++ _) hbt hbody (by simpa using ih)
  | if_ hbt h₁ h₂ _ _ _ ih => simpa using TL.if_ (pre := pre ++ _) hbt h₁ h₂ (by simpa using ih)
  | label hn hk hbd _ _ _ ih => simpa using TL.label (pre := pre ++ _) hn hk hbd (by simpa using ih)
  | frame hm hn hbd _ _ ih => simpa using TL.frame (pre := pre ++ _) hm hn hbd (by simpa using ih)
  | handler hh hbd _ _ ih => simpa using TL.handler (pre := pre ++ _) hh hbd (by simpa using ih)

/-! ## More labels and a return type -/

/-- Label contexts: `Ls'` extends `Ls`. -/
def LblLe (Ls Ls' : List (List FTy)) : Prop := ∀ (l : Nat) ts, Ls[l]? = some ts → Ls'[l]? = some ts

/-- Return types: `R'` extends `R`. -/
def RetLe (R R' : Option (List FTy)) : Prop := ∀ ts, R = some ts → R' = some ts

theorem LblLe.cons {Ls Ls' : List (List FTy)} (tl : List FTy) (h : LblLe Ls Ls') :
    LblLe (tl :: Ls) (tl :: Ls') := by
  intro l ts hl
  cases l with
  | zero => simpa using hl
  | succ l => simpa using h l ts (by simpa using hl)

theorem LblLe.nil (Ls : List (List FTy)) : LblLe [] Ls := by
  intro l ts hl
  simp at hl

theorem RetLe.none (R : Option (List FTy)) : RetLe none R := by
  intro ts h
  cases h

theorem hClauseOk_lbl {Ls Ls' : List (List FTy)} {ts : List FTy} {c : HClause}
    (hL : LblLe Ls Ls') (h : HClauseOk E s Ls ts c) : HClauseOk E s Ls' ts c := by
  cases c with
  | onLabel ta l =>
    obtain ⟨ti, tp, tr, ct', rs, h₁, h₂, h₃, h₄, h₅⟩ := h
    exact ⟨ti, tp, tr, ct', rs, h₁, h₂, h₃, h₄, hL _ _ h₅⟩
  | onSwitch => exact h.elim

theorem onClauseOk_lbl {Ls Ls' : List (List FTy)} {ts : List FTy} {c : OnClause}
    (hL : LblLe Ls Ls') (h : OnClauseOk E s Ls ts c) : OnClauseOk E s Ls' ts c := by
  cases c with
  | onLabel x l =>
    obtain ⟨ta, hx, hc⟩ := h
    exact ⟨ta, hx, hClauseOk_lbl hL hc⟩
  | onSwitch => exact h.elim

/-- **More labels and a return type.** -/
theorem TL.lift {c : List AdminFX} {i o : List FTy} {Ls' : List (List FTy)}
    {R' : Option (List FTy)} (h : TL E s Γ Ls R c i o) (hL : LblLe Ls Ls') (hR : RetLe R R') :
    TL E s Γ Ls' R' c i o := by
  induction h generalizing Ls' R' with
  | nil => exact .nil
  | core hc hn _ ih => exact .core hc hn (ih hL hR)
  | br hl _ ih => exact .br (hL _ _ hl) (ih hL hR)
  | ret hR' _ ih => exact .ret (hR _ hR') (ih hL hR)
  | contRef hk _ ih => exact .contRef hk (ih hL hR)
  | contNew h _ ih => exact .contNew h (ih hL hR)
  | contBind h h' _ ih => exact .contBind h h' (ih hL hR)
  | resume h hh _ ih => exact .resume h (fun c hc => onClauseOk_lbl hL (hh c hc)) (ih hL hR)
  | resumeThrow h hx ht htt hh _ ih =>
    exact .resumeThrow h hx ht htt (fun c hc => onClauseOk_lbl hL (hh c hc)) (ih hL hR)
  | suspend hx ht htt _ ih => exact .suspend hx ht htt (ih hL hR)
  | block hbt _ _ ihb ih => exact .block hbt (ihb (hL.cons _) hR) (ih hL hR)
  | loop hbt _ _ ihb ih => exact .loop hbt (ihb (hL.cons _) hR) (ih hL hR)
  | if_ hbt _ _ _ ih₁ ih₂ ih => exact .if_ hbt (ih₁ (hL.cons _) hR) (ih₂ (hL.cons _) hR) (ih hL hR)
  | label hn _ _ _ ihk ihb ih => exact .label hn (ihk hL hR) (ihb (hL.cons _) hR) (ih hL hR)
  | frame hm hn hbd _ _ ih => exact .frame hm hn hbd (ih hL hR)
  | handler hh hbd _ _ ih =>
    exact .handler (fun c hc => hClauseOk_lbl hL (hh c hc)) hbd (ih hL hR)

/-- Code typed with no labels and no return is typed anywhere. -/
theorem TL.lift0 {c : List AdminFX} {i o : List FTy} (Ls' : List (List FTy))
    (R' : Option (List FTy)) (h : TL E s Γ [] none c i o) : TL E s Γ Ls' R' c i o :=
  TL.lift h (LblLe.nil Ls') (RetLe.none R')

/-! ## Extension -/

theorem getElem?_prefix {Γ Γ' : List TypeIdx} (hΓ : Γ <+: Γ') {k : Nat} {ct : TypeIdx}
    (h : Γ[k]? = some ct) : Γ'[k]? = some ct := by
  obtain ⟨u, rfl⟩ := hΓ
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

/-- What the typing needs of an extension of the store. -/
structure StoreLe (E : TyEnv H) (s s' : Store H) : Prop where
  ct : ∀ {a i o}, E.ct s a i o → E.ct s' a i o
  tags : ∀ {ta : Nat} {ti : TagInst}, s.tags[ta]? = some ti → s'.tags[ta]? = some ti

theorem hClauseOk_mono {s' : Store H} {Ls : List (List FTy)} {ts : List FTy} {c : HClause}
    (hs : StoreLe E s s') (h : HClauseOk E s Ls ts c) : HClauseOk E s' Ls ts c := by
  cases c with
  | onLabel ta l =>
    obtain ⟨ti, tp, tr, ct', rs, h₁, h₂, h₃, h₄, h₅⟩ := h
    exact ⟨ti, tp, tr, ct', rs, hs.tags h₁, h₂, h₃, h₄, h₅⟩
  | onSwitch => exact h.elim

theorem onClauseOk_mono {s' : Store H} {Ls : List (List FTy)} {ts : List FTy} {c : OnClause}
    (hs : StoreLe E s s') (h : OnClauseOk E s Ls ts c) : OnClauseOk E s' Ls ts c := by
  cases c with
  | onLabel x l =>
    obtain ⟨ta, hx, hc⟩ := h
    exact ⟨ta, hx, hClauseOk_mono hs hc⟩
  | onSwitch => exact h.elim

/-- **Monotonicity** in the store and the slot typing. -/
theorem TL.mono {s' : Store H} {Γ' : List TypeIdx} {c : List AdminFX} {i o : List FTy}
    (hs : StoreLe E s s') (hΓ : Γ <+: Γ') (h : TL E s Γ Ls R c i o) : TL E s' Γ' Ls R c i o := by
  induction h with
  | nil => exact .nil
  | core hc hn _ ih => exact .core (hs.ct hc) hn ih
  | br hl _ ih => exact .br hl ih
  | ret hR _ ih => exact .ret hR ih
  | contRef hk _ ih => exact .contRef (getElem?_prefix hΓ hk) ih
  | contNew h _ ih => exact .contNew h ih
  | contBind h h' _ ih => exact .contBind h h' ih
  | resume h hh _ ih => exact .resume h (fun c hc => onClauseOk_mono hs (hh c hc)) ih
  | resumeThrow h hx ht htt hh _ ih =>
    exact .resumeThrow h hx (hs.tags ht) htt (fun c hc => onClauseOk_mono hs (hh c hc)) ih
  | suspend hx ht htt _ ih => exact .suspend hx (hs.tags ht) htt ih
  | block hbt _ _ ihb ih => exact .block hbt ihb ih
  | loop hbt _ _ ihb ih => exact .loop hbt ihb ih
  | if_ hbt _ _ _ ih₁ ih₂ ih => exact .if_ hbt ih₁ ih₂ ih
  | label hn _ _ _ ihk ihb ih => exact .label hn ihk ihb ih
  | frame hm hn _ _ ihb ih => exact .frame hm hn ihb ih
  | handler hh _ _ ihb ih => exact .handler (fun c hc => hClauseOk_mono hs (hh c hc)) ihb ih

/-! ## Values -/

/-- An FX value at an FX type. -/
def VTy (E : TyEnv H) (s : Store H) (Γ : List TypeIdx) : FVal → FTy → Prop
  | .val w, t => E.ct s w.toAdmin [] [t]
  | .cont k, t => ∃ ct, Γ[k]? = some ct ∧ t = .cont ct

/-- FX values at FX types. -/
abbrev ValsTy (E : TyEnv H) (s : Store H) (Γ : List TypeIdx) : List FVal → List FTy → Prop :=
  List.Forall₂ (VTy E s Γ)

theorem val_not_ctl (w : Val) : ¬ IsCtl w.toAdmin := by
  rcases w with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, IsCtl]

/-- Inversion at a Core instruction other than `br` and `return`. -/
theorem TL.core_inv {a : Admin} {as : List AdminFX} {i o : List FTy} (hn : ¬ IsCtl a)
    (h : TL E s Γ Ls R (.core a :: as) i o) :
    ∃ pre i₀ o₀, E.ct s a i₀ o₀ ∧ i = pre ++ i₀ ∧ TL E s Γ Ls R as (pre ++ o₀) o := by
  cases h with
  | core hc _ hr => exact ⟨_, _, _, hc, rfl, hr⟩
  | br => exact (hn trivial).elim
  | ret => exact (hn trivial).elim

/-- **Typed values push their value types.** -/
theorem TL.vals_inv (hval : ∀ {v : Val} {i o}, E.ct s v.toAdmin i o → i = [] ∧ ∃ t, o = [t])
    {vs : List FVal} {i o : List FTy} (h : TL E s Γ Ls R (fvals vs) i o) :
    ∃ T, o = i ++ T ∧ ValsTy E s Γ vs T := by
  induction vs generalizing i with
  | nil =>
    cases h
    exact ⟨[], by simp, .nil⟩
  | cons v vs ih =>
    cases v with
    | val w =>
      obtain ⟨pre, i₀, o₀, hc, rfl, hr⟩ := TL.core_inv (val_not_ctl w) h
      obtain ⟨rfl, t, rfl⟩ := hval hc
      obtain ⟨T, rfl, hT⟩ := ih hr
      exact ⟨t :: T, by simp, .cons hc hT⟩
    | cont k =>
      cases h with
      | contRef hk hr =>
        obtain ⟨T, rfl, hT⟩ := ih hr
        exact ⟨_ :: T, by simp, .cons ⟨_, hk, rfl⟩ hT⟩

/-- Values at their types are typed, under any stack, labels and return type. -/
theorem TL.vals {vs : List FVal} {T : List FTy} (h : ValsTy E s Γ vs T) (i : List FTy) :
    TL E s Γ Ls R (fvals vs) i (i ++ T) := by
  induction h generalizing i with
  | nil => simpa using (TL.nil : TL E s Γ Ls R [] i i)
  | @cons v t vs T hv _ ih =>
    cases v with
    | val w =>
      have h₂ := ih (i ++ [t])
      rw [List.append_assoc, List.singleton_append] at h₂
      simpa [FVal.toAdmin] using TL.core (pre := i) (as := fvals vs) hv (val_not_ctl w) h₂
    | cont k =>
      obtain ⟨ct, hk, rfl⟩ := hv
      have h₂ := ih (i ++ [.cont ct])
      rw [List.append_assoc, List.singleton_append] at h₂
      simpa [FVal.toAdmin] using TL.contRef (pre := i) (as := fvals vs) hk h₂

theorem ValsTy.mono {s' : Store H} {Γ' : List TypeIdx} {vs : List FVal} {T : List FTy}
    (hs : StoreLe E s s') (hΓ : Γ <+: Γ') (h : ValsTy E s Γ vs T) : ValsTy E s' Γ' vs T := by
  refine List.Forall₂.imp (fun v t hv => ?_) h
  cases v with
  | val w => exact hs.ct hv
  | cont k =>
    obtain ⟨ct, hk, rfl⟩ := hv
    exact ⟨ct, getElem?_prefix hΓ hk, rfl⟩

end Silmaril.Proofs.Wasm.Models.FXPres
