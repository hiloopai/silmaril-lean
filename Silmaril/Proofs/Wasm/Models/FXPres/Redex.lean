module

public import Silmaril.Proofs.Wasm.Models.FXPres.Ctx

/-!
# Preservation at the structural redexes

The conclusion of preservation, `PresC`, and its instances at the rules of `StepFXS` that do not
touch continuations: blocks, `loop`, `if`, labels, frames and handler frames with values, `br`,
`return`, traps and exceptions. Also the continuation-store facts (`KOk.mono`, `KOk.set`,
`KOk.push`).

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

/-- **The conclusion of preservation**: a longer slot typing `Γ'`, an extended store, a frame of
module `m₀`, a typed continuation store and the same type. -/
def PresC (E : TyEnv H) (s : Store H) (Γ : List TypeIdx) (Ls : List (List FTy))
    (R : Option (List FTy)) (i o : List FTy) (s' : Store H) (K' : List (Option ContFX))
    (f' : Frame) (code' : List AdminFX) : Prop :=
  ∃ Γ', Γ <+: Γ' ∧ E.ext s s' ∧ f'.module = E.m₀ ∧ KOk E s' Γ' K' ∧ TL E s' Γ' Ls R code' i o

theorem CoreHyp.le (hyp : CoreHyp E P host fx) {s s' : Store H} (h : E.ext s s') :
    StoreLe E s s' :=
  ⟨hyp.ct_mono h, hyp.tags_mono h⟩

theorem tys_length (E : TyEnv H) (ts : List CValType) : (E.tys ts).length = ts.length :=
  List.length_map _

/-! ## The continuation store -/

theorem ContTy.mono (hyp : CoreHyp E P host fx) {s' : Store H} {Γ' : List TypeIdx} {C : ContFX}
    {ct : TypeIdx} (h : ContTy E s Γ C ct) (hs : E.ext s s') (hΓ : Γ <+: Γ') :
    ContTy E s' Γ' C ct := by
  obtain ⟨ps, rs, hct, hC⟩ := h
  exact ⟨ps, rs, hct, fun s'' Γ'' c h₁ h₂ hc => hC s'' Γ'' c (hyp.ext_trans hs h₁) (hΓ.trans h₂) hc⟩

theorem KOk.mono (hyp : CoreHyp E P host fx) {s' : Store H} (h : KOk E s Γ K)
    (hs : E.ext s s') : KOk E s' Γ K := by
  refine ⟨h.1, fun k ct hk => ?_⟩
  rcases h.2 k ct hk with h₁ | ⟨C, hC, hty⟩
  · exact Or.inl h₁
  · exact Or.inr ⟨C, hC, ContTy.mono hyp hty hs (List.prefix_refl _)⟩

theorem KOk.set (h : KOk E s Γ K) (k : Nat) : KOk E s Γ (K.set k none) := by
  refine ⟨by simp [h.1], fun k' ct hk' => ?_⟩
  have hlt : k' < K.length := h.1 ▸ (List.getElem?_eq_some_iff.1 hk').1
  rw [List.getElem?_set]
  by_cases hkk : k = k'
  · subst hkk
    exact Or.inl (by simp [hlt])
  · simpa [hkk] using h.2 k' ct hk'

theorem KOk.push (hyp : CoreHyp E P host fx) {ct : TypeIdx} {C : ContFX} (h : KOk E s Γ K)
    (hC : ContTy E s (Γ ++ [ct]) C ct) : KOk E s (Γ ++ [ct]) (K ++ [some C]) := by
  refine ⟨by simp [h.1], fun k ct' hk => ?_⟩
  by_cases hlt : k < Γ.length
  · have hK : k < K.length := h.1 ▸ hlt
    rw [List.getElem?_append_left hlt] at hk
    rw [List.getElem?_append_left hK]
    rcases h.2 k ct' hk with h₁ | ⟨C', hC', hty⟩
    · exact Or.inl h₁
    · exact Or.inr ⟨C', hC', ContTy.mono hyp hty (hyp.ext_refl s) (List.prefix_append _ _)⟩
  · have hk' : k = Γ.length := by
      have := (List.getElem?_eq_some_iff.1 hk).1
      simp at this
      omega
    subst hk'
    simp at hk
    subst hk
    exact Or.inr ⟨C, by simp [h.1], hC⟩

/-! ## Same store, same continuations -/

theorem presC_same (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {code' : List AdminFX} (h : TL E s Γ Ls R code' i o) : PresC E s Γ Ls R i o s K f code' :=
  ⟨Γ, List.prefix_refl _, hyp.ext_refl s, hf, hK, h⟩

/-- `trap` has every type. -/
theorem trap_typed (hyp : CoreHyp E P host fx) : TL E s Γ Ls R [.core .trap] i o := by
  simpa using TL.core (pre := []) (hyp.trap s i o) (by simp [IsCtl]) (.nil : TL E s Γ Ls R [] o o)

theorem presC_trap (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K) :
    PresC E s Γ Ls R i o s K f [.core .trap] :=
  presC_same hyp hf hK (trap_typed hyp)

/-- **A typed `throwing a` has every type**, under any labels and return type. -/
theorem throwing_typed (hyp : CoreHyp E P host fx) {a : Nat} {i₁ o₁ : List FTy}
    {Ls₁ : List (List FTy)} {R₁ : Option (List FTy)} (h : TL E s Γ Ls₁ R₁ (cthrowing a) i₁ o₁) :
    TL E s Γ Ls R (cthrowing a) i o := by
  have hv : ¬ IsCtl (Admin.ref (.exn a)) := by simp [IsCtl]
  have ht : ¬ IsCtl (Admin.plain .throwRef) := by simp [IsCtl]
  obtain ⟨pre, i₀, o₀, hc, -, hr⟩ := TL.core_inv hv h
  obtain ⟨rfl, x, rfl⟩ := hyp.val (v := .ref (.exn a)) hc
  obtain ⟨pre₂, i₂, o₂, hc₂, heq, -⟩ := TL.core_inv ht hr
  obtain ⟨y, ⟨i₃, rfl⟩, hall⟩ := hyp.throwRef hc₂
  have heq' : pre ++ [x] = (pre₂ ++ i₃) ++ [y] := by rw [heq, List.append_assoc]
  have hxy : [x] = [y] := (List.append_inj' heq' rfl).2
  cases hxy
  have h₂ : TL E s Γ Ls R [.core (.plain .throwRef)] ([] ++ (i ++ [x])) o :=
    .core (hall i o) ht (by simpa using (TL.nil : TL E s Γ Ls R [] o o))
  simpa [cthrowing] using TL.core (pre := i) hc hv (by simpa using h₂)

theorem presC_throwing (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {a : Nat} {i₁ o₁ : List FTy} {Ls₁ : List (List FTy)} {R₁ : Option (List FTy)}
    (h : TL E s Γ Ls₁ R₁ (cthrowing a) i₁ o₁) : PresC E s Γ Ls R i o s K f (cthrowing a) :=
  presC_same hyp hf hK (throwing_typed hyp h)

/-! ## Blocks -/

/-- Values typed at `T` with `|T|` the length of the second half of a stack equation. -/
theorem stack_split {pre i T X : List FTy} (h : pre ++ X = i ++ T) (hl : X.length = T.length) :
    pre = i ∧ X = T :=
  List.append_inj' h hl

theorem blockType_eq (hf : f.module = E.m₀) {bt : BlockType} {t₁ t₂ u₁ u₂ : List CValType}
    (h : f.module.blockType? bt = some (t₁, t₂)) (h' : E.m₀.blockType? bt = some (u₁, u₂)) :
    t₁ = u₁ ∧ t₂ = u₂ := by
  rw [hf, h'] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem pres_block (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {bt : BlockType} {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (h : TL E s Γ Ls R (fvals vs ++ [.block bt body]) i o) :
    PresC E s Γ Ls R i o s K f
      [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)] := by
  obtain ⟨m, hv, hb⟩ := TL.split h
  obtain ⟨T, hmT, hT⟩ := TL.vals_inv hyp.val hv
  cases hb with
  | block hbt' hbody hr =>
    cases hr
    obtain ⟨h₁, h₂⟩ := blockType_eq hf hbt hbt'
    subst h₁ h₂
    obtain ⟨rfl, rfl⟩ := stack_split hmT (by rw [tys_length, ← hm, hT.length_eq])
    refine presC_same hyp hf hK (.label (by simp [tys_length]) .nil ?_ .nil)
    exact TL.append (by simpa using TL.vals (Ls := E.tys t₂ :: Ls) (R := R) hT []) hbody

theorem pres_loop (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {bt : BlockType} {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (h : TL E s Γ Ls R (fvals vs ++ [.loop bt body]) i o) :
    PresC E s Γ Ls R i o s K f
      [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)] := by
  obtain ⟨m, hv, hb⟩ := TL.split h
  obtain ⟨T, hmT, hT⟩ := TL.vals_inv hyp.val hv
  cases hb with
  | loop hbt' hbody hr =>
    cases hr
    obtain ⟨h₁, h₂⟩ := blockType_eq hf hbt hbt'
    subst h₁ h₂
    obtain ⟨rfl, rfl⟩ := stack_split hmT (by rw [tys_length, ← hm, hT.length_eq])
    have hk : TL E s Γ Ls R ([InstrFX.loop bt body].map InstrFX.toAdmin) (E.tys t₁) (E.tys t₂) := by
      simpa [InstrFX.toAdmin] using TL.loop (pre := []) hbt' hbody .nil
    refine presC_same hyp hf hK (.label (by simp [tys_length]) hk ?_ .nil)
    exact TL.append (by simpa using TL.vals (Ls := E.tys t₁ :: Ls) (R := R) hT []) hbody

/-- Inversion at `i32.const c; if`. -/
theorem pres_if (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {c : BitVec 32} {bt : BlockType} {b₁ b₂ b : List InstrFX} (hb : b = b₁ ∨ b = b₂)
    (h : TL E s Γ Ls R [.core (constI32 c), .if_ bt b₁ b₂] i o) :
    PresC E s Γ Ls R i o s K f [.block bt b] := by
  have hn : ¬ IsCtl (constI32 c) := val_not_ctl (Val.i32 c)
  obtain ⟨pre, i₀, o₀, hc, rfl, hr⟩ := TL.core_inv hn h
  obtain ⟨rfl, x, rfl⟩ := hyp.val (v := Val.i32 c) hc
  generalize hm : pre ++ [x] = m at hr
  cases hr with
  | if_ hbt h₁ h₂ hr =>
    cases hr
    rename_i t₁ t₂ pre'
    rw [List.append_nil]
    have hpre : pre = pre' ++ E.tys t₁ := (List.append_inj' hm rfl).1
    subst hpre
    rcases hb with rfl | rfl
    · exact presC_same hyp hf hK (.block hbt h₁ .nil)
    · exact presC_same hyp hf hK (.block hbt h₂ .nil)

end Silmaril.Proofs.Wasm.Models.FXPres
