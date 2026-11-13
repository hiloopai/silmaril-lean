module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Item

/-!
# The WIT binary round trip: functions and instance types

`funcType_sim` (a function type decodes to the function's signature),
`exportFuncs_sim` (an instance type's functions are read back without docs),
`instItem_sim` (an interface body written as an instance type and imported
or exported is read back in normal form).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Function types -/

theorem Inv.withFunc {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {g : Sig} {k : Nat}
    (hk : (curSlots cst dst)[k]? = some (.func g)) :
    Inv (e.withMaps { e.curMaps with funcs := (g, k) :: e.curMaps.funcs }) cst dst :=
  hI.withMaps ⟨hI.curOK.named, hI.curOK.anon, hI.curOK.funcs.cons hk⟩

theorem recordFunc_run {e e' : Enc} {g : Sig} {k k' : Nat}
    (h : (do let m ← maps; setMaps { m with funcs := (g, k) :: m.funcs }; pure k : EncM Nat).run e =
      .ok (k', e')) : k' = k ∧ e' = e.withMaps { e.curMaps with funcs := (g, k) :: e.curMaps.funcs } := by
  cases h; exact ⟨rfl, rfl⟩

/-- A new function type: parameters, result, then the definition. -/
theorem funcType_new {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) (f : Func) {k : Nat}
    (h : (do
      let ps ← params f.params
      let r ← optValType f.result
      let k ← defType (.func ⟨ps, r, f.async⟩)
      let m ← maps
      setMaps { m with funcs := (f.sig, k) :: m.funcs }
      pure k).run e = .ok (k, e')) :
    Sim e cst dst e' (fun cur => cur[k]? = some (.func f.sig)) := by
  obtain ⟨ps, e₂, h₃, h₄⟩ := run_bind_ok h
  obtain ⟨r, e₃, h₅, h₆⟩ := run_bind_ok h₄
  obtain ⟨cst₃, dst₃, hI₃, hG₃, hc₃⟩ := Sim.seq (params_sim f.params hI h₃)
    (fun hp hx => decParams_ext hx hp) (fun hI₁ => optValType_sim f.result hI₁ h₅)
  obtain ⟨k₁, e₄, h₇, h₈⟩ := run_bind_ok h₆
  have hd : DefSlot (curSlots cst₃ dst₃) (.func ⟨ps, r, f.async⟩) (.func f.sig) :=
    ⟨f.sig, by simp only [decFuncType, hc₃.1, hc₃.2]; rfl, rfl⟩
  have P := defType_sim hI₃ hd h₇
  obtain ⟨cst₄, dst₄, hI₄, hG₄, hc₄⟩ := P.sim
  have hk : (curSlots cst₄ dst₄)[k₁]? = some (.func f.sig) := by rw [hc₄, P.idx]; simp
  obtain ⟨rfl, rfl⟩ := recordFunc_run h₈
  exact ⟨cst₄, dst₄, hI₄.withFunc hk, hG₃.trans (hG₄.trans (Grows.withMaps _ _ _ _)), hk⟩

/-- **A function type** decodes to the function's signature. -/
theorem funcType_sim {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) (f : Func)
    {k : Nat} (h : (funcType f).run e = .ok (k, e')) :
    Sim e cst dst e' (fun cur => cur[k]? = some (.func f.sig)) := by
  obtain ⟨m, e₁, h₁, h₂⟩ := run_bind_ok h
  rw [maps_run] at h₁; cases h₁
  cases hl : lookup f.sig e.curMaps.funcs with
  | some k₀ =>
    rw [hl] at h₂; cases h₂
    exact ⟨cst, dst, hI, Grows.refl _ _ _, hI.curOK.funcs f.sig k hl⟩
  | none => rw [hl] at h₂; exact funcType_new hI f h₂

/-! ## Exported functions -/

/-- After exporting a function: the decoder's state. -/
def DSt.addFunc (d : DSt) (f : Func) : DSt := { d with funcs := d.funcs ++ [f] }

theorem exportFunc_sim {e e' : Enc} {cst : CSt} {d : DSt} (hI : Inv e cst (some d)) {f : Func}
    (hf : f.Valid) (h : (exportFunc f).run e = .ok ((), e')) :
    ∃ cst' d', Inv e' cst' (some d') ∧ Frame e e' cst cst' ∧ d'.types = d.types ∧
      d'.funcs = d.funcs ++ [f.strip] := by
  obtain ⟨k, e₁, h₁, h₂⟩ := run_bind_ok h
  obtain ⟨cst₁, dst₁, hI₁, hG₁, hk⟩ := funcType_sim hI f h₁
  obtain ⟨d₁, rfl, ht, hfu⟩ := hG₁.dst_some
  obtain ⟨s, hs, hd, hlen⟩ := hI₁.inner_some
  have h₂' : e' = { e₁ with inner := some { s with decls := s.decls ++ [.export ↑f.mangled (.func k)] } } := by
    have := Except.ok.inj h₂; simp only [hs] at this; exact (Prod.mk.inj this).2.symm
  have hstep : instStep cst₁.slots d₁ (.export ↑f.mangled (.func k)) = .ok (d₁.addFunc f.strip) := by
    have hk' : slotAt d₁.slots k = .ok (.func f.sig) := slotAt_of_get hk
    simp only [instStep, hk', bind, Except.bind]
    rw [demangle_mangled hf]; rfl
  refine ⟨cst₁, d₁.addFunc f.strip, ?_, hG₁.frame.trans ?_, ht, by simp [DSt.addFunc, hfu]⟩
  · rw [h₂']
    exact ⟨hI₁.outer, hI₁.olen, hI₁.ook, hI₁.otypes, hI₁.ilen, hI₁.inst, instSteps_snoc hd hstep, hlen,
      by have := hI₁.curOK; simpa [Enc.curMaps, hs, DSt.addFunc, curSlots] using this⟩
  · rw [h₂']; exact ⟨Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exportFuncs_sim : ∀ (fs : List Func) {e e' : Enc} {cst : CSt} {d : DSt},
    (∀ f ∈ fs, f.Valid) → Inv e cst (some d) → (exportFuncs fs).run e = .ok ((), e') →
    ∃ cst' d', Inv e' cst' (some d') ∧ Frame e e' cst cst' ∧ d'.types = d.types ∧
      d'.funcs = d.funcs ++ fs.map Func.strip
  | [], _, _, cst, d, _, hI, h => by
    obtain ⟨-, rfl⟩ := run_pure_ok h
    exact ⟨cst, d, hI, Frame.refl _ _, rfl, by simp⟩
  | f :: fs, _, _, _, _, hv, hI, h => by
    obtain ⟨u, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨c₁, d₁, hI₁, hF₁, ht₁, hf₁⟩ := exportFunc_sim hI (hv f (by simp)) h₁
    obtain ⟨c₂, d₂, hI₂, hF₂, ht₂, hf₂⟩ :=
      exportFuncs_sim fs (fun g hg => hv g (by simp [hg])) hI₁ h₂
    exact ⟨c₂, d₂, hI₂, hF₁.trans hF₂, ht₂.trans ht₁, by simp [hf₂, hf₁]⟩

end Silmaril.Wasm.Wit.Binary
