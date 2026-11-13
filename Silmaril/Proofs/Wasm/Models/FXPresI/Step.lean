module

public import Silmaril.Proofs.Wasm.Models.FXPresI.Core

/-!
# `CtI` is preserved by Core steps

`stepI`: a Core step (any profile, any host) on `TL`-typed Core code keeps the store, the frame
and the type. The fragment's own rules are `unreachable`, `nop`, `drop`, the integer operators,
`trap` and `throw_ref` propagation; every other rule has an instruction outside the fragment on
its left-hand side (`TL.okI`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres Silmaril.Wasm.Models.FXPresI
open Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {ι : CValType → FTy} {nt : TypeIdx → FTy}
  {s : Store H} {Γ : List TypeIdx} {Ls : List (List FTy)} {R : Option (List FTy)}

local notation "TLI" => TL (envI (H := H) m₀ ι nt)

/-- What a Core step keeps. -/
def Keeps (m₀ : ModuleInst) (ι : CValType → FTy) (nt : TypeIdx → FTy) (c c' : Config H) :
    Prop :=
  ∀ {Γ : List TypeIdx} {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy},
    TL (envI m₀ ι nt) c.store Γ Ls R (c.code.map .core) i o →
    c'.store = c.store ∧ c'.frame = c.frame ∧
      TL (envI m₀ ι nt) c.store Γ Ls R (c'.code.map .core) i o

/-- A rewrite of the code alone. -/
theorem keeps_code {f : Frame} {cs cs' : List Admin}
    (h : ∀ {Γ Ls R i o}, TLI s Γ Ls R (cs.map .core) i o → TLI s Γ Ls R (cs'.map .core) i o) :
    Keeps m₀ ι nt ⟨s, f, cs⟩ ⟨s, f, cs'⟩ :=
  fun ht => ⟨rfl, rfl, h ht⟩

/-- A rule whose left-hand side has an instruction outside the fragment. -/
theorem keeps_absurd {c c' : Config H} (hb : ∃ a ∈ c.code, okB a = false) :
    Keeps m₀ ι nt c c' := by
  intro _ _ _ _ _ ht
  obtain ⟨a, ha, hf⟩ := hb
  have hok : okB a = true := TL.okI ht a ha
  exact absurd hok (by simp [hf])

/-- The result `trap`. -/
theorem keeps_trap {f : Frame} {cs : List Admin} : Keeps m₀ ι nt ⟨s, f, cs⟩ ⟨s, f, [.trap]⟩ :=
  keeps_code fun _ => TL.trapI

/-- `nop`. -/
theorem keeps_nop {f : Frame} : Keeps m₀ ι nt ⟨s, f, [.plain .nop]⟩ ⟨s, f, []⟩ := by
  refine keeps_code fun ht => ?_
  obtain ⟨pre, i₀, o₀, hc, rfl, hr⟩ := TL.invI (by rfl) (by simp [IsCtl]) ht
  cases hc
  cases hr
  simpa using (TL.nil : TLI s _ _ _ [] pre pre)

/-- `drop`. -/
theorem keeps_drop {f : Frame} (v : Val) :
    Keeps m₀ ι nt ⟨s, f, [v.toAdmin, .plain .drop]⟩ ⟨s, f, []⟩ := by
  refine keeps_code fun ht => ?_
  obtain ⟨pre, i₀, o₀, hc, rfl, hr⟩ := TL.core_inv (E := envI m₀ ι nt) (val_not_ctl v) ht
  obtain ⟨rfl, t, rfl⟩ := ctI_val hc
  obtain ⟨pre', i₁, o₁, hd, he, hr'⟩ := TL.invI (by rfl) (by simp [IsCtl]) hr
  cases hd
  cases hr'
  have hp : pre = pre' := List.append_inj_left' he rfl
  subst hp
  simpa using (TL.nil : TLI s _ _ _ [] pre pre)

/-- A unary integer operator. -/
theorem keeps_un {f : Frame} {t : IntType} {x : BitVec t.width} {b : Admin} {z : Admin}
    {tz : FTy} (hb : ∀ {i o : List FTy}, CtI s b i o → i = [intTy t] ∧ o = [tz])
    (hbo : okB b = true) (hbn : ¬ IsCtl b) (hz : CtI s z [] [tz]) :
    Keeps m₀ ι nt ⟨s, f, [.plain (.intConst t x), b]⟩ ⟨s, f, [z]⟩ := by
  refine keeps_code fun ht => ?_
  obtain ⟨pre, i₀, o₀, hc, rfl, hr⟩ := TL.invI (by rfl) (by simp [IsCtl]) ht
  cases hc
  obtain ⟨pre', i₁, o₁, hd, he, hr'⟩ := TL.invI hbo hbn hr
  obtain ⟨rfl, rfl⟩ := hb hd
  cases hr'
  have hp : pre = pre' := List.append_inj_left' he rfl
  subst hp
  simpa using TL.oneI (m₀ := m₀) (ι := ι) (nt := nt) (pre := pre) hz

/-- A binary integer operator. -/
theorem keeps_bin {f : Frame} {t : IntType} {x y : BitVec t.width} {b : Admin} {z : Admin}
    {tz : FTy} (hb : ∀ {i o : List FTy}, CtI s b i o → i = [intTy t, intTy t] ∧ o = [tz])
    (hbo : okB b = true) (hbn : ¬ IsCtl b) (hz : CtI s z [] [tz]) :
    Keeps m₀ ι nt ⟨s, f, [.plain (.intConst t x), .plain (.intConst t y), b]⟩ ⟨s, f, [z]⟩ := by
  refine keeps_code fun ht => ?_
  obtain ⟨pre, i₀, o₀, hc, rfl, hr⟩ := TL.invI (by rfl) (by simp [IsCtl]) ht
  cases hc
  obtain ⟨pre₁, i₁, o₁, hc₁, he₁, hr₁⟩ := TL.invI (by rfl) (by simp [IsCtl]) hr
  cases hc₁
  have hp₁ : pre₁ = pre ++ [intTy t] := by simpa using he₁.symm
  subst hp₁
  obtain ⟨pre', i₂, o₂, hd, he, hr'⟩ := TL.invI hbo hbn hr₁
  obtain ⟨rfl, rfl⟩ := hb hd
  cases hr'
  have hp : pre = pre' :=
    List.append_inj_left' (t₁ := [intTy t, intTy t]) (t₂ := [intTy t, intTy t]) (by simpa using he) rfl
  subst hp
  simpa using TL.oneI (m₀ := m₀) (ι := ι) (nt := nt) (pre := pre) hz

end Silmaril.Proofs.Wasm.Models.FXPresI
