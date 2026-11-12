module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.RMCode.Typed
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.RMCode.Step

/-!
# Round 8, memory SIMD: `Step_read` and `Step` at memory-SIMD-free code, from `FiresEraseD`

At a configuration `c` whose code holds no memory SIMD instruction (the store's function bodies
may hold some), a firing of a `Step_read` rule or of a store-changing `Step` rule at
`configVD hn c` gives a Core step, provided the rule keeps firing when the function code is
erased (`FiresEraseD`):

1. the erased firing is at `configV id (hostC hn c)` (`eraseC_configVD`), and it moves to the
   primitives over `String` at the host with no outcome (`HAgree.fires_read_iff`,
   `fires_step_iff`, with `RMHost.agreeOff_cross`);
2. `hostC hn c` is typed (`typed_hostC`) and keeps round 6's `NoCastV` (`noCastV_hostC`), so round
   6's leaves apply there (`Round6.Target.backwardUpToNC`);
3. the leaf's Core step at the named host store moves back to `c` (`step_setFS`), and the leaf's
   result is the erasure of the image of that successor, so by injectivity of `eraseC`
   (`CodeErase.Swap.eraseC_injective`) the original result is the image of the successor.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMCode

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS NoMemSimd StoreMS)
open Round7.MemSimd (configVD adminsToVD TypedD BwdUpToD msReadRules stepMSRules)
open Round8.RMHost (withFuncs setF agreeOff_cross)
open CodeErase.Swap (eraseC eraseC_injective)

variable {H : Type} {hn : H → String} {P : Profile}

/-! ## The named host store -/

theorem withFuncs_hostifyS (s : Store H) : withFuncs (hostifyS hn s) s.funcs = s := by
  cases s
  rfl

theorem hostifyS_withFuncs {u : Store String} {F : List (FuncInst H)}
    (h : u.funcs = F.map (hostSFI hn)) : hostifyS hn (withFuncs u F) = u := by
  cases u
  simp only [hostifyS, withFuncs] at h ⊢
  rw [h]

/-- The named host store has no Wasm function body. -/
theorem storeMS_hostifyS (s : Store H) : StoreMS (hostifyS hn s) := by
  intro fi hfi fn hcode
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hfi
  cases hcode

theorem setF_hostC (c : Config H) : setF c.store.funcs (hostC hn c) = c := by
  obtain ⟨s, f, is⟩ := c
  simp only [setF, hostC, withFuncs_hostifyS]

theorem eraseC_pair (a b : Value) : eraseC (.tuple [a, b]) = .tuple [eraseC a, eraseC b] := by
  rw [CodeErase.Swap.eraseC_tuple']
  rfl

/-- The leaf's successor at the named host store has memory-SIMD-free code. -/
theorem adminsMS_succ {c : Config H} {c' : Config String} (hms : AdminsMS c.code)
    (hs : Step P Round7.NullHost.nullHost (hostC hn c) c') : AdminsMS c'.code :=
  (Round7.MSPres.step_noMemSimd Round7.NullHost.nullHost_keepsMS hs
    ⟨storeMS_hostifyS c.store, hms⟩).code

/-! ## `Step_read` -/

/-- **The `Step_read` obligation at memory-SIMD-free code, from `FiresEraseD`.** -/
theorem read_of_firesErase {host : HostSemantics H}
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    {i : Nat} (hi : i ∉ msReadRules)
    (hE : FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i)
    (c : Config H) (w : Value) (hms : AdminsMS c.code) (hV : Round7.MSRest.VMS c)
    (hT : TypedD (simEnv (Prims.builtins P hn host)) hn c)
    (hF : Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  have hB := agreeOff_cross P hn host (id : String → String) Round7.NullHost.nullHost
  have hi43 : i ≠ 43 := by
    rintro rfl
    exact hi (by decide)
  -- the erased firing, at the primitives over `String`
  have hF₁ := hE c w hms hT hF
  rw [eraseC_pair, eraseC_configVD hn hms] at hF₁
  have hF₂ := (Round7.HAgree.fires_read_iff hB hi43 _).1 hF₁
  have hT₂ : Typed (simEnv (Prims.builtins P id Round7.NullHost.nullHost)) id (hostC hn c) :=
    typed_hostC hn hms ((Round7.HAgree.typedD_iff hB hn c).1 hT)
  have hNC := noCastV_hostC (hn := hn) (Round7.MemSimd.noCastV_of_noCastVM hV.1 hms)
  -- round 6's leaf at the named host store
  obtain ⟨is', js, hce, hw, hs⟩ := (Round6.Target.backwardUpToNC (hn := id)
    Function.injective_id Round7.NullHost.nullHost_finite hPs hPf).read i (hostC hn c) _ hNC hT₂
    hF₂
  have hw' : w = .list (adminsToV js) :=
    eraseC_injective (hw.trans (eraseC_adminsList js).symm)
  have hjs : AdminsMS js := Round7.VInv.adminsMS_of_codeEq hce (adminsMS_succ hms hs)
  -- back to `c`
  have hback := (step_setFS (host := host) hs c.store.funcs rfl).1
  rw [setF_hostC] at hback
  exact ⟨is', js, hce, by rw [hw', Round7.MemSimd.adminsToVD_eq js hjs], hback⟩

/-! ## `Step` -/

theorem stepBad_of {i : Nat} (h6 : 6 ≤ i) (hms₁ : i ∉ stepMSRules) (h8 : i ≠ 8) (h9 : i ≠ 9) :
    i ∉ Round7.HAgree.stepBad := by
  simp only [Round7.HAgree.stepBad, stepMSRules, List.mem_cons, List.mem_nil_iff,
    or_false] at hms₁ ⊢
  omega

/-- **A leaf's successor at the named host store gives `BwdUpToD` at `c`**: the step moves back
by `step_setFS`, and the leaf's result, the erasure of the image of its successor, is the erasure
of the image of that successor over the original function instances. -/
theorem bwdUpToD_of_leaf {host : HostSemantics H} {c : Config H} {w : Value}
    {c'h d'h : Config String} (hms : AdminsMS c.code) (hce : Bwd.ConfigEq c'h d'h)
    (hw : eraseC w = configV id d'h) (hs : Step P Round7.NullHost.nullHost (hostC hn c) c'h) :
    BwdUpToD hn P host c w := by
  obtain ⟨hback, hfuncs⟩ := step_setFS (host := host) hs c.store.funcs rfl
  have hback' : Step P host c (setF c.store.funcs c'h) := by
    rwa [setF_hostC] at hback
  have hd : AdminsMS d'h.code := Round7.VInv.adminsMS_of_codeEq hce.2.2 (adminsMS_succ hms hs)
  have hdf : d'h.store.funcs = c.store.funcs.map (hostSFI hn) := by
    rw [← hce.1, hfuncs]
    rfl
  have hhd : hostC hn (setF c.store.funcs d'h) = d'h := by
    obtain ⟨u, f, is⟩ := d'h
    simp only [hostC, setF, hostifyS_withFuncs hdf]
  have himg : eraseC (configVD hn (setF c.store.funcs d'h)) = configV id d'h := by
    rw [eraseC_configVD hn hd, hhd]
  have hst : (setF c.store.funcs c'h).store = (setF c.store.funcs d'h).store := by
    simp only [setF, hce.1]
  exact ⟨setF c.store.funcs c'h, setF c.store.funcs d'h, ⟨hst, hce.2.1, hce.2.2⟩,
    eraseC_injective (hw.trans himg.symm), hback'⟩


/-- **The `Step` obligation at memory-SIMD-free code, from `FiresEraseD`**, for the rules from 6
on other than 8, 9 and the memory SIMD store rules. -/
theorem step_of_firesErase {host : HostSemantics H}
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    {i : Nat} (h6 : 6 ≤ i) (hms₁ : i ∉ stepMSRules) (h8 : i ≠ 8) (h9 : i ≠ 9)
    (hE : FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step" i)
    (c : Config H) (w : Value) (hms : AdminsMS c.code) (hV : Round7.MSRest.VMS c)
    (hT : TypedD (simEnv (Prims.builtins P hn host)) hn c)
    (hF : Fires (simEnv (Prims.builtins P hn host)) "Step" i (.tuple [configVD hn c, w])) :
    BwdUpToD hn P host c w := by
  have hB : Round7.HAgree.AgreeOff (Prims.builtins P hn host)
      (Prims.builtins P id Round7.NullHost.nullHost) :=
    agreeOff_cross P hn host (id : String → String) Round7.NullHost.nullHost
  have hbad : i ∉ Round7.HAgree.stepBad := stepBad_of h6 hms₁ h8 h9
  -- the erased firing, at the primitives over `String`
  have hF₁ : Fires (simEnv (Prims.builtins P hn host)) "Step" i
      (.tuple [configV id (hostC hn c), eraseC w]) := by
    have h := hE c w hms hT hF
    rwa [eraseC_pair, eraseC_configVD hn hms] at h
  have hF₂ : Fires (simEnv (Prims.builtins P id Round7.NullHost.nullHost)) "Step" i
      (.tuple [configV id (hostC hn c), eraseC w]) :=
    (Round7.HAgree.fires_step_iff hB hbad _).1 hF₁
  have hT₂ : Typed (simEnv (Prims.builtins P id Round7.NullHost.nullHost)) id (hostC hn c) :=
    typed_hostC hn hms ((Round7.HAgree.typedD_iff hB hn c).1 hT)
  have hNC : Round6.Target.NoCastV (hostC hn c) :=
    noCastV_hostC (Round7.MemSimd.noCastV_of_noCastVM hV.1 hms)
  -- round 6's leaf at the named host store, and the way back
  obtain ⟨c'h, d'h, hce, hw, hs⟩ := (Round6.Target.backwardUpToNC (hn := id)
    Function.injective_id Round7.NullHost.nullHost_finite hPs hPf).step i h6 (hostC hn c) _ hNC
    hT₂ hF₂
  exact bwdUpToD_of_leaf hms hce hw hs

end Silmaril.Wasm.SpecTec.Sim.Round8.RMCode
