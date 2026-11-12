module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.FiresB
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostD.Thms

/-!
# Round 7, `BD`: the three pairs of builtins, and what moves between them

`HAgree.AgreeOff` holds for the three builtins of round 7: `BD P hn host` (`$hostcall` keyed on
`storeVD` images), `BM P hn host = withVBytes (Prims.builtins P hn host)` and round 6's
`BI = Prims.builtins P hn host` (`agreeOff_bd_bm`, `agreeOff_bm_bi`, `agreeOff_bd_bi`). For any two
builtins that agree off `$vbytes_` and `$hostcall`:

* `typedD_iff`: `TypedD` reads alike, at every configuration;
* `fires_pure_iff`, `fires_read_iff` (rules other than 43) and `fires_step_iff` (rules outside
  `stepBad = [1, 2, 3, 4, 5, 8, 9, 23]`), from `Fires`, and `firesB_pure_iff`, `firesB_read_iff`,
  `firesB_step_iff` at round 6's backend reading;
* `backwardUpToDRestSH_agree`: the per-rule backward obligations of the rules without memory SIMD
  and **without the host calls** (`BackwardUpToDRestSH`, `Step` 8 and 9 left out) move across.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (BM withVBytes TypedD BwdUpToD configVD adminsToVD msReadRules stepMSRules)
open Round7.HostD (BD)

variable {B₁ B₂ B₃ : Builtins} {H : Type}

/-! ## The three pairs -/

theorem agreeOff_trans (h₁ : AgreeOff B₁ B₂) (h₂ : AgreeOff B₂ B₃) : AgreeOff B₁ B₃ :=
  fun x ws hx hx' => (h₁ x ws hx hx').trans (h₂ x ws hx hx')

/-- **`BD` and `BM` agree off `$hostcall`**, so off `$vbytes_` and `$hostcall`. -/
theorem agreeOff_bd_bm (P : Profile) (hn : H → String) (host : HostSemantics H) :
    AgreeOff (BD P hn host) (BM P hn host) :=
  fun _ ws _ hx => Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.bd_call_of_ne hx ws

/-- **`BM` and round 6's `BI` agree off `$vbytes_`.** -/
theorem agreeOff_bm_bi (P : Profile) (hn : H → String) (host : HostSemantics H) :
    AgreeOff (BM P hn host) (Prims.builtins P hn host) :=
  agreeOff_withVBytes _

/-- **`BD` and round 6's `BI` agree off `$vbytes_` and `$hostcall`.** -/
theorem agreeOff_bd_bi (P : Profile) (hn : H → String) (host : HostSemantics H) :
    AgreeOff (BD P hn host) (Prims.builtins P hn host) :=
  agreeOff_trans (agreeOff_bd_bm P hn host) (agreeOff_bm_bi P hn host)

/-! ## Typing and single rules -/

/-- **`TypedD` reads alike** at builtins that agree off `$vbytes_` and `$hostcall`. -/
theorem typedD_iff (hB : AgreeOff B₁ B₂) (hn : H → String) (c : Config H) :
    TypedD (simEnv B₁) hn c ↔ TypedD (simEnv B₂) hn c :=
  hasTyp_iff hB defsOk_empty typsG_empty rg_config

/-- The store-changing rules of `Step` off memory SIMD and off the host calls are not in
`stepBad`. -/
theorem not_stepBad {i : Nat} (h6 : 6 ≤ i) (hi : i ∉ stepMSRules) (h8 : i ≠ 8) (h9 : i ≠ 9) :
    i ∉ stepBad := by
  intro hm
  have h23 : i ≠ 23 := fun h => hi (by rw [h]; decide)
  simp only [stepBad, List.mem_cons, List.not_mem_nil, or_false] at hm
  omega

theorem firesB_pure_iff (hB : AgreeOff B₁ B₂) (i : Nat) (v : Value) :
    Round6.Reading.FiresB (simEnv B₁) "Step_pure" i v ↔
      Round6.Reading.FiresB (simEnv B₂) "Step_pure" i v :=
  ⟨firesB_pure hB i v, firesB_pure (agreeOff_symm hB) i v⟩

theorem firesB_read_iff (hB : AgreeOff B₁ B₂) {i : Nat} (hi : i ≠ 43) (v : Value) :
    Round6.Reading.FiresB (simEnv B₁) "Step_read" i v ↔
      Round6.Reading.FiresB (simEnv B₂) "Step_read" i v :=
  ⟨firesB_read hB hi v, firesB_read (agreeOff_symm hB) hi v⟩

theorem firesB_step_iff (hB : AgreeOff B₁ B₂) {i : Nat} (hi : i ∉ stepBad) (v : Value) :
    Round6.Reading.FiresB (simEnv B₁) "Step" i v ↔ Round6.Reading.FiresB (simEnv B₂) "Step" i v :=
  ⟨firesB_step hB hi v, firesB_step (agreeOff_symm hB) hi v⟩

theorem ne43_of_not_ms {i : Nat} (hi : i ∉ msReadRules) : i ≠ 43 := by
  intro h
  exact hi (by rw [h]; decide)

/-! ## The per-rule obligations without the host calls -/

/-- **The per-rule backward obligations off memory SIMD and off the host calls**:
`BackwardUpToDRestS` with `Step` rules 8 and 9 (the host calls) left out. -/
structure BackwardUpToDRestSH (V : Config H → Prop) (env : Env) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`, rule by rule. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    V ⟨s, f, is⟩ → TypedD env hn ⟨s, f, is⟩ →
    Fires env "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, rule by rule, off the memory SIMD rules. -/
  read : ∀ (i : Nat), i ∉ msReadRules → ∀ (c : Config H) (w : Value), V c → TypedD env hn c →
    Fires env "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- The store-changing rules of `Step`, rule by rule, off the memory SIMD rules and the host
  calls. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ stepMSRules → i ≠ 8 → i ≠ 9 → ∀ (c : Config H) (w : Value),
    V c → TypedD env hn c → Fires env "Step" i (.tuple [configVD hn c, w]) → BwdUpToD hn P host c w

/-- `BackwardUpToDRestS` gives `BackwardUpToDRestSH` (it has more obligations). -/
theorem restSH_of_restS {V : Config H → Prop} {env : Env} {hn : H → String} {P : Profile}
    {host : HostSemantics H} (h : Round7.MemSimd.BackwardUpToDRestS V env hn P host) :
    BackwardUpToDRestSH V env hn P host where
  pure := h.pure
  read := h.read
  step i h6 hi _ _ := h.step i h6 hi

/-- **The obligations off memory SIMD and off the host calls move from `B₂` to `B₁`.** -/
theorem backwardUpToDRestSH_agree (hB : AgreeOff B₁ B₂) {V : Config H → Prop} {hn : H → String}
    {P : Profile} {host : HostSemantics H} (h : BackwardUpToDRestSH V (simEnv B₂) hn P host) :
    BackwardUpToDRestSH V (simEnv B₁) hn P host where
  pure i s f is w hV hT hF :=
    h.pure i s f is w hV ((typedD_iff hB hn _).1 hT) ((fires_pure_iff hB i _).1 hF)
  read i hi c w hV hT hF :=
    h.read i hi c w hV ((typedD_iff hB hn c).1 hT) ((fires_read_iff hB (ne43_of_not_ms hi) _).1 hF)
  step i h6 hi h8 h9 c w hV hT hF :=
    h.step i h6 hi h8 h9 c w hV ((typedD_iff hB hn c).1 hT)
      ((fires_step_iff hB (not_stepBad h6 hi h8 h9) _).1 hF)

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
