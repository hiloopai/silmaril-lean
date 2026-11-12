module

public import Silmaril.Proofs.Wasm.Game.Untyped.Adequacy
public import Silmaril.Proofs.Wasm.Game.SpecInst.Basic

/-!
# Worked example: `externref` across both interfaces

`exRelay` imports `env.pass : [externref] → [externref]` and exports
`relay : [externref] → [externref]` with body `local.get 0; call 0`. Neither function
type is scalar (`relay_not_scalar`), so the games of `Silmaril.Wasm.Game.{Strategy,Shared}`
cannot pose these calls at all.

* `exRelay_valid`, `exRelay_prep`, `shape`: validation and the spec's allocation
  (`prepare?`, kernel evaluation `decide +kernel`) against the import store; the shape
  of the two functions of the allocated store.
* `exRelayS_ok`: the allocated store is typed (silmaril-lean's `Instantiate.ok`).
* `echoHost_ok`: the reference-echoing host satisfies `HostOk`.
* `run_relay`: for every profile and every argument, `$invoke(relay, v)` runs under
  `echoHost` to the value `v`: the reference goes out through the import and comes back.

New proofs, following `Silmaril.Proofs.Wasm.Game.Shared.Example`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.UntypedExample

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.UntypedExample Silmaril.Proofs.Wasm.Game
  Silmaril.Proofs.Wasm.Game.SpecInst Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- The closed type `externref = (ref null extern)`. -/
abbrev externC : CValType := .refv (.ref true (.abs .extern))

/-- The function type `[externref] → [externref]`. -/
abbrev relayTy : CCompType := .func (Ty.ofList [externC]) (Ty.ofList [externC])

/-! ### Kernel-checked facts -/

theorem exRelay_valid_some : (validate? exRelay).isSome = true := by decide +kernel
theorem exRelay_prep_some :
    (prepare? evalConst? exRelayStore exRelay (importAddrs exRelayMT)).isSome = true := by
  decide +kernel
theorem t_len : exRelayS.funcs.length = 2 := by decide +kernel
theorem t_expand : exRelayS.funcs.map (fun fi => fi.type.expand?) =
    [some relayTy, some relayTy] := by decide +kernel
theorem t_mod : exRelayS.funcs.map (fun fi => fi.module.funcs) = [[], [0, 1]] := by
  decide +kernel
theorem t_addrs : exportFuncAddrs exRelayPrep.1.frame.module = [1] := by decide +kernel
theorem t_imports : exRelayMT.imports.length = 1 := by decide +kernel
theorem t_imports_func : exRelayMT.imports.map
    (fun xt => match xt with | .func _ => true | _ => false) = [true] := by decide +kernel

/-- **Neither function is scalar**: the scalar games cannot pose these calls. -/
theorem relay_not_scalar : exRelayS.funcs.map (fun fi => FnType.ofDefType? fi.type) =
    [none, none] := by decide +kernel

/-- The host function of import `0`. -/
def isHost0 (fi : FuncInst Nat) : Bool := match fi.code with | .host 0 => true | _ => false

/-- A Wasm function without locals whose body is `local.get 0; call 0`. -/
def isRelayBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.localGet x, .call y]⟩ => x.toNat == 0 && y.toNat == 0
  | _ => false

theorem t_host : exRelayS.funcs.map isHost0 = [true, false] := by decide +kernel
theorem t_body : exRelayS.funcs.map isRelayBody = [false, true] := by decide +kernel

/-! ### Validation, allocation and typing -/

/-- The validated type. -/
theorem exRelay_valid : validate? exRelay = some exRelayMT := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp exRelay_valid_some
  show validate? exRelay = some ((validate? exRelay).getD _)
  rw [hmt]
  rfl

/-- The allocation. -/
theorem exRelay_prep :
    prepare? evalConst? exRelayStore exRelay (importAddrs exRelayMT) = some exRelayPrep := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp exRelay_prep_some
  show _ = some ((prepare? evalConst? exRelayStore exRelay (importAddrs exRelayMT)).getD _)
  rw [hq]
  rfl

/-- All imports are functions. -/
theorem exRelay_funcImports : ∀ xt ∈ exRelayMT.imports, ∃ d, xt = .func d := by
  obtain ⟨x₀, hx⟩ := List.length_eq_one_iff.mp t_imports
  have h' : [x₀].map (fun xt => match xt with | .func _ => true | _ => false) = [true] :=
    hx ▸ t_imports_func
  have h₀ : (match x₀ with | .func _ => true | _ => false) = true := (List.cons.inj h').1
  intro xt hxt
  rw [hx, List.mem_singleton] at hxt
  subst hxt
  cases xt with
  | func d => exact ⟨d, rfl⟩
  | _ => cases h₀

/-- Adding the start call keeps the store. -/
theorem withStart_store (c : Config Nat) (st : Option FuncIdx) : (c.withStart st).store = c.store := by
  cases st <;> rfl

/-- **The instantiated store is typed.** -/
theorem exRelayS_ok : StoreOk exRelayS := by
  have hs : StoreOk exRelayStore := importStore_ok exRelay_valid exRelay_funcImports
  have hinst : Instantiate (profile neverFail) SingleThreaded.divHost exRelayStore exRelay
      (importAddrs exRelayMT) (exRelayPrep.1.withStart exRelayPrep.2) :=
    (prepare?_sound evalConst?_evalSound exRelay_prep
      ⟨exRelayMT.exports, exRelayMT.imports, validate?_sound exRelay_valid,
        importAddrs_typed exRelay_funcImports⟩).2
  have hok : StoreOk (exRelayPrep.1.withStart exRelayPrep.2).store :=
    ConfigOk.storeOk (Instantiate.ok SingleThreaded.divHost_ok hs hinst)
  rw [withStart_store] at hok
  exact hok

/-! ### The shape of the store -/

/-- Reading `isHost0`. -/
theorem isHost0_code {fi : FuncInst Nat} (h : isHost0 fi = true) : fi.code = .host 0 := by
  unfold isHost0 at h
  split at h
  · assumption
  · cases h

/-- Reading `isRelayBody`. -/
theorem isRelayBody_code {fi : FuncInst Nat} (h : isRelayBody fi = true) :
    ∃ (t : TypeIdx) (x : LocalIdx) (y : FuncIdx),
      fi.code = .wasm ⟨t, [], [.localGet x, .call y]⟩ ∧ x.toNat = 0 ∧ y.toNat = 0 := by
  unfold isRelayBody at h
  split at h
  · rename_i t x y hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨t, x, y, hc, h.1, h.2⟩
  · cases h

/-- The shape of the instantiated store. -/
structure Shape (fi₀ fi₁ : FuncInst Nat) (t : TypeIdx) (x : LocalIdx) (y : FuncIdx) : Prop where
  funcs : exRelayS.funcs = [fi₀, fi₁]
  code₀ : fi₀.code = .host 0
  ty₀ : Expand fi₀.type relayTy
  code₁ : fi₁.code = .wasm ⟨t, [], [.localGet x, .call y]⟩
  ty₁ : Expand fi₁.type relayTy
  hx : x.toNat = 0
  hy : y.toNat = 0
  mod₁ : fi₁.module.funcs = [0, 1]

/-- The store has this shape. -/
theorem shape : ∃ fi₀ fi₁ t x y, Shape fi₀ fi₁ t x y := by
  obtain ⟨fi₀, fi₁, hf⟩ := List.length_eq_two.mp t_len
  have hhost : [fi₀, fi₁].map isHost0 = [true, false] := hf ▸ t_host
  have hbody : [fi₀, fi₁].map isRelayBody = [false, true] := hf ▸ t_body
  have hexp : [fi₀, fi₁].map (fun fi => fi.type.expand?) = [some relayTy, some relayTy] :=
    hf ▸ t_expand
  have hmod : [fi₀, fi₁].map (fun fi => fi.module.funcs) = [[], [0, 1]] := hf ▸ t_mod
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hhost hbody hexp hmod
  obtain ⟨t, x, y, hc₁, hx, hy⟩ := isRelayBody_code hbody.2.1
  exact ⟨fi₀, fi₁, t, x, y, ⟨hf, isHost0_code hhost.1, Expand.iff.mpr hexp.1, hc₁,
    Expand.iff.mpr hexp.2.1, hx, hy, hmod.2.1⟩⟩

/-! ### The host -/

/-- **The echoing host satisfies Core's host contract.** -/
theorem echoHost_ok : HostOk echoHost := by
  intro s fi h vs ps rs hs hfi hcode hexp hvs
  by_cases hc : ∀ fi ∈ s.funcs, fi.code = .host h → ∀ ps rs, Expand fi.type (.func ps rs) → ps = rs
  · refine ⟨⟨_, .inl ⟨hc, rfl⟩⟩, ?_⟩
    rintro out (⟨-, rfl⟩ | ⟨hn, -⟩)
    · have hps : ps = rs := hc fi hfi hcode ps rs hexp
      refine ⟨hs, Extend.refl hs, ?_⟩
      show List.Forall₂ (ValOk s) vs rs.toList
      rw [← hps]
      exact hvs
    · exact absurd hc hn
  · refine ⟨⟨_, .inr ⟨hc, rfl⟩⟩, ?_⟩
    rintro out (⟨h1, -⟩ | ⟨-, rfl⟩)
    · exact absurd h1 hc
    · trivial

/-- At the instantiated store, the echoing host returns the arguments of a call of import `0`. -/
theorem echoHost_at {fi₀ fi₁ : FuncInst Nat} {t : TypeIdx} {x : LocalIdx} {y : FuncIdx}
    (h : Shape fi₀ fi₁ t x y) (vs : List Val) :
    echoHost 0 exRelayS vs (.returned exRelayS (.values vs)) := by
  refine .inl ⟨fun fi hfi hcode ps rs hexp => ?_, rfl⟩
  rw [h.funcs, List.mem_cons, List.mem_singleton] at hfi
  rcases hfi with rfl | rfl
  · have heq : relayTy = .func ps rs := Expand.func_eq h.ty₀ hexp
    obtain ⟨hps, hrs⟩ := Ty.func.inj heq
    rw [← hps, ← hrs]
  · rw [h.code₁] at hcode
    cases hcode

/-! ### The run -/

section Run

variable {P : Silmaril.Wasm.Numerics.Profile} {fi₀ fi₁ : FuncInst Nat} {t : TypeIdx}
  {x : LocalIdx} {y : FuncIdx}

/-- A step of a head of the code, in front of a non-empty rest. -/
theorem step_head {host : HostSemantics Nat} {s s' : Store Nat} {f f' : Frame}
    {is is' rest : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hr : rest ≠ []) :
    Step P host ⟨s, f, is ++ rest⟩ ⟨s', f', is' ++ rest⟩ := by
  simpa [vals] using Step.ctxtInstrs (vs := []) (rest := rest) h (.inr hr)

/-- The frame of the call of `relay` on `v`. -/
abbrev relayFrame (fi₁ : FuncInst Nat) (v : Val) : Frame := Frame.forCall fi₁.module [v] []

/-- Entering `relay`. -/
theorem run_enter (h : Shape fi₀ fi₁ t x y) (v : Val) :
    Step P echoHost (invoke exRelayS 1 [v])
      ⟨exRelayS, {}, [.frame 1 (relayFrame fi₁ v)
        [.label 1 [] [.plain (.localGet x), .plain (.call y)]]]⟩ := by
  have hf : exRelayS.funcs[1]? = some fi₁ := by rw [h.funcs]; rfl
  exact Step.callRefFunc (P := P) (host := echoHost) (s := exRelayS) (f := {})
    (c := .callRefType ((exRelayS.funcs[1]?.map FuncInst.type).getD default)) (vs := [v])
    trivial hf h.ty₁ rfl h.code₁

/-- `local.get 0` reads the argument. -/
theorem run_get (h : Shape fi₀ fi₁ t x y) (v : Val) :
    Step P echoHost ⟨exRelayS, relayFrame fi₁ v, [.plain (.localGet x), .plain (.call y)]⟩
      ⟨exRelayS, relayFrame fi₁ v, [v.toAdmin, .plain (.call y)]⟩ := by
  have hl : (relayFrame fi₁ v).local? x = some (some v) := by
    simp [Frame.local?, Frame.forCall, h.hx]
  exact step_head (is := [.plain (.localGet x)]) (Step.«variable» (VariableStep.localGet hl))
    (by simp)

/-- `call 0` reaches the host call. -/
theorem run_call (h : Shape fi₀ fi₁ t x y) (v : Val) :
    Step P echoHost ⟨exRelayS, relayFrame fi₁ v, [v.toAdmin, .plain (.call y)]⟩
      ⟨exRelayS, relayFrame fi₁ v, vals [v] ++ [.ref (.func 0), .callRefType fi₀.type]⟩ := by
  have hf0 : exRelayS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  have hx : (relayFrame fi₁ v).module.funcs[y.toNat]? = some 0 := by
    simp [Frame.forCall, h.mod₁, h.hy]
  simpa [vals] using Step.ctxtInstrs (vs := [v]) (rest := []) (Step.call (P := P)
    (host := echoHost) hx hf0) (.inl (by simp))

/-- **The host echoes the reference back.** -/
theorem run_host (h : Shape fi₀ fi₁ t x y) (v : Val) :
    Step P echoHost
      ⟨exRelayS, relayFrame fi₁ v, vals [v] ++ [.ref (.func 0), .callRefType fi₀.type]⟩
      ⟨exRelayS, relayFrame fi₁ v, vals [v]⟩ := by
  have hf0 : exRelayS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  exact Step.callRefHost (P := P) (r := .values [v]) trivial hf0 h.ty₀ rfl h.code₀
    (echoHost_at h [v])

/-- **The run of `relay`**, every profile, every argument: the argument comes back. -/
theorem run_relay (h : Shape fi₀ fi₁ t x y) (v : Val) :
    Steps P echoHost (invoke exRelayS 1 [v]) ⟨exRelayS, {}, vals [v]⟩ := by
  have h₁ := run_enter (P := P) h v
  have h₂ := Step.ctxtFrame (f := {}) (n := 1) (Step.ctxtLabel (n := 1) (cont := [])
    (run_get (P := P) h v))
  have h₃ := Step.ctxtFrame (f := {}) (n := 1) (Step.ctxtLabel (n := 1) (cont := [])
    (run_call (P := P) h v))
  have h₄ := Step.ctxtFrame (f := {}) (n := 1) (Step.ctxtLabel (n := 1) (cont := [])
    (run_host (P := P) h v))
  have h₅ : Step P echoHost ⟨exRelayS, {}, [.frame 1 (relayFrame fi₁ v)
      [.label 1 [] (vals [v])]]⟩ ⟨exRelayS, {}, [.frame 1 (relayFrame fi₁ v) (vals [v])]⟩ :=
    Step.ctxtFrame Step.labelVals
  have h₆ : Step P echoHost ⟨exRelayS, {}, [.frame 1 (relayFrame fi₁ v) (vals [v])]⟩
      ⟨exRelayS, {}, vals [v]⟩ := Step.frameVals rfl
  exact h₁.steps.trans (h₂.steps.trans (h₃.steps.trans (h₄.steps.trans (h₅.steps.trans h₆.steps))))

end Run

end Silmaril.Proofs.Wasm.Game.UntypedExample
