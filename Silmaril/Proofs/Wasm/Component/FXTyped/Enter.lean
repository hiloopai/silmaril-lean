module

public import Silmaril.Proofs.Wasm.Component.FXTyped.Frame
public import Silmaril.Proofs.Wasm.Component.FXRefV.Map

/-!
# Entering an FX function: inversion

A Core thread of `fxEV P` that calls an FX function becomes an FX thread by one `StepFX'` step
from its Core code (`InternalV`, second case). This module shows that this step is the FX rule
`invoke` at the top of the code, so that the FX thread starts at the outermost frame of the
function:

* `step_allCore_shape`: a `StepFX'` step (no host, FX table `fxOf`) from all-Core code is, under
  a prefix of values and a suffix, a Core step of a block of Core code, a trap or an exception
  passing outwards, or the FX rule `invoke`;
* **`step_enter`**: from the code `vals xs ++ [ref.func a, call_ref]` of a Core invocation of the
  FX function `F` at `a` (with `|xs| = F.nparams` and a host-call redex), the only step is
  `invoke`, to `[frame F.nresults … [label F.nresults [] F.body]]`. A Core step of a block would
  have no host-call redex around it (`Step.noRedex`), the code has neither trap nor exception, and
  an `invoke` deeper in the values would take fewer arguments.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (decompose? splitVals)
open Silmaril.Wasm.Models.FX (AdminFX ContFX ConfigFX FuncFX InstrFX cvals cthrowing)
open Silmaril.Wasm.Models.FXV (StepFX' FVal fvals liftV)
open Silmaril.Wasm.Component.FXEngine (FXCode fxOf noHostFX)
open Silmaril.Proofs.Wasm.Models.FX (isCore map_core_inj)
open Silmaril.Proofs.Wasm.Models.FXV (fvals_liftV allCore_pre all_isCore_split)
open Silmaril.Proofs.Wasm.Component.Reference (noHostH)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- All-Core FX code is Core code. -/
theorem allCore_map : ∀ {l : List AdminFX}, l.all isCore = true → ∃ R : List Admin, l = R.map .core
  | [], _ => ⟨[], rfl⟩
  | .core a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨R, rfl⟩ := allCore_map h.2
    exact ⟨a :: R, rfl⟩
  | .fx _ :: _, h => by simp [isCore] at h
  | .block .. :: _, h => by simp [isCore] at h
  | .loop .. :: _, h => by simp [isCore] at h
  | .if_ .. :: _, h => by simp [isCore] at h
  | .label .. :: _, h => by simp [isCore] at h
  | .frame .. :: _, h => by simp [isCore] at h
  | .handler .. :: _, h => by simp [isCore] at h
  | .contRef _ :: _, h => by simp [isCore] at h

/-- The frame that `invoke` pushes for `F` on the arguments `ws`. -/
abbrev enterCode (F : FuncFX) (ws : List Val) : AdminFX :=
  .frame F.nresults (Frame.forCall F.module ws F.locals)
    [.label F.nresults [] (F.body.map InstrFX.toAdmin)]

/-- **The shape of a `StepFX'` step from all-Core code**: where it happens and what it is. -/
def AllCoreShape (x y : ConfigFX (FXCode H)) : Prop :=
  (∃ (pre : List Val) (B C : List Admin) (c' : Config (FXCode H)),
      x.code = (vals pre ++ B ++ C).map .core ∧
      Step P (noHostH (FXCode H)) ⟨x.store, x.frame, B⟩ c') ∨
    (∃ (pre : List Val) (C : List Admin), x.code = (vals pre ++ [Admin.trap] ++ C).map .core) ∨
    (∃ (pre : List Val) (b : Nat) (C : List Admin),
      x.code = (vals pre ++ throwing b ++ C).map .core) ∨
    (∃ (pre ws : List Val) (a : Nat) (c₀ : Admin) (C : List Admin) (fi : FuncInst (FXCode H))
      (hh : FXCode H) (F : FuncFX),
      x.code = (vals pre ++ vals ws ++ [.ref (.func a), c₀] ++ C).map .core ∧ c₀.IsCallRef ∧
      x.store.funcs[a]? = some fi ∧ fi.code = .host hh ∧ fxOf hh = some F ∧
      ws.length = F.nparams ∧
      y = ⟨x.store, x.conts, x.frame, cvals pre ++ [enterCode F ws] ++ C.map .core⟩)

theorem cvals_eq_map (vs : List Val) : cvals vs = (vals vs).map AdminFX.core := rfl

/-- The `seq` case of `step_allCore_shape`. -/
theorem shape_seq {s s' : Store (FXCode H)} {K K' : List (Option ContFX)} {f f' : Frame}
    {W : List Val} {es es' : List AdminFX} {R : List Admin}
    (ih : AllCoreShape (P := P) ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    AllCoreShape (P := P) ⟨s, K, f, cvals W ++ es ++ R.map .core⟩
      ⟨s', K', f', cvals W ++ es' ++ R.map .core⟩ := by
  rcases ih with ⟨pre, B, C, c', he, hs⟩ | ⟨pre, C, he⟩ | ⟨pre, b, C, he⟩ |
      ⟨pre, ws, a, c₀, C, fi, hh, F, he, hc, hf, hcode, hfx, hn, hy⟩ <;> dsimp only at *
  · refine Or.inl ⟨W ++ pre, B, C ++ R, c', ?_, hs⟩
    simp only [he, cvals_eq_map, vals, List.map_append, List.append_assoc]
  · refine Or.inr (Or.inl ⟨W ++ pre, C ++ R, ?_⟩)
    simp only [he, cvals_eq_map, vals, List.map_append, List.append_assoc]
  · refine Or.inr (Or.inr (Or.inl ⟨W ++ pre, b, C ++ R, ?_⟩))
    simp only [he, cvals_eq_map, vals, List.map_append, List.append_assoc]
  · simp only [ConfigFX.mk.injEq] at hy
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hy
    refine Or.inr (Or.inr (Or.inr ⟨W ++ pre, ws, a, c₀, C ++ R, fi, hh, F, ?_, hc, hf, hcode,
      hfx, hn, ?_⟩))
    · simp only [he, cvals_eq_map, vals, List.map_append, List.append_assoc]
    · simp only [cvals_eq_map, vals, List.map_append, List.append_assoc]

/-- **Where a `StepFX'` step from all-Core code happens.** -/
theorem step_allCore_shape {x y : ConfigFX (FXCode H)}
    (h : StepFX' P (noHostFX H) fxOf x y) : x.code.all isCore = true → AllCoreShape (P := P) x y := by
  induction h with
  | @core s s' K f f' cs cs' h =>
    intro _
    refine Or.inl ⟨[], cs, [], ⟨s', f', cs'⟩, by simp, ?_⟩
    have e := Silmaril.Proofs.Wasm.Component.FXRefV.blockFX_noHost H
    rw [e] at h
    exact h
  | @seq s s' K K' f f' vs es es' rest h hne ih =>
    intro hc
    obtain ⟨W, rfl⟩ := allCore_pre hc
    obtain ⟨-, hes, hrest⟩ := all_isCore_split hc
    obtain ⟨R, rfl⟩ := allCore_map hrest
    rw [fvals_liftV]
    exact shape_seq (ih hes)
  | @trapSeq s K f vs rest hne =>
    intro hc
    obtain ⟨W, rfl⟩ := allCore_pre hc
    obtain ⟨R, rfl⟩ := allCore_map (all_isCore_split hc).2.2
    refine Or.inr (Or.inl ⟨W, R, ?_⟩)
    simp only [fvals_liftV, cvals_eq_map, List.map_append]
    rfl
  | @throwSeq s K f vs b rest hne =>
    intro hc
    obtain ⟨W, rfl⟩ := allCore_pre hc
    obtain ⟨R, rfl⟩ := allCore_map (all_isCore_split hc).2.2
    refine Or.inr (Or.inr (Or.inl ⟨W, b, R, ?_⟩))
    simp only [fvals_liftV, cvals_eq_map, cthrowing, List.map_append]
  | @invoke s K f c vs a fi hh F hc hf hcode hfx hn =>
    intro _
    refine Or.inr (Or.inr (Or.inr ⟨[], vs, a, c, [], fi, hh, F, ?_, hc, hf, hcode, hfx, hn, ?_⟩))
    · simp [cvals_eq_map]
    · simp
  | _ =>
    intro hc
    simp [isCore, cvals, cthrowing] at hc

/-- A call instruction is not a value. -/
theorem isCallRef_val? {c : Admin} (hc : c.IsCallRef) : c.val? = none := by
  rcases c with i | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsCallRef, Admin.val?]
  cases i <;> simp_all

/-- The invocation code splits at the call. -/
theorem splitVals_call (xs : List Val) (a : Nat) {c : Admin} (hc : c.IsCallRef) (C : List Admin) :
    splitVals (vals xs ++ [.ref (.func a), c] ++ C) = (xs ++ [.ref (.func a)], c :: C) := by
  have e : vals xs ++ [.ref (.func a), c] ++ C = vals (xs ++ [.ref (.func a)]) ++ c :: C := by
    simp [vals, Val.toAdmin]
  rw [e]
  exact Silmaril.Wasm.SingleThreaded.splitVals_vals_cons (isCallRef_val? hc) C

/-- The only non-value of the invocation code is the call. -/
theorem mem_call_code {xs : List Val} {a : Nat} {c d : Admin} (hc : c.IsCallRef)
    (hd : d.val? = none) (hdc : ¬ d.IsCallRef) (hm : d ∈ vals xs ++ [.ref (.func a), c]) : False := by
  have hm' : d ∈ vals xs ∨ d = .ref (.func a) ∨ d = c := by
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using hm
  rcases hm' with hm' | hm' | hm'
  · exact Silmaril.Wasm.SingleThreaded.Det.mem_vals hm' hd
  · rw [hm'] at hd
    cases hd
  · exact hdc (hm' ▸ hc)

/-- **The invocation code splits only at its call.** -/
theorem call_code_split {xs pre ws : List Val} {a a' : Nat} {c c₀ : Admin} {C : List Admin}
    (hc : c.IsCallRef) (hc₀ : c₀.IsCallRef)
    (hl : vals xs ++ [.ref (.func a), c] = vals pre ++ vals ws ++ [.ref (.func a'), c₀] ++ C) :
    pre ++ ws = xs ∧ a' = a ∧ c₀ = c ∧ C = [] := by
  have e₁ : vals pre ++ vals ws ++ [.ref (.func a'), c₀] ++ C =
      vals (pre ++ ws) ++ [.ref (.func a'), c₀] ++ C := by simp [vals]
  have hsp₂ : splitVals (vals xs ++ [.ref (.func a), c]) = (xs ++ [.ref (.func a)], [c]) := by
    simpa using splitVals_call xs a hc []
  have hsp : (xs ++ [.ref (.func a)], [c]) = (pre ++ ws ++ [.ref (.func a')], c₀ :: C) := by
    rw [← hsp₂, hl, e₁]
    exact splitVals_call (pre ++ ws) a' hc₀ C
  have hfst : xs ++ [.ref (.func a)] = pre ++ ws ++ [.ref (.func a')] := (Prod.mk.inj hsp).1
  have hsnd : [c] = c₀ :: C := (Prod.mk.inj hsp).2
  have hpw : pre ++ ws = xs := (List.append_inj_left' hfst rfl).symm
  have ha : Val.ref (.func a) = Val.ref (.func a') := by
    simpa using List.append_inj_right' hfst rfl
  exact ⟨hpw, by simpa using ha.symm, (List.cons.inj hsnd).1.symm, (List.cons.inj hsnd).2.symm⟩

/-- The `invoke` case of `step_enter`. -/
theorem enter_invoke {s : Store (FXCode H)} {xs pre ws : List Val} {a : Nat} {fi fi' : FuncInst (FXCode H)}
    {hh hh' : FXCode H} {F F' : FuncFX} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hfx : fxOf hh = some F) (hn : xs.length = F.nparams) (hpw : pre ++ ws = xs)
    (hf' : s.funcs[a]? = some fi') (hcode' : fi'.code = .host hh') (hfx' : fxOf hh' = some F')
    (hn' : ws.length = F'.nparams) : pre = [] ∧ ws = xs ∧ F' = F := by
  have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have hhh : hh' = hh := FuncCode.host.inj (hcode'.symm.trans (hfi ▸ hcode))
  have hF : F' = F := Option.some.inj (hfx'.symm.trans (hhh ▸ hfx))
  have hlen : pre.length + ws.length = xs.length := by rw [← hpw, List.length_append]
  have hpre : pre = [] := List.length_eq_zero_iff.mp (by rw [hF] at hn'; omega)
  exact ⟨hpre, by simpa [hpre] using hpw, hF⟩

/-- **Entering an FX function**: from a Core invocation of the FX function at `a`, with a
host-call redex and as many arguments as parameters, the only `StepFX'` step is `invoke`. -/
theorem step_enter {s : Store (FXCode H)} {K : List (Option ContFX)} {f : Frame} {xs : List Val}
    {a : Nat} {c : Admin} {fi : FuncInst (FXCode H)} {hh : FXCode H} {F : FuncFX}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hfx : fxOf hh = some F) (hn : xs.length = F.nparams)
    (hd : decompose? s (vals xs ++ [.ref (.func a), c]) ≠ none) {y : ConfigFX (FXCode H)}
    (h : StepFX' P (noHostFX H) fxOf ⟨s, K, f, (vals xs ++ [.ref (.func a), c]).map .core⟩ y) :
    y = ⟨s, K, f, [enterCode F xs]⟩ := by
  rcases step_allCore_shape h (Silmaril.Proofs.Wasm.Models.FX.all_isCore_map _) with
      ⟨pre, B, C, c', he, hs⟩ | ⟨pre, C, he⟩ | ⟨pre, b, C, he⟩ |
      ⟨pre, ws, a', c₀, C, fi', hh', F', he, hc₀, hf', hcode', hfx', hn', hy⟩
  · exact (hd (map_core_inj he ▸ Silmaril.Wasm.SingleThreaded.Step.noRedex hs pre C)).elim
  · exact (mem_call_code (d := .trap) hc rfl nofun (by rw [map_core_inj he]; simp)).elim
  · exact (mem_call_code (d := .plain .throwRef) hc rfl nofun
      (by rw [map_core_inj he]; simp [throwing])).elim
  · obtain ⟨hpw, rfl, rfl, rfl⟩ := call_code_split hc hc₀ (map_core_inj he)
    obtain ⟨rfl, rfl, rfl⟩ := enter_invoke hf hcode hfx hn hpw hf' hcode' hfx' hn'
    rw [hy]
    simp

end Silmaril.Proofs.Wasm.Component.FXTyped
