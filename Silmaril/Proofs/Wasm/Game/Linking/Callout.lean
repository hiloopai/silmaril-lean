module

public import Silmaril.Wasm.Link.ControlInversion
public import Silmaril.Wasm.Link.SimulationDefs
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic

/-!
# Static linking: Callout

Original module documentation:

# Host-call redexes across #1936's code relation (M3, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3. Helpers for
`Silmaril.Wasm.Game.Linking.Simulation`: #1936's `AdminRelation.Control` relates the
callout contexts of `decompose?` (`fill_control`), host functions are kept by
`StoreRelation.Related` (`Related.host_lookup`), hence a host-call redex of the source is
one of the target with the same host code and arguments (`decompose?_transfer`), and the
contexts stay related when the host result is plugged in (`Control.result_refl`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

namespace Linking

variable {H : Type}

theorem callRefType_cons' {mode : Mode} {left right : ModuleInst}
    {d : DefType} {xs ys : List Admin} (h : Control mode left right (.callRefType d :: xs) ys) :
    ∃ rest, ys = .callRefType d :: rest ∧ Control mode left right xs rest := by
  generalize ha : Admin.callRefType d = a at h
  cases h
  case callRefType rest => cases ha; exact ⟨_, rfl, rest⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha] at hv
    simp only [Admin.val?, reduceCtorEq] at hv
  all_goals cases ha

theorem callRef_cons' {mode : Mode} {left right : ModuleInst} {c : Admin}
    {xs ys : List Admin} (h : Control mode left right (c :: xs) ys) (hc : c.IsCallRef) :
    ∃ c' rest, ys = c' :: rest ∧ c'.IsCallRef ∧ Control mode left right xs rest := by
  cases c <;> simp only [Admin.IsCallRef] at hc
  case plain i =>
    cases i <;> simp only at hc
    rename_i x
    obtain ⟨j, rest, hcode, rewrite, hrest⟩ := h.plain_cons (by rfl)
    refine ⟨.plain j, rest, hcode, ?_, hrest⟩
    cases mode with
    | same => change Instr.callRef x = j at rewrite; rw [← rewrite]; trivial
    | relocated r =>
      simp only [Instruction, instruction?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
      obtain ⟨y, hy, rfl⟩ := rewrite
      trivial
  case callRefType d =>
    obtain ⟨rest, hcode, hrest⟩ := callRefType_cons' h
    exact ⟨.callRefType d, rest, hcode, trivial, hrest⟩

/-- Peel the value prefix off a related code sequence `vals pre ++ [a] ++ xs`. -/
private theorem values_cons_inv {mode : Mode} {m m' : ModuleInst} {pre : List Val}
    {a : Admin} {xs ys : List Admin} (h : Control mode m m' (vals pre ++ [a] ++ xs) ys) :
    ∃ tail, ys = vals pre ++ tail ∧ Control mode m m' (a :: xs) tail :=
  Control.values_prefix (by simpa only [List.append_assoc, List.singleton_append] using h)

/-- Put the value prefix back in front of related code sequences `a :: xs`, `b :: ys`. -/
private theorem values_cons_fill {mode : Mode} {m m' : ModuleInst} {pre : List Val}
    {a b : Admin} {xs ys : List Admin} (h : Control mode m m' (a :: xs) (b :: ys)) :
    Control mode m m' (vals pre ++ [a] ++ xs) (vals pre ++ [b] ++ ys) := by
  simpa only [List.append_assoc, List.singleton_append] using
    (Control.values _ _ _ pre).append h

/-- #1936's code relation decomposes along a callout context. -/
theorem fill_control (E : Ctx) (X : List Admin) :
    ∀ {mode : Mode} {m m' : ModuleInst} {ys : List Admin}, Control mode m m' (E.fill X) ys →
      ∃ (E' : Ctx) (mode₀ : Mode) (m₀ m₀' : ModuleInst) (Y : List Admin),
        ys = E'.fill Y ∧ Control mode₀ m₀ m₀' X Y ∧
        ∀ Z Z', Control mode₀ m₀ m₀' Z Z' → Control mode m m' (E.fill Z) (E'.fill Z') := by
  induction E with
  | top pre rest =>
    intro mode m m' ys h
    obtain ⟨tail, hys, ht⟩ : ∃ tail, ys = vals pre ++ tail ∧ Control mode m m' (X ++ rest) tail :=
      Control.values_prefix (by simpa only [Ctx.fill, List.append_assoc] using h)
    obtain ⟨Y, R, htail, hX, hR⟩ := ht.split
    refine ⟨.top pre R, mode, m, m', Y, by rw [hys, htail, Ctx.fill, List.append_assoc], hX,
      fun Z Z' hZ => ?_⟩
    simpa only [Ctx.fill, List.append_assoc] using (Control.values _ _ _ pre).append (hZ.append hR)
  | label pre n cont E rest ih =>
    intro mode m m' ys h
    obtain ⟨tail, hys, ht⟩ := values_cons_inv h
    obtain ⟨cont', body', R, htail, hc, hb, hR⟩ := ht.label_cons
    obtain ⟨E', mode₀, m₀, m₀', Y, hbody, hX, hfill⟩ := ih hb
    refine ⟨.label pre n cont' E' R, mode₀, m₀, m₀', Y, by
      rw [hys, htail, hbody, Ctx.fill, List.append_assoc, List.singleton_append], hX,
      fun Z Z' hZ => values_cons_fill (.label hc (hfill Z Z' hZ) hR)⟩
  | handler pre n cs E rest ih =>
    intro mode m m' ys h
    obtain ⟨tail, hys, ht⟩ := values_cons_inv h
    obtain ⟨hmode, hm, body', R, htail, hb, hR⟩ := ht.handler_cons
    obtain ⟨E', mode₀, m₀, m₀', Y, hbody, hX, hfill⟩ := ih hb
    refine ⟨.handler pre n cs E' R, mode₀, m₀, m₀', Y, by
      rw [hys, htail, hbody, Ctx.fill, List.append_assoc, List.singleton_append], hX,
      fun Z Z' hZ => hmode ▸ hm ▸ values_cons_fill (.handler (hfill Z Z' hZ) hR)⟩
  | frame pre n f E rest ih =>
    intro mode m m' ys h
    obtain ⟨tail, hys, ht⟩ := values_cons_inv h
    obtain ⟨innerMode, f', body', R, htail, hf, hb, hR⟩ := ht.frame_cons
    obtain ⟨E', mode₀, m₀, m₀', Y, hbody, hX, hfill⟩ := ih hb
    refine ⟨.frame pre n f' E' R, mode₀, m₀, m₀', Y, by
      rw [hys, htail, hbody, Ctx.fill, List.append_assoc, List.singleton_append], hX,
      fun Z Z' hZ => values_cons_fill (.frame hf (hfill Z Z' hZ) hR)⟩

/-- Completeness of `decompose?`: a host-call redex in a callout context is found. -/
theorem decompose?_fill {s : Store H} (E : Ctx) {args : List Val} {a : Nat} {c : Admin}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : args.length = ps.length) (hcode : fi.code = .host h) :
    decompose? s (E.fill (vals args ++ [.ref (.func a), c])) = some (E, a, h, args) := by
  induction E with
  | top pre rest =>
    have := decompose?_wrap pre rest (decompose?_redex hc hf he hn hcode)
    simpa [Ctx.wrap, Ctx.fill] using this
  | label pre n cont E rest ih =>
    have hsp : splitVals (Ctx.fill (.label pre n cont E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .label n cont (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]
  | handler pre n cs E rest ih =>
    have hsp : splitVals (Ctx.fill (.handler pre n cs E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .handler n cs (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]
  | frame pre n f E rest ih =>
    have hsp : splitVals (Ctx.fill (.frame pre n f E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .frame n f (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]

/-- Host functions are kept by the store relation. -/
theorem Related.host_lookup {s s' : Store H} (hr : StoreRelation.Related s s') {a : Nat}
    {fi : FuncInst H} {h : H} (hf : s.funcs[a]? = some fi) (hc : fi.code = .host h) :
    s'.funcs[a]? = some fi := by
  obtain ⟨fi', hf', hrel⟩ := hr.function_lookup hf
  cases hrel with
  | same => exact hf'
  | relocated => cases hc

/-- A host-call redex of the source is one of the target: same callee, host code and
arguments, and the callout contexts stay related. -/
theorem decompose?_transfer {s s' : Store H} (hr : StoreRelation.Related s s') {mode : Mode}
    {m m' : ModuleInst} {code code' : List Admin} (hcode : Control mode m m' code code')
    {E : Ctx} {a : Nat} {h : H} {args : List Val}
    (hd : decompose? s code = some (E, a, h, args)) :
    ∃ E', decompose? s' code' = some (E', a, h, args) ∧ ∃ (mode₀ : Mode) (m₀ m₀' : ModuleInst),
      ∀ Z Z', Control mode₀ m₀ m₀' Z Z' → Control mode m m' (E.fill Z) (E'.fill Z') := by
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, rfl⟩ := decompose?_sound hd
  obtain ⟨E', mode₀, m₀, m₀', Y, rfl, hX, hfill⟩ := fill_control E _ hcode
  obtain ⟨tail, rfl, ht⟩ := hX.values_prefix
  obtain ⟨tail', rfl, ht'⟩ := ht.ref_cons
  obtain ⟨c', R, rfl, hc', hR⟩ := callRef_cons' ht' hyy
  rw [hR.nil_left]
  exact ⟨E', decompose?_fill E' hc' (Related.host_lookup hr hf hc) he hn hc,
    mode₀, m₀, m₀', hfill⟩

/-- Host results are related to themselves in every mode. -/
theorem Control.result_refl (mode : Mode) (m m' : ModuleInst) (r : Result) :
    Control mode m m' r.toAdmin r.toAdmin := by
  cases r with
  | values vs => exact Control.values mode m m' vs
  | throw a => exact .ref (.throwRef .nil)
  | trap => exact .trap .nil

/-- A finished code has no host-call redex. -/
theorem decompose?_toAdmin (s : Store H) (r : Result) : decompose? s r.toAdmin = none := by
  cases r with
  | values vs => exact decompose?_of_split_nil (splitVals_vals vs)
  | trap =>
    show decompose? s [.trap] = none
    simpa [Ctx.fill, vals] using Ctx.decompose?_fill_trap s (.top [] [])
  | throw a =>
    have hsp : splitVals (Result.throw a).toAdmin = ([.ref (.exn a)], [.plain .throwRef]) := by
      have := splitVals_vals_cons (vs := [.ref (.exn a)]) (d := .plain .throwRef) rfl []
      simpa [vals, Result.toAdmin] using this
    rw [decompose?_of_split hsp]
    rfl

/-- A thread whose code is a finished result has no internal step. -/
theorem toAdmin_no_internal {P : Profile} {s : Store H} {t : Thread} {r : Result}
    (h : (t.config s).code = r.toAdmin) : ∀ y, ¬ InternalP P (s, t) y := by
  rintro ⟨s', t'⟩ ⟨f', code', -, hstep⟩
  have hq := Step.not_quiet hstep
  rw [h] at hq
  cases r with
  | values vs => exact hq (quiet_vals vs)
  | trap => exact hq quiet_trap
  | throw a => exact hq (quiet_throwing a)

/-- A thread at a host-call redex has no internal step. -/
theorem decompose?_no_internal {P : Profile} {s : Store H} {t : Thread}
    {x : Ctx × Nat × H × List Val} (hd : decompose? s (t.config s).code = some x) :
    ∀ y, ¬ InternalP P (s, t) y := by
  rintro ⟨s', t'⟩ ⟨f', code', -, hstep⟩
  have hn := decompose?_none_of_noRedex (Step.noRedex hstep)
  rw [Thread.config_store, hd] at hn
  cases hn

end Linking

end Silmaril.Proofs.Wasm.Game
