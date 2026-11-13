module

public import Silmaril.Proofs.Wasm.Det.Stateless.Basic
public import Silmaril.Wasm.SingleThreaded.Determinism.Head

/-!
# Stateless code: one step (proofs)

`step_sl`: a host-free Core 3.0 step (`Step P Det.noHost`, any profile `P`) of subset code
(`okL`, `PairedFrom`, in a store with `GoodFuns`) stays subset code, keeps the frame's module,
has a store effect `e` writing only globals of `W` (`Eff`), and is, for **every** profile `P'`
and every store `t` agreeing with the current one on the functions and the globals of `R`
(`Agree R`), a step from the same frame and code in `t` with the effect `e` applied to `t`.
New proofs, by induction on the rules of `Step`, in the style of
`Silmaril.Proofs.Wasm.SSA.CoreCert.step_swap`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Stateless

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Stateless
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {A R W : Nat → Bool}

/-- What one step of subset code gives, for the predecessor `q` of the code. -/
structure SStep (A R W : Nat → Bool) (q : Option Admin) (c c' : Config H) : Prop where
  ok : okL A R W c'.frame.module c'.code
  pair : PairedFrom A q c'.code
  last : Blk A (lastOr q c.code) → Blk A (lastOr q c'.code)
  module : c'.frame.module = c.frame.module
  eff : ∃ e : Eff, e.Ok W ∧ c'.store = e.app c.store ∧
    ∀ (P' : Profile) (t : Store H), Agree R t c.store →
      Step P' Det.noHost ⟨t, c.frame, c.code⟩ ⟨e.app t, c'.frame, c'.code⟩

/-- A step that keeps the store and is a step from every store and at every profile. -/
theorem SStep.pure {q : Option Admin} {s : Store H} {f f' : Frame} {code code' : List Admin}
    (hok : okL A R W f'.module code') (hp : PairedFrom A q code')
    (hl : Blk A (lastOr q code) → Blk A (lastOr q code')) (hm : f'.module = f.module)
    (hs : ∀ (P' : Profile) (t : Store H), Agree R t s →
      Step P' Det.noHost ⟨t, f, code⟩ ⟨t, f', code'⟩) :
    SStep A R W q ⟨s, f, code⟩ ⟨s, f', code'⟩ :=
  ⟨hok, hp, hl, hm, .keep, trivial, rfl, hs⟩

/-- Close the side conditions of a step rule. -/
macro "sl_simp" : tactic => `(tactic| simp_all [slInstr, slInstrs, rtPlain, Blk,
  lastOr_cons, okL_expression, Admin.IsCallRef, Admin.IsReturnCallRef, throwing, constI32])

/-! ## The reduction families -/

theorem parametric_out {m : ModuleInst} {is is' : List Admin} (h : ParametricStep is is') :
    okL A R W m is' ∧ (∀ q, PairedFrom A q is') ∧
      ∀ q, Blk A (lastOr q is) → Blk A (lastOr q is') := by
  cases h <;> sl_simp

theorem sstep_parametric {q : Option Admin} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ParametricStep is is') : SStep A R W q ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  .pure (parametric_out (R := R) (W := W) (m := f.module) h).1
    ((parametric_out (R := R) (W := W) (m := f.module) h).2.1 q)
    ((parametric_out (R := R) (W := W) (m := f.module) h).2.2 q) rfl
    fun _ _ _ => .parametric h

theorem numeric_out {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : NumericStep P is is') (hok : okL A R W m is) :
    okL A R W m is' ∧ (∀ q, PairedFrom A q is') ∧
      (∀ q, Blk A (lastOr q is) → Blk A (lastOr q is')) ∧ ∀ P', NumericStep P' is is' := by
  cases h with
  | intUnOp => exact ⟨by sl_simp, by sl_simp, by sl_simp, fun _ => .intUnOp⟩
  | intBinOp h => exact ⟨by sl_simp, by sl_simp, by sl_simp, fun _ => .intBinOp h⟩
  | intBinOpTrap h => exact ⟨by sl_simp, by sl_simp, by sl_simp, fun _ => .intBinOpTrap h⟩
  | intTestOp => exact ⟨by sl_simp, by sl_simp, by sl_simp, fun _ => .intTestOp⟩
  | intRelOp => exact ⟨by sl_simp, by sl_simp, by sl_simp, fun _ => .intRelOp⟩
  | _ => exfalso; sl_simp

theorem sstep_numeric {q : Option Admin} {P : Profile} {s : Store H} {f : Frame}
    {is is' : List Admin} (h : NumericStep P is is') (hok : okL A R W f.module is) :
    SStep A R W q ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  .pure (numeric_out h hok).1 ((numeric_out h hok).2.1 q) ((numeric_out h hok).2.2.1 q) rfl
    fun P' _ _ => .numeric ((numeric_out h hok).2.2.2 P')

theorem vector_absurd {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : VectorStep P is is') (hok : okL A R W m is) : False := by
  cases h <;> sl_simp

theorem table_absurd {P : Profile} {c c' : Config H} (h : TableStep P c c')
    (hok : okL A R W c.frame.module c.code) : False := by
  cases h <;> sl_simp

theorem memory_absurd {P : Profile} {c c' : Config H} (h : MemoryStep P c c')
    (hok : okL A R W c.frame.module c.code) : False := by
  cases h <;> sl_simp

theorem reference_absurd {c c' : Config H} (h : RefStep c c')
    (hok : okL A R W c.frame.module c.code) : False := by
  cases h <;> sl_simp

theorem aggregate_absurd {c c' : Config H} (h : AggregateStep c c')
    (hok : okL A R W c.frame.module c.code) : False := by
  cases h <;> sl_simp

/-! ## Globals -/

theorem global?_eq {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst} :
    s.global? f x = some (a, g) ↔ f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := by
  constructor
  · intro h
    unfold Store.global? at h
    cases ha : f.module.globals[x.toNat]? with
    | none => simp [ha] at h
    | some b =>
      cases hb : s.globals[b]? with
      | none => simp [ha, hb] at h
      | some g' =>
        simp [ha, hb] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hb⟩
  · rintro ⟨ha, hb⟩
    simp [Store.global?, ha, hb]

theorem sstep_globalGet {q : Option Admin} {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} (h : s.global? f x = some (a, g))
    (hok : okL A R W f.module [.plain (.globalGet x)]) :
    SStep A R W q ⟨s, f, [.plain (.globalGet x)]⟩ ⟨s, f, [g.value.toAdmin]⟩ := by
  have hg : f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := global?_eq.mp h
  have hR : R a = true := by
    have h₀ : slInstr A R W f.module (.globalGet x) = true := by
      simpa [rtPlain] using hok.1
    simpa [slInstr, hg.1] using h₀
  refine ⟨by simp, by simp, fun h => by simp [Blk] at h, rfl, .keep, trivial, rfl, ?_⟩
  intro P' t ht
  have ht' : t.global? f x = some (a, g) := global?_eq.mpr ⟨hg.1, (ht.2 a hR).trans hg.2⟩
  exact .variable (.globalGet ht')

theorem sstep_globalSet {q : Option Admin} {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} {v : Val} (h : s.global? f x = some (a, g))
    (hok : okL A R W f.module [v.toAdmin, .plain (.globalSet x)]) :
    SStep A R W q ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ ⟨s.setGlobal a v, f, []⟩ := by
  have hg : f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := global?_eq.mp h
  have hWR : W a = true ∧ R a = true := by
    have h₀ : slInstr A R W f.module (.globalSet x) = true := by
      simpa [rtPlain] using hok.2.1
    simpa [slInstr, hg.1] using h₀
  refine ⟨trivial, trivial, by sl_simp, rfl, .set a v, hWR.1, rfl, ?_⟩
  intro P' t ht
  have hg' : t.globals[a]? = some g := (ht.2 a hWR.2).trans hg.2
  exact .variable (.globalSet (global?_eq.mpr ⟨hg.1, hg'⟩))

theorem sstep_variable {q : Option Admin} {c c' : Config H} (h : VariableStep c c')
    (hok : okL A R W c.frame.module c.code) : SStep A R W q c c' := by
  cases h with
  | localGet hv =>
    exact .pure (by simp) (by simp) (by sl_simp) rfl fun _ _ _ => .variable (.localGet hv)
  | localSet hx =>
    exact .pure trivial trivial (by sl_simp) rfl fun _ _ _ => .variable (.localSet hx)
  | localTee =>
    exact .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl fun _ _ _ => .variable .localTee
  | globalGet h => exact sstep_globalGet h hok
  | globalSet h => exact sstep_globalSet h hok

/-! ## Contexts -/

theorem sstep_ctxtInstrs {q : Option Admin} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin}
    (ih : ∀ q, PairedFrom A q is → SStep A R W q ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hne : vs ≠ [] ∨ rest ≠ []) (hok : okL A R W f.module (vals vs ++ is ++ rest))
    (hp : PairedFrom A q (vals vs ++ is ++ rest)) :
    SStep A R W q ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  have hp₁ : PairedFrom A q (vals vs ++ is) ∧ PairedFrom A (lastOr q (vals vs ++ is)) rest :=
    pairedFrom_append.mp hp
  have hp₂ : PairedFrom A (lastOr q (vals vs)) is := (pairedFrom_append.mp hp₁.1).2
  have hS : SStep A R W (lastOr q (vals vs)) ⟨s, f, is⟩ ⟨s', f', is'⟩ := ih _ hp₂
  have hok₁ : okL A R W f.module is ∧ okL A R W f.module rest := by
    simpa only [okL_append, okL_vals, true_and] using hok
  have hl : lastOr q (vals vs ++ is) = lastOr (lastOr q (vals vs)) is := lastOr_append _ _ _
  have hrest : PairedFrom A (lastOr (lastOr q (vals vs)) is') rest :=
    pairedFrom_mono (hl ▸ hp₁.2) hS.last
  have hok' : okL A R W f'.module (vals vs ++ is' ++ rest) := by
    have hm : f'.module = f.module := hS.module
    simpa only [okL_append, okL_vals, true_and, hm] using And.intro (hm ▸ hS.ok) hok₁.2
  have hp' : PairedFrom A q (vals vs ++ is' ++ rest) := by
    refine pairedFrom_append.mpr ⟨pairedFrom_append.mpr ⟨pairedFrom_vals _ _, hS.pair⟩, ?_⟩
    rw [lastOr_append]
    exact hrest
  have hlast : Blk A (lastOr q (vals vs ++ is ++ rest)) →
      Blk A (lastOr q (vals vs ++ is' ++ rest)) := by
    rw [lastOr_append q (vals vs ++ is) rest, lastOr_append q (vals vs) is,
      lastOr_append q (vals vs ++ is') rest, lastOr_append q (vals vs) is']
    exact blk_lastOr_mono rest hS.last
  obtain ⟨e, he, hs, hst⟩ := hS.eff
  exact ⟨hok', hp', hlast, hS.module, e, he, hs, fun P' t ht => .ctxtInstrs (hst P' t ht) hne⟩

theorem sstep_ctxtLabel {q : Option Admin} {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List Instr} {is is' : List Admin}
    (ih : ∀ q, PairedFrom A q is → SStep A R W q ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hok : okL A R W f.module [.label n cont is]) :
    SStep A R W q ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  have hl : slInstrs A R W f.module cont = true ∧ okL A R W f.module is ∧ PairedFrom A none is :=
    hok.1
  have hS : SStep A R W none ⟨s, f, is⟩ ⟨s', f', is'⟩ := ih none hl.2.2
  have hm : f'.module = f.module := hS.module
  have hok' : okL A R W f'.module [.label n cont is'] :=
    ⟨⟨hm ▸ hl.1, hS.ok, hS.pair⟩, trivial⟩
  obtain ⟨e, he, hs, hst⟩ := hS.eff
  exact ⟨hok', by sl_simp, by sl_simp, hm, e, he, hs, fun P' t ht => .ctxtLabel (hst P' t ht)⟩

theorem sstep_ctxtFrame {q : Option Admin} {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin}
    (ih : okL A R W fi.module is → ∀ q, PairedFrom A q is → SStep A R W q ⟨s, fi, is⟩ ⟨s', fi', is'⟩)
    (hok : okL A R W f.module [.frame n fi is]) :
    SStep A R W q ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  have hl : okL A R W fi.module is ∧ PairedFrom A none is := hok.1
  have hS : SStep A R W none ⟨s, fi, is⟩ ⟨s', fi', is'⟩ := ih hl.1 none hl.2
  have hok' : okL A R W f.module [.frame n fi' is'] := ⟨⟨hS.ok, hS.pair⟩, trivial⟩
  obtain ⟨e, he, hs, hst⟩ := hS.eff
  exact ⟨hok', by sl_simp, by sl_simp, rfl, e, he, hs, fun P' t ht => .ctxtFrame (hst P' t ht)⟩

/-! ## Calls -/

theorem sstep_call {q : Option Admin} {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hok : okL A R W f.module [.plain (.call x)]) :
    SStep A R W q ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  have hA : A a = true := by
    have h₀ : slInstr A R W f.module (.call x) = true := by simpa [rtPlain] using hok.1
    simpa [slInstr, hx] using h₀
  refine .pure (by simp) ⟨fun h => by simp [isCRT] at h, fun _ => hA, trivial⟩
    (fun h => by simp [Blk] at h) rfl fun _ t ht => ?_
  exact .call hx (ht.1.symm ▸ hf)

/-- The callee of a `CALL_REF` in subset code is a function of `A`, and the instruction is the
administrative `CALL_REF dt`. -/
theorem callee_good {q : Option Admin} {m : ModuleInst} {vs : List Val} {a : Nat} {c : Admin}
    (hc : c.IsCallRef) (hok : okL A R W m (vals vs ++ [.ref (.func a), c]))
    (hp : PairedFrom A q (vals vs ++ [.ref (.func a), c])) : A a = true := by
  have hp' : PairedFrom A (lastOr q (vals vs)) [.ref (.func a), c] := (pairedFrom_append.mp hp).2
  have hok' : okA A R W m c := (okL_append.mp hok).2.2.1
  have hcrt : isCRT c = true := by
    unfold Admin.IsCallRef at hc
    split at hc
    · simp [slInstr, rtPlain] at hok'
    · rfl
    · exact hc.elim
  exact hp'.2.1 hcrt

theorem lastOr_callRef {q : Option Admin} {vs : List Val} {r : Ref} {c : Admin} :
    lastOr q (vals vs ++ [.ref r, c]) = some c := by
  rw [lastOr_append, lastOr_cons]
  rfl

theorem not_blk_callRef {c : Admin} (hc : c.IsCallRef) : ¬ Blk A (some c) := by
  unfold Admin.IsCallRef at hc
  split at hc
  · simp [Blk]
  · simp [Blk]
  · exact hc.elim

theorem sstep_callRefFunc {q : Option Admin} {s : Store H} {f : Frame} {c : Admin} {vs : List Val}
    {a : Nat} {fi : FuncInst H} {ps rs : Validation.Ty (.list .val)} {code : Func}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Validation.Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .wasm code)
    (hg : GoodFuns A R W s.funcs) (hok : okL A R W f.module (vals vs ++ [.ref (.func a), c]))
    (hp : PairedFrom A q (vals vs ++ [.ref (.func a), c])) :
    SStep A R W q ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  obtain ⟨fi', hfi', hsl⟩ := hg a (callee_good hc hok hp)
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hf)
  have hbody : slInstrs A R W fi'.module code.body = true := by
    simpa [slFunc, hcode] using hsl
  have hok' : okL A R W f.module [.frame rs.length (Frame.forCall fi'.module vs code.locals)
      [.label rs.length [] (expression code.body)]] :=
    ⟨⟨⟨⟨rfl, okL_expression hbody, pairedFrom_expression _ _⟩, trivial⟩, by sl_simp⟩, trivial⟩
  refine .pure hok' (by sl_simp) (fun h => absurd (lastOr_callRef ▸ h) (not_blk_callRef hc)) rfl
    fun _ t ht => ?_
  exact .callRefFunc hc (ht.1.symm ▸ hf) he hn hcode

theorem not_okA_ret {m : ModuleInst} {c : Admin} (hc : c.IsReturnCallRef) : ¬ okA A R W m c := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · simp [slInstr, rtPlain]
  · exact id
  · exact hc.elim

theorem no_ret {m : ModuleInst} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef) (hok : okL A R W m (vals vs ++ [c] ++ rest)) : False :=
  not_okA_ret hc (okL_append.mp (okL_append.mp hok).1).2.1

theorem no_ret' {m : ModuleInst} {vs' vs : List Val} {c : Admin} {rest : List Admin} {r : Ref}
    (hc : c.IsReturnCallRef) (hok : okL A R W m (vals vs' ++ vals vs ++ [.ref r, c] ++ rest)) :
    False :=
  not_okA_ret hc (okL_append.mp (okL_append.mp hok).1).2.2.1

theorem no_retN {m : ModuleInst} {vs : List Val} {c : Admin} {rest : List Admin} {r : Ref}
    (hc : c.IsReturnCallRef) (hok : okL A R W m (vals vs ++ [.ref r, c] ++ rest)) : False :=
  not_okA_ret hc (okL_append.mp (okL_append.mp hok).1).2.2.1

/-! ## One step -/

/-- **One step of subset code.** -/
theorem step_sl {P : Profile} {c c' : Config H} (h : Step P Det.noHost c c')
    (hg : GoodFuns A R W c.store.funcs) (hok : okL A R W c.frame.module c.code) :
    ∀ q, PairedFrom A q c.code → SStep A R W q c c' := by
  induction h with
  | parametric h => exact fun _ _ => sstep_parametric h
  | numeric h => exact fun _ _ => sstep_numeric h hok
  | vector h => exact (vector_absurd h hok).elim
  | «variable» h => exact fun _ _ => sstep_variable h hok
  | table h => exact (table_absurd h hok).elim
  | memory h => exact (memory_absurd h hok).elim
  | reference h => exact (reference_absurd h hok).elim
  | aggregate h => exact (aggregate_absurd h hok).elim
  | ctxtInstrs _ hne ih =>
    exact fun _ hp => sstep_ctxtInstrs (ih hg (okL_append.mp (okL_append.mp hok).1).2) hne hok hp
  | ctxtLabel _ ih =>
    exact fun _ _ => sstep_ctxtLabel (ih hg hok.1.2.1) hok
  | ctxtHandler _ _ => exact (okA_handler hok.1).elim
  | ctxtFrame _ ih =>
    exact fun _ _ => sstep_ctxtFrame (ih hg) hok
  | block hbt hm =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .block hbt hm
  | loop hbt hm =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .loop hbt hm
  | ifTrue hc =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .ifTrue hc
  | ifFalse =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .ifFalse
  | labelVals =>
    exact fun _ _ => .pure (by simp) (by simp) (by sl_simp) rfl fun _ _ _ => .labelVals
  | brLabelZero hl hn =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .brLabelZero hl hn
  | brLabelSucc hl =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .brLabelSucc hl
  | brHandler => exact (okA_handler hok.1).elim
  | brIfTrue hc =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .brIfTrue hc
  | brIfFalse =>
    exact fun _ _ => .pure trivial trivial (by sl_simp) rfl fun _ _ _ => .brIfFalse
  | brTableLt hi =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .brTableLt hi
  | brTableGe hi =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .brTableGe hi
  | call hx hf => exact fun _ _ => sstep_call hx hf hok
  | callRefNull hc =>
    exact fun _ _ => .pure (by simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .callRefNull hc
  | callRefFunc hc hf he hn hcode =>
    exact fun _ hp => sstep_callRefFunc hc hf he hn hcode hg hok hp
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCallRefLabel hc =>
    exact (no_ret hc hok.1.2.1).elim
  | returnCallRefHandler _ => exact (okA_handler hok.1).elim
  | returnCallRefFrameNull hc => exact (no_retN hc hok.1.1).elim
  | returnCallRefFrameAddr hc _ _ _ =>
    exact (no_ret' hc hok.1.1).elim
  | frameVals hn =>
    exact fun _ _ => .pure (by simp) (by simp) (by sl_simp) rfl
        fun _ _ _ => .frameVals hn
  | returnFrame hn =>
    exact fun _ _ => .pure (by simp) (by simp) (by sl_simp) rfl
        fun _ _ _ => .returnFrame hn
  | returnLabel =>
    exact fun _ _ => .pure (by sl_simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .returnLabel
  | returnHandler => exact (okA_handler hok.1).elim
  | throwRefNull =>
    exact fun _ _ => .pure (by simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .throwRefNull
  | throwRefInstrs hne =>
    exact fun _ _ => .pure (by sl_simp) (by simp) (by sl_simp) rfl
        fun _ _ _ => .throwRefInstrs hne
  | throwRefLabel =>
    exact fun _ _ => .pure (by sl_simp) (by simp) (by sl_simp) rfl
        fun _ _ _ => .throwRefLabel
  | throwRefFrame =>
    exact fun _ _ => .pure (by sl_simp) (by simp) (by sl_simp) rfl
        fun _ _ _ => .throwRefFrame
  | throwRefHandlerEmpty => exact (okA_handler hok.1).elim
  | throwRefHandlerCatch _ _ =>
    exact (okA_handler hok.1).elim
  | throwRefHandlerCatchRef _ _ =>
    exact (okA_handler hok.1).elim
  | throwRefHandlerCatchAll =>
    exact (okA_handler hok.1).elim
  | throwRefHandlerCatchAllRef =>
    exact (okA_handler hok.1).elim
  | throwRefHandlerNext _ => exact (okA_handler hok.1).elim
  | handlerVals => exact (okA_handler hok.1).elim
  | trapInstrs hne =>
    exact fun _ _ => .pure (by simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .trapInstrs hne
  | trapLabel =>
    exact fun _ _ => .pure (by simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .trapLabel
  | trapHandler => exact (okA_handler hok.1).elim
  | trapFrame =>
    exact fun _ _ => .pure (by simp) (by sl_simp) (by sl_simp) rfl
        fun _ _ _ => .trapFrame
  | _ => exfalso; sl_simp

end Silmaril.Proofs.Wasm.Det.Stateless
