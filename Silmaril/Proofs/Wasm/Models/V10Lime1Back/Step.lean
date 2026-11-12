module

public import Silmaril.Proofs.Wasm.Models.V10Lime1Back.Pure

/-!
# The backward lock-step simulation `StepBack`

`step_back`: a Lime1 step under the transported host `src.mapCode V1.Func.toLime`, from the
image of a 1.0 configuration whose store is `Store1`, is the image of a 1.0 step. By induction
on the Lime1 step:

* congruences (`context`, `label`, `frame`): the code decomposes along `codeToLime`;
* `pure`: `pure_back`;
* store rules: stores are read through `Store.mapCode` (memories, tables and globals are shared,
  functions are found by `found_back`), and updated stores are images (`map_setMemory`,
  `map_setGlobal`);
* `invokeWasm`: the 1.0 premise `ft.results.length ≤ 1` is `Store1`;
* `invokeHost`, `invokeHostDiverges`: the transported host is `HostSemantics.mapCode`, whose
  store argument determines the 1.0 store (`store_injective`);
* `memory.copy`, `memory.fill`: no 1.0 instruction maps to them.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Lime1Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution (codeToLime)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V10Lime1Back

variable {H : Type}

/-- The motive of the induction. -/
def StepB (src : V10.OHost H) (c c' : Silmaril.Wasm.Lime1.Execution.Config H) : Prop :=
  ∀ (s₀ : V10.OStore H) (A : List VAdmin), Store1 s₀ →
    c.store = s₀.mapCode Silmaril.Wasm.V1.Func.toLime → codeToLime A = c.code →
      ∃ b, Silmaril.Wasm.V1.Execution.Step src ⟨s₀, c.frame, A⟩ b ∧ c' = b.toLime

/-- A function found in the image store is the image of a function of the 1.0 store. -/
theorem found_back {s₀ : V10.OStore H} {i : Nat} {fn : FuncInst Lime1.Func H}
    (h : (s₀.mapCode Silmaril.Wasm.V1.Func.toLime).funcs[i]? = some fn) :
    ∃ fn₀, s₀.funcs[i]? = some fn₀ ∧ fn₀.mapCode Silmaril.Wasm.V1.Func.toLime = fn := by
  rw [Store.mapCode_funcs_getElem?, Option.map_eq_some_iff] at h
  exact h

/-- The 1.0 preimage of a value prefix followed by an invocation. -/
theorem code_vals_invoke {A : List VAdmin} {vs : List Value} {a : FuncAddr}
    (hA : codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ [.invoke a]) :
    A = Silmaril.Wasm.V1.Execution.values vs ++ [.invoke a] := by
  obtain ⟨A₂, rfl, h₂⟩ := code_values_append.mp hA
  obtain ⟨x, A', rfl, hx, hA'⟩ := code_cons.mp h₂
  have h₁ : x = .invoke a := map_invoke.mp hx
  have h₂ : A' = [] := code_nil.mp hA'
  rw [h₁, h₂]

/-- A leaf rule at the image of a 1.0 instruction. -/
theorem leaf {src : V10.OHost H} {f : Frame} {vs : List Value} {j : Silmaril.Wasm.V1.Instr}
    {s₀ : V10.OStore H} {A : List VAdmin} {c' : Silmaril.Wasm.Lime1.Execution.Config H}
    (hA : codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ [.source j.toLime])
    {b : Silmaril.Wasm.V1.Execution.Config H}
    (hstep : Silmaril.Wasm.V1.Execution.Step src
      ⟨s₀, f, Silmaril.Wasm.V1.Execution.values vs ++ [.source j]⟩ b)
    (hb : c' = b.toLime) :
    ∃ b, Silmaril.Wasm.V1.Execution.Step src ⟨s₀, f, A⟩ b ∧ c' = b.toLime := by
  obtain ⟨j₀, rfl, hj⟩ := code_vals_source.mp hA
  have hj' : j₀ = j := Silmaril.Wasm.V1.Instr.toLime_injective hj
  subst hj'
  exact ⟨b, hstep, hb⟩

/-- No 1.0 instruction maps to an instruction outside the image. -/
theorem no_leaf {A : List VAdmin} {vs : List Value} {j : Lime1.Instr}
    (hj : ∀ j₀ : Silmaril.Wasm.V1.Instr, j₀.toLime ≠ j)
    (hA : codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ [.source j]) : False := by
  obtain ⟨j₀, -, h⟩ := code_vals_source.mp hA
  exact hj j₀ h

theorem memoryCopy_not_image (j₀ : Silmaril.Wasm.V1.Instr) : j₀.toLime ≠ .memoryCopy := by
  cases j₀ <;> simp [Silmaril.Wasm.V1.Instr.toLime]

theorem memoryFill_not_image (j₀ : Silmaril.Wasm.V1.Instr) : j₀.toLime ≠ .memoryFill := by
  cases j₀ <;> simp [Silmaril.Wasm.V1.Instr.toLime]

open Silmaril.Wasm.V1.Execution (Config.toLime) in
theorem stepB_context {src : V10.OHost H} {s s' : V10.LStore H} {f f' : Frame}
    {before after : List LAdmin} (ih : StepB src ⟨s, f, before⟩ ⟨s', f', after⟩)
    (vs : List Value) (tail : List LAdmin) :
    StepB src ⟨s, f, Silmaril.Wasm.Lime1.Execution.values vs ++ before ++ tail⟩
      ⟨s', f', Silmaril.Wasm.Lime1.Execution.values vs ++ after ++ tail⟩ := by
  intro s₀ A hs₁ hs hA
  have hA' : codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ (before ++ tail) := by
    simpa only [List.append_assoc] using hA
  obtain ⟨A₂, rfl, h₂⟩ := code_values_append.mp hA'
  obtain ⟨B, C, rfl, hB, hC⟩ := code_append.mp h₂
  obtain ⟨⟨bs, bf, bc⟩, hstep, hb⟩ := ih s₀ B hs₁ hs hB
  have hb' : s' = bs.mapCode Silmaril.Wasm.V1.Func.toLime ∧ f' = bf ∧ after = codeToLime bc := by
    simpa [Config.toLime] using hb
  refine ⟨⟨bs, bf, Silmaril.Wasm.V1.Execution.values vs ++ bc ++ C⟩,
    by simpa [List.append_assoc] using hstep.context vs C, ?_⟩
  simp only [Config.toLime, hb'.1, hb'.2.1, hb'.2.2, Silmaril.Wasm.V1.Execution.codeToLime_append,
    Silmaril.Wasm.V1.Execution.map_values, hC]

open Silmaril.Wasm.V1.Execution (Config.toLime) in
theorem stepB_label {src : V10.OHost H} {s s' : V10.LStore H} {f f' : Frame}
    {before after : List LAdmin} (ih : StepB src ⟨s, f, before⟩ ⟨s', f', after⟩)
    (n : Nat) (cont : Lime1.Expr) :
    StepB src ⟨s, f, [.label n cont before]⟩ ⟨s', f', [.label n cont after]⟩ := by
  intro s₀ A hs₁ hs hA
  obtain ⟨cont₀, B, rfl, hc, hB⟩ := code_label hA
  obtain ⟨⟨bs, bf, bc⟩, hstep, hb⟩ := ih s₀ B hs₁ hs hB
  have hb' : s' = bs.mapCode Silmaril.Wasm.V1.Func.toLime ∧ f' = bf ∧ after = codeToLime bc := by
    simpa [Config.toLime] using hb
  refine ⟨⟨bs, bf, [.label n cont₀ bc]⟩, hstep.label n cont₀, ?_⟩
  simp [Config.toLime, AdminInstr.map, hb'.1, hb'.2.1, hb'.2.2, ← hc,
    Silmaril.Wasm.V1.Expr.toLime_eq_map]

open Silmaril.Wasm.V1.Execution (Config.toLime) in
theorem stepB_frame {src : V10.OHost H} {s s' : V10.LStore H} {inner inner' : Frame}
    {before after : List LAdmin} (ih : StepB src ⟨s, inner, before⟩ ⟨s', inner', after⟩)
    (n : Nat) (outer : Frame) :
    StepB src ⟨s, outer, [.frame n inner before]⟩ ⟨s', outer, [.frame n inner' after]⟩ := by
  intro s₀ A hs₁ hs hA
  obtain ⟨B, rfl, hB⟩ := code_frame hA
  obtain ⟨⟨bs, bf, bc⟩, hstep, hb⟩ := ih s₀ B hs₁ hs hB
  have hb' : s' = bs.mapCode Silmaril.Wasm.V1.Func.toLime ∧ inner' = bf ∧
      after = codeToLime bc := by
    simpa [Config.toLime] using hb
  refine ⟨⟨bs, outer, [.frame n bf bc]⟩, hstep.frame n outer, ?_⟩
  simp [Config.toLime, AdminInstr.map, hb'.1, hb'.2.1, hb'.2.2]

open Silmaril.Wasm.V1.Execution (Config.toLime) in
theorem stepB_pure {src : V10.OHost H} {s : V10.LStore H} {f : Frame}
    {before after : List LAdmin}
    (hp : Silmaril.Wasm.Lime1.Execution.PureStep f.module.types before after) :
    StepB src ⟨s, f, before⟩ ⟨s, f, after⟩ := by
  intro s₀ A _ hs hA
  obtain ⟨B, hB, rfl⟩ := pure_back hp A hA
  exact ⟨⟨s₀, f, B⟩, .pure s₀ f hB, by simp [Config.toLime, show s = _ from hs]⟩

open Silmaril.Wasm.V1.Execution (Config.toLime) in
theorem stepB_invokeWasm {src : V10.OHost H} {s₀ : V10.OStore H} {f : Frame} {a : FuncAddr}
    {ft : Lime1.FuncType} {module : ModuleInst} {fn : Lime1.Func} {args : List Value}
    (hs₁ : Store1 s₀)
    (found : (s₀.mapCode Silmaril.Wasm.V1.Func.toLime).funcs[a.value]? =
      some (.wasm ft module fn))
    (arity : args.length = ft.params.length) :
    ∃ b, Silmaril.Wasm.V1.Execution.Step src
      ⟨s₀, f, Silmaril.Wasm.V1.Execution.values args ++ [.invoke a]⟩ b ∧
      (⟨s₀.mapCode Silmaril.Wasm.V1.Func.toLime, f, [.frame ft.results.length
        ⟨args ++ fn.locals.map Value.zero, module⟩
        [.label ft.results.length [] (Silmaril.Wasm.Lime1.Execution.expression fn.body)]]⟩ :
        Silmaril.Wasm.Lime1.Execution.Config H) = b.toLime := by
  obtain ⟨fn₀, hf₀, hmap⟩ := found_back found
  cases fn₀ with
  | wasm ft' m' c' =>
    simp only [FuncInst.mapCode, FuncInst.wasm.injEq] at hmap
    obtain ⟨rfl, rfl, rfl⟩ := hmap
    exact ⟨_, .invokeWasm s₀ f a ft' m' c' args hf₀ arity (hs₁ _ _ _ (List.mem_of_getElem? hf₀)),
      by simp [Config.toLime, AdminInstr.map, Silmaril.Wasm.V1.Func.toLime]⟩
  | host => simp [FuncInst.mapCode] at hmap

/-- The transported host's answer on an image store is the image of a 1.0 answer. -/
theorem host_back {src : V10.OHost H} {s₀ : V10.OStore H} {h : H} {args : List Value}
    {out : HostOutcome Lime1.Func H}
    (hb : src.mapCode Silmaril.Wasm.V1.Func.toLime h
      (s₀.mapCode Silmaril.Wasm.V1.Func.toLime) args out) :
    ∃ out₀, src h s₀ args out₀ ∧ out = HostOutcome.mapCode Silmaril.Wasm.V1.Func.toLime out₀ := by
  obtain ⟨before, result, hsb, hout, hsrc⟩ := hb
  have hbefore : before = s₀ := store_injective hsb.symm
  exact ⟨result, hbefore ▸ hsrc, hout⟩

open Silmaril.Wasm.V1.Execution (Config.toLime) in
theorem stepB_invokeHost {src : V10.OHost H} {s₀ : V10.OStore H} {s' : V10.LStore H}
    {f : Frame} {a : FuncAddr} {ft : Lime1.FuncType} {fn : H} {args : List Value} {r : Result}
    (found : (s₀.mapCode Silmaril.Wasm.V1.Func.toLime).funcs[a.value]? = some (.host ft fn))
    (arity : args.length = ft.params.length)
    (behavior : src.mapCode Silmaril.Wasm.V1.Func.toLime fn
      (s₀.mapCode Silmaril.Wasm.V1.Func.toLime) args (.returned s' r)) :
    ∃ b, Silmaril.Wasm.V1.Execution.Step src
      ⟨s₀, f, Silmaril.Wasm.V1.Execution.values args ++ [.invoke a]⟩ b ∧
      (⟨s', f, Silmaril.Wasm.Lime1.Execution.result r⟩ :
        Silmaril.Wasm.Lime1.Execution.Config H) = b.toLime := by
  obtain ⟨fn₀, hf₀, hmap⟩ := found_back found
  obtain ⟨out₀, hsrc, hout⟩ := host_back behavior
  cases fn₀ with
  | wasm => simp [FuncInst.mapCode] at hmap
  | host ft' h' =>
    simp only [FuncInst.mapCode, FuncInst.host.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    cases out₀ with
    | returned s₀' r' =>
      simp only [HostOutcome.mapCode, Silmaril.Wasm.Execution.Host.Outcome.returned.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      exact ⟨_, .invokeHost s₀ s₀' f a ft' h' args _ hf₀ arity hsrc, by simp [Config.toLime]⟩
    | diverged => simp [HostOutcome.mapCode] at hout

open Silmaril.Wasm.V1.Execution (Config.toLime) in
theorem stepB_invokeHostDiverges {src : V10.OHost H} {s₀ : V10.OStore H}
    {f : Frame} {a : FuncAddr} {ft : Lime1.FuncType} {fn : H} {args : List Value}
    (found : (s₀.mapCode Silmaril.Wasm.V1.Func.toLime).funcs[a.value]? = some (.host ft fn))
    (arity : args.length = ft.params.length)
    (behavior : src.mapCode Silmaril.Wasm.V1.Func.toLime fn
      (s₀.mapCode Silmaril.Wasm.V1.Func.toLime) args .diverged) :
    ∃ b, Silmaril.Wasm.V1.Execution.Step src
      ⟨s₀, f, Silmaril.Wasm.V1.Execution.values args ++ [.invoke a]⟩ b ∧
      (⟨s₀.mapCode Silmaril.Wasm.V1.Func.toLime, f,
        Silmaril.Wasm.Lime1.Execution.values args ++ [.invoke a]⟩ :
        Silmaril.Wasm.Lime1.Execution.Config H) = b.toLime := by
  obtain ⟨fn₀, hf₀, hmap⟩ := found_back found
  obtain ⟨out₀, hsrc, hout⟩ := host_back behavior
  cases fn₀ with
  | wasm => simp [FuncInst.mapCode] at hmap
  | host ft' h' =>
    simp only [FuncInst.mapCode, FuncInst.host.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    cases out₀ with
    | returned => simp [HostOutcome.mapCode] at hout
    | diverged =>
      exact ⟨_, .invokeHostDiverges s₀ f a ft' h' args hf₀ arity hsrc,
        by simp [Config.toLime, AdminInstr.map]⟩

set_option linter.unusedSimpArgs false in
open Silmaril.Wasm.V1.Execution (Config.toLime) in
/-- **The backward lock-step simulation.** -/
theorem step_back {src : V10.OHost H} {c c' : Silmaril.Wasm.Lime1.Execution.Config H}
    (h : Silmaril.Wasm.Lime1.Execution.Step (src.mapCode Silmaril.Wasm.V1.Func.toLime) c c') :
    StepB src c c' := by
  induction h with
  | pure s f hp => exact stepB_pure hp
  | context _ vs tail ih => exact stepB_context ih vs tail
  | label _ n cont ih => exact stepB_label ih n cont
  | frame _ n outer ih => exact stepB_frame ih n outer
  | localGet s f i v found =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := []) (j := .localGet i) hA (.localGet s₀ f i v found) (by simp [Config.toLime, AdminInstr.map])
  | localSet s f i v old found =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [v]) (j := .localSet i) hA (.localSet s₀ f i v old found)
      (by simp [Config.toLime, AdminInstr.map])
  | globalGet s f i a g index found =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := []) (j := .globalGet i) hA (.globalGet s₀ f i a g index found)
      (by simp [Config.toLime, AdminInstr.map])
  | globalSet s f i a g v index found mutable =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [v]) (j := .globalSet i) hA (.globalSet s₀ f i a g v index found mutable)
      (by simp [Config.toLime, AdminInstr.map])
  | call s f i a found =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := []) (j := .call i) hA (.call s₀ f i a found) (by simp [Config.toLime, AdminInstr.map])
  | callIndirect s f i c table a fn ft tableFound typeFound element found typeMatch =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    obtain ⟨fn₀, hf₀, rfl⟩ := found_back found
    exact leaf (vs := [.int .i32 c]) (j := .callIndirect i) hA (.callIndirect s₀ f i c table a fn₀
      ft tableFound typeFound element hf₀ (by simpa using typeMatch)) (by simp [Config.toLime, AdminInstr.map])
  | callIndirectBounds s f i c table tableFound outOfBounds =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c]) (j := .callIndirect i) hA
      (.callIndirectBounds s₀ f i c table tableFound outOfBounds) (by simp [Config.toLime, AdminInstr.map])
  | callIndirectNull s f i c table tableFound null =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c]) (j := .callIndirect i) hA
      (.callIndirectNull s₀ f i c table tableFound null) (by simp [Config.toLime, AdminInstr.map])
  | callIndirectType s f i c table a fn ft tableFound typeFound element found typeMismatch =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    obtain ⟨fn₀, hf₀, rfl⟩ := found_back found
    exact leaf (vs := [.int .i32 c]) (j := .callIndirect i) hA (.callIndirectType s₀ f i c table a
      fn₀ ft tableFound typeFound element hf₀ (by simpa using typeMismatch)) (by simp [Config.toLime, AdminInstr.map])
  | invokeWasm s f a ft module fn args found arity =>
    intro s₀ A hs₁ hs hA
    obtain rfl : s = _ := hs
    rw [code_vals_invoke hA]
    exact stepB_invokeWasm hs₁ found arity
  | invokeHost s s' f a ft fn args r found arity behavior =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    rw [code_vals_invoke hA]
    exact stepB_invokeHost found arity behavior
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    rw [code_vals_invoke hA]
    exact stepB_invokeHostDiverges found arity behavior
  | intLoad s f t packed arg c a m v memory loaded =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c]) (j := .intLoad t packed arg) hA
      (.intLoad s₀ f t packed arg c a m v memory loaded) (by simp [Config.toLime, AdminInstr.map])
  | intLoadTrap s f t packed arg c a m memory loaded =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c]) (j := .intLoad t packed arg) hA
      (.intLoadTrap s₀ f t packed arg c a m memory loaded) (by simp [Config.toLime, AdminInstr.map])
  | floatLoad s f t arg c a m v memory loaded =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c]) (j := .floatLoad t arg) hA
      (.floatLoad s₀ f t arg c a m v memory loaded) (by simp [Config.toLime, AdminInstr.map])
  | floatLoadTrap s f t arg c a m memory loaded =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c]) (j := .floatLoad t arg) hA
      (.floatLoadTrap s₀ f t arg c a m memory loaded) (by simp [Config.toLime, AdminInstr.map])
  | intStore s f t packed arg c x a m bytes memory stored =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c, .int t x]) (j := .intStore t packed arg) hA
      (.intStore s₀ f t packed arg c x a m bytes memory stored) (by simp [Config.toLime, AdminInstr.map])
  | intStoreTrap s f t packed arg c x a m memory stored =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c, .int t x]) (j := .intStore t packed arg) hA
      (.intStoreTrap s₀ f t packed arg c x a m memory stored) (by simp [Config.toLime, AdminInstr.map])
  | floatStore s f t arg c x a m bytes memory stored =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c, .float t x]) (j := .floatStore t arg) hA
      (.floatStore s₀ f t arg c x a m bytes memory stored) (by simp [Config.toLime, AdminInstr.map])
  | floatStoreTrap s f t arg c x a m memory stored =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c, .float t x]) (j := .floatStore t arg) hA
      (.floatStoreTrap s₀ f t arg c x a m memory stored) (by simp [Config.toLime, AdminInstr.map])
  | memorySize s f a m memory =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := []) (j := .memorySize) hA (.memorySize s₀ f a m memory)
      (by simp [Config.toLime, AdminInstr.map])
  | memoryGrow s f a m c r bytes memory grown =>
    intro s₀ A _ hs hA
    obtain rfl : s = _ := hs
    exact leaf (vs := [.int .i32 c]) (j := .memoryGrow) hA (.memoryGrow s₀ f a m c r bytes memory grown)
      (by simp [Config.toLime, AdminInstr.map])
  | memoryCopy s f d src' cnt =>
    intro _ A _ _ hA
    exact (no_leaf (vs := [.int .i32 d, .int .i32 src', .int .i32 cnt]) memoryCopy_not_image hA).elim
  | memoryCopyTrap s f d src' cnt =>
    intro _ A _ _ hA
    exact (no_leaf (vs := [.int .i32 d, .int .i32 src', .int .i32 cnt]) memoryCopy_not_image hA).elim
  | memoryFill s f d byte cnt =>
    intro _ A _ _ hA
    exact (no_leaf (vs := [.int .i32 d, .int .i32 byte, .int .i32 cnt]) memoryFill_not_image hA).elim
  | memoryFillTrap s f d byte cnt =>
    intro _ A _ _ hA
    exact (no_leaf (vs := [.int .i32 d, .int .i32 byte, .int .i32 cnt]) memoryFill_not_image hA).elim

/-- **`StepBack` holds at every 1.0 host.** -/
theorem stepBack (src : V10.OHost H) : StepBack src := by
  intro a b' hs₁ h
  rcases a with ⟨s₀, f, A⟩
  exact step_back h s₀ A hs₁ rfl rfl

end Silmaril.Proofs.Wasm.Models.V10Lime1Back
