module

public import Silmaril.Wasm.V1.Execution.Inversion

/-!
# One-step inversions for the run of an idle function

An *idle* function has type `[] -> []` and the empty body. Invoking it on a value stack `vs`
takes three steps: the invocation pushes an activation frame holding an empty label, the label
exits, and the frame exits, leaving `vs`. These lemmas say each step is the only one available,
at any value stack: `step_invoke_inv`, `step_frame_label_inv` and `step_frame_nil_inv`.

They are new, written for `Silmaril.Wasm.Replace.Example`. silmaril-lean's `Step.invoke_inv`,
`Step.label_inv` and `Step.frame_inv` decompose a step at those redexes; the one gap they leave,
the step at a lone invocation, is `step_invoke_singleton`.
-/

@[expose] public section

namespace Silmaril.Wasm.Replace.Example

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1 (Expr Func FuncType)

variable {H : Type}

/-- A value prefix, a non-empty code and a tail making up one instruction: the prefix and the
tail are empty. -/
theorem append_eq_singleton {ws : List Value} {before tl : List Admin} {x : Admin}
    (hb : before ≠ []) (h : values ws ++ before ++ tl = [x]) :
    ws = [] ∧ before = [x] ∧ tl = [] := by
  have hlen : ws.length + before.length + tl.length = 1 := by
    simpa only [List.length_append, values_length, List.length_singleton] using
      congrArg List.length h
  have hb' : before.length ≠ 0 := by simpa using hb
  have hws : ws = [] := List.eq_nil_of_length_eq_zero (by omega)
  have htl : tl = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hbefore : before = [x] := by simpa [hws, htl, values] using h
  exact ⟨hws, hbefore, htl⟩

/-- A saturated invocation that is a lone invocation of `a` has no arguments. -/
theorem invoke_eq_singleton {args : List Value} {b a : FuncAddr}
    (h : values args ++ [AdminInstr.invoke b] = [.invoke a]) : args = [] ∧ b = a := by
  have hargs : args = [] := by simpa using congrArg List.length h
  have hb : b = a := by simpa [hargs, values] using h
  exact ⟨hargs, hb⟩

/-- **The step at a lone invocation of a Wasm function** is `Step.invokeWasm`, on no
arguments. -/
theorem step_invoke_singleton {host : HostSemantics H} {a : FuncAddr} {ft : Silmaril.Wasm.V1.FuncType}
    {md : ModuleInst} {fn : Silmaril.Wasm.V1.Func} :
    ∀ {c c' : Config H}, Step host c c' → c.code = [.invoke a] →
      c.store.funcs[a.value]? = some (.wasm ft md fn) →
      c' = ⟨c.store, c.frame, [.frame ft.results.length ⟨fn.locals.map Value.zero, md⟩
        [.label ft.results.length [] (expression fn.body)]]⟩ := by
  intro c c' h
  induction h with
  | @pure s f before after hp =>
    intro (hc : before = _) _
    have hred : firstRedex before = some (AdminInstr.invoke a) := by rw [hc]; simp
    exact absurd hred (hp.firstRedex_ne_invoke a)
  | @context s s' f f' before after hstep vs tail ih =>
    intro hc hf
    have hne : before ≠ [] := fun hnil => hstep.firstRedex_ne_none (by rw [hnil]; rfl)
    obtain ⟨hvs, hbefore, htail⟩ := append_eq_singleton hne hc
    have he := ih hbefore hf
    simp only [Config.mk.injEq] at he ⊢
    exact ⟨he.1, he.2.1, by rw [hvs, htail, he.2.2]; rfl⟩
  | label _ n cont => intro hc; exact absurd hc (by simp)
  | frame _ n outer => intro hc; exact absurd hc (by simp)
  | invokeWasm s f b ft' md' fn' args found =>
    intro hc hf
    obtain ⟨hargs, hb⟩ := invoke_eq_singleton hc
    have hf' : s.funcs[b.value]? = some (.wasm ft md fn) := hb ▸ hf
    have hfn : (FuncInst.wasm ft' md' fn' : FuncInst Silmaril.Wasm.V1.Func H) = .wasm ft md fn :=
      Option.some.inj (found.symm.trans hf')
    cases hfn
    rw [hargs, List.nil_append]
  | invokeHost s s' f b ft' fn' args r found =>
    intro hc (hf : s.funcs[a.value]? = _)
    obtain ⟨-, hb⟩ := invoke_eq_singleton hc
    have hne : (FuncInst.host ft' fn' : FuncInst Silmaril.Wasm.V1.Func H) ≠ .wasm ft md fn := by simp
    exact absurd (Option.some.inj (found.symm.trans (hb ▸ hf))) hne
  | invokeHostDiverges s f b ft' fn' args found =>
    intro hc (hf : s.funcs[a.value]? = _)
    obtain ⟨-, hb⟩ := invoke_eq_singleton hc
    have hne : (FuncInst.host ft' fn' : FuncInst Silmaril.Wasm.V1.Func H) ≠ .wasm ft md fn := by simp
    exact absurd (Option.some.inj (found.symm.trans (hb ▸ hf))) hne
  | _ => intro hc; exact absurd hc (by simp)

/-- **The step at an invocation of a nullary Wasm function**, at any value stack, is
`Step.invokeWasm` on no arguments: the stack stays underneath. -/
theorem step_invoke_inv {host : HostSemantics H} {s : Store H} {g : Frame} {a : FuncAddr}
    {rs : List Silmaril.Wasm.V1.ValType} {md : ModuleInst} {fn : Silmaril.Wasm.V1.Func} {vs : List Value}
    {c' : Config H} (found : s.funcs[a.value]? = some (.wasm ⟨[], rs⟩ md fn))
    (h : Step host ⟨s, g, values vs ++ [.invoke a]⟩ c') :
    c' = ⟨s, g, values vs ++ [.frame rs.length ⟨fn.locals.map Value.zero, md⟩
      [.label rs.length [] (expression fn.body)]]⟩ := by
  obtain ⟨hframe, pre, args, X, hvs, ⟨fi, hfi, hlen⟩, hpoly, -, hcode⟩ :=
    h.invoke_inv (vs := vs) (tail := []) rfl
  have hfi' : fi = .wasm ⟨[], rs⟩ md fn := Option.some.inj (hfi.symm.trans found)
  have hargs : args = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hfi']; rfl)
  have hpre : pre = vs := by rw [hvs, hargs, List.append_nil]
  have hX := step_invoke_singleton (hpoly g) (by rw [hargs]; rfl) found
  simp only [Config.mk.injEq] at hX
  obtain ⟨st, fr, cd⟩ := c'
  have hcd : cd = values vs ++ X := by simpa [hpre] using hcode
  simp only [Config.mk.injEq]
  exact ⟨hX.1, hframe, by rw [hcd, hX.2.2]⟩

/-- A store-independent rule out of a label around the empty body leaves the empty code. -/
theorem pureStep_label_nil_inv {before after : List Admin} (h : PureStep before after)
    {n : Nat} {cont : Silmaril.Wasm.V1.Expr} (hb : before = [.label n cont []]) : after = [] := by
  cases h <;> simp_all [values]

/-- A store-independent rule out of a frame around the empty body leaves the empty code. -/
theorem pureStep_frame_nil_inv {before after : List Admin} (h : PureStep before after)
    {n : Nat} {fr : Frame} (hb : before = [.frame n fr []]) : after = [] := by
  cases h <;> simp_all [values]

/-- No store-independent rule applies to a frame around a label. -/
theorem pureStep_frame_label_inv {before after : List Admin} (h : PureStep before after)
    {n m : Nat} {fr : Frame} {cont : Silmaril.Wasm.V1.Expr} {body : List Admin}
    (hb : before = [.frame n fr [.label m cont body]]) : False := by
  cases h
  case frameReturn extra vs tail _ =>
    obtain ⟨-, -, hbody⟩ : _ ∧ _ ∧ values extra ++ (values vs ++ .source .return_ :: tail) =
        [.label m cont body] := by simpa using hb
    have hr := congrArg firstRedex hbody
    simp [firstRedex_cons, asValue?] at hr
  all_goals simp_all [values]

/-- Nothing steps out of the empty code. -/
theorem not_step_nil {host : HostSemantics H} {s : Store H} {f : Frame} {c' : Config H} :
    ¬ Step host ⟨s, f, []⟩ c' :=
  fun h => h.firstRedex_ne_none rfl

/-- The only step out of a label around the empty body exits it. -/
theorem step_label_nil_inv {host : HostSemantics H} {s : Store H} {f : Frame} {n : Nat}
    {cont : Silmaril.Wasm.V1.Expr} {c' : Config H} (h : Step host ⟨s, f, [.label n cont []]⟩ c') :
    c' = ⟨s, f, []⟩ := by
  rcases h.label_inv (p := []) (q := []) rfl with ⟨_, hinner, -⟩ | ⟨after, hp, hs, hf, hcode⟩
  · exact absurd hinner not_step_nil
  · have hafter : after = [] := pureStep_label_nil_inv hp rfl
    obtain ⟨st, fr, cd⟩ := c'
    simp only [Config.mk.injEq]
    exact ⟨hs.symm, hf, by simpa [hafter, values] using hcode⟩

/-- The only step out of a frame around an empty label exits the label. -/
theorem step_frame_label_inv {host : HostSemantics H} {s : Store H} {g fr : Frame}
    {n m : Nat} {cont : Silmaril.Wasm.V1.Expr} {vs : List Value} {c' : Config H}
    (h : Step host ⟨s, g, values vs ++ [.frame n fr [.label m cont []]]⟩ c') :
    c' = ⟨s, g, values vs ++ [.frame n fr []]⟩ := by
  obtain ⟨st, f, cd⟩ := c'
  obtain ⟨(hframe : f = g), hcases⟩ := h.frame_inv (p := vs) (q := []) rfl
  rcases hcases with ⟨fr', body', hinner, (hcode : cd = _)⟩ | ⟨after, hp, -, -⟩
  · have he : (⟨st, fr', body'⟩ : Config H) = ⟨s, fr, []⟩ := step_label_nil_inv hinner
    simp only [Config.mk.injEq] at he ⊢
    exact ⟨he.1, hframe, by rw [hcode, he.2.1, he.2.2]⟩
  · exact (pureStep_frame_label_inv hp rfl).elim

/-- The only step out of a frame around the empty body exits it. -/
theorem step_frame_nil_inv {host : HostSemantics H} {s : Store H} {g fr : Frame} {n : Nat}
    {vs : List Value} {c' : Config H} (h : Step host ⟨s, g, values vs ++ [.frame n fr []]⟩ c') :
    c' = ⟨s, g, values vs⟩ := by
  obtain ⟨hframe, hcases⟩ := h.frame_inv (p := vs) (q := []) rfl
  rcases hcases with ⟨fr', body', hinner, -⟩ | ⟨after, hp, hs, hcode⟩
  · exact absurd hinner not_step_nil
  · have hafter : after = [] := pureStep_frame_nil_inv hp rfl
    obtain ⟨st, f, cd⟩ := c'
    simp only [Config.mk.injEq]
    exact ⟨hs.symm, hframe, by simpa [hafter] using hcode⟩

/-- Nothing steps out of a value stack. -/
theorem not_step_values {host : HostSemantics H} {s : Store H} {f : Frame} {vs : List Value}
    {c' : Config H} : ¬ Step host ⟨s, f, values vs⟩ c' :=
  fun h => h.firstRedex_ne_none (firstRedex_values vs)

end Silmaril.Wasm.Replace.Example
