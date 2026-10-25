module

public import Silmaril.Wasm.V1.Execution.Callout

/-!
# Inverting WebAssembly 1.0 reduction at a call boundary

`Silmaril/Wasm/V1/Execution/Step.lean` gives reduction by three congruence
rules — `Step.context`, `Step.label` and `Step.frame` — and a redex rule for
every instruction. Composition through those congruences is
`Silmaril/Wasm/V1/Execution/Properties.lean` (`Steps.context` and friends).
What is missing, and what this file supplies, is the **inversion**: given a
reduction out of a configuration whose active position is a function
invocation, recover the step that the invocation itself took.

## The leading redex

`firstRedex` returns the first administrative instruction of a code sequence
that is not a runtime value. It is the position at which every rule of the
machine acts, and `Step.firstRedex_ne_none` says a configuration that steps has
one.

## Sealed code

`Sealed` is the invariant of an invocation in flight: a prefix of values
followed by at most one trap, pending invocation or activation frame. It is
exactly the set of code sequences reachable from `values args ++ [.invoke a]`,
and it is closed under reduction (`Sealed.step`). Two facts fall out, and they
are the content of the file:

* reduction of sealed code **never reads or writes the enclosing frame**
  (`Sealed.step` produces a step at *every* frame, and leaves the frame it is
  given alone) — the frame of an invocation is the one `Step.invokeWasm`
  pushes, never the caller's;
* consequently sealed runs transport through any evaluation context and any
  frame (`Sealed.steps_plug`), which composes with `Step.plug` of
  `Silmaril/Wasm/V1/Execution/Callout.lean`.

`Sealed.steps` and `Sealed.diverges` are the finite and infinite forms.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*}

/-! ## The leading redex -/

/-- The first administrative instruction that is not a runtime value, if any.
Every reduction rule of the machine acts at this position. -/
def firstRedex : List Admin → Option Admin
  | [] => none
  | x :: rest =>
    match asValue? x with
    | some _ => firstRedex rest
    | none => some x

/-- `firstRedex` on the empty code sequence. -/
@[simp] theorem firstRedex_nil : firstRedex [] = none := rfl

/-- `firstRedex` unfolded at a cons. -/
theorem firstRedex_cons (x : Admin) (rest : List Admin) :
    firstRedex (x :: rest) =
      match asValue? x with
      | some _ => firstRedex rest
      | none => some x := rfl

/-- A leading value is skipped. -/
@[simp] theorem firstRedex_value_cons (v : Runtime.Value) (rest : List Admin) :
    firstRedex (value v :: rest) = firstRedex rest := by
  simp only [firstRedex_cons, asValue?_value]

/-- The leading redex of a concatenation is the first one that exists. -/
@[simp] theorem firstRedex_append (l₁ l₂ : List Admin) :
    firstRedex (l₁ ++ l₂) = (firstRedex l₁).or (firstRedex l₂) := by
  induction l₁ with
  | nil => simp
  | cons x rest ih =>
    simp only [List.cons_append, firstRedex_cons]
    cases asValue? x <;> simp [ih]

/-- A sequence of values has no redex. -/
@[simp] theorem firstRedex_values (vs : List Runtime.Value) : firstRedex (values vs) = none := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa only [values, List.map_cons, firstRedex_value_cons] using ih

/-- Having no leading redex means being a sequence of values. -/
theorem firstRedex_eq_none_iff {l : List Admin} :
    firstRedex l = none ↔ ∀ x ∈ l, asValue? x ≠ none := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    simp only [firstRedex_cons, List.mem_cons]
    cases h : asValue? x with
    | none => simp [h]
    | some v => simp only [reduceCtorEq, true_and, ih, h, forall_eq_or_imp,
        ne_eq, not_false_eq_true, true_and]

/-- A configuration that reduces has a leading redex. -/
theorem Step.firstRedex_ne_none {host : HostSemantics H} {a b : Config H} (h : Step host a b) :
    firstRedex a.code ≠ none := by
  intro hnone
  obtain ⟨x, hx, hv⟩ := h.nonvalue
  exact firstRedex_eq_none_iff.mp hnone x hx hv

/-! ## Sealed code -/

/--
The instructions that may follow the value prefix of an invocation in flight: a
trap, a pending invocation, or an activation frame. Each of them reduces
without consulting the enclosing frame.
-/
inductive SealedHead : Admin → Prop where
  /-- A trap. -/
  | trap : SealedHead .trap
  /-- A pending invocation. -/
  | invoke (a : FuncAddr) : SealedHead (.invoke a)
  /-- An activation frame, which supplies its own frame to its body. -/
  | frame (n : Nat) (fr : Frame) (body : List Admin) : SealedHead (.frame n fr body)

/--
Code that is a self-contained invocation in flight: a prefix of values followed
by at most one trap, pending invocation or activation frame. This is the
reduction-closed invariant of `values args ++ [.invoke a]`.
-/
inductive Sealed : List Admin → Prop where
  /-- A finished invocation: only values are left. -/
  | values (vs : List Runtime.Value) : Sealed (values vs)
  /-- Values followed by the instruction the invocation is parked at. -/
  | head (vs : List Runtime.Value) {x : Admin} (h : SealedHead x) : Sealed (values vs ++ [x])

/-- A sealed head is never a value. -/
theorem SealedHead.not_value {x : Admin} (h : SealedHead x) : asValue? x = none := by
  cases h <;> rfl

/-- The explicit shape of sealed code. -/
theorem sealed_iff {code : List Admin} :
    Sealed code ↔ (∃ vs, code = values vs) ∨
      ∃ (vs : List Runtime.Value) (x : Admin), SealedHead x ∧ code = values vs ++ [x] := by
  constructor
  · intro h
    cases h with
    | values vs => exact .inl ⟨vs, rfl⟩
    | head vs hx => exact .inr ⟨vs, _, hx, rfl⟩
  · rintro (⟨vs, rfl⟩ | ⟨vs, x, hx, rfl⟩)
    · exact .values vs
    · exact .head vs hx

/-- Every result — a value sequence or a trap — is sealed. -/
theorem sealed_result (r : Runtime.Result) : Sealed (result r) := by
  cases r with
  | values vs => exact .values vs
  | trap => simpa only [result, values, List.map_nil, List.nil_append] using
      Sealed.head (x := .trap) [] .trap

/-- A lone trap is sealed. -/
theorem sealed_trap : Sealed [.trap] := sealed_result .trap

/-- The leading redex of sealed code, if any, is a sealed head. -/
theorem Sealed.sealedHead {code : List Admin} (h : Sealed code) {x : Admin}
    (hx : firstRedex code = some x) : SealedHead x := by
  rcases sealed_iff.mp h with ⟨vs, rfl⟩ | ⟨vs, y, hy, rfl⟩
  · simp at hx
  · rw [firstRedex_append, firstRedex_values, Option.none_or, firstRedex_cons,
      hy.not_value] at hx
    cases hx
    exact hy

/--
**Sealed code splits at its leading redex.** If sealed code is cut as a value
prefix, a middle part that has a redex, and a tail, then the middle part is
itself sealed and the tail is empty: nothing of an invocation in flight follows
the position at which it reduces.
-/
theorem sealed_split {vs : List Runtime.Value} {mid tail : List Admin}
    (h : Sealed (values vs ++ mid ++ tail)) (hmid : firstRedex mid ≠ none) :
    Sealed mid ∧ tail = [] := by
  have hor : ∀ l₁ l₂ : List Admin, firstRedex (l₁ ++ l₂) = none → firstRedex l₁ = none := by
    intro l₁ l₂ hl
    rw [firstRedex_append] at hl
    cases hl₁ : firstRedex l₁ with
    | none => rfl
    | some x => rw [hl₁] at hl; simp at hl
  have novalues : ∀ c : List Admin, (∃ ws : List Runtime.Value, values ws = mid ++ c) → False := by
    rintro c ⟨ws, hw⟩
    exact hmid (hor mid c (by rw [← hw, firstRedex_values]))
  rcases sealed_iff.mp h with ⟨ws, hws⟩ | ⟨ws, x, hx, hws⟩
  · exfalso
    have hn : firstRedex (values vs ++ mid ++ tail) = none := by rw [hws, firstRedex_values]
    rw [firstRedex_append, firstRedex_append, firstRedex_values, Option.none_or] at hn
    cases hm : firstRedex mid with
    | none => exact hmid hm
    | some y => rw [hm] at hn; simp at hn
  · rw [List.append_assoc] at hws
    rcases List.append_eq_append_iff.mp hws with ⟨c, hc, hrest⟩ | ⟨c, hc, hrest⟩
    · have hcv : c = values (ws.drop vs.length) := by
        have h1 : (values vs ++ c).drop vs.length = c := by
          rw [← values_length vs]; exact List.drop_left
        rw [← hc] at h1
        rw [← h1]
        simp only [values, List.map_drop]
      subst hcv
      rcases List.append_eq_append_iff.mp hrest with ⟨d, hd, -⟩ | ⟨d, hd, hrest'⟩
      · exact absurd ⟨_, hd⟩ (novalues d)
      · rcases d with _ | ⟨y, d'⟩
        · exact absurd ⟨_, by simpa using hd.symm⟩ (novalues [])
        · have hy : x = y ∧ d' ++ tail = [] := by simpa using hrest'
          obtain ⟨rfl, hnil⟩ := hy
          obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hnil
          exact ⟨hd ▸ Sealed.head _ hx, rfl⟩
    · rcases c with _ | ⟨z, c'⟩
      · simp only [List.nil_append] at hrest
        rcases mid with _ | ⟨y, mid'⟩
        · simp at hmid
        · have hy : x = y ∧ mid' ++ tail = [] := by simpa using hrest
          obtain ⟨rfl, hnil⟩ := hy
          obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hnil
          refine ⟨?_, rfl⟩
          simpa only [values, List.map_nil, List.nil_append] using Sealed.head (x := x) [] hx
      · exfalso
        have hz : x = z ∧ c' ++ (mid ++ tail) = [] := by simpa using hrest
        obtain ⟨rfl, hnil⟩ := hz
        obtain ⟨-, hnil'⟩ := List.append_eq_nil_iff.mp hnil
        obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hnil'
        simp at hmid


/-- A leading trap is the redex. -/
@[simp] theorem firstRedex_trap_cons (rest : List Admin) :
    firstRedex (.trap :: rest) = some .trap := rfl

/-- A leading invocation is the redex. -/
@[simp] theorem firstRedex_invoke_cons (a : FuncAddr) (rest : List Admin) :
    firstRedex (.invoke a :: rest) = some (.invoke a) := rfl

/-- A leading label is the redex. -/
@[simp] theorem firstRedex_label_cons (n : Nat) (cont : Expr) (body rest : List Admin) :
    firstRedex (.label n cont body :: rest) = some (.label n cont body) := rfl

/-- A leading frame is the redex. -/
@[simp] theorem firstRedex_frame_cons (n : Nat) (fr : Frame) (body rest : List Admin) :
    firstRedex (.frame n fr body :: rest) = some (.frame n fr body) := rfl

/-- A source instruction is never a sealed head. -/
theorem SealedHead.not_source {i : Instr} (h : SealedHead (.source i)) : False := by cases h

/-- A label is never a sealed head: a label's body is not an invocation in
flight, because a branch out of it reads the enclosing frame. -/
theorem SealedHead.not_label {n : Nat} {cont : Expr} {body : List Admin}
    (h : SealedHead (.label n cont body)) : False := by cases h

/-- The last instruction of sealed code is a value or a sealed head. This is
the form used to rule out every redex rule that reads the frame: each of their
left-hand sides ends in a source instruction. -/
theorem Sealed.sealedLast {code : List Admin} (h : Sealed code) {x : Admin}
    (hx : code.getLast? = some x) (hv : asValue? x = none) : SealedHead x := by
  rcases sealed_iff.mp h with ⟨vs, rfl⟩ | ⟨vs, y, hy, rfl⟩
  · exfalso
    rw [Execution.values, List.getLast?_map, Option.map_eq_some_iff] at hx
    obtain ⟨v, -, rfl⟩ := hx
    rw [asValue?_value] at hv
    exact absurd hv (by simp)
  · rw [List.getLast?_concat] at hx
    cases hx
    exact hy

/-- Prefixing values preserves sealedness. -/
theorem sealed_values_append {vs : List Runtime.Value} {l : List Admin} (h : Sealed l) :
    Sealed (values vs ++ l) := by
  rcases sealed_iff.mp h with ⟨ws, rfl⟩ | ⟨ws, x, hx, rfl⟩
  · simpa only [← values_append] using Sealed.values (vs ++ ws)
  · simpa only [← List.append_assoc, ← values_append] using Sealed.head (x := x) (vs ++ ws) hx

/-- A lone activation frame is sealed. -/
theorem sealed_frame (n : Nat) (fr : Frame) (body : List Admin) :
    Sealed [.frame n fr body] := by
  simpa only [values, List.map_nil, List.nil_append] using
    Sealed.head (x := .frame n fr body) [] (.frame n fr body)

/-- Store-independent reduction of sealed code yields sealed code. -/
theorem Sealed.pureStep {before after : List Admin} (hc : Sealed before)
    (h : PureStep before after) : Sealed after := by
  cases h with
  | trapValues v vs tail => exact sealed_trap
  | trapTail i tail => exact sealed_trap
  | frameDone n fr vs arity => exact .values vs
  | frameReturn n fr extra vs tail arity => exact .values vs
  | frameTrap n fr => exact sealed_trap
  | _ =>
    exfalso
    first
    | exact (hc.sealedLast rfl rfl).not_label
    | exact (hc.sealedLast rfl rfl).not_source

/-! ## Frame irrelevance -/

/--
**Sealed code reduces without consulting its frame.** A reduction out of sealed
code leaves the frame it is given unchanged, lands in sealed code again, and is
a reduction at *every* frame.

This is the precise sense in which an invocation never reads or writes the
frame it was invoked from: every local operation inside it takes place under
the `.frame` administrative instruction that `Step.invokeWasm` pushes, and the
congruence rule for that instruction (`Step.frame`) leaves the enclosing frame
alone.
-/
theorem Sealed.step {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hc : Sealed c.code) :
    c'.frame = c.frame ∧ Sealed c'.code ∧
      ∀ g : Frame, Step host ⟨c.store, g, c.code⟩ ⟨c'.store, g, c'.code⟩ := by
  induction h with
  | pure s f hp => exact ⟨rfl, hc.pureStep hp, fun g => .pure s g hp⟩
  | context hstep vs tail ih =>
    obtain ⟨hsealed, rfl⟩ := sealed_split hc hstep.firstRedex_ne_none
    obtain ⟨hframe, hafter, hpoly⟩ := ih hsealed
    exact ⟨hframe, by simpa only [List.append_nil] using sealed_values_append hafter,
      fun g => .context (hpoly g) vs []⟩
  | label hstep n cont ih => exact ((hc.sealedLast rfl rfl).not_label).elim
  | frame hstep n outer ih => exact ⟨rfl, sealed_frame _ _ _, fun g => .frame hstep n g⟩
  | invokeWasm s f a ft module fn args found arity resultArity =>
    exact ⟨rfl, sealed_frame _ _ _,
      fun g => .invokeWasm s g a ft module fn args found arity resultArity⟩
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact ⟨rfl, sealed_result r, fun g => .invokeHost s s' g a ft fn args r found arity behavior⟩
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact ⟨rfl, hc, fun g => .invokeHostDiverges s g a ft fn args found arity behavior⟩
  | _ => exact ((hc.sealedLast rfl rfl).not_source).elim

/-- **Sealed runs do not consult the frame.** A finite run out of sealed code
leaves the frame alone, stays sealed, and is a run at every frame. -/
theorem Sealed.steps {host : HostSemantics H} {c c' : Config H} (h : Steps host c c')
    (hc : Sealed c.code) :
    c'.frame = c.frame ∧ Sealed c'.code ∧
      ∀ g : Frame, Steps host ⟨c.store, g, c.code⟩ ⟨c'.store, g, c'.code⟩ := by
  induction h with
  | refl => exact ⟨rfl, hc, fun _ => .refl⟩
  | tail hsteps hstep ih =>
    obtain ⟨hframe, hsealed, hpoly⟩ := ih
    obtain ⟨hframe', hsealed', hpoly'⟩ := Sealed.step hstep hsealed
    exact ⟨hframe'.trans hframe, hsealed', fun g => (hpoly g).tail (hpoly' g)⟩

/-- A sealed run transports into any evaluation context, at any frame. This is
`Steps.context`, `Steps.label` and `Steps.frame` at once, and it is the lemma
that puts a matched invocation back where it came from. -/
theorem Sealed.steps_plug {host : HostSemantics H} {c c' : Config H} (h : Steps host c c')
    (hc : Sealed c.code) (K : EvalCtx Instr) (g : Frame) :
    Steps host ⟨c.store, g, K.plug value c.code⟩ ⟨c'.store, g, K.plug value c'.code⟩ := by
  induction h with
  | refl => exact .refl
  | tail hsteps hstep ih =>
    obtain ⟨-, hsealed, -⟩ := Sealed.steps hsteps hc
    obtain ⟨-, -, hpoly⟩ := Sealed.step hstep hsealed
    exact ih.tail (Step.plug hpoly K g)

/-- **Divergence of sealed code does not consult the frame.** -/
theorem Sealed.diverges {host : HostSemantics H} {s : Store H} {f g : Frame}
    {code : List Admin} (hc : Sealed code) (h : Diverges host ⟨s, f, code⟩) :
    Diverges host ⟨s, g, code⟩ := by
  refine InfiniteTrace.coinduct
    (fun d => ∃ (σ : Store H) (e : List Admin) (k : Frame),
      d = ⟨σ, g, e⟩ ∧ Sealed e ∧ Diverges host ⟨σ, k, e⟩) ?_ ⟨s, code, f, rfl, hc, h⟩
  rintro d ⟨σ, e, k, rfl, hse, hdv⟩
  obtain ⟨⟨σ', k', e'⟩, hstep, htail⟩ := hdv.unfold
  obtain ⟨-, hse', hpoly⟩ := Sealed.step hstep hse
  exact ⟨⟨σ', g, e'⟩, hpoly g, σ', e', k', rfl, hse', htail⟩

/-! ## The invocation redex

`values args ++ [.invoke a]` is sealed, so everything above applies to it; these
are the specialisations used at a call boundary. -/

/-- An invocation redex is sealed. -/
theorem sealed_invoke (args : List Runtime.Value) (a : FuncAddr) :
    Sealed (values args ++ [.invoke a]) := Sealed.head (x := .invoke a) args (.invoke a)

/-- **Frame irrelevance for a terminating invocation.** -/
theorem steps_invoke_frame {host : HostSemantics H} {s s' : Store H} {f g : Frame}
    {a : FuncAddr} {vs : List Runtime.Value} {r : Runtime.Result}
    (h : Steps host ⟨s, f, values vs ++ [.invoke a]⟩ ⟨s', f, result r⟩) :
    Steps host ⟨s, g, values vs ++ [.invoke a]⟩ ⟨s', g, result r⟩ :=
  ((Sealed.steps h (sealed_invoke vs a)).2.2) g

/-- **Frame irrelevance for a diverging invocation.** -/
theorem diverges_invoke_frame {host : HostSemantics H} {s : Store H} {f g : Frame}
    {a : FuncAddr} {vs : List Runtime.Value}
    (h : Diverges host ⟨s, f, values vs ++ [.invoke a]⟩) :
    Diverges host ⟨s, g, values vs ++ [.invoke a]⟩ :=
  Sealed.diverges (sealed_invoke vs a) h

/-! ## Inverting a step at an invocation

`Step.invoke_inv` is the inversion the machine was missing: a reduction out of
a configuration whose leading redex is `.invoke a` is one of the three
invocation rules, applied to the *saturated* suffix of the value prefix, inside
a `Step.context`. Everything else — the tail after the invocation, the values
before the arguments — is untouched.
-/

/-- The instruction a decoded value came from is that value's encoding. -/
theorem value_of_asValue? {x : Admin} {v : Runtime.Value} (h : asValue? x = some v) :
    value v = x := coding.encode_of_decode h

/-- The decomposition of a code sequence at its leading redex. -/
theorem firstRedex_eq_some {l : List Admin} {x : Admin} (h : firstRedex l = some x) :
    ∃ (ws : List Runtime.Value) (rest : List Admin), l = values ws ++ x :: rest := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rw [firstRedex_cons] at h
    cases hy : asValue? y with
    | none =>
      rw [hy] at h
      cases h
      exact ⟨[], l, by simp [Execution.values]⟩
    | some v =>
      rw [hy] at h
      obtain ⟨ws, rest, hrest⟩ := ih h
      exact ⟨v :: ws, rest, by rw [← value_of_asValue? hy, hrest]; simp [Execution.values]⟩

/-- The decomposition of a code sequence at its leading redex is unique. -/
theorem values_cons_inj {ws ws' : List Runtime.Value} {x y : Admin} {rest rest' : List Admin}
    (hx : asValue? x = none) (hy : asValue? y = none)
    (h : values ws ++ x :: rest = values ws' ++ y :: rest') :
    ws = ws' ∧ x = y ∧ rest = rest' := by
  induction ws generalizing ws' with
  | nil =>
    cases ws' with
    | nil => simpa [Execution.values] using h
    | cons v ws' =>
      exfalso
      simp only [Execution.values, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, List.cons.injEq] at h
      rw [h.1, asValue?_value] at hx
      exact absurd hx (by simp)
  | cons v ws ih =>
    cases ws' with
    | nil =>
      exfalso
      simp only [Execution.values, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, List.cons.injEq] at h
      rw [← h.1, asValue?_value] at hy
      exact absurd hy (by simp)
    | cons v' ws' =>
      simp only [Execution.values, List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨hv, hrest⟩ := h
      have hvv : v = v' := by
        have hc := congrArg asValue? hv
        simpa only [asValue?_value, Option.some.injEq] using hc
      obtain ⟨h1, h2, h3⟩ := ih (by simpa only [Execution.values] using hrest)
      exact ⟨by rw [hvv, h1], h2, h3⟩

/-- `values` on a cons. -/
theorem values_cons (v : Runtime.Value) (vs : List Runtime.Value) :
    values (v :: vs) = value v :: values vs := rfl

/-- `values` on the empty list. -/
theorem values_nil : values ([] : List Runtime.Value) = [] := rfl

set_option linter.unusedSimpArgs false in
/-- An invocation is never the leading redex of a store-independent rule. -/
theorem PureStep.firstRedex_ne_invoke {before after : List Admin} (h : PureStep before after)
    (a : FuncAddr) : firstRedex before ≠ some (.invoke a) := by
  cases h <;>
    (try simp only [values_cons, values_nil, List.nil_append, List.cons_append,
      List.append_assoc, firstRedex_value_cons, firstRedex_append, firstRedex_values,
      Option.none_or, firstRedex_trap_cons, firstRedex_label_cons, firstRedex_frame_cons]) <;>
    simp [firstRedex_cons, asValue?]

/-- `Saturated s a args`: the instance at `a` in `s` takes exactly `args` as its
arguments, so `values args ++ [.invoke a]` is the left-hand side of an
invocation rule. Without it the decomposition below is false: a step at
`[value v, .invoke a]` need not leave `value v` alone. -/
def Saturated (s : Store H) (a : FuncAddr) (args : List Runtime.Value) : Prop :=
  ∃ fi : FuncInst Func H, s.funcs[a.value]? = some fi ∧ args.length = fi.type.params.length

/--
Code parked at a redex that no enclosing evaluation context can act on: a
saturated invocation, or an activation frame. This is the invariant of a call
in flight, before it produces its result.
-/
inductive Rigid {H : Type*} (s : Store H) : List Admin → Prop where
  /-- A saturated invocation. -/
  | invoke {args : List Runtime.Value} {a : FuncAddr} (h : Saturated s a args) :
      Rigid s (values args ++ [.invoke a])
  /-- An activation frame. -/
  | frame (n : Nat) (fr : Frame) (body : List Admin) : Rigid s [.frame n fr body]

/-- Rigid code is sealed. -/
theorem Rigid.sealed {s : Store H} {code : List Admin} (h : Rigid s code) : Sealed code := by
  cases h with
  | invoke h => exact sealed_invoke _ _
  | frame n fr body => exact sealed_frame n fr body

set_option linter.unusedSimpArgs false in
/--
**Inversion at an invocation.** A reduction out of code whose leading redex is
`.invoke a` is one of `Step.invokeWasm`, `Step.invokeHost` and
`Step.invokeHostDiverges`, applied to the saturated suffix `args` of the value
prefix; the values before `args` and the instructions after the invocation are
untouched, the frame is untouched, and the step is available at every frame.
-/
theorem Step.invoke_inv {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    {vs : List Runtime.Value} {a : FuncAddr} {tail : List Admin}
    (hcode : c.code = values vs ++ .invoke a :: tail) :
    c'.frame = c.frame ∧ ∃ (pre args : List Runtime.Value) (X : List Admin),
      vs = pre ++ args ∧ Saturated c.store a args ∧
      (∀ g : Frame, Step host ⟨c.store, g, values args ++ [.invoke a]⟩ ⟨c'.store, g, X⟩) ∧
      (Rigid c'.store X ∨ ∃ r : Runtime.Result, X = result r) ∧
      c'.code = values pre ++ X ++ tail := by
  induction h generalizing vs tail with
  | pure s f hp =>
    rename_i before after
    replace hcode : before = values vs ++ .invoke a :: tail := hcode
    exact absurd (by rw [hcode]; simp) (hp.firstRedex_ne_invoke a)
  | context hstep ws tl ih =>
    rename_i s s' f f' before after
    replace hcode : values ws ++ before ++ tl = values vs ++ .invoke a :: tail := hcode
    have hne : firstRedex before ≠ none := hstep.firstRedex_ne_none
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
    have hxa : x = AdminInstr.invoke a := by
      have h1 : firstRedex (values ws ++ before ++ tl) = some x := by simp [hx]
      rw [hcode] at h1
      simpa using h1.symm
    subst hxa
    obtain ⟨rest, tail₁, hbefore⟩ := firstRedex_eq_some hx
    have heq : values (ws ++ rest) ++ (AdminInstr.invoke a) :: (tail₁ ++ tl) =
        values vs ++ (AdminInstr.invoke a) :: tail := by
      rw [← hcode, hbefore, values_append]
      simp [List.append_assoc]
    obtain ⟨h1, -, h3⟩ := values_cons_inj rfl rfl heq
    subst h1
    subst h3
    obtain ⟨hframe, pre, args, X, hrest, hsat, hpoly, hshape, hafter⟩ :=
      ih (show before = values rest ++ .invoke a :: tail₁ from hbefore)
    replace hafter : after = values pre ++ X ++ tail₁ := hafter
    refine ⟨hframe, ws ++ pre, args, X, by rw [hrest, List.append_assoc], hsat, hpoly, hshape, ?_⟩
    show values ws ++ after ++ tl = _
    rw [hafter, values_append]
    simp [List.append_assoc]
  | label hstep n cont ih =>
    rename_i s s' f f' before after
    replace hcode : [AdminInstr.label n cont before] = values vs ++ .invoke a :: tail := hcode
    exact absurd (congrArg firstRedex hcode) (by simp)
  | frame hstep n outer ih =>
    rename_i s s' inner inner' before after
    replace hcode : [AdminInstr.frame n inner before] = values vs ++ .invoke a :: tail := hcode
    exact absurd (congrArg firstRedex hcode) (by simp)
  | invokeWasm s f b ft module fn args found arity resultArity =>
    replace hcode : values args ++ AdminInstr.invoke b :: [] = values vs ++ .invoke a :: tail :=
      hcode
    obtain ⟨rfl, hba, rfl⟩ := values_cons_inj (x := .invoke b) (y := .invoke a) rfl rfl hcode
    have hb : b = a := by injection hba
    subst hb
    exact ⟨rfl, [], args, _, by simp, ⟨_, found, arity⟩,
      fun g => .invokeWasm s g b ft module fn args found arity resultArity,
      .inl (.frame _ _ _), by simp [Execution.values]⟩
  | invokeHost s s' f b ft fn args r found arity behavior =>
    replace hcode : values args ++ AdminInstr.invoke b :: [] = values vs ++ .invoke a :: tail :=
      hcode
    obtain ⟨rfl, hba, rfl⟩ := values_cons_inj (x := .invoke b) (y := .invoke a) rfl rfl hcode
    have hb : b = a := by injection hba
    subst hb
    exact ⟨rfl, [], args, result r, by simp, ⟨_, found, arity⟩,
      fun g => .invokeHost s s' g b ft fn args r found arity behavior, .inr ⟨r, rfl⟩,
      by simp [Execution.values]⟩
  | invokeHostDiverges s f b ft fn args found arity behavior =>
    replace hcode : values args ++ AdminInstr.invoke b :: [] = values vs ++ .invoke a :: tail :=
      hcode
    obtain ⟨rfl, hba, rfl⟩ := values_cons_inj (x := .invoke b) (y := .invoke a) rfl rfl hcode
    have hb : b = a := by injection hba
    subst hb
    exact ⟨rfl, [], args, _, by simp, ⟨_, found, arity⟩,
      fun g => .invokeHostDiverges s g b ft fn args found arity behavior,
      .inl (.invoke ⟨_, found, arity⟩), by simp [Execution.values]⟩
  | _ =>
    exfalso
    have hr := congrArg firstRedex (hcode : _ = values vs ++ .invoke a :: tail)
    simp only [firstRedex_append, firstRedex_values, firstRedex_invoke_cons,
      Option.none_or, values_cons, values_nil, List.nil_append, List.cons_append,
      firstRedex_value_cons] at hr
    simp [firstRedex_cons, asValue?] at hr

/-! ## Inverting a step at a label or a frame -/

/-- The administrative instructions at which a call in flight is parked: an
invocation, or a label or frame containing one. A context can never consume
them, which is why reduction has to take place inside. -/
inductive CallHead : Admin → Prop where
  /-- A pending invocation. -/
  | invoke (a : FuncAddr) : CallHead (.invoke a)
  /-- A label whose body is still running. -/
  | label (n : Nat) (cont : Expr) (body : List Admin) : CallHead (.label n cont body)
  /-- An activation frame whose body is still running. -/
  | frame (n : Nat) (fr : Frame) (body : List Admin) : CallHead (.frame n fr body)

/-- A trap is not a call head. -/
theorem CallHead.not_trap (h : CallHead .trap) : False := by cases h

/-- A source instruction is not a call head. -/
theorem CallHead.not_source {i : Instr} (h : CallHead (.source i)) : False := by cases h

set_option linter.unusedSimpArgs false in
/-- A store-independent rule whose leading redex is a call head consumes
nothing else: its left-hand side is that redex alone. -/
theorem PureStep.eq_singleton_of_firstRedex {before after : List Admin}
    (h : PureStep before after) {x : Admin} (hx : firstRedex before = some x)
    (hcall : CallHead x) : before = [x] := by
  cases h <;>
    (try simp only [values_cons, values_nil, List.nil_append, List.cons_append,
      List.append_assoc, firstRedex_value_cons, firstRedex_append, firstRedex_values,
      Option.none_or, firstRedex_trap_cons, firstRedex_label_cons, firstRedex_frame_cons,
      Option.some.injEq] at hx) <;>
    first
      | (subst hx; exact (hcall.not_trap).elim)
      | (subst hx; simp [List.append_assoc])
      | (rw [firstRedex_cons] at hx
         simp only [asValue?, Option.some.injEq] at hx
         subst hx
         exact (hcall.not_source).elim)

set_option linter.unusedSimpArgs false in
/--
**Inversion at a label.** A reduction out of code whose leading redex is a
label either takes place inside the label's body, or is one of the
store-independent label rules applied to that label alone, inside the
surrounding value prefix and tail.
-/
theorem Step.label_inv {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    {p : List Runtime.Value} {n : Nat} {cont : Expr} {body q : List Admin}
    (hcode : c.code = values p ++ .label n cont body :: q) :
    (∃ body', Step host ⟨c.store, c.frame, body⟩ ⟨c'.store, c'.frame, body'⟩ ∧
        c'.code = values p ++ .label n cont body' :: q) ∨
      (∃ after, PureStep [.label n cont body] after ∧ c.store = c'.store ∧
        c'.frame = c.frame ∧ c'.code = values p ++ after ++ q) := by
  induction h generalizing p q with
  | pure s f hp =>
    rename_i before after
    replace hcode : before = values p ++ .label n cont body :: q := hcode
    have hx : firstRedex before = some (.label n cont body) := by rw [hcode]; simp
    have hsingle := hp.eq_singleton_of_firstRedex hx (.label n cont body)
    rw [hcode] at hsingle
    obtain ⟨hp', -, hq'⟩ := values_cons_inj (ws' := []) (rest' := [])
      (x := AdminInstr.label n cont body)
      (y := AdminInstr.label n cont body) rfl rfl (by simpa [Execution.values] using hsingle)
    subst hp'
    subst hq'
    refine .inr ⟨after, ?_, rfl, rfl, by simp [Execution.values]⟩
    rw [hcode] at hp
    simpa [Execution.values] using hp
  | context hstep ws tl ih =>
    rename_i s s' f f' before after
    replace hcode : values ws ++ before ++ tl = values p ++ .label n cont body :: q := hcode
    have hne : firstRedex before ≠ none := hstep.firstRedex_ne_none
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
    have hxa : x = AdminInstr.label n cont body := by
      have h1 : firstRedex (values ws ++ before ++ tl) = some x := by simp [hx]
      rw [hcode] at h1
      simpa using h1.symm
    subst hxa
    obtain ⟨rest, tail₁, hbefore⟩ := firstRedex_eq_some hx
    have heq : values (ws ++ rest) ++ (AdminInstr.label n cont body) :: (tail₁ ++ tl) =
        values p ++ (AdminInstr.label n cont body) :: q := by
      rw [← hcode, hbefore, values_append]
      simp [List.append_assoc]
    obtain ⟨h1, -, h3⟩ := values_cons_inj rfl rfl heq
    subst h1
    subst h3
    rcases ih (show before = values rest ++ .label n cont body :: tail₁ from hbefore) with
      ⟨body', hinner, hafter⟩ | ⟨mid, hpure, hstore, hframe, hafter⟩
    · replace hafter : after = values rest ++ .label n cont body' :: tail₁ := hafter
      refine .inl ⟨body', hinner, ?_⟩
      show values ws ++ after ++ tl = _
      rw [hafter, values_append]
      simp [List.append_assoc]
    · replace hafter : after = values rest ++ mid ++ tail₁ := hafter
      refine .inr ⟨mid, hpure, hstore, hframe, ?_⟩
      show values ws ++ after ++ tl = _
      rw [hafter, values_append]
      simp [List.append_assoc]
  | label hstep n' cont' ih =>
    rename_i s s' f f' before after
    replace hcode : [AdminInstr.label n' cont' before] = values p ++ .label n cont body :: q :=
      hcode
    obtain ⟨hp', hlab, hq'⟩ := values_cons_inj (ws := []) (rest := [])
      (x := AdminInstr.label n' cont' before)
      (y := AdminInstr.label n cont body) rfl rfl (by simpa [Execution.values] using hcode)
    subst hp'
    obtain ⟨rfl, rfl, rfl⟩ : n' = n ∧ cont' = cont ∧ before = body := by
      injection hlab with h1 h2 h3
      exact ⟨h1, h2, h3⟩
    exact .inl ⟨after, hstep, by simp [Execution.values, ← hq']⟩
  | frame hstep n' outer ih =>
    rename_i s s' inner inner' before after
    replace hcode : [AdminInstr.frame n' inner before] = values p ++ .label n cont body :: q :=
      hcode
    exact absurd (congrArg firstRedex hcode) (by simp)
  | _ =>
    exfalso
    have hr := congrArg firstRedex (hcode : _ = values p ++ .label n cont body :: q)
    simp only [firstRedex_append, firstRedex_values, firstRedex_label_cons,
      Option.none_or, values_cons, values_nil, List.nil_append, List.cons_append,
      firstRedex_value_cons] at hr
    simp [firstRedex_cons, asValue?] at hr

set_option linter.unusedSimpArgs false in
/--
**Inversion at a frame.** A reduction out of code whose leading redex is an
activation frame either takes place inside that frame — at the frame's own
locals, leaving the enclosing frame untouched — or is one of the
store-independent frame rules applied to that frame alone.
-/
theorem Step.frame_inv {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    {p : List Runtime.Value} {n : Nat} {fr : Frame} {body q : List Admin}
    (hcode : c.code = values p ++ .frame n fr body :: q) :
    c'.frame = c.frame ∧
      ((∃ (fr' : Frame) (body' : List Admin),
          Step host ⟨c.store, fr, body⟩ ⟨c'.store, fr', body'⟩ ∧
          c'.code = values p ++ .frame n fr' body' :: q) ∨
        (∃ after, PureStep [.frame n fr body] after ∧ c.store = c'.store ∧
          c'.code = values p ++ after ++ q)) := by
  induction h generalizing p q with
  | pure s f hp =>
    rename_i before after
    replace hcode : before = values p ++ .frame n fr body :: q := hcode
    have hx : firstRedex before = some (.frame n fr body) := by rw [hcode]; simp
    have hsingle := hp.eq_singleton_of_firstRedex hx (.frame n fr body)
    rw [hcode] at hsingle
    obtain ⟨hp', -, hq'⟩ := values_cons_inj (ws' := []) (rest' := [])
      (x := AdminInstr.frame n fr body)
      (y := AdminInstr.frame n fr body) rfl rfl (by simpa [Execution.values] using hsingle)
    subst hp'
    subst hq'
    refine ⟨rfl, .inr ⟨after, ?_, rfl, by simp [Execution.values]⟩⟩
    rw [hcode] at hp
    simpa [Execution.values] using hp
  | context hstep ws tl ih =>
    rename_i s s' f f' before after
    replace hcode : values ws ++ before ++ tl = values p ++ .frame n fr body :: q := hcode
    have hne : firstRedex before ≠ none := hstep.firstRedex_ne_none
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
    have hxa : x = AdminInstr.frame n fr body := by
      have h1 : firstRedex (values ws ++ before ++ tl) = some x := by simp [hx]
      rw [hcode] at h1
      simpa using h1.symm
    subst hxa
    obtain ⟨rest, tail₁, hbefore⟩ := firstRedex_eq_some hx
    have heq : values (ws ++ rest) ++ (AdminInstr.frame n fr body) :: (tail₁ ++ tl) =
        values p ++ (AdminInstr.frame n fr body) :: q := by
      rw [← hcode, hbefore, values_append]
      simp [List.append_assoc]
    obtain ⟨h1, -, h3⟩ := values_cons_inj rfl rfl heq
    subst h1
    subst h3
    obtain ⟨hframe, hrest⟩ := ih (show before = values rest ++ .frame n fr body :: tail₁ from
      hbefore)
    refine ⟨hframe, ?_⟩
    rcases hrest with ⟨fr', body', hinner, hafter⟩ | ⟨mid, hpure, hstore, hafter⟩
    · replace hafter : after = values rest ++ .frame n fr' body' :: tail₁ := hafter
      refine .inl ⟨fr', body', hinner, ?_⟩
      show values ws ++ after ++ tl = _
      rw [hafter, values_append]
      simp [List.append_assoc]
    · replace hafter : after = values rest ++ mid ++ tail₁ := hafter
      refine .inr ⟨mid, hpure, hstore, ?_⟩
      show values ws ++ after ++ tl = _
      rw [hafter, values_append]
      simp [List.append_assoc]
  | label hstep n' cont ih =>
    rename_i s s' f f' before after
    replace hcode : [AdminInstr.label n' cont before] = values p ++ .frame n fr body :: q := hcode
    exact absurd (congrArg firstRedex hcode) (by simp)
  | frame hstep n' outer ih =>
    rename_i s s' inner inner' before after
    replace hcode : [AdminInstr.frame n' inner before] = values p ++ .frame n fr body :: q := hcode
    obtain ⟨hp', hfr, hq'⟩ := values_cons_inj (ws := []) (rest := [])
      (x := AdminInstr.frame n' inner before)
      (y := AdminInstr.frame n fr body) rfl rfl (by simpa [Execution.values] using hcode)
    subst hp'
    obtain ⟨rfl, rfl, rfl⟩ : n' = n ∧ inner = fr ∧ before = body := by
      injection hfr with h1 h2 h3
      exact ⟨h1, h2, h3⟩
    exact ⟨rfl, .inl ⟨inner', after, hstep, by simp [Execution.values, ← hq']⟩⟩
  | _ =>
    exfalso
    have hr := congrArg firstRedex (hcode : _ = values p ++ .frame n fr body :: q)
    simp only [firstRedex_append, firstRedex_values, firstRedex_frame_cons,
      Option.none_or, values_cons, values_nil, List.nil_append, List.cons_append,
      firstRedex_value_cons] at hr
    simp [firstRedex_cons, asValue?] at hr

/-! ## Inverting a step at an evaluation context -/

/-- An encoded value is a source constant, never a trap. -/
@[simp] theorem value_ne_trap (v : Runtime.Value) : value v ≠ .trap := by
  intro h
  have hv := asValue?_value v
  rw [h] at hv
  simp [asValue?] at hv

/-- An encoded value is a source constant, never an invocation. -/
@[simp] theorem value_ne_invoke (v : Runtime.Value) (a : FuncAddr) : value v ≠ .invoke a := by
  intro h
  have hv := asValue?_value v
  rw [h] at hv
  simp [asValue?] at hv

/-- An encoded value is a source constant, never a label. -/
@[simp] theorem value_ne_label (v : Runtime.Value) (n : Nat) (cont : Expr)
    (body : List Admin) : value v ≠ .label n cont body := by
  intro h
  have hv := asValue?_value v
  rw [h] at hv
  simp [asValue?] at hv

/-- An encoded value is a source constant, never a frame. -/
@[simp] theorem value_ne_frame (v : Runtime.Value) (n : Nat) (fr : Frame)
    (body : List Admin) : value v ≠ .frame n fr body := by
  intro h
  have hv := asValue?_value v
  rw [h] at hv
  simp [asValue?] at hv

/-- A value sequence has no call head. -/
theorem callHead_values_absurd {vs : List Runtime.Value} {y : Admin}
    (hy : firstRedex (values vs) = some y) : False := by simp at hy

/-- Code whose leading redex is a source instruction has no call head. -/
theorem callHead_source_absurd {l : List Admin} {i : Instr} {tail : List Admin}
    {vs : List Runtime.Value} (hi : asValue? (.source i) = none)
    (hl : l = values vs ++ .source i :: tail) {y : Admin}
    (hy : firstRedex l = some y) (hcall : CallHead y) : False := by
  rw [hl, firstRedex_append, firstRedex_values, Option.none_or, firstRedex_cons, hi] at hy
  cases hy
  exact hcall.not_source

/-- A trap is not a call head. -/
theorem callHead_trap_absurd {y : Admin} (hy : firstRedex [AdminInstr.trap] = some y)
    (hcall : CallHead y) : False := by
  rw [firstRedex_trap_cons] at hy
  cases hy
  exact hcall.not_trap

/-- A store-independent rule never acts on a label whose body is still parked
at a call: every label rule needs the body to be finished, branching or
trapped. -/
theorem PureStep.not_callHead_label {before after : List Admin} (h : PureStep before after)
    {n : Nat} {cont : Expr} {body : List Admin} (hb : before = [.label n cont body])
    {y : Admin} (hy : firstRedex body = some y) (hcall : CallHead y) : False := by
  cases h
  case labelDone n' cont' vs =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧ values vs = body := by simpa using hb
    exact callHead_values_absurd hy
  case labelBranch n' cont' extra vs tail arity =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧
        values extra ++ values vs ++ [AdminInstr.source (.br ⟨0⟩)] ++ tail = body := by
      simpa using hb
    exact callHead_source_absurd (i := .br ⟨0⟩) (vs := extra ++ vs) (tail := tail) rfl
      (by simp [values_append, List.append_assoc]) hy hcall
  case labelBranchOuter n' cont' vs tail l outer =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧
        values vs ++ [AdminInstr.source (.br l)] ++ tail = body := by simpa using hb
    exact callHead_source_absurd (i := .br l) (vs := vs) (tail := tail) rfl
      (by simp [List.append_assoc]) hy hcall
  case labelReturn n' cont' vs tail =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧
        values vs ++ [AdminInstr.source .return_] ++ tail = body := by simpa using hb
    exact callHead_source_absurd (i := .return_) (vs := vs) (tail := tail) rfl
      (by simp [List.append_assoc]) hy hcall
  case labelTrap n' cont' =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ cont' = cont ∧ [AdminInstr.trap] = body := by simpa using hb
    exact callHead_trap_absurd hy hcall
  all_goals simp [Execution.values] at hb

/-- A store-independent rule never acts on a frame whose body is still parked
at a call. -/
theorem PureStep.not_callHead_frame {before after : List Admin} (h : PureStep before after)
    {n : Nat} {fr : Frame} {body : List Admin} (hb : before = [.frame n fr body])
    {y : Admin} (hy : firstRedex body = some y) (hcall : CallHead y) : False := by
  cases h
  case frameDone n' fr' vs arity =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ fr' = fr ∧ values vs = body := by simpa using hb
    exact callHead_values_absurd hy
  case frameReturn n' fr' extra vs tail arity =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ fr' = fr ∧
        values extra ++ values vs ++ [AdminInstr.source .return_] ++ tail = body := by
      simpa using hb
    exact callHead_source_absurd (i := .return_) (vs := extra ++ vs) (tail := tail) rfl
      (by simp [values_append, List.append_assoc]) hy hcall
  case frameTrap n' fr' =>
    obtain ⟨-, -, rfl⟩ : n' = n ∧ fr' = fr ∧ [AdminInstr.trap] = body := by simpa using hb
    exact callHead_trap_absurd hy hcall
  all_goals simp [Execution.values] at hb

/-! ### Plugging -/

/-- `EvalCtx.plug` at the hole. -/
theorem plug_hole (code : List Admin) :
    (EvalCtx.hole : EvalCtx Instr).plug value code = code := rfl

/-- `EvalCtx.plug` at a value prefix and tail. -/
theorem plug_seq (ws : List Runtime.Value) (K : EvalCtx Instr) (tl code : List Admin) :
    (EvalCtx.seq ws K tl).plug value code = values ws ++ K.plug value code ++ tl := rfl

/-- `EvalCtx.plug` under a label. -/
theorem plug_label (n : Nat) (cont : Expr) (K : EvalCtx Instr) (code : List Admin) :
    (EvalCtx.label n cont K).plug value code = [.label n cont (K.plug value code)] := rfl

/-- `EvalCtx.plug` under a frame. -/
theorem plug_frame (n : Nat) (fr : Frame) (K : EvalCtx Instr) (code : List Admin) :
    (EvalCtx.frame n fr K).plug value code = [.frame n fr (K.plug value code)] := rfl

/-- The leading redex of rigid code is a call head. -/
theorem Rigid.callHead {s : Store H} {X : List Admin} (h : Rigid s X) :
    ∃ y, firstRedex X = some y ∧ CallHead y := by
  cases h with
  | @invoke args a h => exact ⟨.invoke a, by simp, .invoke a⟩
  | frame n fr body => exact ⟨.frame n fr body, by simp, .frame n fr body⟩

/-- The leading redex of rigid code in a context is a call head: no enclosing
value prefix, label or frame can consume it. -/
theorem Rigid.plug_callHead {s : Store H} {X : List Admin} (h : Rigid s X)
    (K : EvalCtx Instr) : ∃ y, firstRedex (K.plug value X) = some y ∧ CallHead y := by
  induction K with
  | hole => exact h.callHead
  | seq ws K₀ tl ih =>
    obtain ⟨y, hy, hcall⟩ := ih
    exact ⟨y, by rw [plug_seq, firstRedex_append, firstRedex_append, firstRedex_values,
      Option.none_or, hy, Option.some_or], hcall⟩
  | label n cont K₀ ih =>
    exact ⟨.label n cont (K₀.plug value X), by rw [plug_label]; simp, .label _ _ _⟩
  | frame n fr K₀ ih =>
    exact ⟨.frame n fr (K₀.plug value X), by rw [plug_frame]; simp, .frame _ _ _⟩

/--
**Inversion at an evaluation context.** A reduction out of rigid code plugged
into any evaluation context takes place at the hole: the context is untouched,
the enclosing frame is untouched, and the step at the hole is available at
every frame.

This is the decomposition the replacement congruence needs — "a run from
`E[values args ++ [.invoke a]]` either never enters `a`, or reaches a
configuration where `a`'s body is active" — and it is what V1 was missing.
-/
theorem Rigid.plug_inv {host : HostSemantics H} {s : Store H} {X : List Admin}
    (hrig : Rigid s X) (K : EvalCtx Instr) :
    ∀ (p : List Runtime.Value) (q : List Admin) (f f' : Frame) (s' : Store H)
      (code' : List Admin),
      Step host ⟨s, f, values p ++ K.plug value X ++ q⟩ ⟨s', f', code'⟩ →
        f' = f ∧ ∃ X', (∀ g : Frame, Step host ⟨s, g, X⟩ ⟨s', g, X'⟩) ∧
          code' = values p ++ K.plug value X' ++ q := by
  induction K with
  | hole =>
    intro p q f f' s' code' hstep
    rw [plug_hole] at hstep
    cases hrig with
    | invoke hsat =>
      rename_i args a
      obtain ⟨fi, hfound, hlen⟩ := hsat
      have hcode : (⟨s, f, values p ++ (values args ++ [AdminInstr.invoke a]) ++ q⟩ :
          Config H).code = values (p ++ args) ++ .invoke a :: q := by
        simp [values_append, List.append_assoc]
      obtain ⟨hframe, pre, args', X', hsplit, hsat', hpoly, -, hafter⟩ :=
        hstep.invoke_inv hcode
      obtain ⟨fi', hfound', hlen'⟩ := hsat'
      rw [hfound] at hfound'
      cases hfound'
      have hlenargs : args'.length = args.length := by rw [hlen', hlen]
      obtain ⟨rfl, rfl⟩ := List.append_inj' hsplit hlenargs.symm
      exact ⟨hframe, X', hpoly, by
        simpa [values_append, List.append_assoc, plug_hole] using hafter⟩
    | frame n fr body =>
      have hcode : (⟨s, f, values p ++ [AdminInstr.frame n fr body] ++ q⟩ : Config H).code =
          values p ++ .frame n fr body :: q := by simp
      obtain ⟨hframe, hcases⟩ := hstep.frame_inv hcode
      rcases hcases with ⟨fr', body', hinner, hafter⟩ | ⟨after, hpure, hstore, hafter⟩
      · exact ⟨hframe, [.frame n fr' body'], fun g => .frame hinner n g, by
          simpa [plug_hole] using hafter⟩
      · replace hstore : s = s' := hstore
        subst hstore
        exact ⟨hframe, after, fun g => Step.pure s g hpure, by simpa [plug_hole] using hafter⟩
  | seq ws K₀ tl ih =>
    intro p q f f' s' code' hstep
    rw [plug_seq] at hstep
    have hstep' : Step host ⟨s, f, values (p ++ ws) ++ K₀.plug value X ++ (tl ++ q)⟩
        ⟨s', f', code'⟩ := by
      simpa only [values_append, List.append_assoc] using hstep
    obtain ⟨hframe, X', hpoly, hafter⟩ := ih (p ++ ws) (tl ++ q) f f' s' code' hstep'
    refine ⟨hframe, X', hpoly, ?_⟩
    rw [hafter, plug_seq]
    simp [values_append, List.append_assoc]
  | label n cont K₀ ih =>
    intro p q f f' s' code' hstep
    rw [plug_label] at hstep
    have hcode : (⟨s, f, values p ++ [AdminInstr.label n cont (K₀.plug value X)] ++ q⟩ :
        Config H).code = values p ++ .label n cont (K₀.plug value X) :: q := by simp
    rcases hstep.label_inv hcode with ⟨body', hinner, hafter⟩ | ⟨after, hpure, -, -, -⟩
    · have hinner' : Step host ⟨s, f, values [] ++ K₀.plug value X ++ []⟩ ⟨s', f', body'⟩ := by
        rw [List.append_nil]
        exact hinner
      obtain ⟨hframe, X', hpoly, hbody⟩ := ih [] [] f f' s' body' hinner'
      replace hafter : code' = values p ++ AdminInstr.label n cont body' :: q := hafter
      refine ⟨hframe, X', hpoly, ?_⟩
      rw [hafter, plug_label, hbody]
      simp [Execution.values]
    · obtain ⟨y, hy, hcall⟩ := hrig.plug_callHead K₀
      exact (hpure.not_callHead_label rfl hy hcall).elim
  | frame n fr K₀ ih =>
    intro p q f f' s' code' hstep
    rw [plug_frame] at hstep
    have hcode : (⟨s, f, values p ++ [AdminInstr.frame n fr (K₀.plug value X)] ++ q⟩ :
        Config H).code = values p ++ .frame n fr (K₀.plug value X) :: q := by simp
    obtain ⟨hframe, hcases⟩ := hstep.frame_inv hcode
    rcases hcases with ⟨fr', body', hinner, hafter⟩ | ⟨after, hpure, -, -⟩
    · have hinner' : Step host ⟨s, fr, values [] ++ K₀.plug value X ++ []⟩ ⟨s', fr', body'⟩ := by
        rw [List.append_nil]
        exact hinner
      obtain ⟨hfr, X', hpoly, hbody⟩ := ih [] [] fr fr' s' body' hinner'
      replace hafter : code' = values p ++ AdminInstr.frame n fr' body' :: q := hafter
      subst hfr
      refine ⟨hframe, X', hpoly, ?_⟩
      rw [hafter, plug_frame, hbody]
      simp [Execution.values]
    · obtain ⟨y, hy, hcall⟩ := hrig.plug_callHead K₀
      exact (hpure.not_callHead_frame rfl hy hcall).elim

/-! ## The call-boundary decomposition

With `Rigid.plug_inv` the decomposition of a run at a call boundary can finally
be stated and proved: a run out of `E[values args ++ [.invoke a]]` either stays
inside the invocation forever, or reaches the invocation's result and continues
from `E[result r]`.
-/

/-- A store-independent rule out of a lone activation frame produces a
result. -/
theorem PureStep.frame_result {before after : List Admin} (h : PureStep before after)
    {n : Nat} {fr : Frame} {body : List Admin} (hb : before = [.frame n fr body]) :
    ∃ r : Runtime.Result, after = result r := by
  cases h
  case frameDone n' fr' vs arity => exact ⟨.values vs, rfl⟩
  case frameReturn n' fr' extra vs tail arity => exact ⟨.values vs, rfl⟩
  case frameTrap n' fr' => exact ⟨.trap, rfl⟩
  all_goals simp [Execution.values] at hb

/-- **Rigid code stays rigid until it produces a result.** -/
theorem Rigid.step_classify {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {X X' : List Admin} (hrig : Rigid s X) (h : Step host ⟨s, f, X⟩ ⟨s', f', X'⟩) :
    Rigid s' X' ∨ ∃ r : Runtime.Result, X' = result r := by
  cases hrig with
  | @invoke args a hsat =>
    obtain ⟨-, pre, args', X'', hsplit, hsat', -, hshape, hafter⟩ :=
      h.invoke_inv (show (⟨s, f, values args ++ [AdminInstr.invoke a]⟩ : Config H).code =
        values args ++ .invoke a :: [] from rfl)
    obtain ⟨fi, hfound, hlen⟩ := hsat
    obtain ⟨fi', hfound', hlen'⟩ := hsat'
    rw [hfound] at hfound'
    cases hfound'
    have hlenargs : args'.length = args.length := by rw [hlen', hlen]
    have hpre : pre = [] := by
      have hl := congrArg List.length hsplit
      simp only [List.length_append, hlenargs] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hpre
    rw [List.nil_append] at hsplit
    subst hsplit
    replace hafter : X' = X'' := by simpa [Execution.values] using hafter
    subst hafter
    exact hshape
  | frame n fr body =>
    obtain ⟨-, hcases⟩ := h.frame_inv
      (show (⟨s, f, [AdminInstr.frame n fr body]⟩ : Config H).code =
        values [] ++ .frame n fr body :: [] by simp [Execution.values])
    rcases hcases with ⟨fr', body', -, hafter⟩ | ⟨after, hpure, -, hafter⟩
    · replace hafter : X' = [AdminInstr.frame n fr' body'] := by
        simpa [Execution.values] using hafter
      exact .inl (hafter ▸ .frame n fr' body')
    · replace hafter : X' = after := by simpa [Execution.values] using hafter
      subst hafter
      exact .inr (hpure.frame_result rfl)

/-- Rigid code in a context is never a result: the invocation is still
pending. -/
theorem Rigid.plug_ne_result {s : Store H} {X : List Admin} (hrig : Rigid s X)
    (K : EvalCtx Instr) (r : Runtime.Result) : K.plug value X ≠ result r := by
  intro heq
  obtain ⟨y, hy, hcall⟩ := hrig.plug_callHead K
  rw [heq] at hy
  cases r with
  | values vs => exact callHead_values_absurd hy
  | trap => exact callHead_trap_absurd hy hcall

/--
**The call-boundary decomposition, finite half.** A run out of rigid code in an
evaluation context that reaches a result must leave the hole: it factors as a
run of the hole to a result — available at *every* frame — followed by a run of
the context filled with that result.
-/
theorem Rigid.steps_factor {host : HostSemantics H} (K : EvalCtx Instr) (f : Frame)
    {c d : Config H} (h : Steps host c d) :
    ∀ (s : Store H) (X : List Admin), c = ⟨s, f, K.plug value X⟩ → Rigid s X →
      (∃ r : Runtime.Result, d.code = result r) →
      ∃ (s₂ : Store H) (r' : Runtime.Result),
        (∀ g : Frame, Steps host ⟨s, g, X⟩ ⟨s₂, g, result r'⟩) ∧
        Steps host ⟨s₂, f, K.plug value (result r')⟩ d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rintro s X rfl hrig ⟨r, hr⟩
    exact absurd hr (hrig.plug_ne_result K r)
  | head hstep hrest ih =>
    rename_i e e'
    rintro s X rfl hrig hfin
    obtain ⟨-, X', hpoly, hcode⟩ := hrig.plug_inv K [] [] f e'.frame e'.store e'.code
      (by simpa [Execution.values] using hstep)
    have hframe : e'.frame = f := (hrig.plug_inv K [] [] f e'.frame e'.store e'.code
      (by simpa [Execution.values] using hstep)).1
    replace hcode : e'.code = K.plug value X' := by
      simpa [Execution.values] using hcode
    rcases hrig.step_classify (hpoly f) with hrig' | ⟨r', rfl⟩
    · obtain ⟨s₂, r'', hsub, hrest'⟩ := ih e'.store X' (by
        rw [← hframe, ← hcode]) hrig' hfin
      exact ⟨s₂, r'', fun g => (hpoly g).steps.trans (hsub g), hrest'⟩
    · refine ⟨e'.store, r', fun g => (hpoly g).steps, ?_⟩
      have : (⟨e'.store, f, K.plug value (result r')⟩ : Config H) = e' := by
        rw [← hframe, ← hcode]
      rw [this]
      exact hrest

/--
**The call-boundary decomposition, infinite half.** An infinite run out of
rigid code in an evaluation context either stays inside the hole forever, or
reaches the hole's result in finitely many steps and diverges afterwards.
-/
theorem Rigid.diverges_factor {host : HostSemantics H} {s : Store H} {X : List Admin}
    (hrig : Rigid s X) (K : EvalCtx Instr) (f : Frame)
    (h : Diverges host ⟨s, f, K.plug value X⟩) :
    (∀ g : Frame, Diverges host ⟨s, g, X⟩) ∨
      ∃ (s₂ : Store H) (r : Runtime.Result),
        (∀ g : Frame, Steps host ⟨s, g, X⟩ ⟨s₂, g, result r⟩) ∧
        Diverges host ⟨s₂, f, K.plug value (result r)⟩ := by
  classical
  by_cases exited : ∃ (s₂ : Store H) (r : Runtime.Result),
      (∀ g : Frame, Steps host ⟨s, g, X⟩ ⟨s₂, g, result r⟩) ∧
      Diverges host ⟨s₂, f, K.plug value (result r)⟩
  · exact .inr exited
  refine .inl fun g => ?_
  refine InfiniteTrace.coinduct
    (fun e => ∃ (σ : Store H) (Y : List Admin), e = ⟨σ, g, Y⟩ ∧ Rigid σ Y ∧
      (∀ k : Frame, Steps host ⟨s, k, X⟩ ⟨σ, k, Y⟩) ∧
      Diverges host ⟨σ, f, K.plug value Y⟩) ?_ ⟨s, X, rfl, hrig, fun _ => .refl, h⟩
  rintro e ⟨σ, Y, rfl, hrigY, hreach, hdiv⟩
  obtain ⟨e', hstep, htail⟩ := hdiv.unfold
  obtain ⟨hframe, Y', hpoly, hcode⟩ := hrigY.plug_inv K [] [] f e'.frame e'.store e'.code
    (by simpa [Execution.values] using hstep)
  replace hcode : e'.code = K.plug value Y' := by simpa [Execution.values] using hcode
  have hrebuild : (⟨e'.store, f, K.plug value Y'⟩ : Config H) = e' := by rw [← hframe, ← hcode]
  rcases hrigY.step_classify (hpoly f) with hrig' | ⟨r, rfl⟩
  · exact ⟨⟨e'.store, g, Y'⟩, hpoly g, e'.store, Y', rfl, hrig',
      fun k => (hreach k).tail (hpoly k), by rw [hrebuild]; exact htail⟩
  · exact absurd ⟨e'.store, r, fun k => (hreach k).tail (hpoly k),
      by rw [hrebuild]; exact htail⟩ exited

end Silmaril.Wasm.V1.Execution
