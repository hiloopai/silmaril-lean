module

public import Silmaril.Wasm.V1.Execution.Inversion
public import Silmaril.Wasm.SpecTec.Sim10.Whole.Defs

/-!
# A reachability invariant of V1 code: plain instructions after the redex

The 1.0 script types the suffix after a `br`, `return` or `trap` redex as `instr*`, while V1
allows any administrative suffix. `Plain10 code` says that the code after the first non-value
of `code` is plain instructions, recursively in label and frame bodies:

* `Plain10` is an inductive predicate, one constructor per kind of first non-value (a source
  instruction, `trap`, a pending invocation, a label, a frame);
* `Plain10.split`: in `values ws ++ x :: rest` with `x` not a value, `rest` is plain and the
  body of `x` (if a label or frame) is `Plain10`;
* **`plain10_step`**: every V1 step preserves `Plain10`. Every `PureStep` produces `Plain10` code
  outright; `context` needs that the inner code has a redex (`Step.firstRedex_ne_none`);
* `plain10_steps`: so does every run, and `plain10_invoke`: the initial code `values args ++
  [.invoke a]` of an invocation is `Plain10`. So every configuration reached from an invocation
  satisfies the invariant.

`GSetOk` (round 2's invariant for `global.set`) passes to the inner code of V1's `context`,
`label` and `frame` (`gsetOk_mid`, `gsetOk_label`, `gsetOk_frame`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps PureStep value values
  expression result asValue? asValue?_value firstRedex firstRedex_eq_some values_cons_inj)
open Silmaril.Wasm.Execution.Runtime (Frame FuncAddr)

variable {H : Type}

/-! ## The invariant -/

/-- **Plain instructions after the first non-value**, recursively in label and frame bodies. -/
inductive Plain10 : List Admin → Prop where
  | plain (is : List V1.Instr) : Plain10 (is.map .source)
  | trap (vs : List Execution.Runtime.Value) (is : List V1.Instr) :
      Plain10 (values vs ++ .trap :: is.map .source)
  | invoke (vs : List Execution.Runtime.Value) (a : FuncAddr) (is : List V1.Instr) :
      Plain10 (values vs ++ .invoke a :: is.map .source)
  | label (vs : List Execution.Runtime.Value) (n : Nat) (cont : V1.Expr) (body : List Admin)
      (is : List V1.Instr) (hb : Plain10 body) :
      Plain10 (values vs ++ .label n cont body :: is.map .source)
  | frame (vs : List Execution.Runtime.Value) (n : Nat) (fr : Frame) (body : List Admin)
      (is : List V1.Instr) (hb : Plain10 body) :
      Plain10 (values vs ++ .frame n fr body :: is.map .source)

/-- The bodies of a label or frame head are `Plain10`. -/
def PlainHead10 (x : Admin) : Prop :=
  (∀ n cont body, x = .label n cont body → Plain10 body) ∧
    ∀ n fr body, x = .frame n fr body → Plain10 body

/-- An instruction other than a label or frame is a `PlainHead10`. -/
theorem plainHead10_of {x : Admin} (hl : ∀ n cont body, x ≠ .label n cont body)
    (hf : ∀ n fr body, x ≠ .frame n fr body) : PlainHead10 x :=
  ⟨fun n cont body h => absurd h (hl n cont body), fun n fr body h => absurd h (hf n fr body)⟩

/-- A value is a source instruction. -/
theorem value_source (v : Execution.Runtime.Value) : ∃ i, value v = .source i := by
  rcases v with ⟨t | t, b⟩ <;> exact ⟨_, rfl⟩

/-- Values are source instructions. -/
theorem values_source (vs : List Execution.Runtime.Value) :
    ∃ is : List V1.Instr, values vs = is.map .source := by
  induction vs with
  | nil => exact ⟨[], rfl⟩
  | cons v vs ih =>
    obtain ⟨i, hi⟩ := value_source v
    obtain ⟨is, his⟩ := ih
    exact ⟨i :: is, by rw [V1.Execution.values_cons, hi, his]; rfl⟩

/-- Sources after values are sources. -/
theorem values_append_sources (vs : List Execution.Runtime.Value) (is : List V1.Instr) :
    ∃ js : List V1.Instr, values vs ++ is.map .source = js.map .source := by
  obtain ⟨ks, hks⟩ := values_source vs
  exact ⟨ks ++ is, by rw [hks, List.map_append]⟩

/-- Values are `Plain10`. -/
theorem plain10_values (vs : List Execution.Runtime.Value) : Plain10 (values vs) := by
  obtain ⟨is, his⟩ := values_source vs
  exact his ▸ .plain is

/-- `[trap]` is `Plain10`. -/
theorem plain10_trap1 : Plain10 [.trap] := .trap [] []

/-- A result is `Plain10`. -/
theorem plain10_result (r : Execution.Runtime.Result) : Plain10 (result r) := by
  cases r with
  | values vs => exact plain10_values vs
  | trap => exact plain10_trap1

/-- **Building `Plain10`** from a first non-value with plain bodies and a plain suffix. -/
theorem plain10_build (vs : List Execution.Runtime.Value) {x : Admin} (hx : PlainHead10 x)
    (is : List V1.Instr) : Plain10 (values vs ++ x :: is.map .source) := by
  cases x with
  | source i =>
    obtain ⟨js, hjs⟩ := values_append_sources vs (i :: is)
    exact hjs ▸ .plain js
  | trap => exact .trap vs is
  | invoke a => exact .invoke vs a is
  | label n cont body => exact .label vs n cont body is (hx.1 n cont body rfl)
  | frame n fr body => exact .frame vs n fr body is (hx.2 n fr body rfl)

/-- `Plain10` code with values in front and plain instructions behind. -/
theorem plain10_wrap {l : List Admin} (h : Plain10 l) (vs : List Execution.Runtime.Value)
    (is : List V1.Instr) : Plain10 (values vs ++ l ++ is.map .source) := by
  cases h with
  | plain js =>
    obtain ⟨ks, hks⟩ := values_append_sources vs (js ++ is)
    rw [List.append_assoc, ← List.map_append]
    exact hks ▸ .plain ks
  | trap ws js =>
    have e : values vs ++ (values ws ++ .trap :: js.map .source) ++ is.map .source =
        values (vs ++ ws) ++ .trap :: (js ++ is).map .source := by simp
    exact e ▸ .trap _ _
  | invoke ws a js =>
    have e : values vs ++ (values ws ++ .invoke a :: js.map .source) ++ is.map .source =
        values (vs ++ ws) ++ .invoke a :: (js ++ is).map .source := by simp
    exact e ▸ .invoke _ _ _
  | label ws n cont body js hb =>
    have e : values vs ++ (values ws ++ .label n cont body :: js.map .source) ++ is.map .source =
        values (vs ++ ws) ++ .label n cont body :: (js ++ is).map .source := by simp
    exact e ▸ .label _ _ _ _ _ hb
  | frame ws n fr body js hb =>
    have e : values vs ++ (values ws ++ .frame n fr body :: js.map .source) ++ is.map .source =
        values (vs ++ ws) ++ .frame n fr body :: (js ++ is).map .source := by simp
    exact e ▸ .frame _ _ _ _ _ hb

/-! ## Reading the invariant -/

@[simp] theorem asValue?_trap : asValue? (.trap : Admin) = none := rfl
@[simp] theorem asValue?_invoke (a : FuncAddr) : asValue? (.invoke a : Admin) = none := rfl
@[simp] theorem asValue?_label (n : Nat) (cont : V1.Expr) (body : List Admin) :
    asValue? (.label n cont body : Admin) = none := rfl
@[simp] theorem asValue?_frame (n : Nat) (fr : Frame) (body : List Admin) :
    asValue? (.frame n fr body : Admin) = none := rfl

/-- A suffix of a sequence of sources after a split is a sequence of sources. -/
theorem sources_split {is : List V1.Instr} {l : List Admin} {x : Admin} {rest : List Admin}
    (h : l ++ x :: rest = is.map .source) :
    (∃ i, x = .source i) ∧ ∃ js : List V1.Instr, rest = js.map .source := by
  obtain ⟨is₁, is₂, -, -, h₂⟩ := List.map_eq_append_iff.1 h.symm
  obtain ⟨i, js, -, hi, hjs⟩ := List.map_eq_cons_iff.1 h₂
  exact ⟨⟨i, hi.symm⟩, js, hjs.symm⟩

/-- Two splits at a non-value agree, so the first inherits the second's plain suffix and head. -/
theorem split_of_eq {ws vs : List Execution.Runtime.Value} {x y : Admin} {rest : List Admin}
    {is : List V1.Instr} (hx : asValue? x = none) (hy : asValue? y = none)
    (hc : values ws ++ x :: rest = values vs ++ y :: is.map .source) (hh : PlainHead10 y) :
    (∃ js : List V1.Instr, rest = js.map .source) ∧ PlainHead10 x := by
  obtain ⟨-, hxy, hr⟩ : ws = vs ∧ x = y ∧ rest = is.map .source := values_cons_inj hx hy hc
  exact ⟨⟨is, hr⟩, hxy ▸ hh⟩

/-- A label head with a `Plain10` body. -/
theorem plainHead10_label {n : Nat} {cont : V1.Expr} {body : List Admin} (hb : Plain10 body) :
    PlainHead10 (.label n cont body) :=
  ⟨fun _ _ _ h => (by cases h; exact hb), fun _ _ _ h => (by cases h)⟩

/-- A frame head with a `Plain10` body. -/
theorem plainHead10_frame {n : Nat} {fr : Frame} {body : List Admin} (hb : Plain10 body) :
    PlainHead10 (.frame n fr body) :=
  ⟨fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h; exact hb)⟩

/-- **`Plain10`, read at its first non-value**: what follows is plain, and the head's bodies are
`Plain10`. -/
theorem Plain10.split {ws : List Execution.Runtime.Value} {x : Admin} {rest : List Admin}
    (h : Plain10 (values ws ++ x :: rest)) (hx : asValue? x = none) :
    (∃ is : List V1.Instr, rest = is.map .source) ∧ PlainHead10 x := by
  generalize hc : values ws ++ x :: rest = code at h
  cases h with
  | plain is =>
    obtain ⟨⟨i, hi⟩, hr⟩ := sources_split hc
    exact ⟨hr, hi ▸ plainHead10_of (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)⟩
  | trap vs is =>
    exact split_of_eq hx rfl hc (plainHead10_of (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
  | invoke vs a is =>
    exact split_of_eq hx rfl hc (plainHead10_of (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
  | label vs n cont body is hb => exact split_of_eq hx rfl hc (plainHead10_label hb)
  | frame vs n fr body is hb => exact split_of_eq hx rfl hc (plainHead10_frame hb)

/-- The first redex is not a value. -/
theorem asValue?_of_firstRedex {l : List Admin} {x : Admin} (h : firstRedex l = some x) :
    asValue? x = none := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rw [V1.Execution.firstRedex_cons] at h
    cases hy : asValue? y with
    | none =>
      rw [hy] at h
      cases h
      exact hy
    | some v =>
      rw [hy] at h
      exact ih h

/-- **The inner code of V1's `context`**: if the middle has a redex, it is `Plain10` and the
suffix is plain. -/
theorem Plain10.mid {vs : List Execution.Runtime.Value} {before tail : List Admin}
    (h : Plain10 (values vs ++ before ++ tail)) (hr : firstRedex before ≠ none) :
    Plain10 before ∧ ∃ is : List V1.Instr, tail = is.map .source := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hr
  obtain ⟨ws, r, rfl⟩ := firstRedex_eq_some hx
  have hv := asValue?_of_firstRedex hx
  have e : values vs ++ (values ws ++ x :: r) ++ tail = values (vs ++ ws) ++ x :: (r ++ tail) := by
    simp
  obtain ⟨⟨is, his⟩, hhead⟩ := (e ▸ h).split hv
  obtain ⟨is₁, is₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 his.symm
  exact ⟨h₁ ▸ plain10_build ws hhead is₁, is₂, h₂.symm⟩

/-- A one-element label code: its body is `Plain10`. -/
theorem Plain10.label_body {n : Nat} {cont : V1.Expr} {body : List Admin}
    (h : Plain10 [.label n cont body]) : Plain10 body :=
  ((show [(.label n cont body : Admin)] = values [] ++ (.label n cont body : Admin) :: [] from rfl) ▸ h).split
    rfl |>.2.1 n cont body rfl

/-- A one-element frame code: its body is `Plain10`. -/
theorem Plain10.frame_body {n : Nat} {fr : Frame} {body : List Admin}
    (h : Plain10 [.frame n fr body]) : Plain10 body :=
  ((show [(.frame n fr body : Admin)] = values [] ++ (.frame n fr body : Admin) :: [] from rfl) ▸ h).split
    rfl |>.2.2 n fr body rfl

/-! ## Preservation -/

/-- One label around `Plain10` code. -/
theorem plain10_label1 (n : Nat) (cont : V1.Expr) {body : List Admin} (hb : Plain10 body) :
    Plain10 [.label n cont body] := .label [] n cont body [] hb

/-- One frame around `Plain10` code. -/
theorem plain10_frame1 (n : Nat) (fr : Frame) {body : List Admin} (hb : Plain10 body) :
    Plain10 [.frame n fr body] := .frame [] n fr body [] hb

/-- Values followed by sources are `Plain10`. -/
theorem plain10_vals_sources (vs : List Execution.Runtime.Value) (is : List V1.Instr) :
    Plain10 (values vs ++ is.map .source) := by
  obtain ⟨js, hjs⟩ := values_append_sources vs is
  exact hjs ▸ .plain js

/-- **Every pure step produces `Plain10` code.** -/
theorem plain10_pureStep {before after : List Admin} (h : PureStep before after) :
    Plain10 after := by
  cases h with
  | nop => exact .plain []
  | unreachable => exact plain10_trap1
  | drop => exact .plain []
  | selectZero a b _ => exact plain10_values [b]
  | selectNonzero a b _ c _ => exact plain10_values [a]
  | block bt body => exact plain10_label1 _ _ (.plain body)
  | loop bt body => exact plain10_label1 _ _ (.plain body)
  | ifZero bt l r => exact .plain [_]
  | ifNonzero bt l r c _ => exact .plain [_]
  | brIfZero => exact .plain []
  | brIfNonzero => exact .plain [_]
  | brTable => exact .plain [_]
  | labelDone n cont vs => exact plain10_values vs
  | labelBranch n cont extra vs tail _ => exact plain10_vals_sources vs cont
  | labelBranchOuter n cont vs tail l _ => exact plain10_vals_sources vs [_]
  | labelReturn n cont vs tail => exact plain10_vals_sources vs [_]
  | frameDone n f vs _ => exact plain10_values vs
  | frameReturn n f extra vs tail _ => exact plain10_values vs
  | trapValues => exact plain10_trap1
  | trapTail => exact plain10_trap1
  | labelTrap => exact plain10_trap1
  | frameTrap => exact plain10_trap1
  | localTee i v => exact plain10_vals_sources [v, v] [_]
  | intUnary => exact plain10_values [_]
  | intBinary => exact plain10_values [_]
  | intBinaryTrap => exact plain10_trap1
  | intTest => exact plain10_values [_]
  | intRel => exact plain10_values [_]
  | floatUnary => exact plain10_values [_]
  | floatBinary => exact plain10_values [_]
  | floatRel => exact plain10_values [_]
  | convert => exact plain10_values [_]
  | convertTrap => exact plain10_trap1

/-- `Plain10` through V1's `context`, given it for the inner step. -/
theorem plain10_context {vs : List Execution.Runtime.Value} {before after tail : List Admin}
    (hp : Plain10 (values vs ++ before ++ tail)) (hr : firstRedex before ≠ none)
    (ih : Plain10 before → Plain10 after) : Plain10 (values vs ++ after ++ tail) := by
  obtain ⟨hb, is, his⟩ : Plain10 before ∧ ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.mid hp hr
  rw [his]
  exact plain10_wrap (ih hb) vs is

/-- **Every V1 step preserves `Plain10`.** -/
theorem plain10_step {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hp : Plain10 c.code) : Plain10 c'.code := by
  induction h with
  | pure s f hs => exact plain10_pureStep hs
  | context hs vs tail ih => exact plain10_context hp hs.firstRedex_ne_none ih
  | label _ n cont ih => exact plain10_label1 n cont (ih hp.label_body)
  | frame _ n outer ih => exact plain10_frame1 n _ (ih hp.frame_body)
  | localGet => exact plain10_values [_]
  | localSet => exact .plain []
  | globalGet => exact plain10_values [_]
  | globalSet => exact .plain []
  | call => exact .invoke [] _ []
  | callIndirect => exact .invoke [] _ []
  | callIndirectBounds => exact plain10_trap1
  | callIndirectNull => exact plain10_trap1
  | callIndirectType => exact plain10_trap1
  | invokeWasm => exact plain10_frame1 _ _ (plain10_label1 _ _ (.plain _))
  | invokeHost => exact plain10_result _
  | invokeHostDiverges => exact hp
  | intLoad => exact plain10_values [_]
  | intLoadTrap => exact plain10_trap1
  | floatLoad => exact plain10_values [_]
  | floatLoadTrap => exact plain10_trap1
  | intStore => exact .plain []
  | intStoreTrap => exact plain10_trap1
  | floatStore => exact .plain []
  | floatStoreTrap => exact plain10_trap1
  | memorySize => exact plain10_values [_]
  | memoryGrow => exact plain10_values [_]

/-- **Every V1 run preserves `Plain10`.** -/
theorem plain10_steps {host : HostSemantics H} {c c' : Config H} (h : Steps host c c')
    (hp : Plain10 c.code) : Plain10 c'.code := by
  induction h with
  | refl => exact hp
  | tail _ h₂ ih => exact plain10_step h₂ ih

/-- **The code of an invocation is `Plain10`**, so every configuration it reaches is. -/
theorem plain10_invoke (args : List Execution.Runtime.Value) (a : FuncAddr) :
    Plain10 (values args ++ [.invoke a]) := .invoke args a []

/-! ## `GSetOk` passes inwards -/

open Silmaril.Wasm.SpecTec.Sim10 (GSetOk ActiveF)

/-- `ActiveF` in a piece is `ActiveF` in the whole. -/
theorem activeF_mid {f f' : Frame} {l₁ l l₂ w : List Admin} (h : ActiveF f l f' w) :
    ActiveF f (l₁ ++ l ++ l₂) f' w := by
  cases h with
  | piece =>
    rename_i a b
    have e : l₁ ++ (a ++ w ++ b) ++ l₂ = (l₁ ++ a) ++ w ++ (b ++ l₂) := by simp
    exact e ▸ .piece
  | label hm ha => exact .label (List.mem_append_left _ (List.mem_append_right _ hm)) ha
  | frame hm ha => exact .frame (List.mem_append_left _ (List.mem_append_right _ hm)) ha

/-- `GSetOk` passes to a piece. -/
theorem gsetOk_mid {s : Store H} {f : Frame} {l₁ l l₂ : List Admin}
    (h : GSetOk s f (l₁ ++ l ++ l₂)) : GSetOk s f l :=
  fun f' v x a g ha => h f' v x a g (activeF_mid ha)

/-- `GSetOk` passes to a label body. -/
theorem gsetOk_label {s : Store H} {f : Frame} {n : Nat} {cont : V1.Expr} {body : List Admin}
    (h : GSetOk s f [.label n cont body]) : GSetOk s f body :=
  fun f' v x a g ha => h f' v x a g (.label (List.mem_singleton_self _) ha)

/-- `GSetOk` passes to a frame body, read in the inner frame. -/
theorem gsetOk_frame {s : Store H} {f fi : Frame} {n : Nat} {body : List Admin}
    (h : GSetOk s f [.frame n fi body]) : GSetOk s fi body :=
  fun f' v x a g ha => h f' v x a g (.frame (List.mem_singleton_self _) ha)

/-- `GSetOk` at a `global.set` redex. -/
theorem gsetOk_redex {s : Store H} {f : Frame} {v : Execution.Runtime.Value} {x : GlobalIdx}
    {a : Execution.Runtime.GlobalAddr} {g : Execution.Runtime.GlobalInst}
    (h : GSetOk s f [value v, .source (.globalSet x)]) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a.value]? = some g) : v.type = g.value.type :=
  h f v x a g (by simpa using (ActiveF.piece (l₁ := []) (l₂ := []) (f := f)
    (w := [value v, .source (.globalSet x)]))) ha hg

end Silmaril.Wasm.SpecTec.Sim10.Whole
