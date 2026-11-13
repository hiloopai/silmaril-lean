module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.HeightLemmas

/-!
# Decomposition of concatenated code, with derivation heights

The counterpart of `Silmaril/Wasm/V1/BigStep/Compose.lean`. Components of a
decomposition are sub-derivations, hence no taller than the whole, so they are
reported at the original height via `BigStepN.mono`.

Composition is the one place where the height genuinely grows: plugging the
derivation of `es'` into the `nil` leaf of the derivation of `es` stacks the two
spines, so `BigStepN.append` adds the two heights.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*} {host : HostSemantics H}

/-- Auxiliary form of `BigStepN.append`: the normal result is generalised so that
the induction on the first derivation goes through, and the height of the second
derivation is generalised so that it survives the descent into the first. -/
theorem BigStepN.append' {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {es : List Admin} {o₁ : Outcome H} (first : BigStepN host n s f vs es o₁) :
    ∀ {m : Nat} {s₂ : Store H} {f₂ : Frame} {ws : List Value} {es' : List Admin}
      {o : Outcome H}, o₁ = ⟨s₂, f₂, .normal ws⟩ → BigStepN host m s₂ f₂ ws es' o →
      BigStepN host (m + n) s f vs (es ++ es') o := by
  induction first with
  | nil s f vs =>
    intro m s₂ f₂ ws es' o heq second
    obtain ⟨rfl, rfl, rfl⟩ : s = s₂ ∧ f = f₂ ∧ vs = ws := by
      simpa only [Outcome.mk.injEq, BigResult.normal.injEq] using heq
    exact second.mono (Nat.le_add_right _ _)
  | plain step _ ih => exact fun heq second => BigStepN.plain step (ih heq second)
  | plainTrap => exact fun heq => nomatch heq
  | trap => exact fun heq => nomatch heq
  | block _ ih => exact fun heq second => BigStepN.block (ih heq second)
  | loop _ ih => exact fun heq second => BigStepN.loop (ih heq second)
  | ifZero _ ih => exact fun heq second => BigStepN.ifZero (ih heq second)
  | ifNonzero nonzero _ ih => exact fun heq second => BigStepN.ifNonzero nonzero (ih heq second)
  | br => exact fun heq => nomatch heq
  | brIfZero _ ih => exact fun heq second => BigStepN.brIfZero (ih heq second)
  | brIfNonzero nonzero _ ih =>
    exact fun heq second => BigStepN.brIfNonzero nonzero (ih heq second)
  | brTable _ ih => exact fun heq second => BigStepN.brTable (ih heq second)
  | return_ => exact fun heq => nomatch heq
  | call found _ ih => exact fun heq second => BigStepN.call found (ih heq second)
  | callIndirect tableFound typeFound element found typeMatch _ ih =>
    exact fun heq second =>
      BigStepN.callIndirect tableFound typeFound element found typeMatch (ih heq second)
  | callIndirectBounds => exact fun heq => nomatch heq
  | callIndirectNull => exact fun heq => nomatch heq
  | callIndirectType => exact fun heq => nomatch heq
  | invokeWasm found arity resultArity _ ih =>
    exact fun heq second => BigStepN.invokeWasm found arity resultArity (ih heq second)
  | invokeHost found arity behavior _ ih =>
    exact fun heq second => BigStepN.invokeHost found arity behavior
      (List.append_assoc _ _ _ ▸ ih heq second)
  | labelNormal inner _ _ ih =>
    exact fun heq second =>
      BigStepN.labelNormal (inner.mono (Nat.le_add_left _ _)) (ih heq second)
  | labelBrZero inner target arity _ _ ih =>
    exact fun heq second => BigStepN.labelBrZero (inner.mono (Nat.le_add_left _ _)) target arity
      (List.append_assoc _ _ _ ▸ ih heq second)
  | labelBrSucc => exact fun heq => nomatch heq
  | labelRet => exact fun heq => nomatch heq
  | labelTrap => exact fun heq => nomatch heq
  | frameNormal inner arity _ _ ih =>
    exact fun heq second =>
      BigStepN.frameNormal (inner.mono (Nat.le_add_left _ _)) arity (ih heq second)
  | frameRet inner arity _ _ ih =>
    exact fun heq second =>
      BigStepN.frameRet (inner.mono (Nat.le_add_left _ _)) arity (ih heq second)
  | frameTrap => exact fun heq => nomatch heq

/-- Sequential composition when the first part terminates normally.

The heights **add**: the derivation of `es'` is grafted onto the `nil` leaf of
the derivation of `es`, so the two spines stack. No common bound works, and in
particular the two inputs and the output cannot all be at the same height `n`:
with `es = es' = [.source i]` for a plain `i`, both inputs are derivable at
height `2` and nowhere lower, while `es ++ es'` needs height `3`. -/
theorem BigStepN.append {n m : Nat} {s s₂ : Store H} {f f₂ : Frame} {vs ws : List Value}
    {es es' : List Admin} {o : Outcome H}
    (first : BigStepN host n s f vs es ⟨s₂, f₂, .normal ws⟩)
    (second : BigStepN host m s₂ f₂ ws es' o) : BigStepN host (n + m) s f vs (es ++ es') o := by
  rw [Nat.add_comm]
  exact first.append' rfl second

/-- Auxiliary form of `BigStepN.append_abrupt`, with the abruptness premise inside
the induction. -/
theorem BigStepN.append_abrupt' {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {es es' : List Admin} {o : Outcome H} (first : BigStepN host n s f vs es o) :
    o.result.Abrupt → BigStepN host n s f vs (es ++ es') o := by
  induction first with
  | nil => exact fun abrupt => abrupt.elim
  | plain step _ ih => exact fun abrupt => BigStepN.plain step (ih abrupt)
  | plainTrap step => exact fun _ => BigStepN.plainTrap step
  | trap => exact fun _ => BigStepN.trap _ _ _ _
  | block _ ih => exact fun abrupt => BigStepN.block (ih abrupt)
  | loop _ ih => exact fun abrupt => BigStepN.loop (ih abrupt)
  | ifZero _ ih => exact fun abrupt => BigStepN.ifZero (ih abrupt)
  | ifNonzero nonzero _ ih => exact fun abrupt => BigStepN.ifNonzero nonzero (ih abrupt)
  | br => exact fun _ => BigStepN.br _ _ _ _ _
  | brIfZero _ ih => exact fun abrupt => BigStepN.brIfZero (ih abrupt)
  | brIfNonzero nonzero _ ih => exact fun abrupt => BigStepN.brIfNonzero nonzero (ih abrupt)
  | brTable _ ih => exact fun abrupt => BigStepN.brTable (ih abrupt)
  | return_ => exact fun _ => BigStepN.return_ _ _ _ _
  | call found _ ih => exact fun abrupt => BigStepN.call found (ih abrupt)
  | callIndirect tableFound typeFound element found typeMatch _ ih =>
    exact fun abrupt => BigStepN.callIndirect tableFound typeFound element found typeMatch
      (ih abrupt)
  | callIndirectBounds tableFound outOfBounds =>
    exact fun _ => BigStepN.callIndirectBounds tableFound outOfBounds
  | callIndirectNull tableFound null => exact fun _ => BigStepN.callIndirectNull tableFound null
  | callIndirectType tableFound typeFound element found typeMismatch =>
    exact fun _ => BigStepN.callIndirectType tableFound typeFound element found typeMismatch
  | invokeWasm found arity resultArity _ ih =>
    exact fun abrupt => BigStepN.invokeWasm found arity resultArity (ih abrupt)
  | invokeHost found arity behavior _ ih =>
    exact fun abrupt => BigStepN.invokeHost found arity behavior
      (List.append_assoc _ _ _ ▸ ih abrupt)
  | labelNormal inner _ _ ih => exact fun abrupt => BigStepN.labelNormal inner (ih abrupt)
  | labelBrZero inner target arity _ _ ih =>
    exact fun abrupt => BigStepN.labelBrZero inner target arity
      (List.append_assoc _ _ _ ▸ ih abrupt)
  | labelBrSucc inner outer => exact fun _ => BigStepN.labelBrSucc inner outer
  | labelRet inner => exact fun _ => BigStepN.labelRet inner
  | labelTrap inner => exact fun _ => BigStepN.labelTrap inner
  | frameNormal inner arity _ _ ih => exact fun abrupt => BigStepN.frameNormal inner arity (ih abrupt)
  | frameRet inner arity _ _ ih => exact fun abrupt => BigStepN.frameRet inner arity (ih abrupt)
  | frameTrap inner => exact fun _ => BigStepN.frameTrap inner

/-- An abrupt first part abandons everything after it. -/
theorem BigStepN.append_abrupt {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {es es' : List Admin} {o : Outcome H} (first : BigStepN host n s f vs es o)
    (abrupt : o.result.Abrupt) : BigStepN host n s f vs (es ++ es') o :=
  first.append_abrupt' abrupt

/-! ### Decomposition -/

/-- The two ways a run of `es ++ es'` decomposes: `es` runs normally and `es'`
continues, or `es` ends abruptly. -/
def AppInv (host : HostSemantics H) (n : Nat) (s : Store H) (f : Frame) (vs : List Value)
    (es es' : List Admin) (o : Outcome H) : Prop :=
  (∃ s₂ f₂ ws, BigStepN host n s f vs es ⟨s₂, f₂, .normal ws⟩ ∧
      BigStepN host n s₂ f₂ ws es' o) ∨
    (BigStepN host n s f vs es o ∧ o.result.Abrupt)

/-- The common case split of every arm: either the prefix is empty, and the whole
run is the continuation, or it starts with the head instruction. -/
theorem AppInv.step {k : Nat} {s : Store H} {f : Frame} {vs : List Value} {a : Admin}
    {tail es es' : List Admin} {o : Outcome H} (heq : a :: tail = es ++ es')
    (horig : BigStepN host (k + 1) s f vs (a :: tail) o)
    (hcons : ∀ es₀, tail = es₀ ++ es' → AppInv host (k + 1) s f vs (a :: es₀) es' o) :
    AppInv host (k + 1) s f vs es es' o := by
  rcases es with _ | ⟨b, es₀⟩
  · have hes : es' = a :: tail := heq.symm
    exact .inl ⟨s, f, vs, BigStepN.nil _ _ _, hes ▸ horig⟩
  · have hc : a = b ∧ tail = es₀ ++ es' := List.cons.inj heq
    exact hc.1 ▸ hcons es₀ hc.2

/-- An arm whose premise continues with `pre ++ tail`: the decomposition of the
premise lifts through the rule `mk`. -/
theorem AppInv.lift {k : Nat} {s s' : Store H} {f f' : Frame} {vs vs' : List Value} {a : Admin}
    {pre es₀ es' : List Admin} {o : Outcome H} (ih : AppInv host k s' f' vs' (pre ++ es₀) es' o)
    (mk : ∀ {c : List Admin} {o' : Outcome H}, BigStepN host k s' f' vs' (pre ++ c) o' →
      BigStepN host (k + 1) s f vs (a :: c) o') :
    AppInv host (k + 1) s f vs (a :: es₀) es' o := by
  rcases ih with ⟨s₂, f₂, ws, h₁, h₂⟩ | ⟨h₁, hab⟩
  · exact .inl ⟨s₂, f₂, ws, mk h₁, h₂.mono (Nat.le_succ _)⟩
  · exact .inr ⟨mk h₁, hab⟩

/-- An arm whose rule ends abruptly whatever follows. -/
theorem AppInv.abrupt {k : Nat} {s : Store H} {f : Frame} {vs : List Value} {a : Admin}
    {es₀ es' : List Admin} {o : Outcome H} (h : BigStepN host (k + 1) s f vs (a :: es₀) o)
    (hab : o.result.Abrupt) : AppInv host (k + 1) s f vs (a :: es₀) es' o :=
  .inr ⟨h, hab⟩

/-- `AppInv.lift` for a premise that continues with one instruction `x` before the
tail. -/
theorem AppInv.lift₁ {k : Nat} {s s' : Store H} {f f' : Frame} {vs vs' : List Value}
    {a x : Admin} {es₀ es' : List Admin} {o : Outcome H}
    (ih : AppInv host k s' f' vs' (x :: es₀) es' o)
    (mk : ∀ {c : List Admin} {o' : Outcome H}, BigStepN host k s' f' vs' (x :: c) o' →
      BigStepN host (k + 1) s f vs (a :: c) o') :
    AppInv host (k + 1) s f vs (a :: es₀) es' o :=
  AppInv.lift (pre := [x]) ih mk

/-- The code of a premise that continues with one instruction before the tail. -/
theorem AppInv.code₁ {x : Admin} {tail es₀ es' : List Admin} (hc : tail = es₀ ++ es') :
    x :: tail = (x :: es₀) ++ es' := by
  rw [hc, List.cons_append]

/-- The code of a premise that continues with `pre ++ tail`. -/
theorem AppInv.code {pre tail es₀ es' : List Admin} (hc : tail = es₀ ++ es') :
    pre ++ tail = (pre ++ es₀) ++ es' := by
  rw [hc, List.append_assoc]

/-- Auxiliary form of `BigStepN.append_inv`: the code is generalised, and the
derivation is passed a second time so that the empty-prefix case can hand it
back unchanged. -/
theorem BigStepN.append_inv' {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {code : List Admin} {o : Outcome H} (h : BigStepN host n s f vs code o) :
    ∀ es es' : List Admin, code = es ++ es' → BigStepN host n s f vs code o →
      AppInv host n s f vs es es' o := by
  induction h with
  | nil =>
    intro es es' heq horig
    have hn : es = [] ∧ es' = [] := List.append_eq_nil_iff.mp heq.symm
    exact .inl ⟨_, _, _, hn.1 ▸ BigStepN.nil _ _ _, hn.2 ▸ BigStepN.nil _ _ _⟩
  | plain step rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift (pre := []) (ih es₀ es' hc rest) (BigStepN.plain step)
  | plainTrap step =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.plainTrap step) trivial
  | trap =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.trap _ _ _ _) trivial
  | block rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest) BigStepN.block
  | loop rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest) BigStepN.loop
  | ifZero rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest) BigStepN.ifZero
  | ifNonzero nonzero rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest) (BigStepN.ifNonzero nonzero)
  | br =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.br _ _ _ _ _) trivial
  | brIfZero rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift (pre := []) (ih es₀ es' hc rest) BigStepN.brIfZero
  | brIfNonzero nonzero rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest) (BigStepN.brIfNonzero nonzero)
  | brTable rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest) BigStepN.brTable
  | return_ =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.return_ _ _ _ _) trivial
  | call found rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest) (BigStepN.call found)
  | callIndirect tableFound typeFound element found typeMatch rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest)
        (BigStepN.callIndirect tableFound typeFound element found typeMatch)
  | callIndirectBounds tableFound outOfBounds =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.callIndirectBounds tableFound outOfBounds) trivial
  | callIndirectNull tableFound null =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.callIndirectNull tableFound null) trivial
  | callIndirectType tableFound typeFound element found typeMismatch =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt
        (BigStepN.callIndirectType tableFound typeFound element found typeMismatch) trivial
  | invokeWasm found arity resultArity rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift₁ (ih _ es' (AppInv.code₁ hc) rest)
        (BigStepN.invokeWasm found arity resultArity)
  | invokeHost found arity behavior rest ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift (ih _ es' (AppInv.code hc) rest) (BigStepN.invokeHost found arity behavior)
  | labelNormal inner rest _ ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift (pre := []) (ih es₀ es' hc rest) (BigStepN.labelNormal inner)
  | labelBrZero inner target arity rest _ ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift (ih _ es' (AppInv.code hc) rest) (BigStepN.labelBrZero inner target arity)
  | labelBrSucc inner outer =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.labelBrSucc inner outer) trivial
  | labelRet inner =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.labelRet inner) trivial
  | labelTrap inner =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.labelTrap inner) trivial
  | frameNormal inner arity rest _ ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift (pre := []) (ih es₀ es' hc rest) (BigStepN.frameNormal inner arity)
  | frameRet inner arity rest _ ih =>
    exact fun es es' heq horig => AppInv.step heq horig fun es₀ hc =>
      AppInv.lift (pre := []) (ih es₀ es' hc rest) (BigStepN.frameRet inner arity)
  | frameTrap inner =>
    exact fun es es' heq horig => AppInv.step heq horig fun _ _ =>
      AppInv.abrupt (BigStepN.frameTrap inner) trivial

/-- Decomposition of a run of concatenated code: the `[seq]` rule, semantically.
Both components are given at the original height, using `BigStepN.mono`. -/
theorem BigStepN.append_inv {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {es es' : List Admin} {o : Outcome H} (h : BigStepN host n s f vs (es ++ es') o) :
    (∃ s₂ f₂ ws, BigStepN host n s f vs es ⟨s₂, f₂, .normal ws⟩ ∧
        BigStepN host n s₂ f₂ ws es' o) ∨
      (BigStepN host n s f vs es o ∧ o.result.Abrupt) :=
  h.append_inv' es es' rfl h

end Silmaril.Wasm.Logic.V1
