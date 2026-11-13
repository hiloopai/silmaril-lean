module

public import Silmaril.Wasm.SingleThreaded.Determinism

/-!
# Determinism of host-free Core steps up to profile choices

Under an arbitrary profile `P` (any `$ND`, relaxed choices, NaN policy and grow policy),
host-free Core reduction is not deterministic: a numeric or vector operator may pick any
result the profile allows, and `memory.grow`/`table.grow` may fail or succeed. This file
shows that these choices, and the bubbling of `TRAP`/`THROW_REF` (the overlap of
`trap-instrs`/`throw_ref-instrs` with `ctxt-instrs`), are the *only* sources of
nondeterminism:

* `Soft P c d`: the step `c ~> d` is, under the context rules, a choice step (a step of the
  numeric, vector, table or memory family) or a bubble (`Det.Bubble`); `Soft.step`;
* `soft_join` (**determinism up to choices**, `Silmaril.Proofs.Wasm.Game.Machine.SoftJoin`): two
  host-free steps from the same configuration under `P` have equal results, or both are
  `Soft`.

A backward simulation can therefore be obtained from a forward one: the forward image of a
source step is the target step itself unless the target step is `Soft`, and `Soft` steps
(choice leaves and bubbles under contexts) are replayed structurally.

Source: the proof follows silmaril-lean's diamond property `Det.DStep.join` and
`Det.Head.det_ctl` (`Silmaril/Wasm/SingleThreaded/Determinism/{Join,HeadCtl}.lean`, pinned
revision), whose control cases and closing tactics (`hd_close`, `ctl_single`, `ctl_step`,
`ctl_body`, `ctl_same`, `ctl_vals`, `ctl_catch`, `ctl_block`) are reused unchanged; only the
context cases and the family cases (where the profile matters) are new. The joinability
relation is instantiated with `SoftPair` instead of `DStep o`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Choice

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-- The families whose result is chosen by the profile. -/
def ChoiceFam : Fam → Prop
  | .numeric | .vector | .table | .memory => True
  | _ => False

/-- A host-free step whose redex is a profile choice or a bubble, under the context rules. -/
inductive Soft (P : Profile) : Config H → Config H → Prop where
  | choice {s : Store H} {f : Frame} {k : Fam} {code : List Admin} {c : Config H}
      (hk : ChoiceFam k) (h : FamRel P k s f code c) : Soft P ⟨s, f, code⟩ c
  | bubble {s : Store H} {f : Frame} {code : List Admin} {c : Config H}
      (h : Bubble s f code c) : Soft P ⟨s, f, code⟩ c
  | instrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
      (h : Soft P ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Soft P ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩
  | label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin}
      (h : Soft P ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Soft P ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩
  | handler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch} {is is' : List Admin}
      (h : Soft P ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Soft P ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩
  | frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
      (h : Soft P ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
      Soft P ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩

/-- Both results are `Soft` successors of `c`. -/
def SoftPair (P : Profile) (c : Config H) (a b : Config H) : Prop := Soft P c a ∧ Soft P c b

/-- Two successors of `c` are equal, or both `Soft`. -/
def SoftJoin (P : Profile) (c : Config H) (a b : Config H) : Prop := a = b ∨ SoftPair P c a b

/-! ### `Soft` steps are steps -/

/-- A choice family step is a host-free step. -/
theorem famRel_step {P : Profile} {k : Fam} {s : Store H} {f : Frame} {code : List Admin}
    {c : Config H} (hk : ChoiceFam k) (h : FamRel P k s f code c) :
    Step P noHost ⟨s, f, code⟩ c := by
  cases k with
  | numeric => obtain ⟨is', hs, rfl⟩ := h; exact .numeric hs
  | vector => obtain ⟨is', hs, rfl⟩ := h; exact .vector hs
  | table => exact .table h
  | memory => exact .memory h
  | _ => exact hk.elim

/-- A bubble is a host-free step. -/
theorem bubble_step {P : Profile} {s : Store H} {f : Frame} {code : List Admin} {c : Config H}
    (h : Bubble s f code c) : Step P noHost ⟨s, f, code⟩ c := by
  obtain ⟨p, q, X, u, r, rfl, hX, hqu, rfl⟩ := h
  have hin : Step P noHost ⟨s, f, vals q ++ X ++ u⟩ ⟨s, f, X⟩ := by
    rcases hX with rfl | ⟨a, rfl⟩
    · exact .trapInstrs hqu
    · exact .throwRefInstrs hqu
  have hl := lift_instrs (P := P) p r _ _ hin
  have hcode : vals (p ++ q) ++ X ++ (u ++ r) = vals p ++ (vals q ++ X ++ u) ++ r := by
    simp [vals_append, List.append_assoc]
  simpa only [hcode] using hl

/-- Every `Soft` step is a host-free step. -/
theorem Soft.step {P : Profile} {c d : Config H} (h : Soft P c d) : Step P noHost c d := by
  induction h with
  | choice hk h => exact famRel_step hk h
  | bubble h => exact bubble_step h
  | instrs _ ih => exact lift_instrs _ _ _ _ ih
  | label _ ih => exact lift_label _ _ _ _ ih
  | handler _ ih => exact lift_handler _ _ _ _ ih
  | frame _ ih => exact lift_frame _ _ _ _ ih

/-! ### Joining under contexts -/

theorem SoftPair.join {P : Profile} {c a b : Config H} (h : SoftPair P c a b) :
    Join (SoftPair P c) a b :=
  ⟨b, .single h, .refl⟩

theorem SoftJoin.join {P : Profile} {c a b : Config H} (h : SoftJoin P c a b) :
    Join (SoftPair P c) a b := by
  rcases h with rfl | h
  · exact Join.rfl'
  · exact h.join

/-- Read a `Join` of `SoftPair` back as `SoftJoin`. -/
theorem SoftJoin.of_join {P : Profile} {c a b : Config H} (h : Join (SoftPair P c) a b) :
    SoftJoin P c a b := by
  obtain ⟨z, ha, hb⟩ := h
  cases ha with
  | refl =>
    cases hb with
    | refl => exact .inl rfl
    | single h => exact .inr ⟨h.2, h.1⟩
  | single h =>
    cases hb with
    | refl => exact .inr h
    | single h' => exact .inr ⟨h.1, h'.1⟩

/-- `SoftJoin` lifts along a step-preserving map that is `Soft`-preserving. -/
theorem SoftJoin.map {P : Profile} {c a b : Config H} (F : Config H → Config H)
    (hF : ∀ x, Soft P c x → Soft P (F c) (F x)) (h : SoftJoin P c a b) :
    SoftJoin P (F c) (F a) (F b) := by
  rcases h with rfl | ⟨ha, hb⟩
  · exact .inl rfl
  · exact .inr ⟨hF a ha, hF b hb⟩

theorem ctxt_label_soft {P : Profile} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {n : Nat}
    {cont : List Instr} {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.label n cont is) → Step P noHost ⟨s, f, body⟩ c₁ →
      Step P noHost ⟨s, f, body⟩ c₂ → SoftJoin P ⟨s, f, body⟩ c₁ c₂)
    (h₁ : Step P noHost ⟨s, f, is⟩ ⟨s₁, f₁, is₁⟩) (h₂ : Step P noHost ⟨s, f, is⟩ ⟨s₂, f₂, is₂⟩)
    (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (SoftPair P ⟨s, f, vals [] ++ [.label n cont is]⟩)
      ⟨s₁, f₁, [.label n cont is₁]⟩ ⟨s₂, f₂, [.label n cont is₂]⟩ := by
  have hin : SoftJoin P ⟨s, f, is⟩ ⟨s₁, f₁, is₁⟩ ⟨s₂, f₂, is₂⟩ :=
    ih s f is _ _ (by simp) h₁ h₂
  have hl := hin.map (fun c => ⟨c.store, c.frame, [.label n cont c.code]⟩)
    (fun x hx => by rcases x with ⟨_, _, _⟩; exact .label hx)
  exact ⟨by simpa using hp, SoftJoin.join hl⟩

theorem ctxt_handler_soft {P : Profile} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {n : Nat}
    {cs : List Catch} {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.handler n cs is) → Step P noHost ⟨s, f, body⟩ c₁ →
      Step P noHost ⟨s, f, body⟩ c₂ → SoftJoin P ⟨s, f, body⟩ c₁ c₂)
    (h₁ : Step P noHost ⟨s, f, is⟩ ⟨s₁, f₁, is₁⟩) (h₂ : Step P noHost ⟨s, f, is⟩ ⟨s₂, f₂, is₂⟩)
    (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (SoftPair P ⟨s, f, vals [] ++ [.handler n cs is]⟩)
      ⟨s₁, f₁, [.handler n cs is₁]⟩ ⟨s₂, f₂, [.handler n cs is₂]⟩ := by
  have hin : SoftJoin P ⟨s, f, is⟩ ⟨s₁, f₁, is₁⟩ ⟨s₂, f₂, is₂⟩ :=
    ih s f is _ _ (by simp) h₁ h₂
  have hl := hin.map (fun c => ⟨c.store, c.frame, [.handler n cs c.code]⟩)
    (fun x hx => by rcases x with ⟨_, _, _⟩; exact .handler hx)
  exact ⟨by simpa using hp, SoftJoin.join hl⟩

theorem ctxt_frame_soft {P : Profile} {s s₁ s₂ : Store H} {f fi fi₁ fi₂ : Frame} {n : Nat}
    {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.frame n fi is) → Step P noHost ⟨s, f, body⟩ c₁ →
      Step P noHost ⟨s, f, body⟩ c₂ → SoftJoin P ⟨s, f, body⟩ c₁ c₂)
    (h₁ : Step P noHost ⟨s, fi, is⟩ ⟨s₁, fi₁, is₁⟩)
    (h₂ : Step P noHost ⟨s, fi, is⟩ ⟨s₂, fi₂, is₂⟩) (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (SoftPair P ⟨s, f, vals [] ++ [.frame n fi is]⟩)
      ⟨s₁, f, [.frame n fi₁ is₁]⟩ ⟨s₂, f, [.frame n fi₂ is₂]⟩ := by
  have hin : SoftJoin P ⟨s, fi, is⟩ ⟨s₁, fi₁, is₁⟩ ⟨s₂, fi₂, is₂⟩ :=
    ih s fi is _ _ (by simp) h₁ h₂
  have hl := hin.map (fun c => ⟨c.store, f, [.frame n c.frame c.code]⟩)
    (fun x hx => by rcases x with ⟨_, _, _⟩; exact .frame hx)
  exact ⟨by simpa using hp, SoftJoin.join hl⟩

end Silmaril.Proofs.Wasm.Game.Choice
