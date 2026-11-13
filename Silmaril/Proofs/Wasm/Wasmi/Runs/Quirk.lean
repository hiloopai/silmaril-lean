module

public import Silmaril.Wasm.Wasmi.Runs.Defs
public import Silmaril.Wasm.Atlas.Variant.Defs

/-!
# Quirk steps are deterministic (proofs)

`ctx_quirk_inv`: a quirk step of wasmi 0.40.0 in an evaluation context
(`Variant.Ctx Quirk c c'`) starts from code with a pending quirk redex (`pending c.code`) and
reaches `⟨c.store, c.frame, fire c.code⟩`. This is the first of the two sanity lemmas of track
wasmi ("`Ctx Quirk c c' → pending c.code`"), with the successor computed. Consequences:

* `step_of_not_pending`: where no quirk redex is pending, a model step is exactly a Core 3.0
  step;
* `step_of_pending`: where one is, a model step is exactly a quirk step, to `fire c.code`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Runs

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi.Observed Silmaril.Wasm.Wasmi.Runs

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The code starts with a float unary operator. -/
def OpHead (l : List Admin) : Prop :=
  ∃ t op r, l = .plain (.floatUnOp t op) :: r

/-- The two-instruction quirk pattern does not start the code `a :: rest`. -/
def NoPat (a : Admin) (rest : List Admin) : Prop :=
  ∀ t x, a = .plain (.floatConst t x) → ¬ OpHead rest

theorem pending_cons {a : Admin} {rest : List Admin} (h : NoPat a rest) :
    pending (a :: rest) = match a.val? with
      | some _ => pending rest
      | none => pendingA a := by
  conv_lhs => unfold pending
  split
  all_goals rename_i heq
  all_goals simp only [List.cons.injEq, reduceCtorEq] at heq
  · obtain ⟨rfl, rfl⟩ := heq
    exact (h _ _ rfl ⟨_, _, _, rfl⟩).elim
  · obtain ⟨rfl, rfl⟩ := heq
    rfl

theorem fire_cons {a : Admin} {rest : List Admin} (h : NoPat a rest) :
    fire (a :: rest) = match a.val? with
      | some _ => a :: fire rest
      | none => fireA a :: rest := by
  conv_lhs => unfold fire
  split
  all_goals rename_i heq
  all_goals simp only [List.cons.injEq, reduceCtorEq] at heq
  · obtain ⟨rfl, rfl⟩ := heq
    exact (h _ _ rfl ⟨_, _, _, rfl⟩).elim
  · obtain ⟨rfl, rfl⟩ := heq
    rfl

/-- A non-value never starts the quirk pattern. -/
theorem noPat_of_none {a : Admin} (ha : a.val? = none) (rest : List Admin) : NoPat a rest := by
  rintro t x rfl
  simp [Admin.val?] at ha

theorem pending_none {a : Admin} (ha : a.val? = none) (rest : List Admin) :
    pending (a :: rest) = pendingA a := by
  rw [pending_cons (noPat_of_none ha rest), ha]

theorem fire_none {a : Admin} (ha : a.val? = none) (rest : List Admin) :
    fire (a :: rest) = fireA a :: rest := by
  rw [fire_cons (noPat_of_none ha rest), ha]

/-- Code starting with an operator has no pending quirk redex. -/
theorem not_opHead {l : List Admin} (h : pending l = true) : ¬ OpHead l := by
  rintro ⟨t, op, r, rfl⟩
  rw [pending_none (by simp [Admin.val?]) r] at h
  simp [pendingA] at h

theorem opHead_append {l rest : List Admin} (hl : l ≠ []) (h : OpHead (l ++ rest)) : OpHead l := by
  obtain ⟨t, op, r, he⟩ := h
  cases l with
  | nil => exact absurd rfl hl
  | cons a l =>
    simp only [List.cons_append, List.cons.injEq] at he
    exact ⟨t, op, l, by rw [he.1]⟩

theorem opHead_vals {vs : List Val} {l : List Admin} (h : OpHead (vals vs ++ l)) :
    vs = [] ∧ OpHead l := by
  cases vs with
  | nil => exact ⟨rfl, by simpa using h⟩
  | cons v vs =>
    obtain ⟨t, op, r, he⟩ := h
    simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at he
    have := congrArg Admin.val? he.1
    rw [Admin.val?_toAdmin] at this
    simp [Admin.val?] at this

/-- **A pending redex stays pending, and is fired alike, after appending code.** -/
theorem pending_append : ∀ {l : List Admin} (rest : List Admin), pending l = true →
    pending (l ++ rest) = true ∧ fire (l ++ rest) = fire l ++ rest
  | [], _, h => by simp [pending] at h
  | a :: l, rest, h => by
    by_cases hp : ∃ t x, a = .plain (.floatConst t x) ∧ OpHead l
    · obtain ⟨t, x, rfl, t', op, r, rfl⟩ := hp
      refine ⟨?_, ?_⟩
      · simpa [pending] using h
      · simp [fire]
    · have hn : NoPat a l := fun t x ha hl => hp ⟨t, x, ha, hl⟩
      rw [pending_cons hn] at h
      cases hv : a.val? with
      | some v =>
        rw [hv] at h
        have hl : l ≠ [] := by
          rintro rfl
          simp [pending] at h
        have hn' : NoPat a (l ++ rest) := fun t x ha ho =>
          not_opHead h (opHead_append hl ho)
        obtain ⟨ih₁, ih₂⟩ := pending_append rest h
        rw [List.cons_append, pending_cons hn', fire_cons hn', fire_cons hn, hv]
        exact ⟨ih₁, by simp [ih₂]⟩
      | none =>
        rw [hv] at h
        rw [List.cons_append, pending_none hv, fire_none hv, fire_none hv]
        exact ⟨h, rfl⟩

/-- **A pending redex stays pending, and is fired alike, under leading values.** -/
theorem pending_vals : ∀ (vs : List Val) {l : List Admin}, pending l = true →
    pending (vals vs ++ l) = true ∧ fire (vals vs ++ l) = vals vs ++ fire l
  | [], _, h => ⟨by simpa using h, by simp⟩
  | v :: vs, l, h => by
    have hn : NoPat v.toAdmin (vals vs ++ l) := fun _ _ _ ho => by
      obtain ⟨rfl, ho⟩ := opHead_vals ho
      exact not_opHead h ho
    obtain ⟨ih₁, ih₂⟩ := pending_vals vs h
    have e : vals (v :: vs) ++ l = v.toAdmin :: (vals vs ++ l) := rfl
    rw [e, pending_cons hn, fire_cons hn, Admin.val?_toAdmin]
    refine ⟨ih₁, ?_⟩
    rw [ih₂]
    rfl

theorem pending_single {a : Admin} (ha : a.val? = none) :
    pending [a] = pendingA a := pending_none ha []

theorem fire_single {a : Admin} (ha : a.val? = none) :
    fire [a] = [fireA a] := fire_none ha []

/-- The quirk redex itself. -/
theorem quirk_base {c c' : Config H} (hq : Quirk c c') :
    pending c.code = true ∧ c' = ⟨c.store, c.frame, fire c.code⟩ := by
  cases hq with
  | @roundNaN _ _ t op x hop hx =>
    have hp : pending [.plain (.floatConst t x), .plain (.floatUnOp t op)] = true := by
      cases t <;> simp [pending, redexB, hop, hx]
    exact ⟨hp, by simp [fire]⟩

/-- A quirk step under values and before code. -/
theorem quirk_instrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (ih : pending is = true ∧ (⟨s', f', is'⟩ : Config H) = ⟨s, f, fire is⟩) :
    pending (vals vs ++ is ++ rest) = true ∧
      (⟨s', f', vals vs ++ is' ++ rest⟩ : Config H) = ⟨s, f, fire (vals vs ++ is ++ rest)⟩ := by
  obtain ⟨hp, he⟩ := ih
  have hp₁ := pending_vals vs hp
  have hp₂ := pending_append rest hp₁.1
  have hs : s' = s ∧ f' = f ∧ is' = fire is := by simpa using he
  refine ⟨hp₂.1, ?_⟩
  rw [hp₂.2, hp₁.2, hs.1, hs.2.1, hs.2.2]

/-- A quirk step inside a single non-value whose `pending` and `fire` go to its body. -/
theorem quirk_wrap {s s' : Store H} {f f' : Frame} {is is' : List Admin} {g : List Admin → Admin}
    (hg : ∀ b, (g b).val? = none) (hp : ∀ b, pendingA (g b) = pending b)
    (hf : ∀ b, fireA (g b) = g (fire b))
    (ih : pending is = true ∧ (⟨s', f', is'⟩ : Config H) = ⟨s, f, fire is⟩) :
    pending [g is] = true ∧ [g is'] = fire [g is] ∧ s' = s ∧ f' = f := by
  have hs : s' = s ∧ f' = f ∧ is' = fire is := by simpa using ih.2
  have h₁ : pending [g is] = true := by rw [pending_single (hg is), hp]; exact ih.1
  have h₂ : fire [g is] = [g (fire is)] := by rw [fire_single (hg is), hf]
  exact ⟨h₁, by rw [h₂, hs.2.2], hs.1, hs.2.1⟩

/-- **Quirk steps**: from a pending redex, to the fired code, with the store and frame kept. -/
theorem ctx_quirk_inv {c c' : Config H} (h : Variant.Ctx Quirk c c') :
    pending c.code = true ∧ c' = ⟨c.store, c.frame, fire c.code⟩ := by
  induction h with
  | base hq => exact quirk_base hq
  | instrs _ ih => exact quirk_instrs ih
  | @label _ _ _ _ n cont _ _ _ ih =>
    obtain ⟨hp, he, hs, hf⟩ := quirk_wrap (g := Admin.label n cont) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) ih
    exact ⟨hp, by rw [← he, hs, hf]⟩
  | @handler _ _ _ _ n cs _ _ _ ih =>
    obtain ⟨hp, he, hs, hf⟩ := quirk_wrap (g := Admin.handler n cs) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) ih
    exact ⟨hp, by rw [← he, hs, hf]⟩
  | @frame _ _ _ fi _ n _ _ _ ih =>
    obtain ⟨hp, he, hs, hfi⟩ := quirk_wrap (g := Admin.frame n fi) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) ih
    exact ⟨hp, by rw [← he, hs, hfi]⟩

/-- **Where no quirk redex is pending, a model step is a Core 3.0 step.** -/
theorem step_of_not_pending {c c' : Config H} (hp : pending c.code = false) :
    Silmaril.Wasm.Wasmi.Observed.Step P host c c' ↔ Execution.Core.Step P host c c' := by
  constructor
  · rintro (⟨-, h⟩ | h)
    · exact h
    · rw [(ctx_quirk_inv h).1] at hp
      cases hp
  · exact fun h => .inl ⟨hp, h⟩

/-- **Where a quirk redex is pending, a model step is a quirk step**, to the fired code. -/
theorem step_of_pending {c c' : Config H} (hp : pending c.code = true) :
    Silmaril.Wasm.Wasmi.Observed.Step P host c c' → c' = ⟨c.store, c.frame, fire c.code⟩ := by
  rintro (⟨hp', -⟩ | h)
  · rw [hp] at hp'
    cases hp'
  · exact (ctx_quirk_inv h).2

end Silmaril.Proofs.Wasm.Wasmi.Runs
