module

public import Silmaril.Elf.Link.Dyn.ProcG.Defs
public import Silmaril.Elf.Link.Dyn.Proc.Thms

/-! # Lifting process runs to a larger image ISA

PROVED (standard axioms): `must_lift`: if the `Open9` process must reach `Q` from `s`, the
extended process must reach `Q` (on the view) from every state whose view is `s`. Runs that
`Open9` cannot continue (an undecoded instruction in the image) are not runs `MustQ` proves,
so the lift is unconditional; new results that need the larger ISA are proved over `procG`
directly.

Stepping kit (PROVED, standard axioms), the `procG` counterparts of `Proc.Thms`:

* **`mustG_step`** (the `must_listed` analogue for any `J`): one `J.step = some x'` in the image
  is a step of `procG`;
* `mustG_insn`, `mustG_listed`: one listed `Open9` instruction of the image, run on the view
  (`L.put` keeps the rest of the `J` state);
* `mustG_bind`; **`mustG_of_mustQ`**: a `proc` run whose goal is "every `J` state with this view
  must reach `Q`" gives that `procG` run (the lift of a `proc` piece followed by more `procG`
  steps).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.ProcG

open Silmaril.X86 (MState State)
open Silmaril.X86.RelIsa (Res Must)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Elf.Link.Dyn.Proc

variable {τ : Type} {J : Isa τ}

/-- **`MustQ` over `proc W` lifts to `procG L W`.** -/
theorem must_lift (L : Silmaril.X86.Open9.isa.Extends J) {W : World} {Q : PState → Prop} {s : PState}
    (h : MustQ W Q s) : ∀ x : τ, L.view x = s.m →
      Must (procG L W) (fun _ => True) (fun y => Q (y.view L)) ⟨x, s.g⟩ := by
  induction h with
  | @done s0 hq =>
    intro x hx
    refine .done ?_
    show Q ⟨L.view x, s0.g⟩
    rw [hx]; exact hq
  | @step s0 _ hns _ ih =>
    intro x hx
    have hcore : (L.view x).core = s0.m.core := by rw [hx]
    refine .step trivial ?_ ?_
    · intro hst
      apply hns
      show step W s0 .stop
      simp only [procG, stepG] at hst
      unfold step
      cases hd : s0.g.done with
      | some _ => rfl
      | none =>
        rw [hd] at hst
        simp only at hst
        by_cases hin : W.InImage s0.m.core.rip.toNat
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hcore]; exact hin))] at hst
          rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
          cases hs : Silmaril.X86.Open9.step s0.m with
          | none => rfl
          | some m' =>
            have := L.step (x := x) (s := m') (by rw [hx]; exact hs)
            rw [this] at hst; cases hst
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcore]; exact hin))] at hst
          rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]
          have e : GState.view L ⟨x, s0.g⟩ = s0 := by
            show (⟨L.view x, s0.g⟩ : PState) = s0; rw [hx]
          simpa [e] using hst
    · intro y hy
      simp only [procG, stepG] at hy
      cases hd : s0.g.done with
      | some _ => rw [hd] at hy; cases hy
      | none =>
        rw [hd] at hy
        simp only at hy
        by_cases hin : W.InImage s0.m.core.rip.toNat
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hcore]; exact hin))] at hy
          cases hs : Silmaril.X86.Open9.step s0.m with
          | none =>
            exfalso; apply hns
            show step W s0 .stop
            unfold step; rw [hd]; simp only; rw [ite_eq_left_of_eq_true _ _ (eq_true hin), hs]; trivial
          | some m' =>
            have hJ := L.step (x := x) (s := m') (by rw [hx]; exact hs)
            rw [hJ] at hy
            cases hy
            have hp : step W s0 (.ok ⟨m', s0.g⟩) := by
              unfold step; rw [hd]; simp only; rw [ite_eq_left_of_eq_true _ _ (eq_true hin), hs]
            exact ih _ hp _ (L.view_put _ _)
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcore]; exact hin))] at hy
          obtain ⟨t, ht, hvt, hgt⟩ := hy
          have e : GState.view L ⟨x, s0.g⟩ = s0 := by
            show (⟨L.view x, s0.g⟩ : PState) = s0; rw [hx]
          rw [e] at ht
          have hp : step W s0 (.ok t) := by
            unfold step; rw [hd]; simp only; rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]; exact ht
          have := ih t hp y.x hvt
          rw [← hgt] at this
          exact this

/-- The extended process must reach `Q`. -/
abbrev MustG (L : Silmaril.X86.Open9.isa.Extends J) (W : World) (Q : GState τ → Prop) (s : GState τ) :
    Prop :=
  Must (procG L W) (fun _ => True) Q s

theorem mustG_bind {L : Silmaril.X86.Open9.isa.Extends J} {W : World} {P Q : GState τ → Prop}
    {s : GState τ} (h : MustG L W P s) (k : ∀ t, P t → MustG L W Q t) : MustG L W Q s :=
  Must.bind h k

/-- **A `proc` run continued on `procG`**: if `proc` must reach states `t` from which every
`J` state with view `t.m` must reach `Q`, then `procG` must reach `Q` from every `J` state with
view `s.m`. -/
theorem mustG_of_mustQ (L : Silmaril.X86.Open9.isa.Extends J) {W : World} {Q : GState τ → Prop}
    {s : PState} {x : τ} (hx : L.view x = s.m)
    (h : MustQ W (fun t => ∀ x' : τ, L.view x' = t.m → MustG L W Q ⟨x', t.g⟩) s) :
    MustG L W Q ⟨x, s.g⟩ :=
  Must.bind (must_lift L h x hx) fun y hy => hy y.x rfl

/-- **One step of the image machine `J`**: `J.step x = some x'` at an image address is a step
of `procG` (the ghost state is unchanged). -/
theorem mustG_step (L : Silmaril.X86.Open9.isa.Extends J) {W : World} {Q : GState τ → Prop}
    {s : GState τ} {x' : τ} (hd : s.g.done = none) (hin : W.InImage (L.view s.x).core.rip.toNat)
    (hs : J.step s.x = some x') (h : MustG L W Q ⟨x', s.g⟩) : MustG L W Q s := by
  refine Must.step trivial ?_ ?_
  · intro hst
    simp only [procG, stepG, hd, hin, ↓reduceIte, hs] at hst
    cases hst
  · intro t ht
    simp only [procG, stepG, hd, hin, ↓reduceIte, hs, Res.ok.injEq] at ht
    subst ht; exact h

/-- **One `Open9` instruction of the image**, run on the view (weakest-precondition form). -/
theorem mustG_insn (L : Silmaril.X86.Open9.isa.Extends J) {W : World} {Q : GState τ → Prop}
    {s : GState τ} {base : Silmaril.X86.Word} {code : List Silmaril.X86.Byte} {o l : Nat}
    {i : Silmaril.X86.Ext9.Instr} (hd : s.g.done = none)
    (hin : W.InImage (L.view s.x).core.rip.toNat) (hl : Silmaril.X86.Ext.Loaded (L.view s.x).memory base code)
    (hrip : (L.view s.x).core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : Silmaril.X86.Open9.decode ((code.drop o).take l) = some (i, l))
    (h : WP (Silmaril.X86.Ext9.exec i (L.view s.x).core (L.view s.x).memory l)
      fun c m => MustG L W Q ⟨L.put s.x ⟨c, m⟩, s.g⟩) : MustG L W Q s := by
  revert h
  cases e : Silmaril.X86.Ext9.exec i (L.view s.x).core (L.view s.x).memory l with
  | ok c m =>
    intro h
    have hs : Silmaril.X86.Open9.step (L.view s.x) = some ⟨c, m⟩ :=
      Silmaril.X86.Open9.step_of_listed hl hrip hfit hdec e
    exact mustG_step L hd hin (L.step hs) h
  | _ => intro h; exact h.elim

/-- **One listed `Open9` instruction of the image** (as `Proc.must_listed`). -/
theorem mustG_listed (L : Silmaril.X86.Open9.isa.Extends J) {W : World} {Q : GState τ → Prop}
    {s : GState τ} {base : Silmaril.X86.Word} {code : List Silmaril.X86.Byte}
    {Ls : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o l : Nat} {i : Silmaril.X86.Ext9.Instr}
    (hL : listingOk code Ls = true) (hlk : Ls.lookup o = some (i, l)) (hd : s.g.done = none)
    (hin : W.InImage (L.view s.x).core.rip.toNat) (hl : Silmaril.X86.Ext.Loaded (L.view s.x).memory base code)
    (hrip : (L.view s.x).core.rip = base + BitVec.ofNat 64 o)
    (h : WP (Silmaril.X86.Ext9.exec i (L.view s.x).core (L.view s.x).memory l)
      fun c m => MustG L W Q ⟨L.put s.x ⟨c, m⟩, s.g⟩) : MustG L W Q s := by
  have hm : (o, i, l) ∈ Ls := by
    clear hL h
    induction Ls with
    | nil => cases hlk
    | cons e Ls ih =>
      obtain ⟨o', x⟩ := e
      simp only [List.lookup_cons] at hlk
      by_cases he : o = o'
      · subst he; simp at hlk; subst hlk; simp
      · have : (o == o') = false := by simpa using he
        rw [this] at hlk
        exact List.mem_cons_of_mem _ (ih hlk)
  have := List.all_eq_true.mp hL _ hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact mustG_insn L hd hin hl hrip this.2 this.1 h


end Silmaril.Elf.Link.Dyn.ProcG
