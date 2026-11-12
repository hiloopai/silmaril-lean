module

public import Silmaril.Cli.Spec.Sha256sum.Defs
public import Silmaril.Cli.Institution.Thms

/-!
# The standard `sha256sum` specification: relations between its levels

PROVED (standard axioms):

* `spec_anti`: a smaller domain is a weaker specification;
* `readOf_empty`, `world_embed_cmd`: an `L2` invocation's default expansion is the world
  `worldCmd` (no environment, every operand missing);
* **`spec_le_lift_stdin`**: the `L3` specification on `Dom.stdin` refines the lift of the `L1`
  sentence `stdin` (silmaril's `Sys.sha256sum_stdin`);
* **`spec_le_lift_cmd`**, `spec_le_lift_cmdOn`: the `L3` specification refines the lift of the
  `L2` sentence `cmd` (on every domain containing the default expansions);
  `dom_mixed_embed`: the `L2` file-error tier `Dom2.missing` lies in `Dom.mixed`.

So an implementation proved against `spec conv D` at `L3` meets `stdin` and `cmd` through its
`L1` and `L2` reducts (`Level.sat_lift_iff`).
-/

@[expose] public section

namespace Silmaril.Cli.Spec.Sha256sum

open Silmaril.Cli.Institution (Level Sen Out1 In2)

theorem spec_anti (conv : PathConv) {D D' : Dom} (h : ∀ i, D' i → D i) :
    spec conv D ≤ spec conv D' :=
  fun i _ H hD => H (h i hD)

/-- An invocation without files: every operand is missing. -/
theorem readOf_empty (conv : PathConv) (i : Input) (hi : i.fs = Fs.empty) (p : List UInt8) :
    readOf conv i p = .openErr .ENOENT := by
  unfold readOf; rw [hi]; cases conv p <;> rfl

theorem world_embed_cmd (conv : PathConv) (a : In2) :
    world conv (Level.full.inProj (Level.command.embed a)) = worldCmd a := by
  simp only [world, worldCmd, Level.inProj, Level.embed]
  congr 1
  funext p
  exact readOf_empty conv _ rfl p

/-- **`L3` refines `L1` on standard input.** -/
theorem spec_le_lift_stdin (conv : PathConv) : spec conv Dom.stdin ≤ Level.lift stdin := by
  intro i o H s hs
  subst hs
  obtain ⟨h1, -, h3, -⟩ := H rfl
  have e : outcome conv (Level.full.inProj (Level.stream.embed s)) =
      { stdout := Silmaril.Apps.Sha256sum.Sys.stdinRecord s, stderr := [], status := 0 } :=
    Silmaril.Apps.Sha256sum.Sys.sha256sum_stdin _ _ _ _
  rw [e] at h1 h3
  exact ⟨h1, h3⟩

/-- **`L3` refines `L2`** on every domain containing the default expansions of `D2`. -/
theorem spec_le_lift_cmdOn (conv : PathConv) {D : Dom} {D2 : In2 → Prop}
    (h : ∀ a, D2 a → D (Level.full.inProj (Level.command.embed a))) :
    spec conv D ≤ Level.lift (cmdOn D2) := by
  intro i o H a ha hD
  subst ha
  obtain ⟨h1, h2, h3, -⟩ := H (h a hD)
  simp only [outcome, world_embed_cmd] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **`L3` refines `L2`.** -/
theorem spec_le_lift_cmd (conv : PathConv) : spec conv Dom.all ≤ Level.lift cmd := by
  intro i o H a ha
  exact spec_le_lift_cmdOn conv (D2 := fun _ => True) (fun _ _ => trivial) i o H a ha trivial

/-- The `L2` file-error tier lies in the `L3` one. -/
theorem dom_mixed_embed (conv : PathConv) (a : In2) (h : Dom2.missing a) :
    Dom.mixed conv (Level.full.inProj (Level.command.embed a)) := by
  refine ⟨h.1, fun x hx => ⟨(h.2 x hx).1, .inr ⟨?_, (h.2 x hx).2⟩⟩⟩
  rintro ⟨d, hd⟩
  cases hc : conv (utf8 x) <;> simp [hc, Level.inProj, Level.embed, Fs.empty] at hd

end Silmaril.Cli.Spec.Sha256sum
