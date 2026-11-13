module

public import Silmaril.Wasm.Jco.Fuse.Glue.Defs
public import Silmaril.Wasm.Component.Wiring.Thms

/-!
# Glue code: inlining is handler composition

* `Code.run_seq`: `c.seq k` runs `c`, then `k` on its results.
* `Code.run_inline`: inlining the bodies `lib` into `c` is interpreting the
  calls of `c` by `glueH lib`.
* `glueH_inline`: **fusing two glue modules is composing their handlers**:
  `glueH (code.map (Code.inline lib)) = (glueH lib).comp (glueH code)`.

All three are proved outright (no hypotheses): they are computations on the
free monad `Prog`.
-/

public section

namespace Silmaril.Wasm.Jco.Fuse

open Silmaril.Games
open Silmaril.Wasm.Component

/-- A trap continues as a trap. -/
theorem cont_none (k : List Flat → Prog sigU (Option Payload)) : cont k none = .pure none := rfl

/-- Binding a continuation of a non-flat answer traps. -/
theorem cont_bind (k : List Flat → Prog sigU (Option Payload))
    (f : Option Payload → Prog sigU (Option Payload)) (hf : f none = .pure none) (r : Option Payload) :
    (cont k r).bind f = cont (fun ys => (k ys).bind f) r := by
  rcases r with _ | (_ | _)
  · exact hf
  · rfl
  · exact hf

/-- Interpreting a continuation. -/
theorem cont_interp (h : Handler sigU sigU) (k : List Flat → Prog sigU (Option Payload))
    (r : Option Payload) :
    (cont k r).interp h = cont (fun ys => (k ys).interp h) r := by
  rcases r with _ | (_ | _) <;> rfl

namespace Code

/-- `c.seq k` runs `c`, then `k` on its results. -/
theorem run_seq (k : Code) : ∀ (c : Code) (xs : List Flat),
    (c.seq k).run xs = (c.run xs).bind (cont k.run)
  | .ret, _ => rfl
  | .trap, _ => rfl
  | .pick ix c, xs => by
    show (match pickVals ix xs with | some ys => (c.seq k).run ys | none => .pure none) =
      (match pickVals ix xs with | some ys => c.run ys | none => .pure none).bind (cont k.run)
    cases pickVals ix xs with
    | none => rfl
    | some ys => exact run_seq k c ys
  | .call j c, xs => by
    show Prog.call (j, Payload.flat xs) (cont (c.seq k).run) =
      Prog.call (j, Payload.flat xs) fun r => (cont c.run r).bind (cont k.run)
    congr 1
    funext r
    rw [cont_bind c.run (cont k.run) rfl]
    congr 1
    funext ys
    exact run_seq k c ys

/-- **Inlining is interpretation**: the calls of `c.inline lib` are those of
`c`, served by the bodies `lib`. -/
theorem run_inline (lib : List Code) : ∀ (c : Code) (xs : List Flat),
    (c.inline lib).run xs = (c.run xs).interp (glueH lib)
  | .ret, _ => rfl
  | .trap, _ => rfl
  | .pick ix c, xs => by
    show (match pickVals ix xs with | some ys => (c.inline lib).run ys | none => .pure none) =
      (match pickVals ix xs with | some ys => c.run ys | none => .pure none).interp (glueH lib)
    cases pickVals ix xs with
    | none => rfl
    | some ys => exact run_inline lib c ys
  | .call j c, xs => by
    have hk : cont (c.inline lib).run = fun r => (cont c.run r).interp (glueH lib) := by
      funext r
      rw [cont_interp]
      congr 1
      funext ys
      exact run_inline lib c ys
    show ((lib[j]?.getD .trap).seq (c.inline lib)).run xs =
      (glueH lib (j, .flat xs)).bind fun r => (cont c.run r).interp (glueH lib)
    have hg : glueH lib (j, .flat xs) = (lib[j]?.getD .trap).run xs := by
      unfold glueH
      cases lib[j]? <;> rfl
    rw [run_seq, hk, hg]

end Code

/-- **Fusing glue code is composing handlers.** -/
theorem glueH_inline (lib code : List Code) :
    glueH (code.map (Code.inline lib)) = (glueH lib).comp (glueH code) := by
  funext q
  obtain ⟨i, x⟩ := q
  show (match (code.map (Code.inline lib))[i]?, x with
      | some c, .flat xs => c.run xs | _, _ => .pure none) =
    (match code[i]?, x with | some c, .flat xs => c.run xs | _, _ => .pure none).interp (glueH lib)
  rw [List.getElem?_map]
  cases code[i]? with
  | none => rfl
  | some c =>
    cases x with
    | flat xs => exact Code.run_inline lib c xs
    | vals _ => rfl

end Silmaril.Wasm.Jco.Fuse
