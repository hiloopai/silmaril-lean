module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Rules

@[expose] public section

/-!
# A while loop in the every-run logic

The hint scan of the LRAT checker is `block (loop (cond; br_if 1; body; br 0))`, entered and
left on an empty operand stack. `w_while` proves it from an invariant `Inv` on the store and the
frame: every iteration from `Inv` ends with `br 1` (leave: the continuation must be safe) or
`br 0` (repeat: `Inv` again), stated by the postcondition `whilePost`. Partial correctness
(Löb induction through `Hoare.HWP.loop`); every profile and host relation.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {rs : List Val} {rest : List Admin} {Q : Post H}

/-- The postcondition of one iteration of the loop: `br 0` (to the loop) needs the invariant,
`br 1` (out of the block) needs the continuation. -/
def whilePost (P : Profile) (host : HostSemantics H) (Inv : Store H → Frame → Prop)
    (rest : List Admin) (Q : Post H) : Post H :=
  loopPost 0 [] (fun s f vs => vs = [] ∧ Inv s f) (labelPost P host 0 [] [] (seqPost P host rest Q))

/-- `br_if`, on the top-first stack. -/
theorem w_brIf {c : BitVec 32} {l : LabelIdx}
    (h₁ : c ≠ 0 → HWP P host s f (vals rs.reverse ++ .plain (.br l) :: rest) Q)
    (h₂ : c = 0 → HWP P host s f (vals rs.reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 c :: rs).reverse ++ .plain (.brIf l) :: rest) Q := by
  rw [vals_rev_push]
  exact HWP.brIf h₁ h₂

/-- `br l` exits with a branch outcome. -/
theorem w_br {l : LabelIdx} (h : Q s f (.br l.toNat rs.reverse)) :
    HWP P host s f (vals rs.reverse ++ .plain (.br l) :: rest) Q :=
  HWP.of_exits (o := .br l.toNat rs.reverse) ⟨l, rest, rfl, rfl⟩ h

/-- Leaving the loop through `br 1`. -/
theorem whilePost_exit {Inv : Store H → Frame → Prop}
    (h : HWP P host s f (vals ([] : List Val).reverse ++ rest) Q) :
    whilePost P host Inv rest Q s f (.br 1 ([] : List Val).reverse) := by
  show labelPost P host 0 [] [] (seqPost P host rest Q) s f (.br 0 ([] ++ []))
  refine ⟨[], [], rfl, rfl, ?_⟩
  exact HWP.of_vals (vs := []) (by simpa [seqPost] using h)

/-- Repeating the loop through `br 0`. -/
theorem whilePost_cont {Inv : Store H → Frame → Prop} (h : Inv s f) :
    whilePost P host Inv rest Q s f (.br 0 ([] : List Val).reverse) :=
  ⟨[], [], rfl, rfl, rfl, h⟩

/-- **The while loop.** -/
theorem w_while {Inv : Store H → Frame → Prop} {body : List Instr} (hI : Inv s f)
    (hbody : ∀ s f, Inv s f →
      HWP P host s f (vals ([] : List Val).reverse ++ expression body) (whilePost P host Inv rest Q)) :
    HWP P host s f (vals ([] : List Val).reverse ++
      .plain (.block .empty [.loop .empty body]) :: rest) Q := by
  have hb := HWP.block (P := P) (host := host) (s := s) (f := f) (us := []) (vs := [])
    (t₁ := []) (t₂ := []) (bt := .empty) (body := [.loop .empty body]) (rest := rest) (Q := Q)
    rfl rfl ?_
  · simpa using hb
  · have hl := HWP.loop (P := P) (host := host) (us := []) (t₁ := []) (t₂ := []) (bt := .empty)
      (body := body) (Q := labelPost P host 0 [] [] (seqPost P host rest Q))
      (Inv := fun s f vs => vs = [] ∧ Inv s f) (fun _ _ _ _ => rfl)
      (fun _ _ _ h => by rw [h.1]; rfl) (fun s f vs h => by
        rw [h.1]; simpa [whilePost] using hbody s f h.2) (s := s) (f := f) (vs := []) ⟨rfl, hI⟩
    simpa [expression] using hl

end Silmaril.Wasm.Examples.LRAT
