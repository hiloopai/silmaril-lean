module

public import Silmaril.Compiler.C.Sem.C1Mono.Defs
public import Silmaril.Compiler.C.Sem.ElabC0.Defs
@[expose] public section

/-!
# Checked structural realisation of C1 in Core

The first slice reuses the structural integer/global/call/control-flow translator
from `ElabC0`. Acceptance checks C1 itself, followed by the exact Core checker;
it never constructs Core from a computed source result. Memory syntax that the
translator cannot represent declines. This establishes faithful realisability,
not agreement with Cerberus's own elaboration.
-/

namespace Silmaril.Compile.C.Sem.ElabC1

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Core.Dynamics

/-- Structural syntax translation, independent of the execution checks. -/
def translate := ElabC0.translate

/-- Completed C1 runs have exactly their observed behaviour. -/
theorem c1_beh_eq {p : TypedProgram} {fuel : Nat} {o : Obs}
    (h : C1.run fuel p = .done o) : C1.beh p = {o} := by
  ext o'
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, why, hn⟩ | ⟨_, hn⟩)
    · have eq := C1.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
      rfl
    · have eq := C1.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
    · have eq := h.symm.trans (hn fuel)
      cases eq
  · rintro rfl
    exact C1.beh_of_done h

/-- The structural result is returned only after two exact observations agree. -/
def elaborate (p : TypedProgram) : Option Program := do
  if C1.check p != .ok () then none else do
    let q ← translate p
    let .done source := C1.run 100000 p | none
    let target ← Compile.Core.exactProgram 100000 q
    if source = target then some q else none

theorem elaborate_sound {p : TypedProgram} {q : Program}
    (h : elaborate p = some q) : C1.InFragment p ∧ Compile.Core.beh q = C1.beh p := by
  unfold elaborate at h
  split at h
  · contradiction
  · rename_i hc
    have fragment : C1.InFragment p := by simpa [C1.InFragment] using hc
    cases ht : translate p with
    | none => simp [ht] at h
    | some q' =>
      simp only [ht] at h
      cases hr : C1.run 100000 p <;> simp only [hr] at h
      all_goals try contradiction
      rename_i source
      cases he : Compile.Core.exactProgram 100000 q' with
      | none => simp [he] at h
      | some target =>
        simp only [Bind.bind, Option.bind, he] at h
        split at h
        · rename_i eq
          cases h
          exact ⟨fragment, (Compile.Core.exactProgram_sound he).trans
            (eq ▸ (c1_beh_eq hr).symm)⟩
        · contradiction

end Silmaril.Compile.C.Sem.ElabC1
