module

public import Silmaril.Cli.Io.Echon.Defs
public import Silmaril.Cli.Io.Command.Thms

/-!
# `echon` satisfies its specification; its check is sound

* **`echon_sat`**: `echonProg.Sat echonSpec`, by `Prog.sat_ofCommandCore_iff`.
* **`echonCheck_sound`**: by `Command.check_sound`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io.Echon

open Silmaril.Cli Silmaril.Cli.Io

/-- **`echon` satisfies its specification.** -/
theorem echon_sat : echonProg.Sat echonSpec :=
  (Prog.sat_ofCommandCore_iff _ _ _).2 fun i _ _ => by
    rw [Result.obs_nil _ _ _ _ _ rfl]
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, rfl⟩

/-- **`echon`'s check is sound.** -/
theorem echonCheck_sound : echonCheck.Sound echonSpec :=
  Command.check_sound _ fun m i s h => by
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨hx, ho⟩, he⟩, hf⟩ := h
    have hfs : s.fs i = i.fs := by
      funext q
      simp [Snap.fs, hf]
    exact ⟨{ stdout := echonLine m, fs := i.fs }, ⟨ho.symm, he.symm, hx.symm, hfs.symm⟩,
      rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

end Silmaril.Cli.Io.Echon

end
