module

public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLink

/-!
# The reference-side conditions of the litmus `dblFwdL`

`dblFwdL_wireTy`: the doubler's export `g` answers `fwdS`'s import `g` at the same type;
`dblFwdL_namesOk`: the export names `g` and `f` are no generated type names (`tag "t" n` has
length `n + 1`, so only `tag "t" 0 = "t"` has length one).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus

/-- The generated name `tag p n` has `n` more characters than `p`. -/
theorem tag_length (p : String) : ∀ n, (tag p n).length = p.length + n
  | 0 => rfl
  | n + 1 => by rw [tag, String.length_push, tag_length p n, Nat.add_assoc]

/-- A one-character name other than `"t"` is no generated type name. -/
theorem ne_tag_t {s : String} (hl : s.length = 1) (ht : s ≠ "t") (n : Nat) : s ≠ tag "t" n := by
  intro e
  have hn : (tag "t" n).length = 1 + n := tag_length "t" n
  rw [← e, hl] at hn
  have h0 : n = 0 := by omega
  subst h0
  exact ht e

theorem dblFwdL_wireTy : dblFwdL.WireTy := by
  refine ⟨rfl, fun k w hk => ?_⟩
  match k, hk with
  | 0, hk =>
    have hw : w = 0 := (Option.some.inj hk).symm
    subst hw
    exact ⟨_, rfl, rfl⟩

theorem dblFwdL_namesOk : dblFwdL.NamesOk := by
  refine ⟨fun x hx n => ?_, fun x hx n => ?_⟩
  · have hx' : x = ⟨"g", ⟨[.u32], [.u32]⟩, 0⟩ := List.mem_singleton.1 hx
    rw [hx']
    exact ne_tag_t rfl (by decide) n
  · have hx' : x = ⟨"f", ⟨[.u32], [.u32]⟩, 0⟩ := List.mem_singleton.1 hx
    rw [hx']
    exact ne_tag_t rfl (by decide) n

end Silmaril.Proofs.Wasm.Component.Reference
