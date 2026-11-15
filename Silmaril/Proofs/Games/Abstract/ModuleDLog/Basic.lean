module

public import Silmaril.Games.Abstract.ModuleDLog.Defs

/-!
# Closing with logged local divergence (proofs)

With an empty log, `closeDLog` is `closeDL`; off `div` it is `close`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.ModuleDLog

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape

universe u

variable {sh : Shape.{u}}

theorem substPre_nil {c : sh.ClosedMod} {q : List (Call sh.E)} (h : SubstPre c [] q) : q = [] := by
  cases h
  rfl

theorem closeDLog_nil (m : sh.OpenMod) (LD : sh.self.Op → Prop) :
    closeDLog m (fun z u => u = [] ∧ LD z) = closeDL m LD := by
  funext f s a
  ext y
  constructor
  · rintro (h | ⟨hy, z, qs, u, q, hp, ⟨rfl, hz⟩, hq, he⟩)
    · exact .inl h
    · obtain rfl := substPre_nil hq
      exact .inr ⟨hy, z, by simpa [he] using hp, hz⟩
  · rintro (h | ⟨hy, z, hp, hz⟩)
    · exact .inl h
    · exact .inr ⟨hy, z, y.1, [], [], hp, ⟨rfl, hz⟩, .nil, by simp⟩

theorem mem_closeDLog_of_ne_div {m : sh.OpenMod}
    {LDL : sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → Prop} {f : sh.F} {s : sh.S}
    {a : sh.A f} {y : CallBeh sh.E sh.S (sh.B f)} (hy : y.2 ≠ .div) :
    y ∈ closeDLog m LDL f s a ↔ y ∈ close m f s a :=
  ⟨fun h => h.elim (fun h => h.elim id fun h => absurd h.1 hy) fun h => absurd h.1 hy,
    fun h => .inl (.inl h)⟩

end Silmaril.Proofs.Games.Abstract.ModuleDLog
