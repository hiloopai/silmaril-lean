module

public import Silmaril.Games.Abstract.Module.Defs
import Silmaril.Proofs.Games.Abstract.Module.Basic

/-!
# Abstract modules: theorems

* `close_mono`: closing is monotone in the open module.
* `resolve_close`: the closed module is a fixpoint of resolution, so each
  closed function's behaviours are its open behaviours with internal calls
  answered by closed behaviours.
* `close_lift`: a module with no internal calls closes to itself. Concrete
  modules whose internal calls are already resolved (Core 3.0 under its store
  semantics) are of this kind.
* `sup_close_le` and `exists_close_not_sup`: the join of closed modules is
  below the closure of the join, and strictly below in general. If one module
  provides `g` and another a function `f` that calls `g`, their join closes to
  an `f` that returns, while neither closes to one. Joins of modules of a
  fixed shape must therefore be taken on open modules and then closed. The
  pointwise join of closed modules is not the closure of anything that links.

**Least fixpoint against divergence (audit).** `close` keeps only finite
derivations. A callee's `div` propagates, but an unproductive recursion is
not detected:

* `exists_close_omits_div`: `f` calling itself closes to the empty set, so
  it has no `div` behaviour.
* `closeD` adds `div` after the import calls of every infinite internal-call
  chain with finitely many import calls. It observes that recursion
  (`exists_closeD_observes_rec_div`), extends `close` (`close_le_closeD`),
  and agrees with it when there are no internal calls (`closeD_lift`).
* Not represented: chains with infinitely many import calls, which are
  infinite productive runs.

No theorem yet says that `closeD` agrees with an operational semantics with
recursion, or that `close` / `closeD` are congruences for the
outcome-sensitive equivalences. Results about outcome-sensitive equivalence
of closed modules must not be inferred from these definitions.
-/

public section

namespace Silmaril.Games.Abstract.Shape

universe u

variable {sh : Shape.{u}}

/-- Closing is monotone. -/
theorem close_mono {m m' : sh.OpenMod} (h : m ≤ m') : close m ≤ close m' :=
  Silmaril.Proofs.Games.Abstract.Module.close_mono h

/-- The closed module is a fixpoint of resolution. -/
theorem resolve_close (m : sh.OpenMod) : resolve m (close m) = close m :=
  Silmaril.Proofs.Games.Abstract.Module.resolve_close m

/-- A module with no internal calls closes to itself. -/
theorem close_lift (c : sh.ClosedMod) : close (lift c) = c :=
  Silmaril.Proofs.Games.Abstract.Module.close_lift c

/-- The join of closed modules is below the closure of the join. -/
theorem sup_close_le (m m' : sh.OpenMod) : close m ⊔ close m' ≤ close (m ⊔ m') :=
  Silmaril.Proofs.Games.Abstract.Module.sup_close_le m m'

open Silmaril.Proofs.Games.Abstract.Module in
/-- Closing does not commute with joins. -/
theorem exists_close_not_sup :
    ∃ (sh : Shape.{0}) (m m' : sh.OpenMod), close m ⊔ close m' ≠ close (m ⊔ m') :=
  ⟨sh₀, m₁, m₂, close_not_sup⟩

open Silmaril.Proofs.Games.Abstract.Module in
/-- The least fixpoint omits divergence by unbounded recursion: a function
calling itself closes to no behaviour at all. -/
theorem exists_close_omits_div :
    ∃ (sh : Shape.{0}) (m : sh.OpenMod) (f : sh.F) (s : sh.S) (a : sh.A f),
      close m f s a = ∅ ∧ (∃ x ∈ m f s a, x.1 ≠ []) :=
  ⟨sh₀, m₃, true, ⟨⟩, ⟨⟩, by rw [close_m₃]; rfl, ⟨_, rfl, by simp⟩⟩

open Silmaril.Proofs.Games.Abstract.Module in
/-- Closing with divergence observes that recursion. -/
theorem exists_closeD_observes_rec_div :
    ∃ (sh : Shape.{0}) (m : sh.OpenMod) (f : sh.F) (s : sh.S) (a : sh.A f),
      close m f s a = ∅ ∧ ([], End.div) ∈ closeD m f s a :=
  ⟨sh₀, m₃, true, ⟨⟩, ⟨⟩, by rw [close_m₃]; rfl, div_mem_closeD_m₃⟩

/-- Closing with divergence extends closing. -/
theorem close_le_closeD (m : sh.OpenMod) : close m ≤ closeD m :=
  Silmaril.Proofs.Games.Abstract.Module.close_le_closeD m

/-- Without internal calls, closing with divergence is the identity. -/
theorem closeD_lift (c : sh.ClosedMod) : closeD (lift c) = c :=
  Silmaril.Proofs.Games.Abstract.Module.closeD_lift c

end Silmaril.Games.Abstract.Shape
