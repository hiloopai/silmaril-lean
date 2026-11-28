module

public import Silmaril.Logic.ACL2.X86Run.Source

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run

open Recursive

/-- The integer projection and arithmetic laws needed on the negative-ZP branch, over a
total old model. The ZP hypothesis ranges over the entire value carrier. -/
structure CountLaws (M : Model old) where
  integer : M.primitives.Value → Option Int
  zp_nil : ∀ n, M.interpret zpSymbol (fun _ => n) = M.primitives.nil →
    ∃ i, integer n = some i ∧ 0 < i
  minus_one : integer (M.interpret minusOneSymbol Fin.elim0) = some (-1)
  add_integers : ∀ (xs : Fin 2 → M.primitives.Value) i j,
    integer (xs 0) = some i → integer (xs 1) = some j →
    integer (M.interpret addSymbol xs) = some (i + j)

/-- Negative integers and values without an integer projection receive rank zero. -/
def rank {M : Model old} (laws : CountLaws M) : Rank M declaration.members :=
  fun state =>
    let count := state.args ⟨0, by rw [member_arity state.symbol]; decide⟩
    ((laws.integer count).getD 0).toNat

def run {M : Model old} (laws : CountLaws M) (h : declaration.Terminates M (rank laws))
    (args : Env M 2) : M.primitives.Value :=
  declaration.interpret M (rank laws) h ⟨2, runSymbol, args⟩

end Silmaril.Logic.ACL2.X86Run
