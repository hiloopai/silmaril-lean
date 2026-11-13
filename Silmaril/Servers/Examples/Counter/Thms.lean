module

public import Silmaril.Servers.Examples.Counter.Defs
public import Silmaril.Servers.Core.Thms

/-!
# A counter server: theorems

`overlap` is linearizable with respect to the counter (`overlap_lin`), by the linearization
points `b` then `a`; `early` is not (`early_not_lin`), by `Sen.lin_seq_iff`: a sequential use
is linearizable only when its history is the counter's. Both are about every server that
refines the counter's atomic-handler server (`Model.sat_lin_of_refines_server`).
-/

@[expose] public section

namespace Silmaril.Servers.Examples.Counter

theorem overlap_lin : Sen.lin (counter.Hist 0) overlap := by
  refine ⟨[.ev (.recv a ()), .ev (.recv b ()), .lin b () (0 : Nat), .ev (.send b (0 : Nat)),
    .lin a () (1 : Nat), .ev (.send a (1 : Nat))], ?_, rfl, ⟨2, ?_⟩⟩
  · exact ⟨_, .cons (.recv rfl) (.cons (.recv rfl)
      (.cons (.lin rfl) (.cons (.send rfl)
      (.cons (.lin rfl) (.cons (.send rfl) (.nil _))))))⟩
  · exact .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _))

theorem early_not_lin : ¬ Sen.lin (counter.Hist 0) early := by
  rw [early, Sen.lin_seq_iff _ (by simp)]
  rintro ⟨q, hr⟩
  cases hr with
  | cons h _ => exact absurd h.1 (by decide)

end Silmaril.Servers.Examples.Counter
