module

public import Silmaril.Wasm.Component.Streams.Net.Defs

/-!
# The Boolean check of a network's well-formedness

`Network.check net = true` implies `net.WF`, so a concrete network is checked by evaluation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Net

open Silmaril.Wasm.Component.Streams.Net

theorem check_chans {net : Network} (h : net.check = true) (c : Nat) (hc : c < net.m) :
    (net.node (net.rd c)).inp = some c ∧ (net.node (net.wr c).1).outs[(net.wr c).2]? = some c ∧
      (net.wr c).1 ≠ net.rd c := by
  have h0 : _ ∧ _ := Bool.and_eq_true_iff.1 h
  have h1 := h0.1
  have h2 := List.all_eq_true.1 h1 c (List.mem_range.2 hc)
  have h3 : ((net.node (net.rd c)).inp = some c ∧ (net.node (net.wr c).1).outs[(net.wr c).2]? = some c)
      ∧ ¬(net.wr c).1 = net.rd c := by simpa using h2
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

theorem check_node {net : Network} (h : net.check = true) (i : Fin net.k) :
    (∀ c, (net.node i).inp = some c → c < net.m ∧ net.rd c = i) ∧
      (∀ j c, (net.node i).outs[j]? = some c → c < net.m ∧ net.wr c = (i, j)) := by
  have h0 : _ ∧ _ := Bool.and_eq_true_iff.1 h
  have h1 := h0.2
  have h2 := List.all_eq_true.1 h1 i (List.mem_finRange i)
  have h3 : _ ∧ _ := Bool.and_eq_true_iff.1 h2
  refine ⟨fun c hc => ?_, fun j c hj => ?_⟩
  · have h4 := h3.1
    rw [hc] at h4
    simpa using h4
  · have hj' : j < (net.node i).outs.length := (List.getElem?_eq_some_iff.1 hj).1
    have h4 := List.all_eq_true.1 h3.2 j (List.mem_range.2 hj')
    rw [hj] at h4
    simpa using h4

/-- **A network that passes the check is well formed.** -/
theorem Network.WF.of_check {net : Network} (h : net.check = true) : net.WF where
  rd_inp c hc := (check_chans h c hc).1
  wr_out c hc := (check_chans h c hc).2.1
  inp_rd i c hi := (check_node h i).1 c hi
  out_wr i j c hj := (check_node h i).2 j c hj
  no_loop c hc := (check_chans h c hc).2.2

end Silmaril.Proofs.Wasm.Component.Streams.Net
