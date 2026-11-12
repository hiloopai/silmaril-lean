module

public import Silmaril.Data.SepList.Defs
public import Silmaril.Data.Cells.Thms

/-!
# Encoded singly linked lists: push and pop

Generic in the pointer encoding (`SLinks.enc`), so the same lemmas serve glibc's safe-linked
tcache and fastbin lists (`PROTECT_PTR`) and plain lists.
-/

@[expose] public section

namespace Silmaril.Data.SepList

open Silmaril.Data

theorem _root_.Silmaril.Data.Frag.Disjoint.apart {x c : Cell} {f : Frag} (h : Frag.Disjoint [x] f) (hc : c ∈ f) :
    c.Apart x := fun b h1 h2 h3 h4 =>
  h b (by simp only [Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil];
          exact List.mem_range'.2 ⟨b - x.addr, by omega, by omega⟩)
    (Frag.mem_bytes hc h1 h2)

theorem slistPush : Task.seplist.slistPush := by
  intro K v a l hf _ hw hd hfit
  intro c hc
  simp only [slist, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact Cell.holds_store_self hfit hw
  · exact (Cell.holds_store_apart (d := ⟨a + K.link, K.ws, K.enc (a + K.link) (l.headD K.nil)⟩)
      ((hd.apart hc).of_eq rfl rfl rfl rfl)).2 (hf c hc)

theorem slistPop : Task.seplist.slistPop := by
  intro K v a l hf c hc
  exact hf c (List.mem_cons_of_mem _ hc)

end Silmaril.Data.SepList
