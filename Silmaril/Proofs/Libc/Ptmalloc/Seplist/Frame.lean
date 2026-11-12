module

public import Silmaril.Libc.Ptmalloc.Rep.Defs
public import Silmaril.Data.Cells.Thms

/-!
# ptmalloc, representation: the local frame

`Seplist.localFrame`: a body that changes only the calling thread's part (the tcache paths)
re-establishes `LocalRep` from the new thread fragment, the arena's and the shared fragments
being framed by `Silmaril.Data.Frag.holds_frame`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Seplist

open Silmaril.Data

theorem localFrame : Task.seplist.localFrame := by
  intro C L St T l l' v v' h hav hav' hsh hag hbk ft' hft hnd
  unfold LocalRep at h ⊢
  rw [hav, hav', hsh]
  obtain ⟨hfa, _, hfs, _, _⟩ := h
  rw [Frag.bytes_append] at hag
  exact ⟨Frag.holds_frame hfa fun a ha => hag a (List.mem_append_left _ ha), hft,
    Frag.holds_frame hfs fun a ha => hag a (List.mem_append_right _ ha), hbk, hnd⟩

/-- **The executable check is sound**: `LocalRep.check = true` on a memory dump gives
`LocalRep`. -/
theorem localRep_of_check {C : Config} {L : Layout} {St : Statics} {T : TlsAddrs} {l : Local}
    {v : MemView} (h : LocalRep.check C L St T l v = true) : LocalRep C L St T l v := by
  unfold LocalRep.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, Frag.sep_of_sepB h5⟩

end Silmaril.Libc.Ptmalloc.Seplist
