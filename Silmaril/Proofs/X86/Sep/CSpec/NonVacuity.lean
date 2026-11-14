module

public import Silmaril.Proofs.X86.Sep.CSpec.Bridge
public import Silmaril.X86.Sep.Xmm.Thms
public import Silmaril.X86.Sep.Demo.Thms
/-!
# Proofs: non-vacuity of the `toC` template

Behind `Silmaril/Machine/X86/Sep/CSpec/Thms.lean` (CP-10b review). Imports only headers and the
sibling proof module `Bridge`.

* `xmmsAny_xmapOf`: `xmmsAny rs` holds of the XMM map owning exactly `rs` (for `rs.Nodup`).
* `xholds_lift_xmmsAll`: an integer assertion that holds of a machine state, with all sixteen
  XMM registers beside it, holds of the XMM machine state.
* `leaf_toC_pre_satisfiable`: a concrete `XState` carries the leaf's code and its whole
  `FnSpec.toC` precondition (`CSpec.Pre`: the entry template with every XMM register, and
  the user precondition), from `Sep.Demo.leafSpec_pre_satisfiable`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepCSpec

open Silmaril.X86 (XReg MState Word)
open Silmaril.X86.Sse9 (XState XFile)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.CSpec

/-- The XMM map owning exactly `rs`, with values from `v`. -/
def xmapOf (rs : List XReg) (v : XFile) : XMap := fun r => if r ∈ rs then some (v r) else none

theorem xmmsAny_xmapOf (v : XFile) : ∀ rs : List XReg, rs.Nodup →
    xmmsAny rs (PMap.empty, xmapOf rs v)
  | [], _ => by
    show _ = XFrag.empty
    exact Prod.ext rfl (funext fun _ => rfl)
  | r :: rs, hn => by
    have hr : r ∉ rs := (List.nodup_cons.1 hn).1
    refine ⟨(PMap.empty, PMap.single r (v r)), (PMap.empty, xmapOf rs v),
      ⟨PMap.disjoint_empty_left _, fun a => ?_⟩, ?_, ⟨v r, rfl, rfl⟩,
      xmmsAny_xmapOf v rs (List.nodup_cons.1 hn).2⟩
    · by_cases e : a = r
      · subst e; exact .inr (by simp [xmapOf, hr])
      · exact .inl (by simp [PMap.single, e])
    · refine Prod.ext (PMap.empty_union _).symm (funext fun a => ?_)
      by_cases e : a = r
      · subst e; simp [xmapOf, XFrag.union, PMap.union, PMap.single]
      · simp [xmapOf, XFrag.union, PMap.union, PMap.single, e]

theorem allXRegs_nodup : allXRegs.Nodup := by decide

theorem mem_allXRegs (r : XReg) : r ∈ allXRegs := by cases r <;> decide

/-- An integer assertion that holds of `m`, with all sixteen XMM registers beside it. -/
theorem xholds_lift_xmmsAll {P : SProp} {m : MState} (v : XFile) (hp : Holds P m) :
    XHolds (lift P ∗ₓ xmmsAny allXRegs) ⟨m, v⟩ := by
  obtain ⟨h, hp, hl⟩ := hp
  refine ⟨XFrag.union (h, PMap.empty) (PMap.empty, xmapOf allXRegs v),
    ⟨_, _, ⟨PMap.disjoint_empty_right h, PMap.disjoint_empty_left _⟩, rfl, ⟨hp, rfl⟩,
      xmmsAny_xmapOf v _ allXRegs_nodup⟩, ?_, ?_⟩
  · show PMap.Le (PMap.union h PMap.empty) (toFrag m)
    rw [PMap.union_empty]; exact hl
  · intro r w e
    simp only [XFrag.union, PMap.empty_union, xmapOf, mem_allXRegs, ite_true] at e
    cases e; rfl

/-- **Non-vacuity of the `toC` template**: a concrete XMM machine state carries the leaf's
code and its whole `FnSpec.toC` precondition. -/
theorem leaf_toC_pre_satisfiable : ∃ x : XState,
    XHolds (↑ₓ(codePt (0x400000 : Word).toNat Silmaril.X86.Leaf.bytes) ∗ₓ
      Silmaril.X86.Sep.Demo.leafSpec.toC.Pre ((2 : Word), (3 : Word)) 0x400000
        ⟨0x7000, 0x401000⟩) x := by
  obtain ⟨m, h, hp, hl⟩ := Silmaril.X86.Sep.Demo.leafSpec_pre_satisfiable
  refine ⟨⟨m, fun _ => 0⟩, ?_⟩
  have e := toC_pre Silmaril.X86.Sep.Demo.leafSpec ((2 : Word), (3 : Word)) 0x400000
    ⟨0x7000, 0x401000⟩
  simp only at e
  rw [e, ← xsep_assoc, ← lift_sep]
  exact xholds_lift_xmmsAll _ ⟨h, hp, hl⟩

end Silmaril.Proofs.X86.SepCSpec
