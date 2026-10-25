module

public import Silmaril.Wasm.Binaryen.DirectizeRun
public import Silmaril.Wasm.Binaryen.Pass.DirectizeInitPrefix

@[expose] public section

/-! # Profile-generic Directize initialisation reachability

Element initialisation makes no numerical choice. Its two stores can therefore
reach the same active code and frame at an arbitrary numerical profile. Each
path is certified by actual forced initialization steps, with the harmless
overlap of absorbing trap cleanup handled separately. The suffix can retain all
its nondeterministic numerical choices. These certificates support observation
transport; arbitrary reachability alone would not justify that transport.
-/

namespace Silmaril.Wasm.Binaryen.DirSim

open Execution.Core Numerics

variable {H : Type}

/-- Initialisation reaches identical active code/frame and the Directize invariant,
or both initialisations trap. The rewritten function stores remain related. -/
def InitAligned (P : Profile) (ok : SiteOk) (mi : ModuleInst)
    (c c' : Config H) : Prop :=
  (∃ cm cm', InitPrefix.Prefix P c cm ∧ InitPrefix.Prefix P c' cm' ∧
    cm.frame = cm'.frame ∧ cm.code = cm'.code ∧
    SR ok mi cm.store cm'.store ∧ FInv ok mi cm) ∨
  (∃ x x', InitPrefix.Prefix P c x ∧ InitPrefix.Prefix P c' x' ∧
    x.code = [.trap] ∧ x'.code = [.trap])

/-- Retain the existing deterministic initialisation API as a specialization. -/
theorem InitAligned.toPre {o : GrowKind → Nat → Nat → Nat → Bool}
    {ok : SiteOk} {mi : ModuleInst} {c c' : Config H}
    (h : InitAligned (Profile.deterministic o) ok mi c c') : Pre ok mi o c c' := by
  rcases h with ⟨cm, cm', hm, hm', hfr, hcode, hSR, hinv⟩ | ht
  · exact .inl ⟨cm, cm', hm.steps, hm'.steps, ⟨hfr, hcode ▸ GL.refl _⟩, hSR, hinv⟩
  · obtain ⟨x, x', hx, hx', hxc, hxc'⟩ := ht
    exact .inr ⟨x, x', hx.steps, hx'.steps, hxc, hxc'⟩

end Silmaril.Wasm.Binaryen.DirSim
