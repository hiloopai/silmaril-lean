module

public import Silmaril.Wasm.JcoTool.LayoutRef.Defs
public import Silmaril.Wasm.JcoTool.Layout.Thms
public import Silmaril.Proofs.Wasm.JcoTool.LayoutRef.Read
public import Silmaril.Wasm.Component.Reference.Thms
public import Silmaril.Wasm.Perf.CoreDecode.Thms
public import Silmaril.Wasm.Perf.ValidateComp.Thms

/-!
# The layout reading on the reference component syntax: theorems

Proofs in `Silmaril.Proofs.Wasm.JcoTool.LayoutRef.{Spaces,Read}`.

* **`read_toRef`**: for a parsed output `x` that translates to the reference component `c`
  (`toRef rd x = some c`, any reader `rd` of core modules), `Layout.read names x` is
  `readRef names c`: the layout reading is a reading of the reference syntax.
* **`spacesRef_sizes`**: the five index spaces `readRef` fills (core functions, core instances,
  functions, instances, types) have the sizes of the reference's index spaces,
  `Component.nextIndex` (`Builder.lean`, `Explainer.md` §Index Spaces): entry `i` of a space is
  the `i`-th definition of that sort.
* **`ToolV.refCheck_valid`**: bytes the reference validator accepts (`ToolV.refCheck`:
  `Reference.check?` with every feature gate, on the bytes read as a `Core3Component` with
  silmaril's verified decoder for the core modules) are a valid reference component
  (`Reference.Valid`, by `Reference.check?_sound`) whose reading is `Layout.read`'s.
  `wasm-jco new` reports the verdict (`reference-valid: yes|no`) and `wasm-jco validate`
  prints it.
* **`ToolV.newFullR_correct`**: the correctness theorem of `wasm-jco new` with the output read
  as a reference component: `newFullL_correct`, and for worlds outside an earlier fragment the
  bytes parse to `x`, `x` translates to a reference component `c`, and `readRef` of `c` is the
  layout the world describes (`Layout.expected` of the plan).

This is still translation validation for the emitter `NewI.emit` (the tool checks the layout
of every output and refuses an output that fails), now stated over the syntax the reference
semantics is defined on; it says how the output's definitions are wired (which core export
each export lifts, what defines each core import), not that the reference machine runs them
as the world's functions.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.LayoutRef

open Silmaril.Wasm.Component (Syntax.Component)

/-- **The layout reading is a reading of the reference syntax.** -/
theorem read_toRef {M : Type} {rd : ByteArray → Option M} {x : XComp} {c : Syntax.Component M}
    (h : toRef rd x = some c) (names : List (String × String)) :
    Layout.read names x = readRef names c := by
  rw [readRef, spacesRef_toRef h, readRS_map]

/-- **The spaces of the reading are the reference's index spaces.** -/
theorem spacesRef_sizes {M : Type} (c : Syntax.Component M) :
    (spacesRef c).cf.size = Syntax.Component.nextIndex (.core .func) c ∧
      (spacesRef c).ci.size = Syntax.Component.nextIndex (.core .instance_) c ∧
      (spacesRef c).ff.size = Syntax.Component.nextIndex .func c ∧
      (spacesRef c).ii.size = Syntax.Component.nextIndex .instance_ c ∧
      (spacesRef c).tt.size = Syntax.Component.nextIndex .type c := by
  have h := foldl_sizes c {}
  simpa [spacesRef] using h

end Silmaril.Wasm.JcoTool.LayoutRef

namespace Silmaril.Wasm.JcoTool.ToolV

open Silmaril.Wasm.Wit.Binary (WorldFull)
open New (bind_ok)
open Layout

theorem refOf_ok {o : Tool.Out} {c : Silmaril.Wasm.Component.Syntax.Component ByteArray}
    (h : refOf o = .ok c) : ∃ x, xparse o.bytes = .ok x ∧ LayoutRef.toRef some x = some c := by
  unfold refOf at h
  split at h
  · cases h
  · rename_i x hx
    split at h
    · rename_i c' hc
      cases h
      exact ⟨x, hx, hc⟩
    · cases h

/-- **The correctness theorem of `wasm-jco new`** (thin wrapper), with the output read as a
reference component. -/
theorem newFullR_correct {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newFullR core wf = .ok o) :
    ∃ o', ToolI.newFull core wf = .ok o' ∧ Checked o o' ∧
      ((ToolI.inOld wf.world = true ∧ Tool.newWith core wf.world = .ok o') ∨
        (ToolI.inOld wf.world = false ∧ ToolI.NewIOk core wf o' ∧
          ∃ p x c, NewI.plan core wf = .ok p ∧ xparse o.bytes = .ok x ∧
            LayoutRef.toRef some x = some c ∧
            LayoutRef.readRef p.mod.importNames c = some (expected p))) := by
  obtain ⟨o₁, h₁, h₂⟩ := bind_ok h
  obtain ⟨c, hc, h₃⟩ := bind_ok h₂
  cases h₃
  obtain ⟨x₀, hx₀, ht⟩ := refOf_ok hc
  obtain ⟨o', ho, hch, hcase⟩ := newFullL_correct h₁
  refine ⟨o', ho, hch, ?_⟩
  rcases hcase with hold | ⟨hw, hok, p, x, hp, hx, hr⟩
  · exact .inl hold
  · have hxx : x = x₀ := by
      rw [hx] at hx₀
      exact Except.ok.inj hx₀
    subst hxx
    exact .inr ⟨hw, hok, p, x, c, hp, hx, ht, (LayoutRef.read_toRef ht _) ▸ hr⟩

theorem refCore3_ok {b : ByteArray} {c : Silmaril.Wasm.Component.Reference.Core3Component}
    (h : refCore3 b = .ok c) :
    ∃ x, xparse b = .ok x ∧ LayoutRef.toRef Silmaril.Wasm.Binary.Core.decode? x = some c := by
  unfold refCore3 at h
  rw [Silmaril.Wasm.Perf.CoreDecode.decodeF_eq] at h
  split at h
  · cases h
  · rename_i x hx
    split at h
    · rename_i c' hc
      cases h
      exact ⟨x, hx, hc⟩
    · cases h

/-- **The reference validator's verdict is sound**: bytes that `refCheck` accepts parse to a
component `x` whose translation `c` (core modules decoded by silmaril's verified decoder) is
valid in the reference's validation relation at the type `ct`, and `Layout.read` of `x` is
`readRef` of `c`. -/
theorem refCheck_valid {b : ByteArray} {ct : Silmaril.Wasm.Component.Reference.ComponentType}
    (h : refCheck b = .ok ct) :
    ∃ x c, xparse b = .ok x ∧ LayoutRef.toRef Silmaril.Wasm.Binary.Core.decode? x = some c ∧
      Silmaril.Wasm.Component.Reference.Valid Silmaril.Wasm.Component.Features.all c ct ∧
      ∀ names, Layout.read names x = LayoutRef.readRef names c := by
  obtain ⟨c, hc, h₂⟩ := bind_ok h
  obtain ⟨x, hx, ht⟩ := refCore3_ok hc
  rw [Silmaril.Wasm.Perf.ValidateR.checkCore3R_eq] at h₂
  have hv : Silmaril.Wasm.Component.Reference.check? Silmaril.Wasm.Component.Features.all c = .ok ct := by
    revert h₂
    cases Silmaril.Wasm.Component.Reference.check? Silmaril.Wasm.Component.Features.all c with
    | ok ct' => intro h₂; cases h₂; rfl
    | error e => intro h₂; cases h₂
  exact ⟨x, c, hx, ht, Silmaril.Wasm.Component.Reference.check?_sound hv,
    fun names => LayoutRef.read_toRef ht names⟩

end Silmaril.Wasm.JcoTool.ToolV
