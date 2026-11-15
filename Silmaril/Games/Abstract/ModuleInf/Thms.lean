module

public import Silmaril.Games.Abstract.ModuleInf.Defs
import Silmaril.Proofs.Games.Abstract.ModuleInf.Basic

/-!
# Closing with productive runs inside one function: theorems

Proofs in `Silmaril.Proofs.Games.Abstract.ModuleInf`.

* `closeInf_subset_closeInfL`: `closeInfL` extends `closeInf`; `closeInfL_bot`: with no
  productive run inside a function it is `closeInf`; `closeInfL_mono`: monotone in them;
* `mem_closeInfL_of_open`: a resolved productive run of the called function is a productive
  run of the closure;
* `closeInfL_descends`, `closeInfL_descPath`: closed under a descent (path) in front, with
  its import calls in front of the stream;
* `substInf_append`: a resolved finite prefix in front of a resolved stream;
  `substInf_mono`: resolution is monotone in the closed module;
* stream bookkeeping: `streamAppend_nil`, `streamAppend_append`, `streamAppend_lt`,
  `streamAppend_ge`, `streamConcat_append`, `exists_streamConcat`, `unbounded_of_frequently`, `streamConcat_map`,
  `streamAppend_chain`, `streamConcat_of_chain`;
* `substInf_of_segments`: resolving segment by segment is resolving one choice per position.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.Shape

open Silmaril.Games

universe u

variable {sh : Shape.{u}}

theorem streamAppend_nil {α : Type u} (ω : Nat → α) : [] ++ω ω = ω :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.streamAppend_nil ω

theorem streamAppend_append {α : Type u} (l₁ l₂ : List α) (ω : Nat → α) :
    (l₁ ++ l₂) ++ω ω = l₁ ++ω (l₂ ++ω ω) :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.streamAppend_append l₁ l₂ ω

theorem streamAppend_lt {α : Type u} {l : List α} {ω : Nat → α} {i : Nat} (h : i < l.length) :
    (l ++ω ω) i = l[i] :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.streamAppend_lt h

theorem streamAppend_ge {α : Type u} {l : List α} {ω : Nat → α} {i : Nat} (h : l.length ≤ i) :
    (l ++ω ω) i = ω (i - l.length) :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.streamAppend_ge h

/-- A list of segments in front of a concatenation. -/
theorem streamConcat_append {α : Type u} {ls : List (List α)} {l : Nat → List α}
    {ω : Nat → α} (h : StreamConcat l ω) : StreamConcat (ls ++ω l) (ls.flatten ++ω ω) :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.streamConcat_append h

/-- Segments that are nonempty infinitely often have an unbounded concatenation. -/
theorem unbounded_of_frequently {α : Type u} (l : Nat → List α)
    (h : ∀ N, ∃ n, N ≤ n ∧ l n ≠ []) (M : Nat) : ∃ n, M ≤ ((List.range n).flatMap l).length :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.unbounded_of_frequently l h M

/-- An unbounded concatenation of segments is a stream. -/
theorem exists_streamConcat {α : Type u} (l : Nat → List α)
    (hu : ∀ N, ∃ n, N ≤ ((List.range n).flatMap l).length) : ∃ ν, StreamConcat l ν :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.exists_streamConcat l hu

theorem streamConcat_map {α β : Type u} (f : α → β) {l : Nat → List α} {ν : Nat → α}
    (h : StreamConcat l ν) : StreamConcat (fun n => (l n).map f) (fun i => f (ν i)) :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.streamConcat_map f h

/-- A chain of streams, each a segment in front of the next. -/
theorem streamAppend_chain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ω w (n + 1)) (n : Nat) :
    w 0 = ((List.range n).flatMap cs) ++ω w n :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.streamAppend_chain h n

theorem streamConcat_of_chain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ω w (n + 1))
    (hu : ∀ N, ∃ n, N ≤ ((List.range n).flatMap cs).length) : StreamConcat cs (w 0) :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.streamConcat_of_chain h hu

/-- **Segment-wise resolution is resolution, one choice per position.** -/
theorem substInf_of_segments {c : sh.ClosedMod} {u : Nat → List (Call (sh.E ⊕ₛ sh.self))}
    {q : Nat → List (Call sh.E)} {ν : Nat → Call (sh.E ⊕ₛ sh.self)} {ω : Nat → Call sh.E}
    (hs : ∀ n, SubstPre c (u n) (q n)) (hu : StreamConcat u ν) (hq : StreamConcat q ω) :
    SubstInf c ν ω :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.substInf_of_segments hs hu hq

/-- Resolution is monotone in the closed module. -/
theorem substInf_mono {c c' : sh.ClosedMod} (h : c ≤ c') {ν : Nat → Call (sh.E ⊕ₛ sh.self)}
    {ω : Nat → Call sh.E} (hs : SubstInf c ν ω) : SubstInf c' ν ω :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.substInf_mono h hs

/-- **A resolved prefix in front of a resolved stream.** -/
theorem substInf_append {c : sh.ClosedMod} {u : List (Call (sh.E ⊕ₛ sh.self))}
    {q : List (Call sh.E)} {ν : Nat → Call (sh.E ⊕ₛ sh.self)} {ω : Nat → Call sh.E}
    (hu : SubstPre c u q) (h : SubstInf c ν ω) : SubstInf c (u ++ω ν) (q ++ω ω) :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.substInf_append hu h

/-- **`closeInfL` extends `closeInf`.** -/
theorem closeInf_subset_closeInfL (m : sh.OpenMod) (mi : OpenInf sh) (f : sh.F) (s : sh.S)
    (a : sh.A f) : closeInf m f s a ⊆ closeInfL m mi f s a :=
  fun _ h => .inl h

/-- With no productive run inside a function, `closeInfL` is `closeInf`. -/
theorem closeInfL_bot (m : sh.OpenMod) (f : sh.F) (s : sh.S) (a : sh.A f) :
    closeInfL m (fun _ _ _ => ∅) f s a = closeInf m f s a :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.closeInfL_bot m f s a

/-- `closeInfL` is monotone in the productive runs inside functions. -/
theorem closeInfL_mono (m : sh.OpenMod) {mi mi' : OpenInf sh} (h : ∀ f s a, mi f s a ⊆ mi' f s a)
    (f : sh.F) (s : sh.S) (a : sh.A f) : closeInfL m mi f s a ⊆ closeInfL m mi' f s a := by
  rintro ω (hω | ⟨z, qs, ν, ω', hp, hν, hs, rfl⟩)
  · exact .inl hω
  · exact .inr ⟨z, qs, ν, ω', hp, h _ _ _ hν, hs, rfl⟩

/-- **A resolved productive run of the called function** is a productive run of the closure. -/
theorem mem_closeInfL_of_open {m : sh.OpenMod} {mi : OpenInf sh} {f : sh.F} {s : sh.S}
    {a : sh.A f} {ν : Nat → Call (sh.E ⊕ₛ sh.self)} {ω : Nat → Call sh.E} (hν : ν ∈ mi f s a)
    (h : SubstInf (close m) ν ω) : ω ∈ closeInfL m mi f s a :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.mem_closeInfL_of_open hν h

/-- **`closeInfL` is closed under a descent in front**: a productive run of the callee, after
the import calls of the descent. -/
theorem closeInfL_descends {m : sh.OpenMod} {mi : OpenInf sh} {x y : sh.self.Op}
    {q : List (Call sh.E)} {ω : Nat → Call sh.E} (hxy : Descends m (close m) x q y)
    (h : ω ∈ closeInfL m mi y.1 y.2.2 y.2.1) : q ++ω ω ∈ closeInfL m mi x.1 x.2.2 x.2.1 :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.closeInfL_descends hxy h

/-- **A finite descent path in front.** -/
theorem closeInfL_descPath {m : sh.OpenMod} {mi : OpenInf sh} {x z : sh.self.Op}
    {qs : List (Call sh.E)} {ω : Nat → Call sh.E} (hp : DescPath m (close m) x qs z)
    (h : ω ∈ closeInfL m mi z.1 z.2.2 z.2.1) : qs ++ω ω ∈ closeInfL m mi x.1 x.2.2 x.2.1 :=
  Silmaril.Proofs.Games.Abstract.ModuleInf.closeInfL_descPath hp h

end Silmaril.Games.Abstract.Shape
