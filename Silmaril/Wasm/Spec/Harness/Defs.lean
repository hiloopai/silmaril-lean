module

public import Silmaril.Wasm.Spec.Basic.Defs

@[expose] public section

/-!
# Harness reduction

A *harness* is a program that drives the program under test through its exports and reports
violations by calling one of its own imports (an `assert`). Linking the harness with the program
hides the program's exports; the program's imports and the harness's own imports and exports stay
visible. Reducing a property `φ` of the program to "the linked system never calls `assert` with a
false argument" is then a statement in institution theory:

* `Wiring Xp Xh Xl`: how the interfaces fit: program imports in the linked imports (`pl`), program
  exports as harness imports (`ph`), the harness's own imports (`oh`, `ol`, e.g. `assert`), and
  harness exports as linked exports (`hx`).
* `Link W tp th tl`: the trace `tl` of the linked system is an interleaving of a program trace
  `tp` and a harness trace `th`, synchronising the program's export events with the harness's
  calls to them (hidden), as `Silmaril.Games.Zip` does for strategy composition.
* `linkTraces W Tp Th`: the traces of the linked system (good when `Tp`, `Th` are,
  `Good.linkTraces`).
* `pullTrace W Th ψ`: the program property "every linked run with the harness satisfies `ψ`".
* `Harness.corridor`: **linking with a harness is a corridor** from the room of `L`-sentences
  about linked systems to the room of program properties: sentences are pulled back
  (`pull W Th ψ`), models are pushed forward (a program `p` denotes `linkTraces W (traces p) Th`
  in the linked room), and satisfaction is preserved (`sat_link_iff`).

For per-trace `ψ`, the pulled property is per-trace (`pullTrace`). A harness `Th` *reduces* `φ`
to `ψ` soundly when every program trace satisfying `pullTrace W Th ψ` satisfies `φ`, and
completely for the converse. `Silmaril.Wasm.Spec.Harness.Thms` proves the most general harness for a
return postcondition `Q` of an export `e` (`retHarness`) sound and complete: the linked system
never calls `assert` with an argument the verdict marks as failing iff every return of `e`
satisfies `Q`. Completeness holds because the harness is most general (it may call the exports in
any order with any arguments) and the property is a safety property of export events; harness
reductions of liveness properties, or of properties of the program's import calls (which the
harness does not see), are not complete in general.
-/

namespace Silmaril.Wasm.Spec

open CategoryTheory Silmaril.Logic.Institution

variable {Ty A R : Type}

/-- Rename the function index of a side event. -/
def SideEv.rename {n m : ℕ} (f : Fin n → Fin m) : SideEv A R n → SideEv A R m
  | .ask i a => .ask (f i) a
  | .ans i r => .ans (f i) r

/-- How a program, a harness and the linked system fit together. -/
structure Wiring (Xp Xh Xl : Iface Ty) where
  /-- Program imports among the linked imports. -/
  pl : Xp.Imp → Xl.Imp
  /-- Program exports among the harness imports. -/
  ph : Xp.Exp → Xh.Imp
  /-- The number of the harness's own imports. -/
  own : ℕ
  /-- The harness's own imports among its imports. -/
  oh : Fin own → Xh.Imp
  /-- The harness's own imports among the linked imports. -/
  ol : Fin own → Xl.Imp
  /-- Harness exports among the linked exports. -/
  hx : Xh.Exp → Xl.Exp

/-- The traces of a linked system: interleavings of a program trace and a harness trace,
synchronised on the program's exports. -/
inductive Link {Xp Xh Xl : Iface Ty} (W : Wiring Xp Xh Xl) :
    List (Event A R Xp) → List (Event A R Xh) → List (Event A R Xl) → Prop where
  /-- Nothing happened. -/
  | nil : Link W [] [] []
  /-- The program calls or is answered by one of its imports (visible). -/
  | pimp {tp th tl} (e : SideEv A R Xp.imports.length) :
      Link W tp th tl → Link W (.inl e :: tp) th (.inl (e.rename W.pl) :: tl)
  /-- The harness calls or is answered by one of its own imports (visible). -/
  | hown {tp th tl} (e : SideEv A R W.own) :
      Link W tp th tl → Link W tp (.inl (e.rename W.oh) :: th) (.inl (e.rename W.ol) :: tl)
  /-- The harness is called or returns at its exports (visible). -/
  | hexp {tp th tl} (e : SideEv A R Xh.exports.length) :
      Link W tp th tl → Link W tp (.inr e :: th) (.inr (e.rename W.hx) :: tl)
  /-- The harness calls the program, or the program returns to it (hidden). -/
  | sync {tp th tl} (e : SideEv A R Xp.exports.length) :
      Link W tp th tl → Link W (.inr e :: tp) (.inl (e.rename W.ph) :: th) tl

/-- The traces of the linked system. -/
def linkTraces {Xp Xh Xl : Iface Ty} (W : Wiring Xp Xh Xl) (Tp : Set (List (Event A R Xp)))
    (Th : Set (List (Event A R Xh))) : Set (List (Event A R Xl)) :=
  {tl | ∃ tp ∈ Tp, ∃ th ∈ Th, Link W tp th tl}

/-- The program property "every linked run with the harness satisfies the per-trace property
`ψ`". -/
def pullTrace {Xp Xh Xl : Iface Ty} (W : Wiring Xp Xh Xl) (Th : Set (List (Event A R Xh)))
    (ψ : List (Event A R Xl) → Prop) (tp : List (Event A R Xp)) : Prop :=
  ∀ th ∈ Th, ∀ tl, Link W tp th tl → ψ tl

/-- Properties of trace sets as a logic (the semantic logic of the format). -/
def semLogic (Ty A R : Type) : Logic Ty A R where
  Fm X := Set (List (Event A R X)) → Prop
  Sat T P := P T

/-- The pullback of an `L`-sentence about linked systems along a harness: a property of the
program's trace set. -/
def pull {Xp Xh Xl : Iface Ty} (W : Wiring Xp Xh Xl) (Th : Set (List (Event A R Xh)))
    (L : Logic Ty A R) (ψ : L.Fm Xl) : (semLogic Ty A R).Fm Xp :=
  fun Tp => L.Sat (linkTraces W Tp Th) ψ

/-- A room whose models are the programs of a semantics, read through a trace map. -/
def progRoom (L : Logic Ty A R) (X : Iface Ty) (M : Type) (tr : M → Set (List (Event A R X))) :
    Room.{0, 0, 0} :=
  ⟨L.Fm X, Cat.of (Discrete M), fun m φ => L.Sat (tr m.as) φ⟩

/-- **Linking with a harness is a corridor**: from `L`-sentences about the linked system (whose
models are programs, denoting their link with the harness) to properties of programs; sentences
are pulled back along the harness, programs are unchanged. -/
def Harness.corridor (S : Semantics Ty A R) {Xp Xh Xl : Iface Ty} (W : Wiring Xp Xh Xl)
    (Th : Set (List (Event A R Xh))) (L : Logic Ty A R) :
    progRoom L Xl (S.Prog Xp) (fun p => linkTraces W (S.traces p) Th) ⟶
      progRoom (semLogic Ty A R) Xp (S.Prog Xp) S.traces :=
  ⟨pull W Th L, 𝟭 _, fun _ _ => Iff.rfl⟩

end Silmaril.Wasm.Spec

namespace Silmaril.Wasm.Spec

variable {Ty A R : Type}

/-! ## The most general harness for a return postcondition -/

/-- The data of a return-postcondition harness: the export `e` under test, the harness's check
import `chk` (an `assert`), the verdict passed to `chk` for each result, the answer `ok` of `chk`,
and the harness's entry export `main` with its argument. -/
structure RetHarness {Xp Xh Xl : Iface Ty} (W : Wiring Xp Xh Xl) (A R : Type) where
  /-- The export under test. -/
  e : Xp.Exp
  /-- The check import (among the harness's own imports). -/
  chk : Fin W.own
  /-- The argument passed to the check after a return of `e`. -/
  verdict : R → A
  /-- The check's answer. -/
  ok : R
  /-- The harness's entry export. -/
  main : Xh.Exp
  /-- Its argument. -/
  arg : A

variable {Xp Xh Xl : Iface Ty} {W : Wiring Xp Xh Xl}

/-- The harness run mirroring a sequence of program export events, checking every return of
`e`. -/
def RetHarness.drive (H : RetHarness W A R) :
    List (SideEv A R Xp.exports.length) → List (Event A R Xh)
  | [] => []
  | .ask j a :: u => .inl (.ask (W.ph j) a) :: H.drive u
  | .ans j r :: u => .inl (.ans (W.ph j) r) ::
      ((if j = H.e then [.inl (.ask (W.oh H.chk) (H.verdict r)), .inl (.ans (W.oh H.chk) H.ok)]
        else []) ++ H.drive u)

/-- **The most general harness**: called at `main`, it may drive the program through any
sequence of export calls (any order, any arguments) and checks every return of `e`. -/
def RetHarness.traces (H : RetHarness W A R) : Set (List (Event A R Xh)) :=
  {th | ∃ u, th <+: .inr (.ask H.main H.arg) :: H.drive u}

/-- The linked run of a program trace with the harness run mirroring it. -/
def RetHarness.linkOf (H : RetHarness W A R) :
    List (Event A R Xp) → List (Event A R Xl)
  | [] => []
  | .inl x :: tp => .inl (x.rename W.pl) :: H.linkOf tp
  | .inr (.ask _ _) :: tp => H.linkOf tp
  | .inr (.ans j r) :: tp =>
      (if j = H.e then [.inl (.ask (W.ol H.chk) (H.verdict r)), .inl (.ans (W.ol H.chk) H.ok)]
        else []) ++ H.linkOf tp

end Silmaril.Wasm.Spec
